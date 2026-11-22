use std::cell::{Cell, RefCell};
use std::ffi::c_void;
use std::fs::{File, OpenOptions};
use std::io::Write as _;
use std::mem::size_of;
use std::path::PathBuf;
use std::ptr::{copy_nonoverlapping, null_mut};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::OnceLock;
use std::thread;
use std::time::Duration;

use windows_sys::Win32::Foundation::{CloseHandle, GetLastError, BOOL, HANDLE, HMODULE, TRUE};
use windows_sys::Win32::System::Diagnostics::Debug::{
    FlushInstructionCache, WriteProcessMemory, IMAGE_NT_HEADERS64,
};
use windows_sys::Win32::System::LibraryLoader::{
    DisableThreadLibraryCalls, GetModuleHandleW, GetProcAddress, LoadLibraryW,
};
use windows_sys::Win32::System::Memory::{
    VirtualAlloc, VirtualFree, VirtualProtect, VirtualProtectEx, VirtualQuery,
    MEMORY_BASIC_INFORMATION, MEM_COMMIT, MEM_RELEASE, MEM_RESERVE, PAGE_EXECUTE,
    PAGE_EXECUTE_READ, PAGE_EXECUTE_READWRITE, PAGE_EXECUTE_WRITECOPY, PAGE_GUARD, PAGE_NOACCESS,
    PAGE_READWRITE,
};
use windows_sys::Win32::System::SystemInformation::GetSystemDirectoryW;
use windows_sys::Win32::System::SystemServices::{
    DLL_PROCESS_ATTACH, IMAGE_DOS_HEADER, IMAGE_DOS_SIGNATURE, IMAGE_NT_SIGNATURE,
};
use windows_sys::Win32::System::Threading::{
    GetCurrentProcess, GetCurrentProcessId, OpenProcess, PROCESS_QUERY_INFORMATION,
    PROCESS_VM_OPERATION, PROCESS_VM_READ, PROCESS_VM_WRITE,
};

const E_FAIL: i32 = 0x80004005u32 as i32;

type DirectInput8CreateFn = unsafe extern "system" fn(
    hinst: *mut c_void,
    dw_version: u32,
    riidltf: *const c_void,
    ppv_out: *mut *mut c_void,
    punk_outer: *mut c_void,
) -> i32;

type ClothStepFn = unsafe extern "system" fn(
    cloth: *mut u8,
    state: *mut u8,
    bones: *mut c_void,
    extra: *mut c_void,
    collision: *mut c_void,
);

type ClothFinishFn = unsafe extern "system" fn(cloth: *mut u8, state: *mut u8);

static REAL_DINPUT8_CREATE: OnceLock<Option<DirectInput8CreateFn>> = OnceLock::new();
static WORKER_STARTED: AtomicBool = AtomicBool::new(false);
static ORIGINAL_STEP: OnceLock<ClothStepFn> = OnceLock::new();
static ORIGINAL_FINISH: OnceLock<ClothFinishFn> = OnceLock::new();
static FRACTIONAL_CALLS: AtomicU64 = AtomicU64::new(0);

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct ParticleHistory {
    position: [f32; 3],
    velocity: [f32; 3],
    anchored: bool,
}

#[repr(C)]
struct FractionContext {
    cloth: *mut u8,
    previous: *const ParticleHistory,
    count: usize,
    alpha: f32,
    step: f32,
}

#[repr(C, align(16))]
struct AlignedState([u8; 0x170]);

thread_local! {
    static ACTIVE_FRACTION: Cell<*mut FractionContext> = const { Cell::new(null_mut()) };
    static HISTORY: RefCell<Vec<ParticleHistory>> = const { RefCell::new(Vec::new()) };
}

struct ActiveGuard(*mut FractionContext);

impl Drop for ActiveGuard {
    fn drop(&mut self) {
        ACTIVE_FRACTION.with(|c| {
            if c.get() == self.0 {
                c.set(null_mut());
            }
        });
    }
}

#[inline(always)]
unsafe fn read_field<T: Copy>(base: *const u8, offset: usize) -> T {
    unsafe { base.add(offset).cast::<T>().read_unaligned() }
}

#[inline(always)]
unsafe fn write_field<T: Copy>(base: *mut u8, offset: usize, value: T) {
    unsafe { base.add(offset).cast::<T>().write_unaligned(value) };
}

unsafe extern "system" fn hk_finish(cloth: *mut u8, state: *mut u8) {
    let ctx_ptr = ACTIVE_FRACTION.with(|c| c.get());
    if !ctx_ptr.is_null() {
        let ctx = unsafe { &*ctx_ptr };
        if ctx.cloth == cloth {
            let particles = unsafe { read_field::<*mut u8>(cloth, 0x90) };
            if !particles.is_null() {
                for i in 0..ctx.count {
                    let old = unsafe { &*ctx.previous.add(i) };
                    if old.anchored {
                        continue;
                    }
                    let p = unsafe { particles.add(i * 64) };
                    for j in 0..3 {
                        let cur_pos = unsafe { read_field::<f32>(p, j * 4) };
                        let cur_vel = unsafe { read_field::<f32>(p, 0x20 + j * 4) };
                        let position = old.position[j] + ctx.alpha * (cur_pos - old.position[j]);
                        let velocity = old.velocity[j] + ctx.alpha * (cur_vel - old.velocity[j]);
                        unsafe {
                            write_field::<f32>(p, j * 4, position);
                            write_field::<f32>(p, 0x20 + j * 4, velocity);
                            write_field::<f32>(p, 0x10 + j * 4, position - velocity * ctx.step);
                        }
                    }
                }
            }
        }
    }
    if let Some(&orig_finish) = ORIGINAL_FINISH.get() {
        unsafe { orig_finish(cloth, state) };
    }
}

unsafe extern "system" fn hk_step(
    cloth: *mut u8,
    state: *mut u8,
    bones: *mut c_void,
    extra: *mut c_void,
    collision: *mut c_void,
) {
    let Some(&orig_step) = ORIGINAL_STEP.get() else {
        return;
    };

    if cloth.is_null() || state.is_null() {
        unsafe { orig_step(cloth, state, bones, extra, collision) };
        return;
    }

    let frame = unsafe { read_field::<f32>(state, 0x134) };
    let current_step = unsafe { read_field::<f32>(state, 0x130) };
    let cloth_flags = unsafe { read_field::<u32>(cloth, 0x38) };
    let count = unsafe { read_field::<u32>(cloth, 0x98) } as usize;
    let attachments = unsafe { read_field::<u32>(cloth, 0xf8) } as usize;
    let state_reset = unsafe { read_field::<u8>(state, 0x152) };

    if cloth_flags != 0
        || count == 0
        || count > 4096
        || attachments > 4096
        || !(frame > 0.0 && frame < 1.0 / 30.0)
        || !(current_step > 0.0)
        || !frame.is_finite()
        || !current_step.is_finite()
        || state_reset != 0
    {
        unsafe { orig_step(cloth, state, bones, extra, collision) };
        return;
    }

    let alpha = (frame * 30.0).clamp(0.05, 1.0);
    let reference_step = current_step / alpha;
    if !(reference_step > 0.0 && reference_step <= 0.2) {
        unsafe { orig_step(cloth, state, bones, extra, collision) };
        return;
    }

    let particles = unsafe { read_field::<*mut u8>(cloth, 0x90) };
    let binds = unsafe { read_field::<*const u8>(cloth, 0xf0) };
    if particles.is_null() || (attachments != 0 && binds.is_null()) {
        unsafe { orig_step(cloth, state, bones, extra, collision) };
        return;
    }

    if ACTIVE_FRACTION.with(|c| !c.get().is_null()) {
        unsafe { orig_step(cloth, state, bones, extra, collision) };
        return;
    }

    let inv_alpha = 1.0 / alpha;

    HISTORY.with(|cell| {
        let mut history = cell.borrow_mut();
        history.clear();
        history.resize(count, ParticleHistory::default());

        for (i, old) in history.iter_mut().enumerate() {
            let p = unsafe { particles.add(i * 64) };
            old.anchored = unsafe { read_field::<u32>(p, 0x38) } != 0;

            for j in 0..3 {
                let mut pos = 0.0f32;
                let mut vel = 0.0f32;
                for axis in 0..3 {
                    let basis = unsafe { read_field::<f32>(state, 0x80 + axis * 16 + j * 4) };
                    pos += basis * unsafe { read_field::<f32>(p, axis * 4) };
                    vel += basis * unsafe { read_field::<f32>(p, 0x20 + axis * 4) };
                }
                old.position[j] = pos;
                old.velocity[j] = vel;
            }
        }

        for i in 0..attachments {
            let index = unsafe { read_field::<u32>(binds, i * 128 + 4) } as usize;
            if index < count {
                history[index].anchored = true;
            }
        }

        let mut local = AlignedState([0u8; 0x170]);
        unsafe {
            copy_nonoverlapping(state, local.0.as_mut_ptr(), 0x170);
            for off in [0xb0usize, 0xb4usize, 0xb8usize] {
                let t = read_field::<f32>(state, off);
                write_field::<f32>(local.0.as_mut_ptr(), off, t * inv_alpha);
            }
            write_field::<f32>(local.0.as_mut_ptr(), 0x130, reference_step);
        }

        let mut ctx = FractionContext {
            cloth,
            previous: history.as_ptr(),
            count,
            alpha,
            step: reference_step,
        };
        let ctx_ptr: *mut FractionContext = &mut ctx;

        ACTIVE_FRACTION.with(|c| c.set(ctx_ptr));
        let _guard = ActiveGuard(ctx_ptr);
        unsafe { orig_step(cloth, local.0.as_mut_ptr(), bones, extra, collision) };
        FRACTIONAL_CALLS.fetch_add(1, Ordering::Relaxed);
    });
}

fn resolve_real_dinput8() -> Option<DirectInput8CreateFn> {
    unsafe {
        let mut buf = [0u16; 512];
        let len = GetSystemDirectoryW(buf.as_mut_ptr(), buf.len() as u32) as usize;
        if len == 0 || len + 16 >= buf.len() {
            return None;
        }
        let suffix: Vec<u16> = "\\dinput8.dll\0".encode_utf16().collect();
        buf[len..len + suffix.len()].copy_from_slice(&suffix);

        let lib = LoadLibraryW(buf.as_ptr());
        if (lib as usize) == 0 {
            return None;
        }
        let proc_ptr = GetProcAddress(lib, b"DirectInput8Create\0".as_ptr())?;
        Some(std::mem::transmute::<_, DirectInput8CreateFn>(proc_ptr))
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "system" fn DirectInput8Create(
    hinst: *mut c_void,
    dw_version: u32,
    riidltf: *const c_void,
    ppv_out: *mut *mut c_void,
    punk_outer: *mut c_void,
) -> i32 {
    match *REAL_DINPUT8_CREATE.get_or_init(resolve_real_dinput8) {
        Some(func) => unsafe { func(hinst, dw_version, riidltf, ppv_out, punk_outer) },
        None => E_FAIL,
    }
}

fn log_path() -> PathBuf {
    std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|d| d.join("wd_coat_fix.log")))
        .unwrap_or_else(|| PathBuf::from("wd_coat_fix.log"))
}

fn append_log(msg: &str) {
    if let Ok(mut f) = OpenOptions::new().create(true).append(true).open(log_path()) {
        let _ = writeln!(f, "{msg}");
        let _ = f.flush();
    }
}

unsafe fn exec_regions(module_base: usize) -> Vec<(usize, usize)> {
    let mut regions = Vec::new();
    let mut addr = module_base;
    let mut mbi: MEMORY_BASIC_INFORMATION = unsafe { std::mem::zeroed() };
    let exec_mask =
        PAGE_EXECUTE | PAGE_EXECUTE_READ | PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY;

    while unsafe {
        VirtualQuery(
            addr as *const c_void,
            &mut mbi,
            size_of::<MEMORY_BASIC_INFORMATION>(),
        )
    } != 0
    {
        if mbi.AllocationBase as usize != module_base {
            break;
        }
        if mbi.State == MEM_COMMIT
            && (mbi.Protect & PAGE_GUARD) == 0
            && (mbi.Protect & exec_mask) != 0
            && mbi.RegionSize > 0
        {
            regions.push((mbi.BaseAddress as usize, mbi.RegionSize));
        }
        addr = mbi.BaseAddress as usize + mbi.RegionSize;
    }
    regions
}

unsafe fn read_safe(module_base: usize, addr: usize, len: usize) -> Option<Vec<u8>> {
    if len == 0 || addr < module_base {
        return None;
    }
    let mut mbi: MEMORY_BASIC_INFORMATION = unsafe { std::mem::zeroed() };
    if unsafe {
        VirtualQuery(
            addr as *const c_void,
            &mut mbi,
            size_of::<MEMORY_BASIC_INFORMATION>(),
        )
    } == 0
    {
        return None;
    }
    if mbi.AllocationBase as usize != module_base
        || mbi.State != MEM_COMMIT
        || (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS)) != 0
    {
        return None;
    }
    let end_avail = mbi.BaseAddress as usize + mbi.RegionSize;
    if addr + len > end_avail {
        return None;
    }
    let slice = unsafe { std::slice::from_raw_parts(addr as *const u8, len) };
    Some(slice.to_vec())
}

fn find_in_slice(slice: &[u8], pattern: &[Option<u8>]) -> Option<usize> {
    if pattern.is_empty() || slice.len() < pattern.len() {
        return None;
    }
    slice.windows(pattern.len()).position(|win| {
        pattern
            .iter()
            .zip(win.iter())
            .all(|(p, b)| p.map_or(true, |x| x == *b))
    })
}

unsafe fn scan_all(
    regions: &[(usize, usize)],
    pattern: &[Option<u8>],
    max_hits: usize,
) -> Vec<usize> {
    let mut hits = Vec::new();
    let Some(first) = pattern.first().copied().flatten() else {
        return hits;
    };
    let plen = pattern.len();

    for &(rbase, rsize) in regions {
        if rsize < plen {
            continue;
        }
        let slice = unsafe { std::slice::from_raw_parts(rbase as *const u8, rsize) };
        let limit = rsize - plen;
        let mut i = 0usize;
        while i <= limit {
            let Some(rel) = slice[i..=limit].iter().position(|&b| b == first) else {
                break;
            };
            let pos = i + rel;
            let matched = pattern[1..]
                .iter()
                .zip(slice[pos + 1..pos + plen].iter())
                .all(|(p, b)| p.map_or(true, |x| x == *b));
            if matched {
                hits.push(rbase + pos);
                if hits.len() >= max_hits {
                    return hits;
                }
            }
            i = pos + 1;
        }
    }
    hits
}

unsafe fn find_callers(regions: &[(usize, usize)], target_va: usize, max_hits: usize) -> Vec<usize> {
    let mut hits = Vec::new();
    for &(rbase, rsize) in regions {
        if rsize < 5 {
            continue;
        }
        let slice = unsafe { std::slice::from_raw_parts(rbase as *const u8, rsize) };
        let limit = rsize - 5;
        let mut i = 0usize;
        while i <= limit {
            let Some(rel) = slice[i..=limit].iter().position(|&b| b == 0xE8) else {
                break;
            };
            let pos = i + rel;
            let disp = i32::from_le_bytes([
                slice[pos + 1],
                slice[pos + 2],
                slice[pos + 3],
                slice[pos + 4],
            ]);
            let call_va = rbase + pos;
            let resolved = (call_va as isize)
                .wrapping_add(5)
                .wrapping_add(disp as isize) as usize;
            if resolved == target_va {
                hits.push(call_va);
                if hits.len() >= max_hits {
                    return hits;
                }
            }
            i = pos + 1;
        }
    }
    hits
}

unsafe fn resolve_call_target(call_va: usize) -> Option<usize> {
    let bytes = unsafe { std::slice::from_raw_parts(call_va as *const u8, 5) };
    if bytes[0] != 0xE8 {
        return None;
    }
    let rel = i32::from_le_bytes([bytes[1], bytes[2], bytes[3], bytes[4]]);
    Some((call_va as isize).wrapping_add(5).wrapping_add(rel as isize) as usize)
}

unsafe fn alloc_relay_near(site0_va: usize, site1_va: usize) -> *mut u8 {
    let aligned = site0_va & !0xFFFFusize;
    for off in (0x10000usize..0x7000_0000usize).step_by(0x10000usize) {
        for cand_opt in [aligned.checked_add(off), aligned.checked_sub(off)] {
            let Some(cand) = cand_opt else { continue };
            if cand == 0 {
                continue;
            }
            let d0 = (cand as isize) - (site0_va as isize + 5);
            let d1 = (cand as isize + 32) - (site1_va as isize + 5);
            if i32::try_from(d0).is_err() || i32::try_from(d1).is_err() {
                continue;
            }
            let ptr = unsafe {
                VirtualAlloc(
                    cand as *const c_void,
                    0x1000,
                    MEM_RESERVE | MEM_COMMIT,
                    PAGE_READWRITE,
                )
            };
            if !ptr.is_null() {
                return ptr.cast::<u8>();
            }
        }
    }
    null_mut()
}

unsafe fn try_vp_patch(
    proc_handle: HANDLE,
    use_vp_ex: bool,
    prot_flag: u32,
    addrs: [usize; 3],
    sizes: [usize; 3],
    write_addrs: [usize; 3],
    payloads: [&[u8]; 3],
) -> Result<(), u32> {
    let mut old_prots = [0u32; 3];
    for i in 0..3 {
        let ok = unsafe {
            if use_vp_ex {
                VirtualProtectEx(
                    proc_handle,
                    addrs[i] as *const c_void,
                    sizes[i],
                    prot_flag,
                    &mut old_prots[i],
                )
            } else {
                VirtualProtect(
                    addrs[i] as *const c_void,
                    sizes[i],
                    prot_flag,
                    &mut old_prots[i],
                )
            }
        };
        if ok == 0 {
            let err = unsafe { GetLastError() };
            for j in 0..i {
                let mut ignored = 0u32;
                unsafe {
                    if use_vp_ex {
                        VirtualProtectEx(
                            proc_handle,
                            addrs[j] as *const c_void,
                            sizes[j],
                            old_prots[j],
                            &mut ignored,
                        );
                    } else {
                        VirtualProtect(
                            addrs[j] as *const c_void,
                            sizes[j],
                            old_prots[j],
                            &mut ignored,
                        );
                    }
                }
            }
            return Err(err);
        }
    }

    for idx in [2usize, 1usize, 0usize] {
        unsafe {
            copy_nonoverlapping(
                payloads[idx].as_ptr(),
                write_addrs[idx] as *mut u8,
                payloads[idx].len(),
            );
        }
    }

    for i in 0..3 {
        let mut ignored = 0u32;
        unsafe {
            FlushInstructionCache(proc_handle, addrs[i] as *const c_void, sizes[i]);
            if use_vp_ex {
                VirtualProtectEx(
                    proc_handle,
                    addrs[i] as *const c_void,
                    sizes[i],
                    old_prots[i],
                    &mut ignored,
                );
            } else {
                VirtualProtect(
                    addrs[i] as *const c_void,
                    sizes[i],
                    old_prots[i],
                    &mut ignored,
                );
            }
        }
    }
    Ok(())
}

unsafe fn try_wpm_patch(
    proc_handle: HANDLE,
    write_addrs: [usize; 3],
    payloads: [&[u8]; 3],
) -> Result<(), u32> {
    for idx in [2usize, 1usize, 0usize] {
        let mut n = 0usize;
        let ok = unsafe {
            WriteProcessMemory(
                proc_handle,
                write_addrs[idx] as *const c_void,
                payloads[idx].as_ptr() as *const c_void,
                payloads[idx].len(),
                &mut n,
            )
        };
        if ok == 0 || n != payloads[idx].len() {
            return Err(unsafe { GetLastError() });
        }
        unsafe {
            FlushInstructionCache(
                proc_handle,
                write_addrs[idx] as *const c_void,
                payloads[idx].len(),
            );
        }
    }
    Ok(())
}

unsafe fn patch_engine_sites(
    step_call_va: usize,
    finish_call_va: usize,
    mulss_va: usize,
    disp_step: i32,
    disp_finish: i32,
) -> Result<&'static str, String> {
    let frame_comp: [u8; 8] = [0xF3, 0x41, 0x0F, 0x59, 0xC8, 0x90, 0x90, 0x90];
    let disp_step_bytes = disp_step.to_le_bytes();
    let disp_finish_bytes = disp_finish.to_le_bytes();

    let addrs = [step_call_va, finish_call_va, mulss_va];
    let sizes = [5usize, 5usize, 8usize];
    let write_addrs = [step_call_va + 1, finish_call_va + 1, mulss_va];
    let payloads: [&[u8]; 3] = [&disp_step_bytes, &disp_finish_bytes, &frame_comp];

    let cur_proc = unsafe { GetCurrentProcess() };
    let pid = unsafe { GetCurrentProcessId() };
    let real_handle = unsafe {
        OpenProcess(
            PROCESS_VM_OPERATION
                | PROCESS_VM_WRITE
                | PROCESS_VM_READ
                | PROCESS_QUERY_INFORMATION,
            0,
            pid,
        )
    };

    if !real_handle.is_null() {
        if unsafe {
            try_vp_patch(
                real_handle,
                true,
                PAGE_EXECUTE_READWRITE,
                addrs,
                sizes,
                write_addrs,
                payloads,
            )
        }
        .is_ok()
        {
            unsafe { CloseHandle(real_handle) };
            return Ok("VirtualProtectEx(RWX)");
        }
        if unsafe { try_wpm_patch(real_handle, write_addrs, payloads) }.is_ok() {
            unsafe { CloseHandle(real_handle) };
            return Ok("WriteProcessMemory(OpenProcess)");
        }
        unsafe { CloseHandle(real_handle) };
    }

    for (name, flag) in [
        ("VirtualProtect(RWX)", PAGE_EXECUTE_READWRITE),
        ("VirtualProtect(WCX)", PAGE_EXECUTE_WRITECOPY),
    ] {
        if unsafe { try_vp_patch(cur_proc, false, flag, addrs, sizes, write_addrs, payloads) }
            .is_ok()
        {
            return Ok(name);
        }
    }

    Err(format!("all patch methods failed (err={})", unsafe {
        GetLastError()
    }))
}

unsafe fn try_install(base: usize) -> Result<String, String> {
    let dos = unsafe { &*(base as *const IMAGE_DOS_HEADER) };
    if dos.e_magic != IMAGE_DOS_SIGNATURE || dos.e_lfanew <= 0 || dos.e_lfanew >= 0x1000 {
        return Err("invalid DOS header".into());
    }
    let nt = unsafe { &*((base + dos.e_lfanew as usize) as *const IMAGE_NT_HEADERS64) };
    if nt.Signature != IMAGE_NT_SIGNATURE {
        return Err("invalid NT header".into());
    }

    let regions = unsafe { exec_regions(base) };
    if regions.is_empty() {
        return Err("waiting for executable sections".into());
    }

    const SETUP_PAT: &[Option<u8>] = &[
        Some(0xF2), Some(0x0F), Some(0x5A), Some(0x40), Some(0x70),
        Some(0x0F), Some(0x28), Some(0xC8),
        Some(0xF3), Some(0x0F), Some(0x58), Some(0x05), None, None, None, None,
        Some(0x0F), Some(0x2F), Some(0xC6),
        Some(0xF3), Some(0x0F), Some(0x59), Some(0x0D), None, None, None, None,
        Some(0x76), Some(0x0A),
        Some(0x0F), Some(0x2F), Some(0xC7),
        Some(0x76), Some(0x08),
        Some(0x0F), Some(0x28), Some(0xC7),
        Some(0xEB), Some(0x03),
        Some(0x0F), Some(0x28), Some(0xC6),
        Some(0xF3), Some(0x44), Some(0x0F), Some(0x11), Some(0x87),
    ];

    let setup_hits = unsafe { scan_all(&regions, SETUP_PAT, 2) };
    if setup_hits.is_empty() {
        return Err("waiting for unpacked setup block".into());
    }
    if setup_hits.len() != 1 {
        return Err(format!("ambiguous setup match: {}", setup_hits.len()));
    }
    let mulss_va = setup_hits[0] + 19;

    const ENTRY_PAT: &[Option<u8>] = &[
        Some(0x48), Some(0x89), Some(0x6C), Some(0x24), Some(0x20),
        Some(0x56), Some(0x57), Some(0x41), Some(0x56),
        Some(0x48), Some(0x83), Some(0xEC), Some(0x40),
    ];
    const FINISH_CALL_PAT: &[Option<u8>] = &[
        Some(0xEB), Some(0x0B),
        Some(0x48), Some(0x8B), Some(0xD6),
        Some(0x48), Some(0x8B), Some(0xCF),
        Some(0xE8), None, None, None, None,
        Some(0x48), Some(0x8B), Some(0xD6),
        Some(0x48), Some(0x8B), Some(0xCF),
        Some(0xE8),
    ];

    let entry_hits = unsafe { scan_all(&regions, ENTRY_PAT, 64) };
    if entry_hits.is_empty() {
        return Err("waiting for unpacked ClothStep".into());
    }

    let mut target: Option<(usize, usize, usize, usize)> = None;
    for fn_va in &entry_hits {
        let fn_va = *fn_va;
        let Some(body) = (unsafe { read_safe(base, fn_va, 0x450) }) else {
            continue;
        };
        let has_130 = body.windows(4).any(|w| w == [0x30, 0x01, 0x00, 0x00]);
        let has_90 = body.windows(4).any(|w| w == [0x90, 0x00, 0x00, 0x00]);
        let has_98 = body.windows(4).any(|w| w == [0x98, 0x00, 0x00, 0x00]);
        if !(has_130 && has_90 && has_98) {
            continue;
        }

        let Some(rel_idx) = find_in_slice(&body[0x200..0x380], FINISH_CALL_PAT) else {
            continue;
        };
        let finish_call_va = fn_va + 0x200 + rel_idx + 8;
        let Some(finish_fn_va) = (unsafe { resolve_call_target(finish_call_va) }) else {
            continue;
        };

        let callers = unsafe { find_callers(&regions, fn_va, 4) };
        if callers.len() != 1 {
            continue;
        }
        let step_call_va = callers[0];
        if target.is_some() {
            return Err("ambiguous ClothStep candidate".into());
        }
        target = Some((fn_va, step_call_va, finish_call_va, finish_fn_va));
    }

    let Some((step_fn_va, step_call_va, finish_call_va, finish_fn_va)) = target else {
        return Err("ClothStep signature not matched yet".into());
    };

    let _ = ORIGINAL_STEP.set(unsafe { std::mem::transmute::<usize, ClothStepFn>(step_fn_va) });
    let _ =
        ORIGINAL_FINISH.set(unsafe { std::mem::transmute::<usize, ClothFinishFn>(finish_fn_va) });

    let relay = unsafe { alloc_relay_near(step_call_va, finish_call_va) };
    if relay.is_null() {
        return Err(format!("alloc_relay_near failed (err={})", unsafe {
            GetLastError()
        }));
    }

    let hooks = [
        hk_step as *const () as usize,
        hk_finish as *const () as usize,
    ];
    let jump_opcode: [u8; 6] = [0xFF, 0x25, 0x00, 0x00, 0x00, 0x00];
    for (i, &hk_addr) in hooks.iter().enumerate() {
        unsafe {
            let slot = relay.add(i * 32);
            copy_nonoverlapping(jump_opcode.as_ptr(), slot, 6);
            copy_nonoverlapping((hk_addr as u64).to_le_bytes().as_ptr(), slot.add(6), 8);
        }
    }

    let mut relay_old_prot = 0u32;
    if unsafe {
        VirtualProtect(
            relay as *const c_void,
            0x1000,
            PAGE_EXECUTE_READ,
            &mut relay_old_prot,
        )
    } == 0
    {
        let err = unsafe { GetLastError() };
        unsafe { VirtualFree(relay as *mut c_void, 0, MEM_RELEASE) };
        return Err(format!("VirtualProtect on relay failed (err={err})"));
    }

    let proc_handle = unsafe { GetCurrentProcess() };
    unsafe { FlushInstructionCache(proc_handle, relay as *const c_void, 64) };

    let disp_step = ((relay as isize) - (step_call_va as isize + 5)) as i32;
    let disp_finish = ((relay as isize + 32) - (finish_call_va as isize + 5)) as i32;

    match unsafe {
        patch_engine_sites(
            step_call_va,
            finish_call_va,
            mulss_va,
            disp_step,
            disp_finish,
        )
    } {
        Ok(method) => Ok(format!(
            "PATCH APPLIED ({method}): mulss_rva={:#x}, step_fn_rva={:#x}, step_call_rva={:#x}, finish_call_rva={:#x}, finish_fn_rva={:#x}",
            mulss_va - base,
            step_fn_va - base,
            step_call_va - base,
            finish_call_va - base,
            finish_fn_va - base
        )),
        Err(diag) => {
            unsafe { VirtualFree(relay as *mut c_void, 0, MEM_RELEASE) };
            Err(diag)
        }
    }
}

fn install_worker() {
    let _ = File::create(log_path());
    append_log("wd_coat_fix (Rust): waiting for Disrupt_b64.dll unpack...");
    let module_name: Vec<u16> = "Disrupt_b64.dll\0".encode_utf16().collect();
    let mut last_err = String::new();

    for _ in 0..1800 {
        let hmod = unsafe { GetModuleHandleW(module_name.as_ptr()) };
        let base = hmod as usize;
        if base == 0 {
            if last_err != "Disrupt_b64.dll not loaded" {
                last_err = "Disrupt_b64.dll not loaded".into();
                append_log(&format!("status: {last_err}"));
            }
        } else {
            match unsafe { try_install(base) } {
                Ok(summary) => {
                    append_log(&summary);
                    for _ in 0..300 {
                        thread::sleep(Duration::from_secs(1));
                        let calls = FRACTIONAL_CALLS.load(Ordering::Relaxed);
                        if calls > 0 {
                            append_log(&format!(
                                "ACTIVE: fractional cloth solver running in-game (calls={calls})."
                            ));
                            return;
                        }
                    }
                    return;
                }
                Err(reason) => {
                    if reason != last_err {
                        append_log(&format!("status: {reason}"));
                        last_err = reason;
                    }
                }
            }
        }
        thread::sleep(Duration::from_millis(100));
    }

    append_log(&format!("FAILED (timeout): {last_err}"));
}

#[unsafe(no_mangle)]
pub unsafe extern "system" fn DllMain(
    hinst_dll: HMODULE,
    fdw_reason: u32,
    _lpv_reserved: *mut c_void,
) -> BOOL {
    if fdw_reason == DLL_PROCESS_ATTACH {
        unsafe { DisableThreadLibraryCalls(hinst_dll) };
        if !WORKER_STARTED.swap(true, Ordering::SeqCst) {
            thread::spawn(install_worker);
        }
    }
    TRUE
}
