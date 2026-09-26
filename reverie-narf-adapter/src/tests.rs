//! In-kernel tests of the Reverie backend (subsystem `reverie-narf`).
//!
//! Each test runs one real x86_64 Linux guest ELF as a scheduled user task
//! under Narf's live syscall dispatcher with an interceptor installed, and
//! inspects what the hosted Tool and the kernel reported once every task of
//! the guest has been reaped.

use alloc::boxed::Box;
use alloc::sync::{Arc, Weak};
use alloc::vec::Vec;
use core::fmt::Write as _;
use core::sync::atomic::{AtomicI64, AtomicU64, Ordering};

use narf_console::Writer;
use narf_filesystem::{FileOps, FsError, FsFuture, Stat};
use narf_kernel_test::{kernel_test_in, TestResult};
use narf_lib::sync::IrqSafeSpinLock;
use narf_memory::{AddressSpace, PhysAddr, RegionPerms};
use narf_scheduler::{Affinity, CpuId, TaskSpec};
use narf_userspace::handlers::tool_view;
use narf_userspace::syscall::{
    NativeSyscallOutcome, NativeSyscallTransition, SyscallInterception, SyscallInterceptor,
    SyscallInvocation, SyscallReturn,
};
use reverie::syscalls::{Addr, MemoryAccess};
use reverie::{Pid, Tool};
use reverie_narf_core::{KernelServices, NarfSyscallOutcome, OriginalSyscallError};
use reverie_narf_tools::canonical::CanonicalTrace;
use reverie_narf_tools::counter1::CounterLocal;
use reverie_narf_tools::passthrough::PassThrough;
use reverie_narf_tools::probe::Probe;

use crate::interceptor::{ConsoleSink, ReverieInterceptor, TaskExitRecord};
use crate::services::{map_native_outcome, NarfKernelServices};

static CANONICAL_GUEST: &[u8] = include_bytes!(env!("REVERIE_NARF_GUEST_CANONICAL"));
static PROBE_GUEST: &[u8] = include_bytes!(env!("REVERIE_NARF_GUEST_PROBE"));
static FORK_GUEST: &[u8] = include_bytes!(env!("REVERIE_NARF_GUEST_FORK"));
static REAPER_GUEST: &[u8] = include_bytes!(env!("REVERIE_NARF_GUEST_REAPER"));

/// Address of the canonical guest's 16-byte message (its `.rodata`).
const CANONICAL_MESSAGE_ADDR: u64 = 0x0000_0080_0000_3000;
const CANONICAL_MESSAGE: &[u8; 16] = b"narf-hermit-poc\n";
/// The canonical guest's text segment.
const CANONICAL_TEXT: core::ops::Range<u64> = 0x0000_0080_0000_2000..0x0000_0080_0000_3000;
const LINUX_WRITE: u32 = 1;

/// About 10 s at 3 GHz, as in the neighbouring scheduled-user smokes.
const WAITER_BUDGET_CYCLES: u64 = 30_000_000_000;

/// The run's root task.
#[derive(Clone, Copy)]
struct Root {
    task_id: u64,
    pid: u64,
}

/// Linux `SIGCHLD`, the exit signal a `fork` child raises in its parent. The
/// cell's root is published as the reaping parent's child with it, so that
/// parent's plain `wait4(-1, &status, 0, NULL)` reaps it.
const LINUX_SIGCHLD: u8 = 17;
/// Linux `__WALL`: wait for a child whatever its exit signal. Used by the
/// post-run check that the reaping parent has no reapable child left.
const LINUX_WALL: u32 = 0x4000_0000;
/// Linux `ECHILD`.
const LINUX_ECHILD: i64 = 10;
/// The reaping-parent guest stores this in its status word before `wait4`.
const REAPER_STATUS_SENTINEL: i32 = 0xdead_beef_u32 as i32;
/// Length of the reaping-parent guest's report (see `guests/reaper_x86_64.S`).
const REAPER_REPORT_LEN: usize = 16;

/// How the run's root ended, as its reaping parent saw it.
///
/// The parent is a second guest process, `REAPER_GUEST`, which the Tool does
/// not host. It reaps the root with the kernel's own `wait4`, and the kernel
/// copies the wait status into the parent's memory; the parent then writes
/// what it received to its fd 1, which a capture-only [`StdoutTap`] records.
#[derive(Clone, Copy)]
struct RootReap {
    /// The reaping parent's identity.
    parent: Root,
    /// What the parent's `wait4(-1, &status, 0, NULL)` returned.
    reaped_pid: i64,
    /// The status word that `wait4` stored in the parent's memory.
    wstatus: i32,
    /// What the parent's second `wait4` returned: `-ECHILD` once its only
    /// child has been reaped.
    second_wait: i64,
    /// The termination status staged for the root when its exit was
    /// announced, read without consuming it; `None` if nothing was staged.
    staged: Option<i32>,
    /// The same for the reaping parent's own exit.
    parent_staged: Option<i32>,
}

/// Sentinels for the staged-termination slots, outside the `i32` range.
const NOT_SEEN: i64 = i64::MIN;
const NOTHING_STAGED: i64 = i64::MIN + 2;
/// The pids whose staged terminations [`record_staged_terminations`] reads.
static ROOT_WATCH: AtomicU64 = AtomicU64::new(0);
static ROOT_STAGED: AtomicI64 = AtomicI64::new(NOT_SEEN);
static PARENT_WATCH: AtomicU64 = AtomicU64::new(0);
static PARENT_STAGED: AtomicI64 = AtomicI64::new(NOT_SEEN);

/// Checks and removes what the reaping parent left once the run is over.
///
/// The parent's reap drops the root's link and the parent's child count, and
/// charges the root's CPU time to the parent's child-CPU row. Returns the
/// nanoseconds that row held.
fn release_reaping_parent(parent_task: u64, root_pid: u64) -> Result<u64, &'static str> {
    use narf_userspace::handlers::{
        __test_clear_pending_exits, __test_parent_link, account_reaped_child,
    };
    let linked = __test_parent_link(root_pid).is_some();
    let mut status = 0i32;
    let queued =
        narf_userspace::user_task::call_wait_child_check(parent_task, -1, LINUX_WALL, &mut status);
    __test_clear_pending_exits(parent_task);
    // With parent 0 this charges nobody; it drops the row's own CPU entries.
    let charged = account_reaped_child(0, parent_task);
    if linked {
        return Err("the root's link to its reaping parent survived the run");
    }
    if queued != 0 {
        return Err("the reaping parent still had a reapable child after the run");
    }
    if account_reaped_child(0, parent_task) != 0 {
        return Err("the reaping parent's child-CPU row survived teardown");
    }
    Ok(charged)
}

/// Thread-exit observer: reads the staged termination status of the root and
/// of its reaping parent. Thread observers run before the process observer
/// that consumes it for the reap.
fn record_staged_terminations(pid: u64, _tid: u64) {
    for (watch, slot) in [(&ROOT_WATCH, &ROOT_STAGED), (&PARENT_WATCH, &PARENT_STAGED)] {
        if pid == 0 || pid != watch.load(Ordering::Acquire) {
            continue;
        }
        let staged = narf_userspace::handlers::peek_pending_termination(pid)
            .map_or(NOTHING_STAGED, i64::from);
        let _ = slot.compare_exchange(NOT_SEEN, staged, Ordering::AcqRel, Ordering::Acquire);
    }
}

fn staged_of(slot: &AtomicI64, missing: &'static str) -> Result<Option<i32>, &'static str> {
    match slot.load(Ordering::Acquire) {
        NOT_SEEN => Err(missing),
        NOTHING_STAGED => Ok(None),
        status => Ok(Some(status as i32)),
    }
}

/// Grace periods [`run_guest`] may drive while reclaiming a run's address
/// spaces. Reclaiming a task takes one; the address-space destructors it runs
/// may retire more, which the next one reclaims.
const RECLAIM_GRACE_PERIODS: u32 = 4;
/// Budget for one of those grace periods.
const RECLAIM_GRACE_PERIOD_NS: u64 = 1_000_000_000;

/// Every distinct address space a task of the current run exited from: the
/// root's and each forked or vforked child's.
static EXITED_SPACES: IrqSafeSpinLock<Vec<Weak<AddressSpace>>> = IrqSafeSpinLock::new(Vec::new());

/// Thread-exit observer: records the exiting task's address space, which is
/// still the active one while its exit fans out.
fn record_exiting_space(_pid: u64, _tid: u64) {
    let Some(space) = narf_scheduler::current_address_space() else {
        return;
    };
    let mut spaces = EXITED_SPACES.lock();
    if !spaces
        .iter()
        .any(|seen| seen.as_ptr() == Arc::as_ptr(&space))
    {
        spaces.push(Arc::downgrade(&space));
    }
}

/// How many distinct address spaces the last successful [`run_guest`] saw
/// tasks exit from, all of which it proved reclaimed.
static RECLAIMED_SPACES: AtomicU64 = AtomicU64::new(0);

fn exited_space_count() -> u64 {
    RECLAIMED_SPACES.load(Ordering::Acquire)
}

/// Waits until nothing of a finished run is left: every address space its
/// tasks exited from has been dropped, and no frame of the root image still
/// has a recorded COW owner.
///
/// A reaped task is not yet reclaimed. The scheduler retires its stackful
/// continuation through RCU, and that continuation owns the future holding the
/// task's address space, so the space outlives the task by one grace period.
/// In the kernel the executor keeps running and its per-round
/// `advance_epoch_if_pending` ends that grace period. `run_until_empty`
/// returns as soon as the run queue drains, so the grace period must be driven
/// here; otherwise the spaces survive into the next test, still sharing COW
/// frames, and any reset of the COW table in between turns their eventual
/// frees into double frees.
fn reclaim_run(spaces: &[Weak<AddressSpace>], frames: &[PhysAddr]) -> Result<(), &'static str> {
    let reclaimed = || {
        spaces.iter().all(|space| space.strong_count() == 0)
            && frames
                .iter()
                .all(|frame| narf_memory::frame::cow::count(*frame) == 0)
    };
    let mut periods = 0;
    while !reclaimed() {
        if periods == RECLAIM_GRACE_PERIODS {
            return Err("the guest's address spaces or COW frames outlived the reclaim grace-period budget after its tasks were reaped");
        }
        let deadline = narf_time::monotonic_ns().saturating_add(RECLAIM_GRACE_PERIOD_NS);
        if !narf_rcu::sync_until(deadline) {
            return Err("an RCU grace period did not elapse within 1 s while reclaiming the guest's address spaces");
        }
        periods += 1;
    }
    Ok(())
}

/// Runs `elf` as a fresh scheduled user process with `interceptor` installed
/// in the live syscall table, until every task it created has been reaped.
///
/// `register` runs after the root task has its Linux identity and before it
/// is runnable. The root is an orphan, which the kernel releases at exit.
fn run_guest(
    elf: &[u8],
    interceptor: Box<dyn SyscallInterceptor>,
    register: impl FnOnce(Root) -> Result<(), &'static str>,
) -> Result<Root, &'static str> {
    run_guest_with(elf, interceptor, register, None).map(|(root, _)| root)
}

/// [`run_guest`], optionally with a reaping parent.
///
/// With `reaper`, that ELF is loaded as a second process, which the
/// interceptor does not host, and the root is published as its child with
/// exit signal `SIGCHLD` before either runs. The root's exit then queues a
/// wait status for that parent instead of releasing the root, and the parent
/// reaps it with its own `wait4`; the harness only watches both exit. The
/// parent's fd 1 is a capture-only [`StdoutTap`], and what the parent wrote
/// there is decoded into the returned [`RootReap`].
fn run_guest_with(
    elf: &[u8],
    interceptor: Box<dyn SyscallInterceptor>,
    register: impl FnOnce(Root) -> Result<(), &'static str>,
    reaper: Option<&[u8]>,
) -> Result<(Root, Option<RootReap>), &'static str> {
    use narf_userspace::syscall::__verification_clear_global as clear_global;
    use narf_userspace::{install_core_syscalls, install_global, install_task_id_lookup};

    let cpu = narf_lib::percpu::current_cpu();
    let original_cr3: u64;
    // SAFETY: reading CR3 has no side effects.
    unsafe {
        core::arch::asm!("mov {v}, cr3", v = out(reg) original_cr3,
            options(nostack, preserves_flags));
    }
    clear_global();
    narf_userspace::user_task::__test_clear_hooks();
    // Kernel-test boots skip the boot-time userspace init, so install the
    // pieces a forking, reaping guest needs, as the boot path does: the
    // wait/exit bookkeeping (which stages each exit's wait status) with its
    // exit observers, and the current task's address-space lookup.
    narf_userspace::user_task::__test_clear_exit_observers();
    narf_userspace::handlers::__test_wait_reset();
    narf_userspace::handlers::wait_init();
    EXITED_SPACES.lock().clear();
    RECLAIMED_SPACES.store(0, Ordering::Release);
    narf_userspace::user_task::register_thread_exit_observer(record_exiting_space);
    ROOT_WATCH.store(0, Ordering::Release);
    ROOT_STAGED.store(NOT_SEEN, Ordering::Release);
    PARENT_WATCH.store(0, Ordering::Release);
    PARENT_STAGED.store(NOT_SEEN, Ordering::Release);
    if reaper.is_some() {
        narf_userspace::user_task::register_thread_exit_observer(record_staged_terminations);
    }
    let original_as_lookup = narf_userspace::address_space_lookup();
    narf_userspace::install_address_space_lookup(|| {
        narf_scheduler::current_address_space()
            .or_else(|| narf_scheduler::address_space_of(narf_scheduler::current_task_id()))
    });

    let mut table = narf_userspace::SyscallTable::new();
    install_core_syscalls(&mut table);
    if table.install_interceptor(interceptor).is_err() {
        return Err("a fresh syscall table already had an interceptor");
    }
    install_global(table);
    install_task_id_lookup(|| narf_scheduler::current_task_id().raw());
    narf_scheduler::__reset_queues_for_test();
    narf_userspace::install_user_task_hooks();

    let teardown = |original_cr3: u64| {
        // SAFETY: restore the kernel CR3 and kernel-GS state after the user
        // tasks have exited, matching the neighbouring scheduled-user smokes.
        unsafe {
            core::arch::asm!("mov cr3, {value}", value = in(reg) original_cr3,
                options(nostack, preserves_flags));
            const IA32_KERNEL_GS_BASE: u32 = 0xC0000102;
            core::arch::asm!(
                "wrmsr",
                in("ecx") IA32_KERNEL_GS_BASE,
                in("eax") 0u32,
                in("edx") 0u32,
                options(nostack, preserves_flags),
            );
            core::arch::asm!("cli", options(nomem, nostack, preserves_flags));
        }
        narf_userspace::user_task::__test_clear_hooks();
        narf_userspace::handlers::__test_reset_task_id_lookup();
        narf_userspace::restore_address_space_lookup(original_as_lookup);
        narf_userspace::user_task::__test_clear_exit_observers();
        narf_userspace::handlers::__test_wait_reset();
        clear_global();
    };

    // SAFETY: paging and the frame allocator are live in the kernel-test
    // environment; the image is a complete static ELF.
    let process = match unsafe { narf_userspace::load_user_process_with(elf, &[], &[], &[]) } {
        Ok(process) => process,
        Err(_) => {
            teardown(original_cr3);
            return Err("the guest ELF failed to load");
        }
    };
    let pid = process.pid.raw();
    let root_space = Arc::downgrade(&process.address_space);
    let root_frames = process
        .address_space
        .regions_snapshot()
        .into_iter()
        .filter(|region| !region.perms.contains(RegionPerms::SHARED))
        .flat_map(|region| region.phys)
        .filter(|frame| frame.raw() != 0)
        .collect::<Vec<_>>();
    let live_before = narf_scheduler::live_user_task_count();
    let mut spec = TaskSpec::user_task();
    spec.affinity = Affinity::pinned(CpuId(cpu as u32));
    let pending = narf_userspace::user_task::prepare_user_process_initial(process, spec);
    let task_id = pending.task_id().raw();
    narf_userspace::handlers::register_pid_task_mapping(pid, task_id);
    let root = Root { task_id, pid };
    if let Err(reason) = register(root) {
        let _ = narf_userspace::task::release_task(task_id);
        teardown(original_cr3);
        return Err(reason);
    }
    let mut parent = None;
    if let Some(reaper_elf) = reaper {
        // SAFETY: as for the root image above.
        let process =
            match unsafe { narf_userspace::load_user_process_with(reaper_elf, &[], &[], &[]) } {
                Ok(process) => process,
                Err(_) => {
                    let _ = narf_userspace::task::release_task(task_id);
                    teardown(original_cr3);
                    return Err("the reaping-parent guest ELF failed to load");
                }
            };
        let parent_pid = process.pid.raw();
        let mut spec = TaskSpec::user_task();
        spec.affinity = Affinity::pinned(CpuId(cpu as u32));
        let parent_pending = narf_userspace::user_task::prepare_user_process_initial(process, spec);
        let parent_task = parent_pending.task_id().raw();
        narf_userspace::handlers::register_pid_task_mapping(parent_pid, parent_task);
        let tap = match tap_console(parent_task, false) {
            Ok(tap) => tap,
            Err(reason) => {
                let _ = narf_userspace::task::release_task(parent_task);
                let _ = narf_userspace::task::release_task(task_id);
                teardown(original_cr3);
                return Err(reason);
            }
        };
        ROOT_WATCH.store(pid, Ordering::Release);
        PARENT_WATCH.store(parent_pid, Ordering::Release);
        narf_userspace::handlers::__test_parent_of_set_with_signal(pid, parent_task, LINUX_SIGCHLD);
        parent = Some((
            Root {
                task_id: parent_task,
                pid: parent_pid,
            },
            tap,
        ));
        // The parent runs first, so its wait4 finds a living child and blocks.
        parent_pending.spawn();
    }
    pending.spawn();

    static WAITER_TIMED_OUT: AtomicU64 = AtomicU64::new(0);
    WAITER_TIMED_OUT.store(0, Ordering::Release);
    let deadline = narf_time::Instant::now().plus_cycles(WAITER_BUDGET_CYCLES);
    narf_scheduler::spawn(async move {
        loop {
            if narf_scheduler::live_user_task_count() <= live_before {
                return;
            }
            if narf_time::Instant::now() >= deadline {
                WAITER_TIMED_OUT.store(1, Ordering::Release);
                return;
            }
            narf_scheduler::yield_now().await;
        }
    });
    narf_scheduler::run_until_empty();
    // Before `teardown`, whose wait-table reset would hide a leftover link.
    let released = parent
        .as_ref()
        .map(|(parent, _)| release_reaping_parent(parent.task_id, pid));
    teardown(original_cr3);

    if WAITER_TIMED_OUT.load(Ordering::Acquire) != 0 {
        return Err("the guest's tasks were not reaped within the budget");
    }
    let reap = match parent {
        None => None,
        Some((parent, tap)) => {
            let report = tap.captured.lock().clone();
            if report.len() != REAPER_REPORT_LEN {
                let _ = writeln!(Writer, "    reaping parent wrote {} bytes", report.len());
                return Err("the reaping parent did not write its 16-byte wait4 report");
            }
            let word = |range: core::ops::Range<usize>| {
                let mut bytes = [0u8; 4];
                bytes.copy_from_slice(&report[range]);
                i32::from_le_bytes(bytes)
            };
            let mut pid_bytes = [0u8; 8];
            pid_bytes.copy_from_slice(&report[0..8]);
            let staged = staged_of(
                &ROOT_STAGED,
                "the root's exit never reached the thread-exit observers",
            )?;
            let parent_staged = staged_of(
                &PARENT_STAGED,
                "the reaping parent's exit never reached the thread-exit observers",
            )?;
            let charged = released.ok_or("the reaping parent was never released")??;
            let _ = writeln!(
                Writer,
                "    reaping parent released; child-CPU row held {charged} ns"
            );
            Some(RootReap {
                parent,
                reaped_pid: i64::from_le_bytes(pid_bytes),
                wstatus: word(8..12),
                second_wait: i64::from(word(12..16)),
                staged,
                parent_staged,
            })
        }
    };
    let spaces = core::mem::take(&mut *EXITED_SPACES.lock());
    if !spaces.iter().any(|space| space.ptr_eq(&root_space)) {
        return Err("the root task's exit did not report its address space");
    }
    reclaim_run(&spaces, &root_frames)?;
    RECLAIMED_SPACES.store(spaces.len() as u64, Ordering::Release);
    Ok((root, reap))
}

/// Runs `elf` with Tool `T` hosted for the whole process tree.
fn run_hosted<T: Tool + 'static>(
    elf: &[u8],
    config: <T::GlobalState as reverie::GlobalTool>::Config,
) -> Result<(ReverieInterceptor<T>, Root), &'static str> {
    let interceptor = match ReverieInterceptor::<T>::new(config) {
        Ok(interceptor) => interceptor,
        Err(_) => return Err("NarfToolHost::new refused the Tool"),
    };
    let root = run_guest(elf, interceptor.boxed(), |root| {
        interceptor
            .host_root(root.task_id)
            .map_err(|_| "register_root refused the root task")
    })?;
    Ok((interceptor, root))
}

/// The checks every hosted run must pass: the root was reaped with
/// `root_status`, every hosted task's exit reached the host exactly once, and
/// the host tore every task down.
fn check_teardown<T: Tool + 'static>(
    interceptor: &ReverieInterceptor<T>,
    root: Root,
    expected_exits: usize,
    root_status: i32,
) -> Result<Vec<TaskExitRecord>, &'static str> {
    let exits = interceptor.exits();
    if exits.len() != expected_exits {
        let _ = writeln!(
            Writer,
            "    expected {expected_exits} task exits, host saw {}",
            exits.len()
        );
        let _ = writeln!(
            Writer,
            "    host live threads {} processes {}, interceptor hosts {}",
            interceptor.host().live_threads(),
            interceptor.host().live_processes(),
            interceptor.hosted_tasks()
        );
        for exit in &exits {
            let _ = writeln!(
                Writer,
                "    exit task {} tid {} wstatus {:#x} process_exited {}",
                exit.task_id,
                exit.tid.as_raw(),
                exit.wstatus,
                exit.process_exited
            );
        }
        return Err("the host did not see every task exit exactly once");
    }
    let Some(root_exit) = exits.iter().find(|exit| exit.task_id == root.task_id) else {
        return Err("the root task's exit never reached the host");
    };
    if root_exit.tid != Pid::from_raw(root.pid as i32) {
        return Err("the root's exit was reported under a tid other than its Linux pid");
    }
    if root_exit.wstatus != root_status {
        let _ = writeln!(Writer, "    root wstatus {:#x}", root_exit.wstatus);
        return Err("the root exited with an unexpected status");
    }
    if interceptor.host().live_threads() != 0 || interceptor.host().live_processes() != 0 {
        return Err("the host still tracks tasks after every task exited");
    }
    if interceptor.hosted_tasks() != 0 {
        return Err("the interceptor still forwards for a reaped task");
    }
    Ok(exits)
}

fn result_of(outcome: Result<TestResult, &'static str>) -> TestResult {
    match outcome {
        Ok(result) => result,
        Err(reason) => TestResult::Fail(reason),
    }
}

// ── Identity, registers, memory and the one-shot original ────────────────

static PROBE_TASK: AtomicU64 = AtomicU64::new(0);
static SEEN_WRITES: AtomicU64 = AtomicU64::new(0);
/// Bitmask of failed identity/register/memory checks; 0 when all held.
static VIEW_FAILURES: AtomicU64 = AtomicU64::new(0);
static FIRST_ORIGINAL: AtomicI64 = AtomicI64::new(i64::MIN);
/// 1 = `Ok(Returned(_))`, 2 = `Err(AlreadyExecuted)`, 3 = `Err(ContextManaged)`,
/// 4 = `Ok(ContextManaged)`.
static SECOND_ORIGINAL: AtomicU64 = AtomicU64::new(0);
static PROBE_EXIT: AtomicI64 = AtomicI64::new(i64::MIN);

/// Drives [`NarfKernelServices`] directly from the guest's `write`: checks
/// the Linux view it presents, then asks for the original twice.
struct ServicesProbe;

impl SyscallInterceptor for ServicesProbe {
    fn on_syscall_enter(
        &self,
        invocation: &SyscallInvocation,
        native: &mut dyn NativeSyscallTransition,
    ) -> SyscallInterception {
        let task_id = invocation.task_id;
        if task_id != PROBE_TASK.load(Ordering::Acquire)
            || invocation.raw_number & reverie_narf_core::NARF_SYSCALL_NUMBER_MASK != LINUX_WRITE
        {
            return SyscallInterception::Continue;
        }
        SEEN_WRITES.fetch_add(1, Ordering::AcqRel);
        let Some(ids) = tool_view::linux_task_ids(task_id) else {
            VIEW_FAILURES.fetch_or(1, Ordering::AcqRel);
            return SyscallInterception::Continue;
        };
        let mut kernel = NarfKernelServices::new(native, task_id, ids, Some(invocation.raw_number));

        let mut failures = 0u64;
        let pid = Pid::from_raw(ids.pid as i32);
        // A thread-group leader's tid is its pid, and neither is the
        // scheduler's task id.
        if kernel.tid() != pid || kernel.pid() != pid {
            failures |= 1 << 1;
        }
        if kernel.tid().as_raw() as u64 == task_id {
            failures |= 1 << 2;
        }
        if kernel.ppid().is_some() {
            failures |= 1 << 3;
        }
        let regs = kernel.regs();
        if regs.orig_rax != u64::from(LINUX_WRITE) || regs.rax != (-38i64) as u64 {
            failures |= 1 << 4;
        }
        if regs.rdi != 1 || regs.rsi != CANONICAL_MESSAGE_ADDR || regs.rdx != 16 {
            failures |= 1 << 5;
        }
        if !CANONICAL_TEXT.contains(&regs.rip) || regs.cs != 0x33 || regs.ss != 0x2b {
            failures |= 1 << 6;
        }
        let mut message = [0u8; 16];
        let read = Addr::<u8>::from_raw(regs.rsi as usize)
            .ok_or(reverie::syscalls::Errno::EFAULT)
            .and_then(|addr| kernel.memory().read_exact(addr, &mut message));
        if read.is_err() || &message != CANONICAL_MESSAGE {
            failures |= 1 << 7;
        }
        VIEW_FAILURES.fetch_or(failures, Ordering::AcqRel);

        match kernel.execute_original() {
            Ok(NarfSyscallOutcome::Returned(value)) => {
                FIRST_ORIGINAL.store(value, Ordering::Release)
            }
            _ => FIRST_ORIGINAL.store(i64::MIN + 1, Ordering::Release),
        }
        let second = match kernel.execute_original() {
            Ok(NarfSyscallOutcome::Returned(_)) => 1,
            Err(OriginalSyscallError::AlreadyExecuted) => 2,
            Err(OriginalSyscallError::ContextManaged) => 3,
            Ok(NarfSyscallOutcome::ContextManaged) => 4,
        };
        SECOND_ORIGINAL.store(second, Ordering::Release);
        SyscallInterception::Continue
    }

    fn on_task_exit(&self, task_id: u64, _pid: u64, wstatus: i32) {
        if task_id == PROBE_TASK.load(Ordering::Acquire) {
            PROBE_EXIT.store(i64::from(wstatus), Ordering::Release);
        }
    }
}

/// The services a Tool callback gets report the task's root-namespace Linux
/// identity (not its scheduler id), Linux entry registers with `orig_rax`
/// set to the syscall number, and the task's memory; and the kernel runs the
/// original syscall at most once however often it is asked.
fn reverie_narf_services_view_and_one_shot_original() -> TestResult {
    PROBE_TASK.store(0, Ordering::Release);
    SEEN_WRITES.store(0, Ordering::Release);
    VIEW_FAILURES.store(0, Ordering::Release);
    FIRST_ORIGINAL.store(i64::MIN, Ordering::Release);
    SECOND_ORIGINAL.store(0, Ordering::Release);
    PROBE_EXIT.store(i64::MIN, Ordering::Release);
    result_of((|| {
        run_guest(CANONICAL_GUEST, Box::new(ServicesProbe), |root| {
            PROBE_TASK.store(root.task_id, Ordering::Release);
            Ok(())
        })?;
        if SEEN_WRITES.load(Ordering::Acquire) != 1 {
            return Err("the guest's write did not reach the interceptor exactly once");
        }
        let failures = VIEW_FAILURES.load(Ordering::Acquire);
        if failures != 0 {
            let _ = writeln!(Writer, "    services view failures {failures:#x}");
            return Err("the services' identity, registers or memory were wrong");
        }
        if FIRST_ORIGINAL.load(Ordering::Acquire) != 16 {
            return Err("the first execute_original did not return write's 16");
        }
        match SECOND_ORIGINAL.load(Ordering::Acquire) {
            2 => {}
            1 => return Err("the kernel executed the original syscall twice"),
            _ => return Err("the second execute_original did not report AlreadyExecuted"),
        }
        if PROBE_EXIT.load(Ordering::Acquire) != 0 {
            return Err("the guest did not exit 0 after the one-shot original");
        }
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!(
    "reverie-narf",
    reverie_narf_services_view_and_one_shot_original
);

// ── Unmodified Tools ──────────────────────────────────────────────────────

/// counter1, unmodified from reverie-examples, counts the canonical guest's
/// two syscalls (write, exit) through its global state, and the task's exit
/// tears its state down in the host exactly once.
fn reverie_narf_counter1_counts_and_tears_down() -> TestResult {
    result_of((|| {
        let (interceptor, root) = run_hosted::<CounterLocal>(CANONICAL_GUEST, ())?;
        let exits = check_teardown(&interceptor, root, 1, 0)?;
        if !exits[0].process_exited {
            return Err("the root's exit did not end its process in the host");
        }
        let total = interceptor.host().global().total();
        if total != 2 {
            let _ = writeln!(Writer, "    counter1 total {total}");
            return Err("counter1 did not count exactly write and exit");
        }
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!("reverie-narf", reverie_narf_counter1_counts_and_tears_down);

/// counter1 follows a process tree: fork and vfork children are registered
/// before their first instruction, their syscalls reach the Tool, and every
/// task's exit reaches the host once. The guest checks each child's wait
/// status itself and exits 0 only if both are right.
fn reverie_narf_counter1_follows_fork_and_vfork() -> TestResult {
    result_of((|| {
        let (interceptor, root) = run_hosted::<CounterLocal>(FORK_GUEST, ())?;
        let exits = check_teardown(&interceptor, root, 3, 0)?;
        if exits.iter().filter(|exit| exit.process_exited).count() != 3 {
            return Err("each of the three processes did not end exactly once");
        }
        // Narf implements vfork as a copy, so the tree has three address
        // spaces, and run_guest proved each one reclaimed.
        if exited_space_count() != 3 {
            let _ = writeln!(Writer, "    exited address spaces {}", exited_space_count());
            return Err("the run did not reclaim the parent's, fork child's and vfork child's address spaces");
        }
        let children = exits
            .iter()
            .filter(|exit| exit.task_id != root.task_id)
            .map(|exit| exit.wstatus)
            .collect::<Vec<_>>();
        if children != [0x0700, 0x0900] {
            let _ = writeln!(Writer, "    child wstatus {children:x?}");
            return Err("the children did not exit 7 (fork) then 9 (vfork)");
        }
        // Parent: fork, wait4, vfork, wait4, exit; each child: exit.
        let total = interceptor.host().global().total();
        if total != 7 {
            let _ = writeln!(Writer, "    counter1 total {total}");
            return Err("counter1 did not count the tree's seven syscalls");
        }
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!("reverie-narf", reverie_narf_counter1_follows_fork_and_vfork);

/// Probe returns `getpid() + 5` from a non-tail inject, which the guest
/// checks against `gettid()`; its per-thread state persists across the
/// thread's three syscalls and its RPCs reach the global state directly.
fn reverie_narf_probe_inject_and_thread_state() -> TestResult {
    result_of((|| {
        let (interceptor, root) = run_hosted::<Probe>(PROBE_GUEST, ())?;
        check_teardown(&interceptor, root, 1, 0)?;
        let global = interceptor.host().global();
        if global.events() != 3 || global.thread_state_sum() != 1 + 2 + 3 {
            let _ = writeln!(
                Writer,
                "    probe events {} thread-state sum {}",
                global.events(),
                global.thread_state_sum()
            );
            return Err("Probe's global state did not see getpid, gettid and exit in order");
        }
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!("reverie-narf", reverie_narf_probe_inject_and_thread_state);

/// PassThrough tail-injects every syscall; the guest's own check that
/// write returned 16 is what makes it exit 0.
fn reverie_narf_passthrough_runs_guest_unchanged() -> TestResult {
    result_of((|| {
        let (interceptor, root) = run_hosted::<PassThrough>(CANONICAL_GUEST, ())?;
        check_teardown(&interceptor, root, 1, 0)?;
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!(
    "reverie-narf",
    reverie_narf_passthrough_runs_guest_unchanged
);

/// Wraps the root's fd-1 console file: forwards every call to it unchanged and
/// keeps a copy of the bytes its `write` accepted.
///
/// The serial line is not byte evidence of the guest's output: the console
/// writer emits each byte as a `char`, so a byte above 0x7f leaves as two, and
/// the line interleaves the guest's bytes with everything else the kernel
/// prints. The copy is taken where the guest's `write` hands its bytes to the
/// console file.
///
/// A capture-only tap (`forward == false`) accepts every byte without passing
/// it on, for output that is binary and must not reach the serial line.
struct StdoutTap {
    console: Arc<dyn FileOps>,
    forward: bool,
    captured: IrqSafeSpinLock<Vec<u8>>,
}

impl FileOps for StdoutTap {
    fn read<'a>(&'a self, offset: u64, buf: &'a mut [u8]) -> FsFuture<'a, usize> {
        self.console.read(offset, buf)
    }

    fn write<'a>(&'a self, offset: u64, buf: &'a [u8]) -> FsFuture<'a, usize> {
        if !self.forward {
            self.captured.lock().extend_from_slice(buf);
            return Box::pin(async move { Ok(buf.len()) });
        }
        let accepted = self.console.write(offset, buf);
        Box::pin(async move {
            let n = accepted.await?;
            self.captured.lock().extend_from_slice(&buf[..n]);
            Ok(n)
        })
    }

    fn stat(&self) -> Stat {
        self.console.stat()
    }

    fn block_on_input(&self) -> bool {
        self.console.block_on_input()
    }

    fn poll_readiness(&self) -> u32 {
        self.console.poll_readiness()
    }

    fn tty_id(&self) -> Option<u32> {
        self.console.tty_id()
    }

    fn tty_fg_pgrp(&self) -> Option<u64> {
        self.console.tty_fg_pgrp()
    }

    fn tty_tostop(&self) -> bool {
        self.console.tty_tostop()
    }

    fn ioctl(&self, cmd: u32, arg: usize) -> Result<u64, FsError> {
        self.console.ioctl(cmd, arg)
    }
}

/// Puts a forwarding [`StdoutTap`] in front of `task_id`'s fd 1.
fn tap_stdout(task_id: u64) -> Result<Arc<StdoutTap>, &'static str> {
    tap_console(task_id, true)
}

/// Puts a [`StdoutTap`] in front of `task_id`'s fd 1, which must still be the
/// console file of a fresh descriptor table: one object behind fds 1 and 2,
/// a character device, the boot console's tty.
fn tap_console(task_id: u64, forward: bool) -> Result<Arc<StdoutTap>, &'static str> {
    narf_userspace::fd::with_table(task_id, |table| {
        let (Some(stdout), Some(stderr)) = (table.get(1), table.get(2)) else {
            return Err("the root's descriptor table has no fd 1 or fd 2");
        };
        if !Arc::ptr_eq(&stdout.ops, &stderr.ops)
            || stdout.ops.stat().mode.file_type != narf_filesystem::FileType::Special
            || stdout.ops.tty_id() != Some(narf_filesystem::TTY_ID_CONSOLE)
        {
            return Err("the root's fd 1 is not the fresh table's console file");
        }
        let mut entry = stdout.clone();
        let tap = Arc::new(StdoutTap {
            console: entry.ops.clone(),
            forward,
            captured: IrqSafeSpinLock::new(Vec::new()),
        });
        entry.ops = tap.clone();
        table.set(1, entry);
        Ok(tap)
    })
    .ok_or("the root's descriptor table was unavailable")?
}

/// The N cell of the Linux/Narf parity comparison: the shared canonical-trace
/// Tool, unchanged, writes its records to the kernel console. This is the
/// only test that emits canonical records.
///
/// It also prints the cell's other two observables, each exactly once, for
/// the external comparator: the bytes the guest wrote to fd 1, captured by a
/// [`StdoutTap`], and the root's wait status as its reaping parent, a real
/// guest process, received it from its own `wait4`. Their expected values
/// live in the comparator, not here. The records lie between the
/// [`CELL_BEGIN`] and [`CELL_RECORDS_END`] lines, which the comparator uses
/// to reject records printed by anything else.
fn reverie_narf_canonical_trace_cell() -> TestResult {
    let _ = writeln!(Writer, "{CELL_BEGIN}");
    result_of((|| {
        let interceptor = ReverieInterceptor::<CanonicalTrace<ConsoleSink>>::new(())
            .map_err(|_| "NarfToolHost::new refused the Tool")?;
        let mut tap = None;
        let (root, reap) = run_guest_with(
            CANONICAL_GUEST,
            interceptor.boxed(),
            |root| {
                tap = Some(tap_stdout(root.task_id)?);
                interceptor
                    .host_root(root.task_id)
                    .map_err(|_| "register_root refused the root task")
            },
            Some(REAPER_GUEST),
        )?;
        let _ = writeln!(Writer, "{CELL_RECORDS_END}");
        let tap = tap.ok_or("the root's fd 1 was never tapped")?;
        let reap = reap.ok_or("the run did not reap its root")?;
        let captured = tap.captured.lock().clone();
        let mut line = alloc::string::String::new();
        for byte in &captured {
            let _ = write!(line, "{byte:02x}");
        }
        let _ = writeln!(
            Writer,
            "NARF-CELL stdout-capture=fd1-tap bytes={} hex={line}",
            captured.len()
        );
        if reap.reaped_pid != root.pid as i64 {
            let _ = writeln!(
                Writer,
                "    reaping parent's wait4 returned {}",
                reap.reaped_pid
            );
            return Err("the reaping parent's wait4 did not return the root's pid");
        }
        if reap.wstatus == REAPER_STATUS_SENTINEL {
            return Err("the reaping parent's wait4 reaped the root but stored no status");
        }
        let _ = writeln!(
            Writer,
            "NARF-CELL exit wstatus={:#06x} source=guest-parent-wait4",
            reap.wstatus
        );
        if reap.second_wait != -LINUX_ECHILD {
            let _ = writeln!(Writer, "    second wait4 returned {}", reap.second_wait);
            return Err("the reaping parent's second wait4 did not report ECHILD");
        }
        if reap.parent_staged != Some(0) {
            let _ = writeln!(Writer, "    reaping parent staged {:?}", reap.parent_staged);
            return Err("the reaping parent did not exit 0");
        }
        if reap.parent.pid == root.pid {
            return Err("the reaping parent and the root share a pid");
        }
        if reap.staged != Some(reap.wstatus) {
            let _ = writeln!(Writer, "    staged termination {:?}", reap.staged);
            return Err("the reaped wait status differs from the termination staged at exit");
        }
        let exits = check_teardown(&interceptor, root, 1, reap.wstatus)?;
        if exits.len() != 1 || !exits[0].process_exited {
            return Err("the root's exit did not end its process in the host");
        }
        if reap.wstatus != 0 {
            return Err("the root did not exit 0");
        }
        Ok(TestResult::Pass)
    })())
}
kernel_test_in!("reverie-narf", reverie_narf_canonical_trace_cell);

/// Marks where the cell's canonical records may begin on the console.
const CELL_BEGIN: &str = "NARF-CELL begin test=reverie_narf_canonical_trace_cell";
/// Printed once the cell's run is over; every record precedes it.
const CELL_RECORDS_END: &str = "NARF-CELL records-end";

// ── Return mapping ────────────────────────────────────────────────────────

/// A native result reaches the Tool as the value the guest would observe:
/// Narf's typed status is folded exactly as the syscall return path folds it.
fn reverie_narf_native_outcome_uses_linux_abi_fold() -> TestResult {
    let cases = [
        (SyscallReturn::ok(16), 16),
        (SyscallReturn::ok((-9i64) as u64), -9),
        // An unimplemented number keeps Linux's -ENOSYS in its value half.
        (SyscallReturn::not_implemented(), -38),
        // A failure status whose value is no errno folds to -EINVAL.
        (SyscallReturn::invalid_op(), -22),
    ];
    for (native, expected) in cases {
        if native.linux_abi_result() != expected {
            return TestResult::Fail("linux_abi_result changed its fold");
        }
        if map_native_outcome(NativeSyscallOutcome::Returned(native))
            != NarfSyscallOutcome::Returned(expected)
        {
            return TestResult::Fail("map_native_outcome diverged from the Linux-ABI fold");
        }
    }
    if map_native_outcome(NativeSyscallOutcome::ContextManaged)
        != NarfSyscallOutcome::ContextManaged
    {
        return TestResult::Fail("a context-managed outcome was not preserved");
    }
    TestResult::Pass
}
kernel_test_in!(
    "reverie-narf",
    reverie_narf_native_outcome_uses_linux_abi_fold
);
