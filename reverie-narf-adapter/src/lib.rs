//! Direct, in-kernel adapter between Narf interception and `reverie-narf-core`.
//!
//! The adapter owns one Tool, its process-tree global state, and one state value
//! per intercepted Narf task. It passes direct references into Tool callbacks;
//! no serialization or IPC transport exists in this path.

#![no_std]
#![forbid(unsafe_op_in_unsafe_fn)]

extern crate alloc;

use alloc::collections::BTreeMap;
use core::future::Future;
use core::pin::pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use narf_lib::sync::IrqSafeSpinLock;
use narf_userspace::syscall::{
    NativeSyscallOriginalError, NativeSyscallOutcome, NativeSyscallRequest,
    NativeSyscallTransition, SyscallArgs, SyscallInterception, SyscallInterceptor,
    SyscallInvocation, SyscallReturn,
};
use reverie_narf_core::{
    drive_syscall, DrivenSyscall, KernelTransition, NarfSyscallOutcome, NarfSyscallRequest,
    OriginalSyscallError, SyscallEvent, Tool,
};

enum ThreadSlot<S> {
    Ready(S),
    Active,
}

/// A Narf syscall interceptor hosting one generic kernel-compatible Tool.
pub struct ReverieInterceptor<T>
where
    T: Tool,
{
    tool: T,
    global: T::GlobalState,
    thread_states: IrqSafeSpinLock<BTreeMap<u64, ThreadSlot<T::ThreadState>>>,
}

impl<T> ReverieInterceptor<T>
where
    T: Tool,
{
    /// Creates one process-tree Tool instance with direct global state.
    pub const fn new(tool: T, global: T::GlobalState) -> Self {
        Self {
            tool,
            global,
            thread_states: IrqSafeSpinLock::new(BTreeMap::new()),
        }
    }

    /// Returns the Tool's process-tree singleton.
    pub fn global(&self) -> &T::GlobalState {
        &self.global
    }
}

impl<T> core::fmt::Debug for ReverieInterceptor<T>
where
    T: Tool,
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("ReverieInterceptor")
            .finish_non_exhaustive()
    }
}

struct Transition<'a> {
    native: &'a mut dyn NativeSyscallTransition,
}

impl KernelTransition for Transition<'_> {
    fn execute_original(&mut self) -> Result<NarfSyscallOutcome, OriginalSyscallError> {
        self.native
            .execute_original()
            .map(map_native_outcome)
            .map_err(|error| match error {
                NativeSyscallOriginalError::AlreadyExecuted => {
                    OriginalSyscallError::AlreadyExecuted
                }
                NativeSyscallOriginalError::ContextManaged => OriginalSyscallError::ContextManaged,
            })
    }

    fn execute_injected(&mut self, request: NarfSyscallRequest) -> NarfSyscallOutcome {
        map_native_outcome(self.native.execute_injected(NativeSyscallRequest::new(
            request.number,
            args(request.args),
        )))
    }
}

fn map_native_outcome(outcome: NativeSyscallOutcome) -> NarfSyscallOutcome {
    match outcome {
        NativeSyscallOutcome::Returned(result) => {
            NarfSyscallOutcome::Returned(result.linux_abi_result())
        }
        NativeSyscallOutcome::ContextManaged => NarfSyscallOutcome::ContextManaged,
    }
}

fn args(values: [u64; 6]) -> SyscallArgs {
    SyscallArgs {
        arg0: values[0],
        arg1: values[1],
        arg2: values[2],
        arg3: values[3],
        arg4: values[4],
        arg5: values[5],
    }
}

fn request(invocation: &SyscallInvocation) -> NarfSyscallRequest {
    NarfSyscallRequest {
        number: invocation.raw_number,
        args: [
            invocation.args.arg0,
            invocation.args.arg1,
            invocation.args.arg2,
            invocation.args.arg3,
            invocation.args.arg4,
            invocation.args.arg5,
        ],
    }
}

fn noop_raw_waker() -> RawWaker {
    unsafe fn clone(_: *const ()) -> RawWaker {
        noop_raw_waker()
    }
    unsafe fn no_op(_: *const ()) {}
    RawWaker::new(
        core::ptr::null(),
        &RawWakerVTable::new(clone, no_op, no_op, no_op),
    )
}

fn poll_ready<F: Future>(future: F) -> Option<F::Output> {
    // SAFETY: the no-op raw waker has no data and every vtable operation is a
    // no-op, so its static lifetime and clone/drop behavior are valid.
    let waker = unsafe { Waker::from_raw(noop_raw_waker()) };
    let mut context = Context::from_waker(&waker);
    let mut future = pin!(future);
    match future.as_mut().poll(&mut context) {
        Poll::Ready(output) => Some(output),
        Poll::Pending => None,
    }
}

impl<T> SyscallInterceptor for ReverieInterceptor<T>
where
    T: Tool + Send,
    T::GlobalState: Send,
    T::ThreadState: Default + Send,
{
    fn on_syscall_enter(
        &self,
        invocation: &SyscallInvocation,
        native: &mut dyn NativeSyscallTransition,
    ) -> SyscallInterception {
        let mut thread_state = {
            let mut states = self.thread_states.lock();
            match states.insert(invocation.task_id, ThreadSlot::Active) {
                Some(ThreadSlot::Ready(state)) => state,
                Some(ThreadSlot::Active) => {
                    panic!("reverie-narf recursively entered one task")
                }
                None => T::ThreadState::default(),
            }
        };

        let original = request(invocation);
        let event = SyscallEvent {
            request: original,
            task_id: invocation.task_id,
            instruction_pointer: invocation.instruction_pointer,
            stack_pointer: invocation.stack_pointer,
        };
        let mut transition = Transition { native };
        let outcome = poll_ready(drive_syscall(
            &self.tool,
            &self.global,
            &mut thread_state,
            &mut transition,
            event,
        ));

        {
            let mut states = self.thread_states.lock();
            match states.insert(invocation.task_id, ThreadSlot::Ready(thread_state)) {
                Some(ThreadSlot::Active) => {}
                _ => panic!("reverie-narf task-state ownership changed during callback"),
            }
        }

        match outcome {
            Some(DrivenSyscall::Complete(value)) => {
                SyscallInterception::Complete(SyscallReturn::ok(value as u64))
            }
            Some(DrivenSyscall::ContextManaged) => SyscallInterception::Continue,
            Some(DrivenSyscall::Fatal(class)) => {
                panic!("reverie-narf Tool stopped the run with fatal class {class}")
            }
            None => panic!("reverie-narf Tool suspended without a kernel wake source"),
        }
    }
}

mod tests {
    use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    use super::*;
    use narf_kernel_test::{kernel_test_in, TestResult};
    use reverie_narf_core::{Guest, ToolError};

    #[derive(Default)]
    struct Global {
        thread_state_sum: AtomicU64,
    }

    struct Probe;

    impl Tool for Probe {
        type GlobalState = Global;
        type ThreadState = u64;

        async fn handle_syscall<'a, K>(
            &'a self,
            guest: &'a mut Guest<'_, Self, K>,
            event: SyscallEvent,
        ) -> Result<i64, ToolError>
        where
            K: KernelTransition + 'a,
        {
            *guest.thread_state_mut() += 1;
            let state = *guest.thread_state();
            guest
                .global()
                .thread_state_sum
                .fetch_add(state, Ordering::Relaxed);
            Ok(guest.inject(event.request).await + 5)
        }
    }

    #[derive(Default)]
    struct Native {
        original_calls: AtomicUsize,
    }

    impl NativeSyscallTransition for Native {
        fn execute_original(&mut self) -> Result<NativeSyscallOutcome, NativeSyscallOriginalError> {
            if self.original_calls.fetch_add(1, Ordering::Relaxed) == 0 {
                Ok(NativeSyscallOutcome::Returned(SyscallReturn::ok(37)))
            } else {
                Err(NativeSyscallOriginalError::AlreadyExecuted)
            }
        }

        fn execute_injected(&mut self, _request: NativeSyscallRequest) -> NativeSyscallOutcome {
            NativeSyscallOutcome::Returned(SyscallReturn::ok(99))
        }
    }

    fn invocation(task_id: u64) -> SyscallInvocation {
        SyscallInvocation {
            raw_number: 39,
            version: 0,
            syscall: None,
            args: SyscallArgs::default(),
            task_id,
            instruction_pointer: 0x1000,
            stack_pointer: 0x2000,
        }
    }

    fn smoke_real_narf_transition_with_direct_persistent_state() -> TestResult {
        let interceptor = ReverieInterceptor::new(Probe, Global::default());

        for expected_sum in [1, 3] {
            let mut native = Native::default();
            let outcome = interceptor.on_syscall_enter(&invocation(7), &mut native);
            match outcome {
                SyscallInterception::Complete(result) if result.value as i64 == 42 => {}
                _ => return TestResult::Fail("Tool did not retain the expected return"),
            }
            if native.original_calls.load(Ordering::Relaxed) != 1 {
                return TestResult::Fail("native original did not execute exactly once");
            }
            if interceptor
                .global()
                .thread_state_sum
                .load(Ordering::Relaxed)
                != expected_sum
            {
                return TestResult::Fail("direct per-task state did not persist");
            }
        }
        TestResult::Pass
    }

    fn smoke_non_ok_native_status_matches_x86_linux_abi_result() -> TestResult {
        let native = SyscallReturn::not_implemented();
        let backend_off_rax = native.linux_abi_result();
        let backend_result = match map_native_outcome(NativeSyscallOutcome::Returned(native)) {
            NarfSyscallOutcome::Returned(value) => value,
            NarfSyscallOutcome::ContextManaged => {
                return TestResult::Fail("normal non-Ok return became context-managed");
            }
        };
        let backend_on_rax = SyscallReturn::ok(backend_result as u64).linux_abi_result();
        if backend_off_rax != -22 || backend_on_rax != backend_off_rax {
            return TestResult::Fail("adapter did not preserve the architecture status fold");
        }
        TestResult::Pass
    }

    kernel_test_in!(
        "reverie-narf",
        smoke_real_narf_transition_with_direct_persistent_state
    );
    kernel_test_in!(
        "reverie-narf",
        smoke_non_ok_native_status_matches_x86_linux_abi_result
    );
}
