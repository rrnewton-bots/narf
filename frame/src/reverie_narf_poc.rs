//! Minimal production-table Tool used while bringing up the Narf backend.

use core::fmt::Write;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use reverie_narf_adapter::ReverieInterceptor;
use reverie_narf_core::{Guest, KernelTransition, SyscallEvent, Tool, ToolError};

#[derive(Default)]
pub(crate) struct Global {
    callbacks: AtomicU64,
    announced: AtomicBool,
}

pub(crate) struct PassThrough;

impl Tool for PassThrough {
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
        guest.global().callbacks.fetch_add(1, Ordering::Relaxed);
        if !guest.global().announced.swap(true, Ordering::AcqRel) {
            let _ = writeln!(
                narf_console::Writer,
                "INFO reverie-narf-poc backend=v1 state=active"
            );
        }
        Ok(guest.inject(event.request).await)
    }
}

pub(crate) fn interceptor() -> ReverieInterceptor<PassThrough> {
    ReverieInterceptor::new(PassThrough, Global::default())
}
