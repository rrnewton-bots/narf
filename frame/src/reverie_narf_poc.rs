//! Fail-closed canonical-trace Tool for the bounded equivalence guest.

use core::fmt::Write;

use reverie_narf_adapter::ReverieInterceptor;
use reverie_narf_core::{Guest, KernelTransition, SyscallEvent, Tool, ToolError};

#[derive(Default)]
pub(crate) struct Global;

#[derive(Default)]
pub(crate) struct ThreadState {
    next_sequence: u64,
}

pub(crate) struct PassThrough;

impl Tool for PassThrough {
    type GlobalState = Global;
    type ThreadState = ThreadState;

    async fn handle_syscall<'a, K>(
        &'a self,
        guest: &'a mut Guest<'_, Self, K>,
        event: SyscallEvent,
    ) -> Result<i64, ToolError>
    where
        K: KernelTransition + 'a,
    {
        let sequence = guest.thread_state().next_sequence;
        guest.thread_state_mut().next_sequence += 1;
        match event.request.number {
            1 => {
                let _ = writeln!(
                    narf_console::Writer,
                    "INFO narf-hermit-canonical-v1 seq={sequence} phase=enter nr=1 a0={} a1=0x{:016x} a2={}",
                    event.request.args[0],
                    event.request.args[1],
                    event.request.args[2]
                );
                let result = guest.inject(event.request).await;
                let _ = writeln!(
                    narf_console::Writer,
                    "INFO narf-hermit-canonical-v1 seq={sequence} phase=return result={result}"
                );
                Ok(result)
            }
            60 => {
                let _ = writeln!(
                    narf_console::Writer,
                    "INFO narf-hermit-canonical-v1 seq={sequence} phase=enter nr=60 a0={}",
                    event.request.args[0]
                );
                Ok(guest.inject(event.request).await)
            }
            _ => Err(ToolError::Fatal(1)),
        }
    }
}

pub(crate) fn interceptor() -> ReverieInterceptor<PassThrough> {
    ReverieInterceptor::new(PassThrough, Global::default())
}
