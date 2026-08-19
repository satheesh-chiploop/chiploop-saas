// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    ClearFault,
    ReqPending,
    StaleFault,
    TimeoutFault,
    RangeFault,
}

#[inline]
pub fn interrupt_count() -> usize {
    5
}

pub const CLEAR_FAULT_BIT: u32 = 0;
pub const REQ_PENDING_BIT: u32 = 1;
pub const STALE_FAULT_BIT: u32 = 2;
pub const TIMEOUT_FAULT_BIT: u32 = 3;
pub const RANGE_FAULT_BIT: u32 = 4;

#[inline]
pub fn handle_clear_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_req_pending() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_stale_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_timeout_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_range_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        CLEAR_FAULT_BIT => { handle_clear_fault(); true }
        REQ_PENDING_BIT => { handle_req_pending(); true }
        STALE_FAULT_BIT => { handle_stale_fault(); true }
        TIMEOUT_FAULT_BIT => { handle_timeout_fault(); true }
        RANGE_FAULT_BIT => { handle_range_fault(); true }
        _ => false,
    }
}
