// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    ClearFaults,
    TimeoutFault,
    StaleFault,
    InvalidPayloadFault,
    FaultPending,
}

#[inline]
pub fn interrupt_count() -> usize {
    5
}

pub const CLEAR_FAULTS_BIT: u32 = 0;
pub const TIMEOUT_FAULT_BIT: u32 = 1;
pub const STALE_FAULT_BIT: u32 = 2;
pub const INVALID_PAYLOAD_FAULT_BIT: u32 = 3;
pub const FAULT_PENDING_BIT: u32 = 4;

#[inline]
pub fn handle_clear_faults() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_timeout_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_stale_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_invalid_payload_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_pending() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        CLEAR_FAULTS_BIT => { handle_clear_faults(); true }
        TIMEOUT_FAULT_BIT => { handle_timeout_fault(); true }
        STALE_FAULT_BIT => { handle_stale_fault(); true }
        INVALID_PAYLOAD_FAULT_BIT => { handle_invalid_payload_fault(); true }
        FAULT_PENDING_BIT => { handle_fault_pending(); true }
        _ => false,
    }
}
