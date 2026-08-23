// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    StreamVelocitySetpoint,
    StreamVelocitySetpoint,
    FaultMask,
    FaultMask,
    FaultSummary,
}

#[inline]
pub fn interrupt_count() -> usize {
    5
}

pub const STREAM_VELOCITY_SETPOINT_BIT: u32 = 0;
pub const STREAM_VELOCITY_SETPOINT_BIT: u32 = 1;
pub const FAULT_MASK_BIT: u32 = 2;
pub const FAULT_MASK_BIT: u32 = 3;
pub const FAULT_SUMMARY_BIT: u32 = 4;

#[inline]
pub fn handle_stream_velocity_setpoint() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_stream_velocity_setpoint() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_mask() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_mask() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_summary() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        STREAM_VELOCITY_SETPOINT_BIT => { handle_stream_velocity_setpoint(); true }
        STREAM_VELOCITY_SETPOINT_BIT => { handle_stream_velocity_setpoint(); true }
        FAULT_MASK_BIT => { handle_fault_mask(); true }
        FAULT_MASK_BIT => { handle_fault_mask(); true }
        FAULT_SUMMARY_BIT => { handle_fault_summary(); true }
        _ => false,
    }
}
