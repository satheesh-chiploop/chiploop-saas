// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    ClearFaults,
    TimeoutFault,
    IrqPending,
    VelocityFixedPoint,
    FaultCause,
    StickyFaultBits,
    IrqAck,
}

#[inline]
pub fn interrupt_count() -> usize {
    7
}

pub const CLEAR_FAULTS_BIT: u32 = 0;
pub const TIMEOUT_FAULT_BIT: u32 = 1;
pub const IRQ_PENDING_BIT: u32 = 2;
pub const VELOCITY_FIXED_POINT_BIT: u32 = 3;
pub const FAULT_CAUSE_BIT: u32 = 4;
pub const STICKY_FAULT_BITS_BIT: u32 = 5;
pub const IRQ_ACK_BIT: u32 = 6;

#[inline]
pub fn handle_clear_faults() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_timeout_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_pending() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_velocity_fixed_point() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_cause() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_sticky_fault_bits() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_ack() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        CLEAR_FAULTS_BIT => { handle_clear_faults(); true }
        TIMEOUT_FAULT_BIT => { handle_timeout_fault(); true }
        IRQ_PENDING_BIT => { handle_irq_pending(); true }
        VELOCITY_FIXED_POINT_BIT => { handle_velocity_fixed_point(); true }
        FAULT_CAUSE_BIT => { handle_fault_cause(); true }
        STICKY_FAULT_BITS_BIT => { handle_sticky_fault_bits(); true }
        IRQ_ACK_BIT => { handle_irq_ack(); true }
        _ => false,
    }
}
