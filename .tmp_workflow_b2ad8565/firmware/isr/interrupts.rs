// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    FaultStatus,
    FaultStatus,
    FaultCause,
    FaultIrq,
}

#[inline]
pub fn interrupt_count() -> usize {
    4
}

pub const FAULT_STATUS_BIT: u32 = 0;
pub const FAULT_STATUS_BIT: u32 = 1;
pub const FAULT_CAUSE_BIT: u32 = 2;
pub const FAULT_IRQ_BIT: u32 = 3;

#[inline]
pub fn handle_fault_status() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_status() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_cause() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_irq() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        FAULT_STATUS_BIT => { handle_fault_status(); true }
        FAULT_STATUS_BIT => { handle_fault_status(); true }
        FAULT_CAUSE_BIT => { handle_fault_cause(); true }
        FAULT_IRQ_BIT => { handle_fault_irq(); true }
        _ => false,
    }
}
