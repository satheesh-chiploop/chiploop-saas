// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    Integrity,
    IrqCtrl,
    IrqEnable,
    ClearStickyFaults,
    StaleDataFault,
    TimeoutFault,
    LastFaultCode,
}

#[inline]
pub fn interrupt_count() -> usize {
    7
}

pub const INTEGRITY_BIT: u32 = 0;
pub const IRQ_CTRL_BIT: u32 = 1;
pub const IRQ_ENABLE_BIT: u32 = 2;
pub const CLEAR_STICKY_FAULTS_BIT: u32 = 3;
pub const STALE_DATA_FAULT_BIT: u32 = 4;
pub const TIMEOUT_FAULT_BIT: u32 = 5;
pub const LAST_FAULT_CODE_BIT: u32 = 6;

#[inline]
pub fn handle_integrity() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_ctrl() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_enable() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_clear_sticky_faults() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_stale_data_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_timeout_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_last_fault_code() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        INTEGRITY_BIT => { handle_integrity(); true }
        IRQ_CTRL_BIT => { handle_irq_ctrl(); true }
        IRQ_ENABLE_BIT => { handle_irq_enable(); true }
        CLEAR_STICKY_FAULTS_BIT => { handle_clear_sticky_faults(); true }
        STALE_DATA_FAULT_BIT => { handle_stale_data_fault(); true }
        TIMEOUT_FAULT_BIT => { handle_timeout_fault(); true }
        LAST_FAULT_CODE_BIT => { handle_last_fault_code(); true }
        _ => false,
    }
}
