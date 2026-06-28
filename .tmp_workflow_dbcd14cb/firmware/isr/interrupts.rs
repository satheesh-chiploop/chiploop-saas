// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    IrqEnable,
    SampleDone,
    AlertPending,
    IrqStatus,
    IrqClear,
    ClearSampleDone,
}

#[inline]
pub fn interrupt_count() -> usize {
    6
}

pub const IRQ_ENABLE_BIT: u32 = 0;
pub const SAMPLE_DONE_BIT: u32 = 1;
pub const ALERT_PENDING_BIT: u32 = 2;
pub const IRQ_STATUS_BIT: u32 = 3;
pub const IRQ_CLEAR_BIT: u32 = 4;
pub const CLEAR_SAMPLE_DONE_BIT: u32 = 5;

#[inline]
pub fn handle_irq_enable() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_sample_done() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_alert_pending() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_status() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_clear() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_clear_sample_done() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        IRQ_ENABLE_BIT => { handle_irq_enable(); true }
        SAMPLE_DONE_BIT => { handle_sample_done(); true }
        ALERT_PENDING_BIT => { handle_alert_pending(); true }
        IRQ_STATUS_BIT => { handle_irq_status(); true }
        IRQ_CLEAR_BIT => { handle_irq_clear(); true }
        CLEAR_SAMPLE_DONE_BIT => { handle_clear_sample_done(); true }
        _ => false,
    }
}
