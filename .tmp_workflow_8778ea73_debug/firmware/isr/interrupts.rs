// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    IrqEnable,
    Ready,
    BistDone,
    Done,
    IrqStatus,
    IrqClear,
    ClrBistDone,
}

#[inline]
pub fn interrupt_count() -> usize {
    7
}

pub const IRQ_ENABLE_BIT: u32 = 0;
pub const READY_BIT: u32 = 1;
pub const BIST_DONE_BIT: u32 = 2;
pub const DONE_BIT: u32 = 3;
pub const IRQ_STATUS_BIT: u32 = 4;
pub const IRQ_CLEAR_BIT: u32 = 5;
pub const CLR_BIST_DONE_BIT: u32 = 6;

#[inline]
pub fn handle_irq_enable() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_ready() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_bist_done() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_done() {
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
pub fn handle_clr_bist_done() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        IRQ_ENABLE_BIT => { handle_irq_enable(); true }
        READY_BIT => { handle_ready(); true }
        BIST_DONE_BIT => { handle_bist_done(); true }
        DONE_BIT => { handle_done(); true }
        IRQ_STATUS_BIT => { handle_irq_status(); true }
        IRQ_CLEAR_BIT => { handle_irq_clear(); true }
        CLR_BIST_DONE_BIT => { handle_clr_bist_done(); true }
        _ => false,
    }
}
