// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    ReservedErrorEn,
    ReservedErrorFlag,
    FaultCtrl,
    FaultClear,
    FaultLatched,
}

#[inline]
pub fn interrupt_count() -> usize {
    5
}

pub const RESERVED_ERROR_EN_BIT: u32 = 0;
pub const RESERVED_ERROR_FLAG_BIT: u32 = 1;
pub const FAULT_CTRL_BIT: u32 = 2;
pub const FAULT_CLEAR_BIT: u32 = 3;
pub const FAULT_LATCHED_BIT: u32 = 4;

#[inline]
pub fn handle_reserved_error_en() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_reserved_error_flag() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_ctrl() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_clear() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_latched() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        RESERVED_ERROR_EN_BIT => { handle_reserved_error_en(); true }
        RESERVED_ERROR_FLAG_BIT => { handle_reserved_error_flag(); true }
        FAULT_CTRL_BIT => { handle_fault_ctrl(); true }
        FAULT_CLEAR_BIT => { handle_fault_clear(); true }
        FAULT_LATCHED_BIT => { handle_fault_latched(); true }
        _ => false,
    }
}
