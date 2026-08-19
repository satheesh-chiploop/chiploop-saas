// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    IrqEnable,
    VelocitySetpoint,
    FaultClearW1C,
    FaultSticky,
    ResponseReady,
    IrqStatus,
    Fault,
}

#[inline]
pub fn interrupt_count() -> usize {
    7
}

pub const IRQ_ENABLE_BIT: u32 = 0;
pub const VELOCITY_SETPOINT_BIT: u32 = 1;
pub const FAULT_CLEAR_W1C_BIT: u32 = 2;
pub const FAULT_STICKY_BIT: u32 = 3;
pub const RESPONSE_READY_BIT: u32 = 4;
pub const IRQ_STATUS_BIT: u32 = 5;
pub const FAULT_BIT: u32 = 6;

#[inline]
pub fn handle_irq_enable() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_velocity_setpoint() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_clear_w1c() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault_sticky() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_response_ready() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_irq_status() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn handle_fault() {
    // Default ISR scaffold: replace with concrete firmware behavior as needed.
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        IRQ_ENABLE_BIT => { handle_irq_enable(); true }
        VELOCITY_SETPOINT_BIT => { handle_velocity_setpoint(); true }
        FAULT_CLEAR_W1C_BIT => { handle_fault_clear_w1c(); true }
        FAULT_STICKY_BIT => { handle_fault_sticky(); true }
        RESPONSE_READY_BIT => { handle_response_ready(); true }
        IRQ_STATUS_BIT => { handle_irq_status(); true }
        FAULT_BIT => { handle_fault(); true }
        _ => false,
    }
}
