// ASSUMPTION: Interrupt decode is software-mediated using firmware-visible status/interrupt bits.
// ASSUMPTION: No MCU-style external vector table is generated unless the hardware contract explicitly requires one.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptSource {
    NoneDeclared,
}

#[inline]
pub fn interrupt_count() -> usize {
    0
}

#[inline]
pub fn dispatch_interrupt(bit_index: u32) -> bool {
    match bit_index {
        _ => false,
    }
}
