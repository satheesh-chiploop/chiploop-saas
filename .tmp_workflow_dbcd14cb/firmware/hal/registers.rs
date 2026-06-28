use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CONTROL_OFFSET: usize = 0x00000000;
pub const CONTROL_ENABLE_SHIFT: u32 = 0;
pub const CONTROL_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_ENABLE_MASK: u32 = 0x00000001;
pub const CONTROL_SAMPLE_START_SHIFT: u32 = 1;
pub const CONTROL_SAMPLE_START_WIDTH: u32 = 1;
pub const CONTROL_SAMPLE_START_MASK: u32 = 0x00000002;
pub const CONTROL_IRQ_ENABLE_SHIFT: u32 = 2;
pub const CONTROL_IRQ_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_IRQ_ENABLE_MASK: u32 = 0x00000004;
pub const CONTROL_ALERT_CLEAR_SHIFT: u32 = 3;
pub const CONTROL_ALERT_CLEAR_WIDTH: u32 = 1;
pub const CONTROL_ALERT_CLEAR_MASK: u32 = 0x00000008;
pub const CONTROL_RESERVED_SHIFT: u32 = 4;
pub const CONTROL_RESERVED_WIDTH: u32 = 12;
pub const CONTROL_RESERVED_MASK: u32 = 0x0000FFF0;
pub const STATUS_OFFSET: usize = 0x00000004;
pub const STATUS_SAMPLE_DONE_SHIFT: u32 = 0;
pub const STATUS_SAMPLE_DONE_WIDTH: u32 = 1;
pub const STATUS_SAMPLE_DONE_MASK: u32 = 0x00000001;
pub const STATUS_ALERT_PENDING_SHIFT: u32 = 1;
pub const STATUS_ALERT_PENDING_WIDTH: u32 = 1;
pub const STATUS_ALERT_PENDING_MASK: u32 = 0x00000002;
pub const STATUS_ADC_VALID_SEEN_SHIFT: u32 = 2;
pub const STATUS_ADC_VALID_SEEN_WIDTH: u32 = 1;
pub const STATUS_ADC_VALID_SEEN_MASK: u32 = 0x00000004;
pub const STATUS_BUSY_SHIFT: u32 = 3;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u32 = 0x00000008;
pub const STATUS_RESERVED_SHIFT: u32 = 4;
pub const STATUS_RESERVED_WIDTH: u32 = 12;
pub const STATUS_RESERVED_MASK: u32 = 0x0000FFF0;
pub const THRESHOLD_OFFSET: usize = 0x00000008;
pub const THRESHOLD_THRESHOLD_CODE_SHIFT: u32 = 0;
pub const THRESHOLD_THRESHOLD_CODE_WIDTH: u32 = 12;
pub const THRESHOLD_THRESHOLD_CODE_MASK: u32 = 0x00000FFF;
pub const THRESHOLD_RESERVED_SHIFT: u32 = 12;
pub const THRESHOLD_RESERVED_WIDTH: u32 = 4;
pub const THRESHOLD_RESERVED_MASK: u32 = 0x0000F000;
pub const LATEST_TEMP_OFFSET: usize = 0x0000000C;
pub const LATEST_TEMP_TEMP_CODE_SHIFT: u32 = 0;
pub const LATEST_TEMP_TEMP_CODE_WIDTH: u32 = 12;
pub const LATEST_TEMP_TEMP_CODE_MASK: u32 = 0x00000FFF;
pub const LATEST_TEMP_RESERVED_SHIFT: u32 = 12;
pub const LATEST_TEMP_RESERVED_WIDTH: u32 = 4;
pub const LATEST_TEMP_RESERVED_MASK: u32 = 0x0000F000;
pub const SAMPLE_COUNT_OFFSET: usize = 0x00000010;
pub const SAMPLE_COUNT_SAMPLE_COUNT_SHIFT: u32 = 0;
pub const SAMPLE_COUNT_SAMPLE_COUNT_WIDTH: u32 = 16;
pub const SAMPLE_COUNT_SAMPLE_COUNT_MASK: u32 = 0x0000FFFF;
pub const IRQ_STATUS_OFFSET: usize = 0x00000014;
pub const IRQ_STATUS_ALERT_SHIFT: u32 = 0;
pub const IRQ_STATUS_ALERT_WIDTH: u32 = 1;
pub const IRQ_STATUS_ALERT_MASK: u32 = 0x00000001;
pub const IRQ_STATUS_SAMPLE_DONE_SHIFT: u32 = 1;
pub const IRQ_STATUS_SAMPLE_DONE_WIDTH: u32 = 1;
pub const IRQ_STATUS_SAMPLE_DONE_MASK: u32 = 0x00000002;
pub const IRQ_STATUS_RESERVED_SHIFT: u32 = 2;
pub const IRQ_STATUS_RESERVED_WIDTH: u32 = 14;
pub const IRQ_STATUS_RESERVED_MASK: u32 = 0x0000FFFC;
pub const IRQ_CLEAR_OFFSET: usize = 0x00000018;
pub const IRQ_CLEAR_CLEAR_ALERT_SHIFT: u32 = 0;
pub const IRQ_CLEAR_CLEAR_ALERT_WIDTH: u32 = 1;
pub const IRQ_CLEAR_CLEAR_ALERT_MASK: u32 = 0x00000001;
pub const IRQ_CLEAR_CLEAR_SAMPLE_DONE_SHIFT: u32 = 1;
pub const IRQ_CLEAR_CLEAR_SAMPLE_DONE_WIDTH: u32 = 1;
pub const IRQ_CLEAR_CLEAR_SAMPLE_DONE_MASK: u32 = 0x00000002;
pub const IRQ_CLEAR_RESERVED_SHIFT: u32 = 2;
pub const IRQ_CLEAR_RESERVED_WIDTH: u32 = 14;
pub const IRQ_CLEAR_RESERVED_MASK: u32 = 0x0000FFFC;

#[inline]
fn reg_ptr(offset: usize) -> *mut u32 {
    (BASE_ADDRESS + offset) as *mut u32
}

#[inline]
fn read_reg(offset: usize) -> u32 {
    unsafe { read_volatile(reg_ptr(offset) as *const u32) }
}

#[inline]
fn write_reg(offset: usize, value: u32) {
    unsafe { write_volatile(reg_ptr(offset), value) }
}

#[inline]
pub fn read_control() -> u32 {
    read_reg(CONTROL_OFFSET)
}

#[inline]
pub fn write_control(value: u32) {
    write_reg(CONTROL_OFFSET, value)
}

#[inline]
pub fn get_control_enable() -> u32 {
    (read_control() & CONTROL_ENABLE_MASK) >> CONTROL_ENABLE_SHIFT
}

#[inline]
pub fn set_control_enable(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_ENABLE_MASK) | ((value << CONTROL_ENABLE_SHIFT) & CONTROL_ENABLE_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_sample_start() -> u32 {
    (read_control() & CONTROL_SAMPLE_START_MASK) >> CONTROL_SAMPLE_START_SHIFT
}

#[inline]
pub fn set_control_sample_start(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_SAMPLE_START_MASK) | ((value << CONTROL_SAMPLE_START_SHIFT) & CONTROL_SAMPLE_START_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_irq_enable() -> u32 {
    (read_control() & CONTROL_IRQ_ENABLE_MASK) >> CONTROL_IRQ_ENABLE_SHIFT
}

#[inline]
pub fn set_control_irq_enable(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_IRQ_ENABLE_MASK) | ((value << CONTROL_IRQ_ENABLE_SHIFT) & CONTROL_IRQ_ENABLE_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_alert_clear() -> u32 {
    (read_control() & CONTROL_ALERT_CLEAR_MASK) >> CONTROL_ALERT_CLEAR_SHIFT
}

#[inline]
pub fn set_control_alert_clear(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_ALERT_CLEAR_MASK) | ((value << CONTROL_ALERT_CLEAR_SHIFT) & CONTROL_ALERT_CLEAR_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_reserved() -> u32 {
    (read_control() & CONTROL_RESERVED_MASK) >> CONTROL_RESERVED_SHIFT
}

#[inline]
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_sample_done() -> u32 {
    (read_status() & STATUS_SAMPLE_DONE_MASK) >> STATUS_SAMPLE_DONE_SHIFT
}

#[inline]
pub fn get_status_alert_pending() -> u32 {
    (read_status() & STATUS_ALERT_PENDING_MASK) >> STATUS_ALERT_PENDING_SHIFT
}

#[inline]
pub fn get_status_adc_valid_seen() -> u32 {
    (read_status() & STATUS_ADC_VALID_SEEN_MASK) >> STATUS_ADC_VALID_SEEN_SHIFT
}

#[inline]
pub fn get_status_busy() -> u32 {
    (read_status() & STATUS_BUSY_MASK) >> STATUS_BUSY_SHIFT
}

#[inline]
pub fn get_status_reserved() -> u32 {
    (read_status() & STATUS_RESERVED_MASK) >> STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_threshold() -> u32 {
    read_reg(THRESHOLD_OFFSET)
}

#[inline]
pub fn write_threshold(value: u32) {
    write_reg(THRESHOLD_OFFSET, value)
}

#[inline]
pub fn get_threshold_threshold_code() -> u32 {
    (read_threshold() & THRESHOLD_THRESHOLD_CODE_MASK) >> THRESHOLD_THRESHOLD_CODE_SHIFT
}

#[inline]
pub fn set_threshold_threshold_code(value: u32) {
    let current = read_threshold();
    let next = (current & !THRESHOLD_THRESHOLD_CODE_MASK) | ((value << THRESHOLD_THRESHOLD_CODE_SHIFT) & THRESHOLD_THRESHOLD_CODE_MASK);
    write_threshold(next);
}

#[inline]
pub fn get_threshold_reserved() -> u32 {
    (read_threshold() & THRESHOLD_RESERVED_MASK) >> THRESHOLD_RESERVED_SHIFT
}

#[inline]
pub fn read_latest_temp() -> u32 {
    read_reg(LATEST_TEMP_OFFSET)
}

#[inline]
pub fn get_latest_temp_temp_code() -> u32 {
    (read_latest_temp() & LATEST_TEMP_TEMP_CODE_MASK) >> LATEST_TEMP_TEMP_CODE_SHIFT
}

#[inline]
pub fn get_latest_temp_reserved() -> u32 {
    (read_latest_temp() & LATEST_TEMP_RESERVED_MASK) >> LATEST_TEMP_RESERVED_SHIFT
}

#[inline]
pub fn read_sample_count() -> u32 {
    read_reg(SAMPLE_COUNT_OFFSET)
}

#[inline]
pub fn get_sample_count_sample_count() -> u32 {
    (read_sample_count() & SAMPLE_COUNT_SAMPLE_COUNT_MASK) >> SAMPLE_COUNT_SAMPLE_COUNT_SHIFT
}

#[inline]
pub fn read_irq_status() -> u32 {
    read_reg(IRQ_STATUS_OFFSET)
}

#[inline]
pub fn get_irq_status_alert() -> u32 {
    (read_irq_status() & IRQ_STATUS_ALERT_MASK) >> IRQ_STATUS_ALERT_SHIFT
}

#[inline]
pub fn get_irq_status_sample_done() -> u32 {
    (read_irq_status() & IRQ_STATUS_SAMPLE_DONE_MASK) >> IRQ_STATUS_SAMPLE_DONE_SHIFT
}

#[inline]
pub fn get_irq_status_reserved() -> u32 {
    (read_irq_status() & IRQ_STATUS_RESERVED_MASK) >> IRQ_STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_irq_clear() -> u32 {
    read_reg(IRQ_CLEAR_OFFSET)
}

#[inline]
pub fn write_irq_clear(value: u32) {
    write_reg(IRQ_CLEAR_OFFSET, value)
}

#[inline]
pub fn get_irq_clear_clear_alert() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_CLEAR_ALERT_MASK) >> IRQ_CLEAR_CLEAR_ALERT_SHIFT
}

#[inline]
pub fn set_irq_clear_clear_alert(value: u32) {
    let current = read_irq_clear();
    let next = (current & !IRQ_CLEAR_CLEAR_ALERT_MASK) | ((value << IRQ_CLEAR_CLEAR_ALERT_SHIFT) & IRQ_CLEAR_CLEAR_ALERT_MASK);
    write_irq_clear(next);
}

#[inline]
pub fn get_irq_clear_clear_sample_done() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_CLEAR_SAMPLE_DONE_MASK) >> IRQ_CLEAR_CLEAR_SAMPLE_DONE_SHIFT
}

#[inline]
pub fn set_irq_clear_clear_sample_done(value: u32) {
    let current = read_irq_clear();
    let next = (current & !IRQ_CLEAR_CLEAR_SAMPLE_DONE_MASK) | ((value << IRQ_CLEAR_CLEAR_SAMPLE_DONE_SHIFT) & IRQ_CLEAR_CLEAR_SAMPLE_DONE_MASK);
    write_irq_clear(next);
}

#[inline]
pub fn get_irq_clear_reserved() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_RESERVED_MASK) >> IRQ_CLEAR_RESERVED_SHIFT
}

