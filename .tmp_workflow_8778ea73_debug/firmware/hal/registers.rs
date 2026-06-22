use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CONTROL_OFFSET: usize = 0x00000000;
pub const CONTROL_ENABLE_SHIFT: u32 = 0;
pub const CONTROL_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_ENABLE_MASK: u32 = 0x00000001;
pub const CONTROL_SOFT_RESET_SHIFT: u32 = 1;
pub const CONTROL_SOFT_RESET_WIDTH: u32 = 1;
pub const CONTROL_SOFT_RESET_MASK: u32 = 0x00000002;
pub const CONTROL_IRQ_ENABLE_SHIFT: u32 = 2;
pub const CONTROL_IRQ_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_IRQ_ENABLE_MASK: u32 = 0x00000004;
pub const CONTROL_RESERVED_SHIFT: u32 = 31;
pub const CONTROL_RESERVED_WIDTH: u32 = 1;
pub const CONTROL_RESERVED_MASK: u32 = 0x80000000;
pub const STATUS_OFFSET: usize = 0x00000004;
pub const STATUS_READY_SHIFT: u32 = 0;
pub const STATUS_READY_WIDTH: u32 = 1;
pub const STATUS_READY_MASK: u32 = 0x00000001;
pub const STATUS_BIST_DONE_SHIFT: u32 = 1;
pub const STATUS_BIST_DONE_WIDTH: u32 = 1;
pub const STATUS_BIST_DONE_MASK: u32 = 0x00000002;
pub const STATUS_BIST_FAIL_SHIFT: u32 = 2;
pub const STATUS_BIST_FAIL_WIDTH: u32 = 1;
pub const STATUS_BIST_FAIL_MASK: u32 = 0x00000004;
pub const STATUS_BUSY_SHIFT: u32 = 3;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u32 = 0x00000008;
pub const STATUS_RESERVED_SHIFT: u32 = 31;
pub const STATUS_RESERVED_WIDTH: u32 = 1;
pub const STATUS_RESERVED_MASK: u32 = 0x80000000;
pub const MEM_ADDR_OFFSET: usize = 0x00000008;
pub const MEM_ADDR_ADDR_SHIFT: u32 = 7;
pub const MEM_ADDR_ADDR_WIDTH: u32 = 1;
pub const MEM_ADDR_ADDR_MASK: u32 = 0x00000080;
pub const MEM_ADDR_RESERVED_SHIFT: u32 = 31;
pub const MEM_ADDR_RESERVED_WIDTH: u32 = 1;
pub const MEM_ADDR_RESERVED_MASK: u32 = 0x80000000;
pub const MEM_WDATA_OFFSET: usize = 0x0000000C;
pub const MEM_WDATA_WDATA_SHIFT: u32 = 31;
pub const MEM_WDATA_WDATA_WIDTH: u32 = 1;
pub const MEM_WDATA_WDATA_MASK: u32 = 0x80000000;
pub const MEM_RDATA_OFFSET: usize = 0x00000010;
pub const MEM_RDATA_RDATA_SHIFT: u32 = 31;
pub const MEM_RDATA_RDATA_WIDTH: u32 = 1;
pub const MEM_RDATA_RDATA_MASK: u32 = 0x80000000;
pub const MEM_CONTROL_OFFSET: usize = 0x00000014;
pub const MEM_CONTROL_MEM_WRITE_SHIFT: u32 = 0;
pub const MEM_CONTROL_MEM_WRITE_WIDTH: u32 = 1;
pub const MEM_CONTROL_MEM_WRITE_MASK: u32 = 0x00000001;
pub const MEM_CONTROL_MEM_READ_SHIFT: u32 = 1;
pub const MEM_CONTROL_MEM_READ_WIDTH: u32 = 1;
pub const MEM_CONTROL_MEM_READ_MASK: u32 = 0x00000002;
pub const MEM_CONTROL_RESERVED_SHIFT: u32 = 31;
pub const MEM_CONTROL_RESERVED_WIDTH: u32 = 1;
pub const MEM_CONTROL_RESERVED_MASK: u32 = 0x80000000;
pub const BIST_CONTROL_OFFSET: usize = 0x00000018;
pub const BIST_CONTROL_START_SHIFT: u32 = 0;
pub const BIST_CONTROL_START_WIDTH: u32 = 1;
pub const BIST_CONTROL_START_MASK: u32 = 0x00000001;
pub const BIST_CONTROL_CLEAR_RESULT_SHIFT: u32 = 1;
pub const BIST_CONTROL_CLEAR_RESULT_WIDTH: u32 = 1;
pub const BIST_CONTROL_CLEAR_RESULT_MASK: u32 = 0x00000002;
pub const BIST_CONTROL_RESERVED_SHIFT: u32 = 31;
pub const BIST_CONTROL_RESERVED_WIDTH: u32 = 1;
pub const BIST_CONTROL_RESERVED_MASK: u32 = 0x80000000;
pub const BIST_STATUS_OFFSET: usize = 0x0000001C;
pub const BIST_STATUS_DONE_SHIFT: u32 = 0;
pub const BIST_STATUS_DONE_WIDTH: u32 = 1;
pub const BIST_STATUS_DONE_MASK: u32 = 0x00000001;
pub const BIST_STATUS_FAIL_SHIFT: u32 = 1;
pub const BIST_STATUS_FAIL_WIDTH: u32 = 1;
pub const BIST_STATUS_FAIL_MASK: u32 = 0x00000002;
pub const BIST_STATUS_RUNNING_SHIFT: u32 = 2;
pub const BIST_STATUS_RUNNING_WIDTH: u32 = 1;
pub const BIST_STATUS_RUNNING_MASK: u32 = 0x00000004;
pub const BIST_STATUS_LAST_FAIL_ADDR_SHIFT: u32 = 10;
pub const BIST_STATUS_LAST_FAIL_ADDR_WIDTH: u32 = 1;
pub const BIST_STATUS_LAST_FAIL_ADDR_MASK: u32 = 0x00000400;
pub const BIST_STATUS_RESERVED_SHIFT: u32 = 31;
pub const BIST_STATUS_RESERVED_WIDTH: u32 = 1;
pub const BIST_STATUS_RESERVED_MASK: u32 = 0x80000000;
pub const IRQ_STATUS_OFFSET: usize = 0x00000020;
pub const IRQ_STATUS_BIST_DONE_SHIFT: u32 = 0;
pub const IRQ_STATUS_BIST_DONE_WIDTH: u32 = 1;
pub const IRQ_STATUS_BIST_DONE_MASK: u32 = 0x00000001;
pub const IRQ_STATUS_BIST_FAIL_SHIFT: u32 = 1;
pub const IRQ_STATUS_BIST_FAIL_WIDTH: u32 = 1;
pub const IRQ_STATUS_BIST_FAIL_MASK: u32 = 0x00000002;
pub const IRQ_STATUS_RESERVED_SHIFT: u32 = 31;
pub const IRQ_STATUS_RESERVED_WIDTH: u32 = 1;
pub const IRQ_STATUS_RESERVED_MASK: u32 = 0x80000000;
pub const IRQ_CLEAR_OFFSET: usize = 0x00000024;
pub const IRQ_CLEAR_CLR_BIST_DONE_SHIFT: u32 = 0;
pub const IRQ_CLEAR_CLR_BIST_DONE_WIDTH: u32 = 1;
pub const IRQ_CLEAR_CLR_BIST_DONE_MASK: u32 = 0x00000001;
pub const IRQ_CLEAR_CLR_BIST_FAIL_SHIFT: u32 = 1;
pub const IRQ_CLEAR_CLR_BIST_FAIL_WIDTH: u32 = 1;
pub const IRQ_CLEAR_CLR_BIST_FAIL_MASK: u32 = 0x00000002;
pub const IRQ_CLEAR_RESERVED_SHIFT: u32 = 31;
pub const IRQ_CLEAR_RESERVED_WIDTH: u32 = 1;
pub const IRQ_CLEAR_RESERVED_MASK: u32 = 0x80000000;

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
pub fn get_control_soft_reset() -> u32 {
    (read_control() & CONTROL_SOFT_RESET_MASK) >> CONTROL_SOFT_RESET_SHIFT
}

#[inline]
pub fn set_control_soft_reset(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_SOFT_RESET_MASK) | ((value << CONTROL_SOFT_RESET_SHIFT) & CONTROL_SOFT_RESET_MASK);
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
pub fn get_control_reserved() -> u32 {
    (read_control() & CONTROL_RESERVED_MASK) >> CONTROL_RESERVED_SHIFT
}

#[inline]
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_ready() -> u32 {
    (read_status() & STATUS_READY_MASK) >> STATUS_READY_SHIFT
}

#[inline]
pub fn get_status_bist_done() -> u32 {
    (read_status() & STATUS_BIST_DONE_MASK) >> STATUS_BIST_DONE_SHIFT
}

#[inline]
pub fn get_status_bist_fail() -> u32 {
    (read_status() & STATUS_BIST_FAIL_MASK) >> STATUS_BIST_FAIL_SHIFT
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
pub fn read_mem_addr() -> u32 {
    read_reg(MEM_ADDR_OFFSET)
}

#[inline]
pub fn write_mem_addr(value: u32) {
    write_reg(MEM_ADDR_OFFSET, value)
}

#[inline]
pub fn get_mem_addr_addr() -> u32 {
    (read_mem_addr() & MEM_ADDR_ADDR_MASK) >> MEM_ADDR_ADDR_SHIFT
}

#[inline]
pub fn set_mem_addr_addr(value: u32) {
    let current = read_mem_addr();
    let next = (current & !MEM_ADDR_ADDR_MASK) | ((value << MEM_ADDR_ADDR_SHIFT) & MEM_ADDR_ADDR_MASK);
    write_mem_addr(next);
}

#[inline]
pub fn get_mem_addr_reserved() -> u32 {
    (read_mem_addr() & MEM_ADDR_RESERVED_MASK) >> MEM_ADDR_RESERVED_SHIFT
}

#[inline]
pub fn read_mem_wdata() -> u32 {
    read_reg(MEM_WDATA_OFFSET)
}

#[inline]
pub fn write_mem_wdata(value: u32) {
    write_reg(MEM_WDATA_OFFSET, value)
}

#[inline]
pub fn get_mem_wdata_wdata() -> u32 {
    (read_mem_wdata() & MEM_WDATA_WDATA_MASK) >> MEM_WDATA_WDATA_SHIFT
}

#[inline]
pub fn set_mem_wdata_wdata(value: u32) {
    let current = read_mem_wdata();
    let next = (current & !MEM_WDATA_WDATA_MASK) | ((value << MEM_WDATA_WDATA_SHIFT) & MEM_WDATA_WDATA_MASK);
    write_mem_wdata(next);
}

#[inline]
pub fn read_mem_rdata() -> u32 {
    read_reg(MEM_RDATA_OFFSET)
}

#[inline]
pub fn get_mem_rdata_rdata() -> u32 {
    (read_mem_rdata() & MEM_RDATA_RDATA_MASK) >> MEM_RDATA_RDATA_SHIFT
}

#[inline]
pub fn read_mem_control() -> u32 {
    read_reg(MEM_CONTROL_OFFSET)
}

#[inline]
pub fn write_mem_control(value: u32) {
    write_reg(MEM_CONTROL_OFFSET, value)
}

#[inline]
pub fn get_mem_control_mem_write() -> u32 {
    (read_mem_control() & MEM_CONTROL_MEM_WRITE_MASK) >> MEM_CONTROL_MEM_WRITE_SHIFT
}

#[inline]
pub fn set_mem_control_mem_write(value: u32) {
    let current = read_mem_control();
    let next = (current & !MEM_CONTROL_MEM_WRITE_MASK) | ((value << MEM_CONTROL_MEM_WRITE_SHIFT) & MEM_CONTROL_MEM_WRITE_MASK);
    write_mem_control(next);
}

#[inline]
pub fn get_mem_control_mem_read() -> u32 {
    (read_mem_control() & MEM_CONTROL_MEM_READ_MASK) >> MEM_CONTROL_MEM_READ_SHIFT
}

#[inline]
pub fn set_mem_control_mem_read(value: u32) {
    let current = read_mem_control();
    let next = (current & !MEM_CONTROL_MEM_READ_MASK) | ((value << MEM_CONTROL_MEM_READ_SHIFT) & MEM_CONTROL_MEM_READ_MASK);
    write_mem_control(next);
}

#[inline]
pub fn get_mem_control_reserved() -> u32 {
    (read_mem_control() & MEM_CONTROL_RESERVED_MASK) >> MEM_CONTROL_RESERVED_SHIFT
}

#[inline]
pub fn read_bist_control() -> u32 {
    read_reg(BIST_CONTROL_OFFSET)
}

#[inline]
pub fn write_bist_control(value: u32) {
    write_reg(BIST_CONTROL_OFFSET, value)
}

#[inline]
pub fn get_bist_control_start() -> u32 {
    (read_bist_control() & BIST_CONTROL_START_MASK) >> BIST_CONTROL_START_SHIFT
}

#[inline]
pub fn set_bist_control_start(value: u32) {
    let current = read_bist_control();
    let next = (current & !BIST_CONTROL_START_MASK) | ((value << BIST_CONTROL_START_SHIFT) & BIST_CONTROL_START_MASK);
    write_bist_control(next);
}

#[inline]
pub fn get_bist_control_clear_result() -> u32 {
    (read_bist_control() & BIST_CONTROL_CLEAR_RESULT_MASK) >> BIST_CONTROL_CLEAR_RESULT_SHIFT
}

#[inline]
pub fn set_bist_control_clear_result(value: u32) {
    let current = read_bist_control();
    let next = (current & !BIST_CONTROL_CLEAR_RESULT_MASK) | ((value << BIST_CONTROL_CLEAR_RESULT_SHIFT) & BIST_CONTROL_CLEAR_RESULT_MASK);
    write_bist_control(next);
}

#[inline]
pub fn get_bist_control_reserved() -> u32 {
    (read_bist_control() & BIST_CONTROL_RESERVED_MASK) >> BIST_CONTROL_RESERVED_SHIFT
}

#[inline]
pub fn read_bist_status() -> u32 {
    read_reg(BIST_STATUS_OFFSET)
}

#[inline]
pub fn get_bist_status_done() -> u32 {
    (read_bist_status() & BIST_STATUS_DONE_MASK) >> BIST_STATUS_DONE_SHIFT
}

#[inline]
pub fn get_bist_status_fail() -> u32 {
    (read_bist_status() & BIST_STATUS_FAIL_MASK) >> BIST_STATUS_FAIL_SHIFT
}

#[inline]
pub fn get_bist_status_running() -> u32 {
    (read_bist_status() & BIST_STATUS_RUNNING_MASK) >> BIST_STATUS_RUNNING_SHIFT
}

#[inline]
pub fn get_bist_status_last_fail_addr() -> u32 {
    (read_bist_status() & BIST_STATUS_LAST_FAIL_ADDR_MASK) >> BIST_STATUS_LAST_FAIL_ADDR_SHIFT
}

#[inline]
pub fn get_bist_status_reserved() -> u32 {
    (read_bist_status() & BIST_STATUS_RESERVED_MASK) >> BIST_STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_irq_status() -> u32 {
    read_reg(IRQ_STATUS_OFFSET)
}

#[inline]
pub fn write_irq_status(value: u32) {
    write_reg(IRQ_STATUS_OFFSET, value)
}

#[inline]
pub fn get_irq_status_bist_done() -> u32 {
    (read_irq_status() & IRQ_STATUS_BIST_DONE_MASK) >> IRQ_STATUS_BIST_DONE_SHIFT
}

#[inline]
pub fn set_irq_status_bist_done(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_BIST_DONE_MASK) | ((value << IRQ_STATUS_BIST_DONE_SHIFT) & IRQ_STATUS_BIST_DONE_MASK);
    write_irq_status(next);
}

#[inline]
pub fn get_irq_status_bist_fail() -> u32 {
    (read_irq_status() & IRQ_STATUS_BIST_FAIL_MASK) >> IRQ_STATUS_BIST_FAIL_SHIFT
}

#[inline]
pub fn set_irq_status_bist_fail(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_BIST_FAIL_MASK) | ((value << IRQ_STATUS_BIST_FAIL_SHIFT) & IRQ_STATUS_BIST_FAIL_MASK);
    write_irq_status(next);
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
pub fn get_irq_clear_clr_bist_done() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_CLR_BIST_DONE_MASK) >> IRQ_CLEAR_CLR_BIST_DONE_SHIFT
}

#[inline]
pub fn set_irq_clear_clr_bist_done(value: u32) {
    let current = read_irq_clear();
    let next = (current & !IRQ_CLEAR_CLR_BIST_DONE_MASK) | ((value << IRQ_CLEAR_CLR_BIST_DONE_SHIFT) & IRQ_CLEAR_CLR_BIST_DONE_MASK);
    write_irq_clear(next);
}

#[inline]
pub fn get_irq_clear_clr_bist_fail() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_CLR_BIST_FAIL_MASK) >> IRQ_CLEAR_CLR_BIST_FAIL_SHIFT
}

#[inline]
pub fn set_irq_clear_clr_bist_fail(value: u32) {
    let current = read_irq_clear();
    let next = (current & !IRQ_CLEAR_CLR_BIST_FAIL_MASK) | ((value << IRQ_CLEAR_CLR_BIST_FAIL_SHIFT) & IRQ_CLEAR_CLR_BIST_FAIL_MASK);
    write_irq_clear(next);
}

#[inline]
pub fn get_irq_clear_reserved() -> u32 {
    (read_irq_clear() & IRQ_CLEAR_RESERVED_MASK) >> IRQ_CLEAR_RESERVED_SHIFT
}

#[inline]
pub fn set_irq_clear_reserved(value: u32) {
    let current = read_irq_clear();
    let next = (current & !IRQ_CLEAR_RESERVED_MASK) | ((value << IRQ_CLEAR_RESERVED_SHIFT) & IRQ_CLEAR_RESERVED_MASK);
    write_irq_clear(next);
}

