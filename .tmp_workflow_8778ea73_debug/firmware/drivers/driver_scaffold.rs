use crate::hal::registers::*;

pub struct DigitalSubsystemDriver;

impl DigitalSubsystemDriver {
    #[inline]
    pub const fn new() -> Self {
        Self
    }

    #[inline]
    pub fn read_control(&self) -> u32 {
        read_control()
    }

    #[inline]
    pub fn write_control(&self, value: u32) {
        write_control(value)
    }

    #[inline]
    pub fn get_control_enable(&self) -> bool {
        get_control_enable() != 0
    }

    #[inline]
    pub fn set_control_enable(&self, value: bool) {
        set_control_enable(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_soft_reset(&self) -> bool {
        get_control_soft_reset() != 0
    }

    #[inline]
    pub fn set_control_soft_reset(&self, value: bool) {
        set_control_soft_reset(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_irq_enable(&self) -> bool {
        get_control_irq_enable() != 0
    }

    #[inline]
    pub fn set_control_irq_enable(&self, value: bool) {
        set_control_irq_enable(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_reserved(&self) -> bool {
        get_control_reserved() != 0
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_ready(&self) -> bool {
        get_status_ready() != 0
    }

    #[inline]
    pub fn get_status_bist_done(&self) -> bool {
        get_status_bist_done() != 0
    }

    #[inline]
    pub fn get_status_bist_fail(&self) -> bool {
        get_status_bist_fail() != 0
    }

    #[inline]
    pub fn get_status_busy(&self) -> bool {
        get_status_busy() != 0
    }

    #[inline]
    pub fn get_status_reserved(&self) -> bool {
        get_status_reserved() != 0
    }

    #[inline]
    pub fn read_mem_addr(&self) -> u32 {
        read_mem_addr()
    }

    #[inline]
    pub fn write_mem_addr(&self, value: u32) {
        write_mem_addr(value)
    }

    #[inline]
    pub fn get_mem_addr_addr(&self) -> bool {
        get_mem_addr_addr() != 0
    }

    #[inline]
    pub fn set_mem_addr_addr(&self, value: bool) {
        set_mem_addr_addr(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_mem_addr_reserved(&self) -> bool {
        get_mem_addr_reserved() != 0
    }

    #[inline]
    pub fn read_mem_wdata(&self) -> u32 {
        read_mem_wdata()
    }

    #[inline]
    pub fn write_mem_wdata(&self, value: u32) {
        write_mem_wdata(value)
    }

    #[inline]
    pub fn get_mem_wdata_wdata(&self) -> bool {
        get_mem_wdata_wdata() != 0
    }

    #[inline]
    pub fn set_mem_wdata_wdata(&self, value: bool) {
        set_mem_wdata_wdata(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_mem_rdata(&self) -> u32 {
        read_mem_rdata()
    }

    #[inline]
    pub fn get_mem_rdata_rdata(&self) -> bool {
        get_mem_rdata_rdata() != 0
    }

    #[inline]
    pub fn read_mem_control(&self) -> u32 {
        read_mem_control()
    }

    #[inline]
    pub fn write_mem_control(&self, value: u32) {
        write_mem_control(value)
    }

    #[inline]
    pub fn get_mem_control_mem_write(&self) -> bool {
        get_mem_control_mem_write() != 0
    }

    #[inline]
    pub fn set_mem_control_mem_write(&self, value: bool) {
        set_mem_control_mem_write(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_mem_control_mem_read(&self) -> bool {
        get_mem_control_mem_read() != 0
    }

    #[inline]
    pub fn set_mem_control_mem_read(&self, value: bool) {
        set_mem_control_mem_read(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_mem_control_reserved(&self) -> bool {
        get_mem_control_reserved() != 0
    }

    #[inline]
    pub fn read_bist_control(&self) -> u32 {
        read_bist_control()
    }

    #[inline]
    pub fn write_bist_control(&self, value: u32) {
        write_bist_control(value)
    }

    #[inline]
    pub fn get_bist_control_start(&self) -> bool {
        get_bist_control_start() != 0
    }

    #[inline]
    pub fn set_bist_control_start(&self, value: bool) {
        set_bist_control_start(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_bist_control_clear_result(&self) -> bool {
        get_bist_control_clear_result() != 0
    }

    #[inline]
    pub fn set_bist_control_clear_result(&self, value: bool) {
        set_bist_control_clear_result(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_bist_control_reserved(&self) -> bool {
        get_bist_control_reserved() != 0
    }

    #[inline]
    pub fn read_bist_status(&self) -> u32 {
        read_bist_status()
    }

    #[inline]
    pub fn get_bist_status_done(&self) -> bool {
        get_bist_status_done() != 0
    }

    #[inline]
    pub fn get_bist_status_fail(&self) -> bool {
        get_bist_status_fail() != 0
    }

    #[inline]
    pub fn get_bist_status_running(&self) -> bool {
        get_bist_status_running() != 0
    }

    #[inline]
    pub fn get_bist_status_last_fail_addr(&self) -> bool {
        get_bist_status_last_fail_addr() != 0
    }

    #[inline]
    pub fn get_bist_status_reserved(&self) -> bool {
        get_bist_status_reserved() != 0
    }

    #[inline]
    pub fn read_irq_status(&self) -> u32 {
        read_irq_status()
    }

    #[inline]
    pub fn write_irq_status(&self, value: u32) {
        write_irq_status(value)
    }

    #[inline]
    pub fn get_irq_status_bist_done(&self) -> bool {
        get_irq_status_bist_done() != 0
    }

    #[inline]
    pub fn set_irq_status_bist_done(&self, value: bool) {
        set_irq_status_bist_done(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_bist_fail(&self) -> bool {
        get_irq_status_bist_fail() != 0
    }

    #[inline]
    pub fn set_irq_status_bist_fail(&self, value: bool) {
        set_irq_status_bist_fail(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_reserved(&self) -> bool {
        get_irq_status_reserved() != 0
    }

    #[inline]
    pub fn read_irq_clear(&self) -> u32 {
        read_irq_clear()
    }

    #[inline]
    pub fn write_irq_clear(&self, value: u32) {
        write_irq_clear(value)
    }

    #[inline]
    pub fn get_irq_clear_clr_bist_done(&self) -> bool {
        get_irq_clear_clr_bist_done() != 0
    }

    #[inline]
    pub fn set_irq_clear_clr_bist_done(&self, value: bool) {
        set_irq_clear_clr_bist_done(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_clear_clr_bist_fail(&self) -> bool {
        get_irq_clear_clr_bist_fail() != 0
    }

    #[inline]
    pub fn set_irq_clear_clr_bist_fail(&self, value: bool) {
        set_irq_clear_clr_bist_fail(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_clear_reserved(&self) -> bool {
        get_irq_clear_reserved() != 0
    }

    #[inline]
    pub fn set_irq_clear_reserved(&self, value: bool) {
        set_irq_clear_reserved(if value { 1 } else { 0 })
    }

}
