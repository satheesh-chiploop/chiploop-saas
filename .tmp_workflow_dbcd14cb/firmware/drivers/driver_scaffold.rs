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
    pub fn get_control_sample_start(&self) -> bool {
        get_control_sample_start() != 0
    }

    #[inline]
    pub fn set_control_sample_start(&self, value: bool) {
        set_control_sample_start(if value { 1 } else { 0 })
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
    pub fn get_control_alert_clear(&self) -> bool {
        get_control_alert_clear() != 0
    }

    #[inline]
    pub fn set_control_alert_clear(&self, value: bool) {
        set_control_alert_clear(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_reserved(&self) -> u16 {
        get_control_reserved() as u16
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_sample_done(&self) -> bool {
        get_status_sample_done() != 0
    }

    #[inline]
    pub fn get_status_alert_pending(&self) -> bool {
        get_status_alert_pending() != 0
    }

    #[inline]
    pub fn get_status_adc_valid_seen(&self) -> bool {
        get_status_adc_valid_seen() != 0
    }

    #[inline]
    pub fn get_status_busy(&self) -> bool {
        get_status_busy() != 0
    }

    #[inline]
    pub fn get_status_reserved(&self) -> u16 {
        get_status_reserved() as u16
    }

    #[inline]
    pub fn read_threshold(&self) -> u32 {
        read_threshold()
    }

    #[inline]
    pub fn write_threshold(&self, value: u32) {
        write_threshold(value)
    }

    #[inline]
    pub fn get_threshold_threshold_code(&self) -> u16 {
        get_threshold_threshold_code() as u16
    }

    #[inline]
    pub fn set_threshold_threshold_code(&self, value: u16) {
        set_threshold_threshold_code(value as u32)
    }

    #[inline]
    pub fn get_threshold_reserved(&self) -> u8 {
        get_threshold_reserved() as u8
    }

    #[inline]
    pub fn read_latest_temp(&self) -> u32 {
        read_latest_temp()
    }

    #[inline]
    pub fn get_latest_temp_temp_code(&self) -> u16 {
        get_latest_temp_temp_code() as u16
    }

    #[inline]
    pub fn get_latest_temp_reserved(&self) -> u8 {
        get_latest_temp_reserved() as u8
    }

    #[inline]
    pub fn read_sample_count(&self) -> u32 {
        read_sample_count()
    }

    #[inline]
    pub fn get_sample_count_sample_count(&self) -> u16 {
        get_sample_count_sample_count() as u16
    }

    #[inline]
    pub fn read_irq_status(&self) -> u32 {
        read_irq_status()
    }

    #[inline]
    pub fn get_irq_status_alert(&self) -> bool {
        get_irq_status_alert() != 0
    }

    #[inline]
    pub fn get_irq_status_sample_done(&self) -> bool {
        get_irq_status_sample_done() != 0
    }

    #[inline]
    pub fn get_irq_status_reserved(&self) -> u16 {
        get_irq_status_reserved() as u16
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
    pub fn get_irq_clear_clear_alert(&self) -> bool {
        get_irq_clear_clear_alert() != 0
    }

    #[inline]
    pub fn set_irq_clear_clear_alert(&self, value: bool) {
        set_irq_clear_clear_alert(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_clear_clear_sample_done(&self) -> bool {
        get_irq_clear_clear_sample_done() != 0
    }

    #[inline]
    pub fn set_irq_clear_clear_sample_done(&self, value: bool) {
        set_irq_clear_clear_sample_done(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_clear_reserved(&self) -> u16 {
        get_irq_clear_reserved() as u16
    }

}
