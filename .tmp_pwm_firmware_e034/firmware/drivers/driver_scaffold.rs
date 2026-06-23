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
    pub fn get_control_reserved(&self) -> u8 {
        get_control_reserved() as u8
    }

    #[inline]
    pub fn read_duty_cycle(&self) -> u32 {
        read_duty_cycle()
    }

    #[inline]
    pub fn write_duty_cycle(&self, value: u32) {
        write_duty_cycle(value)
    }

    #[inline]
    pub fn get_duty_cycle_duty_cycle(&self) -> u8 {
        get_duty_cycle_duty_cycle() as u8
    }

    #[inline]
    pub fn set_duty_cycle_duty_cycle(&self, value: u8) {
        set_duty_cycle_duty_cycle(value as u32)
    }

    #[inline]
    pub fn read_period(&self) -> u32 {
        read_period()
    }

    #[inline]
    pub fn write_period(&self, value: u32) {
        write_period(value)
    }

    #[inline]
    pub fn get_period_period(&self) -> u8 {
        get_period_period() as u8
    }

    #[inline]
    pub fn set_period_period(&self, value: u8) {
        set_period_period(value as u32)
    }

    #[inline]
    pub fn read_counter_value(&self) -> u32 {
        read_counter_value()
    }

    #[inline]
    pub fn get_counter_value_counter_value(&self) -> u8 {
        get_counter_value_counter_value() as u8
    }

}
