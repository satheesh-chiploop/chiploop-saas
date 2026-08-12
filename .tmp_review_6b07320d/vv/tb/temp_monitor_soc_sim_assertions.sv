/*
 * Auto-generated system-level SVA scaffold.
 * Derived from system integration intent and top-level simulation module.
 * This module observes only top-level signals and does not invent internal hierarchy.
 * Input sample: avdd, avss, clk, rd_addr, rd_en, reset_n, sensor_temp_celsius, wr_addr, wr_data, wr_en
 * Output sample: alert_irq, alert_status, rd_data, temp_code, threshold_code
 */

module temp_monitor_soc_sim_assertions (
  input logic alert_irq,
  input logic alert_status,
  input logic avdd,
  input logic avss,
  input logic clk,
  input logic rd_addr,
  input logic rd_data,
  input logic rd_en,
  input logic reset_n,
  input logic sensor_temp_celsius,
  input logic temp_code,
  input logic threshold_code,
  input logic wr_addr,
  input logic wr_data,
  input logic wr_en
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(reset_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $error("Reset signal has X/Z state.");
  property p_alert_irq_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(alert_irq);
  endproperty

  a_alert_irq_known_after_reset: assert property(p_alert_irq_known_after_reset)
    else $error("Top-level output alert_irq has X/Z after reset release.");
  property p_alert_status_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(alert_status);
  endproperty

  a_alert_status_known_after_reset: assert property(p_alert_status_known_after_reset)
    else $error("Top-level output alert_status has X/Z after reset release.");
  property p_rd_data_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(rd_data);
  endproperty

  a_rd_data_known_after_reset: assert property(p_rd_data_known_after_reset)
    else $error("Top-level output rd_data has X/Z after reset release.");
  property p_temp_code_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(temp_code);
  endproperty

  a_temp_code_known_after_reset: assert property(p_temp_code_known_after_reset)
    else $error("Top-level output temp_code has X/Z after reset release.");
  property p_threshold_code_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(threshold_code);
  endproperty

  a_threshold_code_known_after_reset: assert property(p_threshold_code_known_after_reset)
    else $error("Top-level output threshold_code has X/Z after reset release.");
  property p_alert_irq_single_bit_known;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(alert_irq);
  endproperty

  a_alert_irq_single_bit_known: assert property(p_alert_irq_single_bit_known)
    else $error("Indicator output alert_irq has X/Z after reset release.");
endmodule
