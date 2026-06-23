/*
 * Auto-generated SVA scaffold.
 * Derived from spec_json / digital_spec_json.
 * No hardcoded design-specific signal assumptions.
 */

module pwm_controller_assertions (
  input logic clk,
  input logic [7:0] counter_value,
  input logic pwm_out,
  input logic [7:0] rd_addr,
  input logic [7:0] rd_data,
  input logic rd_en,
  input logic reset_n,
  input logic [7:0] wr_addr,
  input logic [7:0] wr_data,
  input logic wr_en
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(reset_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $error("Reset signal has X/Z state.");
  property p_rd_data_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(rd_data);
  endproperty

  a_rd_data_known_after_reset: assert property(p_rd_data_known_after_reset)
    else $error("Signal rd_data has X/Z after reset release.");
  property p_pwm_out_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(pwm_out);
  endproperty

  a_pwm_out_known_after_reset: assert property(p_pwm_out_known_after_reset)
    else $error("Signal pwm_out has X/Z after reset release.");
  property p_counter_value_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(counter_value);
  endproperty

  a_counter_value_known_after_reset: assert property(p_counter_value_known_after_reset)
    else $error("Signal counter_value has X/Z after reset release.");

endmodule
