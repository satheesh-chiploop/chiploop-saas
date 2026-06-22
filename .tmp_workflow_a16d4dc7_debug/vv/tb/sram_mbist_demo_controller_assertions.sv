/*
 * Auto-generated SVA scaffold.
 * Derived from spec_json / digital_spec_json.
 * No hardcoded design-specific signal assumptions.
 */

module sram_mbist_demo_controller_assertions (
  input logic bist_done,
  input logic bist_fail,
  input logic bist_start,
  input logic clk,
  input logic irq,
  input logic [7:0] rd_addr,
  input logic [31:0] rd_data,
  input logic rd_en,
  input logic ready,
  input logic reset_n,
  input logic [7:0] wr_addr,
  input logic [31:0] wr_data,
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
  property p_ready_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(ready);
  endproperty

  a_ready_known_after_reset: assert property(p_ready_known_after_reset)
    else $error("Signal ready has X/Z after reset release.");
  property p_bist_done_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(bist_done);
  endproperty

  a_bist_done_known_after_reset: assert property(p_bist_done_known_after_reset)
    else $error("Signal bist_done has X/Z after reset release.");
  property p_bist_fail_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(bist_fail);
  endproperty

  a_bist_fail_known_after_reset: assert property(p_bist_fail_known_after_reset)
    else $error("Signal bist_fail has X/Z after reset release.");
  property p_irq_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(irq);
  endproperty

  a_irq_known_after_reset: assert property(p_irq_known_after_reset)
    else $error("Signal irq has X/Z after reset release.");

endmodule
