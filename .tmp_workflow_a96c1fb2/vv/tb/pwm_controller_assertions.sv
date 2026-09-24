module pwm_controller_assertions (
  input logic clk,
  input logic [7:0] counter_value,
  input logic [7:0] duty_cycle,
  input logic enable,
  input logic [7:0] period,
  input logic pwm_out,
  input logic reset_n
);

  property p_reset_known;
    @(posedge clk)
      !$isunknown(reset_n);
  endproperty

  a_reset_known: assert property(p_reset_known)
    else $fatal(1, "Reset signal has X/Z state.");

  property p_pwm_out_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(pwm_out);
  endproperty

  a_pwm_out_known_after_reset: assert property(p_pwm_out_known_after_reset)
    else $fatal(1, "Signal pwm_out has X/Z after reset release.");

  property p_counter_value_known_after_reset;
    @(posedge clk) disable iff (!reset_n)
      !$isunknown(counter_value);
  endproperty

  a_counter_value_known_after_reset: assert property(p_counter_value_known_after_reset)
    else $fatal(1, "Signal counter_value has X/Z after reset release.");

  // REQ-001
  property p_a_req_001;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |=> (counter_value == $past(counter_value) + 8'd1) or (counter_value == 8'd0);
  endproperty

  a_req_001: assert property(p_a_req_001) else $display("ASSERTION_FAILURE a_req_001");

  property p_cover_req_001;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_001: cover property(p_cover_req_001);

  // REQ-003
  property p_a_req_003;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (pwm_out == (counter_value < duty_cycle));
  endproperty

  a_req_003: assert property(p_a_req_003) else $display("ASSERTION_FAILURE a_req_003");

  property p_cover_req_003;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_003: cover property(p_cover_req_003);

  // REQ-004
  property p_a_req_004;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (counter_value == $past(counter_value));
  endproperty

  a_req_004: assert property(p_a_req_004) else $display("ASSERTION_FAILURE a_req_004");

  property p_cover_req_004;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_004: cover property(p_cover_req_004);

  // REQ-005
  property p_a_req_005;
    @(posedge clk)
      !reset_n |=> (counter_value == 8'd0 && pwm_out == 1'b0);
  endproperty

  a_req_005: assert property(p_a_req_005) else $display("ASSERTION_FAILURE a_req_005");

  property p_cover_req_005;
    @(posedge clk)
      !reset_n;
  endproperty

  c_req_005: cover property(p_cover_req_005);

  // REQ-006
  property p_a_req_006;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'd0);
  endproperty

  a_req_006: assert property(p_a_req_006) else $display("ASSERTION_FAILURE a_req_006");

  property p_cover_req_006;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period));
  endproperty

  c_req_006: cover property(p_cover_req_006);

  // REQ-007
  property p_a_req_007;
    @(posedge clk) disable iff (!reset_n)
      (!enable) |=> (counter_value == $past(counter_value));
  endproperty

  a_req_007: assert property(p_a_req_007) else $display("ASSERTION_FAILURE a_req_007");

  property p_cover_req_007;
    @(posedge clk) disable iff (!reset_n)
      (!enable);
  endproperty

  c_req_007: cover property(p_cover_req_007);

  // REQ-008
  property p_a_req_008;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (pwm_out == (counter_value < duty_cycle));
  endproperty

  a_req_008: assert property(p_a_req_008) else $display("ASSERTION_FAILURE a_req_008");

  property p_cover_req_008;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_008: cover property(p_cover_req_008);

  // REQ-010
  property p_a_req_010;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period)) |=> (counter_value == ($past(counter_value) + 8'd1));
  endproperty

  a_req_010: assert property(p_a_req_010) else $display("ASSERTION_FAILURE a_req_010");

  property p_cover_req_010;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period));
  endproperty

  c_req_010: cover property(p_cover_req_010);

  // REQ-011
  property p_a_req_011;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> 1'b1;
  endproperty

  a_req_011: assert property(p_a_req_011) else $display("ASSERTION_FAILURE a_req_011");

  property p_cover_req_011;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_011: cover property(p_cover_req_011);

  // REQ-014
  property p_a_req_014;
    @(posedge clk)
      !reset_n |=> (counter_value == 8'd0 && pwm_out == 1'b0);
  endproperty

  a_req_014: assert property(p_a_req_014) else $display("ASSERTION_FAILURE a_req_014");

  property p_cover_req_014;
    @(posedge clk)
      !reset_n;
  endproperty

  c_req_014: cover property(p_cover_req_014);

endmodule