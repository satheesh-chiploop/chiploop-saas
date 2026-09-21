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
    else $error("Reset signal has X/Z state.");

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

  // REQ-001
  property p_a_req_001;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |=> $stable(counter_value) or (counter_value == $past(counter_value) + 8'd1) or (counter_value == 8'd0);
  endproperty

  a_req_001: assert property(p_a_req_001);

  c_req_001: cover property (@(posedge clk) disable iff (!reset_n) 1'b1);

  // REQ-002
  property p_a_req_002;
    @(posedge clk) disable iff (!reset_n)
      (enable && ($past(counter_value) == period)) |=> (counter_value == 8'd0);
  endproperty

  a_req_002: assert property(p_a_req_002);

  c_req_002: cover property (@(posedge clk) disable iff (!reset_n) (enable && ($past(counter_value) == period)));

  // REQ-003
  property p_a_req_003;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle) |-> (pwm_out == 1'b1);
  endproperty

  a_req_003: assert property(p_a_req_003);

  c_req_003: cover property (@(posedge clk) disable iff (!reset_n) (counter_value < duty_cycle));

  // REQ-004
  property p_a_req_004;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (counter_value == counter_value);
  endproperty

  a_req_004: assert property(p_a_req_004);

  c_req_004: cover property (@(posedge clk) disable iff (!reset_n) 1'b1);

  // REQ-005
  property p_a_req_005;
    @(posedge clk)
      (!reset_n) |=> (counter_value == 8'd0 && pwm_out == 1'b0);
  endproperty

  a_req_005: assert property(p_a_req_005);

  c_req_005: cover property (@(posedge clk) (!reset_n));

  // REQ-006
  property p_a_req_006;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |=> $stable(counter_value) or (counter_value == $past(counter_value) + 8'd1) or (counter_value == 8'd0);
  endproperty

  a_req_006: assert property(p_a_req_006);

  c_req_006: cover property (@(posedge clk) disable iff (!reset_n) 1'b1);

  // REQ-007
  property p_a_req_007;
    @(posedge clk) disable iff (!reset_n)
      (!enable) |=> (counter_value == $past(counter_value));
  endproperty

  a_req_007: assert property(p_a_req_007);

  c_req_007: cover property (@(posedge clk) disable iff (!reset_n) (!enable));

  // REQ-008
  property p_a_req_008;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'd0);
  endproperty

  a_req_008: assert property(p_a_req_008);

  c_req_008: cover property (@(posedge clk) disable iff (!reset_n) (enable && (counter_value == period)));

  // REQ-009
  property p_a_req_009;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value < period)) |=> (counter_value == $past(counter_value) + 8'd1);
  endproperty

  a_req_009: assert property(p_a_req_009);

  c_req_009: cover property (@(posedge clk) disable iff (!reset_n) (enable && (counter_value < period)));

  // REQ-010
  property p_a_req_010;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle) |-> (pwm_out == 1'b1);
  endproperty

  a_req_010: assert property(p_a_req_010);

  c_req_010: cover property (@(posedge clk) disable iff (!reset_n) (counter_value < duty_cycle));

  // REQ-011
  property p_a_req_011;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (pwm_out == ((counter_value < duty_cycle) ? 1'b1 : 1'b0));
  endproperty

  a_req_011: assert property(p_a_req_011);

  c_req_011: cover property (@(posedge clk) disable iff (!reset_n) 1'b1);

  // REQ-012
  property p_a_req_012;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |=> (((counter_value < duty_cycle) == (counter_value < duty_cycle)) && ((counter_value < period) == (counter_value < period)));
  endproperty

  a_req_012: assert property(p_a_req_012);

  c_req_012: cover property (@(posedge clk) disable iff (!reset_n) 1'b1);

endmodule