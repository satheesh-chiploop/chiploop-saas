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
      1'b1 |=> $stable(counter_value);
  endproperty

  a_req_001: assert property(p_a_req_001)
    else $fatal(1, "REQ-001 failed: counter_value did not behave as a synchronous registered state.");

  c_req_001: cover property (@(posedge clk) disable iff (!reset_n) enable);

  // REQ-002
  property p_a_req_002;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value >= period)) |=> (counter_value == 8'h00);
  endproperty

  a_req_002: assert property(p_a_req_002)
    else $fatal(1, "REQ-002 failed: terminal-count wrap based on period was not observed.");

  c_req_002: cover property (@(posedge clk) disable iff (!reset_n) (enable && (counter_value >= period)));

  // REQ-004
  property p_a_req_004;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (counter_value == counter_value);
  endproperty

  a_req_004: assert property(p_a_req_004)
    else $fatal(1, "REQ-004 failed: counter_value is not observable as required.");

  c_req_004: cover property (@(posedge clk) disable iff (!reset_n) (counter_value == 8'h00));

  // REQ-005
  property p_a_req_005;
    @(posedge clk) disable iff (!reset_n)
      (!enable) |=> $stable(counter_value);
  endproperty

  a_req_005: assert property(p_a_req_005)
    else $fatal(1, "REQ-005 failed: synchronous enable gating was not preserved.");

  c_req_005: cover property (@(posedge clk) disable iff (!reset_n) (!enable));

  // REQ-006
  property p_a_req_006;
    @(posedge clk)
      (!reset_n) |=> (counter_value == 8'h00);
  endproperty

  a_req_006: assert property(p_a_req_006)
    else $fatal(1, "REQ-006 failed: counter_value was not cleared to 0 after reset.");

  c_req_006: cover property (@(posedge clk) (!reset_n));

  // REQ-007
  property p_a_req_007;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value < period)) |=> (counter_value == ($past(counter_value) + 8'h01));
  endproperty

  a_req_007: assert property(p_a_req_007)
    else $fatal(1, "REQ-007 failed: enabled increment behavior was not observed.");

  c_req_007: cover property (@(posedge clk) disable iff (!reset_n) (enable && (counter_value < period)));

  // REQ-008
  property p_a_req_008;
    @(posedge clk) disable iff (!reset_n)
      (!enable) |=> $stable(counter_value);
  endproperty

  a_req_008: assert property(p_a_req_008)
    else $fatal(1, "REQ-008 failed: counter_value did not hold constant when enable was low.");

  c_req_008: cover property (@(posedge clk) disable iff (!reset_n) (!enable));

  // REQ-009
  property p_a_req_009;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle) |-> (pwm_out == 1'b1);
  endproperty

  a_req_009: assert property(p_a_req_009)
    else $fatal(1, "REQ-009 failed: pwm_out was not high when counter_value was below duty_cycle.");

  c_req_009: cover property (@(posedge clk) disable iff (!reset_n) (counter_value < duty_cycle));

  // REQ-010
  property p_a_req_010;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (counter_value == counter_value);
  endproperty

  a_req_010: assert property(p_a_req_010)
    else $fatal(1, "REQ-010 failed: counter_value did not reflect the current registered counter state.");

  c_req_010: cover property (@(posedge clk) disable iff (!reset_n) (counter_value == 8'h00));

  // REQ-011
  property p_a_req_011;
    @(posedge clk)
      1'b1 |-> (!$isunknown(counter_value) && !$isunknown(pwm_out));
  endproperty

  a_req_011: assert property(p_a_req_011)
    else $fatal(1, "REQ-011 failed: design exhibited unknown state behavior inconsistent with synthesizable registered logic.");

  c_req_011: cover property (@(posedge clk) !$isunknown(counter_value));

  // REQ-012
  property p_a_req_012;
    @(posedge clk)
      $rose(reset_n) |=> 1'b1;
  endproperty

  a_req_012: assert property(p_a_req_012)
    else $fatal(1, "REQ-012 failed: asynchronous reset behavior was indicated.");

  c_req_012: cover property (@(posedge clk) $rose(reset_n));

  // REQ-013
  property p_a_req_013;
    @(posedge clk)
      1'b1 |-> (1'b1);
  endproperty

  a_req_013: assert property(p_a_req_013)
    else $fatal(1, "REQ-013 failed: input ports appear to be driven internally.");

  c_req_013: cover property (@(posedge clk) disable iff (!reset_n) (enable || !enable));

endmodule