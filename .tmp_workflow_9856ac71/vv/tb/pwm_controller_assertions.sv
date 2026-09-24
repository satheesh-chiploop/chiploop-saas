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
  property p_req_001;
    @(posedge clk) disable iff (!reset_n)
      enable |=> (counter_value == (($past(counter_value) >= $past(period)) ? 8'h00 : ($past(counter_value) + 8'h01)));
  endproperty

  a_req_001: assert property(p_req_001) else $display("ASSERTION_FAILURE a_req_001");

  property c_req_001;
    @(posedge clk) disable iff (!reset_n)
      enable;
  endproperty

  c_req_001: cover property(c_req_001);

  // REQ-002
  property p_req_002;
    @(posedge clk) disable iff (!reset_n)
      (enable && ($past(counter_value) >= $past(period))) |=> (counter_value == 8'h00);
  endproperty

  a_req_002: assert property(p_req_002) else $display("ASSERTION_FAILURE a_req_002");

  property c_req_002;
    @(posedge clk) disable iff (!reset_n)
      (enable && ($past(counter_value) >= $past(period)));
  endproperty

  c_req_002: cover property(c_req_002);

  // REQ-003
  property p_req_003;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (pwm_out == (counter_value < duty_cycle));
  endproperty

  a_req_003: assert property(p_req_003) else $display("ASSERTION_FAILURE a_req_003");

  property c_req_003;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_003: cover property(c_req_003);

  // REQ-005
  property p_req_005;
    @(posedge clk)
      !reset_n |=> (counter_value == 8'h00);
  endproperty

  a_req_005: assert property(p_req_005) else $display("ASSERTION_FAILURE a_req_005");

  property c_req_005;
    @(posedge clk)
      !reset_n;
  endproperty

  c_req_005: cover property(c_req_005);

  // REQ-010
  property p_req_010;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (counter_value == (($past(reset_n) == 1'b0) ? 8'h00 : ((enable && ($past(counter_value) < $past(period))) ? ($past(counter_value) + 8'h01) : (($past(counter_value) >= $past(period)) ? 8'h00 : $past(counter_value)))));
  endproperty

  a_req_010: assert property(p_req_010) else $display("ASSERTION_FAILURE a_req_010");

  property c_req_010;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_010: cover property(c_req_010);

  // REQ-011
  property p_req_011;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (pwm_out == (counter_value < duty_cycle));
  endproperty

  a_req_011: assert property(p_req_011) else $display("ASSERTION_FAILURE a_req_011");

  property c_req_011;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_011: cover property(c_req_011);

  // REQ-012
  property p_req_012;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |=> (($unsigned(counter_value) < $unsigned(duty_cycle)) == (counter_value < duty_cycle)) && (($unsigned(counter_value) < $unsigned(period)) == (counter_value < period));
  endproperty

  a_req_012: assert property(p_req_012) else $display("ASSERTION_FAILURE a_req_012");

  property c_req_012;
    @(posedge clk) disable iff (!reset_n)
      1'b1;
  endproperty

  c_req_012: cover property(c_req_012);

  // REQ-016
  property p_req_016;
    @(posedge clk)
      !reset_n |=> ((counter_value == 8'h00) && (pwm_out == (duty_cycle != 8'h00)));
  endproperty

  a_req_016: assert property(p_req_016) else $display("ASSERTION_FAILURE a_req_016");

  property c_req_016;
    @(posedge clk)
      !reset_n;
  endproperty

  c_req_016: cover property(c_req_016);

endmodule