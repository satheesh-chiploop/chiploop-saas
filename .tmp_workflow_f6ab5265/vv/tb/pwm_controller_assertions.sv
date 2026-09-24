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

  property p_req_001;
    @(posedge clk)
      !reset_n |=> (counter_value == 8'h00);
  endproperty

  a_req_001: assert property(p_req_001) else $display("ASSERTION_FAILURE a_req_001");

  c_req_001: cover property (@(posedge clk) !reset_n);

  property p_req_002;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'h00);
  endproperty

  a_req_002: assert property(p_req_002) else $display("ASSERTION_FAILURE a_req_002");

  c_req_002: cover property (@(posedge clk) disable iff (!reset_n) (enable && (counter_value == period)));

  property p_req_003;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle) |-> (pwm_out == 1'b1);
  endproperty

  a_req_003: assert property(p_req_003) else $display("ASSERTION_FAILURE a_req_003");

  c_req_003: cover property (@(posedge clk) disable iff (!reset_n) (counter_value < duty_cycle));

  property p_req_004;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (!$isunknown(counter_value));
  endproperty

  a_req_004: assert property(p_req_004) else $display("ASSERTION_FAILURE a_req_004");

  c_req_004: cover property (@(posedge clk) disable iff (!reset_n) !$isunknown(counter_value));

  property p_req_011;
    @(posedge clk) disable iff (!reset_n)
      (duty_cycle == 8'h00) |-> (pwm_out == 1'b0);
  endproperty

  a_req_011: assert property(p_req_011) else $display("ASSERTION_FAILURE a_req_011");

  c_req_011: cover property (@(posedge clk) disable iff (!reset_n) (duty_cycle == 8'h00));

  property p_req_012;
    @(posedge clk) disable iff (!reset_n)
      (duty_cycle > period) |-> ((counter_value < duty_cycle) |-> (pwm_out == 1'b1));
  endproperty

  a_req_012: assert property(p_req_012) else $display("ASSERTION_FAILURE a_req_012");

  c_req_012: cover property (@(posedge clk) disable iff (!reset_n) (duty_cycle > period));

  property p_req_014;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> (!$isunknown(pwm_out) && !$isunknown(counter_value));
  endproperty

  a_req_014: assert property(p_req_014) else $display("ASSERTION_FAILURE a_req_014");

  c_req_014: cover property (@(posedge clk) disable iff (!reset_n) (enable || !enable));

  property p_req_017;
    @(posedge clk) !reset_n |=> ((counter_value == 8'h00) && (pwm_out == 1'b0));
  endproperty

  a_req_017: assert property(p_req_017) else $display("ASSERTION_FAILURE a_req_017");

  c_req_017: cover property (@(posedge clk) !reset_n);

endmodule