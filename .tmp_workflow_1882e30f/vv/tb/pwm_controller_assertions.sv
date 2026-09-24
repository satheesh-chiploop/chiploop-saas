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
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period)) |=> (counter_value == ($past(counter_value) + 8'h01));
  endproperty

  a_req_001: assert property (p_req_001) else $display("ASSERTION_FAILURE a_req_001");

  property p_cover_req_001;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period));
  endproperty

  c_req_001: cover property (p_cover_req_001);

  property p_req_002;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle) |-> (pwm_out == 1'b1);
  endproperty

  a_req_002: assert property (p_req_002) else $display("ASSERTION_FAILURE a_req_002");

  property p_cover_req_002;
    @(posedge clk) disable iff (!reset_n)
      (counter_value < duty_cycle);
  endproperty

  c_req_002: cover property (p_cover_req_002);

  property p_req_003;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'h00);
  endproperty

  a_req_003: assert property (p_req_003) else $display("ASSERTION_FAILURE a_req_003");

  property p_cover_req_003;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period));
  endproperty

  c_req_003: cover property (p_cover_req_003);

  property p_req_004;
    @(posedge clk) disable iff (!reset_n)
      (counter_value == $past(counter_value)) |-> (counter_value == $past(counter_value));
  endproperty

  a_req_004: assert property (p_req_004) else $display("ASSERTION_FAILURE a_req_004");

  property p_cover_req_004;
    @(posedge clk) disable iff (!reset_n)
      (counter_value == $past(counter_value));
  endproperty

  c_req_004: cover property (p_cover_req_004);

  property p_req_005;
    @(posedge clk)
      (!reset_n) |=> ((counter_value == 8'h00) && (pwm_out == 1'b0));
  endproperty

  a_req_005: assert property (p_req_005) else $display("ASSERTION_FAILURE a_req_005");

  property p_cover_req_005;
    @(posedge clk)
      (!reset_n);
  endproperty

  c_req_005: cover property (p_cover_req_005);

  property p_req_006;
    @(posedge clk)
      (!reset_n) |=> (counter_value == 8'h00);
  endproperty

  a_req_006: assert property (p_req_006) else $display("ASSERTION_FAILURE a_req_006");

  property p_cover_req_006;
    @(posedge clk)
      (!reset_n);
  endproperty

  c_req_006: cover property (p_cover_req_006);

  property p_req_007;
    @(posedge clk) disable iff (!reset_n)
      (!enable) |=> $stable(counter_value);
  endproperty

  a_req_007: assert property (p_req_007) else $display("ASSERTION_FAILURE a_req_007");

  property p_cover_req_007;
    @(posedge clk) disable iff (!reset_n)
      (!enable);
  endproperty

  c_req_007: cover property (p_cover_req_007);

  property p_req_008;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'h00);
  endproperty

  a_req_008: assert property (p_req_008) else $display("ASSERTION_FAILURE a_req_008");

  property p_cover_req_008;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period));
  endproperty

  c_req_008: cover property (p_cover_req_008);

  property p_req_009;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period)) |=> (counter_value == ($past(counter_value) + 8'h01));
  endproperty

  a_req_009: assert property (p_req_009) else $display("ASSERTION_FAILURE a_req_009");

  property p_cover_req_009;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value != period));
  endproperty

  c_req_009: cover property (p_cover_req_009);

  property p_req_010;
    @(posedge clk) disable iff (!reset_n)
      1'b1 |-> ((pwm_out == ((counter_value < duty_cycle) ? 1'b1 : 1'b0)));
  endproperty

  a_req_010: assert property (p_req_010) else $display("ASSERTION_FAILURE a_req_010");

  property p_cover_req_010;
    @(posedge clk) disable iff (!reset_n)
      (pwm_out == ((counter_value < duty_cycle) ? 1'b1 : 1'b0));
  endproperty

  c_req_010: cover property (p_cover_req_010);

  property p_req_011;
    @(posedge clk) disable iff (!reset_n)
      (pwm_out == ((counter_value < duty_cycle) ? 1'b1 : 1'b0));
  endproperty

  a_req_011: assert property (p_req_011) else $display("ASSERTION_FAILURE a_req_011");

  property p_cover_req_011;
    @(posedge clk) disable iff (!reset_n)
      (pwm_out == ((counter_value < duty_cycle) ? 1'b1 : 1'b0));
  endproperty

  c_req_011: cover property (p_cover_req_011);

  property p_req_012;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period)) |=> (counter_value == 8'h00);
  endproperty

  a_req_012: assert property (p_req_012) else $display("ASSERTION_FAILURE a_req_012");

  property p_cover_req_012;
    @(posedge clk) disable iff (!reset_n)
      (enable && (counter_value == period));
  endproperty

  c_req_012: cover property (p_cover_req_012);

  property p_req_015;
    @(posedge clk)
      (!reset_n) |=> ((counter_value == 8'h00) && (pwm_out == 1'b0));
  endproperty

  a_req_015: assert property (p_req_015) else $display("ASSERTION_FAILURE a_req_015");

  property p_cover_req_015;
    @(posedge clk)
      (!reset_n);
  endproperty

  c_req_015: cover property (p_cover_req_015);

endmodule