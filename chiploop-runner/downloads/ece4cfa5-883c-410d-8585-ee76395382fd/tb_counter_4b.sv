`timescale 1ns/1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
module tb_counter_4b;
  bit clk;
  always #5 clk = ~clk;
  counter_4b_if tb_if(clk);
  counter_4b dut(.clk(tb_if.clk));
  initial begin
    clk = 0;
    run_test("uvm_test");
  end
endmodule
