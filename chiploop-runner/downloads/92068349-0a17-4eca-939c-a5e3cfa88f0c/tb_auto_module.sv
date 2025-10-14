`timescale 1ns/1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
module tb_auto_module;
  bit clk;
  always #5 clk = ~clk;
  auto_module_if tb_if(clk);
  auto_module dut(.clk(tb_if.clk));
  initial begin
    clk = 0;
    run_test("uvm_test");
  end
endmodule
