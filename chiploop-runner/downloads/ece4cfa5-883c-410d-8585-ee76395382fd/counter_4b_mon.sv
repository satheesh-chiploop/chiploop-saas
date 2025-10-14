`ifndef COUNTER_4B_MON_SV
`define COUNTER_4B_MON_SV
class counter_4b_mon extends uvm_monitor;
  `uvm_component_utils(counter_4b_mon)
  virtual counter_4b_if vif;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  task run_phase(uvm_phase phase); `uvm_info("MON","Running monitor phase",UVM_LOW) endtask
endclass
`endif
