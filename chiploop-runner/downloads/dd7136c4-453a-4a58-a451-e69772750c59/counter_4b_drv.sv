`ifndef COUNTER_4B_DRV_SV
`define COUNTER_4B_DRV_SV
class counter_4b_drv extends uvm_driver #(uvm_sequence_item);
  `uvm_component_utils(counter_4b_drv)
  virtual counter_4b_if vif;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  task run_phase(uvm_phase phase); `uvm_info("DRV","Running driver phase",UVM_LOW) endtask
endclass
`endif
