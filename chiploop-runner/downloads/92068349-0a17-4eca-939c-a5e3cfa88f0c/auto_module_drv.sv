`ifndef AUTO_MODULE_DRV_SV
`define AUTO_MODULE_DRV_SV
class auto_module_drv extends uvm_driver #(uvm_sequence_item);
  `uvm_component_utils(auto_module_drv)
  virtual auto_module_if vif;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  task run_phase(uvm_phase phase); `uvm_info("DRV","Running driver phase",UVM_LOW) endtask
endclass
`endif
