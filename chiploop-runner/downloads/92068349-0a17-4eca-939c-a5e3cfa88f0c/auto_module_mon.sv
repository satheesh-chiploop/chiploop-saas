`ifndef AUTO_MODULE_MON_SV
`define AUTO_MODULE_MON_SV
class auto_module_mon extends uvm_monitor;
  `uvm_component_utils(auto_module_mon)
  virtual auto_module_if vif;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  task run_phase(uvm_phase phase); `uvm_info("MON","Running monitor phase",UVM_LOW) endtask
endclass
`endif
