`ifndef AUTO_MODULE_ENV_SV
`define AUTO_MODULE_ENV_SV
class auto_module_env extends uvm_env;
  `uvm_component_utils(auto_module_env)
  auto_module_drv drv;
  auto_module_mon mon;
  auto_module_seq seq;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv=auto_module_drv::type_id::create("drv",this);
    mon=auto_module_mon::type_id::create("mon",this);
    seq=auto_module_seq::type_id::create("seq",this);
  endfunction
endclass
`endif
