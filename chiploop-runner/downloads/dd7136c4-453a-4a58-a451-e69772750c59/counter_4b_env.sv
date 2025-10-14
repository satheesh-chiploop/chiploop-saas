`ifndef COUNTER_4B_ENV_SV
`define COUNTER_4B_ENV_SV
class counter_4b_env extends uvm_env;
  `uvm_component_utils(counter_4b_env)
  counter_4b_drv drv;
  counter_4b_mon mon;
  counter_4b_seq seq;
  function new(string name, uvm_component parent); super.new(name,parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv=counter_4b_drv::type_id::create("drv",this);
    mon=counter_4b_mon::type_id::create("mon",this);
    seq=counter_4b_seq::type_id::create("seq",this);
  endfunction
endclass
`endif
