`ifndef AUTO_MODULE_SEQ_SV
`define AUTO_MODULE_SEQ_SV
class auto_module_seq extends uvm_sequence #(uvm_sequence_item);
  `uvm_object_utils(auto_module_seq)
  function new(string name="auto_module_seq"); super.new(name); endfunction
  task body(); `uvm_info("SEQ","Running sequence",UVM_LOW) endtask
endclass
`endif
