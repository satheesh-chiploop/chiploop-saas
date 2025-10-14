`ifndef COUNTER_4B_SEQ_SV
`define COUNTER_4B_SEQ_SV
class counter_4b_seq extends uvm_sequence #(uvm_sequence_item);
  `uvm_object_utils(counter_4b_seq)
  function new(string name="counter_4b_seq"); super.new(name); endfunction
  task body(); `uvm_info("SEQ","Running sequence",UVM_LOW) endtask
endclass
`endif
