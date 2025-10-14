Here are the UVM testcases for the auto_module:

**Directed Tests**

```systemverilog
class auto_module_directed_test extends uvm_test;
  `uvm_component_utils(auto_module_directed_test)

  function new(string name = "auto_module_directed_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_driver drv;
    auto_module_sequencer seq;

    drv = auto_module_driver::type_id::create("drv", this);
    seq = auto_module_sequencer::type_id::create("seq", this);

    // Basic functionality test
    phase.raise_objection("basic_func_test");
    drv.send_clk_reset Enable(0, 1); // reset for 2 cycles, enable off
    drv.send_clk_reset Enable(1, 0); // reset off, enable on
    drv.send_clk_reset Enable(0, 1); // reset on, enable off
    phase.drop_objection();

    // Corner case test - disable during reset
    phase.raise_objection("corner_case_test");
    drv.send_clk_reset Enable(0, 1); // reset for 2 cycles, enable off
    drv.send_clk_reset Enable(1, 0); // reset on, enable off
    drv.send_clk_reset Enable(0, 1); // reset off, enable on
    phase.drop_objection();
  endtask
endclass
```

**Randomized Tests**

```systemverilog
class auto_module_randN_test extends uvm_test;
  `uvm_component_utils(auto_module_randN_test)

  function new(string name = "auto_module_randN_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_driver drv;
    auto_module_sequencer seq;

    drv = auto_module_driver::type_id::create("drv", this);
    seq = auto_module_sequencer::type_id::create("seq", this);

    // Seed setup
    `urandom_seed(1234)

    // Test 1: Enable on reset
    phase.raise_objection("rand_test_1");
    uvm_do_with(drv, "test_enable_on_reset", { enable == 0; count == 4'b0000 });
    phase.drop_objection();

    // Test 2: Disable during reset
    phase.raise_objection("rand_test_2");
    uvm_do_with(drv, "test_disable_during_reset", { enable == 1; count == 4'b1111 });
    phase.drop_objection();

    // Test 3: Enable after reset
    phase.raise_objection("rand_test_3");
    uvm_do_with(drv, "test_enable_after_reset", { enable == 0; count == 4'b0001 });
    phase.drop_objection();

    // Test 4: Disable after reset
    phase.raise_objection("rand_test_4");
    uvm_do_with(drv, "test_disable_after_reset", { enable == 1; count == 4'b1110 });
    phase.drop_objection();

    // Test 5: Mixed scenarios
    phase.raise_objection("rand_test_5");
    uvm_do_with(drv, "test_mixed_scenarios", { enable == 0; count == 4'b1010 });
    phase.drop_objection();
  endtask
endclass

constraint auto_module_driver_seq {
  bit [3:0] count;
  `uvm_field_int(count, UVM_ALL_VALUE)
}

sequence test_enable_on_reset {
  let enable = 1;
  let count = 4'b0000;
  `uvm_do_with(drv, item, {enable;count})
}

sequence test_disable_during_reset {
  let enable = 0;
  let count = 4'b1111;
  `uvm_do_with(drv, item, {enable;count})
}

sequence test_enable_after_reset {
  let enable = 1;
  let count = 4'b0001;
  `uvm_do_with(drv, item, {enable;count})
}

sequence test_disable_after_reset {
  let enable = 0;
  let count = 4'b1110;
  `uvm_do_with(drv, item, {enable;count})
}

sequence test_mixed_scenarios {
  let enable = 1;
  let count = 4'b1010;
  `uvm_do_with(drv, item, {enable;count})
}
```

Note that the seed value is hardcoded to `1234` in the random tests. In a real-world scenario, you would typically use a parameterized seed or a more sophisticated seed setup mechanism.