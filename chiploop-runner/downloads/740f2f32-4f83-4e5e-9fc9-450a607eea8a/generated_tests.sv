Here are the UVM testcases for the auto_module:

**Directed Tests**

```sv
class auto_module_directed_test extends uvm_test;
  `uvm_component_utils(auto_module_directed_test)

  function new(string name = "auto_module_directed_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Basic functionality test
    phase.raise_objection("start", UVM_NO_HANG);
    agent.start_item(0, 1); // count = 0001
    agent.finish_item();
    phase.drop_objection();

    // Corner case: reset test
    phase.raise_objection("start", UVM_NO_HANG);
    agent.start_item(0, 0); // count = 0000 (reset)
    agent.finish_item();
    phase.drop_objection();
  endtask

endclass
```

**Randomized Tests**

```sv
class auto_module_rand1_test extends uvm_test;
  `uvm_component_utils(auto_module_rand1_test)

  function new(string name = "auto_module_rand1_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Randomized test: counter_en = 0, count = random value
    rand int count;
    constraint c { count inside [0:15]; }
    phase.raise_objection("start", UVM_NO_HANG);
    uvm_do_with(agent, "count", count);
    agent.finish_item();
    phase.drop_objection();
  endtask

endclass

`define AUTO_MODULE_RAND2_TEST
class auto_module_rand2_test extends uvm_test;
  `uvm_component_utils(auto_module_rand2_test)

  function new(string name = "auto_module_rand2_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Randomized test: counter_en = 1, count = random value
    rand int count;
    constraint c { count inside [0:15]; }
    phase.raise_objection("start", UVM_NO_HANG);
    uvm_do_with(agent, "count", count + 1);
    agent.finish_item();
    phase.drop_objection();
  endtask

endclass

`define AUTO_MODULE_RAND3_TEST
class auto_module_rand3_test extends uvm_test;
  `uvm_component_utils(auto_module_rand3_test)

  function new(string name = "auto_module_rand3_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Randomized test: counter_en = random value, count = random value
    rand int counter_en;
    constraint ce { counter_en inside [0:1]; }
    rand int count;
    constraint c { count inside [0:15]; }
    phase.raise_objection("start", UVM_NO_HANG);
    agent.start_item(counter_en, count);
    agent.finish_item();
    phase.drop_objection();
  endtask

endclass

`define AUTO_MODULE_RAND4_TEST
class auto_module_rand4_test extends uvm_test;
  `uvm_component_utils(auto_module_rand4_test)

  function new(string name = "auto_module_rand4_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Randomized test: counter_en = random value, count = 0
    rand int counter_en;
    constraint ce { counter_en inside [0:1]; }
    phase.raise_objection("start", UVM_NO_HANG);
    agent.start_item(counter_en, 0);
    agent.finish_item();
    phase.drop_objection();
  endtask

endclass

`define AUTO_MODULE_RAND5_TEST
class auto_module_rand5_test extends uvm_test;
  `uvm_component_utils(auto_module_rand5_test)

  function new(string name = "auto_module_rand5_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    auto_module_agent agent;

    // Randomized test: counter_en = 0, count = random value
    rand int count;
    constraint c { count inside [0:15]; }
    $urandom(10); // seed for randomization
    phase.raise_objection("start", UVM_NO_HANG);
    start_item(agent, "count", count);
    finish_item();
    phase.drop_objection();
  endtask

endclass
```

Note that you can modify the constraints and randomized tests as per your requirements. Also, ensure to include the seed usage in each random test case.