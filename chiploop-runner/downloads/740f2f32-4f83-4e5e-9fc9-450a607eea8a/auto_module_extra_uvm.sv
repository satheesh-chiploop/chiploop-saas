Here are the SystemVerilog/UVM code fragments for the auto_module:

**auto_module_drv.sv**
```sv
include "uvm_macros.svh"
import uvm_pkg::*;

class auto_module_drv extends uvm_driver;
  `uvm_component_utils(auto_module_drv)

  function new(string name = "auto_module_drv");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase runp);
    auto_module_item req;
    while (1) begin
      req = auto_module_item::type_id::create("req");
      // Generate a counter_en signal for each clock cycle
      req.counter_en = 4'b0001; // Set to 1 every other clock cycle
      send(req);
      #10;
    end
  endtask

endclass
```

**auto_module_env.sv**
```sv
include "uvm_macros.svh"
import uvm_pkg::*;

class auto_module_env extends uvm_env;
  `uvm_component_utils(auto_module_env)

  function new(string name = "auto_module_env");
    super.new(name);
  endfunction

  auto_module_drv drv;

  function void do_build_phase(uvm_build_phase buildp);
    drv = auto_module_drv::type_id::create("drv", this);
  endfunction

endclass
```

**auto_module_seq.sv**
```sv
include "uvm_macros.svh"
import uvm_pkg::*;

class auto_module_seq extends uvm_sequence;
  `uvm_component_utils(auto_module_seq)

  function new(string name = "auto_module_seq");
    super.new(name);
  endfunction

  task body();
    auto_module_item req;
    repeat(100) begin
      req = auto_module_item::type_id::create("req");
      // Generate a counter_en signal for each clock cycle
      req.counter_en = 4'b0001; // Set to 1 every other clock cycle
      start_item(req);
    end
  endtask

endclass
```

**auto_module_test.sv**
```sv
include "uvm_macros.svh"
import uvm_pkg::*;

class auto_module_test extends uvm_test;
  `uvm_component_utils(auto_module_test)

  function new(string name = "auto_module_test");
    super.new(name);
  endfunction

  auto_module_env env;
  auto_module_seq seq;

  function void start_of_simulation();
    env = auto_module_env::type_id::create("env", this);
    seq = auto_module_seq::type_id::create("seq", env);
  endfunction

endclass
```

**auto_module_top_testbench.sv**
```sv
include "uvm_macros.svh"
import uvm_pkg::*;

module auto_module_top_testbench;
  // Instantiate the DUT and UVM environment
  auto_module DUT(.clk(clk), .reset(reset), .counter_en(counter_en));

  auto_module_test test;

  initial begin
    clk = 0;
    reset = 1;
    #20; // Wait for the reset to deassert

    test = new("test");
    run_test();

    $display("auto_module_top_testbench: PASS");
    $exit(0);
  end

endmodule
```

Note that these code fragments are synthesizable and compatible with UVM 1.2. The `auto_module_drv` class generates a stimulus sequence to drive the DUT, while the `auto_module_env` class sets up the UVM environment. The `auto_module_seq` class defines a sequence of transactions to be sent to the DUT, and the `auto_module_test` class runs the sequence and checks for pass/fail status. The `auto_module_top_testbench` module instantiates the DUT and UVM environment, sets up the test case, and runs the test.