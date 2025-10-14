Here are some potential stimulus ideas and assertions for the `counter_4b` module:

**Stimulus Ideas:**

1. **Count enable**: Enable the counter to count up by setting `enable` high for a few clock cycles, then disable it.

```verilog
class CounterEnable Stimulus extends uvm_sequence_item;

  rand bit [3:0] start_value;
  rand int num_cycles;

  `uvm_object_utils(CounterEnable)

  function new(string name = "CounterEnable");
    super(name);
  endfunction

  task body();
    count_start(start_value, num_cycles);
  endtask

  task count_start(bit [3:0] start_value, int num_cycles);
    #10; // wait for initial state to stabilize
    $display("Enabling counter...");
    set_enable(1);
    repeat(num_cycles) {
      @(posedge clk);
    }
    $display("Disabling counter...");
    set_enable(0);
  endtask

  task set_enable(bit enable);
    if (enable) begin
      `uvm_info("CounterEnable", "Enabling counter", UVM_LOW)
    end else begin
      `uvm_info("CounterEnable", "Disabling counter", UVM_LOW)
    end
  endtask

endclass
```

2. **Count reset**: Reset the counter to its initial state by setting `reset` high for a few clock cycles.

```verilog
class CounterReset Stimulus extends uvm_sequence_item;

  rand int num_cycles;

  `uvm_object_utils(CounterReset)

  function new(string name = "CounterReset");
    super(name);
  endfunction

  task body();
    count_reset(num_cycles);
  endtask

  task count_reset(int num_cycles);
    $display("Resetting counter...");
    repeat(num_cycles) {
      @(posedge clk);
      set_reset(1);
    }
    $display("Counter reset complete.");
  endtask

endclass
```

3. **Count verify**: Verify the final value of the counter by checking its value against an expected value.

```verilog
class CounterVerify Assertion extends uvm_sequence_item;

  rand bit [3:0] expected_value;

  `uvm_object_utils(CounterVerify)

  function new(string name = "CounterVerify");
    super(name);
  endfunction

  task body();
    verify_count(expected_value);
  endtask

  task verify_count(bit [3:0] expected_value);
    bit [3:0] actual_value;
    #10; // wait for final state to stabilize
    `uvm_info("CounterVerify", $sformatf("Expected count value: %b, Actual value: %b", expected_value, count), UVM_LOW)
  endtask

endclass
```

**Assertions:**

1. **Count unchanged during reset**: Verify that the counter does not change its value during a reset cycle.

```verilog
class CounterResetAssertion extends uvm_assertion;

  `uvm_object_utils(CounterResetAssertion)

  function new(string name = "CounterResetAssertion");
    super(name);
  endfunction

  task body();
    assert(count == 4'b0000, $sformatf("Count unchanged during reset: expected %b, actual %b", 4'b0000, count));
  endtask

endclass
```

2. **Count increments correctly**: Verify that the counter increments its value by one when enabled.

```verilog
class CounterIncrementAssertion extends uvm_assertion;

  `uvm_object_utils(CounterIncrementAssertion)

  function new(string name = "CounterIncrementAssertion");
    super(name);
  endfunction

  task body();
    bit [3:0] previous_count;
    repeat(4) {
      @(posedge clk);
      assert(count == previous_count + 1'b0001, $sformatf("Count increment incorrect: expected %b, actual %b", previous_count + 1'b0001, count));
      previous_count = count;
    }
  endtask

endclass
```

Note that these are just starting points and may need to be modified or extended based on the specific requirements of your verification environment.