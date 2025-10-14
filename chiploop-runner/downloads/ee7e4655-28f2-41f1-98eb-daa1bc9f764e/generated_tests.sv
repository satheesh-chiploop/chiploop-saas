Here are the UVM testcases for the counter_4b module:

**Directed Tests**

```verilog
class counter_4b_basic_test extends uvm_test;
  `uvm_component_utils(counter_4b_basic_test)

  function new(string name = "counter_4b_basic_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    counter_4b_model mdl;

    // Initialize the model
    mdl = new();
    uvm_config_db #(counter_4b_model) ::set(null, "mdl", "model");

    // Test basic functionality
    `uvm_do_with(mdl, "cnt_set(0)", clk("10ns"), reset("1ps"), enable("0"));
    `uvm_do_with(mdl, "cnt_set(1)", clk("20ns"), reset("0"), enable("1"));
    `uvm_do_with(mdl, "cnt_set(3)", clk("30ns"), reset("0"), enable("0"));

    // Test corner case: reset high during count
    `uvm_do_with(mdl, "cnt_set(4)", clk("40ns"), reset("1"), enable("0"));
  endtask

endclass

**Randomized Tests**

```verilog
class counter_4b_rand_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand_test)

  function new(string name = "counter_4b_rand_test");
    super.new(name);
  endfunction

  task run_phase(uvm_phase phase);
    rand counter_4b_model mdl;
    int seed;

    // Initialize the model and seed
    seed = $urandom % 1000;
    mdl = new(seed);

    // Test randomized count increments
    for (int i = 0; i < 10; i++) begin
      `uvm_do_with(mdl, "cnt_set({i})",
        clk($urandom() % 100 + 1),
        reset($urandom() % 2),
        enable($urandom() % 2)
      );
    end

    // Test randomized reset and count
    for (int i = 0; i < 5; i++) begin
      `uvm_do_with(mdl, "cnt_set({i})",
        clk($urandom() % 100 + 1),
        reset($urandom() % 2),
        enable($urandom() % 2)
      );
      mdl.reset(1);
      #10;
      mdl.reset(0);
    end
  endtask

endclass
```

Note: The seed value is randomly generated using `$urandom()` and used to initialize the `counter_4b_model` instance.