Here are the UVM testcases for the counter_4b module:

```systemverilog
// Directed tests
class counter_4b_basic_test extends uvm_test;
  `uvm_component_utils(counter_4b_basic_test)

  function new(string name = "counter_4b_basic_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Basic functionality test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    // Test count reset
    agent.set_reset(1'b1);
    run_phase.wait_for_grants();
    assert(agent.get_count() == 0);

    // Test count increment
    agent.set_enable(1'b1);
    for (int i = 0; i < 4; i++) begin
      run_phase.raise_item(i);
    end
    run_phase.item_done();
    assert(agent.get_count() == 4'd4);

    // Test count disable
    agent.set_enable(1'b0);
    run_phase.wait_for_grants();
    assert(agent.get_count() == 4'd4);
  endtask
endclass

class counter_4b_corner_test extends uvm_test;
  `uvm_component_utils(counter_4b_corner_test)

  function new(string name = "counter_4b_corner_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Corner case test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    // Test count reset and increment with reset
    agent.set_reset(1'b1);
    run_phase.wait_for_grants();
    assert(agent.get_count() == 0);

    agent.set_enable(1'b1);
    for (int i = 0; i < 4; i++) begin
      run_phase.raise_item(i);
    end
    run_phase.item_done();
    agent.set_reset(1'b0);
    run_phase.wait_for_grants();
    assert(agent.get_count() == 0);
  endtask
endclass

// Randomized tests
class counter_4b_rand1_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand1_test)

  function new(string name = "counter_4b_rand1_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Randomized test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    rand bit [3:0] count;
    constraint c {
      count > 4'd0;
    }

    for (int i = 0; i < 10; i++) begin
      count = $urandom%16 + 4'd1;
      uvm_do_with(agent, item(count));
    end

    run_phase.item_done();
  endtask
endclass

class counter_4b_rand2_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand2_test)

  function new(string name = "counter_4b_rand2_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Randomized test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    rand bit [3:0] count;
    constraint c {
      count < 4'd15;
    }

    for (int i = 0; i < 10; i++) begin
      count = $urandom%16 + 4'd1;
      uvm_do_with(agent, item(count));
    end

    run_phase.item_done();
  endtask
endclass

class counter_4b_rand3_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand3_test)

  function new(string name = "counter_4b_rand3_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Randomized test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    rand bit [3:0] count;
    constraint c {
      count == 4'd2;
    }

    for (int i = 0; i < 10; i++) begin
      uvm_do_with(agent, item(count));
    end

    run_phase.item_done();
  endtask
endclass

class counter_4b_rand4_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand4_test)

  function new(string name = "counter_4b_rand4_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Randomized test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    rand bit [3:0] count;
    constraint c {
      count > 4'd5;
    }

    for (int i = 0; i < 10; i++) begin
      count = $urandom%16 + 4'd1;
      uvm_do_with(agent, item(count));
    end

    run_phase.item_done();
  endtask
endclass

class counter_4b_rand5_test extends uvm_test;
  `uvm_component_utils(counter_4b_rand5_test)

  function new(string name = "counter_4b_rand5_test");
    super.new(name);
  endfunction

  task run_phase(uvm_run_phase run_phase);
    // Randomized test
    counter_4b_model agent = counter_4b_model::type_id::create("agent");
    uvm_config_db#(uvm_objection*)::set(null, "uvm_test_top", "objection", uvm_top.get());
    agent.configure(null);
    agent.build_phase(run_phase);
    agent.start();

    rand bit [3:0] count;
    constraint c {
      count < 4'd10;
    }

    for (int i = 0; i < 10; i++) begin
      count = $urandom%16 + 4'd1;
      uvm_do_with(agent, item(count));
    end

    run_phase.item_done();
  endtask
endclass