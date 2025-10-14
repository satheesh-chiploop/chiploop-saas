Here are some stimulus ideas and assertions for the `counter_4b` module using SystemVerilog and UVM:

**Stimulus Ideas:**

1. **Reset Stimulus:** Send a single reset pulse on the `reset` input, followed by a few clock cycles to ensure the counter is cleared.
```systemverilog
seq_item_port.write({reset});
#100; // Wait for 100 clocks
```
2. **Enable and Clock Stimulus:** Enable the counter with `enable` set to `1`, then increment the clock to see if the counter increments correctly.
```systemverilog
seq_item_port.write({1'b1}); // Enable = 1
#10; // Wait for 10 clocks
```
3. **Reset and Enable Stimulus:** Reset the counter, then enable it and increment the clock to verify that the counter resets and then starts counting from 0.
```systemverilog
seq_item_port.write({reset});
#100; // Wait for 100 clocks
seq_item_port.write({1'b1}); // Enable = 1
#10; // Wait for 10 clocks
```
4. **Long Run Stimulus:** Send a sequence of clock pulses while `enable` is set to `1`, verifying that the counter increments correctly over time.
```systemverilog
for (int i = 0; i < 100; i++) {
    seq_item_port.write({1'b1}); // Enable = 1
    #10; // Wait for 10 clocks
}
```
**Assertions:**

1. **Counter Reset Assertion:** Verify that the counter is cleared to `4'b0000` after a reset pulse.
```systemverilog
assertion_port.write(count == 4'b0000);
```
2. **Counter Increment Assertion:** Verify that the counter increments by one when `enable` is set to `1` and the clock pulses.
```systemverilog
for (int i = 0; i < 100; i++) {
    assertion_port.write(count == i);
}
```
3. **Counter Wraparound Assertion:** Verify that the counter wraps around to `4'b0000` when it reaches the maximum value (`4'b1111`) and then increments again.
```systemverlog
assertion_port.write(count == 4'b0000 && count != 4'b1111);
```
These stimulus ideas and assertions can be used as a starting point for verifying the `counter_4b` module using UVM. Note that these are just examples, and you may need to modify them or add more complex stimuli and assertions depending on your specific verification requirements.