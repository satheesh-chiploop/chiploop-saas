```
default clocking @(posedge clk); endclocking

property reset_behavior [label="Reset Behavior"];
assert property ($reset |--> $setup(1, 0) => count == 4'b0000);

property enable_disable [label="Enable/Disable Operation"];
assert property (counter_en |--> $setup(1, 0) && ~$setup(1, 1) => 
    ($rose(counter_en) |--> $next(count) == $old(count) + 1);

property transition_validity [label="Counter Transition Validity"];
assert property ($rose(counter_en) |--> $next(count) <= 4'b1111);

property clock_stability [label="Clock Stability"];
assert property (clk |--> $setup(1, 0) && ~$setup(1, 1) => 
    ($stable(clk) |--> $stable(count));

end
```