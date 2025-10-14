`default clocking @(posedge clk); endclocking`

`assert property (@(posedge clk)) 
  "reset_behavior" : ($reset && $count == 4'b0000);

assert property (@(posedge clk)) 
  "enable_disable" : (!$reset && (!$enable || $count == $old($count)));

assert property (@(posedge clk)) 
  "counter_transition" : ($reset || ($enable && $new($count) == $old($count) + 1));

assert property (@(posedge clk)) 
  "clock_stability" : !($clk && !$clk);

cover property (@(posedge clk)) 
  "overflow_underflow" : ($count >= 4'b1111 || $count < 0);

`