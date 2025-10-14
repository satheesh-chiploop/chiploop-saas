Here's the SystemVerilog covergroup code:

```
covergroup counter_cg @(posedge clk);
  option.auto_bin_max = 100;
  
  // Clock and Reset Coverpoints
  cp_clk: coverpoint clk {
    bins valid_clk = 'h1; 
    bins invalid_clk = 'h0;
  }
  cp_reset: coverpoint reset {
    bins reset_high = 1'b1; 
    bins reset_low = 1'b0;
  }
  
  // Enable Coverpoint
  cp_enable: coverpoint enable {
    bins enable_high = 1'b1; 
    bins enable_low = 1'b0;
  }
  
  // State Coverpoint
  cp_state: coverpoint q {
    bins zero [0] = '{default: 0};
    bins one [1] = '{default: 1};
    bins two [2] = '{default: 2};
    bins three [3] = '{default: 4}; // 2^2
    bins four [4] = '{default: 8}; // 2^3
    automatic bins middle[] = '{default: (0, 4)};
  }
  
  // Cross Coverage
  cg_en_reset: cross cp_enable, cp_reset {
    bins enable_low_reset_high = '{cp_enable.enable_low} && {cp_reset.reset_high};
    bins enable_low_reset_low = '{cp_enable.enable_low} && {cp_reset.reset_low};
    bins enable_high_reset_high = '{cp_enable.enable_high} && {cp_reset.reset_high};
    bins enable_high_reset_low = '{cp_enable.enable_high} && {cp_reset.reset_low};
  }
  
  // State × Count Cross Coverage
  cg_state_count: cross cp_state, count {
    for (int i = 0; i <= 4; i++) begin
      foreach ([count[i]]) begin
        bins state_[i] = '{cp_state} == {i};
      end
    end
  }
  
endgroup : counter_cg;
```