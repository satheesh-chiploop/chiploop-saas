covergroup counter_cg(clk, reset, enable);
  coverpoint clk {
    bins valid_clk = { [0: $value == 1] },
         invalid_clk = { default: $value == 0 };
  }
  
  coverpoint reset {
    bins reset_high = { [0: $value == 1] },
        reset_low = { default: $value == 0 };
  }
  
  coverpoint enable {
    bins enable_high = { [0: $value == 1] },
        enable_low = { default: $value == 0 };
  }
  
  coverpoint state {
    bins zero = { [$value == 4'b0000] },
         one = { [$value == 4'b0001] },
         two = { [$value == 4'b0010] },
         three = { [$value == 4'b0011] },
         four = { [$value == 4'b0100] };
  }
  
  coverpoint count {
    bins zero_to_four = { [$value >= 4'h0000 && $value <= 4'h0004] },
        five_to_eight = { [$value >= 4'h0005 && $value <= 4'h0010] },
        nine_to_twelve = { [$value >= 4'h0011 && $value <= 4'h0012] };
  }
  
  cross enable, reset {
    bins en_reset_zero = { [enable == 1'b0 && reset == 1'b0] },
        en_reset_one = { [enable == 1'b0 && reset == 1'b1] },
        en_high_reset_low = { [enable == 1'b1 && reset == 1'b0] };
  }
  
  cross state, output {
    bins zero_zero = { [state == 4'b0000 && count == 4'b0000] },
        one_one = { [state == 4'b0001 && count == 4'b0001] },
        two_two = { [state == 4'b0010 && count == 4'b0010] },
        three_three = { [state == 4'b0011 && count == 4'b0011] };
  }
endcovergroup