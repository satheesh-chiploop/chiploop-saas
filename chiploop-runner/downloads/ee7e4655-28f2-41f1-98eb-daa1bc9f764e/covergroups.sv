Here's the SystemVerilog covergroup code for the given RTL:
```
covergroup counter_cg @( posedge clk );

  // Coverpoint: Enable signal
  cpg_enable: coverpoint enable {
    bins e0 = 'b0;
    bins e1 = 'b1;
  }

  // Coverpoint: Reset signal
  cpg_reset: coverpoint reset {
    bins r0 = 'b0;
    bins r1 = 'b1;
  }

  // Coverpoint: State (count)
  cpg_state: coverpoint count {
    bins [4] = '{default_bins};
  }

  // Cross-coverage for enable × reset
  xcp_enr: cross cpg_enable, cpg_reset {
    bins en_rst00 = '{0,0};
    bins en_rst01 = '{1,0};
    bins en_rst10 = '{0,1};
    bins en_rst11 = '{1,1};
  }

  // Cross-coverage for state × output
  xcp_sto: cross cpg_state, count {
    bins [4][4] = '{default_bins};
  }

endgroup
```