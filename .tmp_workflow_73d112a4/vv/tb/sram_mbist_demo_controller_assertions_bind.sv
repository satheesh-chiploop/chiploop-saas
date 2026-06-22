/*
 * Auto-generated SVA bind file.
 * Uses only spec-declared signals.
 */
bind sram_mbist_demo_controller sram_mbist_demo_controller_assertions u_sram_mbist_demo_controller_assertions (
  .clk(clk),
  .reset_n(reset_n),
  .wr_en(wr_en),
  .wr_addr(wr_addr),
  .wr_data(wr_data),
  .rd_en(rd_en),
  .rd_addr(rd_addr),
  .bist_start(bist_start),
  .rd_data(rd_data),
  .ready(ready),
  .bist_done(bist_done),
  .bist_fail(bist_fail),
  .irq(irq)
);
