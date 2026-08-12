/*
 * Auto-generated system SVA bind file.
 * Uses only top-level signals declared in the resolved system contract.
 */
bind temp_monitor_soc_sim temp_monitor_soc_sim_assertions u_temp_monitor_soc_sim_assertions (
  .alert_irq(alert_irq),
  .alert_status(alert_status),
  .avdd(avdd),
  .avss(avss),
  .clk(clk),
  .rd_addr(rd_addr),
  .rd_data(rd_data),
  .rd_en(rd_en),
  .reset_n(reset_n),
  .sensor_temp_celsius(sensor_temp_celsius),
  .temp_code(temp_code),
  .threshold_code(threshold_code),
  .wr_addr(wr_addr),
  .wr_data(wr_data),
  .wr_en(wr_en)
);
