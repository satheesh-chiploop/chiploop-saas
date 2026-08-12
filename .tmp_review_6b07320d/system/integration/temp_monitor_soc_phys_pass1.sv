module temp_monitor_soc_phys (
  output logic alert_irq,
  output logic alert_status,
  input logic avdd,
  input logic avss,
  input logic clk,
  input logic [7:0] rd_addr,
  output logic [15:0] rd_data,
  input logic rd_en,
  input logic reset_n,
  input logic [15:0] sensor_temp_celsius,
  output logic [11:0] temp_code,
  output logic [11:0] threshold_code,
  input logic [7:0] wr_addr,
  input logic [15:0] wr_data,
  input logic wr_en
);

  // NOTE: physical top may still use behavioral analog override if no physical macro wrapper was supplied.

  // Auto-generated interconnect wires
  logic w_10_u_analog_adc_valid_u_digital_adc_valid;
  logic w_8_u_digital_sample_req_u_analog_sample_req;
  logic [11:0] w_9_u_analog_adc_code_u_digital_adc_code;

  temp_sensor_adc_model u_analog (
    .adc_code(w_9_u_analog_adc_code_u_digital_adc_code),
    .adc_valid(w_10_u_analog_adc_valid_u_digital_adc_valid),
    .avdd(avdd),
    .avss(avss),
    .sample_req(w_8_u_digital_sample_req_u_analog_sample_req),
    .sensor_temp_celsius(sensor_temp_celsius)
  );

  temp_monitor_digital u_digital (
    .adc_code(w_9_u_analog_adc_code_u_digital_adc_code),
    .adc_valid(w_10_u_analog_adc_valid_u_digital_adc_valid),
    .alert_irq(alert_irq),
    .alert_status(alert_status),
    .clk(clk),
    .rd_addr(rd_addr),
    .rd_data(rd_data),
    .rd_en(rd_en),
    .reset_n(reset_n),
    .sample_req(w_8_u_digital_sample_req_u_analog_sample_req),
    .temp_code(temp_code),
    .threshold_code(threshold_code),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .wr_en(wr_en)
  );

endmodule