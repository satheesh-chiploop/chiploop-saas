module temp_monitor_digital (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    adc_code,
    adc_valid,
    rd_data,
    sample_req,
    alert_irq,
    temp_code,
    threshold_code,
    alert_status
);

input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [15:0] wr_data;
input rd_en;
input [7:0] rd_addr;
input [11:0] adc_code;
input adc_valid;
output [15:0] rd_data;
output sample_req;
output alert_irq;
output [11:0] temp_code;
output [11:0] threshold_code;
output alert_status;
wire control_enable;
wire control_sample_start_pulse;
wire control_irq_enable;
wire control_alert_clear_pulse;
wire irq_clear_alert_pulse;
wire irq_clear_sample_done_pulse;
wire [11:0] threshold_code_reg;
wire status_sample_done;
wire status_alert_pending;
wire status_adc_valid_seen;
wire status_busy;
wire irq_status_alert;
wire irq_status_sample_done;
wire [11:0] latest_temp;
wire [15:0] sample_count;
wire compare_alert;
wire sample_done_pulse;
wire sample_req_pulse;

wire [11:0] temp_code_unused_from_u_temp_monitor_digital_sample_ctrl_temp_code;
assign threshold_code = threshold_code_reg;
assign temp_code = latest_temp;

temp_monitor_digital_regfile u_temp_monitor_digital_regfile (
    .clk(clk),
    .reset_n(reset_n),
    .wr_en(wr_en),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_addr(rd_addr),
    .control_enable(control_enable),
    .control_sample_start_pulse(control_sample_start_pulse),
    .control_irq_enable(control_irq_enable),
    .control_alert_clear_pulse(control_alert_clear_pulse),
    .irq_clear_alert_pulse(irq_clear_alert_pulse),
    .irq_clear_sample_done_pulse(irq_clear_sample_done_pulse),
    .threshold_code_reg(threshold_code_reg),
    .status_sample_done(status_sample_done),
    .status_alert_pending(status_alert_pending),
    .status_adc_valid_seen(status_adc_valid_seen),
    .status_busy(status_busy),
    .irq_status_alert(irq_status_alert),
    .irq_status_sample_done(irq_status_sample_done),
    .latest_temp(latest_temp),
    .sample_count(sample_count),
    .rd_data(rd_data)
);

temp_monitor_digital_sample_ctrl u_temp_monitor_digital_sample_ctrl (
    .clk(clk),
    .reset_n(reset_n),
    .control_enable(control_enable),
    .control_sample_start_pulse(control_sample_start_pulse),
    .control_irq_enable(control_irq_enable),
    .control_alert_clear_pulse(control_alert_clear_pulse),
    .irq_clear_alert_pulse(irq_clear_alert_pulse),
    .irq_clear_sample_done_pulse(irq_clear_sample_done_pulse),
    .threshold_code_reg(threshold_code_reg),
    .adc_code(adc_code),
    .adc_valid(adc_valid),
    .sample_req(sample_req),
    .alert_irq(alert_irq),
    .temp_code(temp_code_unused_from_u_temp_monitor_digital_sample_ctrl_temp_code),
    .alert_status(alert_status),
    .status_sample_done(status_sample_done),
    .status_alert_pending(status_alert_pending),
    .status_adc_valid_seen(status_adc_valid_seen),
    .status_busy(status_busy),
    .irq_status_alert(irq_status_alert),
    .irq_status_sample_done(irq_status_sample_done),
    .latest_temp(latest_temp),
    .sample_count(sample_count),
    .compare_alert(compare_alert),
    .sample_done_pulse(sample_done_pulse),
    .sample_req_pulse(sample_req_pulse)
);

endmodule
