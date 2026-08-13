module smart_sensor_hub_mcu (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    sensor_temp_raw,
    sensor_humidity_raw,
    sensor_air_raw,
    sensor_valid,
    rd_data,
    sensor_sample_req,
    alert_irq,
    fifo_level,
    low_power_active,
    sample_count,
    alert_status
);
input clk;
input reset_n;
input wr_en;
input [11:0] wr_addr;
input [31:0] wr_data;
input rd_en;
input [11:0] rd_addr;
input [15:0] sensor_temp_raw;
input [15:0] sensor_humidity_raw;
input [15:0] sensor_air_raw;
input sensor_valid;
output [31:0] rd_data;
output sensor_sample_req;
output alert_irq;
output [5:0] fifo_level;
output low_power_active;
output [31:0] sample_count;
output [7:0] alert_status;
assign rd_data = 32'd0;
assign sensor_sample_req = 1'b0;
assign alert_irq = 1'b0;
assign fifo_level = 6'd0;
assign low_power_active = 1'b0;
assign sample_count = 32'd0;
assign alert_status = 8'd0;

endmodule
