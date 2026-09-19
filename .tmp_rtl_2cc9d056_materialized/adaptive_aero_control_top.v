module adaptive_aero_control_top (
    input         clk,
    input         reset_n,
    input         mmio_valid,
    input         mmio_write,
    input  [15:0] mmio_addr,
    input  [31:0] mmio_wdata,
    output [31:0] mmio_rdata,
    output        mmio_ready,
    output        model_req_valid,
    output [63:0] model_req_data,
    input         model_req_ready,
    input         model_rsp_valid,
    input  [63:0] model_rsp_data,
    output        model_rsp_ready,
    input  [15:0] vehicle_speed_mps,
    input         sensor_valid,
    input         sensor_fault,
    input         sensor_stale,
    output        actuator_cmd_valid,
    output [15:0] actuator_cmd_data,
    output        fault_latched,
    output        safety_inhibit,
    output        history_csb,
    output        history_we,
    output [9:0]  history_addr,
    output [63:0] history_din,
    input  [63:0] history_dout
);

wire cfg_enable;
wire [15:0] cfg_min_speed_mps;
wire [15:0] cfg_max_speed_mps;
wire [15:0] cfg_cmd_min;
wire [15:0] cfg_cmd_max;
wire [15:0] cfg_timeout_cycles;
wire [15:0] cfg_stale_limit_cycles;
wire [1:0]  cfg_model_select;
wire cfg_fault_clear;

wire status_fault_latched;
wire status_safety_inhibit;
wire status_last_cmd_valid;
wire [15:0] status_last_cmd_data;
wire [15:0] status_last_speed_mps;
wire status_timeout_active;

wire history_wr_en;
wire [9:0] history_wr_addr;
wire [63:0] history_wr_data;
wire [63:0] history_rd_data;

wire [31:0] mmio_rdata_i;
wire mmio_ready_i;
wire model_req_valid_i;
wire [63:0] model_req_data_i;
wire model_rsp_ready_i;
wire actuator_cmd_valid_i;
wire [15:0] actuator_cmd_data_i;
wire fault_latched_i;
wire safety_inhibit_i;

wire history_csb_i;
wire history_we_i;
wire [9:0] history_addr_i;
wire [63:0] history_din_i;

assign mmio_rdata = mmio_rdata_i;
assign mmio_ready = mmio_ready_i;
assign model_req_valid = model_req_valid_i;
assign model_req_data = model_req_data_i;
assign model_rsp_ready = model_rsp_ready_i;
assign actuator_cmd_valid = actuator_cmd_valid_i;
assign actuator_cmd_data = actuator_cmd_data_i;
assign fault_latched = fault_latched_i;
assign safety_inhibit = safety_inhibit_i;

assign history_csb = history_csb_i;
assign history_we = history_we_i;
assign history_addr = history_addr_i;
assign history_din = history_din_i;

assign history_rd_data = history_dout;

aero_mmio_csr_block u_aero_mmio_csr_block (
    .clk(clk),
    .reset_n(reset_n),
    .mmio_valid(mmio_valid),
    .mmio_write(mmio_write),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_rdata(mmio_rdata_i),
    .mmio_ready(mmio_ready_i),
    .cfg_enable(cfg_enable),
    .cfg_min_speed_mps(cfg_min_speed_mps),
    .cfg_max_speed_mps(cfg_max_speed_mps),
    .cfg_cmd_min(cfg_cmd_min),
    .cfg_cmd_max(cfg_cmd_max),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_stale_limit_cycles(cfg_stale_limit_cycles),
    .cfg_model_select(cfg_model_select),
    .cfg_fault_clear(cfg_fault_clear),
    .status_fault_latched(status_fault_latched),
    .status_safety_inhibit(status_safety_inhibit),
    .status_last_cmd_valid(status_last_cmd_valid),
    .status_last_cmd_data(status_last_cmd_data),
    .status_last_speed_mps(status_last_speed_mps),
    .status_timeout_active(status_timeout_active)
);

adaptive_aero_controller_core u_adaptive_aero_controller_core (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_min_speed_mps(cfg_min_speed_mps),
    .cfg_max_speed_mps(cfg_max_speed_mps),
    .cfg_cmd_min(cfg_cmd_min),
    .cfg_cmd_max(cfg_cmd_max),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_stale_limit_cycles(cfg_stale_limit_cycles),
    .cfg_model_select(cfg_model_select),
    .cfg_fault_clear(cfg_fault_clear),
    .vehicle_speed_mps(vehicle_speed_mps),
    .sensor_valid(sensor_valid),
    .sensor_fault(sensor_fault),
    .sensor_stale(sensor_stale),
    .model_req_valid(model_req_valid_i),
    .model_req_data(model_req_data_i),
    .model_req_ready(model_req_ready),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(model_rsp_ready_i),
    .actuator_cmd_valid(actuator_cmd_valid_i),
    .actuator_cmd_data(actuator_cmd_data_i),
    .fault_latched(fault_latched_i),
    .safety_inhibit(safety_inhibit_i),
    .status_last_cmd_valid(status_last_cmd_valid),
    .status_last_cmd_data(status_last_cmd_data),
    .status_last_speed_mps(status_last_speed_mps),
    .status_timeout_active(status_timeout_active),
    .history_wr_en(history_wr_en),
    .history_wr_addr(history_wr_addr),
    .history_wr_data(history_wr_data),
    .history_rd_data(history_rd_data)
);

assign history_csb_i = history_wr_en;
assign history_we_i = history_wr_en;
assign history_addr_i = history_wr_addr;
assign history_din_i = history_wr_data;

adaptive_aero_history_wrapper u_adaptive_aero_history_wrapper (
    .clk(clk),
    .reset_n(reset_n),
    .history_csb(history_csb_i),
    .history_we(history_we_i),
    .history_addr(history_addr_i),
    .history_din(history_din_i),
    .history_dout(history_dout)
);

endmodule