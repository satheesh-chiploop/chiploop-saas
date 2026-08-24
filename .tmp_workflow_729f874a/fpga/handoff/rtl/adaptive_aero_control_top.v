module adaptive_aero_control_top (
    input clk,
    input reset_n,
    input [7:0] mmio_addr,
    input [31:0] mmio_wdata,
    input mmio_valid,
    input mmio_write,
    output [31:0] mmio_rdata,
    output mmio_ready,
    output model_req_valid,
    output [63:0] model_req_data,
    input model_req_ready,
    input model_rsp_valid,
    input [63:0] model_rsp_data,
    output model_rsp_ready,
    output actuator_cmd_valid,
    output [15:0] actuator_cmd_data,
    input actuator_cmd_ready,
    output fault_latched,
    output status_valid,
    output [31:0] status_data
);
wire cfg_enable;
wire [1:0] cfg_mode;
wire [15:0] cfg_timeout_cycles;
wire [15:0] cfg_command_min;
wire [15:0] cfg_command_max;
wire [15:0] cfg_speed_min;
wire [15:0] cfg_speed_max;
wire [7:0] cfg_model_req_tag;
wire [15:0] cfg_model_timeout_cycles;
wire cfg_history_capture_en;
wire cfg_fault_clear;
wire status_fault_latched;
wire status_timeout;
wire status_stale;
wire status_response_valid;
wire status_actuator_valid;
wire status_speed_valid;
wire [15:0] status_speed_raw;
wire [15:0] status_command_raw;
wire history_wr_en;
wire [63:0] history_wr_data;
wire [7:0] history_wr_addr;
wire [7:0] history_rd_addr;
wire history_rd_en;
wire [63:0] history_rd_data;

wire adaptive_aero_controller_core_status_response_valid;
wire [15:0] adaptive_aero_controller_core_status_speed_raw;
wire adaptive_aero_controller_core_status_speed_valid;
wire adaptive_aero_controller_core_status_stale;
wire adaptive_aero_controller_core_status_timeout;
adaptive_aero_mmio_csr u_mmio_csr (
    .clk(clk),
    .reset_n(reset_n),
    .mmio_addr(mmio_addr),
    .mmio_wdata(mmio_wdata),
    .mmio_valid(mmio_valid),
    .mmio_write(mmio_write),
    .mmio_rdata(mmio_rdata),
    .mmio_ready(mmio_ready),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_command_min(cfg_command_min),
    .cfg_command_max(cfg_command_max),
    .cfg_speed_min(cfg_speed_min),
    .cfg_speed_max(cfg_speed_max),
    .cfg_model_req_tag(cfg_model_req_tag),
    .cfg_model_timeout_cycles(cfg_model_timeout_cycles),
    .cfg_history_capture_en(cfg_history_capture_en),
    .cfg_fault_clear(cfg_fault_clear),
    .status_fault_latched(status_fault_latched),
    .status_timeout(status_timeout),
    .status_stale(status_stale),
    .status_response_valid(status_response_valid),
    .status_actuator_valid(status_actuator_valid),
    .status_speed_valid(status_speed_valid),
    .status_speed_raw(status_speed_raw),
    .status_command_raw(status_command_raw)
);

adaptive_aero_controller_core u_controller_core (
    .clk(clk),
    .reset_n(reset_n),
    .cfg_enable(cfg_enable),
    .cfg_mode(cfg_mode),
    .cfg_timeout_cycles(cfg_timeout_cycles),
    .cfg_command_min(cfg_command_min),
    .cfg_command_max(cfg_command_max),
    .cfg_speed_min(cfg_speed_min),
    .cfg_speed_max(cfg_speed_max),
    .cfg_model_req_tag(cfg_model_req_tag),
    .cfg_model_timeout_cycles(cfg_model_timeout_cycles),
    .cfg_history_capture_en(cfg_history_capture_en),
    .cfg_fault_clear(cfg_fault_clear),
    .model_rsp_valid(model_rsp_valid),
    .model_rsp_data(model_rsp_data),
    .model_rsp_ready(model_rsp_ready),
    .command_valid(actuator_cmd_valid),
    .command_data(actuator_cmd_data),
    .fault_latched(fault_latched),
    .status_timeout(status_timeout),
    .status_stale(status_stale),
    .status_response_valid(status_response_valid),
    .status_actuator_valid(status_actuator_valid),
    .status_speed_valid(status_speed_valid),
    .status_speed_raw(status_speed_raw),
    .status_command_raw(status_command_raw),
    .history_wr_en(history_wr_en),
    .history_wr_data(history_wr_data),
    .history_wr_addr(history_wr_addr)
);

adaptive_aero_history_store u_history_store (
    .clk(clk),
    .reset_n(reset_n),
    .wr_en(history_wr_en),
    .wr_addr(history_wr_addr),
    .wr_data(history_wr_data),
    .rd_addr(history_rd_addr),
    .rd_data(history_rd_data),
    .rd_en(history_rd_en)
);

assign model_req_valid = actuator_cmd_valid;
assign model_req_data = {48'd0, actuator_cmd_data};
assign status_valid = mmio_ready;
assign status_data = mmio_rdata;
assign history_rd_addr = cfg_model_req_tag;
assign history_rd_en = cfg_history_capture_en;

assign status_fault_latched = fault_latched;

endmodule
