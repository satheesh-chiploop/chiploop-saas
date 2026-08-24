module adaptive_aero_mmio_csr (
    input clk,
    input reset_n,
    input [7:0] mmio_addr,
    input [31:0] mmio_wdata,
    input mmio_valid,
    input mmio_write,
    output reg [31:0] mmio_rdata,
    output reg mmio_ready,
    output reg cfg_enable,
    output reg [1:0] cfg_mode,
    output reg [15:0] cfg_timeout_cycles,
    output reg [15:0] cfg_command_min,
    output reg [15:0] cfg_command_max,
    output reg [15:0] cfg_speed_min,
    output reg [15:0] cfg_speed_max,
    output reg [7:0] cfg_model_req_tag,
    output reg [15:0] cfg_model_timeout_cycles,
    output reg cfg_history_capture_en,
    output reg cfg_fault_clear,
    input status_fault_latched,
    input status_timeout,
    input status_stale,
    input status_response_valid,
    input status_actuator_valid,
    input status_speed_valid,
    input [15:0] status_speed_raw,
    input [15:0] status_command_raw
);

reg [31:0] ctrl_reg;
reg [31:0] timeouts_reg;
reg [31:0] limits_reg;
reg [31:0] speed_window_reg;
reg [31:0] model_meta_reg;
reg [31:0] history_reg;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        ctrl_reg <= 32'd0;
        timeouts_reg <= 32'd1000 | (32'd1000 << 16);
        limits_reg <= 32'd4095 << 16;
        speed_window_reg <= 32'd20 | (32'd55 << 16);
        model_meta_reg <= 32'd0;
        history_reg <= 32'd0;
        cfg_fault_clear <= 1'b0;
    end else begin
        cfg_fault_clear <= 1'b0;
        if (mmio_valid && mmio_write) begin
            case (mmio_addr)
                8'h00: ctrl_reg <= mmio_wdata;
                8'h01: timeouts_reg <= mmio_wdata;
                8'h02: limits_reg <= mmio_wdata;
                8'h03: speed_window_reg <= mmio_wdata;
                8'h04: model_meta_reg <= mmio_wdata;
                8'h07: history_reg <= mmio_wdata;
                default: begin end
            endcase
        end
        if (mmio_valid && mmio_write && mmio_addr == 8'h00 && mmio_wdata[4]) cfg_fault_clear <= 1'b1;
    end
end

always @(*) begin
    mmio_rdata = 32'd0;
    mmio_ready = mmio_valid;
    cfg_enable = ctrl_reg[0];
    cfg_mode = ctrl_reg[2:1];
    cfg_history_capture_en = ctrl_reg[3];
    cfg_timeout_cycles = timeouts_reg[15:0];
    cfg_model_timeout_cycles = timeouts_reg[31:16];
    cfg_command_min = limits_reg[15:0];
    cfg_command_max = limits_reg[31:16];
    cfg_speed_min = speed_window_reg[15:0];
    cfg_speed_max = speed_window_reg[31:16];
    cfg_model_req_tag = model_meta_reg[7:0];
    case (mmio_addr)
        8'h00: mmio_rdata = ctrl_reg;
        8'h01: mmio_rdata = timeouts_reg;
        8'h02: mmio_rdata = limits_reg;
        8'h03: mmio_rdata = speed_window_reg;
        8'h04: mmio_rdata = model_meta_reg;
        8'h05: mmio_rdata = {26'd0, status_speed_valid, status_actuator_valid, status_response_valid, status_stale, status_timeout, status_fault_latched};
        8'h06: mmio_rdata = {status_command_raw, status_speed_raw};
        8'h07: mmio_rdata = history_reg;
        default: mmio_rdata = 32'd0;
    endcase
end

endmodule
