module aero_mmio_csr_block (
    input         clk,
    input         reset_n,
    input         mmio_valid,
    input         mmio_write,
    input  [15:0] mmio_addr,
    input  [31:0] mmio_wdata,
    output reg [31:0] mmio_rdata,
    output reg        mmio_ready,
    output reg        cfg_enable,
    output reg [15:0] cfg_min_speed_mps,
    output reg [15:0] cfg_max_speed_mps,
    output reg [15:0] cfg_cmd_min,
    output reg [15:0] cfg_cmd_max,
    output reg [15:0] cfg_timeout_cycles,
    output reg [15:0] cfg_stale_limit_cycles,
    output reg [1:0]  cfg_model_select,
    output reg        cfg_fault_clear,
    input         status_fault_latched,
    input         status_safety_inhibit,
    input         status_last_cmd_valid,
    input  [15:0] status_last_cmd_data,
    input  [15:0] status_last_speed_mps,
    input         status_timeout_active
);

localparam [15:0] ADDR_CTRL       = 16'h0000;
localparam [15:0] ADDR_SPEED      = 16'h0004;
localparam [15:0] ADDR_CMD        = 16'h0008;
localparam [15:0] ADDR_TIMING     = 16'h000C;
localparam [15:0] ADDR_STATUS     = 16'h0010;
localparam [15:0] ADDR_LAST_SPEED = 16'h0014;

reg [31:0] read_data_next;
reg ready_next;
reg cfg_fault_clear_next;

always @(*) begin
    read_data_next = 32'h00000000;
    ready_next = 1'b1;
    cfg_fault_clear_next = 1'b0;

    case (mmio_addr)
        ADDR_CTRL: begin
            read_data_next = {27'b0, 1'b0, cfg_model_select, cfg_fault_clear, cfg_enable};
            if (mmio_valid && mmio_write) begin
                cfg_fault_clear_next = mmio_wdata[3];
            end
        end
        ADDR_SPEED: begin
            read_data_next = {cfg_max_speed_mps, cfg_min_speed_mps};
        end
        ADDR_CMD: begin
            read_data_next = {cfg_cmd_max, cfg_cmd_min};
        end
        ADDR_TIMING: begin
            read_data_next = {cfg_stale_limit_cycles, cfg_timeout_cycles};
        end
        ADDR_STATUS: begin
            read_data_next = {status_last_cmd_data, 12'b000000000000, status_timeout_active, status_last_cmd_valid, status_safety_inhibit, status_fault_latched};
        end
        ADDR_LAST_SPEED: begin
            read_data_next = {16'h0000, status_last_speed_mps};
        end
        default: begin
            read_data_next = 32'h00000000;
        end
    endcase
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cfg_enable <= 1'b0;
        cfg_min_speed_mps <= 16'd20;
        cfg_max_speed_mps <= 16'd55;
        cfg_cmd_min <= 16'd0;
        cfg_cmd_max <= 16'd1023;
        cfg_timeout_cycles <= 16'd64;
        cfg_stale_limit_cycles <= 16'd16;
        cfg_model_select <= 2'b00;
        cfg_fault_clear <= 1'b0;
        mmio_rdata <= 32'h00000000;
        mmio_ready <= 1'b1;
    end else begin
        mmio_rdata <= read_data_next;
        mmio_ready <= ready_next;
        cfg_fault_clear <= cfg_fault_clear_next;
        if (mmio_valid && mmio_write) begin
            case (mmio_addr)
                ADDR_CTRL: begin
                    cfg_enable <= mmio_wdata[0];
                    cfg_model_select <= mmio_wdata[2:1];
                end
                ADDR_SPEED: begin
                    cfg_min_speed_mps <= mmio_wdata[15:0];
                    cfg_max_speed_mps <= mmio_wdata[31:16];
                end
                ADDR_CMD: begin
                    cfg_cmd_min <= mmio_wdata[15:0];
                    cfg_cmd_max <= mmio_wdata[31:16];
                end
                ADDR_TIMING: begin
                    cfg_timeout_cycles <= mmio_wdata[15:0];
                    cfg_stale_limit_cycles <= mmio_wdata[31:16];
                end
                default: begin
                end
            endcase
        end
    end
end

endmodule