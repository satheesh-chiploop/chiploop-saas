module adaptive_aero_mmio_csr (
    input         clk,
    input         reset_n,
    input  [15:0] mmio_addr,
    input  [31:0] mmio_wdata,
    input         mmio_valid,
    input         mmio_we,
    output reg [31:0] mmio_rdata,
    output reg        mmio_ready,
    output reg        mmio_error,
    output reg        cfg_enable,
    output reg        cfg_surrogate_select,
    output reg [15:0] cfg_timeout_cycles,
    output reg [15:0] cfg_stale_limit_cycles,
    output reg [7:0] cfg_tilt_limit,
    output reg [7:0] cfg_deflection_limit,
    output reg [1:0] cfg_mode_select,
    output reg        cfg_clear_fault,
    output reg [8:0] cfg_history_base,
    output reg [7:0] cfg_payload_base,
    input             status_fault_latched,
    input             status_model_busy,
    input             status_model_valid,
    input             status_timeout_active,
    input             status_stale_active,
    input      [7:0] status_last_response_code,
    input             status_valid
);

always @(*) begin
    mmio_error = 1'b0;
    case (mmio_addr)
        16'h0000: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0004: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0008: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h000C: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0010: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0014: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0018: begin
            if (mmio_valid && mmio_we) begin
            end
        end
        16'h0020: begin
        end
        16'h0024: begin
        end
        16'h0028: begin
        end
        default: begin
            mmio_error = 1'b1;
        end
    endcase
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cfg_enable <= 1'b0;
        cfg_surrogate_select <= 1'b0;
        cfg_timeout_cycles <= 16'd1000;
        cfg_stale_limit_cycles <= 16'd300;
        cfg_tilt_limit <= 8'd32;
        cfg_deflection_limit <= 8'd32;
        cfg_mode_select <= 2'b00;
        mmio_ready <= 1'b1;
        cfg_clear_fault <= 1'b0;
    end else begin
        mmio_ready <= 1'b1;
        cfg_clear_fault <= 1'b0;
        if (mmio_valid && mmio_we) begin
            case (mmio_addr)
                16'h0000: begin
                    cfg_enable <= mmio_wdata[0];
                    cfg_surrogate_select <= mmio_wdata[1];
                    cfg_mode_select <= mmio_wdata[3:2];
                end
                16'h0004: cfg_timeout_cycles <= mmio_wdata[15:0];
                16'h0008: cfg_stale_limit_cycles <= mmio_wdata[15:0];
                16'h000C: cfg_tilt_limit <= mmio_wdata[7:0];
                16'h0010: cfg_deflection_limit <= mmio_wdata[7:0];
                16'h0014: cfg_history_base <= mmio_wdata[8:0];
                16'h0018: cfg_payload_base <= mmio_wdata[7:0];
                default: begin
                end
            endcase
        end
        if (mmio_valid && !mmio_we) begin
            case (mmio_addr)
                16'h0000: mmio_rdata <= {27'h0000000, 1'b0, cfg_mode_select, cfg_surrogate_select, cfg_enable};
                16'h0004: mmio_rdata <= {16'h0000, cfg_timeout_cycles};
                16'h0008: mmio_rdata <= {16'h0000, cfg_stale_limit_cycles};
                16'h000C: mmio_rdata <= {24'h000000, cfg_tilt_limit};
                16'h0010: mmio_rdata <= {24'h000000, cfg_deflection_limit};
                16'h0014: mmio_rdata <= {23'h000000, cfg_history_base};
                16'h0018: mmio_rdata <= {24'h000000, cfg_payload_base};
                16'h0020: mmio_rdata <= {16'h0000, status_last_response_code, 2'b00, status_stale_active, status_timeout_active, status_model_valid, status_model_busy, status_fault_latched, status_valid};
                16'h0024: mmio_rdata <= {20'b0, cfg_timeout_cycles[7:0], cfg_enable, cfg_surrogate_select, cfg_mode_select};
                16'h0028: mmio_rdata <= {24'h000000, cfg_payload_base};
                default: mmio_rdata <= 32'h00000000;
            endcase
        end
        if (mmio_valid && mmio_we && mmio_addr == 16'h0000 && mmio_wdata[4]) begin
            cfg_clear_fault <= 1'b1;
        end
    end
end

endmodule
