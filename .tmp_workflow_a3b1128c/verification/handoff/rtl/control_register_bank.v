module control_register_bank (
    input         clk,
    input         reset_n,
    input         cfg_valid,
    input         cfg_write,
    input  [3:0] cfg_addr,
    input  [31:0] cfg_wdata,
    output [31:0] cfg_rdata,
    output        cfg_ready,
    output reg    enable,
    output reg [15:0] timeout_limit_cycles,
    output reg [7:0] sequence_window,
    output reg [15:0] actuator_min,
    output reg [15:0] actuator_max,
    output reg [15:0] fallback_command,
    output reg        slew_limit_enable,
    output reg [7:0] slew_limit,
    output reg        clear_sticky_status,
    input  [31:0] status_image
);

reg [31:0] cfg_rdata_r;
reg        cfg_ready_r;

assign cfg_rdata = cfg_rdata_r;
assign cfg_ready = cfg_ready_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        enable <= 1'b0;
        timeout_limit_cycles <= 16'd64;
        sequence_window <= 8'd8;
        actuator_min <= 16'd0;
        actuator_max <= 16'd255;
        fallback_command <= 16'd0;
        slew_limit_enable <= 1'b0;
        slew_limit <= 8'd0;
        clear_sticky_status <= 1'b0;
        cfg_ready_r <= 1'b0;
        cfg_rdata_r <= 32'd0;
    end else begin
        cfg_ready_r <= cfg_valid;
        clear_sticky_status <= 1'b0;
        if (cfg_valid && cfg_write) begin
            case (cfg_addr)
                4'h0: begin
                    enable <= cfg_wdata[0];
                    clear_sticky_status <= cfg_wdata[1];
                    slew_limit_enable <= cfg_wdata[3];
                end
                4'h1: begin
                    timeout_limit_cycles <= {8'd0, cfg_wdata[7:0]};
                    sequence_window <= cfg_wdata[15:8];
                end
                4'h2: begin
                    actuator_min <= {8'd0, cfg_wdata[7:0]};
                end
                4'h3: begin
                    actuator_max <= {8'd0, cfg_wdata[7:0]};
                end
                4'h4: begin
                    fallback_command <= {8'd0, cfg_wdata[7:0]};
                end
                4'h5: begin
                    slew_limit <= cfg_wdata[7:0];
                end
                default: begin
                end
            endcase
        end
        case (cfg_addr)
            4'h0: cfg_rdata_r <= {24'd0, status_image[7:0]};
            4'h1: cfg_rdata_r <= {16'd0, timeout_limit_cycles[7:0], sequence_window};
            4'h2: cfg_rdata_r <= {24'd0, actuator_min[7:0]};
            4'h3: cfg_rdata_r <= {24'd0, actuator_max[7:0]};
            4'h4: cfg_rdata_r <= {24'd0, fallback_command[7:0]};
            4'h5: cfg_rdata_r <= {24'd0, slew_limit};
            4'h6: cfg_rdata_r <= status_image;
            4'h7: cfg_rdata_r <= {24'd0, status_image[7:0]};
            default: cfg_rdata_r <= 32'd0;
        endcase
    end
end

endmodule
