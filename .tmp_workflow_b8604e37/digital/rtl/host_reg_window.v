module host_reg_window (
    input clk,
    input rst_n,
    input reg_valid,
    input reg_we,
    input reg_re,
    input [7:0] reg_addr,
    input [31:0] reg_wdata,
    input [3:0] reg_byte_en,
    output reg reg_ready,
    output reg [31:0] reg_rdata,
    output reg cfg_enable,
    output reg [1:0] cfg_mode_sel,
    output reg [15:0] cfg_env_limit,
    output reg [15:0] cfg_stale_timeout,
    output reg [15:0] cfg_seq_base,
    output reg [15:0] cfg_heartbeat_timeout,
    output reg [15:0] cfg_act_min,
    output reg [15:0] cfg_act_max,
    output reg [7:0] cfg_rate_limit,
    output reg [15:0] cfg_safe_output,
    output reg cfg_fault_clear,
    output reg cfg_reserved_error_en,
    input [1:0] status_mode,
    input status_fault_latched,
    input status_timeout,
    input status_stale,
    input status_heartbeat_seen,
    input [15:0] status_last_cmd,
    input [15:0] status_last_seq,
    input [15:0] telemetry_accepted_packets,
    input [15:0] telemetry_rejected_packets,
    input [15:0] telemetry_timeout_events,
    input [15:0] telemetry_stale_events,
    input [15:0] telemetry_fallback_entries,
    input [15:0] telemetry_last_valid_seq,
    output reg fault_latched_clear
);

reg reserved_error_flag;
reg [31:0] read_data;

always @(*) begin
    read_data = 32'h00000000;
    case (reg_addr)
        8'h00: read_data = {21'b0, cfg_reserved_error_en, 6'b0, cfg_mode_sel, 1'b0, cfg_enable};
        8'h04: read_data = {16'b0, cfg_env_limit};
        8'h08: read_data = {16'b0, cfg_stale_timeout};
        8'h0C: read_data = {16'b0, cfg_seq_base};
        8'h10: read_data = {16'b0, cfg_heartbeat_timeout};
        8'h14: read_data = {16'b0, cfg_act_min};
        8'h18: read_data = {16'b0, cfg_act_max};
        8'h1C: read_data = {24'b0, cfg_rate_limit};
        8'h20: read_data = {16'b0, cfg_safe_output};
        8'h24: read_data = {31'b0, cfg_fault_clear};
        8'h28: read_data = {26'b0, status_heartbeat_seen, status_stale, status_timeout, status_fault_latched, status_mode};
        8'h2C: read_data = {16'b0, status_last_cmd};
        8'h30: read_data = {16'b0, status_last_seq};
        8'h34: read_data = {16'b0, telemetry_accepted_packets};
        8'h38: read_data = {16'b0, telemetry_rejected_packets};
        8'h3C: read_data = {16'b0, telemetry_timeout_events};
        8'h40: read_data = {16'b0, telemetry_stale_events};
        8'h44: read_data = {16'b0, telemetry_fallback_entries};
        8'h48: read_data = {16'b0, telemetry_last_valid_seq};
        default: read_data = {31'b0, reserved_error_flag};
    endcase
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_enable <= 1'b0;
        cfg_mode_sel <= 2'b00;
        cfg_env_limit <= 16'h0000;
        cfg_stale_timeout <= 16'h0020;
        cfg_seq_base <= 16'h0000;
        cfg_heartbeat_timeout <= 16'h0100;
        cfg_act_min <= 16'h0000;
        cfg_act_max <= 16'hFFFF;
        cfg_rate_limit <= 8'h10;
        cfg_safe_output <= 16'h0000;
        cfg_fault_clear <= 1'b0;
        cfg_reserved_error_en <= 1'b0;
        fault_latched_clear <= 1'b0;
        reserved_error_flag <= 1'b0;
        reg_ready <= 1'b0;
        reg_rdata <= 32'h00000000;
    end else begin
        reg_ready <= reg_valid;
        reg_rdata <= reg_re ? read_data : reg_rdata;
        cfg_fault_clear <= 1'b0;
        fault_latched_clear <= 1'b0;
        if (reg_valid && reg_we) begin
            case (reg_addr)
                8'h00: begin
                    if (reg_byte_en[0]) begin
                        cfg_enable <= reg_wdata[0];
                        cfg_mode_sel <= reg_wdata[2:1];
                    end
                    if (reg_byte_en[1]) begin
                        cfg_reserved_error_en <= reg_wdata[8];
                    end
                end
                8'h04: begin
                    if (reg_byte_en[0]) cfg_env_limit[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_env_limit[15:8] <= reg_wdata[15:8];
                end
                8'h08: begin
                    if (reg_byte_en[0]) cfg_stale_timeout[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_stale_timeout[15:8] <= reg_wdata[15:8];
                end
                8'h0C: begin
                    if (reg_byte_en[0]) cfg_seq_base[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_seq_base[15:8] <= reg_wdata[15:8];
                end
                8'h10: begin
                    if (reg_byte_en[0]) cfg_heartbeat_timeout[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_heartbeat_timeout[15:8] <= reg_wdata[15:8];
                end
                8'h14: begin
                    if (reg_byte_en[0]) cfg_act_min[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_act_min[15:8] <= reg_wdata[15:8];
                end
                8'h18: begin
                    if (reg_byte_en[0]) cfg_act_max[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_act_max[15:8] <= reg_wdata[15:8];
                end
                8'h1C: begin
                    if (reg_byte_en[0]) cfg_rate_limit <= reg_wdata[7:0];
                end
                8'h20: begin
                    if (reg_byte_en[0]) cfg_safe_output[7:0] <= reg_wdata[7:0];
                    if (reg_byte_en[1]) cfg_safe_output[15:8] <= reg_wdata[15:8];
                end
                8'h24: begin
                    if (reg_byte_en[0] && reg_wdata[0]) cfg_fault_clear <= 1'b1;
                    if (reg_byte_en[0] && reg_wdata[0]) fault_latched_clear <= 1'b1;
                end
                default: begin
                    if (cfg_reserved_error_en) reserved_error_flag <= 1'b1;
                end
            endcase
            if (reg_addr >= 8'h4C) begin
                if (cfg_reserved_error_en) reserved_error_flag <= 1'b1;
                if (reg_byte_en[0] && reg_wdata[0]) reserved_error_flag <= 1'b0;
            end
        end
    end
end

endmodule
