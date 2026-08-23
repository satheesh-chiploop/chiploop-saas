module request_validator (
    input clk,
    input rst_n,
    input rx_pkt_valid,
    input [15:0] rx_pkt_seq,
    input [15:0] rx_pkt_timestamp,
    input [3:0] rx_pkt_cmd_type,
    input [7:0] rx_pkt_vel_bin,
    input [15:0] rx_pkt_geom_ref,
    input [7:0] rx_pkt_integrity,
    input [15:0] rx_pkt_age,
    input rsp_valid,
    input [127:0] rsp_data,
    output reg rsp_ready,
    input cfg_enable,
    input [1:0] cfg_mode_sel,
    input [15:0] cfg_env_limit,
    input [15:0] cfg_stale_timeout,
    input [15:0] cfg_seq_base,
    input [15:0] cfg_heartbeat_timeout,
    output reg req_accept,
    output reg req_reject,
    output reg req_fault,
    output reg req_stale,
    output reg req_timeout,
    output reg req_seq_ok,
    output reg req_integrity_ok,
    output reg req_env_ok,
    output reg rsp_accept,
    output reg rsp_reject,
    output reg rsp_seq_ok,
    output reg rsp_fresh_ok,
    output reg rsp_cmd_valid,
    output reg [15:0] rsp_act_cmd,
    output reg heartbeat_seen,
    output reg [15:0] last_valid_seq
);

reg [15:0] heartbeat_age;
reg outstanding_valid;
reg [15:0] outstanding_seq;
reg [15:0] outstanding_timestamp;

wire integrity_ok;
wire seq_ok;
wire env_ok;
wire stale_now;
wire timeout_now;
wire fresh_rsp_ok;
wire rsp_seq_match;
wire rsp_integrity_hint;
wire [15:0] rsp_cmd_from_data;

assign integrity_ok = (rx_pkt_integrity == (rx_pkt_seq[7:0] ^ rx_pkt_timestamp[7:0]));
assign seq_ok = (rx_pkt_seq >= cfg_seq_base) && ((last_valid_seq == 16'h0000) ? 1'b1 : (rx_pkt_seq > last_valid_seq));
assign env_ok = (rx_pkt_vel_bin <= cfg_env_limit[7:0]) && (rx_pkt_cmd_type != 4'hF) && (cfg_mode_sel != 2'b11);
assign stale_now = (rx_pkt_age >= cfg_stale_timeout) && (cfg_stale_timeout != 16'h0000);
assign timeout_now = (heartbeat_age >= cfg_heartbeat_timeout) && (cfg_heartbeat_timeout != 16'h0000);
assign rsp_seq_match = outstanding_valid && (rsp_data[15:0] == outstanding_seq);
assign fresh_rsp_ok = rsp_valid && rsp_seq_match && !timeout_now && !stale_now;
assign rsp_integrity_hint = (rsp_data[67:60] == (rsp_data[15:8] ^ rsp_data[31:24]));
assign rsp_cmd_from_data = rsp_data[31:16];

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rsp_ready <= 1'b1;
        req_accept <= 1'b0;
        req_reject <= 1'b0;
        req_fault <= 1'b0;
        req_stale <= 1'b0;
        req_timeout <= 1'b0;
        req_seq_ok <= 1'b0;
        req_integrity_ok <= 1'b0;
        req_env_ok <= 1'b0;
        rsp_accept <= 1'b0;
        rsp_reject <= 1'b0;
        rsp_seq_ok <= 1'b0;
        rsp_fresh_ok <= 1'b0;
        rsp_cmd_valid <= 1'b0;
        rsp_act_cmd <= 16'h0000;
        heartbeat_seen <= 1'b0;
        last_valid_seq <= 16'h0000;
        heartbeat_age <= 16'h0000;
        outstanding_valid <= 1'b0;
        outstanding_seq <= 16'h0000;
        outstanding_timestamp <= 16'h0000;
    end else begin
        req_accept <= 1'b0;
        req_reject <= 1'b0;
        req_fault <= 1'b0;
        req_stale <= 1'b0;
        req_timeout <= 1'b0;
        rsp_accept <= 1'b0;
        rsp_reject <= 1'b0;
        rsp_fresh_ok <= 1'b0;
        rsp_cmd_valid <= 1'b0;
        req_seq_ok <= 1'b0;
        req_integrity_ok <= 1'b0;
        req_env_ok <= 1'b0;
        rsp_seq_ok <= 1'b0;
        heartbeat_seen <= 1'b0;
        rsp_ready <= 1'b1;
        if (cfg_enable) begin
            heartbeat_age <= heartbeat_age + 16'h0001;
            if (rx_pkt_valid) begin
                req_seq_ok <= seq_ok;
                req_integrity_ok <= integrity_ok;
                req_env_ok <= env_ok;
                if (integrity_ok && seq_ok && env_ok && !stale_now && !timeout_now) begin
                    req_accept <= 1'b1;
                    last_valid_seq <= rx_pkt_seq;
                    outstanding_valid <= 1'b1;
                    outstanding_seq <= rx_pkt_seq;
                    outstanding_timestamp <= rx_pkt_timestamp;
                    heartbeat_age <= 16'h0000;
                    heartbeat_seen <= 1'b1;
                end else begin
                    req_reject <= 1'b1;
                    if (!integrity_ok || !seq_ok || !env_ok) req_fault <= 1'b1;
                    if (stale_now) req_stale <= 1'b1;
                    if (timeout_now) req_timeout <= 1'b1;
                end
            end
            if (rsp_valid) begin
                rsp_seq_ok <= rsp_seq_match;
                rsp_fresh_ok <= fresh_rsp_ok;
                if (fresh_rsp_ok && rsp_integrity_hint) begin
                    rsp_accept <= 1'b1;
                    rsp_cmd_valid <= 1'b1;
                    rsp_act_cmd <= rsp_cmd_from_data;
                    heartbeat_seen <= 1'b1;
                    heartbeat_age <= 16'h0000;
                    outstanding_valid <= 1'b0;
                end else begin
                    rsp_reject <= 1'b1;
                end
            end
        end else begin
            outstanding_valid <= 1'b0;
            heartbeat_age <= 16'h0000;
            if (rx_pkt_valid) begin
                req_reject <= 1'b1;
            end
            if (rsp_valid) begin
                rsp_reject <= 1'b1;
            end
        end
        if (timeout_now) req_timeout <= 1'b1;
        if (stale_now) req_stale <= 1'b1;
    end
end

endmodule
