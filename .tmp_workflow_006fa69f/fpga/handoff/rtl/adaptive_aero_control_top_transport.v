module adaptive_aero_control_top_transport (
    clk,
    reset,
    cfg_enable,
    cfg_mode,
    cfg_hold_last_valid,
    cfg_fallback_enable,
    cfg_heartbeat_enable,
    cfg_seq_reset,
    cfg_signed_clamp,
    cfg_queue_depth,
    cfg_service_flags,
    cfg_timeout_cycles,
    cfg_heartbeat_timeout_cycles,
    cfg_mode_context,
    cfg_operating_point_tag,
    cfg_velocity_tag,
    cfg_geometry_id,
    cfg_velocity_setpoint,
    cfg_age_basis,
    req_valid,
    req_ready,
    req_data,
    rsp_valid,
    rsp_ready,
    rsp_data,
    act_valid,
    act_ready,
    act_data,
    fault_summary,
    heartbeat_status,
    accepted_req_count,
    accepted_rsp_count,
    rejected_rsp_count,
    fallback_entry_count
);

input clk;
input reset;
input cfg_enable;
input [2:0] cfg_mode;
input cfg_hold_last_valid;
input cfg_fallback_enable;
input cfg_heartbeat_enable;
input cfg_seq_reset;
input cfg_signed_clamp;
input [2:0] cfg_queue_depth;
input [7:0] cfg_service_flags;
input [31:0] cfg_timeout_cycles;
input [31:0] cfg_heartbeat_timeout_cycles;
input [3:0] cfg_mode_context;
input [11:0] cfg_operating_point_tag;
input [15:0] cfg_velocity_tag;
input [31:0] cfg_geometry_id;
input [31:0] cfg_velocity_setpoint;
input [31:0] cfg_age_basis;
output reg req_valid;
input req_ready;
output reg [127:0] req_data;
input rsp_valid;
output reg rsp_ready;
input [127:0] rsp_data;
output reg act_valid;
input act_ready;
output reg [63:0] act_data;
output reg [7:0] fault_summary;
output reg [7:0] heartbeat_status;
output reg [15:0] accepted_req_count;
output reg [15:0] accepted_rsp_count;
output reg [7:0] rejected_rsp_count;
output reg [7:0] fallback_entry_count;
reg [15:0] req_seq;
reg [31:0] cycle_count;
reg [31:0] outstanding_age;
reg outstanding;
reg [31:0] heartbeat_age;
reg [63:0] fallback_cmd;
reg [7:0] fault_next;
reg [7:0] hb_next;
reg [63:0] act_next;
reg [127:0] req_next;
reg req_fire;
reg rsp_fire;
reg req_accept;
reg rsp_accept;
reg fallback_active;
reg timeout_fault;
reg protocol_fault;
reg seq_fault;
reg stale_fault;
reg heartbeat_fault;
reg clamp_fault;
wire [15:0] rsp_seq_field;
wire [15:0] rsp_proto_field;
wire [15:0] rsp_status_field;
wire [31:0] rsp_cmd0;
wire [31:0] rsp_cmd1;
reg [63:0] act_clamp_next;

assign rsp_seq_field = rsp_data[15:0];
assign rsp_proto_field = rsp_data[31:16];
assign rsp_status_field = rsp_data[31:0];
assign rsp_cmd0 = rsp_data[63:32];
assign rsp_cmd1 = rsp_data[95:64];

always @(posedge clk or posedge reset) begin
    if (reset) begin
        req_valid <= 1'b0;
        req_data <= 128'h00000000000000000000000000000000;
        rsp_ready <= 1'b1;
        act_valid <= 1'b0;
        act_data <= 64'h0000000000000000;
        fault_summary <= 8'h20;
        heartbeat_status <= 8'h00;
        accepted_req_count <= 16'h0000;
        accepted_rsp_count <= 16'h0000;
        rejected_rsp_count <= 8'h00;
        fallback_entry_count <= 8'h00;
        req_seq <= 16'h0000;
        cycle_count <= 32'h00000000;
        outstanding_age <= 32'h00000000;
        outstanding <= 1'b0;
        heartbeat_age <= 32'h00000000;
        fallback_cmd <= 64'h0000000000000000;
    end else begin
        cycle_count <= cycle_count + 32'd1;
        if (cfg_seq_reset) begin
            req_seq <= 16'h0000;
        end
        if (heartbeat_age != 32'hffffffff) begin
            heartbeat_age <= heartbeat_age + 32'd1;
        end
        if (!outstanding) begin
            outstanding_age <= 32'h00000000;
        end else if (outstanding_age != 32'hffffffff) begin
            outstanding_age <= outstanding_age + 32'd1;
        end
        if (req_valid && req_ready) begin
            accepted_req_count <= accepted_req_count + 16'd1;
            outstanding <= 1'b1;
            req_seq <= req_seq + 16'd1;
            outstanding_age <= 32'h00000000;
            fallback_cmd <= {17'b0, cfg_velocity_setpoint[15:0], cfg_geometry_id[15:0], cfg_mode_context, cfg_mode, cfg_service_flags};
        end
        if (rsp_valid && rsp_ready) begin
            if ((rsp_proto_field[3:0] == 4'h1) && outstanding && (rsp_seq_field == req_seq)) begin
                accepted_rsp_count <= accepted_rsp_count + 16'd1;
                outstanding <= 1'b0;
                act_data <= {rsp_cmd1[15:0], rsp_cmd0[15:0], rsp_cmd1[31:16], rsp_cmd0[31:16]};
                act_valid <= 1'b1;
                heartbeat_age <= 32'h00000000;
            end else begin
                rejected_rsp_count <= rejected_rsp_count + 8'd1;
            end
        end
        if (act_valid && act_ready) begin
            act_valid <= 1'b0;
        end
        if (cfg_enable && !outstanding && !req_valid) begin
            req_valid <= 1'b1;
            req_data <= {16'h0001, req_seq, cfg_mode_context, cfg_mode, cfg_service_flags, cfg_operating_point_tag, cfg_velocity_tag, cfg_geometry_id, cfg_velocity_setpoint, cfg_age_basis};
        end
        if (req_valid && req_ready) begin
            req_valid <= 1'b0;
        end
        ;
        fallback_active <= 1'b0;
        timeout_fault <= 1'b0;
        protocol_fault <= 1'b0;
        seq_fault <= 1'b0;
        stale_fault <= 1'b0;
        heartbeat_fault <= 1'b0;
        clamp_fault <= 1'b0;
        if (outstanding && (outstanding_age >= cfg_timeout_cycles)) begin
            timeout_fault <= 1'b1;
            stale_fault <= 1'b1;
            fallback_active <= cfg_fallback_enable;
            if (cfg_fallback_enable) begin
                fallback_entry_count <= fallback_entry_count + 8'd1;
                act_valid <= 1'b1;
                act_data <= fallback_cmd;
            end
        end
        if (cfg_heartbeat_enable && (heartbeat_age >= cfg_heartbeat_timeout_cycles)) begin
            heartbeat_fault <= 1'b1;
            fallback_active <= cfg_fallback_enable;
            if (cfg_fallback_enable) begin
                act_valid <= 1'b1;
                act_data <= fallback_cmd;
            end
        end
        if (rsp_valid && rsp_ready && outstanding) begin
            if (rsp_proto_field[3:0] != 4'h1) begin
                protocol_fault <= 1'b1;
                rejected_rsp_count <= rejected_rsp_count + 8'd1;
            end
            if (rsp_seq_field != req_seq) begin
                seq_fault <= 1'b1;
            end
        end
        if (cfg_hold_last_valid && accepted_rsp_count != 16'h0000) begin
            fallback_active <= 1'b0;
        end
        heartbeat_status <= {7'h00, ~heartbeat_fault};
        fault_summary <= {heartbeat_fault, clamp_fault, fallback_active, stale_fault, seq_fault, protocol_fault, timeout_fault, 1'b0};
    end
end

always @(*) begin
    req_fire = req_valid && req_ready;
    rsp_fire = rsp_valid && rsp_ready;
    req_accept = cfg_enable && !outstanding && !req_valid;
    rsp_accept = outstanding && rsp_valid && rsp_ready && (rsp_data[31:16] == 16'h0001) && (rsp_data[15:0] == req_seq);
    req_next = req_data;
    act_next = act_data;
    act_clamp_next = act_data;
    fault_next = fault_summary;
    hb_next = heartbeat_status;
    if (outstanding && (outstanding_age >= cfg_timeout_cycles)) begin
        act_next = fallback_cmd;
        act_clamp_next = fallback_cmd;
    end
    if (cfg_heartbeat_enable && (heartbeat_age >= cfg_heartbeat_timeout_cycles)) begin
        act_next = fallback_cmd;
        act_clamp_next = fallback_cmd;
    end
    if (rsp_fire && outstanding) begin
        if (rsp_data[31:16] != 16'h0001) begin
        end
        if (rsp_data[15:0] != req_seq) begin
        end
        if ((rsp_data[31:16] == 16'h0001) && (rsp_data[15:0] == req_seq)) begin
            act_next = {rsp_data[63:32], rsp_data[95:64]};
            act_clamp_next = {rsp_data[63:32], rsp_data[95:64]};
        end
    end
    if (!cfg_enable) begin
        act_next = 64'h0000000000000000;
        act_clamp_next = 64'h0000000000000000;
    end
    if (cfg_signed_clamp) begin
        if ($signed(act_clamp_next[15:0]) < $signed({1'b0, 15'h0000})) begin
            act_next[15:0] = 16'h0000;
        end else if ($signed(act_clamp_next[15:0]) > $signed({1'b0, 15'h7fff})) begin
            act_next[15:0] = 16'h7fff;
        end
    end else begin
        if (act_clamp_next[15:0] < 16'h0000) begin
            act_next[15:0] = 16'h0000;
        end else if (act_clamp_next[15:0] > 16'hffff) begin
            act_next[15:0] = 16'hffff;
        end
    end
end

endmodule
