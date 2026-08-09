module adaptive_aero_control_top (
    clk,
    reset_n,
    reg_addr,
    reg_wdata,
    reg_we,
    reg_re,
    reg_rdata,
    reg_ready,
    model_req_valid,
    model_req_ready,
    model_req_data,
    model_rsp_valid,
    model_rsp_ready,
    model_rsp_data,
    actuator_cmd,
    safe_state
);

input clk;
input reset_n;
input [7:0] reg_addr;
input [31:0] reg_wdata;
input reg_we;
input reg_re;
output [31:0] reg_rdata;
output reg_ready;
output model_req_valid;
input model_req_ready;
output [127:0] model_req_data;
input model_rsp_valid;
output model_rsp_ready;
input [127:0] model_rsp_data;
output [31:0] actuator_cmd;
output [3:0] safe_state;
reg [31:0] reg_rdata_r;
reg reg_ready_r;
reg model_req_valid_r;
reg [127:0] model_req_data_r;
reg model_rsp_ready_r;
reg [31:0] actuator_cmd_r;
reg [3:0] safe_state_r;
reg [31:0] cfg0_stream_velocity;
reg [7:0] cfg1_geom_source_id;
reg [23:0] cfg1_geom_desc_ptr_lo;
reg [31:0] cfg1_geom_desc_ptr_hi;
reg [31:0] cfg2_clamp_min;
reg [31:0] cfg3_clamp_max;
reg [15:0] cfg4_request_timeout;
reg [15:0] cfg4_cmd_freshness_threshold;
reg cfg5_config_valid;
reg cfg5_config_complete;
reg cfg5_req_arm;
reg cfg5_soft_clear_faults;

reg status_response_valid;
reg status_stale_reject;
reg status_timeout_fault;
reg status_clamp_event;
reg status_fallback_active;
reg status_outstanding_seq_valid;
reg status_config_complete_seen;
reg status_watchdog_expired;
reg status_rsp_invalid;
reg status_config_invalid;

reg [15:0] last_request_seq;
reg [15:0] last_accepted_rsp_seq;
reg [15:0] outstanding_seq;
reg [15:0] watchdog_count;
reg [15:0] response_age;
reg outstanding_valid;
reg response_pending;
reg request_active;
reg timeout_fault_sticky;
reg stale_reject_sticky;
reg clamp_event_sticky;
reg rsp_invalid_sticky;
reg config_invalid_sticky;
reg fallback_active_int;
reg [31:0] req_opcode_seq_csum;
reg [31:0] req_geom_meta;
reg [31:0] req_geom_desc_lo;
reg [31:0] req_geom_desc_hi;
reg [31:0] rsp_actuation_raw;
reg [31:0] accepted_rsp_data;
reg [31:0] clamped_actuation;
reg [31:0] request_packet0_shadow;
reg [31:0] request_packet1_shadow;
reg [31:0] request_packet2_shadow;
reg [31:0] request_packet3_shadow;
reg [31:0] rsp_summary0_shadow;
reg [31:0] rsp_summary1_shadow;

wire clamp_min_le_max;
wire cfg_valid_ok;
wire config_complete_ok;
wire config_ok;
wire [31:0] request_packet0_value;
wire [31:0] request_packet1_value;
wire [31:0] request_packet2_value;
wire [31:0] request_packet3_value;
wire [31:0] rsp_summary0_value;
wire [31:0] rsp_summary1_value;
wire [31:0] status0_value;
wire [31:0] status1_value;
wire [31:0] status2_value;
wire [31:0] status3_value;
wire req_issue_ok;
wire rsp_seq_match;
wire rsp_framing_ok;
wire rsp_service_ok;
wire rsp_fresh_ok;
wire rsp_accept_ok;
wire [15:0] next_request_seq;
wire [15:0] next_watchdog_count;
wire [31:0] req_checksum_mix;
wire [31:0] rsp_seq_expanded;
wire [31:0] geom_desc_lo_ext;
wire [31:0] geom_source_id_ext;
wire [31:0] request_timeout_ext;

assign reg_rdata = reg_rdata_r;
assign reg_ready = reg_ready_r;
assign model_req_valid = model_req_valid_r;
assign model_req_data = model_req_data_r;
assign model_rsp_ready = model_rsp_ready_r;
assign actuator_cmd = actuator_cmd_r;
assign safe_state = safe_state_r;

assign clamp_min_le_max = (cfg2_clamp_min <= cfg3_clamp_max);
assign cfg_valid_ok = cfg5_config_valid;
assign config_complete_ok = cfg5_config_complete;
assign config_ok = cfg_valid_ok & config_complete_ok & clamp_min_le_max;

assign geom_desc_lo_ext = {8'b0, cfg1_geom_desc_ptr_lo};
assign geom_source_id_ext = {24'b0, cfg1_geom_source_id};
assign request_timeout_ext = {16'b0, cfg4_request_timeout};
assign req_checksum_mix = cfg0_stream_velocity ^ geom_source_id_ext ^ request_timeout_ext ^ {16'b0, last_request_seq};
assign next_request_seq = last_request_seq + 16'd1;
assign next_watchdog_count = watchdog_count + 16'd1;
assign rsp_seq_expanded = {16'b0, outstanding_seq};

assign req_issue_ok = config_ok & cfg5_req_arm & (~outstanding_valid) & (~fallback_active_int);

assign rsp_seq_match = outstanding_valid & model_rsp_valid & (model_rsp_data[15:0] == outstanding_seq);
assign rsp_framing_ok = model_rsp_data[24];
assign rsp_service_ok = model_rsp_data[26];
assign rsp_fresh_ok = (model_rsp_data[31:16] <= cfg4_cmd_freshness_threshold);
assign rsp_accept_ok = model_rsp_valid & model_rsp_ready_r & rsp_framing_ok & rsp_seq_match & rsp_service_ok & rsp_fresh_ok & outstanding_valid;

assign request_packet0_value = {8'hA5, last_request_seq, req_checksum_mix[31:24]};
assign request_packet1_value = {cfg1_geom_source_id, 8'h00, cfg0_stream_velocity[31:16]};
assign request_packet2_value = {8'b0, cfg1_geom_desc_ptr_lo};
assign request_packet3_value = cfg1_geom_desc_ptr_hi;
assign rsp_summary0_value = {7'b0, 3'b000, model_rsp_valid, rsp_accept_ok, rsp_fresh_ok, rsp_service_ok, rsp_seq_match, rsp_framing_ok, outstanding_seq};
assign rsp_summary1_value = rsp_actuation_raw;

assign status0_value = {22'b0,
                        status_config_complete_seen,
                        status_outstanding_seq_valid,
                        status_fallback_active,
                        status_clamp_event,
                        status_timeout_fault,
                        status_stale_reject,
                        status_response_valid,
                        response_pending,
                        request_active,
                        1'b0};
assign status1_value = {last_accepted_rsp_seq, last_request_seq};
assign status2_value = actuator_cmd_r;
assign status3_value = {28'b0, status_config_invalid, status_rsp_invalid, status_timeout_fault, status_watchdog_expired};

always @(*) begin
    reg_rdata_r = 32'h00000000;
    reg_ready_r = 1'b1;
    model_req_valid_r = 1'b0;
    model_req_data_r = 128'h00000000000000000000000000000000;
    model_rsp_ready_r = 1'b0;
    actuator_cmd_r = 32'h00000000;
    safe_state_r = 4'b0001;

    case (reg_addr)
        8'h00: reg_rdata_r = cfg0_stream_velocity;
        8'h04: reg_rdata_r = {cfg1_geom_desc_ptr_lo[23:0], cfg1_geom_source_id};
        8'h08: reg_rdata_r = cfg2_clamp_min;
        8'h0C: reg_rdata_r = cfg3_clamp_max;
        8'h10: reg_rdata_r = {cfg4_cmd_freshness_threshold, cfg4_request_timeout};
        8'h14: reg_rdata_r = {28'b0, cfg5_soft_clear_faults, cfg5_req_arm, cfg5_config_complete, cfg5_config_valid};
        8'h18: reg_rdata_r = status0_value;
        8'h1C: reg_rdata_r = status1_value;
        8'h20: reg_rdata_r = status2_value;
        8'h24: reg_rdata_r = status3_value;
        8'h28: reg_rdata_r = request_packet0_shadow;
        8'h2C: reg_rdata_r = request_packet1_shadow;
        8'h30: reg_rdata_r = request_packet2_shadow;
        8'h34: reg_rdata_r = request_packet3_shadow;
        8'h38: reg_rdata_r = rsp_summary0_shadow;
        8'h3C: reg_rdata_r = rsp_summary1_shadow;
        default: reg_rdata_r = 32'h00000000;
    endcase

    if (config_ok && (~fallback_active_int)) begin
        safe_state_r = {status_timeout_fault, status_stale_reject, status_clamp_event, 1'b0};
        actuator_cmd_r = clamped_actuation;
    end else begin
        safe_state_r = {status_timeout_fault, status_stale_reject, status_rsp_invalid | status_config_invalid, 1'b1};
        actuator_cmd_r = 32'h00000000;
    end

    if (req_issue_ok && model_req_ready) begin
        model_req_valid_r = 1'b1;
        model_req_data_r = {8'b0, req_checksum_mix, cfg1_geom_desc_ptr_hi, cfg1_geom_desc_ptr_lo, cfg0_stream_velocity};
    end else begin
        model_req_valid_r = 1'b0;
        model_req_data_r = {req_opcode_seq_csum, req_geom_meta, req_geom_desc_hi, req_geom_desc_lo};
    end

    model_rsp_ready_r = outstanding_valid & config_ok & (~fallback_active_int);
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cfg0_stream_velocity <= 32'h00000000;
        cfg1_geom_source_id <= 8'h00;
        cfg1_geom_desc_ptr_lo <= 24'h000000;
        cfg1_geom_desc_ptr_hi <= 32'h00000000;
        cfg2_clamp_min <= 32'h00000000;
        cfg3_clamp_max <= 32'h00000000;
        cfg4_request_timeout <= 16'h0000;
        cfg4_cmd_freshness_threshold <= 16'h0000;
        cfg5_config_valid <= 1'b0;
        cfg5_config_complete <= 1'b0;
        cfg5_req_arm <= 1'b0;
        cfg5_soft_clear_faults <= 1'b0;
        status_response_valid <= 1'b0;
        status_stale_reject <= 1'b0;
        status_timeout_fault <= 1'b0;
        status_clamp_event <= 1'b0;
        status_fallback_active <= 1'b1;
        status_outstanding_seq_valid <= 1'b0;
        status_config_complete_seen <= 1'b0;
        status_watchdog_expired <= 1'b0;
        status_rsp_invalid <= 1'b0;
        status_config_invalid <= 1'b1;
        last_request_seq <= 16'h0000;
        last_accepted_rsp_seq <= 16'h0000;
        outstanding_seq <= 16'h0000;
        watchdog_count <= 16'h0000;
        response_age <= 16'h0000;
        outstanding_valid <= 1'b0;
        response_pending <= 1'b0;
        request_active <= 1'b0;
        timeout_fault_sticky <= 1'b0;
        stale_reject_sticky <= 1'b0;
        clamp_event_sticky <= 1'b0;
        rsp_invalid_sticky <= 1'b0;
        config_invalid_sticky <= 1'b1;
        fallback_active_int <= 1'b1;
        req_opcode_seq_csum <= 32'h00000000;
        req_geom_meta <= 32'h00000000;
        req_geom_desc_lo <= 32'h00000000;
        req_geom_desc_hi <= 32'h00000000;
        rsp_actuation_raw <= 32'h00000000;
        accepted_rsp_data <= 32'h00000000;
        clamped_actuation <= 32'h00000000;
        request_packet0_shadow <= 32'h00000000;
        request_packet1_shadow <= 32'h00000000;
        request_packet2_shadow <= 32'h00000000;
        request_packet3_shadow <= 32'h00000000;
        rsp_summary0_shadow <= 32'h00000000;
        rsp_summary1_shadow <= 32'h00000000;
    end else begin
        cfg5_soft_clear_faults <= 1'b0;

        if (reg_we) begin
            case (reg_addr)
                8'h00: cfg0_stream_velocity <= reg_wdata;
                8'h04: begin
                    cfg1_geom_source_id <= reg_wdata[7:0];
                    cfg1_geom_desc_ptr_lo <= reg_wdata[31:8];
                end
                8'h08: cfg2_clamp_min <= reg_wdata;
                8'h0C: cfg3_clamp_max <= reg_wdata;
                8'h10: begin
                    cfg4_request_timeout <= reg_wdata[15:0];
                    cfg4_cmd_freshness_threshold <= reg_wdata[31:16];
                end
                8'h14: begin
                    cfg5_config_valid <= reg_wdata[0];
                    cfg5_config_complete <= reg_wdata[1];
                    cfg5_req_arm <= reg_wdata[2];
                    cfg5_soft_clear_faults <= reg_wdata[3];
                end
                default: begin
                end
            endcase
        end

        cfg1_geom_desc_ptr_hi <= {8'b0, cfg1_geom_desc_ptr_lo} + {24'b0, cfg1_geom_source_id};

        status_config_invalid <= ~(cfg5_config_valid & cfg5_config_complete & clamp_min_le_max);
        status_config_complete_seen <= cfg5_config_complete & cfg5_config_valid;
        status_fallback_active <= fallback_active_int;
        status_outstanding_seq_valid <= outstanding_valid;
        status_timeout_fault <= timeout_fault_sticky;
        status_stale_reject <= stale_reject_sticky;
        status_clamp_event <= clamp_event_sticky;
        status_rsp_invalid <= rsp_invalid_sticky;
        status_watchdog_expired <= timeout_fault_sticky;
        status_response_valid <= rsp_accept_ok;

        if (cfg5_soft_clear_faults) begin
            timeout_fault_sticky <= 1'b0;
            stale_reject_sticky <= 1'b0;
            clamp_event_sticky <= 1'b0;
            rsp_invalid_sticky <= 1'b0;
            config_invalid_sticky <= 1'b0;
        end

        if (req_issue_ok && model_req_ready) begin
            last_request_seq <= next_request_seq;
            outstanding_seq <= next_request_seq;
            outstanding_valid <= 1'b1;
            response_pending <= 1'b1;
            request_active <= 1'b1;
            watchdog_count <= 16'h0000;
            req_opcode_seq_csum <= {8'hA5, next_request_seq, req_checksum_mix[31:24]};
            req_geom_meta <= {1'b0, cfg1_geom_source_id, 7'b0, cfg4_request_timeout[7:0], cfg0_stream_velocity[31:24]};
            req_geom_desc_lo <= {8'b0, cfg1_geom_desc_ptr_lo};
            req_geom_desc_hi <= cfg1_geom_desc_ptr_hi;
            request_packet0_shadow <= {8'hA5, next_request_seq, req_checksum_mix[31:24]};
            request_packet1_shadow <= {cfg1_geom_source_id, 8'h00, cfg0_stream_velocity[31:16]};
            request_packet2_shadow <= {8'b0, cfg1_geom_desc_ptr_lo};
            request_packet3_shadow <= cfg1_geom_desc_ptr_hi;
            rsp_summary0_shadow <= rsp_summary0_value;
            rsp_summary1_shadow <= rsp_summary1_value;
        end else if (outstanding_valid) begin
            watchdog_count <= next_watchdog_count;
        end

        if (model_rsp_valid) begin
            if (rsp_accept_ok) begin
                last_accepted_rsp_seq <= outstanding_seq;
                accepted_rsp_data <= model_rsp_data[95:64];
                rsp_actuation_raw <= model_rsp_data[95:64];
                response_age <= model_rsp_data[31:16];
                outstanding_valid <= 1'b0;
                response_pending <= 1'b0;
                request_active <= 1'b0;
                fallback_active_int <= 1'b0;
                if (model_rsp_data[95:64] < cfg2_clamp_min) begin
                    clamped_actuation <= cfg2_clamp_min;
                    clamp_event_sticky <= 1'b1;
                end else if (model_rsp_data[95:64] > cfg3_clamp_max) begin
                    clamped_actuation <= cfg3_clamp_max;
                    clamp_event_sticky <= 1'b1;
                end else begin
                    clamped_actuation <= model_rsp_data[95:64];
                end
            end else begin
                rsp_invalid_sticky <= 1'b1;
                stale_reject_sticky <= ~rsp_seq_match;
                fallback_active_int <= 1'b1;
            end
        end

        if (outstanding_valid && (cfg4_request_timeout != 16'h0000) && (watchdog_count >= cfg4_request_timeout)) begin
            timeout_fault_sticky <= 1'b1;
            fallback_active_int <= 1'b1;
            outstanding_valid <= 1'b0;
            response_pending <= 1'b0;
            request_active <= 1'b0;
        end

        if (~config_ok) begin
            fallback_active_int <= 1'b1;
            config_invalid_sticky <= 1'b1;
        end
    end
end

endmodule
