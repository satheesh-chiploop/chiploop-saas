module motor_control_top (
    clk,
    reset_n,
    host_if_addr,
    host_if_wdata,
    host_if_we,
    host_if_re,
    host_if_valid,
    host_if_rdata,
    host_if_ready,
    gpu_request_if_valid,
    gpu_request_if_ready,
    gpu_request_if_data,
    gpu_response_if_valid,
    gpu_response_if_ready,
    gpu_response_if_data,
    actuator_cmd_if_valid,
    actuator_cmd_if_ready,
    actuator_cmd_if_cmd,
    heartbeat_if_hb,
    status_busy,
    status_req_outstanding,
    status_resp_valid,
    status_velocity_ok,
    status_timeout_fault,
    status_stale_fault,
    status_duplicate_fault,
    status_range_fault,
    status_transport_fault,
    status_watchdog_fault,
    status_fallback_active,
    status_cmd_clamped,
    status_fault_latched,
    fault_code
);

input clk;
input reset_n;
input [5:0] host_if_addr;
input [63:0] host_if_wdata;
input host_if_we;
input host_if_re;
input host_if_valid;
output [63:0] host_if_rdata;
output host_if_ready;
output gpu_request_if_valid;
input gpu_request_if_ready;
output [63:0] gpu_request_if_data;
input gpu_response_if_valid;
output gpu_response_if_ready;
input [63:0] gpu_response_if_data;
output actuator_cmd_if_valid;
input actuator_cmd_if_ready;
output [31:0] actuator_cmd_if_cmd;
input heartbeat_if_hb;
output status_busy;
output status_req_outstanding;
output status_resp_valid;
output status_velocity_ok;
output status_timeout_fault;
output status_stale_fault;
output status_duplicate_fault;
output status_range_fault;
output status_transport_fault;
output status_watchdog_fault;
output status_fallback_active;
output status_cmd_clamped;
output status_fault_latched;
output [7:0] fault_code;
reg [63:0] host_if_rdata_r;
reg host_if_ready_r;
reg gpu_request_if_valid_r;
reg [63:0] gpu_request_if_data_r;
reg gpu_response_if_ready_r;
reg actuator_cmd_if_valid_r;
reg [31:0] actuator_cmd_if_cmd_r;
reg status_busy_r;
reg status_req_outstanding_r;
reg status_resp_valid_r;
reg status_velocity_ok_r;
reg status_timeout_fault_r;
reg status_stale_fault_r;
reg status_duplicate_fault_r;
reg status_range_fault_r;
reg status_transport_fault_r;
reg status_watchdog_fault_r;
reg status_fallback_active_r;
reg status_cmd_clamped_r;
reg status_fault_latched_r;
reg [7:0] fault_code_r;
reg [63:0] csr0_control_reg;
reg [7:0] csr1_timeout_reg;
reg [15:0] csr2_velocity_reg;
reg [15:0] csr3_actuator_min_reg;
reg [15:0] csr4_actuator_max_reg;
reg [15:0] req_seq_reg;
reg [63:0] last_desc_reg;
reg [63:0] last_resp_summary_reg;
reg [7:0] timeout_counter_reg;
reg [7:0] watchdog_counter_reg;
reg [63:0] pending_resp_data_reg;
reg [15:0] pending_resp_token_reg;
reg pending_resp_valid_reg;
reg pending_launch_reg;
reg [15:0] active_req_seq_reg;
reg [63:0] active_desc_reg;
reg [1:0] launch_state_reg;

wire enable;
wire soft_reset;
wire model_launch;
wire ack_fault;
wire safe_mode_force;
wire [2:0] mode_select;
wire [7:0] timeout_cfg;
wire [15:0] velocity_mps_q;
wire [15:0] actuator_min;
wire [15:0] actuator_max;
wire velocity_ok;
wire hard_fault_any;
wire fault_latched_any;
wire [15:0] rx_seq;
wire rx_seq_match_active;
wire rx_seq_mismatch;
wire rx_seq_duplicate;
wire host_access;
wire host_write;
wire host_read;
wire timeout_expired;
wire watchdog_expired;
wire [31:0] safe_cmd_word;
wire [31:0] validated_cmd_word;
wire [31:0] clamped_cmd_word;
wire cmd_needs_clamp;
wire cmd_validated_ok;
wire [63:0] descriptor_word;
wire [63:0] response_summary_word;

assign enable = csr0_control_reg[0];
assign soft_reset = csr0_control_reg[1];
assign model_launch = csr0_control_reg[2];
assign ack_fault = csr0_control_reg[3];
assign safe_mode_force = csr0_control_reg[4];
assign mode_select = csr0_control_reg[7:5];
assign timeout_cfg = csr1_timeout_reg[7:0];
assign velocity_mps_q = csr2_velocity_reg[15:0];
assign actuator_min = csr3_actuator_min_reg[15:0];
assign actuator_max = csr4_actuator_max_reg[15:0];
assign velocity_ok = (velocity_mps_q >= 16'd20) && (velocity_mps_q <= 16'd55);
assign fault_latched_any = status_fault_latched_r;
assign hard_fault_any = status_fault_latched_r;
assign rx_seq = gpu_response_if_data[15:0];
assign rx_seq_match_active = (pending_resp_valid_reg && gpu_response_if_valid && (rx_seq == active_req_seq_reg) && status_req_outstanding_r);
assign rx_seq_mismatch = (gpu_response_if_valid && status_req_outstanding_r && pending_resp_valid_reg && (rx_seq != active_req_seq_reg));
assign rx_seq_duplicate = (gpu_response_if_valid && !status_req_outstanding_r && (rx_seq == active_req_seq_reg));
assign host_access = host_if_valid;
assign host_write = host_if_valid && host_if_we;
assign host_read = host_if_valid && host_if_re;
assign timeout_expired = (timeout_counter_reg == 8'h00) && status_req_outstanding_r && pending_launch_reg;
assign watchdog_expired = (watchdog_counter_reg == 8'h00) && !heartbeat_if_hb;
assign safe_cmd_word = 32'h00000000;
assign validated_cmd_word = response_summary_word[31:0];
assign cmd_needs_clamp = (validated_cmd_word < {16'h0000, actuator_min}) || (validated_cmd_word > {16'h0000, actuator_max});
assign clamped_cmd_word = (validated_cmd_word < {16'h0000, actuator_min}) ? {16'h0000, actuator_min} : ((validated_cmd_word > {16'h0000, actuator_max}) ? {16'h0000, actuator_max} : validated_cmd_word);
assign cmd_validated_ok = status_resp_valid_r && !hard_fault_any && !safe_mode_force && enable && velocity_ok;

assign descriptor_word = last_desc_reg;
assign response_summary_word = last_resp_summary_reg;

assign host_if_rdata = host_if_rdata_r;
assign host_if_ready = host_if_ready_r;
assign gpu_request_if_valid = gpu_request_if_valid_r;
assign gpu_request_if_data = gpu_request_if_data_r;
assign gpu_response_if_ready = gpu_response_if_ready_r;
assign actuator_cmd_if_valid = actuator_cmd_if_valid_r;
assign actuator_cmd_if_cmd = actuator_cmd_if_cmd_r;
assign status_busy = status_busy_r;
assign status_req_outstanding = status_req_outstanding_r;
assign status_resp_valid = status_resp_valid_r;
assign status_velocity_ok = status_velocity_ok_r;
assign status_timeout_fault = status_timeout_fault_r;
assign status_stale_fault = status_stale_fault_r;
assign status_duplicate_fault = status_duplicate_fault_r;
assign status_range_fault = status_range_fault_r;
assign status_transport_fault = status_transport_fault_r;
assign status_watchdog_fault = status_watchdog_fault_r;
assign status_fallback_active = status_fallback_active_r;
assign status_cmd_clamped = status_cmd_clamped_r;
assign status_fault_latched = status_fault_latched_r;
assign fault_code = fault_code_r;

always @(*) begin
    host_if_rdata_r = 64'h0000000000000000;
    host_if_ready_r = 1'b1;
    status_busy_r = status_req_outstanding_r || status_fault_latched_r || pending_launch_reg;
    status_velocity_ok_r = velocity_ok;
    if (host_access) begin
        case (host_if_addr)
            6'h00: host_if_rdata_r = csr0_control_reg;
            6'h01: host_if_rdata_r = {56'h00000000000000, csr1_timeout_reg};
            6'h02: host_if_rdata_r = {48'h000000000000, csr2_velocity_reg};
            6'h03: host_if_rdata_r = {48'h000000000000, csr3_actuator_min_reg};
            6'h04: host_if_rdata_r = {48'h000000000000, csr4_actuator_max_reg};
            6'h05: host_if_rdata_r = {56'h00000000000000, status_busy_r, status_req_outstanding_r, status_resp_valid_r, status_velocity_ok_r, status_timeout_fault_r, status_stale_fault_r, status_duplicate_fault_r, status_range_fault_r};
            6'h06: host_if_rdata_r = {48'h000000000000, status_transport_fault_r, status_watchdog_fault_r, status_fallback_active_r, status_cmd_clamped_r, status_fault_latched_r, 3'h0, fault_code_r};
            6'h07: host_if_rdata_r = {48'h000000000000, req_seq_reg};
            6'h08: host_if_rdata_r = last_desc_reg[31:0];
            6'h09: host_if_rdata_r = last_desc_reg[63:32];
            6'h0A: host_if_rdata_r = last_resp_summary_reg[31:0];
            6'h0B: host_if_rdata_r = last_resp_summary_reg[63:32];
            default: host_if_rdata_r = 64'h0000000000000000;
        endcase
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        csr0_control_reg <= 64'h0000000000000000;
        csr1_timeout_reg <= 8'h00;
        csr2_velocity_reg <= 16'h0000;
        csr3_actuator_min_reg <= 16'h0000;
        csr4_actuator_max_reg <= 16'hffff;
        req_seq_reg <= 16'h0000;
        last_desc_reg <= 64'h0000000000000000;
        last_resp_summary_reg <= 64'h0000000000000000;
        timeout_counter_reg <= 8'h00;
        watchdog_counter_reg <= 8'h00;
        pending_resp_data_reg <= 64'h0000000000000000;
        pending_resp_token_reg <= 16'h0000;
        pending_resp_valid_reg <= 1'b0;
        pending_launch_reg <= 1'b0;
        active_req_seq_reg <= 16'h0000;
        active_desc_reg <= 64'h0000000000000000;
        launch_state_reg <= 2'b00;
        status_resp_valid_r <= 1'b0;
        status_timeout_fault_r <= 1'b0;
        status_stale_fault_r <= 1'b0;
        status_duplicate_fault_r <= 1'b0;
        status_range_fault_r <= 1'b0;
        status_transport_fault_r <= 1'b0;
        status_watchdog_fault_r <= 1'b0;
        status_fallback_active_r <= 1'b1;
        status_cmd_clamped_r <= 1'b0;
        status_fault_latched_r <= 1'b0;
        fault_code_r <= 8'h00;
        gpu_request_if_valid_r <= 1'b0;
        gpu_request_if_data_r <= 64'h0000000000000000;
        gpu_response_if_ready_r <= 1'b1;
        actuator_cmd_if_valid_r <= 1'b1;
        actuator_cmd_if_cmd_r <= 32'h00000000;
    end else begin
        if (soft_reset) begin
            status_resp_valid_r <= 1'b0;
            status_timeout_fault_r <= 1'b0;
            status_stale_fault_r <= 1'b0;
            status_duplicate_fault_r <= 1'b0;
            status_range_fault_r <= 1'b0;
            status_transport_fault_r <= 1'b0;
            status_watchdog_fault_r <= 1'b0;
            status_cmd_clamped_r <= 1'b0;
            status_fault_latched_r <= 1'b0;
            fault_code_r <= 8'h00;
            pending_launch_reg <= 1'b0;
            pending_resp_valid_reg <= 1'b0;
            timeout_counter_reg <= csr1_timeout_reg;
            watchdog_counter_reg <= 8'h00;
            status_fallback_active_r <= 1'b1;
        end else begin
            if (host_write && (host_if_addr == 6'h00)) begin
                csr0_control_reg <= host_if_wdata;
            end
            if (host_write && (host_if_addr == 6'h01)) csr1_timeout_reg <= host_if_wdata[7:0];
            if (host_write && (host_if_addr == 6'h02)) csr2_velocity_reg <= host_if_wdata[15:0];
            if (host_write && (host_if_addr == 6'h03)) csr3_actuator_min_reg <= host_if_wdata[15:0];
            if (host_write && (host_if_addr == 6'h04)) csr4_actuator_max_reg <= host_if_wdata[15:0];
            if (host_write && (host_if_addr == 6'h00) && host_if_wdata[1]) begin
                status_fault_latched_r <= 1'b0;
                status_timeout_fault_r <= 1'b0;
                status_stale_fault_r <= 1'b0;
                status_duplicate_fault_r <= 1'b0;
                status_range_fault_r <= 1'b0;
                status_transport_fault_r <= 1'b0;
                status_watchdog_fault_r <= 1'b0;
                fault_code_r <= 8'h00;
            end
            if (host_write && (host_if_addr == 6'h00) && host_if_wdata[3]) begin
                status_fault_latched_r <= 1'b0;
                status_timeout_fault_r <= 1'b0;
                status_stale_fault_r <= 1'b0;
                status_duplicate_fault_r <= 1'b0;
                status_range_fault_r <= 1'b0;
                status_transport_fault_r <= 1'b0;
                status_watchdog_fault_r <= 1'b0;
                fault_code_r <= 8'h00;
            end
            if (host_write && (host_if_addr == 6'h00) && host_if_wdata[2] && enable && velocity_ok && !hard_fault_any && !safe_mode_force) begin
                pending_launch_reg <= 1'b1;
                req_seq_reg <= req_seq_reg + 16'h0001;
                active_req_seq_reg <= req_seq_reg + 16'h0001;
                active_desc_reg <= {16'h0000, req_seq_reg + 16'h0001, 8'hA5, 8'h5A, mode_select, 29'h00000000};
                last_desc_reg <= {16'h0000, req_seq_reg + 16'h0001, 8'hA5, 8'h5A, mode_select, 29'h00000000};
                timeout_counter_reg <= csr1_timeout_reg;
                watchdog_counter_reg <= csr1_timeout_reg;
                status_req_outstanding_r <= 1'b1;
                status_resp_valid_r <= 1'b0;
                pending_resp_valid_reg <= 1'b1;
                pending_resp_token_reg <= req_seq_reg + 16'h0001;
            end
            if (host_write && (host_if_addr == 6'h00) && host_if_wdata[4]) begin
                status_fallback_active_r <= 1'b1;
            end
            if (!enable || safe_mode_force || hard_fault_any || !velocity_ok) begin
                status_fallback_active_r <= 1'b1;
            end
            if (gpu_request_if_valid_r && gpu_request_if_ready) begin
                pending_launch_reg <= 1'b0;
            end
            if (gpu_response_if_valid && status_req_outstanding_r) begin
                if (rx_seq_match_active) begin
                    status_resp_valid_r <= 1'b1;
                    status_fallback_active_r <= 1'b0;
                    last_resp_summary_reg <= gpu_response_if_data;
                    status_cmd_clamped_r <= cmd_needs_clamp;
                    if (cmd_needs_clamp) begin
                        actuator_cmd_if_cmd_r <= clamped_cmd_word;
                    end else begin
                        actuator_cmd_if_cmd_r <= validated_cmd_word;
                    end
                    status_req_outstanding_r <= 1'b0;
                    pending_resp_valid_reg <= 1'b0;
                end else if (rx_seq_mismatch) begin
                    status_stale_fault_r <= 1'b1;
                    status_fault_latched_r <= 1'b1;
                    status_transport_fault_r <= 1'b1;
                    fault_code_r <= 8'h05;
                    status_fallback_active_r <= 1'b1;
                end
            end else if (gpu_response_if_valid && !status_req_outstanding_r) begin
                if (rx_seq_duplicate) begin
                    status_duplicate_fault_r <= 1'b1;
                    status_fault_latched_r <= 1'b1;
                    fault_code_r <= 8'h04;
                    status_fallback_active_r <= 1'b1;
                end
            end
            if (status_req_outstanding_r && !timeout_expired && timeout_counter_reg != 8'h00) begin
                timeout_counter_reg <= timeout_counter_reg - 8'h01;
            end
            if (status_req_outstanding_r && timeout_expired) begin
                status_timeout_fault_r <= 1'b1;
                status_fault_latched_r <= 1'b1;
                fault_code_r <= 8'h02;
                status_req_outstanding_r <= 1'b0;
                pending_launch_reg <= 1'b0;
                status_fallback_active_r <= 1'b1;
            end
            if (!heartbeat_if_hb) begin
                if (watchdog_counter_reg != 8'h00) begin
                    watchdog_counter_reg <= watchdog_counter_reg - 8'h01;
                end else begin
                    status_watchdog_fault_r <= 1'b1;
                    status_fault_latched_r <= 1'b1;
                    fault_code_r <= 8'h06;
                    status_fallback_active_r <= 1'b1;
                end
            end else begin
                watchdog_counter_reg <= csr1_timeout_reg;
            end
            if (ack_fault && enable && !safe_mode_force) begin
                status_fault_latched_r <= 1'b0;
                status_timeout_fault_r <= 1'b0;
                status_stale_fault_r <= 1'b0;
                status_duplicate_fault_r <= 1'b0;
                status_range_fault_r <= 1'b0;
                status_transport_fault_r <= 1'b0;
                status_watchdog_fault_r <= 1'b0;
                fault_code_r <= 8'h00;
            end
            if (!enable || safe_mode_force || status_fault_latched_r) begin
                status_fallback_active_r <= 1'b1;
            end else if (status_resp_valid_r) begin
                status_fallback_active_r <= 1'b0;
            end
            if (!enable || safe_mode_force || status_fallback_active_r || status_fault_latched_r) begin
                actuator_cmd_if_valid_r <= 1'b1;
                actuator_cmd_if_cmd_r <= safe_cmd_word;
            end else if (status_resp_valid_r) begin
                actuator_cmd_if_valid_r <= 1'b1;
                actuator_cmd_if_cmd_r <= clamped_cmd_word;
            end else begin
                actuator_cmd_if_valid_r <= 1'b1;
                actuator_cmd_if_cmd_r <= safe_cmd_word;
            end
        end
    end
end

endmodule
