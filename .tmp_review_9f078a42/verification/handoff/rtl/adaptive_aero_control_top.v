module adaptive_aero_control_top (
    clk,
    reset_n,
    mmio_addr,
    mmio_wdata,
    mmio_we,
    mmio_re,
    mmio_rdata,
    mmio_ready,
    mmio_error,
    req_valid,
    req_ready,
    req_data,
    rsp_valid,
    rsp_ready,
    rsp_data,
    act_cmd_valid,
    act_cmd_fault,
    act_cmd_data,
    irq
);

input clk;
input reset_n;
input [3:0] mmio_addr;
input [63:0] mmio_wdata;
input mmio_we;
input mmio_re;
output [63:0] mmio_rdata;
output mmio_ready;
output mmio_error;
output req_valid;
input req_ready;
output [63:0] req_data;
input rsp_valid;
output rsp_ready;
input [63:0] rsp_data;
output act_cmd_valid;
output act_cmd_fault;
output [31:0] act_cmd_data;
output irq;

reg [63:0] mmio_rdata_r;
reg mmio_ready_r;
reg mmio_error_r;
reg req_valid_r;
reg [63:0] req_data_r;
reg rsp_ready_r;
reg act_cmd_valid_r;
reg act_cmd_fault_r;
reg [31:0] act_cmd_data_r;
reg irq_r;

reg [7:0] ctrl_reg;
reg [63:0] mode_seq_reg;
reg [63:0] limits_reg;
reg [63:0] bounds_reg;
reg [63:0] irq_en_reg;
reg [63:0] req_meta_reg;

reg [15:0] accepted_count_reg;
reg [15:0] rejected_count_reg;

reg [15:0] outstanding_seq_reg;
reg [15:0] outstanding_age_reg;
reg outstanding_valid_reg;

reg status_req_accepted_reg;
reg status_rsp_received_reg;
reg status_rsp_validated_reg;
reg status_clamp_applied_reg;
reg status_stale_reject_reg;
reg status_timeout_reg;
reg status_fallback_active_reg;
reg status_fault_active_reg;
reg busy_reg;

reg req_hist_csb;
reg req_hist_web;
reg [3:0] req_hist_addr;
reg [63:0] req_hist_din;
wire [63:0] req_hist_dout;

reg [1:0] state_reg;
reg [1:0] state_next;

reg [63:0] status_reg_r;
reg [63:0] read_data_next;

reg pending_launch_reg;
reg pending_clear_fault_reg;
reg pending_rearm_reg;
reg hold_safe_sel_reg;
reg launch_accept_pulse;
reg clear_fault_pulse;
reg rearm_pulse;
reg req_hist_write_pulse;
reg req_hist_read_pulse;
reg req_hist_write_pending_reg;
reg req_hist_read_pending_reg;
reg rsp_valid_sync;
reg [15:0] rsp_seq_in;
reg [15:0] rsp_cmd_in;
reg rsp_schema_ok;
reg [31:0] clamp_value_next;
reg clamp_needed_next;
reg fallback_value_sel;
reg fault_latched_reg;
reg transport_error_reg;
reg malformed_rsp_reg;

localparam STATE_IDLE = 2'd0;
localparam STATE_ISSUE_REQ = 2'd1;
localparam STATE_WAIT_RSP = 2'd2;
localparam STATE_FAULT = 2'd3;

assign mmio_rdata = mmio_rdata_r;
assign mmio_ready = mmio_ready_r;
assign mmio_error = mmio_error_r;
assign req_valid = req_valid_r;
assign req_data = req_data_r;
assign rsp_ready = rsp_ready_r;
assign act_cmd_valid = act_cmd_valid_r;
assign act_cmd_fault = act_cmd_fault_r;
assign act_cmd_data = act_cmd_data_r;
assign irq = irq_r;

assign req_hist_dout = 64'h0000000000000000;

always @(*) begin
    state_next = state_reg;
    mmio_rdata_r = 64'h0000000000000000;
    mmio_ready_r = 1'b1;
    mmio_error_r = 1'b0;
    status_reg_r = 64'h0000000000000000;
    read_data_next = 64'h0000000000000000;
    launch_accept_pulse = 1'b0;
    clear_fault_pulse = 1'b0;
    rearm_pulse = 1'b0;
    req_hist_write_pulse = 1'b0;
    req_hist_read_pulse = 1'b0;
    clamp_value_next = 32'h00000000;
    clamp_needed_next = 1'b0;
    fallback_value_sel = hold_safe_sel_reg;
    rsp_valid_sync = rsp_valid;
    rsp_seq_in = rsp_data[15:0];
    rsp_cmd_in = rsp_data[31:16];
    rsp_schema_ok = ~rsp_data[63];
    transport_error_reg = 1'b0;
    malformed_rsp_reg = 1'b0;

    status_reg_r[0] = busy_reg;
    status_reg_r[1] = status_req_accepted_reg;
    status_reg_r[2] = status_rsp_received_reg;
    status_reg_r[3] = status_rsp_validated_reg;
    status_reg_r[4] = status_clamp_applied_reg;
    status_reg_r[5] = status_stale_reject_reg;
    status_reg_r[6] = status_timeout_reg;
    status_reg_r[7] = status_fallback_active_reg;
    status_reg_r[8] = status_fault_active_reg;
    status_reg_r[31:16] = accepted_count_reg;
    status_reg_r[47:32] = rejected_count_reg;

    case (mmio_addr)
        4'h0: read_data_next = {59'b0, ctrl_reg[4:0]};
        4'h1: read_data_next = mode_seq_reg;
        4'h2: read_data_next = limits_reg;
        4'h3: read_data_next = bounds_reg;
        4'h4: read_data_next = status_reg_r;
        4'h5: read_data_next = irq_en_reg;
        4'h6: read_data_next = req_meta_reg;
        4'h7: read_data_next = {58'b0, req_hist_read_pending_reg, req_hist_write_pending_reg, req_hist_addr};
        default: read_data_next = 64'h0000000000000000;
    endcase

    if (mmio_we) begin
        case (mmio_addr)
            4'h0: begin
                if (mmio_wdata[2]) clear_fault_pulse = 1'b1;
                if (mmio_wdata[3]) rearm_pulse = 1'b1;
                if (mmio_wdata[1]) launch_accept_pulse = 1'b1;
            end
            4'h7: begin
                req_hist_write_pulse = mmio_wdata[4];
                req_hist_read_pulse = mmio_wdata[5];
            end
            default: begin
            end
        endcase
    end

    if (mmio_re) begin
        mmio_rdata_r = read_data_next;
    end

    if (ctrl_reg[0] && launch_accept_pulse && !outstanding_valid_reg && !status_fault_active_reg) begin
        state_next = STATE_ISSUE_REQ;
    end else begin
    end

    if (outstanding_valid_reg) begin
    end else if (ctrl_reg[0] && !status_fault_active_reg) begin
    end else begin
    end

    if (outstanding_valid_reg && (outstanding_age_reg >= limits_reg[15:0]) && (limits_reg[15:0] != 16'h0000)) begin
        state_next = STATE_FAULT;
    end

    if (rsp_valid_sync && outstanding_valid_reg) begin
        if (rsp_schema_ok && (rsp_seq_in == outstanding_seq_reg) && !status_timeout_reg) begin
            clamp_needed_next = 1'b0;
            if (rsp_cmd_in < bounds_reg[15:0]) begin
                clamp_value_next = {16'h0000, bounds_reg[15:0]};
                clamp_needed_next = 1'b1;
            end else if (rsp_cmd_in > bounds_reg[31:16]) begin
                clamp_value_next = {16'h0000, bounds_reg[31:16]};
                clamp_needed_next = 1'b1;
            end else begin
                clamp_value_next = {16'h0000, rsp_cmd_in};
            end
            state_next = STATE_IDLE;
        end else begin
            state_next = STATE_FAULT;
        end
    end

    if (clear_fault_pulse) begin
    end

    if (rearm_pulse && ctrl_reg[0] && !status_fault_active_reg) begin
        state_next = STATE_IDLE;
    end

    if (req_hist_write_pulse) begin
    end
    if (req_hist_read_pulse) begin
    end

    if (status_fault_active_reg) begin
        if (hold_safe_sel_reg) begin
        end else begin
        end
    end


    if (state_reg == STATE_IDLE) begin
    end else if (state_reg == STATE_ISSUE_REQ) begin
    end else if (state_reg == STATE_WAIT_RSP) begin
    end else begin
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        ctrl_reg <= 8'h00;
        mode_seq_reg <= 64'h0000000000000000;
        limits_reg <= 64'h0000000000000000;
        bounds_reg <= 64'h0000000000000000;
        irq_en_reg <= 64'h0000000000000000;
        req_meta_reg <= 64'h0000000000000000;
        accepted_count_reg <= 16'h0000;
        rejected_count_reg <= 16'h0000;
        outstanding_seq_reg <= 16'h0000;
        outstanding_age_reg <= 16'h0000;
        outstanding_valid_reg <= 1'b0;
        status_req_accepted_reg <= 1'b0;
        status_rsp_received_reg <= 1'b0;
        status_rsp_validated_reg <= 1'b0;
        status_clamp_applied_reg <= 1'b0;
        status_stale_reject_reg <= 1'b0;
        status_timeout_reg <= 1'b0;
        status_fallback_active_reg <= 1'b0;
        status_fault_active_reg <= 1'b0;
        busy_reg <= 1'b0;
        req_valid_r <= 1'b0;
        req_data_r <= 64'h0000000000000000;
        rsp_ready_r <= 1'b1;
        act_cmd_valid_r <= 1'b0;
        act_cmd_fault_r <= 1'b0;
        act_cmd_data_r <= 32'h00000000;
        irq_r <= 1'b0;
        req_hist_csb <= 1'b1;
        req_hist_web <= 1'b1;
        req_hist_addr <= 4'h0;
        req_hist_din <= 64'h0000000000000000;
        state_reg <= STATE_IDLE;
        pending_launch_reg <= 1'b0;
        pending_clear_fault_reg <= 1'b0;
        pending_rearm_reg <= 1'b0;
        hold_safe_sel_reg <= 1'b0;
        req_hist_write_pending_reg <= 1'b0;
        req_hist_read_pending_reg <= 1'b0;
        fault_latched_reg <= 1'b0;
    end else begin
        state_reg <= state_next;
        ctrl_reg[0] <= ctrl_reg[0];
        ctrl_reg[4] <= ctrl_reg[4];
        hold_safe_sel_reg <= ctrl_reg[4];
        if (mmio_we && (mmio_addr == 4'h0)) begin
            ctrl_reg[0] <= mmio_wdata[0];
            ctrl_reg[4] <= mmio_wdata[4];
        end
        if (mmio_we && (mmio_addr == 4'h1)) mode_seq_reg <= mmio_wdata;
        if (mmio_we && (mmio_addr == 4'h2)) limits_reg <= mmio_wdata;
        if (mmio_we && (mmio_addr == 4'h3)) bounds_reg <= mmio_wdata;
        if (mmio_we && (mmio_addr == 4'h5)) irq_en_reg <= mmio_wdata;
        if (mmio_we && (mmio_addr == 4'h6)) req_meta_reg <= mmio_wdata;
        if (mmio_we && (mmio_addr == 4'h7)) begin
            req_hist_addr <= mmio_wdata[3:0];
            req_hist_write_pending_reg <= mmio_wdata[4];
            req_hist_read_pending_reg <= mmio_wdata[5];
        end
        if (launch_accept_pulse && ctrl_reg[0] && !outstanding_valid_reg && !status_fault_active_reg) begin
            outstanding_valid_reg <= 1'b1;
            outstanding_seq_reg <= mode_seq_reg[23:8];
            outstanding_age_reg <= 16'h0000;
            status_req_accepted_reg <= 1'b1;
        end else begin
            status_req_accepted_reg <= 1'b0;
        end
        if (outstanding_valid_reg) begin
            if (outstanding_age_reg != 16'hFFFF) outstanding_age_reg <= outstanding_age_reg + 16'h0001;
        end
        if (rsp_valid && outstanding_valid_reg) begin
            status_rsp_received_reg <= 1'b1;
        end else begin
            status_rsp_received_reg <= 1'b0;
        end
        if (clear_fault_pulse) begin
            status_timeout_reg <= 1'b0;
            status_stale_reject_reg <= 1'b0;
            status_fault_active_reg <= 1'b0;
            status_fallback_active_reg <= 1'b0;
        end
        if (rearm_pulse && ctrl_reg[0] && !status_fault_active_reg) begin
            fault_latched_reg <= 1'b0;
        end
        if (status_fault_active_reg) fault_latched_reg <= 1'b1;
        if (req_hist_write_pending_reg) begin
            req_hist_csb <= 1'b0;
            req_hist_web <= 1'b0;
            req_hist_din <= req_data_r;
            req_hist_write_pending_reg <= 1'b0;
        end else if (req_hist_read_pending_reg) begin
            req_hist_csb <= 1'b0;
            req_hist_web <= 1'b1;
            req_hist_read_pending_reg <= 1'b0;
        end else begin
            req_hist_csb <= 1'b1;
            req_hist_web <= 1'b1;
        end
        if (status_fault_active_reg) begin
            act_cmd_valid_r <= 1'b1;
            act_cmd_fault_r <= 1'b1;
            if (hold_safe_sel_reg) act_cmd_data_r <= 32'h00000000;
            else act_cmd_data_r <= bounds_reg[47:16];
        end else if (state_reg == STATE_IDLE) begin
            act_cmd_valid_r <= 1'b0;
            act_cmd_fault_r <= 1'b0;
        end
        irq_r <= irq_r | ((irq_en_reg[0] & status_req_accepted_reg) |
                         (irq_en_reg[1] & status_rsp_validated_reg) |
                         (irq_en_reg[2] & status_clamp_applied_reg) |
                         (irq_en_reg[3] & status_stale_reject_reg) |
                         (irq_en_reg[4] & status_timeout_reg) |
                         (irq_en_reg[5] & status_fault_active_reg) |
                         (irq_en_reg[6] & status_rsp_received_reg));
    end
end

endmodule
