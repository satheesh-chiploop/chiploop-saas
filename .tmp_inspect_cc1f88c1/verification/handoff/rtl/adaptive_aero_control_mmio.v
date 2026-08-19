module adaptive_aero_control_mmio (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_we_i,
    wb_cyc_i,
    wb_stb_i,
    wb_ack_o,
    wb_stall_o,
    wb_err_o,
    wb_sel_i,
    wb_cti_i,
    wb_bte_i,
    cfg_global_enable,
    cfg_release_enable,
    cfg_clear_faults,
    cfg_request_launch,
    cfg_mode_sel,
    cfg_timeout_threshold,
    cfg_stale_age_threshold,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_actuator_rate_limit,
    cfg_request_payload,
    cfg_interrupt_ack,
    status_busy,
    status_response_ready,
    status_stale_rejected,
    status_timeout_fault,
    status_invalid_response,
    status_clamp_applied,
    status_fallback_active,
    status_sequence_mismatch,
    current_sequence_id,
    last_accepted_command,
    last_response_summary,
    sticky_faults,
    irq_pending
);
    input clk;
    input reset_n;
    input [31:0] wb_adr_i;
    input [31:0] wb_dat_i;
    output [31:0] wb_dat_o;
    input wb_we_i;
    input wb_cyc_i;
    input wb_stb_i;
    output wb_ack_o;
    output wb_stall_o;
    output wb_err_o;
    input [3:0] wb_sel_i;
    input [2:0] wb_cti_i;
    input [1:0] wb_bte_i;
    output cfg_global_enable;
    output cfg_release_enable;
    output cfg_clear_faults;
    output cfg_request_launch;
    output [1:0] cfg_mode_sel;
    output [15:0] cfg_timeout_threshold;
    output [15:0] cfg_stale_age_threshold;
    output [15:0] cfg_actuator_min_limit;
    output [15:0] cfg_actuator_max_limit;
    output [15:0] cfg_actuator_rate_limit;
    output [31:0] cfg_request_payload;
    output cfg_interrupt_ack;
    input status_busy;
    input status_response_ready;
    input status_stale_rejected;
    input status_timeout_fault;
    input status_invalid_response;
    input status_clamp_applied;
    input status_fallback_active;
    input status_sequence_mismatch;
    input [15:0] current_sequence_id;
    input [31:0] last_accepted_command;
    input [63:0] last_response_summary;
    input [15:0] sticky_faults;
    input irq_pending;

    reg cfg_global_enable_r;
    reg cfg_release_enable_r;
    reg cfg_clear_faults_r;
    reg cfg_request_launch_r;
    reg [1:0] cfg_mode_sel_r;
    reg [15:0] cfg_timeout_threshold_r;
    reg [15:0] cfg_stale_age_threshold_r;
    reg [15:0] cfg_actuator_min_limit_r;
    reg [15:0] cfg_actuator_max_limit_r;
    reg [15:0] cfg_actuator_rate_limit_r;
    reg [31:0] cfg_request_payload_r;
    reg cfg_interrupt_ack_r;
    reg [31:0] wb_dat_o_r;
    reg wb_ack_o_r;
    reg wb_err_o_r;
    reg [31:0] wb_addr_word;
    reg [31:0] rd_data;
    reg wb_access;
    reg wb_write;
    reg wb_read;
    reg [31:0] control_reg;
    reg [31:0] timeout_reg;
    reg [31:0] stale_reg;
    reg [31:0] amin_reg;
    reg [31:0] amax_reg;
    reg [31:0] arate_reg;
    reg [31:0] request_reg;
    reg [31:0] fault_clear_reg;

    assign cfg_global_enable = cfg_global_enable_r;
    assign cfg_release_enable = cfg_release_enable_r;
    assign cfg_clear_faults = cfg_clear_faults_r;
    assign cfg_request_launch = cfg_request_launch_r;
    assign cfg_mode_sel = cfg_mode_sel_r;
    assign cfg_timeout_threshold = cfg_timeout_threshold_r;
    assign cfg_stale_age_threshold = cfg_stale_age_threshold_r;
    assign cfg_actuator_min_limit = cfg_actuator_min_limit_r;
    assign cfg_actuator_max_limit = cfg_actuator_max_limit_r;
    assign cfg_actuator_rate_limit = cfg_actuator_rate_limit_r;
    assign cfg_request_payload = cfg_request_payload_r;
    assign cfg_interrupt_ack = cfg_interrupt_ack_r;
    assign wb_dat_o = wb_dat_o_r;
    assign wb_ack_o = wb_ack_o_r;
    assign wb_err_o = wb_err_o_r;
    assign wb_stall_o = 1'b0;

    always @(*) begin
        wb_addr_word = wb_adr_i[31:0];
        wb_access = wb_cyc_i & wb_stb_i;
        wb_write = wb_access & wb_we_i;
        wb_read = wb_access & ~wb_we_i;
        control_reg = 32'h00000000;
        timeout_reg = 32'h00000000;
        stale_reg = 32'h00000000;
        amin_reg = 32'h00000000;
        amax_reg = 32'h00000000;
        arate_reg = 32'h00000000;
        request_reg = 32'h00000000;
        fault_clear_reg = 32'h00000000;
        control_reg[0] = cfg_global_enable_r;
        control_reg[1] = cfg_release_enable_r;
        control_reg[4 +: 2] = cfg_mode_sel_r;
        timeout_reg[15:0] = cfg_timeout_threshold_r;
        stale_reg[15:0] = cfg_stale_age_threshold_r;
        amin_reg[15:0] = cfg_actuator_min_limit_r;
        amax_reg[15:0] = cfg_actuator_max_limit_r;
        arate_reg[15:0] = cfg_actuator_rate_limit_r;
        request_reg[31:1] = cfg_request_payload_r[30:0];
        fault_clear_reg[0] = 1'b0;
        rd_data = 32'h00000000;
        case (wb_addr_word[9:2])
            8'h00: rd_data = control_reg;
            8'h01: rd_data = {24'h000000, status_sequence_mismatch, status_fallback_active, status_clamp_applied, status_invalid_response, status_timeout_fault, status_stale_rejected, status_response_ready, status_busy};
            8'h02: rd_data = {16'h0000, current_sequence_id};
            8'h03: rd_data = timeout_reg;
            8'h04: rd_data = stale_reg;
            8'h05: rd_data = amin_reg;
            8'h06: rd_data = amax_reg;
            8'h07: rd_data = arate_reg;
            8'h08: rd_data = request_reg;
            8'h09: rd_data = last_response_summary[31:0];
            8'h0A: rd_data = last_response_summary[63:32];
            8'h0B: rd_data = last_accepted_command;
            8'h0C: rd_data = {16'h0000, sticky_faults};
            8'h0D: rd_data = fault_clear_reg;
            default: rd_data = 32'h00000000;
        endcase
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            cfg_global_enable_r <= 1'b0;
            cfg_release_enable_r <= 1'b0;
            cfg_clear_faults_r <= 1'b0;
            cfg_request_launch_r <= 1'b0;
            cfg_mode_sel_r <= 2'b00;
            cfg_timeout_threshold_r <= 16'h0000;
            cfg_stale_age_threshold_r <= 16'h0000;
            cfg_actuator_min_limit_r <= 16'h0000;
            cfg_actuator_max_limit_r <= 16'h0000;
            cfg_actuator_rate_limit_r <= 16'h0000;
            cfg_request_payload_r <= 32'h00000000;
            cfg_interrupt_ack_r <= 1'b0;
            wb_dat_o_r <= 32'h00000000;
            wb_ack_o_r <= 1'b0;
            wb_err_o_r <= 1'b0;
        end else begin
            cfg_clear_faults_r <= 1'b0;
            cfg_request_launch_r <= 1'b0;
            cfg_interrupt_ack_r <= 1'b0;
            wb_ack_o_r <= wb_access;
            wb_err_o_r <= wb_access & (wb_addr_word[9:2] > 8'h0D);
            wb_dat_o_r <= rd_data;
            if (wb_write) begin
                case (wb_addr_word[9:2])
                    8'h00: begin
                        if (wb_sel_i[0]) begin
                            cfg_global_enable_r <= wb_dat_i[0];
                            cfg_release_enable_r <= wb_dat_i[1];
                            cfg_mode_sel_r <= wb_dat_i[5:4];
                        end
                    end
                    8'h03: begin
                        if (wb_sel_i[0]) cfg_timeout_threshold_r <= wb_dat_i[15:0];
                    end
                    8'h04: begin
                        if (wb_sel_i[0]) cfg_stale_age_threshold_r <= wb_dat_i[15:0];
                    end
                    8'h05: begin
                        if (wb_sel_i[0]) cfg_actuator_min_limit_r <= wb_dat_i[15:0];
                    end
                    8'h06: begin
                        if (wb_sel_i[0]) cfg_actuator_max_limit_r <= wb_dat_i[15:0];
                    end
                    8'h07: begin
                        if (wb_sel_i[0]) cfg_actuator_rate_limit_r <= wb_dat_i[15:0];
                    end
                    8'h08: begin
                        if (wb_sel_i[0]) begin
                            cfg_request_payload_r <= wb_dat_i;
                            cfg_request_launch_r <= wb_dat_i[0];
                        end
                    end
                    8'h0D: begin
                        if (wb_sel_i[0] && wb_dat_i[0]) cfg_clear_faults_r <= 1'b1;
                    end
                    default: begin
                    end
                endcase
                if (wb_addr_word[9:2] == 8'h00 && wb_sel_i[0] && wb_dat_i[6]) cfg_interrupt_ack_r <= 1'b1;
            end
        end
    end
endmodule
