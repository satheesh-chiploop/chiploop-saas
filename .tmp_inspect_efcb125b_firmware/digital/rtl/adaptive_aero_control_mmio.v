module adaptive_aero_control_mmio (
    input             clk,
    input             reset_n,
    input      [31:0] wb_adr_i,
    input      [31:0] wb_dat_i,
    output reg [31:0] wb_dat_o,
    input      [3:0] wb_sel_i,
    input             wb_cyc_i,
    input             wb_stb_i,
    input             wb_we_i,
    output reg        wb_ack_o,
    output reg        wb_err_o,
    output reg        wb_rty_o,
    output reg [1:0] cfg_mode,
    output reg        cfg_cmd_valid,
    output reg [15:0] cfg_velocity_q8_8,
    output reg [15:0] cfg_geometry_handle,
    output reg [15:0] cfg_request_seq,
    output reg [15:0] cfg_timeout_threshold,
    output reg [15:0] cfg_actuator_min,
    output reg [15:0] cfg_actuator_max,
    output reg [15:0] cfg_actuator_slew,
    output reg [15:0] cfg_velocity_low_limit,
    output reg [15:0] cfg_velocity_high_limit,
    output reg [15:0] cfg_safe_state_cmd,
    output reg        cfg_hold_last_safe,
    output reg [7:0] cfg_irq_enable,
    output reg        cfg_fault_clear,
    output reg        cfg_irq_ack,
    input             status_outstanding_req,
    input      [15:0] status_last_accepted_seq,
    input      [15:0] status_response_seq,
    input      [15:0] status_timeout_count,
    input      [15:0] status_stale_reject_count,
    input      [15:0] status_invalid_env_count,
    input      [7:0] status_fault_code,
    input             status_safe_state,
    input             status_fault_latched,
    input      [7:0] status_irq_sticky,
    input      [15:0] status_actuator_cmd,
    input             status_actuator_valid,
    input      [15:0] status_age_counter,
    input      [63:0] status_last_req_word,
    input      [63:0] status_last_resp_word
);
    reg [31:0] rd_data;
    reg [3:0]  sel_mask;
    wire       bus_fire;
    wire       bus_write;
    wire       bus_read;
    wire [7:0] addr_word;

    assign bus_fire  = wb_cyc_i & wb_stb_i;
    assign bus_write = bus_fire & wb_we_i;
    assign bus_read  = bus_fire & ~wb_we_i;
    assign addr_word = wb_adr_i[7:0];

    always @(*) begin
        wb_dat_o = rd_data;
    end

    always @(*) begin
        sel_mask = wb_sel_i;
    end

    always @(posedge clk) begin
        if (!reset_n) begin
            cfg_mode <= 2'b00;
            cfg_cmd_valid <= 1'b0;
            cfg_velocity_q8_8 <= 16'd9941;
            cfg_geometry_handle <= 16'd0;
            cfg_request_seq <= 16'd0;
            cfg_timeout_threshold <= 16'd0;
            cfg_actuator_min <= 16'd0;
            cfg_actuator_max <= 16'd4095;
            cfg_actuator_slew <= 16'd16;
            cfg_velocity_low_limit <= 16'd5;
            cfg_velocity_high_limit <= 16'd45;
            cfg_safe_state_cmd <= 16'd0;
            cfg_hold_last_safe <= 1'b0;
            cfg_irq_enable <= 8'hff;
            cfg_fault_clear <= 1'b0;
            cfg_irq_ack <= 1'b0;
            wb_ack_o <= 1'b0;
            wb_err_o <= 1'b0;
            wb_rty_o <= 1'b0;
        end else begin
            cfg_cmd_valid <= 1'b0;
            cfg_fault_clear <= 1'b0;
            cfg_irq_ack <= 1'b0;
            wb_ack_o <= 1'b0;
            wb_err_o <= 1'b0;
            wb_rty_o <= 1'b0;

            if (bus_fire) begin
                wb_ack_o <= 1'b1;
                case (addr_word)
                    8'h00: begin
                        if (bus_write) begin
                            if (sel_mask[0]) begin
                                cfg_mode <= wb_dat_i[1:0];
                                cfg_cmd_valid <= wb_dat_i[2];
                                cfg_hold_last_safe <= wb_dat_i[3];
                                cfg_fault_clear <= wb_dat_i[4];
                                cfg_irq_ack <= wb_dat_i[5];
                            end
                            if (sel_mask[1]) begin
                                cfg_irq_enable <= wb_dat_i[15:8];
                            end
                        end
                    end
                    8'h04: begin
                        if (bus_write && sel_mask[0]) begin
                            cfg_velocity_q8_8 <= wb_dat_i[15:0];
                        end
                    end
                    8'h08: begin
                        if (bus_write && sel_mask[0]) begin
                            cfg_geometry_handle <= wb_dat_i[15:0];
                        end
                    end
                    8'h0C: begin
                        if (bus_write && sel_mask[0]) begin
                            cfg_request_seq <= wb_dat_i[15:0];
                        end
                    end
                    8'h10: begin
                        if (bus_write) begin
                            if (sel_mask[0]) cfg_timeout_threshold <= wb_dat_i[15:0];
                            if (sel_mask[2]) cfg_velocity_low_limit <= wb_dat_i[23:16];
                            if (sel_mask[3]) cfg_velocity_high_limit <= wb_dat_i[31:24];
                        end
                    end
                    8'h14: begin
                        if (bus_write) begin
                            if (sel_mask[0]) cfg_actuator_min <= wb_dat_i[15:0];
                            if (sel_mask[2]) cfg_actuator_max <= wb_dat_i[31:16];
                        end
                    end
                    8'h18: begin
                        if (bus_write && sel_mask[0]) begin
                            cfg_actuator_slew <= wb_dat_i[15:0];
                        end
                    end
                    8'h1C: begin
                        if (bus_write && sel_mask[0]) begin
                            cfg_safe_state_cmd <= wb_dat_i[15:0];
                        end
                    end
                    8'h40: begin
                        if (bus_write && sel_mask[0]) begin
                            if (wb_dat_i[0]) cfg_irq_enable[0] <= 1'b0;
                            if (wb_dat_i[1]) cfg_irq_enable[1] <= 1'b0;
                            if (wb_dat_i[2]) cfg_irq_enable[2] <= 1'b0;
                            if (wb_dat_i[3]) cfg_irq_enable[3] <= 1'b0;
                            if (wb_dat_i[4]) cfg_irq_enable[4] <= 1'b0;
                        end
                    end
                    default: begin
                    end
                endcase
            end
        end
    end

    always @(*) begin
        rd_data = 32'h00000000;
        case (addr_word)
            8'h00: rd_data = {2'b0, 16'h0000, cfg_irq_enable, cfg_fault_clear, cfg_irq_ack, cfg_hold_last_safe, cfg_cmd_valid, cfg_mode};
            8'h04: rd_data = {16'h0000, cfg_velocity_q8_8};
            8'h08: rd_data = {16'h0000, cfg_geometry_handle};
            8'h0C: rd_data = {status_last_accepted_seq, cfg_request_seq};
            8'h10: rd_data = {cfg_velocity_high_limit[7:0], cfg_velocity_low_limit[7:0], cfg_timeout_threshold};
            8'h14: rd_data = {cfg_actuator_max, cfg_actuator_min};
            8'h18: rd_data = {16'h0000, cfg_actuator_slew};
            8'h1C: rd_data = {16'h0000, cfg_safe_state_cmd};
            8'h20: rd_data = {16'h0000, status_fault_code, 4'h0, status_actuator_valid, status_fault_latched, status_safe_state, status_outstanding_req};
            8'h24: rd_data = {status_stale_reject_count, status_timeout_count};
            8'h28: rd_data = {status_age_counter, status_invalid_env_count};
            8'h2C: rd_data = {status_response_seq, status_last_accepted_seq};
            8'h30: rd_data = status_last_req_word[31:0];
            8'h34: rd_data = status_last_req_word[63:32];
            8'h38: rd_data = status_last_resp_word[31:0];
            8'h3C: rd_data = status_last_resp_word[63:32];
            8'h40: rd_data = {27'h0000000, status_irq_sticky[4:0]};
            8'h44: rd_data = {22'h000000, status_safe_state, status_fault_latched, status_fault_code};
            default: rd_data = 32'h00000000;
        endcase
    end
endmodule
