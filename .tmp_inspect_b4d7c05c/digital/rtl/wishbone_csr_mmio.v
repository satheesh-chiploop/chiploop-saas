module wishbone_csr_mmio (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_sel_i,
    wb_ack_o,
    wb_err_o,
    start_request,
    clear_faults,
    safe_mode_select,
    request_seq,
    stream_velocity,
    geometry_id,
    flow_condition_sel,
    control_mode,
    timeout_cycles,
    freshness_cycles,
    actuator_min,
    actuator_max,
    rate_limit,
    config_valid,
    busy,
    response_valid,
    timeout_fault,
    stale_fault,
    response_seq_mismatch,
    invalid_payload_fault,
    fallback_active,
    last_good_command,
    current_sequence,
    fault_pending,
    interrupt_o
);
    input clk;
    input reset_n;
    input [31:0] wb_adr_i;
    input [31:0] wb_dat_i;
    output [31:0] wb_dat_o;
    input wb_cyc_i;
    input wb_stb_i;
    input wb_we_i;
    input [3:0] wb_sel_i;
    output wb_ack_o;
    output wb_err_o;
    output start_request;
    output clear_faults;
    output safe_mode_select;
    output [15:0] request_seq;
    output [31:0] stream_velocity;
    output [15:0] geometry_id;
    output [3:0] flow_condition_sel;
    output [3:0] control_mode;
    output [31:0] timeout_cycles;
    output [31:0] freshness_cycles;
    output [31:0] actuator_min;
    output [31:0] actuator_max;
    output [31:0] rate_limit;
    output config_valid;
    input busy;
    input response_valid;
    input timeout_fault;
    input stale_fault;
    input response_seq_mismatch;
    input invalid_payload_fault;
    input fallback_active;
    input [31:0] last_good_command;
    input [15:0] current_sequence;
    input fault_pending;
    output interrupt_o;

    reg [15:0] request_seq_r;
    reg [31:0] stream_velocity_r;
    reg [15:0] geometry_id_r;
    reg [3:0] flow_condition_sel_r;
    reg [3:0] control_mode_r;
    reg [31:0] timeout_cycles_r;
    reg [31:0] freshness_cycles_r;
    reg [31:0] actuator_min_r;
    reg [31:0] actuator_max_r;
    reg [31:0] rate_limit_r;
    reg config_valid_r;
    reg safe_mode_select_r;

    reg start_request_r;
    reg clear_faults_r;

    reg [31:0] wb_dat_o_r;
    reg wb_ack_o_r;
    reg wb_err_o_r;
    reg interrupt_o_r;

    wire wb_access;
    assign wb_access = wb_cyc_i & wb_stb_i;

    assign request_seq = request_seq_r;
    assign stream_velocity = stream_velocity_r;
    assign geometry_id = geometry_id_r;
    assign flow_condition_sel = flow_condition_sel_r;
    assign control_mode = control_mode_r;
    assign timeout_cycles = timeout_cycles_r;
    assign freshness_cycles = freshness_cycles_r;
    assign actuator_min = actuator_min_r;
    assign actuator_max = actuator_max_r;
    assign rate_limit = rate_limit_r;
    assign config_valid = config_valid_r;
    assign safe_mode_select = safe_mode_select_r;
    assign start_request = start_request_r;
    assign clear_faults = clear_faults_r;
    assign wb_dat_o = wb_dat_o_r;
    assign wb_ack_o = wb_ack_o_r;
    assign wb_err_o = wb_err_o_r;
    assign interrupt_o = interrupt_o_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            request_seq_r <= 16'h0000;
            stream_velocity_r <= 32'h00000000;
            geometry_id_r <= 16'h0000;
            flow_condition_sel_r <= 4'h0;
            control_mode_r <= 4'h0;
            timeout_cycles_r <= 32'd500000;
            freshness_cycles_r <= 32'd500000;
            actuator_min_r <= 32'h00000000;
            actuator_max_r <= 32'h0000ffff;
            rate_limit_r <= 32'h00000000;
            config_valid_r <= 1'b0;
            safe_mode_select_r <= 1'b0;
            start_request_r <= 1'b0;
            clear_faults_r <= 1'b0;
            wb_dat_o_r <= 32'h00000000;
            wb_ack_o_r <= 1'b0;
            wb_err_o_r <= 1'b0;
            interrupt_o_r <= 1'b0;
        end else begin
            start_request_r <= 1'b0;
            clear_faults_r <= 1'b0;
            wb_ack_o_r <= 1'b0;
            wb_err_o_r <= 1'b0;
            interrupt_o_r <= fault_pending | response_valid;

            if (wb_access) begin
                wb_ack_o_r <= 1'b1;
                case (wb_adr_i[7:0])
                    8'h00: begin
                        if (wb_we_i) begin
                            if (wb_sel_i[0]) begin
                                start_request_r <= wb_dat_i[0];
                                clear_faults_r <= wb_dat_i[1];
                                safe_mode_select_r <= wb_dat_i[2];
                                config_valid_r <= wb_dat_i[3];
                            end
                        end
                        wb_dat_o_r <= {28'h0000000, config_valid_r, safe_mode_select_r, clear_faults_r, start_request_r};
                    end
                    8'h04: begin
                        if (wb_we_i) begin
                            if (wb_sel_i[0]) begin
                                request_seq_r <= wb_dat_i[15:0];
                            end
                            if (wb_sel_i[2]) begin
                                flow_condition_sel_r <= wb_dat_i[19:16];
                                control_mode_r <= wb_dat_i[23:20];
                            end
                        end
                        wb_dat_o_r <= {8'h00, control_mode_r, flow_condition_sel_r, request_seq_r};
                    end
                    8'h08: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            stream_velocity_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= stream_velocity_r;
                    end
                    8'h0C: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            geometry_id_r <= wb_dat_i[15:0];
                        end
                        wb_dat_o_r <= {16'h0000, geometry_id_r};
                    end
                    8'h10: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            timeout_cycles_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= timeout_cycles_r;
                    end
                    8'h14: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            freshness_cycles_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= freshness_cycles_r;
                    end
                    8'h18: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            actuator_min_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= actuator_min_r;
                    end
                    8'h1C: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            actuator_max_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= actuator_max_r;
                    end
                    8'h20: begin
                        if (wb_we_i && wb_sel_i[0]) begin
                            rate_limit_r <= wb_dat_i;
                        end
                        wb_dat_o_r <= rate_limit_r;
                    end
                    8'h24: begin
                        wb_dat_o_r <= {24'h000000, fault_pending, fallback_active, invalid_payload_fault, response_seq_mismatch, stale_fault, timeout_fault, response_valid, busy};
                    end
                    8'h28: begin
                        wb_dat_o_r <= {16'h0000, last_good_command[31:16]};
                        wb_dat_o_r[15:0] <= current_sequence;
                    end
                    8'h2C: begin
                        wb_dat_o_r <= last_good_command;
                    end
                    default: begin
                        wb_err_o_r <= 1'b1;
                        wb_dat_o_r <= 32'h00000000;
                    end
                endcase
            end else begin
                wb_dat_o_r <= wb_dat_o_r;
            end
        end
    end

endmodule
