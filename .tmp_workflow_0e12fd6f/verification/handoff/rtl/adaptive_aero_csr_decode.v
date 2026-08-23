module adaptive_aero_csr_decode (
    clk,
    rst_n,
    csr_addr_data,
    csr_wr_en,
    csr_wr_data,
    csr_rd_data,
    csr_rd_valid,
    cfg_enable,
    cfg_soft_clear_faults,
    cfg_force_inhibit,
    cfg_queue_depth_enable,
    cfg_response_accept_enable,
    cfg_timeout_cycles,
    cfg_max_actuator_cmd,
    cfg_min_actuator_cmd,
    cfg_rate_limit_step,
    status_busy,
    status_response_valid_seen,
    status_stale_fault,
    status_timeout_fault,
    status_protocol_fault,
    status_fallback_active,
    status_request_pending,
    status_response_accepted,
    status_timeout_count,
    status_stale_reject_count,
    status_fallback_activation_count,
    status_last_seq_accepted,
    status_last_seq_rejected
);
    input         clk;
    input         rst_n;
    input  [63:0] csr_addr_data;
    input         csr_wr_en;
    input  [63:0] csr_wr_data;
    output [63:0] csr_rd_data;
    output        csr_rd_valid;
    output        cfg_enable;
    output        cfg_soft_clear_faults;
    output        cfg_force_inhibit;
    output        cfg_queue_depth_enable;
    output        cfg_response_accept_enable;
    output [31:0] cfg_timeout_cycles;
    output [15:0] cfg_max_actuator_cmd;
    output [15:0] cfg_min_actuator_cmd;
    output [15:0] cfg_rate_limit_step;
    input         status_busy;
    input         status_response_valid_seen;
    input         status_stale_fault;
    input         status_timeout_fault;
    input         status_protocol_fault;
    input         status_fallback_active;
    input         status_request_pending;
    input         status_response_accepted;
    input  [31:0] status_timeout_count;
    input  [31:0] status_stale_reject_count;
    input  [31:0] status_fallback_activation_count;
    input  [31:0] status_last_seq_accepted;
    input  [31:0] status_last_seq_rejected;
    reg cfg_enable_r;
    reg cfg_soft_clear_faults_r;
    reg cfg_force_inhibit_r;
    reg cfg_queue_depth_enable_r;
    reg cfg_response_accept_enable_r;
    reg [31:0] cfg_timeout_cycles_r;
    reg [15:0] cfg_max_actuator_cmd_r;
    reg [15:0] cfg_min_actuator_cmd_r;
    reg [15:0] cfg_rate_limit_step_r;
    reg [63:0] csr_rd_data_r;
    reg csr_rd_valid_r;

    assign cfg_enable = cfg_enable_r;
    assign cfg_soft_clear_faults = cfg_soft_clear_faults_r;
    assign cfg_force_inhibit = cfg_force_inhibit_r;
    assign cfg_queue_depth_enable = cfg_queue_depth_enable_r;
    assign cfg_response_accept_enable = cfg_response_accept_enable_r;
    assign cfg_timeout_cycles = cfg_timeout_cycles_r;
    assign cfg_max_actuator_cmd = cfg_max_actuator_cmd_r;
    assign cfg_min_actuator_cmd = cfg_min_actuator_cmd_r;
    assign cfg_rate_limit_step = cfg_rate_limit_step_r;
    assign csr_rd_data = csr_rd_data_r;
    assign csr_rd_valid = csr_rd_valid_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cfg_enable_r <= 1'b0;
            cfg_soft_clear_faults_r <= 1'b0;
            cfg_force_inhibit_r <= 1'b1;
            cfg_queue_depth_enable_r <= 1'b0;
            cfg_response_accept_enable_r <= 1'b1;
            cfg_timeout_cycles_r <= 32'd1000;
            cfg_max_actuator_cmd_r <= 16'd32767;
            cfg_min_actuator_cmd_r <= 16'd0;
            cfg_rate_limit_step_r <= 16'd0;
        end else begin
            cfg_soft_clear_faults_r <= 1'b0;
            if (csr_wr_en) begin
                case (csr_addr_data[7:0])
                    8'h00: begin
                        cfg_enable_r <= csr_wr_data[0];
                        cfg_soft_clear_faults_r <= csr_wr_data[1];
                        cfg_force_inhibit_r <= csr_wr_data[2];
                        cfg_queue_depth_enable_r <= csr_wr_data[3];
                        cfg_response_accept_enable_r <= csr_wr_data[4];
                    end
                    8'h08: cfg_timeout_cycles_r <= csr_wr_data[31:0];
                    8'h10: cfg_max_actuator_cmd_r <= csr_wr_data[15:0];
                    8'h18: cfg_min_actuator_cmd_r <= csr_wr_data[15:0];
                    8'h20: cfg_rate_limit_step_r <= csr_wr_data[15:0];
                    default: begin
                    end
                endcase
            end
        end
    end

    always @(*) begin
        csr_rd_data_r = 64'd0;
        csr_rd_valid_r = 1'b0;
        case (csr_addr_data[7:0])
            8'h00: begin
                csr_rd_data_r = {59'd0, cfg_response_accept_enable_r, cfg_queue_depth_enable_r, cfg_force_inhibit_r, cfg_soft_clear_faults_r, cfg_enable_r};
                csr_rd_valid_r = 1'b1;
            end
            8'h08: begin
                csr_rd_data_r = {32'd0, cfg_timeout_cycles_r};
                csr_rd_valid_r = 1'b1;
            end
            8'h10: begin
                csr_rd_data_r = {48'd0, cfg_max_actuator_cmd_r};
                csr_rd_valid_r = 1'b1;
            end
            8'h18: begin
                csr_rd_data_r = {48'd0, cfg_min_actuator_cmd_r};
                csr_rd_valid_r = 1'b1;
            end
            8'h20: begin
                csr_rd_data_r = {48'd0, cfg_rate_limit_step_r};
                csr_rd_valid_r = 1'b1;
            end
            8'h28: begin
                csr_rd_data_r = {56'd0, status_response_accepted, status_request_pending, status_fallback_active, status_protocol_fault, status_timeout_fault, status_stale_fault, status_response_valid_seen, status_busy};
                csr_rd_valid_r = 1'b1;
            end
            8'h30: begin
                csr_rd_data_r = {16'd0, status_fallback_activation_count[15:0], status_stale_reject_count[15:0], status_timeout_count[15:0]};
                csr_rd_valid_r = 1'b1;
            end
            8'h38: begin
                csr_rd_data_r = {status_last_seq_rejected, status_last_seq_accepted};
                csr_rd_valid_r = 1'b1;
            end
            default: begin
                csr_rd_data_r = 64'd0;
                csr_rd_valid_r = 1'b0;
            end
        endcase
    end
endmodule
