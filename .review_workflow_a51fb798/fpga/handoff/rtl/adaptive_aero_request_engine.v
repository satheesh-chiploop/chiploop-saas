module adaptive_aero_request_engine (
    clk,
    reset_n,
    cfg_enable,
    cfg_arm_request,
    cfg_clear_fault,
    cfg_operating_velocity_mps,
    cfg_timeout_cycles,
    cfg_max_outstanding,
    cfg_mode_status,
    cfg_request_seq,
    host_req_stream_ready,
    req_launch_pulse,
    req_seq_out,
    req_packet_128,
    req_fifo_push,
    req_fifo_pop,
    req_fifo_full,
    req_fifo_empty,
    reg_request_pending,
    last_request_id,
    fault_queue_full_sticky,
    fault_host_not_ready_sticky
);
    input clk;
    input reset_n;
    input cfg_enable;
    input cfg_arm_request;
    input cfg_clear_fault;
    input [15:0] cfg_operating_velocity_mps;
    input [23:0] cfg_timeout_cycles;
    input [3:0] cfg_max_outstanding;
    input [7:0] cfg_mode_status;
    input [15:0] cfg_request_seq;
    input host_req_stream_ready;
    output reg req_launch_pulse;
    output reg [15:0] req_seq_out;
    output reg [127:0] req_packet_128;
    output reg req_fifo_push;
    input req_fifo_pop;
    input req_fifo_full;
    input req_fifo_empty;
    output reg reg_request_pending;
    output reg [15:0] last_request_id;
    output reg fault_queue_full_sticky;
    output reg fault_host_not_ready_sticky;

    reg [3:0] outstanding_count;
    reg [15:0] seq_reg;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            req_launch_pulse <= 1'b0;
            req_seq_out <= 16'h0000;
            req_packet_128 <= 128'h0;
            req_fifo_push <= 1'b0;
            reg_request_pending <= 1'b0;
            last_request_id <= 16'h0000;
            fault_queue_full_sticky <= 1'b0;
            fault_host_not_ready_sticky <= 1'b0;
            outstanding_count <= 4'h0;
            seq_reg <= 16'h0000;
        end else begin
            req_launch_pulse <= 1'b0;
            req_fifo_push <= 1'b0;
            if (cfg_clear_fault) begin
                fault_queue_full_sticky <= 1'b0;
                fault_host_not_ready_sticky <= 1'b0;
            end
            if (req_fifo_pop && outstanding_count != 4'h0) begin
                outstanding_count <= outstanding_count - 4'h1;
            end
            if (cfg_enable && cfg_arm_request && !req_fifo_full) begin
                if (host_req_stream_ready) begin
                    req_launch_pulse <= 1'b1;
                    req_fifo_push <= 1'b1;
                    req_seq_out <= seq_reg;
                    req_packet_128 <= {64'h0000000000000000, cfg_mode_status, cfg_operating_velocity_mps, cfg_timeout_cycles[15:0], seq_reg, 8'b0};
                    last_request_id <= seq_reg;
                    seq_reg <= seq_reg + 16'h0001;
                    reg_request_pending <= 1'b1;
                    if (outstanding_count != cfg_max_outstanding) begin
                        outstanding_count <= outstanding_count + 4'h1;
                    end
                end else begin
                    fault_host_not_ready_sticky <= 1'b1;
                end
            end
            if (req_fifo_full) begin
                fault_queue_full_sticky <= 1'b1;
            end
            if (outstanding_count == 4'h0) begin
                reg_request_pending <= 1'b0;
            end
        end
    end
endmodule
