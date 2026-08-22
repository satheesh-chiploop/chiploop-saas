module adaptive_aero_model_gateway (
    clk,
    reset_n,
    cfg_enable,
    cfg_mode,
    cfg_request_trigger,
    cfg_output_mode,
    cfg_request_flags,
    cfg_velocity_ref,
    req_valid,
    req_ready,
    req_data,
    rsp_valid,
    rsp_ready,
    rsp_data,
    pending,
    busy,
    seq_last_accepted,
    req_seq,
    rsp_seq,
    rsp_cmd,
    fault_transport,
    fault_malformed,
    fault_stale
);
    input clk;
    input reset_n;
    input cfg_enable;
    input [1:0] cfg_mode;
    input cfg_request_trigger;
    input [1:0] cfg_output_mode;
    input [7:0] cfg_request_flags;
    input [15:0] cfg_velocity_ref;
    output reg req_valid;
    input req_ready;
    output reg [63:0] req_data;
    input rsp_valid;
    output reg rsp_ready;
    input [63:0] rsp_data;
    output reg pending;
    output reg busy;
    output reg [15:0] seq_last_accepted;
    output reg [15:0] req_seq;
    output reg [15:0] rsp_seq;
    output reg [15:0] rsp_cmd;
    output reg fault_transport;
    output reg fault_malformed;
    output reg fault_stale;

    reg [15:0] pending_seq;
    reg pending_reg;
    reg [15:0] seq_next;
    reg [15:0] req_seq_next;
    reg [15:0] rsp_seq_next;
    reg [15:0] rsp_cmd_next;
    reg [15:0] seq_last_accepted_next;
    reg fault_transport_next;
    reg fault_malformed_next;
    reg fault_stale_next;
    reg req_valid_next;
    reg rsp_ready_next;
    reg [63:0] req_data_next;
    reg pending_next;
    reg busy_next;

    wire request_fire;
    wire response_fire;
    wire sequence_match;
    wire response_malformed;
    wire response_stale;
    wire response_fault;
    assign request_fire = cfg_enable & cfg_request_trigger & (~pending_reg) & req_ready;
    assign response_fire = pending_reg & rsp_valid & rsp_ready;
    assign sequence_match = (rsp_data[15:0] == pending_seq);
    assign response_stale = pending_reg & rsp_valid & (~sequence_match);
    assign response_malformed = pending_reg & rsp_valid & (rsp_data[31:16] == 16'hDEAD);
    assign response_fault = response_stale | response_malformed;

    always @(*) begin
        req_valid_next = 1'b0;
        rsp_ready_next = 1'b0;
        req_data_next = req_data;
        pending_next = pending_reg;
        busy_next = pending_reg;
        seq_next = req_seq;
        req_seq_next = req_seq;
        rsp_seq_next = rsp_seq;
        rsp_cmd_next = rsp_cmd;
        seq_last_accepted_next = seq_last_accepted;
        fault_transport_next = 1'b0;
        fault_malformed_next = 1'b0;
        fault_stale_next = 1'b0;

        if (cfg_enable && (~pending_reg) && cfg_request_trigger) begin
            req_data_next = {16'hA55A, cfg_output_mode, cfg_request_flags, cfg_mode, cfg_velocity_ref, req_seq + 16'h0001, 8'h00};
            if (req_ready) begin
                req_valid_next = 1'b1;
                req_seq_next = req_seq + 16'h0001;
                pending_next = 1'b1;
                busy_next = 1'b1;
            end else begin
                req_valid_next = 1'b1;
            end
        end else if (pending_reg) begin
            req_data_next = {16'hA55A, cfg_output_mode, cfg_request_flags, cfg_mode, cfg_velocity_ref, req_seq, 4'b0};
        end

        rsp_ready_next = pending_reg & cfg_enable;

        if (response_fire) begin
            rsp_seq_next = rsp_data[15:0];
            rsp_cmd_next = rsp_data[31:16];
            if (sequence_match) begin
                seq_last_accepted_next = rsp_data[15:0];
                pending_next = 1'b0;
                busy_next = 1'b0;
            end else begin
                fault_transport_next = 1'b1;
                fault_stale_next = 1'b1;
            end
            if (response_malformed) begin
                fault_malformed_next = 1'b1;
            end
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            req_valid <= 1'b0;
            req_data <= 64'h0000000000000000;
            rsp_ready <= 1'b0;
            pending <= 1'b0;
            busy <= 1'b0;
            seq_last_accepted <= 16'h0000;
            req_seq <= 16'h0000;
            rsp_seq <= 16'h0000;
            rsp_cmd <= 16'h0000;
            fault_transport <= 1'b0;
            fault_malformed <= 1'b0;
            fault_stale <= 1'b0;
            pending_reg <= 1'b0;
            pending_seq <= 16'h0000;
        end else begin
            req_valid <= req_valid_next;
            req_data <= req_data_next;
            rsp_ready <= rsp_ready_next;
            pending <= pending_next;
            busy <= busy_next;
            seq_last_accepted <= seq_last_accepted_next;
            req_seq <= req_seq_next;
            rsp_seq <= rsp_seq_next;
            rsp_cmd <= rsp_cmd_next;
            fault_transport <= fault_transport_next;
            fault_malformed <= fault_malformed_next;
            fault_stale <= fault_stale_next;
            pending_reg <= pending_next;
            if (cfg_enable && (~pending_reg) && cfg_request_trigger && req_ready) begin
                pending_seq <= req_seq + 16'h0001;
            end
        end
    end
endmodule
