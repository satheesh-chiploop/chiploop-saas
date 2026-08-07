module transport_dispatch_fsm (
    input clk_rst_n,
    input accepted_i,
    input rejected_i,
    input stale_i,
    input [15:0] request_id_i,
    input [7:0] service_selector_i,
    input [15:0] geometry_handle_i,
    input [7:0] velocity_i,
    input [7:0] flags_i,
    input service_busy_i,
    input service_done_i,
    input service_error_i,
    input [15:0] timeout_limit_i,
    input fifo_enable_i,
    output reg dispatch_req_o,
    output reg [15:0] dispatch_request_id_o,
    output reg [7:0] dispatch_service_selector_o,
    output reg [15:0] dispatch_geometry_handle_o,
    output reg [7:0] dispatch_velocity_o,
    output reg [7:0] dispatch_flags_o,
    output reg timeout_active_o,
    output reg timeout_expired_o,
    output reg [15:0] latest_request_id_o,
    output reg busy_o,
    output reg error_o
);
    localparam [2:0] IDLE = 3'd0;
    localparam [2:0] DISPATCH = 3'd1;
    localparam [2:0] WAIT_RESP = 3'd2;
    localparam [2:0] FALLBACK = 3'd3;
    localparam [2:0] ERROR_HOLD = 3'd4;

    reg [2:0] state_r, state_n;
    reg [15:0] timeout_cnt_r, timeout_cnt_n;

    always @(posedge clk_rst_n or negedge clk_rst_n) begin
        if (!clk_rst_n) begin
            state_r <= IDLE;
            timeout_cnt_r <= 16'h0000;
            dispatch_req_o <= 1'b0;
            dispatch_request_id_o <= 16'h0000;
            dispatch_service_selector_o <= 8'h00;
            dispatch_geometry_handle_o <= 16'h0000;
            dispatch_velocity_o <= 8'h00;
            dispatch_flags_o <= 8'h00;
            timeout_active_o <= 1'b0;
            timeout_expired_o <= 1'b0;
            latest_request_id_o <= 16'h0000;
            busy_o <= 1'b0;
            error_o <= 1'b0;
        end else begin
            state_r <= state_n;
            timeout_cnt_r <= timeout_cnt_n;
            dispatch_req_o <= 1'b0;
            timeout_expired_o <= 1'b0;
            case (state_r)
                IDLE: begin
                    busy_o <= 1'b0;
                    timeout_active_o <= 1'b0;
                    error_o <= 1'b0;
                    if (accepted_i) begin
                        dispatch_req_o <= 1'b1;
                        dispatch_request_id_o <= request_id_i;
                        dispatch_service_selector_o <= service_selector_i;
                        dispatch_geometry_handle_o <= geometry_handle_i;
                        dispatch_velocity_o <= velocity_i;
                        dispatch_flags_o <= flags_i;
                        latest_request_id_o <= request_id_i;
                        busy_o <= 1'b1;
                        timeout_active_o <= 1'b1;
                    end else if (rejected_i || stale_i) begin
                        error_o <= 1'b0;
                    end
                end
                DISPATCH: begin
                    busy_o <= 1'b1;
                    timeout_active_o <= 1'b1;
                end
                WAIT_RESP: begin
                    busy_o <= 1'b1;
                    timeout_active_o <= 1'b1;
                    if (service_error_i) begin
                        error_o <= 1'b1;
                    end
                    if (service_done_i) begin
                        busy_o <= 1'b0;
                        timeout_active_o <= 1'b0;
                    end
                    if (timeout_cnt_r >= timeout_limit_i) begin
                        timeout_expired_o <= 1'b1;
                        busy_o <= 1'b0;
                        timeout_active_o <= 1'b0;
                    end
                end
                FALLBACK: begin
                    busy_o <= 1'b0;
                    timeout_active_o <= 1'b0;
                end
                ERROR_HOLD: begin
                    busy_o <= 1'b0;
                    timeout_active_o <= 1'b0;
                    error_o <= 1'b1;
                end
                default: begin
                    busy_o <= 1'b0;
                    timeout_active_o <= 1'b0;
                    error_o <= 1'b0;
                end
            endcase
            if (state_r == WAIT_RESP && busy_o) begin
                timeout_cnt_r <= timeout_cnt_r + 16'h0001;
            end else begin
                timeout_cnt_r <= 16'h0000;
            end
            if (service_error_i)
                state_r <= ERROR_HOLD;
        end
    end

    always @(*) begin
        state_n = state_r;
        timeout_cnt_n = timeout_cnt_r;
        case (state_r)
            IDLE: begin
                if (accepted_i) begin
                    state_n = DISPATCH;
                    timeout_cnt_n = 16'h0000;
                end
            end
            DISPATCH: begin
                state_n = WAIT_RESP;
                timeout_cnt_n = 16'h0000;
            end
            WAIT_RESP: begin
                if (service_error_i) begin
                    state_n = ERROR_HOLD;
                end else if (service_done_i) begin
                    state_n = IDLE;
                end else if (timeout_cnt_r >= timeout_limit_i) begin
                    state_n = FALLBACK;
                end
            end
            FALLBACK: begin
                state_n = IDLE;
            end
            ERROR_HOLD: begin
                state_n = IDLE;
            end
            default: begin
                state_n = IDLE;
            end
        endcase
    end
endmodule
