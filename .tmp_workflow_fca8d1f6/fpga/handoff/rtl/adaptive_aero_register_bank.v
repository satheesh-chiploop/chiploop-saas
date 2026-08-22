module adaptive_aero_register_bank (
    clk,
    reset_n,
    reg_cs_n,
    reg_valid,
    reg_we,
    reg_re,
    reg_addr,
    reg_wdata,
    reg_rdata,
    reg_ready,
    cfg_enable,
    cfg_mode,
    cfg_request_trigger,
    cfg_fault_clear,
    cfg_output_mode,
    cfg_timeout_cycles,
    cfg_act_min,
    cfg_act_max,
    cfg_act_safe,
    cfg_velocity_ref,
    cfg_request_flags,
    status_busy,
    status_pending,
    status_timeout_active,
    status_fallback_active,
    status_fault_sticky,
    status_seq_last_accepted,
    status_req_seq,
    status_rsp_seq,
    status_rsp_cmd
);
    input clk;
    input reset_n;
    input reg_cs_n;
    input reg_valid;
    input reg_we;
    input reg_re;
    input [7:0] reg_addr;
    input [31:0] reg_wdata;
    output reg [31:0] reg_rdata;
    output reg reg_ready;
    output reg cfg_enable;
    output reg [1:0] cfg_mode;
    output reg cfg_request_trigger;
    output reg cfg_fault_clear;
    output reg [1:0] cfg_output_mode;
    output reg [31:0] cfg_timeout_cycles;
    output reg [15:0] cfg_act_min;
    output reg [15:0] cfg_act_max;
    output reg [15:0] cfg_act_safe;
    output reg [15:0] cfg_velocity_ref;
    output reg [7:0] cfg_request_flags;
    input status_busy;
    input status_pending;
    input status_timeout_active;
    input status_fallback_active;
    input [31:0] status_fault_sticky;
    input [15:0] status_seq_last_accepted;
    input [15:0] status_req_seq;
    input [15:0] status_rsp_seq;
    input [15:0] status_rsp_cmd;
    reg [31:0] reg_rdata_next;
    reg reg_ready_next;
    reg cfg_enable_next;
    reg [1:0] cfg_mode_next;
    reg cfg_request_trigger_next;
    reg cfg_fault_clear_next;
    reg [1:0] cfg_output_mode_next;
    reg [31:0] cfg_timeout_cycles_next;
    reg [15:0] cfg_act_min_next;
    reg [15:0] cfg_act_max_next;
    reg [15:0] cfg_act_safe_next;
    reg [15:0] cfg_velocity_ref_next;
    reg [7:0] cfg_request_flags_next;

    localparam [7:0] ADDR_CONTROL          = 8'h00;
    localparam [7:0] ADDR_STATUS           = 8'h04;
    localparam [7:0] ADDR_TIMEOUT_CYCLES   = 8'h08;
    localparam [7:0] ADDR_ACT_MIN          = 8'h0C;
    localparam [7:0] ADDR_ACT_MAX          = 8'h10;
    localparam [7:0] ADDR_ACT_SAFE         = 8'h14;
    localparam [7:0] ADDR_VELOCITY_REF     = 8'h18;
    localparam [7:0] ADDR_SEQ_LAST_ACCEPTED= 8'h1C;
    localparam [7:0] ADDR_REQ_SEQ          = 8'h20;
    localparam [7:0] ADDR_RSP_SEQ          = 8'h24;
    localparam [7:0] ADDR_RSP_CMD          = 8'h28;
    localparam [7:0] ADDR_FAULT_STICKY     = 8'h2C;

    wire access_fire;
    assign access_fire = (~reg_cs_n) & reg_valid;

    always @(*) begin
        reg_rdata_next = 32'h00000000;
        reg_ready_next = 1'b1;
        cfg_enable_next = cfg_enable;
        cfg_mode_next = cfg_mode;
        cfg_request_trigger_next = 1'b0;
        cfg_fault_clear_next = 1'b0;
        cfg_output_mode_next = cfg_output_mode;
        cfg_timeout_cycles_next = cfg_timeout_cycles;
        cfg_act_min_next = cfg_act_min;
        cfg_act_max_next = cfg_act_max;
        cfg_act_safe_next = cfg_act_safe;
        cfg_velocity_ref_next = cfg_velocity_ref;
        cfg_request_flags_next = cfg_request_flags;

        if (access_fire) begin
            if (reg_we) begin
                case (reg_addr)
                    ADDR_CONTROL: begin
                        cfg_enable_next = reg_wdata[0];
                        cfg_mode_next = reg_wdata[2:1];
                        cfg_request_trigger_next = reg_wdata[3];
                        cfg_fault_clear_next = reg_wdata[4];
                        cfg_output_mode_next = reg_wdata[6:5];
                    end
                    ADDR_TIMEOUT_CYCLES: begin
                        cfg_timeout_cycles_next = reg_wdata;
                    end
                    ADDR_ACT_MIN: begin
                        cfg_act_min_next = reg_wdata[15:0];
                    end
                    ADDR_ACT_MAX: begin
                        cfg_act_max_next = reg_wdata[15:0];
                    end
                    ADDR_ACT_SAFE: begin
                        cfg_act_safe_next = reg_wdata[15:0];
                    end
                    ADDR_VELOCITY_REF: begin
                        cfg_velocity_ref_next = reg_wdata[15:0];
                    end
                    ADDR_CONTROL: begin
                        cfg_enable_next = reg_wdata[0];
                        cfg_mode_next = reg_wdata[2:1];
                        cfg_request_trigger_next = reg_wdata[3];
                        cfg_fault_clear_next = reg_wdata[4];
                        cfg_output_mode_next = reg_wdata[6:5];
                    end
                    default: begin
                    end
                endcase
            end
            if (reg_re) begin
                case (reg_addr)
                    ADDR_CONTROL: begin
                        reg_rdata_next = {25'h0000000, cfg_output_mode, cfg_fault_clear_next, cfg_request_trigger_next, cfg_mode_next, cfg_enable_next};
                    end
                    ADDR_STATUS: begin
                        reg_rdata_next = {26'h0000000, status_fallback_active, status_busy, status_pending, status_timeout_active, |status_fault_sticky, status_busy};
                        reg_rdata_next[5] = |status_fault_sticky;
                        reg_rdata_next[4] = status_fallback_active;
                        reg_rdata_next[3] = status_timeout_active;
                        reg_rdata_next[2] = status_pending;
                        reg_rdata_next[1] = status_busy;
                        reg_rdata_next[0] = status_busy;
                    end
                    ADDR_TIMEOUT_CYCLES: begin
                        reg_rdata_next = cfg_timeout_cycles;
                    end
                    ADDR_ACT_MIN: begin
                        reg_rdata_next = {16'h0000, cfg_act_min};
                    end
                    ADDR_ACT_MAX: begin
                        reg_rdata_next = {16'h0000, cfg_act_max};
                    end
                    ADDR_ACT_SAFE: begin
                        reg_rdata_next = {16'h0000, cfg_act_safe};
                    end
                    ADDR_VELOCITY_REF: begin
                        reg_rdata_next = {16'h0000, cfg_velocity_ref};
                    end
                    ADDR_SEQ_LAST_ACCEPTED: begin
                        reg_rdata_next = {16'h0000, status_seq_last_accepted};
                    end
                    ADDR_REQ_SEQ: begin
                        reg_rdata_next = {16'h0000, status_req_seq};
                    end
                    ADDR_RSP_SEQ: begin
                        reg_rdata_next = {16'h0000, status_rsp_seq};
                    end
                    ADDR_RSP_CMD: begin
                        reg_rdata_next = {16'h0000, status_rsp_cmd};
                    end
                    ADDR_FAULT_STICKY: begin
                        reg_rdata_next = status_fault_sticky;
                    end
                    default: begin
                        reg_rdata_next = 32'h00000000;
                    end
                endcase
            end
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_rdata <= 32'h00000000;
            reg_ready <= 1'b1;
            cfg_enable <= 1'b0;
            cfg_mode <= 2'b00;
            cfg_request_trigger <= 1'b0;
            cfg_fault_clear <= 1'b0;
            cfg_output_mode <= 2'b00;
            cfg_timeout_cycles <= 32'h00000000;
            cfg_act_min <= 16'h0000;
            cfg_act_max <= 16'h0000;
            cfg_act_safe <= 16'h0000;
            cfg_velocity_ref <= 16'h0000;
            cfg_request_flags <= 8'h00;
        end else begin
            reg_rdata <= reg_rdata_next;
            reg_ready <= reg_ready_next;
            cfg_enable <= cfg_enable_next;
            cfg_mode <= cfg_mode_next;
            cfg_request_trigger <= cfg_request_trigger_next;
            cfg_fault_clear <= cfg_fault_clear_next;
            cfg_output_mode <= cfg_output_mode_next;
            cfg_timeout_cycles <= cfg_timeout_cycles_next;
            cfg_act_min <= cfg_act_min_next;
            cfg_act_max <= cfg_act_max_next;
            cfg_act_safe <= cfg_act_safe_next;
            cfg_velocity_ref <= cfg_velocity_ref_next;
            cfg_request_flags <= cfg_request_flags_next;
        end
    end
endmodule
