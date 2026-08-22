module adaptive_aero_register_map (
    clk,
    reset_n,
    apb_ctrl_addr,
    apb_ctrl_wdata,
    apb_ctrl_valid,
    apb_ctrl_write,
    apb_ctrl_ready,
    apb_ctrl_rdata,
    apb_ctrl_rvalid,
    cfg_enable,
    cfg_soft_reset,
    cfg_arm_request,
    cfg_clear_fault,
    cfg_operating_velocity_mps,
    cfg_timeout_cycles,
    cfg_max_outstanding,
    cfg_clamp_min,
    cfg_clamp_max,
    cfg_request_seq,
    cfg_response_seq,
    cfg_fault_status,
    cfg_mode_status,
    cfg_irq_enable,
    reg_read_data,
    reg_read_valid,
    reg_write_accept,
    reg_fault_sticky,
    reg_request_pending,
    reg_fallback_active
);
    input clk;
    input reset_n;
    input [7:0] apb_ctrl_addr;
    input [63:0] apb_ctrl_wdata;
    input apb_ctrl_valid;
    input apb_ctrl_write;
    output reg apb_ctrl_ready;
    output reg [63:0] apb_ctrl_rdata;
    output reg apb_ctrl_rvalid;
    output reg cfg_enable;
    output reg cfg_soft_reset;
    output reg cfg_arm_request;
    output reg cfg_clear_fault;
    output reg [15:0] cfg_operating_velocity_mps;
    output reg [23:0] cfg_timeout_cycles;
    output reg [3:0] cfg_max_outstanding;
    output reg [15:0] cfg_clamp_min;
    output reg [15:0] cfg_clamp_max;
    output reg [15:0] cfg_request_seq;
    output reg [15:0] cfg_response_seq;
    input [7:0] cfg_fault_status;
    input [7:0] cfg_mode_status;
    output reg cfg_irq_enable;
    input [63:0] reg_read_data;
    input reg_read_valid;
    input reg_write_accept;
    input [15:0] reg_fault_sticky;
    input reg_request_pending;
    input reg_fallback_active;

    reg [63:0] ctrl_reg;
    reg [63:0] timing_reg;
    reg [63:0] clamp_reg;
    reg [63:0] req_desc_lo_reg;
    reg [63:0] req_desc_hi_reg;
    reg [63:0] read_data_next;
    reg read_valid_next;
    reg write_accept_next;

    localparam [7:0] ADDR_CTRL       = 8'h00;
    localparam [7:0] ADDR_TIMING     = 8'h08;
    localparam [7:0] ADDR_CLAMP      = 8'h10;
    localparam [7:0] ADDR_STATUS0    = 8'h18;
    localparam [7:0] ADDR_OBS0       = 8'h20;
    localparam [7:0] ADDR_COUNTERS   = 8'h28;
    localparam [7:0] ADDR_REQ_LO     = 8'h30;
    localparam [7:0] ADDR_REQ_HI     = 8'h38;

    always @(*) begin
        read_data_next = 64'h0;
        read_valid_next = 1'b0;
        write_accept_next = 1'b0;
        if (apb_ctrl_valid) begin
            if (apb_ctrl_write) begin
                write_accept_next = 1'b1;
            end else begin
                read_valid_next = 1'b1;
            end
        end
        case (apb_ctrl_addr)
            ADDR_CTRL: begin
                read_data_next = {8'h00, cfg_fault_status, cfg_mode_status, cfg_response_seq, cfg_request_seq, cfg_irq_enable, cfg_clear_fault, cfg_arm_request, cfg_soft_reset, cfg_enable, 3'b0};
            end
            ADDR_TIMING: begin
                read_data_next = {16'b0, cfg_max_outstanding, 4'h0, cfg_timeout_cycles, cfg_operating_velocity_mps};
            end
            ADDR_CLAMP: begin
                read_data_next = {32'h00000000, cfg_clamp_max, cfg_clamp_min};
            end
            ADDR_STATUS0: begin
                read_data_next = {46'b0, reg_fallback_active, reg_fault_sticky, reg_request_pending};
            end
            ADDR_OBS0: begin
                read_data_next = {32'h00000000, req_desc_hi_reg[31:0]};
            end
            ADDR_COUNTERS: begin
                read_data_next = {16'h0000, reg_fault_sticky, 16'h0000, 16'h0000};
            end
            ADDR_REQ_LO: begin
                read_data_next = req_desc_lo_reg;
            end
            ADDR_REQ_HI: begin
                read_data_next = req_desc_hi_reg;
            end
            default: begin
                read_data_next = 64'h0000000000000000;
            end
        endcase
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            ctrl_reg <= 64'h0000000000000000;
            timing_reg <= 64'h0000000000000001;
            clamp_reg <= 64'h0000000000000000;
            req_desc_lo_reg <= 64'h0000000000000000;
            req_desc_hi_reg <= 64'h0000000000000000;
            apb_ctrl_ready <= 1'b0;
            apb_ctrl_rdata <= 64'h0000000000000000;
            apb_ctrl_rvalid <= 1'b0;
            cfg_enable <= 1'b0;
            cfg_soft_reset <= 1'b0;
            cfg_arm_request <= 1'b0;
            cfg_clear_fault <= 1'b0;
            cfg_operating_velocity_mps <= 16'h0000;
            cfg_timeout_cycles <= 24'h000000;
            cfg_max_outstanding <= 4'h1;
            cfg_clamp_min <= 16'h0000;
            cfg_clamp_max <= 16'h0000;
            cfg_request_seq <= 16'h0000;
            cfg_response_seq <= 16'h0000;
            cfg_irq_enable <= 1'b0;
        end else begin
            apb_ctrl_ready <= write_accept_next;
            apb_ctrl_rdata <= read_data_next;
            apb_ctrl_rvalid <= read_valid_next;

            cfg_enable <= ctrl_reg[0];
            cfg_soft_reset <= ctrl_reg[1];
            cfg_arm_request <= ctrl_reg[2];
            cfg_clear_fault <= ctrl_reg[3];
            cfg_irq_enable <= ctrl_reg[4];
            cfg_operating_velocity_mps <= timing_reg[15:0];
            cfg_timeout_cycles <= timing_reg[39:16];
            cfg_max_outstanding <= timing_reg[43:40];
            cfg_clamp_min <= clamp_reg[15:0];
            cfg_clamp_max <= clamp_reg[31:16];
            cfg_request_seq <= ctrl_reg[39:24];
            cfg_response_seq <= ctrl_reg[55:40];

            if (apb_ctrl_valid && apb_ctrl_write) begin
                case (apb_ctrl_addr)
                    ADDR_CTRL: begin
                        ctrl_reg[0] <= apb_ctrl_wdata[0];
                        ctrl_reg[1] <= apb_ctrl_wdata[1];
                        ctrl_reg[2] <= apb_ctrl_wdata[2];
                        ctrl_reg[3] <= apb_ctrl_wdata[3];
                        ctrl_reg[4] <= apb_ctrl_wdata[4];
                        ctrl_reg[23:16] <= apb_ctrl_wdata[23:16];
                        ctrl_reg[39:24] <= apb_ctrl_wdata[39:24];
                        ctrl_reg[55:40] <= apb_ctrl_wdata[55:40];
                    end
                    ADDR_TIMING: begin
                        timing_reg[15:0] <= apb_ctrl_wdata[15:0];
                        timing_reg[39:16] <= apb_ctrl_wdata[39:16];
                        timing_reg[43:40] <= apb_ctrl_wdata[43:40];
                    end
                    ADDR_CLAMP: begin
                        clamp_reg[15:0] <= apb_ctrl_wdata[15:0];
                        clamp_reg[31:16] <= apb_ctrl_wdata[31:16];
                    end
                    ADDR_REQ_LO: begin
                        req_desc_lo_reg <= apb_ctrl_wdata;
                    end
                    ADDR_REQ_HI: begin
                        req_desc_hi_reg <= apb_ctrl_wdata;
                    end
                    default: begin
                    end
                endcase
            end

            if (reg_write_accept) begin
                ctrl_reg[2] <= 1'b0;
                ctrl_reg[1] <= 1'b0;
                ctrl_reg[3] <= 1'b0;
            end

            if (reg_read_valid) begin
                ctrl_reg[23:16] <= cfg_mode_status;
                ctrl_reg[55:40] <= cfg_response_seq;
            end
            if (reg_fault_sticky != 16'h0000) begin
                ctrl_reg[63:56] <= cfg_fault_status;
            end
        end
    end
endmodule
