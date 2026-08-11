module adaptive_aero_control_csr (
    clk,
    rst_n,
    cfg_wr_en,
    cfg_rd_en,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    enable,
    clear_faults,
    mode_select,
    freshness_limit,
    timeout_limit,
    max_cmd,
    min_cmd,
    rate_limit,
    fallback_mode,
    sequence_counter,
    fault_status,
    idle_safe
);
    input clk;
    input rst_n;
    input cfg_wr_en;
    input cfg_rd_en;
    input [5:0] cfg_addr;
    input [63:0] cfg_wdata;
    output [63:0] cfg_rdata;
    output enable;
    output clear_faults;
    output [2:0] mode_select;
    output [7:0] freshness_limit;
    output [7:0] timeout_limit;
    output [15:0] max_cmd;
    output [15:0] min_cmd;
    output [15:0] rate_limit;
    output [3:0] fallback_mode;
    output [15:0] sequence_counter;
    input [15:0] fault_status;
    input idle_safe;

    reg enable_r;
    reg clear_faults_r;
    reg [2:0] mode_select_r;
    reg [7:0] freshness_limit_r;
    reg [7:0] timeout_limit_r;
    reg [15:0] max_cmd_r;
    reg [15:0] min_cmd_r;
    reg [15:0] rate_limit_r;
    reg [3:0] fallback_mode_r;
    reg [15:0] sequence_counter_r;
    reg [63:0] cfg_rdata_r;
    assign enable = enable_r;
    assign clear_faults = clear_faults_r;
    assign mode_select = mode_select_r;
    assign freshness_limit = freshness_limit_r;
    assign timeout_limit = timeout_limit_r;
    assign max_cmd = max_cmd_r;
    assign min_cmd = min_cmd_r;
    assign rate_limit = rate_limit_r;
    assign fallback_mode = fallback_mode_r;
    assign sequence_counter = sequence_counter_r;
    assign cfg_rdata = cfg_rdata_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            enable_r <= 1'b0;
            clear_faults_r <= 1'b0;
            mode_select_r <= 3'b000;
            freshness_limit_r <= 8'h00;
            timeout_limit_r <= 8'h00;
            max_cmd_r <= 16'h0000;
            min_cmd_r <= 16'h0000;
            rate_limit_r <= 16'h0000;
            fallback_mode_r <= 4'h0;
            sequence_counter_r <= 16'h0001;
            cfg_rdata_r <= 64'h0000_0000_0000_0000;
        end else begin
            clear_faults_r <= 1'b0;
            if (cfg_wr_en) begin
                if (cfg_addr == 6'h00) begin
                    enable_r <= cfg_wdata[0];
                    clear_faults_r <= cfg_wdata[1] & idle_safe;
                    mode_select_r <= cfg_wdata[4:2];
                    freshness_limit_r <= cfg_wdata[12:5];
                    timeout_limit_r <= cfg_wdata[20:13];
                    max_cmd_r <= cfg_wdata[36:21];
                    min_cmd_r <= cfg_wdata[52:37];
                    rate_limit_r <= cfg_wdata[63:48];
                end else if (cfg_addr == 6'h01) begin
                    sequence_counter_r <= cfg_wdata[15:0];
                    fallback_mode_r <= cfg_wdata[19:16];
                end
            end
            if (cfg_rd_en) begin
                case (cfg_addr)
                    6'h00: cfg_rdata_r <= {19'h00000, rate_limit_r, min_cmd_r, max_cmd_r, 1'b0, timeout_limit_r, freshness_limit_r, mode_select_r, 1'b0, enable_r};
                    6'h01: cfg_rdata_r <= {44'h00000000000, fallback_mode_r, sequence_counter_r};
                    6'h02: cfg_rdata_r <= {48'h000000000000, fault_status};
                    default: cfg_rdata_r <= 64'h0000_0000_0000_0000;
                endcase
            end else begin
                cfg_rdata_r <= cfg_rdata_r;
            end
        end
    end
endmodule
