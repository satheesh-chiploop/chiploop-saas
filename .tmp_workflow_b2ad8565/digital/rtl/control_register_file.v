module control_register_file (
    input         clk,
    input         rst_n,
    input         mmio_valid,
    input         mmio_write,
    input  [7:0] mmio_addr,
    input  [63:0] mmio_wdata,
    output reg [63:0] mmio_rdata,
    output        mmio_ready,
    output reg    cfg_enable,
    output reg [2:0] cfg_mode,
    output reg [15:0] cfg_timeout_threshold,
    output reg [15:0] cfg_request_seq_seed,
    output reg [15:0] cfg_response_age_limit,
    output reg [31:0] cfg_actuator_min,
    output reg [31:0] cfg_actuator_max,
    output reg    cfg_slew_enable,
    output reg [15:0] cfg_slew_limit,
    output reg [2:0] cfg_safe_selector,
    output reg    cfg_fault_clear_w1c,
    output reg    fault_status,
    output reg [7:0] fault_cause,
    output reg [15:0] revision_id,
    output reg [31:0] last_good_cmd,
    output reg [15:0] timeout_counter_snapshot,
    output reg [15:0] request_id_snapshot,
    output reg    status_snapshot_valid
);

assign mmio_ready = mmio_valid;

wire mmio_access;
assign mmio_access = mmio_valid;

wire write_sel_rev;
wire write_sel_ctrl;
wire write_sel_min;
wire write_sel_max;
wire write_sel_fault;
wire write_sel_watch;
wire write_sel_status;

assign write_sel_rev   = mmio_access & mmio_write & (mmio_addr == 8'h00);
assign write_sel_ctrl  = mmio_access & mmio_write & (mmio_addr == 8'h04);
assign write_sel_min   = mmio_access & mmio_write & (mmio_addr == 8'h08);
assign write_sel_max   = mmio_access & mmio_write & (mmio_addr == 8'h0C);
assign write_sel_fault = mmio_access & mmio_write & (mmio_addr == 8'h10);
assign write_sel_watch = mmio_access & mmio_write & (mmio_addr == 8'h14);
assign write_sel_status = mmio_access & mmio_write & (mmio_addr == 8'h18);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_enable <= 1'b0;
        cfg_mode <= 3'b000;
        cfg_timeout_threshold <= 16'h0000;
        cfg_request_seq_seed <= 16'h0000;
        cfg_response_age_limit <= 16'h0000;
        cfg_actuator_min <= 32'h00000000;
        cfg_actuator_max <= 32'hFFFFFFFF;
        cfg_slew_enable <= 1'b0;
        cfg_slew_limit <= 16'h0000;
        cfg_safe_selector <= 3'b000;
        cfg_fault_clear_w1c <= 1'b0;
        fault_status <= 1'b0;
        fault_cause <= 8'h00;
        revision_id <= 16'h0001;
        last_good_cmd <= 32'h00000000;
        timeout_counter_snapshot <= 16'h0000;
        request_id_snapshot <= 16'h0000;
        status_snapshot_valid <= 1'b0;
        mmio_rdata <= 64'h0000000000000000;
    end else begin
        cfg_fault_clear_w1c <= 1'b0;
        status_snapshot_valid <= 1'b0;

        if (write_sel_ctrl) begin
            cfg_enable <= mmio_wdata[0];
            cfg_mode <= mmio_wdata[3:1];
            cfg_slew_enable <= mmio_wdata[4];
            cfg_safe_selector <= mmio_wdata[7:5];
            cfg_request_seq_seed <= mmio_wdata[31:16];
            cfg_response_age_limit <= mmio_wdata[47:32];
            cfg_timeout_threshold <= mmio_wdata[63:48];
        end
        if (write_sel_min) begin
            cfg_actuator_min <= mmio_wdata[31:0];
        end
        if (write_sel_max) begin
            cfg_actuator_max <= mmio_wdata[31:0];
        end
        if (write_sel_fault) begin
            if (mmio_wdata[0]) begin
                fault_status <= 1'b0;
                fault_cause <= 8'h00;
            end
        end
        if (write_sel_watch) begin
            timeout_counter_snapshot <= mmio_wdata[15:0];
            request_id_snapshot <= mmio_wdata[31:16];
            last_good_cmd <= mmio_wdata[63:32];
            status_snapshot_valid <= 1'b1;
        end
        if (write_sel_status) begin
            status_snapshot_valid <= 1'b1;
        end
        if (mmio_access && !mmio_write) begin
            case (mmio_addr)
                8'h00: mmio_rdata <= {48'h000000000000, revision_id};
                8'h04: mmio_rdata <= {cfg_timeout_threshold, cfg_response_age_limit, cfg_request_seq_seed, 8'h00, cfg_safe_selector, cfg_slew_enable, cfg_mode, cfg_enable};
                8'h08: mmio_rdata <= {32'h00000000, cfg_actuator_min};
                8'h0C: mmio_rdata <= {32'h00000000, cfg_actuator_max};
                8'h10: mmio_rdata <= {48'h000000000000, fault_cause, 7'h00, fault_status};
                8'h14: mmio_rdata <= {last_good_cmd, request_id_snapshot, timeout_counter_snapshot};
                8'h18: mmio_rdata <= {57'b0, status_snapshot_valid, actuator_status_bits};
                8'h1C: mmio_rdata <= 64'h0000000000000000;
                default: mmio_rdata <= 64'h0000000000000000;
            endcase
        end
        if (mmio_access && mmio_write && (mmio_addr == 8'h00)) begin
            revision_id <= revision_id;
        end
        if (cfg_enable) begin
            cfg_fault_clear_w1c <= cfg_fault_clear_w1c;
        end
    end
end

wire [5:0] actuator_status_bits;
assign actuator_status_bits = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};

endmodule
