module adaptive_aero_control_registers (
    clk,
    reset,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_sel_i,
    wb_ack_o,
    wb_err_o,
    cfg_enable,
    cfg_mode_select,
    cfg_request_sequence,
    cfg_timeout_limit,
    cfg_stale_limit,
    cfg_velocity_mps,
    cfg_velocity_min_mps,
    cfg_velocity_max_mps,
    cfg_actuator_min,
    cfg_actuator_max,
    cfg_actuator_safe_pos,
    cfg_interrupt_mask,
    cfg_clear_faults,
    status_rsp_accepted,
    status_rsp_rejected,
    status_stale_event,
    status_timeout_event,
    status_clamp_event,
    status_safe_inhibit,
    status_fault_latched,
    fault_status,
    fault_code,
    accepted_rsp_count,
    rejected_rsp_count,
    stale_event_count,
    timeout_event_count,
    clamp_event_count,
    last_good_sequence,
    last_fault_code,
    identification,
    request_packet_shadow,
    response_metadata_shadow
);

input clk;
input reset;
input [7:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input wb_cyc_i;
input wb_stb_i;
input wb_we_i;
input [3:0] wb_sel_i;
output wb_ack_o;
output wb_err_o;
output cfg_enable;
output [2:0] cfg_mode_select;
output [7:0] cfg_request_sequence;
output [15:0] cfg_timeout_limit;
output [7:0] cfg_stale_limit;
output [15:0] cfg_velocity_mps;
output [15:0] cfg_velocity_min_mps;
output [15:0] cfg_velocity_max_mps;
output [15:0] cfg_actuator_min;
output [15:0] cfg_actuator_max;
output [15:0] cfg_actuator_safe_pos;
output [7:0] cfg_interrupt_mask;
output cfg_clear_faults;
input status_rsp_accepted;
input status_rsp_rejected;
input status_stale_event;
input status_timeout_event;
input status_clamp_event;
input status_safe_inhibit;
input status_fault_latched;
input [15:0] fault_status;
input [7:0] fault_code;
input [15:0] accepted_rsp_count;
input [15:0] rejected_rsp_count;
input [15:0] stale_event_count;
input [15:0] timeout_event_count;
input [15:0] clamp_event_count;
input [7:0] last_good_sequence;
input [7:0] last_fault_code;
output [31:0] identification;
input [127:0] request_packet_shadow;
input [31:0] response_metadata_shadow;
reg [31:0] wb_dat_o_r;
reg wb_ack_o_r;
reg wb_err_o_r;
reg cfg_enable_r;
reg [2:0] cfg_mode_select_r;
reg [7:0] cfg_request_sequence_r;
reg [15:0] cfg_timeout_limit_r;
reg [7:0] cfg_stale_limit_r;
reg [15:0] cfg_velocity_mps_r;
reg [15:0] cfg_velocity_min_mps_r;
reg [15:0] cfg_velocity_max_mps_r;
reg [15:0] cfg_actuator_min_r;
reg [15:0] cfg_actuator_max_r;
reg [15:0] cfg_actuator_safe_pos_r;
reg [7:0] cfg_interrupt_mask_r;
reg cfg_clear_faults_r;
reg [31:0] identification_r;
reg [31:0] ctrl_reg;
reg [31:0] seq_reg;
reg [31:0] timeout_reg;
reg [31:0] velocity_reg;
reg [31:0] clamp_reg;
reg [31:0] safe_reg;
reg [31:0] status_reg;
reg [31:0] fault_reg;
reg [31:0] counts0_reg;
reg [31:0] counts1_reg;
reg [31:0] counts2_reg;
reg [31:0] resp_meta_reg;
reg [31:0] read_mux;

wire write_fire;
wire read_fire;
wire sel_ok;
reg [31:0] ctrl_next;
reg [31:0] timeout_next;
reg [31:0] velocity_next;
reg [31:0] clamp_next;
reg [31:0] safe_next;
wire [31:0] fault_clear_mask;

assign write_fire = wb_cyc_i & wb_stb_i & wb_we_i;
assign read_fire = wb_cyc_i & wb_stb_i & ~wb_we_i;
assign sel_ok = (wb_sel_i == 4'b1111);
assign fault_clear_mask = {16{cfg_clear_faults_r}};

always @(*) begin
    read_mux = 32'h00000000;
    case (wb_adr_i)
        8'h00: read_mux = identification_r;
        8'h04: read_mux = ctrl_reg;
        8'h08: read_mux = seq_reg;
        8'h0C: read_mux = timeout_reg;
        8'h10: read_mux = velocity_reg;
        8'h14: read_mux = clamp_reg;
        8'h18: read_mux = safe_reg;
        8'h1C: read_mux = status_reg;
        8'h20: read_mux = fault_reg;
        8'h24: read_mux = counts0_reg;
        8'h28: read_mux = counts1_reg;
        8'h2C: read_mux = counts2_reg;
        8'h30: read_mux = resp_meta_reg;
        default: read_mux = 32'h00000000;
    endcase
end

always @(*) begin
    ctrl_next = ctrl_reg;
    timeout_next = timeout_reg;
    velocity_next = velocity_reg;
    clamp_next = clamp_reg;
    safe_next = safe_reg;

    if (write_fire) begin
        case (wb_adr_i)
            8'h04: begin
                if (wb_sel_i[0]) ctrl_next[7:0] = (ctrl_reg[7:0] & ~8'h10) | (wb_dat_i[7:0] & 8'h1F);
                if (wb_sel_i[1]) ctrl_next[15:8] = wb_dat_i[15:8];
            end
            8'h08: begin
                if (wb_sel_i[0]) ctrl_next[31:24] = ctrl_reg[31:24];
            end
            8'h0C: begin
                if (wb_sel_i[0]) timeout_next[7:0] = wb_dat_i[7:0];
                if (wb_sel_i[1]) timeout_next[15:8] = wb_dat_i[15:8];
                if (wb_sel_i[2]) timeout_next[23:16] = wb_dat_i[23:16];
                if (wb_sel_i[3]) timeout_next[31:24] = wb_dat_i[31:24];
            end
            8'h10: begin
                if (wb_sel_i[0]) velocity_next[7:0] = wb_dat_i[7:0];
                if (wb_sel_i[1]) velocity_next[15:8] = wb_dat_i[15:8];
                if (wb_sel_i[2]) velocity_next[23:16] = wb_dat_i[23:16];
                if (wb_sel_i[3]) velocity_next[31:24] = wb_dat_i[31:24];
            end
            8'h14: begin
                if (wb_sel_i[0]) clamp_next[7:0] = wb_dat_i[7:0];
                if (wb_sel_i[1]) clamp_next[15:8] = wb_dat_i[15:8];
                if (wb_sel_i[2]) clamp_next[23:16] = wb_dat_i[23:16];
                if (wb_sel_i[3]) clamp_next[31:24] = wb_dat_i[31:24];
            end
            8'h18: begin
                if (wb_sel_i[0]) safe_next[7:0] = wb_dat_i[7:0];
                if (wb_sel_i[1]) safe_next[15:8] = wb_dat_i[15:8];
            end
            default: begin
            end
        endcase
    end
end

always @(posedge clk) begin
    if (reset) begin
        wb_dat_o_r <= 32'h00000000;
        wb_ack_o_r <= 1'b0;
        wb_err_o_r <= 1'b0;
        cfg_enable_r <= 1'b0;
        cfg_mode_select_r <= 3'b000;
        cfg_request_sequence_r <= 8'h00;
        cfg_timeout_limit_r <= 16'd1000;
        cfg_stale_limit_r <= 8'd8;
        cfg_velocity_mps_r <= 16'd20;
        cfg_velocity_min_mps_r <= 16'd20;
        cfg_velocity_max_mps_r <= 16'd55;
        cfg_actuator_min_r <= 16'h0000;
        cfg_actuator_max_r <= 16'hFFFF;
        cfg_actuator_safe_pos_r <= 16'h0000;
        cfg_interrupt_mask_r <= 8'h00;
        cfg_clear_faults_r <= 1'b0;
        identification_r <= {16'd22033, 16'd256};
        ctrl_reg <= 32'h00000000;
        seq_reg <= 32'h00000000;
        timeout_reg <= 32'h000003E8;
        velocity_reg <= 32'h37001414;
        clamp_reg <= 32'hFFFF0000;
        safe_reg <= 32'h00000000;
        status_reg <= 32'h00000000;
        fault_reg <= 32'h00000000;
        counts0_reg <= 32'h00000000;
        counts1_reg <= 32'h00000000;
        counts2_reg <= 32'h00000000;
        resp_meta_reg <= 32'h00000000;
    end else begin
        wb_ack_o_r <= wb_cyc_i & wb_stb_i;
        wb_err_o_r <= write_fire & ~sel_ok;
        wb_dat_o_r <= read_mux;

        ctrl_reg[0] <= cfg_enable_r;
        ctrl_reg[3:1] <= cfg_mode_select_r;
        ctrl_reg[4] <= 1'b0;
        ctrl_reg[15:8] <= cfg_interrupt_mask_r;
        ctrl_reg[31:16] <= 16'h0000;

        seq_reg <= {24'h000000, cfg_request_sequence_r};
        timeout_reg <= timeout_next;
        velocity_reg <= {cfg_velocity_max_mps_r[7:0], cfg_velocity_min_mps_r[7:0], cfg_velocity_mps_r};
        clamp_reg <= {cfg_actuator_max_r, cfg_actuator_min_r};
        safe_reg <= {16'h0000, cfg_actuator_safe_pos_r};

        if (write_fire && wb_adr_i == 8'h04 && wb_sel_i[0]) begin
            cfg_enable_r <= wb_dat_i[0];
            cfg_mode_select_r <= wb_dat_i[3:1];
            cfg_clear_faults_r <= wb_dat_i[4];
        end else begin
            cfg_clear_faults_r <= 1'b0;
        end
        if (write_fire && wb_adr_i == 8'h04 && wb_sel_i[1]) begin
            cfg_interrupt_mask_r <= wb_dat_i[15:8];
        end
        if (write_fire && wb_adr_i == 8'h08 && wb_sel_i[0]) begin
            cfg_request_sequence_r <= wb_dat_i[7:0];
        end
        if (write_fire && wb_adr_i == 8'h0C) begin
            if (wb_sel_i[0]) cfg_timeout_limit_r[7:0] <= wb_dat_i[7:0];
            if (wb_sel_i[1]) cfg_timeout_limit_r[15:8] <= wb_dat_i[15:8];
            if (wb_sel_i[2]) cfg_stale_limit_r <= wb_dat_i[23:16];
        end
        if (write_fire && wb_adr_i == 8'h10) begin
            if (wb_sel_i[0]) cfg_velocity_mps_r[7:0] <= wb_dat_i[7:0];
            if (wb_sel_i[1]) cfg_velocity_mps_r[15:8] <= wb_dat_i[15:8];
            if (wb_sel_i[2]) cfg_velocity_min_mps_r <= wb_dat_i[23:16];
            if (wb_sel_i[3]) cfg_velocity_max_mps_r <= wb_dat_i[31:24];
        end
        if (write_fire && wb_adr_i == 8'h14) begin
            if (wb_sel_i[0]) cfg_actuator_min_r[7:0] <= wb_dat_i[7:0];
            if (wb_sel_i[1]) cfg_actuator_min_r[15:8] <= wb_dat_i[15:8];
            if (wb_sel_i[2]) cfg_actuator_max_r[7:0] <= wb_dat_i[23:16];
            if (wb_sel_i[3]) cfg_actuator_max_r[15:8] <= wb_dat_i[31:24];
        end
        if (write_fire && wb_adr_i == 8'h18) begin
            if (wb_sel_i[0]) cfg_actuator_safe_pos_r[7:0] <= wb_dat_i[7:0];
            if (wb_sel_i[1]) cfg_actuator_safe_pos_r[15:8] <= wb_dat_i[15:8];
        end
        if (reset) begin end

        if (status_rsp_accepted) status_reg[0] <= 1'b1;
        if (status_rsp_rejected) status_reg[1] <= 1'b1;
        if (status_stale_event) status_reg[2] <= 1'b1;
        if (status_timeout_event) status_reg[3] <= 1'b1;
        if (status_clamp_event) status_reg[4] <= 1'b1;
        status_reg[5] <= status_safe_inhibit;
        if (status_fault_latched) status_reg[6] <= 1'b1;

        if (cfg_clear_faults_r) begin
            status_reg[6:0] <= status_reg[6:0] & 7'b0000000;
            fault_reg[15:0] <= fault_reg[15:0] & ~fault_clear_mask;
        end

        fault_reg[15:0] <= fault_status;
        fault_reg[23:16] <= fault_code;
        fault_reg[31:24] <= 8'h00;

        counts0_reg[15:0] <= accepted_rsp_count;
        counts0_reg[31:16] <= rejected_rsp_count;
        counts1_reg[15:0] <= stale_event_count;
        counts1_reg[31:16] <= timeout_event_count;
        counts2_reg[15:0] <= clamp_event_count;
        counts2_reg[23:16] <= last_good_sequence;
        counts2_reg[31:24] <= last_fault_code;
        resp_meta_reg <= response_metadata_shadow;
    end
end

assign wb_dat_o = wb_dat_o_r;
assign wb_ack_o = wb_ack_o_r;
assign wb_err_o = wb_err_o_r;
assign cfg_enable = cfg_enable_r;
assign cfg_mode_select = cfg_mode_select_r;
assign cfg_request_sequence = cfg_request_sequence_r;
assign cfg_timeout_limit = cfg_timeout_limit_r;
assign cfg_stale_limit = cfg_stale_limit_r;
assign cfg_velocity_mps = cfg_velocity_mps_r;
assign cfg_velocity_min_mps = cfg_velocity_min_mps_r;
assign cfg_velocity_max_mps = cfg_velocity_max_mps_r;
assign cfg_actuator_min = cfg_actuator_min_r;
assign cfg_actuator_max = cfg_actuator_max_r;
assign cfg_actuator_safe_pos = cfg_actuator_safe_pos_r;
assign cfg_interrupt_mask = cfg_interrupt_mask_r;
assign cfg_clear_faults = cfg_clear_faults_r;
assign identification = identification_r;

endmodule
