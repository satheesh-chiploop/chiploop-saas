module adaptive_aero_control_top (
    clk,
    reset_n,
    cmd_candidate_a,
    cmd_candidate_b,
    cmd_candidate_c,
    cmd_candidate_d,
    cmd_candidate_valid,
    cfg_cmd_min_a,
    cfg_cmd_max_a,
    cfg_cmd_min_b,
    cfg_cmd_max_b,
    cfg_cmd_min_c,
    cfg_cmd_max_c,
    cfg_cmd_min_d,
    cfg_cmd_max_d,
    actuator_enable_in,
    actuator_cmd_a,
    actuator_cmd_b,
    actuator_cmd_c,
    actuator_cmd_d,
    actuator_enable_out,
    sanity_fault
);

input clk;
input reset_n;
input [11:0] cmd_candidate_a;
input [11:0] cmd_candidate_b;
input [11:0] cmd_candidate_c;
input [11:0] cmd_candidate_d;
input cmd_candidate_valid;
input [11:0] cfg_cmd_min_a;
input [11:0] cfg_cmd_max_a;
input [11:0] cfg_cmd_min_b;
input [11:0] cfg_cmd_max_b;
input [11:0] cfg_cmd_min_c;
input [11:0] cfg_cmd_max_c;
input [11:0] cfg_cmd_min_d;
input [11:0] cfg_cmd_max_d;
input actuator_enable_in;
output [11:0] actuator_cmd_a;
output [11:0] actuator_cmd_b;
output [11:0] actuator_cmd_c;
output [11:0] actuator_cmd_d;
output actuator_enable_out;
output sanity_fault;

reg [11:0] actuator_cmd_a_r;
reg [11:0] actuator_cmd_b_r;
reg [11:0] actuator_cmd_c_r;
reg [11:0] actuator_cmd_d_r;
reg actuator_enable_out_r;
reg sanity_fault_r;

reg [11:0] clamp_a;
reg [11:0] clamp_b;
reg [11:0] clamp_c;
reg [11:0] clamp_d;

reg fault_range_a;
reg fault_range_b;
reg fault_range_c;
reg fault_range_d;
reg valid_inputs;

assign actuator_cmd_a = actuator_cmd_a_r;
assign actuator_cmd_b = actuator_cmd_b_r;
assign actuator_cmd_c = actuator_cmd_c_r;
assign actuator_cmd_d = actuator_cmd_d_r;
assign actuator_enable_out = actuator_enable_out_r;
assign sanity_fault = sanity_fault_r;

always @(*) begin
    clamp_a = 12'h000;
    clamp_b = 12'h000;
    clamp_c = 12'h000;
    clamp_d = 12'h000;
    fault_range_a = 1'b0;
    fault_range_b = 1'b0;
    fault_range_c = 1'b0;
    fault_range_d = 1'b0;
    valid_inputs = 1'b0;

    if (cfg_cmd_min_a > cfg_cmd_max_a)
        fault_range_a = 1'b1;
    if (cfg_cmd_min_b > cfg_cmd_max_b)
        fault_range_b = 1'b1;
    if (cfg_cmd_min_c > cfg_cmd_max_c)
        fault_range_c = 1'b1;
    if (cfg_cmd_min_d > cfg_cmd_max_d)
        fault_range_d = 1'b1;

    if (cmd_candidate_a < cfg_cmd_min_a)
        clamp_a = cfg_cmd_min_a;
    else if (cmd_candidate_a > cfg_cmd_max_a)
        clamp_a = cfg_cmd_max_a;
    else
        clamp_a = cmd_candidate_a;

    if (cmd_candidate_b < cfg_cmd_min_b)
        clamp_b = cfg_cmd_min_b;
    else if (cmd_candidate_b > cfg_cmd_max_b)
        clamp_b = cfg_cmd_max_b;
    else
        clamp_b = cmd_candidate_b;

    if (cmd_candidate_c < cfg_cmd_min_c)
        clamp_c = cfg_cmd_min_c;
    else if (cmd_candidate_c > cfg_cmd_max_c)
        clamp_c = cfg_cmd_max_c;
    else
        clamp_c = cmd_candidate_c;

    if (cmd_candidate_d < cfg_cmd_min_d)
        clamp_d = cfg_cmd_min_d;
    else if (cmd_candidate_d > cfg_cmd_max_d)
        clamp_d = cfg_cmd_max_d;
    else
        clamp_d = cmd_candidate_d;

    valid_inputs = cmd_candidate_valid & actuator_enable_in &
                   ~fault_range_a & ~fault_range_b & ~fault_range_c & ~fault_range_d;
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        actuator_cmd_a_r <= 12'h000;
        actuator_cmd_b_r <= 12'h000;
        actuator_cmd_c_r <= 12'h000;
        actuator_cmd_d_r <= 12'h000;
        actuator_enable_out_r <= 1'b0;
        sanity_fault_r <= 1'b0;
    end else begin
        if (valid_inputs) begin
            actuator_cmd_a_r <= clamp_a;
            actuator_cmd_b_r <= clamp_b;
            actuator_cmd_c_r <= clamp_c;
            actuator_cmd_d_r <= clamp_d;
            actuator_enable_out_r <= 1'b1;
            sanity_fault_r <= 1'b0;
        end else begin
            actuator_cmd_a_r <= cfg_cmd_min_a;
            actuator_cmd_b_r <= cfg_cmd_min_b;
            actuator_cmd_c_r <= cfg_cmd_min_c;
            actuator_cmd_d_r <= cfg_cmd_min_d;
            actuator_enable_out_r <= 1'b0;
            if (cmd_candidate_valid == 1'b0 || actuator_enable_in == 1'b0)
                sanity_fault_r <= 1'b0;
            else
                sanity_fault_r <= fault_range_a | fault_range_b | fault_range_c | fault_range_d;
        end
    end
end

endmodule
