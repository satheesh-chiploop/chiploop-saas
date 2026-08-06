module command_saturator (
    clk,
    reset_n,
    command_enable,
    command_vector,
    supervisor_release,
    min_bound,
    max_bound,
    rate_limit_step,
    saturated_command,
    saturated_valid,
    command_clamped
);
input clk;
input reset_n;
input command_enable;
input [63:0] command_vector;
input supervisor_release;
input [63:0] min_bound;
input [63:0] max_bound;
input [63:0] rate_limit_step;
output [63:0] saturated_command;
output saturated_valid;
output command_clamped;

reg [63:0] saturated_command_r;
reg saturated_valid_r;
reg command_clamped_r;
reg [63:0] previous_command_r;
reg [63:0] clipped_command_r;

wire [63:0] bounded_low;
wire [63:0] bounded_high;
wire [63:0] rate_limited;
wire low_violation;
wire high_violation;
wire rate_violation;

assign low_violation = (command_vector < min_bound);
assign high_violation = (command_vector > max_bound);
assign bounded_low = low_violation ? min_bound : command_vector;
assign bounded_high = high_violation ? max_bound : bounded_low;
assign rate_violation = (bounded_high > (previous_command_r + rate_limit_step)) | (bounded_high < (previous_command_r - rate_limit_step));
assign rate_limited = rate_violation ? previous_command_r : bounded_high;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        saturated_command_r <= 64'h0000000000000000;
        saturated_valid_r <= 1'b0;
        command_clamped_r <= 1'b0;
        previous_command_r <= 64'h0000000000000000;
        clipped_command_r <= 64'h0000000000000000;
    end else begin
        saturated_valid_r <= 1'b0;
        command_clamped_r <= 1'b0;
        if (command_enable & supervisor_release) begin
            clipped_command_r <= rate_limited;
            saturated_command_r <= rate_limited;
            saturated_valid_r <= 1'b1;
            command_clamped_r <= low_violation | high_violation | rate_violation;
            previous_command_r <= rate_limited;
        end
    end
end

assign saturated_command = saturated_command_r;
assign saturated_valid = saturated_valid_r;
assign command_clamped = command_clamped_r;

endmodule
