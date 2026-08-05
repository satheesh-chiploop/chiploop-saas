module actuator_clamper (
    clk,
    rst_n,
    raw_cmd_valid,
    raw_actuator_cmd,
    cfg_actuator_min,
    cfg_actuator_max,
    clamped_cmd_valid,
    clamped_actuator_cmd,
    clamp_event
);

input clk;
input rst_n;
input raw_cmd_valid;
input [31:0] raw_actuator_cmd;
input [31:0] cfg_actuator_min;
input [31:0] cfg_actuator_max;
output reg clamped_cmd_valid;
output reg [31:0] clamped_actuator_cmd;
output reg clamp_event;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        clamped_cmd_valid <= 1'b0;
        clamped_actuator_cmd <= 32'h00000000;
        clamp_event <= 1'b0;
    end else begin
        clamped_cmd_valid <= raw_cmd_valid;
        clamp_event <= 1'b0;
        if (raw_cmd_valid) begin
            if ($signed(raw_actuator_cmd) < $signed(cfg_actuator_min)) begin
                clamped_actuator_cmd <= cfg_actuator_min;
                clamp_event <= 1'b1;
            end else if ($signed(raw_actuator_cmd) > $signed(cfg_actuator_max)) begin
                clamped_actuator_cmd <= cfg_actuator_max;
                clamp_event <= 1'b1;
            end else begin
                clamped_actuator_cmd <= raw_actuator_cmd;
            end
        end else begin
            clamped_actuator_cmd <= 32'h00000000;
        end
    end
end

endmodule
