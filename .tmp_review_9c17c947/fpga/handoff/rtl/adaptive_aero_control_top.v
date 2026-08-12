module adaptive_aero_control_top (
    input  clk,
    input  reset_n,
    input  [11:0] requested_cmd,
    input  [1:0] fallback_sel,
    input  [11:0] cmd_min_limit,
    input  [11:0] cmd_max_limit,
    output reg [11:0] safe_cmd,
    output reg clamp_hit
);

reg [11:0] selected_cmd;
reg [11:0] fallback_cmd;
reg [11:0] clamped_cmd;
reg clamp_hit_next;

always @(*) begin
    fallback_cmd = 12'h000;
    case (fallback_sel)
        2'b00: fallback_cmd = 12'h000;
        2'b01: fallback_cmd = 12'h080;
        2'b10: fallback_cmd = 12'h100;
        default: fallback_cmd = 12'h020;
    endcase

    selected_cmd = requested_cmd;
    if (selected_cmd == 12'h000) begin
        selected_cmd = fallback_cmd;
    end

    clamp_hit_next = 1'b0;
    clamped_cmd = selected_cmd;

    if (clamped_cmd < cmd_min_limit) begin
        clamped_cmd = cmd_min_limit;
        clamp_hit_next = 1'b1;
    end

    if (clamped_cmd > cmd_max_limit) begin
        clamped_cmd = cmd_max_limit;
        clamp_hit_next = 1'b1;
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        safe_cmd <= 12'h020;
        clamp_hit <= 1'b0;
    end else begin
        safe_cmd <= clamped_cmd;
        clamp_hit <= clamp_hit_next;
    end
end

endmodule
