module pwm_controller (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    rd_data,
    pwm_out,
    counter_value
);

input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [7:0] wr_data;
input rd_en;
input [7:0] rd_addr;
output [7:0] rd_data;
output pwm_out;
output [7:0] counter_value;
reg [7:0] control_reg;
reg [7:0] duty_cycle_reg;
reg [7:0] period_reg;
reg [7:0] counter_reg;
reg [7:0] rd_data_r;
reg pwm_out_r;

assign rd_data = rd_data_r;
assign pwm_out = pwm_out_r;
assign counter_value = counter_reg;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 8'h00;
        duty_cycle_reg <= 8'h00;
        period_reg <= 8'h00;
        counter_reg <= 8'h00;
        rd_data_r <= 8'h00;
        pwm_out_r <= 1'b0;
    end else begin
        if (wr_en) begin
            case (wr_addr)
                8'h00: begin
                    control_reg[0] <= wr_data[0];
                end
                8'h04: begin
                    duty_cycle_reg <= wr_data;
                end
                8'h08: begin
                    period_reg <= wr_data;
                end
                default: begin
                end
            endcase
        end

        if (control_reg[0] && (period_reg != 8'h00)) begin
            if (counter_reg == period_reg) begin
                counter_reg <= 8'h00;
            end else begin
                counter_reg <= counter_reg + 8'h01;
            end
        end

        case (rd_addr)
            8'h00: rd_data_r <= {7'b0000000, control_reg[0]};
            8'h04: rd_data_r <= duty_cycle_reg;
            8'h08: rd_data_r <= period_reg;
            8'h0C: rd_data_r <= counter_reg;
            default: rd_data_r <= 8'h00;
        endcase

        pwm_out_r <= control_reg[0] && (counter_reg < duty_cycle_reg);
    end
end

endmodule
