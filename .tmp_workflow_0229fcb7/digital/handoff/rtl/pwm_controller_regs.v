module pwm_controller_regs (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    rd_data,
    enable,
    duty_cycle,
    period,
    counter_value
);
input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [7:0] wr_data;
input rd_en;
input [7:0] rd_addr;
output reg [7:0] rd_data;
output reg enable;
output reg [7:0] duty_cycle;
output reg [7:0] period;
output reg [7:0] counter_value;

reg [7:0] control_reg;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 8'h00;
        duty_cycle <= 8'h00;
        period <= 8'h00;
        counter_value <= 8'h00;
        rd_data <= 8'h00;
        enable <= 1'b0;
    end else begin
        if (wr_en) begin
            case (wr_addr)
                8'h00: begin
                    control_reg <= {7'h00, wr_data[0]};
                    enable <= wr_data[0];
                end
                8'h04: begin
                    duty_cycle <= wr_data;
                end
                8'h08: begin
                    period <= wr_data;
                end
                default: begin
                end
            endcase
        end

        if (enable && (period != 8'h00)) begin
            if (counter_value == period)
                counter_value <= 8'h00;
            else
                counter_value <= counter_value + 8'h01;
        end

        if (rd_en) begin
            case (rd_addr)
                8'h00: rd_data <= {7'h00, control_reg[0]};
                8'h04: rd_data <= duty_cycle;
                8'h08: rd_data <= period;
                8'h0C: rd_data <= counter_value;
                default: rd_data <= 8'h00;
            endcase
        end else begin
            rd_data <= 8'h00;
        end
    end
end

endmodule
