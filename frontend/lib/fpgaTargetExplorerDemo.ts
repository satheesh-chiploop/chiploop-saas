export const MINIRV_EDGE_TOP = "minirv_edge_controller";

export const MINIRV_EDGE_CONTROLLER_RTL = `module minirv_edge_controller (
  input  wire        clk,
  input  wire        reset_n,
  input  wire [3:0]  debug_addr_a,
  input  wire [3:0]  debug_addr_b,
  input  wire [31:0] sensor_data,
  input  wire        sensor_valid,
  input  wire        uart_rx,
  output reg         uart_tx,
  output reg  [3:0]  pwm_out,
  output wire [31:0] debug_data,
  output reg         interrupt
);
  reg [31:0] register_bank [0:15];
  reg [31:0] pc;
  reg [31:0] instruction;
  reg [31:0] operand_a;
  reg [31:0] operand_b;
  reg [31:0] alu_result;
  reg [31:0] multiply_result;
  reg [31:0] sensor_accumulator;
  reg [15:0] sample_count;
  reg [15:0] timer_count;
  reg [7:0] pwm_counter;
  reg [7:0] pwm_duty [0:3];
  reg [9:0] uart_divider;
  reg [3:0] uart_bit;
  reg [9:0] uart_shift;
  reg [3:0] write_address;
  reg [31:0] write_data;
  reg write_enable;
  integer index;

  wire [31:0] read_a = register_bank[debug_addr_a];
  wire [31:0] read_b = register_bank[debug_addr_b];
  wire [31:0] rotated = (operand_a << operand_b[4:0]) | (operand_a >> (32-operand_b[4:0]));
  wire [63:0] full_product = operand_a * operand_b;
  assign debug_data = read_a ^ read_b ^ alu_result ^ sensor_accumulator;

  always @* begin
    case (instruction[5:0])
      6'h00: alu_result = operand_a + operand_b;
      6'h01: alu_result = operand_a - operand_b;
      6'h02: alu_result = operand_a ^ operand_b;
      6'h03: alu_result = operand_a | operand_b;
      6'h04: alu_result = operand_a & operand_b;
      6'h05: alu_result = operand_a << operand_b[4:0];
      6'h06: alu_result = operand_a >> operand_b[4:0];
      6'h07: alu_result = $signed(operand_a) >>> operand_b[4:0];
      6'h08: alu_result = ($signed(operand_a) < $signed(operand_b));
      6'h09: alu_result = (operand_a < operand_b);
      6'h0a: alu_result = rotated;
      6'h0b: alu_result = full_product[31:0];
      6'h0c: alu_result = full_product[63:32];
      6'h0d: alu_result = {operand_a[15:0], operand_b[15:0]};
      6'h0e: alu_result = {operand_b[7:0], operand_a[23:0]};
      6'h0f: alu_result = operand_a + {operand_b[15:0], 16'h0};
      default: alu_result = operand_a ^ {instruction[15:0], instruction[31:16]};
    endcase
  end

  always @* begin
    write_enable = instruction[31] | sensor_valid;
    write_address = sensor_valid ? sample_count[3:0] : instruction[9:6];
    write_data = sensor_valid ? sensor_data + sensor_accumulator : alu_result;
  end

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      pc <= 0;
      instruction <= 32'h8000_0000;
      operand_a <= 0;
      operand_b <= 1;
      multiply_result <= 0;
      sensor_accumulator <= 0;
      sample_count <= 0;
      timer_count <= 0;
      pwm_counter <= 0;
      pwm_duty[0] <= 8'd32;
      pwm_duty[1] <= 8'd64;
      pwm_duty[2] <= 8'd128;
      pwm_duty[3] <= 8'd192;
      uart_divider <= 0;
      uart_bit <= 0;
      uart_shift <= 10'h3ff;
      uart_tx <= 1;
      interrupt <= 0;
      for (index = 0; index < 16; index = index + 1)
        register_bank[index] <= 32'h1357_0000 ^ index;
    end else begin
      pc <= pc + 4;
      instruction <= read_a + pc + {26'd0, debug_addr_b};
      operand_a <= read_a ^ sensor_accumulator;
      operand_b <= read_b + sample_count;
      multiply_result <= full_product[31:0];
      timer_count <= timer_count + 1;
      pwm_counter <= pwm_counter + 1;
      pwm_out[0] <= pwm_counter < pwm_duty[0];
      pwm_out[1] <= pwm_counter < pwm_duty[1];
      pwm_out[2] <= pwm_counter < pwm_duty[2];
      pwm_out[3] <= pwm_counter < pwm_duty[3];
      if (write_enable)
        register_bank[write_address] <= write_data ^ multiply_result;
      if (sensor_valid) begin
        sensor_accumulator <= sensor_accumulator + sensor_data;
        sample_count <= sample_count + 1;
        pwm_duty[sample_count[1:0]] <= sensor_data[7:0];
      end
      interrupt <= (&timer_count[11:0]) | (sensor_accumulator[31:24] > 8'hc0);
      if (uart_divider == 10'd103) begin
        uart_divider <= 0;
        uart_tx <= uart_shift[0];
        uart_shift <= {1'b1, uart_shift[9:1]};
        if (uart_bit == 0 && sensor_valid) begin
          uart_shift <= {1'b1, sensor_data[7:0], 1'b0};
          uart_bit <= 10;
        end else if (uart_bit != 0) begin
          uart_bit <= uart_bit - 1;
        end
      end else begin
        uart_divider <= uart_divider + 1;
      end
      if (!uart_rx)
        register_bank[15] <= register_bank[15] + 32'h0101_0101;
    end
  end
endmodule
`;

export const MINIRV_EDGE_EXPLORER_NOTES = `MiniRV Edge Controller reference journey.
Compare one fixed RTL design across supported iCE40 and ECP5 targets at 75 MHz. The dual-read 16x32 register bank, 32-bit ALU, multiplier, sensor accumulator, UART, timer, interrupt logic, and four PWM channels are intentionally substantial enough to create a meaningful multi-board utilization and timing comparison.`;
