// Auto-generated limited MBIST controller collateral.
// Demonstration-quality March C- controller for a single-port scratchpad.
module chiploop_mbist_controller #(
  parameter int ADDR_WIDTH = 4,
  parameter int DATA_WIDTH = 8
) (
  input  logic                  clk,
  input  logic                  reset_n,
  input  logic                  start,
  output logic                  done,
  output logic                  fail,
  output logic [ADDR_WIDTH-1:0] mem_addr,
  output logic                  mem_we,
  output logic [DATA_WIDTH-1:0] mem_wdata,
  input  logic [DATA_WIDTH-1:0] mem_rdata
);
  typedef enum logic [2:0] {
    IDLE,
    WRITE_ZERO_UP,
    READ_ZERO_WRITE_ONE_UP,
    READ_ONE_WRITE_ZERO_DOWN,
    READ_ZERO_DOWN,
    DONE
  } state_t;

  state_t state;
  logic [ADDR_WIDTH-1:0] addr;

  assign mem_addr = addr;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      state <= IDLE;
      addr <= '0;
      done <= 1'b0;
      fail <= 1'b0;
      mem_we <= 1'b0;
      mem_wdata <= '0;
    end else begin
      done <= 1'b0;
      mem_we <= 1'b0;
      unique case (state)
        IDLE: begin
          fail <= 1'b0;
          addr <= '0;
          if (start) state <= WRITE_ZERO_UP;
        end
        WRITE_ZERO_UP: begin
          mem_we <= 1'b1;
          mem_wdata <= '0;
          if (&addr) begin
            addr <= '0;
            state <= READ_ZERO_WRITE_ONE_UP;
          end else begin
            addr <= addr + 1'b1;
          end
        end
        READ_ZERO_WRITE_ONE_UP: begin
          if (mem_rdata != '0) fail <= 1'b1;
          mem_we <= 1'b1;
          mem_wdata <= '1;
          if (&addr) begin
            addr <= '1;
            state <= READ_ONE_WRITE_ZERO_DOWN;
          end else begin
            addr <= addr + 1'b1;
          end
        end
        READ_ONE_WRITE_ZERO_DOWN: begin
          if (mem_rdata != '1) fail <= 1'b1;
          mem_we <= 1'b1;
          mem_wdata <= '0;
          if (addr == '0) begin
            addr <= '1;
            state <= READ_ZERO_DOWN;
          end else begin
            addr <= addr - 1'b1;
          end
        end
        READ_ZERO_DOWN: begin
          if (mem_rdata != '0) fail <= 1'b1;
          if (addr == '0) state <= DONE;
          else addr <= addr - 1'b1;
        end
        DONE: begin
          done <= 1'b1;
          if (!start) state <= IDLE;
        end
        default: state <= IDLE;
      endcase
    end
  end
endmodule
