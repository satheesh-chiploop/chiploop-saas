// Auto-generated FPGA-only serialized transport shell.
// The verified core RTL remains unchanged; ASIC flows continue to use the core top.
module adaptive_aero_control_top_spi_fpga_top (
  input  logic clk,
  input  logic reset_n,
  input  logic spi_sclk,
  input  logic spi_cs_n,
  input  logic spi_mosi,
  output logic spi_miso,
  output logic fault_indicator
);
  localparam integer INPUT_BITS = 172;
  localparam integer OUTPUT_BITS = 197;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift;
  logic core_cfg_we;
  logic core_cfg_re;
  logic [7:0] core_cfg_addr;
  logic [31:0] core_cfg_wdata;
  logic core_req_ready;
  logic core_resp_valid;
  logic [127:0] core_resp_data;
  wire [31:0] core_cfg_rdata;
  wire core_req_valid;
  wire [127:0] core_req_data;
  wire core_resp_ready;
  wire [31:0] core_actuator_cmd;
  wire core_actuator_valid;
  wire core_safe_fallback_active;
  wire core_model_timeout;
  assign core_cfg_we = rx_active[0 +: 1];
  assign core_cfg_re = rx_active[1 +: 1];
  assign core_cfg_addr = rx_active[2 +: 8];
  assign core_cfg_wdata = rx_active[10 +: 32];
  assign core_req_ready = rx_active[42 +: 1];
  assign core_resp_valid = rx_active[43 +: 1];
  assign core_resp_data = rx_active[44 +: 128];
  wire [OUTPUT_BITS-1:0] core_response = {core_cfg_rdata, core_req_valid, core_req_data, core_resp_ready, core_actuator_cmd, core_actuator_valid, core_safe_fallback_active, core_model_timeout};
  assign fault_indicator = 1'b0;
  always_ff @(posedge spi_sclk or posedge spi_cs_n or negedge reset_n) begin
    if (!reset_n) begin
      rx_shift <= '0; rx_active <= '0; tx_shift <= '0;
    end else if (spi_cs_n) begin
      rx_active <= rx_shift;
      tx_shift <= core_response;
    end else begin
      rx_shift <= {rx_shift[170:0], spi_mosi};
      tx_shift <= {tx_shift[195:0], 1'b0};
    end
  end
  always_comb spi_miso = tx_shift[OUTPUT_BITS-1];
  adaptive_aero_control_top u_core (
    .clk(clk),
    .rst_n(reset_n),
    .cfg_we(core_cfg_we),
    .cfg_re(core_cfg_re),
    .cfg_addr(core_cfg_addr),
    .cfg_wdata(core_cfg_wdata),
    .cfg_rdata(core_cfg_rdata),
    .req_valid(core_req_valid),
    .req_ready(core_req_ready),
    .req_data(core_req_data),
    .resp_valid(core_resp_valid),
    .resp_ready(core_resp_ready),
    .resp_data(core_resp_data),
    .actuator_cmd(core_actuator_cmd),
    .actuator_valid(core_actuator_valid),
    .safe_fallback_active(core_safe_fallback_active),
    .model_timeout(core_model_timeout)
  );
endmodule
