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
  localparam integer INPUT_BITS = 170;
  localparam integer OUTPUT_BITS = 198;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_in_cmd_valid;
  logic [63:0] core_in_cmd_data;
  logic core_out_act_ready;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [63:0] core_model_rsp_data;
  logic core_cfg_valid;
  logic core_cfg_write;
  logic [3:0] core_cfg_addr;
  logic [31:0] core_cfg_wdata;
  wire core_in_cmd_ready;
  wire core_out_act_valid;
  wire [63:0] core_out_act_data;
  wire core_model_req_valid;
  wire [63:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire [31:0] core_cfg_rdata;
  wire core_cfg_ready;
  wire core_status_valid;
  wire [31:0] core_status_data;
  assign core_in_cmd_valid = rx_active[0 +: 1];
  assign core_in_cmd_data = rx_active[1 +: 64];
  assign core_out_act_ready = rx_active[65 +: 1];
  assign core_model_req_ready = rx_active[66 +: 1];
  assign core_model_rsp_valid = rx_active[67 +: 1];
  assign core_model_rsp_data = rx_active[68 +: 64];
  assign core_cfg_valid = rx_active[132 +: 1];
  assign core_cfg_write = rx_active[133 +: 1];
  assign core_cfg_addr = rx_active[134 +: 4];
  assign core_cfg_wdata = rx_active[138 +: 32];
  wire [OUTPUT_BITS-1:0] core_response = {core_in_cmd_ready, core_out_act_valid, core_out_act_data, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_cfg_rdata, core_cfg_ready, core_status_valid, core_status_data};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[168:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[196:0], 1'b0};
      else tx_shift <= {tx_shift[196:0], 1'b0};
    end
  end
  // Synchronize frame completion into the core clock domain. The host
  // keeps MOSI stable around CS rising as required by the protocol.
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      spi_cs_meta <= 1'b1; spi_cs_sync <= 1'b1; spi_cs_prev <= 1'b1;
      rx_active <= '0; tx_snapshot <= '0;
    end else begin
      spi_cs_meta <= spi_cs_n; spi_cs_sync <= spi_cs_meta; spi_cs_prev <= spi_cs_sync;
      if (spi_cs_sync && !spi_cs_prev) rx_active <= rx_shift;
      tx_snapshot <= core_response;
    end
  end
  always_comb spi_miso = spi_active ? tx_shift[OUTPUT_BITS-1] : tx_snapshot[OUTPUT_BITS-1];
  adaptive_aero_control_top u_core (
    .clk(clk),
    .reset_n(reset_n),
    .in_cmd_valid(core_in_cmd_valid),
    .in_cmd_data(core_in_cmd_data),
    .in_cmd_ready(core_in_cmd_ready),
    .out_act_valid(core_out_act_valid),
    .out_act_data(core_out_act_data),
    .out_act_ready(core_out_act_ready),
    .model_req_valid(core_model_req_valid),
    .model_req_data(core_model_req_data),
    .model_req_ready(core_model_req_ready),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_data(core_model_rsp_data),
    .model_rsp_ready(core_model_rsp_ready),
    .cfg_valid(core_cfg_valid),
    .cfg_write(core_cfg_write),
    .cfg_addr(core_cfg_addr),
    .cfg_wdata(core_cfg_wdata),
    .cfg_rdata(core_cfg_rdata),
    .cfg_ready(core_cfg_ready),
    .status_valid(core_status_valid),
    .status_data(core_status_data)
  );
endmodule
