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
  localparam integer INPUT_BITS = 204;
  localparam integer OUTPUT_BITS = 197;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_cfg_valid;
  logic core_cfg_write;
  logic [7:0] core_cfg_addr;
  logic [31:0] core_cfg_wdata;
  logic [31:0] core_veh_speed_mps;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [127:0] core_model_rsp_data;
  wire [31:0] core_cfg_rdata;
  wire core_cfg_ready;
  wire core_model_req_valid;
  wire [127:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_aero_actuator_valid;
  wire [31:0] core_aero_actuator_cmd;
  wire core_status_irq;
  assign core_cfg_valid = rx_active[0 +: 1];
  assign core_cfg_write = rx_active[1 +: 1];
  assign core_cfg_addr = rx_active[2 +: 8];
  assign core_cfg_wdata = rx_active[10 +: 32];
  assign core_veh_speed_mps = rx_active[42 +: 32];
  assign core_model_req_ready = rx_active[74 +: 1];
  assign core_model_rsp_valid = rx_active[75 +: 1];
  assign core_model_rsp_data = rx_active[76 +: 128];
  wire [OUTPUT_BITS-1:0] core_response = {core_cfg_rdata, core_cfg_ready, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_aero_actuator_valid, core_aero_actuator_cmd, core_status_irq};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[202:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[195:0], 1'b0};
      else tx_shift <= {tx_shift[195:0], 1'b0};
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
    .rst_n(reset_n),
    .cfg_valid(core_cfg_valid),
    .cfg_write(core_cfg_write),
    .cfg_addr(core_cfg_addr),
    .cfg_wdata(core_cfg_wdata),
    .cfg_rdata(core_cfg_rdata),
    .cfg_ready(core_cfg_ready),
    .veh_speed_mps(core_veh_speed_mps),
    .model_req_valid(core_model_req_valid),
    .model_req_ready(core_model_req_ready),
    .model_req_data(core_model_req_data),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_ready(core_model_rsp_ready),
    .model_rsp_data(core_model_rsp_data),
    .aero_actuator_valid(core_aero_actuator_valid),
    .aero_actuator_cmd(core_aero_actuator_cmd),
    .status_irq(core_status_irq)
  );
endmodule
