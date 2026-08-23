module stream_rx (
    input clk,
    input rst_n,
    input req_valid,
    input [127:0] req_data,
    output reg req_ready,
    output reg rx_pkt_valid,
    output reg [15:0] rx_pkt_seq,
    output reg [15:0] rx_pkt_timestamp,
    output reg [3:0] rx_pkt_cmd_type,
    output reg [7:0] rx_pkt_vel_bin,
    output reg [15:0] rx_pkt_geom_ref,
    output reg [7:0] rx_pkt_integrity,
    output reg [15:0] rx_pkt_age
);

wire [15:0] payload_seq;
wire [15:0] payload_timestamp;
wire [3:0] payload_cmd_type;
wire [7:0] payload_vel_bin;
wire [15:0] payload_geom_ref;
wire [7:0] payload_integrity;
wire [15:0] payload_age;
wire req_fire;

assign payload_seq = req_data[15:0];
assign payload_timestamp = req_data[31:16];
assign payload_cmd_type = req_data[35:32];
assign payload_vel_bin = req_data[43:36];
assign payload_geom_ref = req_data[59:44];
assign payload_integrity = req_data[67:60];
assign payload_age = req_data[83:68];
assign req_fire = req_valid && req_ready;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        req_ready <= 1'b1;
        rx_pkt_valid <= 1'b0;
        rx_pkt_seq <= 16'h0000;
        rx_pkt_timestamp <= 16'h0000;
        rx_pkt_cmd_type <= 4'h0;
        rx_pkt_vel_bin <= 8'h00;
        rx_pkt_geom_ref <= 16'h0000;
        rx_pkt_integrity <= 8'h00;
        rx_pkt_age <= 16'h0000;
    end else begin
        req_ready <= 1'b1;
        rx_pkt_valid <= req_fire;
        if (req_fire) begin
            rx_pkt_seq <= payload_seq;
            rx_pkt_timestamp <= payload_timestamp;
            rx_pkt_cmd_type <= payload_cmd_type;
            rx_pkt_vel_bin <= payload_vel_bin;
            rx_pkt_geom_ref <= payload_geom_ref;
            rx_pkt_integrity <= payload_integrity;
            rx_pkt_age <= payload_age;
        end
    end
end

endmodule
