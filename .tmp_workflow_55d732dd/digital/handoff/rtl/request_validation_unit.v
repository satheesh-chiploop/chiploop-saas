module request_validation_unit (
    input clk_rst_n,
    input req_stream_valid,
    input [127:0] req_stream_data,
    output reg accepted_o,
    output reg rejected_o,
    output reg stale_o,
    output reg [15:0] request_id_o,
    output reg [3:0] protocol_version_o,
    output reg [3:0] request_type_o,
    output reg [7:0] service_selector_o,
    output reg [15:0] geometry_handle_o,
    output reg [7:0] stream_velocity_mps_o,
    output reg [7:0] flags_o
);
    reg [15:0] last_request_id_r;

    always @(posedge clk_rst_n or negedge clk_rst_n) begin
        if (!clk_rst_n) begin
            accepted_o <= 1'b0;
            rejected_o <= 1'b0;
            stale_o <= 1'b0;
            request_id_o <= 16'h0000;
            protocol_version_o <= 4'h0;
            request_type_o <= 4'h0;
            service_selector_o <= 8'h00;
            geometry_handle_o <= 16'h0000;
            stream_velocity_mps_o <= 8'h00;
            flags_o <= 8'h00;
            last_request_id_r <= 16'h0000;
        end else begin
            accepted_o <= 1'b0;
            rejected_o <= 1'b0;
            stale_o <= 1'b0;
            if (req_stream_valid) begin
                request_id_o <= req_stream_data[15:0];
                protocol_version_o <= req_stream_data[19:16];
                request_type_o <= req_stream_data[23:20];
                service_selector_o <= req_stream_data[31:24];
                geometry_handle_o <= req_stream_data[47:32];
                stream_velocity_mps_o <= req_stream_data[55:48];
                flags_o <= req_stream_data[63:56];
                if ((req_stream_data[19:16] == 4'h1) &&
                    ((req_stream_data[23:20] & 4'hF) != 4'h0) &&
                    (req_stream_data[55:48] >= 8'd20) &&
                    (req_stream_data[55:48] <= 8'd55)) begin
                    if (req_stream_data[15:0] < last_request_id_r) begin
                        stale_o <= 1'b1;
                        rejected_o <= 1'b1;
                    end else begin
                        accepted_o <= 1'b1;
                        last_request_id_r <= req_stream_data[15:0];
                    end
                end else begin
                    rejected_o <= 1'b1;
                end
            end
        end
    end
endmodule
