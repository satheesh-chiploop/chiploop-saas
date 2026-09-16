module aero_history_logger(
    clk,
    reset_n,
    status_valid,
    status_code,
    fault_latched,
    host_cmd_valid,
    host_cmd_opcode,
    host_cmd_data,
    sensor_airdata_valid,
    sensor_airspeed,
    sensor_altitude,
    sensor_angle_of_attack,
    sensor_gload,
    history_csb_n,
    history_we_n,
    history_addr,
    history_din,
    history_dout,
    history_commit_valid,
    history_commit_tag
);
input clk;
input reset_n;
input status_valid;
input [7:0] status_code;
input fault_latched;
input host_cmd_valid;
input [7:0] host_cmd_opcode;
input [31:0] host_cmd_data;
input sensor_airdata_valid;
input [15:0] sensor_airspeed;
input [15:0] sensor_altitude;
input [15:0] sensor_angle_of_attack;
input [15:0] sensor_gload;
output reg history_csb_n;
output reg history_we_n;
output reg [7:0] history_addr;
output reg [31:0] history_din;
input [31:0] history_dout;
output reg history_commit_valid;
output reg [7:0] history_commit_tag;
reg [7:0] hist_ptr;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        history_csb_n <= 1'b1;
        history_we_n <= 1'b1;
        history_addr <= 8'h00;
        history_din <= 32'h00000000;
        history_commit_valid <= 1'b0;
        history_commit_tag <= 8'h00;
        hist_ptr <= 8'h00;
    end else begin
        history_commit_valid <= status_valid | host_cmd_valid | sensor_airdata_valid | fault_latched;
        history_commit_tag <= status_code ^ host_cmd_opcode;
        history_csb_n <= ~(status_valid | host_cmd_valid | sensor_airdata_valid | fault_latched);
        history_we_n <= ~(host_cmd_valid | sensor_airdata_valid);
        history_addr <= hist_ptr;
        history_din <= {status_code, host_cmd_opcode, sensor_airspeed[7:0], sensor_altitude[7:0]} ^ history_dout;
        if (status_valid | host_cmd_valid | sensor_airdata_valid | fault_latched) begin
            hist_ptr <= hist_ptr + 8'h01;
        end
    end
end

endmodule
