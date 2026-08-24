//      // verilator_coverage annotation
        module adaptive_aero_control_top (
 000026     input clk,
+000026  point: type=toggle comment=clk:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000025  point: type=toggle comment=clk:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001     input reset_n,
+000001  point: type=toggle comment=reset_n:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=reset_n:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001     input [7:0] mmio_addr,
+000001  point: type=toggle comment=mmio_addr[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_addr[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_addr[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_addr[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_addr[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_addr[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_addr[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input [31:0] mmio_wdata,
-000000  point: type=toggle comment=mmio_wdata[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_wdata[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input mmio_valid,
-000000  point: type=toggle comment=mmio_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input mmio_write,
-000000  point: type=toggle comment=mmio_write:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_write:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001     output [31:0] mmio_rdata,
-000000  point: type=toggle comment=mmio_rdata[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=mmio_rdata[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_rdata[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output mmio_ready,
-000000  point: type=toggle comment=mmio_ready:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=mmio_ready:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output model_req_valid,
-000000  point: type=toggle comment=model_req_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output [63:0] model_req_data,
-000000  point: type=toggle comment=model_req_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input model_req_ready,
-000000  point: type=toggle comment=model_req_ready:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_req_ready:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input model_rsp_valid,
-000000  point: type=toggle comment=model_rsp_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input [63:0] model_rsp_data,
-000000  point: type=toggle comment=model_rsp_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001     output model_rsp_ready,
+000001  point: type=toggle comment=model_rsp_ready:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=model_rsp_ready:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output actuator_cmd_valid,
-000000  point: type=toggle comment=actuator_cmd_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output [15:0] actuator_cmd_data,
-000000  point: type=toggle comment=actuator_cmd_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     input actuator_cmd_ready,
-000000  point: type=toggle comment=actuator_cmd_ready:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=actuator_cmd_ready:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output fault_latched,
-000000  point: type=toggle comment=fault_latched:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=fault_latched:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000     output status_valid,
-000000  point: type=toggle comment=status_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001     output [31:0] status_data
-000000  point: type=toggle comment=status_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=status_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
        );
%000000 wire cfg_enable;
-000000  point: type=toggle comment=cfg_enable:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_enable:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [1:0] cfg_mode;
-000000  point: type=toggle comment=cfg_mode[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_mode[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_mode[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_mode[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001 wire [15:0] cfg_timeout_cycles;
-000000  point: type=toggle comment=cfg_timeout_cycles[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_timeout_cycles[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_timeout_cycles[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [15:0] cfg_command_min;
-000000  point: type=toggle comment=cfg_command_min[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_min[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001 wire [15:0] cfg_command_max;
+000001  point: type=toggle comment=cfg_command_max[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_command_max[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_command_max[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001 wire [15:0] cfg_speed_min;
-000000  point: type=toggle comment=cfg_speed_min[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_min[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_min[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_min[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001 wire [15:0] cfg_speed_max;
+000001  point: type=toggle comment=cfg_speed_max[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_max[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_max[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_max[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_speed_max[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_speed_max[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [7:0] cfg_model_req_tag;
-000000  point: type=toggle comment=cfg_model_req_tag[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_req_tag[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
~000001 wire [15:0] cfg_model_timeout_cycles;
-000000  point: type=toggle comment=cfg_model_timeout_cycles[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire cfg_history_capture_en;
-000000  point: type=toggle comment=cfg_history_capture_en:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_history_capture_en:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire cfg_fault_clear;
-000000  point: type=toggle comment=cfg_fault_clear:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=cfg_fault_clear:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_fault_latched;
-000000  point: type=toggle comment=status_fault_latched:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_fault_latched:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_timeout;
-000000  point: type=toggle comment=status_timeout:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_timeout:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_stale;
-000000  point: type=toggle comment=status_stale:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_stale:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_response_valid;
-000000  point: type=toggle comment=status_response_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_response_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_actuator_valid;
-000000  point: type=toggle comment=status_actuator_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_actuator_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire status_speed_valid;
-000000  point: type=toggle comment=status_speed_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [15:0] status_speed_raw;
-000000  point: type=toggle comment=status_speed_raw[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_speed_raw[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [15:0] status_command_raw;
-000000  point: type=toggle comment=status_command_raw[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=status_command_raw[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire history_wr_en;
-000000  point: type=toggle comment=history_wr_en:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_en:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [63:0] history_wr_data;
-000000  point: type=toggle comment=history_wr_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [7:0] history_wr_addr;
-000000  point: type=toggle comment=history_wr_addr[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_wr_addr[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [7:0] history_rd_addr;
-000000  point: type=toggle comment=history_rd_addr[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_addr[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire history_rd_en;
-000000  point: type=toggle comment=history_rd_en:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_en:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [63:0] history_rd_data;
-000000  point: type=toggle comment=history_rd_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=history_rd_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
        
%000000 wire adaptive_aero_controller_core_status_response_valid;
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_response_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_response_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire [15:0] adaptive_aero_controller_core_status_speed_raw;
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_raw[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire adaptive_aero_controller_core_status_speed_valid;
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_speed_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire adaptive_aero_controller_core_status_stale;
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_stale:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_stale:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
%000000 wire adaptive_aero_controller_core_status_timeout;
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_timeout:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core
-000000  point: type=toggle comment=adaptive_aero_controller_core_status_timeout:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core
        adaptive_aero_mmio_csr u_mmio_csr (
            .clk(clk),
            .reset_n(reset_n),
            .mmio_addr(mmio_addr),
            .mmio_wdata(mmio_wdata),
            .mmio_valid(mmio_valid),
            .mmio_write(mmio_write),
            .mmio_rdata(mmio_rdata),
            .mmio_ready(mmio_ready),
            .cfg_enable(cfg_enable),
            .cfg_mode(cfg_mode),
            .cfg_timeout_cycles(cfg_timeout_cycles),
            .cfg_command_min(cfg_command_min),
            .cfg_command_max(cfg_command_max),
            .cfg_speed_min(cfg_speed_min),
            .cfg_speed_max(cfg_speed_max),
            .cfg_model_req_tag(cfg_model_req_tag),
            .cfg_model_timeout_cycles(cfg_model_timeout_cycles),
            .cfg_history_capture_en(cfg_history_capture_en),
            .cfg_fault_clear(cfg_fault_clear),
            .status_fault_latched(status_fault_latched),
            .status_timeout(status_timeout),
            .status_stale(status_stale),
            .status_response_valid(status_response_valid),
            .status_actuator_valid(status_actuator_valid),
            .status_speed_valid(status_speed_valid),
            .status_speed_raw(status_speed_raw),
            .status_command_raw(status_command_raw)
        );
        
        adaptive_aero_controller_core u_controller_core (
            .clk(clk),
            .reset_n(reset_n),
            .cfg_enable(cfg_enable),
            .cfg_mode(cfg_mode),
            .cfg_timeout_cycles(cfg_timeout_cycles),
            .cfg_command_min(cfg_command_min),
            .cfg_command_max(cfg_command_max),
            .cfg_speed_min(cfg_speed_min),
            .cfg_speed_max(cfg_speed_max),
            .cfg_model_req_tag(cfg_model_req_tag),
            .cfg_model_timeout_cycles(cfg_model_timeout_cycles),
            .cfg_history_capture_en(cfg_history_capture_en),
            .cfg_fault_clear(cfg_fault_clear),
            .model_rsp_valid(model_rsp_valid),
            .model_rsp_data(model_rsp_data),
            .model_rsp_ready(model_rsp_ready),
            .command_valid(actuator_cmd_valid),
            .command_data(actuator_cmd_data),
            .fault_latched(fault_latched),
            .status_timeout(status_timeout),
            .status_stale(status_stale),
            .status_response_valid(status_response_valid),
            .status_actuator_valid(status_actuator_valid),
            .status_speed_valid(status_speed_valid),
            .status_speed_raw(status_speed_raw),
            .status_command_raw(status_command_raw),
            .history_wr_en(history_wr_en),
            .history_wr_data(history_wr_data),
            .history_wr_addr(history_wr_addr)
        );
        
        adaptive_aero_history_store u_history_store (
            .clk(clk),
            .reset_n(reset_n),
            .wr_en(history_wr_en),
            .wr_addr(history_wr_addr),
            .wr_data(history_wr_data),
            .rd_addr(history_rd_addr),
            .rd_data(history_rd_data),
            .rd_en(history_rd_en)
        );
        
        assign model_req_valid = actuator_cmd_valid;
        assign model_req_data = {48'd0, actuator_cmd_data};
        assign status_valid = mmio_ready;
        assign status_data = mmio_rdata;
        assign history_rd_addr = cfg_model_req_tag;
        assign history_rd_en = cfg_history_capture_en;
        
        assign status_fault_latched = fault_latched;
        
        endmodule
        
