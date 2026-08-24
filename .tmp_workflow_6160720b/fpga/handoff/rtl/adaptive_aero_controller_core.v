//      // verilator_coverage annotation
        module adaptive_aero_controller_core (
 000026     input clk,
+000026  point: type=toggle comment=clk:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=toggle comment=clk:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input reset_n,
+000001  point: type=toggle comment=reset_n:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=reset_n:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input cfg_enable,
-000000  point: type=toggle comment=cfg_enable:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_enable:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input [1:0] cfg_mode,
-000000  point: type=toggle comment=cfg_mode[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_mode[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_mode[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_mode[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input [15:0] cfg_timeout_cycles,
-000000  point: type=toggle comment=cfg_timeout_cycles[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_timeout_cycles[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_timeout_cycles[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input [15:0] cfg_command_min,
-000000  point: type=toggle comment=cfg_command_min[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_min[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input [15:0] cfg_command_max,
+000001  point: type=toggle comment=cfg_command_max[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_command_max[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_command_max[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input [15:0] cfg_speed_min,
-000000  point: type=toggle comment=cfg_speed_min[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_min[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_min[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_min[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input [15:0] cfg_speed_max,
+000001  point: type=toggle comment=cfg_speed_max[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_max[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_max[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_max[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_speed_max[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_speed_max[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input [7:0] cfg_model_req_tag,
-000000  point: type=toggle comment=cfg_model_req_tag[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_req_tag[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     input [15:0] cfg_model_timeout_cycles,
-000000  point: type=toggle comment=cfg_model_timeout_cycles[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=cfg_model_timeout_cycles[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_model_timeout_cycles[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input cfg_history_capture_en,
-000000  point: type=toggle comment=cfg_history_capture_en:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_history_capture_en:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input cfg_fault_clear,
-000000  point: type=toggle comment=cfg_fault_clear:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cfg_fault_clear:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input model_rsp_valid,
-000000  point: type=toggle comment=model_rsp_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     input [63:0] model_rsp_data,
-000000  point: type=toggle comment=model_rsp_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001     output reg model_rsp_ready,
+000001  point: type=toggle comment=model_rsp_ready:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_rsp_ready:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg command_valid,
-000000  point: type=toggle comment=command_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg [15:0] command_data,
-000000  point: type=toggle comment=command_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=command_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg fault_latched,
-000000  point: type=toggle comment=fault_latched:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=fault_latched:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg status_timeout,
-000000  point: type=toggle comment=status_timeout:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_timeout:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg status_stale,
-000000  point: type=toggle comment=status_stale:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_stale:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg status_response_valid,
-000000  point: type=toggle comment=status_response_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_response_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg status_actuator_valid,
-000000  point: type=toggle comment=status_actuator_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_actuator_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg status_speed_valid,
-000000  point: type=toggle comment=status_speed_valid:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_valid:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg [15:0] status_speed_raw,
-000000  point: type=toggle comment=status_speed_raw[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_speed_raw[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg [15:0] status_command_raw,
-000000  point: type=toggle comment=status_command_raw[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=status_command_raw[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg history_wr_en,
-000000  point: type=toggle comment=history_wr_en:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_en:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg [63:0] history_wr_data,
-000000  point: type=toggle comment=history_wr_data[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[16]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[16]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[17]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[17]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[18]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[18]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[19]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[19]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[20]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[20]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[21]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[21]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[22]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[22]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[23]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[23]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[24]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[24]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[25]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[25]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[26]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[26]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[27]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[27]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[28]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[28]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[29]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[29]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[30]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[30]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[31]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[31]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[32]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[32]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[33]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[33]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[34]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[34]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[35]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[35]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[36]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[36]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[37]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[37]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[38]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[38]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[39]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[39]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[40]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[40]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[41]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[41]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[42]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[42]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[43]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[43]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[44]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[44]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[45]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[45]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[46]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[46]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[47]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[47]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[48]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[48]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[49]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[49]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[50]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[50]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[51]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[51]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[52]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[52]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[53]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[53]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[54]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[54]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[55]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[55]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[56]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[56]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[57]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[57]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[58]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[58]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[59]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[59]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[60]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[60]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[61]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[61]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[62]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[62]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[63]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[63]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_data[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000     output reg [7:0] history_wr_addr
-000000  point: type=toggle comment=history_wr_addr[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_wr_addr[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
        );
        
%000000 reg [15:0] speed_sample_reg;
-000000  point: type=toggle comment=speed_sample_reg[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=speed_sample_reg[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 reg [15:0] response_cmd_reg;
-000000  point: type=toggle comment=response_cmd_reg[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_cmd_reg[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000013 reg [15:0] age_counter_reg;
+000013  point: type=toggle comment=age_counter_reg[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000012  point: type=toggle comment=age_counter_reg[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000006  point: type=toggle comment=age_counter_reg[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000006  point: type=toggle comment=age_counter_reg[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000003  point: type=toggle comment=age_counter_reg[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000003  point: type=toggle comment=age_counter_reg[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000002  point: type=toggle comment=age_counter_reg[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=age_counter_reg[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=age_counter_reg[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=age_counter_reg[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 reg [7:0] history_ptr_reg;
-000000  point: type=toggle comment=history_ptr_reg[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=history_ptr_reg[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 reg seen_response_reg;
-000000  point: type=toggle comment=seen_response_reg:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=seen_response_reg:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
        
%000000 wire [15:0] model_speed_sample;
-000000  point: type=toggle comment=model_speed_sample[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_speed_sample[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 wire [7:0] model_tag_sample;
-000000  point: type=toggle comment=model_tag_sample[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_tag_sample[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 wire [15:0] model_cmd_sample;
-000000  point: type=toggle comment=model_cmd_sample[0]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[0]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[10]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[10]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[11]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[11]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[12]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[12]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[13]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[13]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[14]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[14]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[15]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[15]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[1]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[1]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[2]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[2]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[3]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[3]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[4]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[4]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[5]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[5]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[6]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[6]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[7]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[7]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[8]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[8]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[9]:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=model_cmd_sample[9]:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001 wire speed_in_range;
+000001  point: type=toggle comment=speed_in_range:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=speed_in_range:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001 wire cmd_in_range;
+000001  point: type=toggle comment=cmd_in_range:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=cmd_in_range:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001 wire timeout_hit;
+000001  point: type=toggle comment=timeout_hit:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=toggle comment=timeout_hit:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000 wire stale_hit;
-000000  point: type=toggle comment=stale_hit:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=stale_hit:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000001 wire response_tag_ok;
+000001  point: type=toggle comment=response_tag_ok:0->1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=toggle comment=response_tag_ok:1->0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
        
        assign model_tag_sample = model_rsp_data[7:0];
        assign model_speed_sample = model_rsp_data[31:16];
        assign model_cmd_sample = model_rsp_data[47:32];
        assign speed_in_range = (model_speed_sample >= cfg_speed_min) && (model_speed_sample <= cfg_speed_max);
        assign cmd_in_range = (model_cmd_sample >= cfg_command_min) && (model_cmd_sample <= cfg_command_max);
        assign timeout_hit = (age_counter_reg >= cfg_timeout_cycles) || (age_counter_reg >= cfg_model_timeout_cycles);
        assign stale_hit = seen_response_reg && (age_counter_reg >= cfg_timeout_cycles);
        assign response_tag_ok = (model_tag_sample == cfg_model_req_tag);
        
 000026 always @(posedge clk or negedge reset_n) begin
+000026  point: type=line comment=block hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025     if (!reset_n) begin
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000001  point: type=expr comment=(reset_n==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=(reset_n==1) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         model_rsp_ready <= 1'b1;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         command_valid <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         command_data <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         fault_latched <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_timeout <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_stale <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_response_valid <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_actuator_valid <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_speed_valid <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_speed_raw <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         status_command_raw <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         history_wr_en <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         history_wr_data <= 64'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         history_wr_addr <= 8'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         speed_sample_reg <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         response_cmd_reg <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         age_counter_reg <= 16'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         history_ptr_reg <= 8'd0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000001         seen_response_reg <= 1'b0;
+000001  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025     end else begin
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025         model_rsp_ready <= 1'b1;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025         history_wr_en <= 1'b0;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025         if (cfg_fault_clear) fault_latched <= 1'b0;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025         if (model_rsp_valid && model_rsp_ready) begin
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(model_rsp_ready==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=(model_rsp_valid==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(model_rsp_valid==1 && model_rsp_ready==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             speed_sample_reg <= model_speed_sample;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             response_cmd_reg <= model_cmd_sample;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             seen_response_reg <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             age_counter_reg <= 16'd0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_response_valid <= response_tag_ok;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_speed_valid <= speed_in_range;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_speed_raw <= model_speed_sample;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_command_raw <= model_cmd_sample;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_stale <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             status_timeout <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             if (!cfg_enable || !response_tag_ok || !speed_in_range || !cmd_in_range) begin
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(cfg_enable==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(cfg_enable==1 && response_tag_ok==1 && speed_in_range==1 && cmd_in_range==1) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(cmd_in_range==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(response_tag_ok==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(speed_in_range==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 command_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 fault_latched <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_actuator_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000             end else begin
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 if (cfg_mode == 2'b00) command_data <= model_cmd_sample;
-000000  point: type=line comment=elsif hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 else if (cfg_mode == 2'b01) command_data <= (model_cmd_sample < cfg_command_min) ? cfg_command_min : model_cmd_sample;
-000000  point: type=branch comment=cond_then hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=cond_else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=line comment=elsif hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((model_cmd_sample < cfg_command_min)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((model_cmd_sample < cfg_command_min)==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 else if (cfg_mode == 2'b10) command_data <= (model_cmd_sample > cfg_command_max) ? cfg_command_max : model_cmd_sample;
-000000  point: type=branch comment=cond_then hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=cond_else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=line comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=line comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((model_cmd_sample > cfg_command_max)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((model_cmd_sample > cfg_command_max)==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 else command_data <= model_cmd_sample ^ cfg_model_req_tag;
-000000  point: type=line comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 if (command_data < cfg_command_min) command_data <= cfg_command_min;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 if (command_data > cfg_command_max) command_data <= cfg_command_max;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 command_valid <= 1'b1;
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_actuator_valid <= 1'b1;
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
%000000             if (cfg_history_capture_en) begin
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_en <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_data <= {16'b0, cfg_model_req_tag, model_tag_sample, model_speed_sample, model_cmd_sample};
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_addr <= history_ptr_reg;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_ptr_reg <= history_ptr_reg + 8'd1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
 000025         end else begin
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025             if (age_counter_reg != 16'hFFFF) age_counter_reg <= age_counter_reg + 16'd1;
+000025  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025             if (timeout_hit) begin
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_timeout <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 fault_latched <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 command_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_actuator_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
~000025             if (stale_hit) begin
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_stale <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 fault_latched <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 command_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 status_actuator_valid <= 1'b0;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
~000025             if (cfg_history_capture_en) begin
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_en <= 1'b1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_data <= {16'b0, cfg_model_req_tag, 8'hFF, speed_sample_reg, response_cmd_reg};
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_wr_addr <= history_ptr_reg;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
%000000                 history_ptr_reg <= history_ptr_reg + 8'd1;
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
 000025             status_response_valid <= 1'b0;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025             status_speed_valid <= (speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max);
-000000  point: type=expr comment=((speed_sample_reg <= cfg_speed_max)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=((speed_sample_reg >= cfg_speed_min)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((speed_sample_reg >= cfg_speed_min)==1 && (speed_sample_reg <= cfg_speed_max)==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025             status_speed_raw <= speed_sample_reg;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025             status_command_raw <= response_cmd_reg;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
~000025             if (!cfg_enable || fault_latched || timeout_hit || stale_hit || !((speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max))) begin
+000025  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((speed_sample_reg <= cfg_speed_max)==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=((speed_sample_reg >= cfg_speed_min)==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=(cfg_enable==0) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(cfg_enable==1 && fault_latched==0 && timeout_hit==0 && stale_hit==0 && (speed_sample_reg >= cfg_speed_min)==1 && (speed_sample_reg <= cfg_speed_max)==1) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(fault_latched==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(stale_hit==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(timeout_hit==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025                 command_valid <= 1'b0;
+000025  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
 000025                 status_actuator_valid <= 1'b0;
+000025  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
                    end
                end
~000025         if (cfg_fault_clear && !status_timeout && !status_stale && (speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max)) fault_latched <= 1'b0;
+000025  point: type=branch comment=else hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=((speed_sample_reg <= cfg_speed_max)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=((speed_sample_reg >= cfg_speed_min)==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
+000025  point: type=expr comment=(cfg_fault_clear==0) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(cfg_fault_clear==1 && status_timeout==0 && status_stale==0 && (speed_sample_reg >= cfg_speed_min)==1 && (speed_sample_reg <= cfg_speed_max)==1) => 1 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(status_stale==1) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=expr comment=(status_timeout==1) => 0 hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
-000000  point: type=branch comment=if hier=adaptive_aero_control_top_spi_fpga_top.u_core.u_controller_core
            end
        end
        
        endmodule
        
