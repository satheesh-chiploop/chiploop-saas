module pwm_controller (clk,
    pwm_out,
    rd_en,
    reset_n,
    scan_en,
    wr_en,
    counter_value,
    rd_addr,
    rd_data,
    scan_in,
    scan_out,
    wr_addr,
    wr_data);
 input clk;
 output pwm_out;
 input rd_en;
 input reset_n;
 input scan_en;
 input wr_en;
 output [7:0] counter_value;
 input [7:0] rd_addr;
 output [7:0] rd_data;
 input [3:0] scan_in;
 output [3:0] scan_out;
 input [7:0] wr_addr;
 input [7:0] wr_data;

 wire _000_;
 wire _001_;
 wire _002_;
 wire _003_;
 wire _004_;
 wire _005_;
 wire _006_;
 wire _007_;
 wire _008_;
 wire _009_;
 wire _010_;
 wire _011_;
 wire _012_;
 wire _013_;
 wire _014_;
 wire _015_;
 wire _016_;
 wire _017_;
 wire _018_;
 wire _019_;
 wire _020_;
 wire _021_;
 wire _022_;
 wire _023_;
 wire _024_;
 wire _025_;
 wire _026_;
 wire _027_;
 wire _028_;
 wire _029_;
 wire _030_;
 wire _031_;
 wire _032_;
 wire _033_;
 wire _034_;
 wire _035_;
 wire _036_;
 wire _037_;
 wire _038_;
 wire _039_;
 wire _040_;
 wire _041_;
 wire _042_;
 wire _043_;
 wire _044_;
 wire _045_;
 wire _046_;
 wire _047_;
 wire _048_;
 wire _049_;
 wire _050_;
 wire _051_;
 wire _052_;
 wire _053_;
 wire _054_;
 wire _055_;
 wire _056_;
 wire _057_;
 wire _058_;
 wire _059_;
 wire _060_;
 wire _061_;
 wire _062_;
 wire _063_;
 wire _064_;
 wire _065_;
 wire _066_;
 wire _067_;
 wire _068_;
 wire _069_;
 wire _070_;
 wire _071_;
 wire _072_;
 wire _073_;
 wire _074_;
 wire _075_;
 wire _076_;
 wire _077_;
 wire _078_;
 wire _079_;
 wire _080_;
 wire _081_;
 wire _082_;
 wire _083_;
 wire _084_;
 wire _085_;
 wire _086_;
 wire _087_;
 wire _088_;
 wire _089_;
 wire _090_;
 wire _091_;
 wire _092_;
 wire _093_;
 wire _094_;
 wire _095_;
 wire _096_;
 wire _097_;
 wire _098_;
 wire _099_;
 wire _100_;
 wire _101_;
 wire _102_;
 wire _103_;
 wire _104_;
 wire _105_;
 wire _106_;
 wire _107_;
 wire _108_;
 wire _109_;
 wire _110_;
 wire _111_;
 wire _112_;
 wire \duty_cycle[0] ;
 wire \duty_cycle[1] ;
 wire \duty_cycle[2] ;
 wire \duty_cycle[3] ;
 wire \duty_cycle[4] ;
 wire \duty_cycle[5] ;
 wire \duty_cycle[6] ;
 wire \duty_cycle[7] ;
 wire enable;
 wire \period[0] ;
 wire \period[1] ;
 wire \period[2] ;
 wire \period[3] ;
 wire \period[4] ;
 wire \period[5] ;
 wire \period[6] ;
 wire \period[7] ;

 sky130_fd_sc_hd__a22o_2 _113_ (.A1(counter_value[7]),
    .A2(_112_),
    .B1(_033_),
    .B2(\period[7] ),
    .X(_050_));
 sky130_fd_sc_hd__o21a_2 _114_ (.A1(_049_),
    .A2(_050_),
    .B1(rd_en),
    .X(_007_));
 sky130_fd_sc_hd__a22o_2 _115_ (.A1(_104_),
    .A2(\duty_cycle[6] ),
    .B1(\duty_cycle[7] ),
    .B2(_105_),
    .X(_051_));
 sky130_fd_sc_hd__a22o_2 _116_ (.A1(_102_),
    .A2(\duty_cycle[4] ),
    .B1(\duty_cycle[5] ),
    .B2(_103_),
    .X(_052_));
 sky130_fd_sc_hd__and2b_2 _117_ (.A_N(counter_value[1]),
    .B(\duty_cycle[1] ),
    .X(_053_));
 sky130_fd_sc_hd__nand2b_2 _118_ (.A_N(\duty_cycle[1] ),
    .B(counter_value[1]),
    .Y(_054_));
 sky130_fd_sc_hd__and2b_2 _119_ (.A_N(counter_value[0]),
    .B(\duty_cycle[0] ),
    .X(_055_));
 sky130_fd_sc_hd__o221a_2 _120_ (.A1(_100_),
    .A2(\duty_cycle[2] ),
    .B1(_053_),
    .B2(_055_),
    .C1(_054_),
    .X(_056_));
 sky130_fd_sc_hd__a22o_2 _121_ (.A1(_100_),
    .A2(\duty_cycle[2] ),
    .B1(\duty_cycle[3] ),
    .B2(_101_),
    .X(_057_));
 sky130_fd_sc_hd__o22a_2 _122_ (.A1(_101_),
    .A2(\duty_cycle[3] ),
    .B1(\duty_cycle[4] ),
    .B2(_102_),
    .X(_058_));
 sky130_fd_sc_hd__o21a_2 _123_ (.A1(_056_),
    .A2(_057_),
    .B1(_058_),
    .X(_059_));
 sky130_fd_sc_hd__or2_2 _124_ (.A(_103_),
    .B(\duty_cycle[5] ),
    .X(_060_));
 sky130_fd_sc_hd__o221a_2 _125_ (.A1(_104_),
    .A2(\duty_cycle[6] ),
    .B1(_052_),
    .B2(_059_),
    .C1(_060_),
    .X(_061_));
 sky130_fd_sc_hd__o221a_2 _126_ (.A1(_105_),
    .A2(\duty_cycle[7] ),
    .B1(_051_),
    .B2(_061_),
    .C1(enable),
    .X(pwm_out));
 sky130_fd_sc_hd__or3_2 _127_ (.A(wr_addr[5]),
    .B(wr_addr[4]),
    .C(wr_addr[7]),
    .X(_062_));
 sky130_fd_sc_hd__or3b_2 _128_ (.A(_062_),
    .B(wr_addr[6]),
    .C_N(wr_en),
    .X(_063_));
 sky130_fd_sc_hd__or2_2 _129_ (.A(wr_addr[2]),
    .B(_063_),
    .X(_064_));
 sky130_fd_sc_hd__or4_2 _130_ (.A(wr_addr[1]),
    .B(wr_addr[0]),
    .C(wr_addr[3]),
    .D(_064_),
    .X(_065_));
 sky130_fd_sc_hd__mux2_1 _131_ (.A0(wr_data[0]),
    .A1(enable),
    .S(_065_),
    .X(_008_));
 sky130_fd_sc_hd__or4b_2 _132_ (.A(wr_addr[1]),
    .B(wr_addr[0]),
    .C(wr_addr[3]),
    .D_N(wr_addr[2]),
    .X(_066_));
 sky130_fd_sc_hd__or2_2 _133_ (.A(_063_),
    .B(_066_),
    .X(_067_));
 sky130_fd_sc_hd__mux2_1 _134_ (.A0(wr_data[0]),
    .A1(\duty_cycle[0] ),
    .S(_067_),
    .X(_009_));
 sky130_fd_sc_hd__mux2_1 _135_ (.A0(wr_data[1]),
    .A1(\duty_cycle[1] ),
    .S(_067_),
    .X(_010_));
 sky130_fd_sc_hd__mux2_1 _136_ (.A0(wr_data[2]),
    .A1(\duty_cycle[2] ),
    .S(_067_),
    .X(_011_));
 sky130_fd_sc_hd__mux2_1 _137_ (.A0(wr_data[3]),
    .A1(\duty_cycle[3] ),
    .S(_067_),
    .X(_012_));
 sky130_fd_sc_hd__mux2_1 _138_ (.A0(wr_data[4]),
    .A1(\duty_cycle[4] ),
    .S(_067_),
    .X(_013_));
 sky130_fd_sc_hd__mux2_1 _139_ (.A0(wr_data[5]),
    .A1(\duty_cycle[5] ),
    .S(_067_),
    .X(_014_));
 sky130_fd_sc_hd__mux2_1 _140_ (.A0(wr_data[6]),
    .A1(\duty_cycle[6] ),
    .S(_067_),
    .X(_015_));
 sky130_fd_sc_hd__mux2_1 _141_ (.A0(wr_data[7]),
    .A1(\duty_cycle[7] ),
    .S(_067_),
    .X(_016_));
 sky130_fd_sc_hd__or4_2 _142_ (.A(\period[5] ),
    .B(\period[4] ),
    .C(\period[7] ),
    .D(\period[6] ),
    .X(_068_));
 sky130_fd_sc_hd__or4_2 _143_ (.A(\period[1] ),
    .B(\period[0] ),
    .C(\period[3] ),
    .D(\period[2] ),
    .X(_069_));
 sky130_fd_sc_hd__o21ai_2 _144_ (.A1(_068_),
    .A2(_069_),
    .B1(enable),
    .Y(_070_));
 sky130_fd_sc_hd__xor2_2 _145_ (.A(\period[4] ),
    .B(counter_value[4]),
    .X(_071_));
 sky130_fd_sc_hd__xor2_2 _146_ (.A(\period[1] ),
    .B(counter_value[1]),
    .X(_072_));
 sky130_fd_sc_hd__xor2_2 _147_ (.A(\period[3] ),
    .B(counter_value[3]),
    .X(_073_));
 sky130_fd_sc_hd__xor2_2 _148_ (.A(\period[7] ),
    .B(counter_value[7]),
    .X(_074_));
 sky130_fd_sc_hd__or4_2 _149_ (.A(_071_),
    .B(_072_),
    .C(_073_),
    .D(_074_),
    .X(_075_));
 sky130_fd_sc_hd__xor2_2 _150_ (.A(\period[0] ),
    .B(counter_value[0]),
    .X(_076_));
 sky130_fd_sc_hd__xor2_2 _151_ (.A(\period[6] ),
    .B(counter_value[6]),
    .X(_077_));
 sky130_fd_sc_hd__xor2_2 _152_ (.A(\period[5] ),
    .B(counter_value[5]),
    .X(_078_));
 sky130_fd_sc_hd__xor2_2 _153_ (.A(\period[2] ),
    .B(counter_value[2]),
    .X(_079_));
 sky130_fd_sc_hd__or4_2 _154_ (.A(_076_),
    .B(_077_),
    .C(_078_),
    .D(_079_),
    .X(_080_));
 sky130_fd_sc_hd__or3_2 _155_ (.A(_070_),
    .B(_075_),
    .C(_080_),
    .X(_081_));
 sky130_fd_sc_hd__o211a_2 _156_ (.A1(_068_),
    .A2(_069_),
    .B1(enable),
    .C1(counter_value[0]),
    .X(_082_));
 sky130_fd_sc_hd__a21bo_2 _157_ (.A1(_099_),
    .A2(_070_),
    .B1_N(_081_),
    .X(_083_));
 sky130_fd_sc_hd__nor2_2 _158_ (.A(_082_),
    .B(_083_),
    .Y(_017_));
 sky130_fd_sc_hd__and2_2 _159_ (.A(counter_value[0]),
    .B(counter_value[1]),
    .X(_084_));
 sky130_fd_sc_hd__and2_2 _160_ (.A(counter_value[1]),
    .B(_082_),
    .X(_085_));
 sky130_fd_sc_hd__o21ai_2 _161_ (.A1(counter_value[1]),
    .A2(_082_),
    .B1(_081_),
    .Y(_086_));
 sky130_fd_sc_hd__nor2_2 _162_ (.A(_085_),
    .B(_086_),
    .Y(_018_));
 sky130_fd_sc_hd__nand2_2 _163_ (.A(counter_value[2]),
    .B(_085_),
    .Y(_087_));
 sky130_fd_sc_hd__o211a_2 _164_ (.A1(counter_value[2]),
    .A2(_085_),
    .B1(_087_),
    .C1(_081_),
    .X(_019_));
 sky130_fd_sc_hd__and2_2 _165_ (.A(counter_value[2]),
    .B(counter_value[3]),
    .X(_088_));
 sky130_fd_sc_hd__o2111a_2 _166_ (.A1(_068_),
    .A2(_069_),
    .B1(_084_),
    .C1(_088_),
    .D1(enable),
    .X(_089_));
 sky130_fd_sc_hd__inv_2 _167_ (.A(_089_),
    .Y(_090_));
 sky130_fd_sc_hd__nand2_2 _168_ (.A(_081_),
    .B(_090_),
    .Y(_091_));
 sky130_fd_sc_hd__a21oi_2 _169_ (.A1(_101_),
    .A2(_087_),
    .B1(_091_),
    .Y(_020_));
 sky130_fd_sc_hd__or2_2 _170_ (.A(counter_value[4]),
    .B(_089_),
    .X(_092_));
 sky130_fd_sc_hd__o211a_2 _171_ (.A1(_102_),
    .A2(_090_),
    .B1(_092_),
    .C1(_081_),
    .X(_021_));
 sky130_fd_sc_hd__a21o_2 _172_ (.A1(counter_value[4]),
    .A2(_089_),
    .B1(counter_value[5]),
    .X(_093_));
 sky130_fd_sc_hd__and3_2 _173_ (.A(counter_value[4]),
    .B(counter_value[5]),
    .C(_089_),
    .X(_094_));
 sky130_fd_sc_hd__inv_2 _174_ (.A(_094_),
    .Y(_095_));
 sky130_fd_sc_hd__and3_2 _175_ (.A(_081_),
    .B(_093_),
    .C(_095_),
    .X(_022_));
 sky130_fd_sc_hd__or2_2 _176_ (.A(counter_value[6]),
    .B(_094_),
    .X(_096_));
 sky130_fd_sc_hd__o211a_2 _177_ (.A1(_104_),
    .A2(_095_),
    .B1(_096_),
    .C1(_081_),
    .X(_023_));
 sky130_fd_sc_hd__a21o_2 _178_ (.A1(counter_value[6]),
    .A2(_094_),
    .B1(counter_value[7]),
    .X(_097_));
 sky130_fd_sc_hd__o311a_2 _179_ (.A1(_104_),
    .A2(_105_),
    .A3(_095_),
    .B1(_097_),
    .C1(_081_),
    .X(_024_));
 sky130_fd_sc_hd__nor4b_2 _180_ (.A(wr_addr[1]),
    .B(_064_),
    .C(wr_addr[0]),
    .D_N(wr_addr[3]),
    .Y(_098_));
 sky130_fd_sc_hd__mux2_1 _181_ (.A0(\period[0] ),
    .A1(wr_data[0]),
    .S(_098_),
    .X(_025_));
 sky130_fd_sc_hd__mux2_1 _182_ (.A0(\period[1] ),
    .A1(wr_data[1]),
    .S(_098_),
    .X(_026_));
 sky130_fd_sc_hd__mux2_1 _183_ (.A0(\period[2] ),
    .A1(wr_data[2]),
    .S(_098_),
    .X(_027_));
 sky130_fd_sc_hd__mux2_1 _184_ (.A0(\period[3] ),
    .A1(wr_data[3]),
    .S(_098_),
    .X(_028_));
 sky130_fd_sc_hd__mux2_1 _185_ (.A0(\period[4] ),
    .A1(wr_data[4]),
    .S(_098_),
    .X(_029_));
 sky130_fd_sc_hd__mux2_1 _186_ (.A0(\period[5] ),
    .A1(wr_data[5]),
    .S(_098_),
    .X(_030_));
 sky130_fd_sc_hd__mux2_1 _187_ (.A0(\period[6] ),
    .A1(wr_data[6]),
    .S(_098_),
    .X(_031_));
 sky130_fd_sc_hd__mux2_1 _188_ (.A0(\period[7] ),
    .A1(wr_data[7]),
    .S(_098_),
    .X(_032_));
 sky130_fd_sc_hd__inv_2 _189_ (.A(counter_value[0]),
    .Y(_099_));
 sky130_fd_sc_hd__inv_2 _190_ (.A(counter_value[2]),
    .Y(_100_));
 sky130_fd_sc_hd__inv_2 _191_ (.A(counter_value[3]),
    .Y(_101_));
 sky130_fd_sc_hd__inv_2 _192_ (.A(counter_value[4]),
    .Y(_102_));
 sky130_fd_sc_hd__inv_2 _193_ (.A(counter_value[5]),
    .Y(_103_));
 sky130_fd_sc_hd__inv_2 _194_ (.A(counter_value[6]),
    .Y(_104_));
 sky130_fd_sc_hd__inv_2 _195_ (.A(counter_value[7]),
    .Y(_105_));
 sky130_fd_sc_hd__inv_2 _196_ (.A(rd_addr[2]),
    .Y(_106_));
 sky130_fd_sc_hd__or3_2 _197_ (.A(rd_addr[1]),
    .B(rd_addr[0]),
    .C(rd_addr[3]),
    .X(_107_));
 sky130_fd_sc_hd__or4_2 _198_ (.A(rd_addr[5]),
    .B(rd_addr[4]),
    .C(rd_addr[7]),
    .D(rd_addr[6]),
    .X(_108_));
 sky130_fd_sc_hd__or2_2 _199_ (.A(_106_),
    .B(_108_),
    .X(_109_));
 sky130_fd_sc_hd__nor2_2 _200_ (.A(_107_),
    .B(_109_),
    .Y(_110_));
 sky130_fd_sc_hd__or3b_2 _201_ (.A(rd_addr[1]),
    .B(rd_addr[0]),
    .C_N(rd_addr[3]),
    .X(_111_));
 sky130_fd_sc_hd__nor2_2 _202_ (.A(_109_),
    .B(_111_),
    .Y(_112_));
 sky130_fd_sc_hd__nor3_2 _203_ (.A(rd_addr[2]),
    .B(_108_),
    .C(_111_),
    .Y(_033_));
 sky130_fd_sc_hd__or4b_2 _204_ (.A(rd_addr[2]),
    .B(_107_),
    .C(_108_),
    .D_N(enable),
    .X(_034_));
 sky130_fd_sc_hd__a21bo_2 _205_ (.A1(\period[0] ),
    .A2(_033_),
    .B1_N(_034_),
    .X(_035_));
 sky130_fd_sc_hd__a221o_2 _206_ (.A1(\duty_cycle[0] ),
    .A2(_110_),
    .B1(_112_),
    .B2(counter_value[0]),
    .C1(_035_),
    .X(_036_));
 sky130_fd_sc_hd__and2_2 _207_ (.A(rd_en),
    .B(_036_),
    .X(_000_));
 sky130_fd_sc_hd__and2_2 _208_ (.A(\duty_cycle[1] ),
    .B(_110_),
    .X(_037_));
 sky130_fd_sc_hd__a22o_2 _209_ (.A1(counter_value[1]),
    .A2(_112_),
    .B1(_033_),
    .B2(\period[1] ),
    .X(_038_));
 sky130_fd_sc_hd__o21a_2 _210_ (.A1(_037_),
    .A2(_038_),
    .B1(rd_en),
    .X(_001_));
 sky130_fd_sc_hd__and2_2 _211_ (.A(\period[2] ),
    .B(_033_),
    .X(_039_));
 sky130_fd_sc_hd__a221o_2 _212_ (.A1(\duty_cycle[2] ),
    .A2(_110_),
    .B1(_112_),
    .B2(counter_value[2]),
    .C1(_039_),
    .X(_040_));
 sky130_fd_sc_hd__and2_2 _213_ (.A(rd_en),
    .B(_040_),
    .X(_002_));
 sky130_fd_sc_hd__and2_2 _214_ (.A(\duty_cycle[3] ),
    .B(_110_),
    .X(_041_));
 sky130_fd_sc_hd__a22o_2 _215_ (.A1(counter_value[3]),
    .A2(_112_),
    .B1(_033_),
    .B2(\period[3] ),
    .X(_042_));
 sky130_fd_sc_hd__o21a_2 _216_ (.A1(_041_),
    .A2(_042_),
    .B1(rd_en),
    .X(_003_));
 sky130_fd_sc_hd__and2_2 _217_ (.A(\duty_cycle[4] ),
    .B(_110_),
    .X(_043_));
 sky130_fd_sc_hd__a22o_2 _218_ (.A1(counter_value[4]),
    .A2(_112_),
    .B1(_033_),
    .B2(\period[4] ),
    .X(_044_));
 sky130_fd_sc_hd__o21a_2 _219_ (.A1(_043_),
    .A2(_044_),
    .B1(rd_en),
    .X(_004_));
 sky130_fd_sc_hd__and2_2 _220_ (.A(counter_value[5]),
    .B(_112_),
    .X(_045_));
 sky130_fd_sc_hd__a22o_2 _221_ (.A1(\duty_cycle[5] ),
    .A2(_110_),
    .B1(_033_),
    .B2(\period[5] ),
    .X(_046_));
 sky130_fd_sc_hd__o21a_2 _222_ (.A1(_045_),
    .A2(_046_),
    .B1(rd_en),
    .X(_005_));
 sky130_fd_sc_hd__and2_2 _223_ (.A(counter_value[6]),
    .B(_112_),
    .X(_047_));
 sky130_fd_sc_hd__a22o_2 _224_ (.A1(\duty_cycle[6] ),
    .A2(_110_),
    .B1(_033_),
    .B2(\period[6] ),
    .X(_048_));
 sky130_fd_sc_hd__o21a_2 _225_ (.A1(_047_),
    .A2(_048_),
    .B1(rd_en),
    .X(_006_));
 sky130_fd_sc_hd__and2_2 _226_ (.A(\duty_cycle[7] ),
    .B(_110_),
    .X(_049_));
 sky130_fd_sc_hd__sdfrtp_2 _227_ (.CLK(clk),
    .D(_008_),
    .RESET_B(reset_n),
    .SCD(scan_in[0]),
    .SCE(scan_en),
    .Q(enable));
 sky130_fd_sc_hd__sdfrtp_2 _228_ (.CLK(clk),
    .D(_009_),
    .RESET_B(reset_n),
    .SCD(scan_in[1]),
    .SCE(scan_en),
    .Q(\duty_cycle[0] ));
 sky130_fd_sc_hd__sdfrtp_2 _229_ (.CLK(clk),
    .D(_010_),
    .RESET_B(reset_n),
    .SCD(scan_in[2]),
    .SCE(scan_en),
    .Q(\duty_cycle[1] ));
 sky130_fd_sc_hd__sdfrtp_2 _230_ (.CLK(clk),
    .D(_011_),
    .RESET_B(reset_n),
    .SCD(scan_in[3]),
    .SCE(scan_en),
    .Q(\duty_cycle[2] ));
 sky130_fd_sc_hd__sdfrtp_2 _231_ (.CLK(clk),
    .D(_012_),
    .RESET_B(reset_n),
    .SCD(enable),
    .SCE(scan_en),
    .Q(\duty_cycle[3] ));
 sky130_fd_sc_hd__sdfrtp_2 _232_ (.CLK(clk),
    .D(_013_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[0] ),
    .SCE(scan_en),
    .Q(\duty_cycle[4] ));
 sky130_fd_sc_hd__sdfrtp_2 _233_ (.CLK(clk),
    .D(_014_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[1] ),
    .SCE(scan_en),
    .Q(\duty_cycle[5] ));
 sky130_fd_sc_hd__sdfrtp_2 _234_ (.CLK(clk),
    .D(_015_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[2] ),
    .SCE(scan_en),
    .Q(\duty_cycle[6] ));
 sky130_fd_sc_hd__sdfrtp_2 _235_ (.CLK(clk),
    .D(_016_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[3] ),
    .SCE(scan_en),
    .Q(\duty_cycle[7] ));
 sky130_fd_sc_hd__sdfrtp_2 _236_ (.CLK(clk),
    .D(_017_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[4] ),
    .SCE(scan_en),
    .Q(counter_value[0]));
 sky130_fd_sc_hd__sdfrtp_2 _237_ (.CLK(clk),
    .D(_018_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[5] ),
    .SCE(scan_en),
    .Q(counter_value[1]));
 sky130_fd_sc_hd__sdfrtp_2 _238_ (.CLK(clk),
    .D(_019_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[6] ),
    .SCE(scan_en),
    .Q(counter_value[2]));
 sky130_fd_sc_hd__sdfrtp_2 _239_ (.CLK(clk),
    .D(_020_),
    .RESET_B(reset_n),
    .SCD(\duty_cycle[7] ),
    .SCE(scan_en),
    .Q(counter_value[3]));
 sky130_fd_sc_hd__sdfrtp_2 _240_ (.CLK(clk),
    .D(_021_),
    .RESET_B(reset_n),
    .SCD(counter_value[0]),
    .SCE(scan_en),
    .Q(counter_value[4]));
 sky130_fd_sc_hd__sdfrtp_2 _241_ (.CLK(clk),
    .D(_022_),
    .RESET_B(reset_n),
    .SCD(counter_value[1]),
    .SCE(scan_en),
    .Q(counter_value[5]));
 sky130_fd_sc_hd__sdfrtp_2 _242_ (.CLK(clk),
    .D(_023_),
    .RESET_B(reset_n),
    .SCD(counter_value[2]),
    .SCE(scan_en),
    .Q(counter_value[6]));
 sky130_fd_sc_hd__sdfrtp_2 _243_ (.CLK(clk),
    .D(_024_),
    .RESET_B(reset_n),
    .SCD(counter_value[3]),
    .SCE(scan_en),
    .Q(counter_value[7]));
 sky130_fd_sc_hd__sdfrtp_2 _244_ (.CLK(clk),
    .D(_000_),
    .RESET_B(reset_n),
    .SCD(counter_value[4]),
    .SCE(scan_en),
    .Q(rd_data[0]));
 sky130_fd_sc_hd__sdfrtp_2 _245_ (.CLK(clk),
    .D(_001_),
    .RESET_B(reset_n),
    .SCD(counter_value[5]),
    .SCE(scan_en),
    .Q(rd_data[1]));
 sky130_fd_sc_hd__sdfrtp_2 _246_ (.CLK(clk),
    .D(_002_),
    .RESET_B(reset_n),
    .SCD(counter_value[6]),
    .SCE(scan_en),
    .Q(rd_data[2]));
 sky130_fd_sc_hd__sdfrtp_2 _247_ (.CLK(clk),
    .D(_003_),
    .RESET_B(reset_n),
    .SCD(counter_value[7]),
    .SCE(scan_en),
    .Q(rd_data[3]));
 sky130_fd_sc_hd__sdfrtp_2 _248_ (.CLK(clk),
    .D(_004_),
    .RESET_B(reset_n),
    .SCD(rd_data[0]),
    .SCE(scan_en),
    .Q(rd_data[4]));
 sky130_fd_sc_hd__sdfrtp_2 _249_ (.CLK(clk),
    .D(_005_),
    .RESET_B(reset_n),
    .SCD(rd_data[1]),
    .SCE(scan_en),
    .Q(rd_data[5]));
 sky130_fd_sc_hd__sdfrtp_2 _250_ (.CLK(clk),
    .D(_006_),
    .RESET_B(reset_n),
    .SCD(rd_data[2]),
    .SCE(scan_en),
    .Q(rd_data[6]));
 sky130_fd_sc_hd__sdfrtp_2 _251_ (.CLK(clk),
    .D(_007_),
    .RESET_B(reset_n),
    .SCD(rd_data[3]),
    .SCE(scan_en),
    .Q(rd_data[7]));
 sky130_fd_sc_hd__sdfrtp_2 _252_ (.CLK(clk),
    .D(_025_),
    .RESET_B(reset_n),
    .SCD(rd_data[4]),
    .SCE(scan_en),
    .Q(\period[0] ));
 sky130_fd_sc_hd__sdfrtp_2 _253_ (.CLK(clk),
    .D(_026_),
    .RESET_B(reset_n),
    .SCD(rd_data[5]),
    .SCE(scan_en),
    .Q(\period[1] ));
 sky130_fd_sc_hd__sdfrtp_2 _254_ (.CLK(clk),
    .D(_027_),
    .RESET_B(reset_n),
    .SCD(rd_data[6]),
    .SCE(scan_en),
    .Q(\period[2] ));
 sky130_fd_sc_hd__sdfrtp_2 _255_ (.CLK(clk),
    .D(_028_),
    .RESET_B(reset_n),
    .SCD(rd_data[7]),
    .SCE(scan_en),
    .Q(\period[3] ));
 sky130_fd_sc_hd__sdfrtp_2 _256_ (.CLK(clk),
    .D(_029_),
    .RESET_B(reset_n),
    .SCD(\period[0] ),
    .SCE(scan_en),
    .Q(\period[4] ));
 sky130_fd_sc_hd__sdfrtp_2 _257_ (.CLK(clk),
    .D(_030_),
    .RESET_B(reset_n),
    .SCD(\period[1] ),
    .SCE(scan_en),
    .Q(\period[5] ));
 sky130_fd_sc_hd__sdfrtp_2 _258_ (.CLK(clk),
    .D(_031_),
    .RESET_B(reset_n),
    .SCD(\period[2] ),
    .SCE(scan_en),
    .Q(\period[6] ));
 sky130_fd_sc_hd__sdfrtp_2 _259_ (.CLK(clk),
    .D(_032_),
    .RESET_B(reset_n),
    .SCD(\period[3] ),
    .SCE(scan_en),
    .Q(\period[7] ));
 assign scan_out[1] = \period[4] ;
 assign scan_out[2] = \period[5] ;
 assign scan_out[3] = \period[6] ;
 assign scan_out[0] = \period[7] ;
endmodule
