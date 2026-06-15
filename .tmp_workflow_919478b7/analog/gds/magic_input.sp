.lib "$PDK_ROOT/sky130A/libs.tech/ngspice/sky130.lib.spice" tt
.subckt temp_sensor_adc_model "adc_code[0]" "adc_code[10]" "adc_code[11]" "adc_code[1]" "adc_code[2]" "adc_code[3]" "adc_code[4]" "adc_code[5]" "adc_code[6]" "adc_code[7]" "adc_code[8]" "adc_code[9]" "sensor_temp_celsius[0]" "sensor_temp_celsius[10]" "sensor_temp_celsius[11]" "sensor_temp_celsius[12]" "sensor_temp_celsius[13]" "sensor_temp_celsius[14]" "sensor_temp_celsius[15]" "sensor_temp_celsius[1]" "sensor_temp_celsius[2]" "sensor_temp_celsius[3]" "sensor_temp_celsius[4]" "sensor_temp_celsius[5]" "sensor_temp_celsius[6]" "sensor_temp_celsius[7]" "sensor_temp_celsius[8]" "sensor_temp_celsius[9]" VGND VPWR adc_code[0] adc_code[10] adc_code[11] adc_code[1] adc_code[2] adc_code[3] adc_code[4] adc_code[5] adc_code[6] adc_code[7] adc_code[8] adc_code[9] adc_valid avdd avss sample_req sensor_temp_celsius[0] sensor_temp_celsius[10] sensor_temp_celsius[11] sensor_temp_celsius[12] sensor_temp_celsius[13] sensor_temp_celsius[14] sensor_temp_celsius[15] sensor_temp_celsius[1] sensor_temp_celsius[2] sensor_temp_celsius[3] sensor_temp_celsius[4] sensor_temp_celsius[5] sensor_temp_celsius[6] sensor_temp_celsius[7] sensor_temp_celsius[8] sensor_temp_celsius[9]
Mbuf0 adc_valid sample_req avdd avdd sky130_fd_pr__pfet_01v8 W=1 L=0.15
Mbuf1 adc_valid sample_req avss avss sky130_fd_pr__nfet_01v8 W=1 L=0.15
Mcode0 "adc_code[0]" sensor_temp_celsius[0] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode1 "adc_code[1]" sensor_temp_celsius[1] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode2 "adc_code[2]" sensor_temp_celsius[2] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode3 "adc_code[3]" sensor_temp_celsius[3] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode4 "adc_code[4]" sensor_temp_celsius[4] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode5 "adc_code[5]" sensor_temp_celsius[5] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode6 "adc_code[6]" sensor_temp_celsius[6] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode7 "adc_code[7]" sensor_temp_celsius[7] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode8 "adc_code[8]" sensor_temp_celsius[8] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode9 "adc_code[9]" sensor_temp_celsius[9] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode10 "adc_code[10]" sensor_temp_celsius[10] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mcode11 "adc_code[11]" sensor_temp_celsius[11] avdd avdd sky130_fd_pr__pfet_01v8 W=0.84 L=0.15
Mpull0 "adc_code[0]" sensor_temp_celsius[0] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull1 "adc_code[1]" sensor_temp_celsius[1] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull2 "adc_code[2]" sensor_temp_celsius[2] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull3 "adc_code[3]" sensor_temp_celsius[3] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull4 "adc_code[4]" sensor_temp_celsius[4] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull5 "adc_code[5]" sensor_temp_celsius[5] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull6 "adc_code[6]" sensor_temp_celsius[6] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull7 "adc_code[7]" sensor_temp_celsius[7] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull8 "adc_code[8]" sensor_temp_celsius[8] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull9 "adc_code[9]" sensor_temp_celsius[9] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull10 "adc_code[10]" sensor_temp_celsius[10] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpull11 "adc_code[11]" sensor_temp_celsius[11] avss avss sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
.ends temp_sensor_adc_model
.end
