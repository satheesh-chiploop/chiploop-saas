.lib "$PDK_ROOT/sky130A/libs.tech/ngspice/sky130.lib.spice" tt
.subckt temp_sensor_adc_model "adc_code[0]" "adc_code[10]" "adc_code[11]" "adc_code[1]" "adc_code[2]" "adc_code[3]" "adc_code[4]" "adc_code[5]" "adc_code[6]" "adc_code[7]" "adc_code[8]" "adc_code[9]" "sensor_temp_celsius[0]" "sensor_temp_celsius[10]" "sensor_temp_celsius[11]" "sensor_temp_celsius[12]" "sensor_temp_celsius[13]" "sensor_temp_celsius[14]" "sensor_temp_celsius[15]" "sensor_temp_celsius[1]" "sensor_temp_celsius[2]" "sensor_temp_celsius[3]" "sensor_temp_celsius[4]" "sensor_temp_celsius[5]" "sensor_temp_celsius[6]" "sensor_temp_celsius[7]" "sensor_temp_celsius[8]" "sensor_temp_celsius[9]" VGND VPWR adc_code[0] adc_code[10] adc_code[11] adc_code[1] adc_code[2] adc_code[3] adc_code[4] adc_code[5] adc_code[6] adc_code[7] adc_code[8] adc_code[9] adc_valid avdd avss sample_req sensor_temp_celsius[0] sensor_temp_celsius[10] sensor_temp_celsius[11] sensor_temp_celsius[12] sensor_temp_celsius[13] sensor_temp_celsius[14] sensor_temp_celsius[15] sensor_temp_celsius[1] sensor_temp_celsius[2] sensor_temp_celsius[3] sensor_temp_celsius[4] sensor_temp_celsius[5] sensor_temp_celsius[6] sensor_temp_celsius[7] sensor_temp_celsius[8] sensor_temp_celsius[9]
Mpd0 adc_code[0] sample_req VPWR VPWR sky130_fd_pr__pfet_01v8 W=1 L=0.15
Mnd0 adc_code[0] sample_req VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd1 adc_code[1] sensor_temp_celsius[0] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1 L=0.15
Mnd1 adc_code[1] sensor_temp_celsius[0] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd2 adc_code[2] sensor_temp_celsius[1] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.2 L=0.15
Mnd2 adc_code[2] sensor_temp_celsius[1] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd3 adc_code[3] sensor_temp_celsius[2] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.2 L=0.15
Mnd3 adc_code[3] sensor_temp_celsius[2] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd4 adc_code[4] sensor_temp_celsius[3] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.4 L=0.15
Mnd4 adc_code[4] sensor_temp_celsius[3] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd5 adc_code[5] sensor_temp_celsius[4] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.4 L=0.15
Mnd5 adc_code[5] sensor_temp_celsius[4] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd6 adc_code[6] sensor_temp_celsius[5] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.6 L=0.15
Mnd6 adc_code[6] sensor_temp_celsius[5] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd7 adc_code[7] sensor_temp_celsius[6] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.6 L=0.15
Mnd7 adc_code[7] sensor_temp_celsius[6] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd8 adc_code[8] sensor_temp_celsius[7] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.8 L=0.15
Mnd8 adc_code[8] sensor_temp_celsius[7] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd9 adc_code[9] sensor_temp_celsius[8] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.8 L=0.15
Mnd9 adc_code[9] sensor_temp_celsius[8] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd10 adc_code[10] sensor_temp_celsius[9] VPWR VPWR sky130_fd_pr__pfet_01v8 W=2 L=0.15
Mnd10 adc_code[10] sensor_temp_celsius[9] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpd11 adc_code[11] sensor_temp_celsius[10] VPWR VPWR sky130_fd_pr__pfet_01v8 W=2 L=0.15
Mnd11 adc_code[11] sensor_temp_celsius[10] VGND VGND sky130_fd_pr__nfet_01v8 W=0.84 L=0.15
Mpuv adc_valid sample_req VPWR VPWR sky130_fd_pr__pfet_01v8 W=2.4 L=0.15
Mnuv adc_valid sensor_temp_celsius[11] VGND VGND sky130_fd_pr__nfet_01v8 W=1.2 L=0.15
Mpuv2 adc_valid sensor_temp_celsius[12] VPWR VPWR sky130_fd_pr__pfet_01v8 W=1.2 L=0.15
Mnuv2 adc_valid sample_req VGND VGND sky130_fd_pr__nfet_01v8 W=1.2 L=0.15
.ends temp_sensor_adc_model
.end
