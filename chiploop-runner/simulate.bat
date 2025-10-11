:: simulate.bat
@echo off
setlocal
set DESIGN_PATH=%1
set TOP_MODULE=%2
set OUTPUT_DIR=%3

if "%OUTPUT_DIR%"=="" set OUTPUT_DIR=sim_results

mkdir %OUTPUT_DIR%
cd %OUTPUT_DIR%

vlib work
vlog -sv "%DESIGN_PATH%\*.sv" "%DESIGN_PATH%\*.v"
vsim -c -coverage %TOP_MODULE% -do "run -all; coverage save -onexit coverage.ucdb; exit"
vcover report -details coverage.ucdb > coverage_report.txt

echo Simulation
