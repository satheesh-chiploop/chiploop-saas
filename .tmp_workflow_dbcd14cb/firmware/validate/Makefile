TOPLEVEL_LANG = verilog
TOPLEVEL = temp_monitor_soc_sim
MODULE = test_firmware_smoke
SIM ?= verilator

ifeq ($(SIM),verilator)
EXTRA_ARGS += -Wno-fatal -Wno-CASEINCOMPLETE
endif

VERILOG_SOURCES = \
	digital/rtl/temp_monitor_digital.v

include $(shell cocotb-config --makefiles)/Makefile.sim
