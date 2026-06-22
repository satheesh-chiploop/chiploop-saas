TOPLEVEL_LANG = verilog
TOPLEVEL = pwm_controller
MODULE = test_firmware_smoke
SIM ?= verilator

ifeq ($(SIM),verilator)
EXTRA_ARGS += -Wno-fatal -Wno-CASEINCOMPLETE
endif

VERILOG_SOURCES = \
	digital/rtl/demo_sram_32x256_model.v

include $(shell cocotb-config --makefiles)/Makefile.sim
