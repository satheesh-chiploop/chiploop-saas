TOPLEVEL_LANG = verilog
TOPLEVEL = pwm_controller
MODULE = test_firmware_smoke
SIM ?= verilator

ifeq ($(SIM),verilator)
EXTRA_ARGS += -Wno-fatal -Wno-CASEINCOMPLETE
endif

VERILOG_SOURCES = \
	digital/rtl/pwm_controller.v

include $(shell cocotb-config --makefiles)/Makefile.sim
