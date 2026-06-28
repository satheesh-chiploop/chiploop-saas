import cocotb
from cocotb.triggers import Timer

# ASSUMPTION: No clock-like input was detected on the generated top.
# ASSUMPTION: Firmware preload / runtime stimulus will be integrated later.

@cocotb.test()
async def firmware_smoke(dut):
    await Timer(1, units="us")
