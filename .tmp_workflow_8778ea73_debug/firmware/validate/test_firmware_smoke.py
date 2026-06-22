import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

# ASSUMPTION: Only top-level DUT signals are used.
# ASSUMPTION: Firmware ELF preload is not yet wired into this smoke test.


async def _watchdog(dut, cycles=200):
    for _ in range(cycles):
        await RisingEdge(dut.clk)
    raise AssertionError("Watchdog timeout: smoke test made no visible progress")

async def reset_sequence(dut, cycles=10):
    # ASSUMPTION: No reset-like input was detected on the generated top.
    for _ in range(cycles):
        await RisingEdge(dut.clk)


@cocotb.test()
async def firmware_test(dut):
    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    cocotb.start_soon(_watchdog(dut, cycles=200))
    await reset_sequence(dut)
    for _ in range(20):
        await RisingEdge(dut.clk)
    await Timer(1, units="us")
