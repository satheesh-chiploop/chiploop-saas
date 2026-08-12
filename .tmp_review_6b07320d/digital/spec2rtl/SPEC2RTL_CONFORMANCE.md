# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 84
- Matched: 80
- Partial: 1
- Missing: 3
- Inconclusive: 0
- Interface: pass
- Register map: pass
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-002 [missing]: Generate one-cycle pulses for SAMPLE_START, ALERT_CLEAR, and IRQ_CLEAR bits.
- REQ-029 [missing]: IRQ_CLEAR bit 1 clears IRQ_STATUS.sample_done and STATUS.sample_done.
- REQ-048 [partial]: CONTROL bit 0 is a stored level bit.
- REQ-059 [missing]: One-cycle pulses must not self-stretch.
