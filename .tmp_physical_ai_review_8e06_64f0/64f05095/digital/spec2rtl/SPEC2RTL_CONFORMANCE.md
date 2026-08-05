# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 84
- Matched: 63
- Partial: 1
- Missing: 20
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-001 [missing]: Fan out clock and reset to all submodules.
- REQ-002 [missing]: Provide top-level request/response/actuator/fault interfaces.
- REQ-003 [missing]: Hold all outputs safe on reset and while configuration is incomplete.
- REQ-004 [missing]: Enforce request sequencing and freshness supervision.
- REQ-005 [missing]: Prevent any direct bypass from model response to actuator output.
- REQ-007 [partial]: All sequential state is synchronous to clk.
- REQ-008 [missing]: No local physics or neural inference is performed.
- REQ-010 [missing]: Every request carries request_id and timestamp/cycle-age metadata.
- REQ-013 [missing]: Command synthesis shall use deterministic fixed-point arithmetic only.
- REQ-016 [missing]: Sticky fault state remains asserted until cleared by the defined clear mechanism.
- REQ-064 [missing]: Sequence request issuance.
- REQ-065 [missing]: Preserve request/response transaction correlation fields.
- REQ-066 [missing]: Provide bounded transaction tracking.
- REQ-069 [missing]: Carry request_id and timestamp in every request.
- REQ-070 [missing]: Accept geometry and flow only when both are valid and the controller is configured.
- REQ-071 [missing]: Do not generate or transform any physics-model inference data.
- REQ-072 [missing]: Timeout detection is synchronous and deterministic.
- REQ-073 [missing]: Request payload format is bounded-width and architecture-defined.
- REQ-079 [missing]: Enforce request/response correlation.
- REQ-080 [missing]: Qualify valid responses only after ID and freshness checks.
