# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 64
- Matched: 57
- Partial: 0
- Missing: 7
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-001 [missing]: Capture and register configuration metadata for geometry source, format, and ID.
- REQ-004 [missing]: Drive a valid request bundle to the external surrogate using explicit transaction ports.
- REQ-009 [missing]: Synthesize an actuator command from validated model outputs using fixed-point policy logic.
- REQ-010 [missing]: Clamp actuator command to configurable bounds and optionally apply rate limiting.
- REQ-023 [missing]: Command synthesis shall be deterministic fixed-point combinational logic based on validated model outputs; the RTL shall not model surrogate physics.
- REQ-031 [missing]: No combinational loops, X-dependent control, or asynchronous recovery behavior are permitted.
