# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 68
- Matched: 50
- Partial: 4
- Missing: 14
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-002 [missing]: Assemble model_request_out semantics through explicit request output ports.
- REQ-004 [missing]: Track a single outstanding request and its age.
- REQ-006 [partial]: Accept only matching, valid, and fresh model responses.
- REQ-008 [missing]: Capture compact response metadata including drag, lift, surface_pressure summary, and flow_field token.
- REQ-009 [missing]: Generate deterministic actuator command setpoints from validated responses and flow conditions.
- REQ-010 [missing]: Clamp commands to CMD_MIN and CMD_MAX and optionally rate-limit delta per cycle.
- REQ-012 [missing]: Expose system status flags for safety, integration, and verification.
- REQ-013 [missing]: Never bypass safety checks with model-derived commands.
- REQ-020 [missing]: The response validation filter shall verify identity, completeness, and freshness before command synthesis may use the response fields.
- REQ-022 [missing]: The synthesized command shall be registered before the clamp stage.
- REQ-024 [missing]: If rate limiting is enabled by parameterization, setpoint delta per cycle shall not exceed RATE_MAX_DELTA.
- REQ-025 [partial]: Rate-limited or clamped commands shall remain valid and safe for downstream actuation.
- REQ-028 [missing]: Final actuator outputs shall be registered before driving actuator_cmd_out ports.
- REQ-029 [partial]: valid shall reflect the final decision that a command is valid for use this cycle.
- REQ-030 [partial]: busy shall reflect whether an outstanding request is active.
- REQ-032 [missing]: The IP shall not instantiate any physics inference engine, neural network, GPU worker, or transport protocol.
- REQ-033 [missing]: The IP shall not use unbounded loops, dynamic allocation, file I/O, or real-number arithmetic.
