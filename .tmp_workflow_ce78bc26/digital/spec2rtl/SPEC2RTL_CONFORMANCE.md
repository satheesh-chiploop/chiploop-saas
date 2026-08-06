# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 84
- Matched: 72
- Partial: 1
- Missing: 11
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-004 [missing]: Prevent issuance of model requests when any safety criterion fails.
- REQ-005 [missing]: Ensure all top-level outputs are driven by registered logic only.
- REQ-006 [partial]: Every externally visible state update is synchronous to clk.
- REQ-036 [missing]: No combinational propagation of raw geometry inputs to any later stage is permitted without registered capture.
- REQ-048 [missing]: All comparisons are synchronous and fixed-width; no floating-point or non-synthesizable logic is used.
- REQ-054 [missing]: Maintain a monotonic request_id counter.
- REQ-055 [missing]: Capture and hold request timestamp for freshness comparisons.
- REQ-064 [missing]: A single internal free-running counter or equivalent synchronous timebase shall supply request_timestamp values.
- REQ-075 [missing]: Validate response structure and freshness conditions.
- REQ-076 [missing]: Provide explicit model output fields as opaque control inputs.
- REQ-077 [missing]: Suppress invalid or stale responses from reaching the policy stage.
