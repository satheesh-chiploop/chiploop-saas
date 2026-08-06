# Spec-to-RTL Conformance Report

Status: **partial**

- Requirements checked: 84
- Matched: 73
- Partial: 2
- Missing: 9
- Inconclusive: 0
- Interface: pass
- Register map: issues
- Clock/reset: pass

## Missing Or Partial Requirements
- REQ-001 [missing]: Qualify outbound model requests using input-validity, envelope, and fallback-routing rules.
- REQ-003 [missing]: Accept only matching, fresh, well-formed responses.
- REQ-008 [missing]: Guarantee registered actuator command output with no combinational path from response inputs to actuator outputs.
- REQ-015 [missing]: Command synthesis shall be deterministic and parameterizable for active-aerodynamics actuator domain scaling, but shall not perform physics inference.
- REQ-046 [missing]: Package geometry reference and stream velocity into the outbound request payload.
- REQ-051 [missing]: The request payload shall include transaction identifiers, geometry reference, and flow/velocity context in a deterministic encoded format.
- REQ-069 [missing]: Assert explicit stale, invalid, and timeout indicators for supervisory consumption.
- REQ-070 [partial]: Provide normalized model-output words only on accepted responses.
- REQ-072 [partial]: Any failure of ID, sequence, format, or age checks shall be flagged as stale or invalid and shall not update accepted model output data.
- REQ-074 [missing]: No output word derived from a rejected response may be used by command synthesis.
