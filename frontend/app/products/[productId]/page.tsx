"use client";

import { useEffect, useMemo, useState } from "react";
import { useParams, useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";
import SpecTextBox from "@/components/SpecTextBox";
import { apiDelete, apiGet, apiPatch, apiPost } from "@/lib/apiClient";

type Stage = {
  id: string;
  label: string;
  app: string;
  required?: boolean;
  recommended?: boolean;
  optional?: boolean;
  enabled?: boolean;
  settings?: Record<string, unknown>;
};

type Product = {
  id: string;
  name: string;
  product_type: string;
  starting_point: string;
  description: string;
  status: string;
  stage_config?: {
    source?: string;
    reference_slug?: string;
    stages?: Stage[];
  };
  stage_results?: Record<string, unknown>;
  updated_at?: string;
};

type ProductRun = {
  id: string;
  product_id: string;
  status: string;
  current_stage?: string | null;
  error?: string | null;
  stage_results?: Record<string, unknown>;
  logs?: string | null;
  created_at?: string;
  updated_at?: string;
  completed_at?: string | null;
};

type StageRun = {
  id: string;
  stage_id: string;
  stage_label: string;
  app: string;
  status: string;
  workflow_id?: string | null;
  run_id?: string | null;
  outputs?: Record<string, unknown> | null;
  error?: string | null;
  started_at?: string | null;
  completed_at?: string | null;
};

type ProductRunWithStages = ProductRun & {
  stage_runs?: StageRun[];
};

type StageOption = string | {
  value: string;
  label?: string;
  disabled?: boolean;
};

const APP_LINKS: Record<string, string> = {
  Digital_Arch2RTL: "/apps/arch2rtl",
  Digital_DQA: "/apps/dqa",
  Digital_Verify: "/apps/verify",
  Digital_Arch2Synthesis: "/apps/arch2synthesis",
  Digital_Arch2Tapeout: "/apps/arch2tapeout",
  verify_closure_loop: "/apps/verify",
  Embedded_Run: "/apps/embedded-run",
  System_Software: "/apps/system-software",
  System_Software_Validation_L2: "/apps/system-software-validation",
  System_Product_App_Builder: "/apps/system-product-builder",
  System_RTL: "/apps/system-rtl",
  System_DQA: "/apps/system-dqa",
  System_Sim: "/apps/system-sim",
  System_Synthesis: "/apps/system-synthesis",
  System_Firmware: "/apps/system-firmware",
  System_PD: "/apps/system-pd",
};

type StageField = {
  key: string;
  label: string;
  type: "text" | "number" | "boolean" | "select";
  defaultValue: string | number | boolean;
  required?: boolean;
  helper?: string;
  options?: StageOption[];
};

type StageSchema = {
  fields: StageField[];
  note?: string;
};

const FALLBACK_STAGE_SCHEMAS: Record<string, StageSchema> = {
  Digital_Arch2RTL: {
    note: "Spec text can be left blank only when the product description is detailed enough to use as the RTL spec.",
    fields: [
      { key: "project_name", label: "Project name", type: "text", defaultValue: "" },
      { key: "top_module", label: "Top module", type: "text", defaultValue: "" },
      { key: "design_language", label: "Design language", type: "text", defaultValue: "systemverilog" },
      { key: "spec_text", label: "Spec text", type: "text", defaultValue: "", helper: "Used before product description fallback." },
      { key: "enable_regmap", label: "Generate register map", type: "boolean", defaultValue: true },
      { key: "enable_upf_lite", label: "Generate UPF-lite", type: "boolean", defaultValue: false },
      { key: "enable_packaging", label: "Generate handoff package", type: "boolean", defaultValue: true },
      { key: "enable_scan_dft", label: "Enable scan/DFT intent", type: "boolean", defaultValue: false },
      { key: "insert_mbist", label: "Insert MBIST", type: "boolean", defaultValue: false },
      { key: "mbist_algorithm", label: "MBIST algorithm", type: "select", defaultValue: "march-c", options: ["march-c", "march-raw"] },
      { key: "run_spec2rtl_check", label: "Run Spec2RTL compliance check", type: "boolean", defaultValue: false },
      { key: "throughput_latency_targets", label: "Throughput/latency targets", type: "text", defaultValue: "" },
      { key: "power_priority", label: "Power priority", type: "text", defaultValue: "" },
    ],
  },
  Digital_DQA: {
    note: "DQA uses the Arch2RTL handoff and does not regenerate RTL.",
    fields: [
      { key: "run_lint", label: "Run lint", type: "boolean", defaultValue: true },
      { key: "run_cdc", label: "Run CDC", type: "boolean", defaultValue: true },
      { key: "run_reset", label: "Run reset integrity", type: "boolean", defaultValue: true },
      { key: "run_synthesis_readiness", label: "Run synthesis readiness", type: "boolean", defaultValue: true },
      { key: "lint_profile", label: "Lint profile", type: "text", defaultValue: "default" },
      { key: "cdc_profile", label: "CDC profile", type: "text", defaultValue: "default" },
      { key: "enable_autofix", label: "Enable autofix", type: "boolean", defaultValue: false },
    ],
  },
  Digital_Verify: {
    fields: [
      { key: "test_intent", label: "Test intent", type: "text", defaultValue: "Run smoke, reset, register access, and representative functional tests." },
      { key: "verification_plan", label: "Verification plan", type: "text", defaultValue: "" },
      { key: "monitor_checker_plan", label: "Monitor/checker plan", type: "text", defaultValue: "" },
      { key: "random_vs_directed", label: "Random vs directed", type: "select", defaultValue: "both", options: [
        { value: "both", label: "Directed then random" },
        { value: "directed", label: "Directed only" },
        { value: "random", label: "Random only" },
      ] },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional, 70% line" },
      { key: "coverage_plan", label: "Coverage plan", type: "text", defaultValue: "" },
      { key: "simulator_type", label: "Simulator", type: "select", defaultValue: "verilator", options: [
        { value: "verilator", label: "Verilator + Cocotb" },
        { value: "icarus", label: "Icarus Verilog (planned)", disabled: true },
        { value: "questa", label: "Questa (planned)", disabled: true },
        { value: "vcs", label: "VCS (planned)", disabled: true },
        { value: "xcelium", label: "Xcelium (planned)", disabled: true },
      ] },
      { key: "code_coverage_tool", label: "Code coverage tool", type: "select", defaultValue: "verilator_coverage", options: [
        { value: "verilator_coverage", label: "verilator_coverage" },
        { value: "none", label: "Disabled" },
        { value: "urg", label: "Synopsys URG (planned)", disabled: true },
        { value: "imc", label: "Cadence IMC (planned)", disabled: true },
        { value: "vcover", label: "Questa vcover (planned)", disabled: true },
      ] },
      { key: "formal_tool", label: "Formal tool", type: "select", defaultValue: "none", options: [
        { value: "none", label: "Disabled" },
        { value: "symbiyosys", label: "SymbiYosys (sby)" },
        { value: "jasper", label: "JasperGold (planned)", disabled: true },
        { value: "vc_formal", label: "VC Formal (planned)", disabled: true },
      ] },
      { key: "formal_solver", label: "Formal solver", type: "select", defaultValue: "z3", options: [
        { value: "z3", label: "Z3" },
        { value: "boolector", label: "Boolector" },
      ] },
      { key: "golden_model_tool", label: "Golden model tool", type: "select", defaultValue: "none", options: [
        { value: "none", label: "Disabled" },
        { value: "chiploop_python_scoreboard", label: "ChipLoop Python scoreboard" },
        { value: "custom_python", label: "Custom Python model (planned)", disabled: true },
        { value: "matlab", label: "MATLAB reference model (planned)", disabled: true },
      ] },
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 10 },
      { key: "run_closure_analysis", label: "Run closure analysis", type: "boolean", defaultValue: true },
      { key: "enable_failure_debug", label: "Run failure debug", type: "boolean", defaultValue: false },
      { key: "failure_debug_log_only_first", label: "Failure debug log-only first", type: "boolean", defaultValue: true },
      { key: "failure_debug_generate_vcd", label: "Generate VCD for failures", type: "boolean", defaultValue: true },
      { key: "failure_debug_auto_apply_tb", label: "Auto-apply TB fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_auto_apply_rtl", label: "Auto-apply RTL fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_rerun_failing", label: "Rerun failing tests", type: "boolean", defaultValue: true },
    ],
  },
  Digital_Arch2Synthesis: {
    note: "Synthesis uses the generated Arch2RTL handoff as RTL input and runs the synthesis stage directly.",
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130A" },
      { key: "toolchain", label: "Toolchain", type: "text", defaultValue: "openlane2" },
      { key: "target_frequency_mhz", label: "Target frequency MHz", type: "number", defaultValue: 100 },
      { key: "constraints_sdc", label: "Constraints SDC", type: "text", defaultValue: "" },
      { key: "run_logic_equivalence", label: "Run logic equivalence", type: "boolean", defaultValue: true },
      { key: "run_synthesis_readiness", label: "Run synthesis readiness", type: "boolean", defaultValue: true },
      { key: "run_synthesis_closure_loop", label: "Run synthesis closure loop", type: "boolean", defaultValue: false },
      { key: "max_synthesis_closure_iterations", label: "Max synthesis closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_synthesis_timing_repair", label: "Allow synthesis setup timing repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_lec_repair", label: "Allow synthesis LEC repair", type: "boolean", defaultValue: true },
      { key: "stop_on_synthesis_closure_failure", label: "Stop downstream on synthesis closure failure", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_lec_failure", label: "Stop downstream on synthesis LEC failure", type: "boolean", defaultValue: false },
    ],
  },
  Digital_Arch2Tapeout: {
    note: "Tapeout uses the generated Arch2RTL handoff as RTL input and runs synthesis through physical signoff.",
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130A" },
      { key: "toolchain", label: "Toolchain", type: "text", defaultValue: "openlane2" },
      { key: "target_frequency_mhz", label: "Target frequency MHz", type: "number", defaultValue: 100 },
      { key: "constraints_sdc", label: "Constraints SDC", type: "text", defaultValue: "" },
      { key: "effort", label: "Implementation effort", type: "select", defaultValue: "balanced", options: ["fast", "balanced", "signoff"] },
      { key: "run_fill", label: "Run fill", type: "boolean", defaultValue: true },
      { key: "run_drc", label: "Run DRC", type: "boolean", defaultValue: true },
      { key: "run_lvs", label: "Run LVS", type: "boolean", defaultValue: true },
      { key: "run_logic_equivalence", label: "Run logic equivalence", type: "boolean", defaultValue: true },
      { key: "run_signoff_closure_loop", label: "Run signoff closure loop", type: "boolean", defaultValue: false },
      { key: "max_signoff_closure_iterations", label: "Max signoff closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_timing_repair", label: "Allow timing repair", type: "boolean", defaultValue: true },
      { key: "allow_drc_repair", label: "Allow DRC repair", type: "boolean", defaultValue: true },
      { key: "allow_lvs_repair", label: "Allow LVS repair", type: "boolean", defaultValue: true },
      { key: "allow_lec_repair", label: "Allow LEC repair", type: "boolean", defaultValue: true },
      { key: "run_synthesis_closure_loop", label: "Run synthesis closure loop", type: "boolean", defaultValue: false },
      { key: "max_synthesis_closure_iterations", label: "Max synthesis closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_synthesis_timing_repair", label: "Allow synthesis setup timing repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_lec_repair", label: "Allow synthesis LEC repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_retiming", label: "Allow synthesis retiming", type: "boolean", defaultValue: false },
      { key: "allow_synthesis_hierarchy_flattening", label: "Allow synthesis hierarchy flattening", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_closure_failure", label: "Stop downstream on synthesis closure failure", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_lec_failure", label: "Stop downstream on synthesis LEC failure", type: "boolean", defaultValue: false },
    ],
  },
  System_RTL: {
    note: "System RTL starts from explicit digital, analog, and SoC specs. Downstream System apps auto-bind to this generated workflow.",
    fields: [
      { key: "digital_spec", label: "Digital spec", type: "text", defaultValue: "", required: true },
      { key: "analog_spec", label: "Analog spec", type: "text", defaultValue: "", required: true },
      { key: "soc_spec", label: "SoC spec", type: "text", defaultValue: "", required: true },
      { key: "enable_spec2rtl", label: "Spec2RTL check", type: "boolean", defaultValue: true },
    ],
  },
  System_Sim: {
    fields: [
      { key: "test_intent", label: "Test intent", type: "text", defaultValue: "Run integrated system smoke and register-path scenarios." },
      { key: "verification_plan", label: "Verification plan", type: "text", defaultValue: "" },
      { key: "monitor_checker_plan", label: "Monitor/checker plan", type: "text", defaultValue: "" },
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 6 },
      { key: "system_sim_testcases", label: "Testcases", type: "text", defaultValue: "system_smoke_test, integrated_input_sanity" },
      { key: "system_sim_seeds", label: "Seeds", type: "text", defaultValue: "1,2,3,4" },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional" },
      { key: "coverage_plan", label: "Coverage point plan", type: "text", defaultValue: "" },
      { key: "system_sim_num_iters", label: "Iteration budget", type: "number", defaultValue: 25 },
      { key: "simulator_type", label: "Simulator", type: "select", defaultValue: "verilator", options: [
        { value: "verilator", label: "verilator" },
        { value: "icarus", label: "icarus" },
      ] },
      { key: "code_coverage_tool", label: "Code coverage", type: "select", defaultValue: "verilator_coverage", options: [
        { value: "verilator_coverage", label: "verilator_coverage" },
        { value: "none", label: "Disabled" },
      ] },
      { key: "formal_tool", label: "Formal tool", type: "select", defaultValue: "none", options: [
        { value: "none", label: "Disabled" },
        { value: "symbiyosys", label: "SymbiYosys (sby)" },
      ] },
      { key: "formal_solver", label: "Formal solver", type: "select", defaultValue: "z3", options: [
        { value: "z3", label: "Z3" },
        { value: "boolector", label: "Boolector" },
      ] },
      { key: "golden_model_tool", label: "Golden model comparison", type: "select", defaultValue: "none", options: [
        { value: "none", label: "Disabled" },
        { value: "chiploop_python_scoreboard", label: "ChipLoop Python scoreboard" },
      ] },
      { key: "random_vs_directed", label: "Random vs directed", type: "select", defaultValue: "both", options: [
        { value: "both", label: "Directed then random" },
        { value: "directed", label: "Directed only" },
        { value: "random", label: "Random only" },
      ] },
      { key: "run_closure_analysis", label: "Run closure analysis", type: "boolean", defaultValue: false },
      { key: "enable_failure_debug", label: "Debug failing tests", type: "boolean", defaultValue: false },
      { key: "failure_debug_log_only_first", label: "Failure debug log-only first", type: "boolean", defaultValue: true },
      { key: "failure_debug_generate_vcd", label: "Generate VCD for failures", type: "boolean", defaultValue: true },
      { key: "failure_debug_auto_apply_tb", label: "Auto-apply TB fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_auto_apply_rtl", label: "Auto-apply RTL fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_rerun_failing", label: "Rerun failing tests", type: "boolean", defaultValue: true },
    ],
  },
  System_DQA: {
    note: "System DQA uses the System RTL handoff and does not rerun register-map generation.",
    fields: [
      { key: "run_lint", label: "Run lint", type: "boolean", defaultValue: true },
      { key: "run_cdc", label: "Run CDC", type: "boolean", defaultValue: true },
      { key: "run_reset", label: "Run reset integrity", type: "boolean", defaultValue: true },
      { key: "run_synthesis_readiness", label: "Run synthesis readiness", type: "boolean", defaultValue: true },
    ],
  },
  System_Firmware: {
    note: "Firmware auto-binds the System RTL workflow ID, including register-map and top-level handoff artifacts.",
    fields: [
      { key: "firmware_language", label: "Firmware language", type: "select", defaultValue: "rust", options: [
        { value: "rust", label: "Rust" },
        { value: "c", label: "C" },
      ] },
      { key: "validate_registers", label: "Validate registers", type: "boolean", defaultValue: true },
      { key: "enable_cosim", label: "Enable firmware co-sim", type: "boolean", defaultValue: true },
    ],
  },
  System_Synthesis: {
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130A" },
      { key: "toolchain", label: "Toolchain", type: "text", defaultValue: "openlane2" },
      { key: "target_frequency_mhz", label: "Target frequency MHz", type: "number", defaultValue: 100 },
      { key: "constraints_sdc", label: "Constraints SDC", type: "text", defaultValue: "" },
      { key: "run_spec2rtl_check", label: "Run Spec2RTL compliance check", type: "boolean", defaultValue: false },
      { key: "enable_scan_dft", label: "Enable scan/DFT intent", type: "boolean", defaultValue: false },
      { key: "run_synthesis_closure_loop", label: "Run synthesis closure loop", type: "boolean", defaultValue: false },
      { key: "max_synthesis_closure_iterations", label: "Max synthesis closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_synthesis_timing_repair", label: "Allow synthesis setup timing repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_lec_repair", label: "Allow synthesis LEC repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_retiming", label: "Allow synthesis retiming", type: "boolean", defaultValue: false },
      { key: "allow_synthesis_hierarchy_flattening", label: "Allow synthesis hierarchy flattening", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_closure_failure", label: "Stop downstream on synthesis closure failure", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_lec_failure", label: "Stop downstream on synthesis LEC failure", type: "boolean", defaultValue: false },
    ],
  },
  System_PD: {
    fields: [
      { key: "foundry", label: "Foundry", type: "text", defaultValue: "sky130" },
      { key: "pdk", label: "PDK", type: "text", defaultValue: "sky130A" },
      { key: "toolchain", label: "Toolchain", type: "text", defaultValue: "openlane2" },
      { key: "target_frequency_mhz", label: "Target frequency MHz", type: "number", defaultValue: 100 },
      { key: "constraints_sdc", label: "Constraints SDC", type: "text", defaultValue: "" },
      { key: "effort", label: "Implementation effort", type: "select", defaultValue: "balanced", options: ["fast", "balanced", "signoff"] },
      { key: "run_spec2rtl_check", label: "Run Spec2RTL compliance check", type: "boolean", defaultValue: false },
      { key: "enable_scan_dft", label: "Enable scan/DFT intent", type: "boolean", defaultValue: false },
      { key: "analog_physical_mode", label: "Analog physical mode", type: "select", defaultValue: "blackbox", options: [
        { value: "blackbox", label: "Blackbox analog macro" },
        { value: "generate_sky130_gds", label: "Generate Sky130 GDS" },
        { value: "provided_gds", label: "Provided GDS/SPICE" },
      ] },
      { key: "analog_pdk", label: "Analog PDK", type: "text", defaultValue: "sky130A" },
      { key: "analog_spice_text", label: "Provided analog SPICE/netlist", type: "text", defaultValue: "" },
      { key: "regenerate_lef_lib_after_gds", label: "Regenerate LEF/LIB after GDS", type: "boolean", defaultValue: true },
      { key: "run_lef_lib_consistency", label: "Run LEF/LIB consistency", type: "boolean", defaultValue: true },
      { key: "run_logic_equivalence", label: "Run logic equivalence", type: "boolean", defaultValue: true },
      { key: "run_fill", label: "Run fill", type: "boolean", defaultValue: true },
      { key: "run_drc", label: "Run DRC", type: "boolean", defaultValue: true },
      { key: "run_lvs", label: "Run LVS", type: "boolean", defaultValue: true },
      { key: "run_signoff_closure_loop", label: "Run signoff closure loop", type: "boolean", defaultValue: false },
      { key: "max_signoff_closure_iterations", label: "Max signoff closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_timing_repair", label: "Allow timing repair", type: "boolean", defaultValue: true },
      { key: "allow_drc_repair", label: "Allow DRC repair", type: "boolean", defaultValue: true },
      { key: "allow_lvs_repair", label: "Allow LVS repair", type: "boolean", defaultValue: true },
      { key: "allow_lec_repair", label: "Allow LEC repair", type: "boolean", defaultValue: true },
      { key: "run_synthesis_closure_loop", label: "Run synthesis closure loop", type: "boolean", defaultValue: false },
      { key: "max_synthesis_closure_iterations", label: "Max synthesis closure iterations", type: "number", defaultValue: 1 },
      { key: "allow_synthesis_timing_repair", label: "Allow synthesis setup timing repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_lec_repair", label: "Allow synthesis LEC repair", type: "boolean", defaultValue: true },
      { key: "allow_synthesis_retiming", label: "Allow synthesis retiming", type: "boolean", defaultValue: false },
      { key: "allow_synthesis_hierarchy_flattening", label: "Allow synthesis hierarchy flattening", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_closure_failure", label: "Stop downstream on synthesis closure failure", type: "boolean", defaultValue: false },
      { key: "stop_on_synthesis_lec_failure", label: "Stop downstream on synthesis LEC failure", type: "boolean", defaultValue: false },
    ],
  },
  Embedded_Run: {
    fields: [
      { key: "firmware_language", label: "Firmware language", type: "select", defaultValue: "rust", options: [
        { value: "rust", label: "Rust" },
        { value: "c", label: "C" },
      ] },
      { key: "enable_cosim", label: "Enable firmware co-sim", type: "boolean", defaultValue: false },
    ],
  },
  verify_closure_loop: {
    fields: [
      { key: "max_iterations", label: "Max iterations", type: "number", defaultValue: 1 },
      { key: "seed_count", label: "Seed count", type: "number", defaultValue: 10 },
      { key: "seed_budget", label: "Seed budget", type: "number", defaultValue: 10 },
      { key: "coverage_targets", label: "Coverage target", type: "text", defaultValue: "90% functional, 70% line" },
      { key: "rerun_mode", label: "Rerun mode", type: "select", defaultValue: "coverage_targeted", options: [
        { value: "coverage_targeted", label: "Coverage targeted" },
        { value: "failed_only", label: "Failed tests only" },
        { value: "full_regression", label: "Full regression" },
      ] },
      { key: "random_vs_directed", label: "Random vs directed", type: "select", defaultValue: "both", options: [
        { value: "both", label: "Directed then random" },
        { value: "directed", label: "Directed only" },
        { value: "random", label: "Random only" },
      ] },
      { key: "enable_failure_debug", label: "Run failure debug", type: "boolean", defaultValue: false },
      { key: "failure_debug_log_only_first", label: "Failure debug log-only first", type: "boolean", defaultValue: true },
      { key: "failure_debug_generate_vcd", label: "Generate VCD for failures", type: "boolean", defaultValue: true },
      { key: "failure_debug_auto_apply_tb", label: "Auto-apply TB fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_auto_apply_rtl", label: "Auto-apply RTL fixes", type: "boolean", defaultValue: false },
      { key: "failure_debug_rerun_failing", label: "Rerun failing tests", type: "boolean", defaultValue: true },
    ],
  },
  System_Software: {
    fields: [
      { key: "app_names", label: "App names", type: "text", defaultValue: "status_cli, product_service" },
      { key: "target_language", label: "Target language", type: "select", defaultValue: "rust", options: [
        { value: "rust", label: "Rust" },
        { value: "c", label: "C" },
        { value: "mixed", label: "Mixed C/Rust" },
      ] },
      { key: "sdk_style", label: "SDK style", type: "select", defaultValue: "rust_crate", options: [
        { value: "rust_crate", label: "Rust crate" },
        { value: "c_sdk", label: "C SDK" },
        { value: "mixed", label: "Mixed SDK" },
      ] },
      { key: "build_system", label: "Build system", type: "select", defaultValue: "cargo", options: [
        { value: "cargo", label: "Cargo" },
        { value: "cmake", label: "CMake" },
        { value: "make", label: "Make" },
      ] },
    ],
  },
  System_Software_Validation_L2: {
    fields: [
      { key: "validation_mode", label: "Validation mode", type: "select", defaultValue: "full_co_simulation", options: [
        { value: "full_co_simulation", label: "Full co-simulation" },
        { value: "software_package_validation", label: "Software package validation" },
      ] },
    ],
  },
  System_Product_App_Builder: {
    fields: [
      { key: "app_type", label: "App type", type: "select", defaultValue: "web_dashboard", options: [
        { value: "web_dashboard", label: "Web dashboard" },
        { value: "cli_tool", label: "CLI tool (planned)", disabled: true },
      ] },
      { key: "target_runtime", label: "Target runtime", type: "select", defaultValue: "simulated_device", options: [
        { value: "simulated_device", label: "Simulated device" },
        { value: "board_transport", label: "Board transport (planned)", disabled: true },
      ] },
    ],
  },
};

const FALLBACK_STAGE_SCHEMA: StageSchema = {
  fields: [{ key: "notes", label: "Notes", type: "text", defaultValue: "" }],
};

type StageCatalogItem = {
  app: string;
  label: string;
  category: "Digital" | "System" | "Embedded" | "Software" | "Validation" | "Product";
  produces: string[];
  requires?: string[][];
  warning?: string;
};

const STAGE_CATALOG: StageCatalogItem[] = [
  { app: "Digital_Arch2RTL", label: "Digital RTL", category: "Digital", produces: ["arch2rtl", "digital_rtl"] },
  { app: "Digital_DQA", label: "Digital DQA", category: "Digital", produces: ["dqa"], requires: [["arch2rtl"]] },
  { app: "Digital_Verify", label: "Digital Verify", category: "Digital", produces: ["verify"], requires: [["arch2rtl"]] },
  { app: "Digital_Arch2Synthesis", label: "Digital Synthesis", category: "Digital", produces: ["arch2synthesis"], requires: [["arch2rtl"]] },
  { app: "Digital_Arch2Tapeout", label: "Digital Tapeout", category: "Digital", produces: ["tapeout"], requires: [["arch2rtl"]] },
  { app: "verify_closure_loop", label: "Verify Closure Loop", category: "Digital", produces: ["closure"], requires: [["verify"]] },
  { app: "Embedded_Run", label: "Firmware", category: "Embedded", produces: ["firmware"], requires: [["arch2rtl"], ["system_rtl"]] },
  { app: "System_RTL", label: "System RTL", category: "System", produces: ["system_rtl"] },
  { app: "System_DQA", label: "System DQA", category: "System", produces: ["system_dqa"], requires: [["system_rtl"]] },
  { app: "System_Sim", label: "System Sim / Verify", category: "System", produces: ["system_sim", "validation"], requires: [["system_rtl"]] },
  { app: "System_Synthesis", label: "System Synthesis", category: "System", produces: ["system_synthesis"], requires: [["system_rtl"]] },
  { app: "System_Firmware", label: "System Firmware", category: "System", produces: ["system_firmware", "firmware"], requires: [["system_rtl"]] },
  { app: "System_PD", label: "System PD", category: "System", produces: ["system_pd"], warning: "As a Product stage this uses a prior System RTL handoff. Standalone System PD can run the full System RTL plus PD sequence." },
  { app: "System_Software", label: "System Software", category: "Software", produces: ["software"], requires: [["firmware"], ["system_firmware"]] },
  { app: "System_Software_Validation_L2", label: "Software Validation", category: "Validation", produces: ["validation"], requires: [["software"]] },
  { app: "System_Product_App_Builder", label: "Product App", category: "Product", produces: ["product_app"], requires: [["software", "validation"]] },
];

const STAGE_CATALOG_BY_APP: Record<string, StageCatalogItem> = Object.fromEntries(STAGE_CATALOG.map((item) => [item.app, item]));

function typeLabel(value: string) {
  return value.replace(/_/g, "-").replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function stageKind(stage: Stage) {
  if (stage.required) return "Required";
  if (stage.recommended) return "Recommended";
  if (stage.optional) return "Optional";
  return "Stage";
}

function stageEnabled(stage: Stage) {
  if (stage.required) return true;
  if (stage.optional && stage.enabled === undefined) return false;
  return stage.enabled !== false;
}

function fieldValue(stage: Stage, field: StageField) {
  return stage.settings?.[field.key] ?? field.defaultValue;
}

function optionValue(option: StageOption) {
  return typeof option === "string" ? option : option.value;
}

function optionLabel(option: StageOption) {
  return typeof option === "string" ? option : option.label || option.value;
}

function optionDisabled(option: StageOption) {
  return typeof option === "string" ? false : Boolean(option.disabled);
}

function isBlank(value: unknown) {
  return value === undefined || value === null || (typeof value === "string" && value.trim().length === 0);
}

function formatDate(value?: string | null) {
  if (!value) return "-";
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return "-";
  return date.toLocaleString();
}

function appLink(app: string, workflowId?: string | null, runId?: string | null) {
  const base = APP_LINKS[app] || "/apps";
  if (!workflowId) return base;
  const params = new URLSearchParams({ workflow_id: workflowId });
  if (runId) params.set("run_id", runId);
  return `${base}?${params.toString()}`;
}

function dashboardStageForApp(app: string) {
  const map: Record<string, string> = {
    Digital_Arch2RTL: "arch2rtl",
    System_RTL: "arch2rtl",
    Digital_DQA: "dqa",
    System_DQA: "dqa",
    Digital_Verify: "verification",
    verify_closure_loop: "verification",
    System_Sim: "verification",
    Digital_Arch2Synthesis: "synthesis",
    System_Synthesis: "synthesis",
    Digital_Arch2Tapeout: "tapeout",
    System_PD: "tapeout",
    Embedded_Run: "embedded",
    System_Firmware: "embedded",
    System_Software: "software",
    System_Software_Validation_L2: "validation",
    System_Product_App_Builder: "product",
  };
  return map[app] || "arch2rtl";
}

function stageRunDashboardLink(stageRun: StageRun) {
  if (!stageRun.workflow_id) return appLink(stageRun.app);
  const params = new URLSearchParams({
    stage: dashboardStageForApp(stageRun.app),
    status: stageRun.status || "completed",
    app: stageRun.app,
  });
  if (stageRun.run_id) params.set("run_id", stageRun.run_id);
  return `/dashboard/${encodeURIComponent(stageRun.workflow_id)}?${params.toString()}`;
}

function parseLogLines(logs?: string | null) {
  if (!logs) return [];
  return logs.split("\n").map((line) => line.trimEnd()).filter((line) => line.trim().length > 0);
}

function stageSummaryStatus(status: string) {
  const normalized = String(status || "").toLowerCase();
  if (normalized === "completed" || normalized === "success" || normalized === "succeeded") return "Passed";
  if (normalized === "failed" || normalized === "error") return "Failed";
  if (normalized === "cancelled" || normalized === "canceled") return "Cancelled";
  return "Running";
}

function stageSummaryTone(summary: string) {
  if (summary === "Passed") return "bg-emerald-500/10 text-emerald-200";
  if (summary === "Failed") return "bg-rose-500/10 text-rose-200";
  if (summary === "Cancelled") return "bg-slate-700/60 text-slate-200";
  return "bg-cyan-500/10 text-cyan-200";
}

function stageRunAgentCount(stageRun: StageRun): number | null {
  const outputs = stageRun.outputs || {};
  const candidates = [
    outputs.agent_count,
    outputs.agents_participated,
    outputs.agents_executed,
  ];
  for (const candidate of candidates) {
    if (typeof candidate === "number" && Number.isFinite(candidate)) return candidate;
    if (typeof candidate === "string" && candidate.trim()) {
      const parsed = Number(candidate);
      if (Number.isFinite(parsed)) return parsed;
    }
  }
  return null;
}

function workflowSummaryName(stageRun: StageRun) {
  return stageRun.app || stageRun.stage_label || stageRun.stage_id;
}

function isRichTextField(field: StageField) {
  return [
    "spec_text",
    "digital_spec",
    "analog_spec",
    "soc_spec",
    "test_intent",
    "verification_plan",
    "monitor_checker_plan",
    "coverage_plan",
    "constraints_sdc",
    "analog_spice_text",
    "throughput_latency_targets",
  ].includes(field.key);
}

function voiceLoopTypeForApp(app: string) {
  if (app.startsWith("System_")) return "system";
  if (app.startsWith("Embedded_")) return "embedded";
  return "digital";
}

function makeStageId(app: string, stages: Stage[]) {
  const base = app.toLowerCase().replace(/[^a-z0-9]+/g, "_").replace(/^_+|_+$/g, "") || "stage";
  const used = new Set(stages.map((stage) => stage.id));
  if (!used.has(base)) return base;
  let index = 2;
  while (used.has(`${base}_${index}`)) index += 1;
  return `${base}_${index}`;
}

function validateStageSequence(stages: Stage[]) {
  const produced = new Set<string>();
  const enabledStages = stages.filter(stageEnabled);
  const findings: Array<{ severity: "error" | "warning"; stageId: string; stageLabel: string; message: string }> = [];
  for (const stage of enabledStages) {
    const meta = STAGE_CATALOG_BY_APP[stage.app];
    if (!meta) {
      findings.push({ severity: "warning", stageId: stage.id, stageLabel: stage.label, message: "This app is not in the Product stage catalog yet." });
      continue;
    }
    const requirementOptions = meta.requires || [];
    const missingRequirement = requirementOptions.length && !requirementOptions.some((group) => group.every((key) => produced.has(key)))
      ? requirementOptions[0]
      : null;
    if (missingRequirement) {
      findings.push({
        severity: "error",
        stageId: stage.id,
        stageLabel: stage.label,
        message: `${meta.label} expects upstream ${missingRequirement.join(" + ")} output before this stage.`,
      });
    }
    if (meta.warning) {
      findings.push({ severity: "warning", stageId: stage.id, stageLabel: stage.label, message: meta.warning });
    }
    if (stage.app === "Digital_Verify" && produced.has("system_rtl") && !produced.has("arch2rtl")) {
      findings.push({ severity: "warning", stageId: stage.id, stageLabel: stage.label, message: "Digital Verify is normally paired with Digital Arch2RTL. For System RTL, use System Sim / Verify." });
    }
    if ((stage.app === "Embedded_Run" || stage.app === "System_Firmware") && !produced.has("arch2rtl") && !produced.has("system_rtl")) {
      findings.push({ severity: "error", stageId: stage.id, stageLabel: stage.label, message: "Firmware stages need an RTL/register-map handoff before they run." });
    }
    for (const output of meta.produces) produced.add(output);
  }
  return findings;
}

const STAGE_ACTION_BUTTON_CLASS =
  "flex h-12 w-28 shrink-0 items-center justify-center rounded-md border border-cyan-700/70 px-2 text-center text-sm font-semibold leading-5 text-cyan-100 transition hover:bg-cyan-950/40";

function StepRail({ active }: { active: "define" | "configure" | "run" }) {
  const steps = [
    { id: "define", label: "Define", text: "Create product" },
    { id: "configure", label: "Configure", text: "Review stages" },
    { id: "run", label: "Run", text: "Track results" },
  ] as const;
  return (
    <div className="grid gap-2 rounded-lg border border-slate-800 bg-slate-900/45 p-3 sm:grid-cols-3">
      {steps.map((step, index) => (
        <div
          key={step.id}
          className={`rounded-md border px-3 py-2 ${
            active === step.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-950/60"
          }`}
        >
          <div className="text-xs font-semibold uppercase tracking-wide text-slate-500">Step {index + 1}</div>
          <div className={active === step.id ? "text-sm font-semibold text-cyan-100" : "text-sm font-semibold text-white"}>{step.label}</div>
          <div className="mt-1 text-xs text-slate-400">{step.text}</div>
        </div>
      ))}
    </div>
  );
}

export default function ProductDetailPage() {
  const params = useParams<{ productId: string }>();
  const router = useRouter();
  const productId = params.productId;
  const [product, setProduct] = useState<Product | null>(null);
  const [loading, setLoading] = useState(true);
  const [saving, setSaving] = useState(false);
  const [running, setRunning] = useState(false);
  const [deletingRunId, setDeletingRunId] = useState<string | null>(null);
  const [message, setMessage] = useState<string | null>(null);
  const [selectedStageId, setSelectedStageId] = useState<string | null>(null);
  const [newStageApp, setNewStageApp] = useState(STAGE_CATALOG[0]?.app || "Digital_Arch2RTL");
  const [draggedStageId, setDraggedStageId] = useState<string | null>(null);
  const [productRun, setProductRun] = useState<ProductRun | null>(null);
  const [stageRuns, setStageRuns] = useState<StageRun[]>([]);
  const [runHistory, setRunHistory] = useState<ProductRunWithStages[]>([]);
  const [stageSchemas, setStageSchemas] = useState<Record<string, StageSchema>>(FALLBACK_STAGE_SCHEMAS);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const schemas = await apiGet<{ status: string; stage_schemas: Record<string, StageSchema> }>("/products/stage-schemas");
        if (mounted && schemas.stage_schemas) setStageSchemas(schemas.stage_schemas);
      } catch {
        // Keep local fallback schemas during rollout or local backend mismatch.
      }
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const out = await apiGet<{ status: string; product: Product }>(`/products/${productId}`);
        if (!mounted) return;
        setProduct(out.product);
        setSelectedStageId(out.product.stage_config?.stages?.[0]?.id || null);
        try {
          const history = await apiGet<{ status: string; product_runs: ProductRunWithStages[] }>(`/products/${productId}/runs`);
          if (!mounted) return;
          setRunHistory(history.product_runs || []);
          const latest = history.product_runs?.[0];
          if (latest) {
            setProductRun(latest);
            setStageRuns(latest.stage_runs || []);
          }
        } catch {
          // Run history is non-blocking; product configuration should still load.
        }
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to load product");
      } finally {
        if (mounted) setLoading(false);
      }
    })();
    return () => { mounted = false; };
  }, [productId]);

  const stages = useMemo(() => product?.stage_config?.stages || [], [product]);
  const sequenceFindings = useMemo(() => validateStageSequence(stages), [stages]);
  const sequenceErrors = sequenceFindings.filter((finding) => finding.severity === "error");
  const selectedStage = stages.find((stage) => stage.id === selectedStageId) || stages[0] || null;
  const stageRunById = useMemo(() => {
    const out: Record<string, StageRun> = {};
    for (const stageRun of stageRuns) out[stageRun.stage_id] = stageRun;
    return out;
  }, [stageRuns]);
  const missingRequirements = useMemo(() => {
    if (!product) return [];
    const missing: Array<{ stageId: string; stageLabel: string; fieldLabel: string }> = [];
    for (const stage of stages) {
      if (!stageEnabled(stage)) continue;
      const schema = stageSchemas[stage.app];
      for (const field of schema?.fields || []) {
        if (field.required && isBlank(fieldValue(stage, field))) {
          missing.push({ stageId: stage.id, stageLabel: stage.label, fieldLabel: field.label });
        }
      }
      if (stage.app === "Digital_Arch2RTL") {
        const specText = String(stage.settings?.spec_text || "").trim();
        if (!specText && !String(product.description || "").trim()) {
          missing.push({ stageId: stage.id, stageLabel: stage.label, fieldLabel: "Spec text or product description" });
        }
      }
    }
    for (const finding of sequenceErrors) {
      missing.push({ stageId: finding.stageId, stageLabel: finding.stageLabel, fieldLabel: finding.message });
    }
    return missing;
  }, [product, stages, stageSchemas, sequenceErrors]);
  const activeRun = Boolean(productRun && ["queued", "running"].includes(productRun.status));
  const failedStageRun = stageRuns.find((stageRun) => stageRun.status === "failed") || null;
  const failedStage = failedStageRun ? stages.find((stage) => stage.id === failedStageRun.stage_id) || null : null;
  const runCounts = useMemo(() => ({
    completed: stageRuns.filter((stageRun) => stageRun.status === "completed").length,
    failed: stageRuns.filter((stageRun) => stageRun.status === "failed").length,
    running: stageRuns.filter((stageRun) => ["queued", "running"].includes(stageRun.status)).length,
  }), [stageRuns]);
  const stageRunSummaries = useMemo(() => stageRuns.map((stageRun) => ({
    stageRun,
    name: workflowSummaryName(stageRun),
    summary: stageSummaryStatus(stageRun.status),
    agentCount: stageRunAgentCount(stageRun),
  })), [stageRuns]);
  const overallRunSummary = useMemo(() => {
    if (!stageRunSummaries.length) return { status: "Not Run", totalAgents: 0, knownAgentCounts: false };
    const hasFailed = stageRunSummaries.some((item) => item.summary === "Failed");
    const hasCancelled = stageRunSummaries.some((item) => item.summary === "Cancelled");
    const hasRunning = stageRunSummaries.some((item) => item.summary === "Running");
    const knownAgentCounts = stageRunSummaries.some((item) => item.agentCount !== null);
    const totalAgents = stageRunSummaries.reduce((sum, item) => sum + (item.agentCount || 0), 0);
    return {
      status: hasFailed ? "Failed" : hasCancelled ? "Cancelled" : hasRunning ? "Running" : "Passed",
      totalAgents,
      knownAgentCounts,
    };
  }, [stageRunSummaries]);
  const productRunLogLines = useMemo(() => parseLogLines(productRun?.logs), [productRun?.logs]);

  useEffect(() => {
    if (!productRun || !product || !["queued", "running"].includes(productRun.status)) return;
    let mounted = true;
    const poll = async () => {
      try {
        const out = await apiGet<{ status: string; product_run: ProductRun; stage_runs: StageRun[] }>(
          `/products/${product.id}/runs/${productRun.id}`,
        );
        if (!mounted) return;
        setProductRun(out.product_run);
        setStageRuns(out.stage_runs || []);
        setRunHistory((current) => current.map((run) => (
          run.id === out.product_run.id ? { ...out.product_run, stage_runs: out.stage_runs || [] } : run
        )));
        setProduct((current) => current ? {
          ...current,
          status: out.product_run.status,
          stage_results: out.product_run.stage_results || current.stage_results,
        } : current);
        if (!["queued", "running"].includes(out.product_run.status)) setRunning(false);
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to refresh product run");
      }
    };
    const timer = window.setInterval(() => { void poll(); }, 2500);
    void poll();
    return () => {
      mounted = false;
      window.clearInterval(timer);
    };
  }, [productRun, product]);

  function updateStage(stageId: string, patch: Partial<Stage>) {
    setProduct((current) => {
      if (!current) return current;
      const nextStages = (current.stage_config?.stages || []).map((stage) => (
        stage.id === stageId ? { ...stage, ...patch } : stage
      ));
      return {
        ...current,
        stage_config: {
          ...(current.stage_config || {}),
          stages: nextStages,
        },
      };
    });
  }

  function replaceStages(nextStages: Stage[], selectedId?: string | null) {
    setProduct((current) => {
      if (!current) return current;
      return {
        ...current,
        stage_config: {
          ...(current.stage_config || {}),
          stages: nextStages,
        },
      };
    });
    if (selectedId !== undefined) setSelectedStageId(selectedId);
  }

  function addStageFromCatalog() {
    const catalogItem = STAGE_CATALOG_BY_APP[newStageApp] || STAGE_CATALOG[0];
    if (!catalogItem) return;
    const newStage: Stage = {
      id: makeStageId(catalogItem.app, stages),
      label: catalogItem.label,
      app: catalogItem.app,
      optional: true,
      enabled: true,
      settings: {},
    };
    replaceStages([...stages, newStage], newStage.id);
  }

  function moveStage(stageId: string, direction: -1 | 1) {
    const currentIndex = stages.findIndex((stage) => stage.id === stageId);
    const nextIndex = currentIndex + direction;
    if (currentIndex < 0 || nextIndex < 0 || nextIndex >= stages.length) return;
    const nextStages = [...stages];
    const [stage] = nextStages.splice(currentIndex, 1);
    nextStages.splice(nextIndex, 0, stage);
    replaceStages(nextStages, stageId);
  }

  function dropStageOnTarget(targetStageId: string) {
    if (!draggedStageId || draggedStageId === targetStageId) return;
    const draggedIndex = stages.findIndex((stage) => stage.id === draggedStageId);
    const targetIndex = stages.findIndex((stage) => stage.id === targetStageId);
    if (draggedIndex < 0 || targetIndex < 0) return;
    const nextStages = [...stages];
    const [draggedStage] = nextStages.splice(draggedIndex, 1);
    nextStages.splice(targetIndex, 0, draggedStage);
    replaceStages(nextStages, draggedStageId);
    setDraggedStageId(null);
  }

  function removeStage(stageId: string) {
    const stage = stages.find((item) => item.id === stageId);
    if (!stage || stage.required) return;
    const nextStages = stages.filter((item) => item.id !== stageId);
    replaceStages(nextStages, nextStages[0]?.id || null);
  }

  function updateStageKind(stageId: string, kind: "required" | "recommended" | "optional") {
    updateStage(stageId, {
      required: kind === "required",
      recommended: kind === "recommended",
      optional: kind === "optional",
      enabled: kind === "required" ? true : stageEnabled(stages.find((stage) => stage.id === stageId) || { id: stageId, label: "", app: "" }),
    });
  }

  function updateStageSetting(stageId: string, key: string, value: unknown) {
    setProduct((current) => {
      if (!current) return current;
      const nextStages = (current.stage_config?.stages || []).map((stage) => {
        if (stage.id !== stageId) return stage;
        return {
          ...stage,
          settings: {
            ...(stage.settings || {}),
            [key]: value,
          },
        };
      });
      return {
        ...current,
        stage_config: {
          ...(current.stage_config || {}),
          stages: nextStages,
        },
      };
    });
  }

  async function saveDraft() {
    if (!product) return;
    setSaving(true);
    setMessage(null);
    try {
      const out = await apiPatch<{ status: string; product: Product }>(`/products/${product.id}`, {
        stage_config: product.stage_config || {},
        status: product.status,
      });
      setProduct(out.product);
      setMessage("Product draft saved.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to save product");
    } finally {
      setSaving(false);
    }
  }

  async function runProduct(startStage?: string, resumeProductRunId?: string) {
    if (!product) return;
    if (missingRequirements.length) {
      setMessage("Complete required configuration before running the product.");
      setSelectedStageId(missingRequirements[0].stageId);
      return;
    }
    setRunning(true);
    setMessage(null);
    try {
      await saveDraft();
      const out = await apiPost<{ status: string; product_run: ProductRun }>(`/products/${product.id}/run`, {
        start_stage: startStage,
        resume_product_run_id: resumeProductRunId,
      });
      setProductRun(out.product_run);
      setProduct((current) => current ? { ...current, status: out.product_run.status } : current);
      setStageRuns([]);
      setRunHistory((current) => [{ ...out.product_run, stage_runs: [] }, ...current.filter((run) => run.id !== out.product_run.id)]);
      setMessage(startStage ? `Product run restarted from ${startStage}.` : "Product run started. Supported stages run in order with workflow handoffs.");
    } catch (error) {
      setRunning(false);
      setMessage(error instanceof Error ? error.message : "Failed to start product run");
    }
  }

  async function cancelRun() {
    if (!product || !productRun) return;
    setMessage(null);
    try {
      const out = await apiPost<{ status: string; product_run: ProductRun }>(`/products/${product.id}/runs/${productRun.id}/cancel`, {});
      setProductRun(out.product_run);
      setProduct((current) => current ? { ...current, status: out.product_run.status } : current);
      setRunHistory((current) => current.map((run) => (run.id === out.product_run.id ? { ...run, ...out.product_run } : run)));
      setRunning(false);
      setMessage("Product run cancellation requested. The orchestrator will stop before the next stage.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to cancel product run");
    }
  }

  async function deleteRunHistory(run: ProductRunWithStages) {
    if (!product || deletingRunId) return;
    setDeletingRunId(run.id);
    setMessage(null);
    try {
      await apiDelete<{ status: string; deleted_product_run_id: string }>(`/products/${product.id}/runs/${run.id}`);
      const nextHistory = runHistory.filter((item) => item.id !== run.id);
      setRunHistory(nextHistory);
      if (productRun?.id === run.id) {
        const next = nextHistory[0] || null;
        setProductRun(next);
        setStageRuns(next?.stage_runs || []);
      }
      setMessage("Run history entry deleted.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to delete run history entry");
    } finally {
      setDeletingRunId(null);
    }
  }

  async function skipFailedOptionalStage() {
    if (!product || !failedStage || failedStage.required) return;
    const nextStages = stages.map((stage) => (
      stage.id === failedStage.id ? { ...stage, enabled: false } : stage
    ));
    const nextStageConfig = { ...(product.stage_config || {}), stages: nextStages };
    setProduct({ ...product, stage_config: nextStageConfig });
    setSelectedStageId(failedStage.id);
    setSaving(true);
    setMessage(null);
    try {
      const out = await apiPatch<{ status: string; product: Product }>(`/products/${product.id}`, {
        stage_config: nextStageConfig,
        status: product.status,
      });
      setProduct(out.product);
      setMessage(`${failedStage.label} will be skipped on the next run.`);
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to skip optional stage");
    } finally {
      setSaving(false);
    }
  }

  if (loading) {
    return (
      <main className="min-h-screen bg-slate-950 text-slate-100">
        <TopNav current="products" showPlanBadge />
        <div className="mx-auto max-w-7xl px-4 py-8 text-sm text-slate-300">Loading product...</div>
      </main>
    );
  }

  if (!product) {
    return (
      <main className="min-h-screen bg-slate-950 text-slate-100">
        <TopNav current="products" showPlanBadge />
        <div className="mx-auto max-w-7xl px-4 py-8">
          <div className="rounded-lg border border-rose-500/30 bg-rose-950/30 p-4 text-sm text-rose-100">{message || "Product not found."}</div>
          <button onClick={() => router.push("/products")} className="mt-4 rounded-lg border border-slate-700 px-3 py-2 text-sm text-slate-200 hover:bg-slate-800">Back to Products</button>
        </div>
      </main>
    );
  }

  return (
    <main className="min-h-screen bg-slate-950 text-slate-100">
      <TopNav current="products" showPlanBadge />
      <div className="mx-auto max-w-7xl px-4 py-6 sm:px-6">
        <div className="mb-5 flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
          <div>
            <button onClick={() => router.push("/products")} className="mb-3 text-sm font-semibold text-cyan-300 hover:text-cyan-200">Back to Products</button>
            <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Step 2: Configure Product</div>
            <h1 className="mt-2 text-3xl font-bold tracking-normal text-white">{product.name}</h1>
            <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">{product.description || "Review stages, configure required inputs, then run product development."}</p>
            <div className="mt-3 flex flex-wrap gap-2 text-xs">
              <span className="rounded-md bg-slate-800 px-2 py-1 text-slate-300">{typeLabel(product.product_type)}</span>
              <span className="rounded-md bg-slate-800 px-2 py-1 text-slate-300">{product.starting_point.replace(/_/g, " ")}</span>
              <span className="rounded-md border border-slate-700 px-2 py-1 text-slate-300">{product.status}</span>
            </div>
          </div>
          <div className="flex gap-2">
            <button onClick={saveDraft} disabled={saving} className="rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300 disabled:opacity-60">
              {saving ? "Saving..." : "Save Draft"}
            </button>
            <button onClick={() => router.push("/apps")} className="rounded-lg border border-slate-700 px-4 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800">
              Open Apps
            </button>
          </div>
        </div>

        <div className="mb-5">
          <StepRail active="configure" />
        </div>

        {message ? <div className="mb-5 rounded-lg border border-cyan-500/30 bg-cyan-950/30 px-4 py-3 text-sm text-cyan-100">{message}</div> : null}

        <div className="grid gap-5 lg:grid-cols-[0.95fr_1.05fr]">
          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
            <div className="flex flex-col gap-4">
              <div>
                <h2 className="text-xl font-semibold text-white">Development Stages</h2>
                <p className="mt-1 text-sm text-slate-400">Add existing Apps to this product, then drag or move stages into the intended sequence.</p>
              </div>
              <div className="flex flex-col gap-2 rounded-lg border border-slate-800 bg-slate-950/60 p-3 sm:flex-row sm:items-center">
                <select
                  value={newStageApp}
                  onChange={(event) => setNewStageApp(event.target.value)}
                  className="min-w-0 flex-1 rounded-md border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                >
                  {STAGE_CATALOG.map((item) => (
                    <option key={item.app} value={item.app}>{item.category} - {item.label}</option>
                  ))}
                </select>
                <button
                  onClick={addStageFromCatalog}
                  className="rounded-md bg-cyan-400 px-3 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300"
                >
                  Add Stage
                </button>
                <span className="rounded-md bg-slate-900 px-2 py-2 text-center text-xs text-slate-300">{stages.length} stages</span>
              </div>
            </div>
            {sequenceFindings.length ? (
              <div className="mt-4 rounded-lg border border-amber-500/25 bg-amber-950/20 p-3">
                <div className="text-sm font-semibold text-amber-100">Sequence guidance</div>
                <div className="mt-2 grid gap-2">
                  {sequenceFindings.map((finding) => (
                    <button
                      key={`${finding.stageId}-${finding.message}`}
                      onClick={() => setSelectedStageId(finding.stageId)}
                      className={`rounded-md border px-3 py-2 text-left text-xs leading-5 ${
                        finding.severity === "error"
                          ? "border-rose-500/30 bg-rose-950/20 text-rose-100 hover:border-rose-400/70"
                          : "border-amber-500/25 bg-slate-950/40 text-amber-100 hover:border-amber-400/70"
                      }`}
                    >
                      {finding.stageLabel}: {finding.message}
                    </button>
                  ))}
                </div>
              </div>
            ) : null}
            <div className="mt-5 space-y-3">
              {stages.length === 0 ? (
                <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">No stages configured yet.</div>
              ) : stages.map((stage, index) => (
                <div
                  key={stage.id}
                  draggable
                  onClick={() => setSelectedStageId(stage.id)}
                  onDragStart={() => setDraggedStageId(stage.id)}
                  onDragOver={(event) => event.preventDefault()}
                  onDrop={() => dropStageOnTarget(stage.id)}
                  onDragEnd={() => setDraggedStageId(null)}
                  role="button"
                  tabIndex={0}
                  onKeyDown={(event) => {
                    if (event.key === "Enter" || event.key === " ") setSelectedStageId(stage.id);
                  }}
                  className={`w-full cursor-grab rounded-lg border p-4 text-left transition active:cursor-grabbing ${
                    selectedStage?.id === stage.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-950/60 hover:border-slate-600"
                  }`}
                >
                  <div className="flex items-start justify-between gap-3">
                    <div>
                      <div className="text-xs font-semibold text-slate-500">Stage {index + 1}</div>
                      <div className="mt-1 font-semibold text-white">{stage.label}</div>
                      <div className="mt-1 text-xs text-slate-400">{stage.app}</div>
                    </div>
                    <div className="text-right">
                      <div className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300">{stageKind(stage)}</div>
                      <div className={`mt-2 text-xs font-semibold ${
                        stageRunById[stage.id]?.status === "completed"
                          ? "text-emerald-300"
                          : stageRunById[stage.id]?.status === "failed"
                          ? "text-rose-300"
                          : stageRunById[stage.id]?.status === "running"
                          ? "text-cyan-300"
                          : stageEnabled(stage)
                          ? "text-emerald-300"
                          : "text-slate-500"
                      }`}>
                        {stageRunById[stage.id]?.status || (stageEnabled(stage) ? "Enabled" : "Skipped")}
                      </div>
                    </div>
                  </div>
                  <div className="mt-3 flex flex-wrap gap-2">
                    <button
                      type="button"
                      onClick={(event) => {
                        event.stopPropagation();
                        moveStage(stage.id, -1);
                      }}
                      disabled={index === 0}
                      className="rounded-md border border-slate-700 px-2 py-1 text-xs font-semibold text-slate-200 hover:bg-slate-800 disabled:cursor-not-allowed disabled:opacity-40"
                    >
                      Move Up
                    </button>
                    <button
                      type="button"
                      onClick={(event) => {
                        event.stopPropagation();
                        moveStage(stage.id, 1);
                      }}
                      disabled={index === stages.length - 1}
                      className="rounded-md border border-slate-700 px-2 py-1 text-xs font-semibold text-slate-200 hover:bg-slate-800 disabled:cursor-not-allowed disabled:opacity-40"
                    >
                      Move Down
                    </button>
                    {!stage.required ? (
                      <button
                        type="button"
                        onClick={(event) => {
                          event.stopPropagation();
                          removeStage(stage.id);
                        }}
                        className="rounded-md border border-rose-500/40 px-2 py-1 text-xs font-semibold text-rose-100 hover:bg-rose-950/40"
                      >
                        Remove
                      </button>
                    ) : null}
                  </div>
                </div>
              ))}
            </div>
          </section>

          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
            {selectedStage ? (
              <>
                <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
                  <div>
                    <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">{stageKind(selectedStage)}</div>
                    <h2 className="mt-2 text-xl font-semibold text-white">{selectedStage.label}</h2>
                    <p className="mt-1 text-sm text-slate-400">{selectedStage.app}</p>
                  </div>
                  <div className="flex flex-wrap gap-2">
                    <select
                      value={selectedStage.required ? "required" : selectedStage.recommended ? "recommended" : "optional"}
                      onChange={(event) => updateStageKind(selectedStage.id, event.target.value as "required" | "recommended" | "optional")}
                      className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm font-semibold text-slate-200 outline-none focus:border-cyan-400"
                    >
                      <option value="required">Required</option>
                      <option value="recommended">Recommended</option>
                      <option value="optional">Optional</option>
                    </select>
                    {!selectedStage.required ? (
                      <button
                        onClick={() => updateStage(selectedStage.id, { enabled: !stageEnabled(selectedStage) })}
                        className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                      >
                        {stageEnabled(selectedStage) ? "Skip" : "Enable"}
                      </button>
                    ) : null}
                    <button
                      onClick={() => router.push(APP_LINKS[selectedStage.app] || "/apps")}
                      className="rounded-lg bg-slate-100 px-3 py-2 text-sm font-semibold text-slate-950 hover:bg-white"
                    >
                      Open App
                    </button>
                    {!selectedStage.required ? (
                      <button
                        onClick={() => removeStage(selectedStage.id)}
                        className="rounded-lg border border-rose-500/40 px-3 py-2 text-sm font-semibold text-rose-100 hover:bg-rose-950/40"
                      >
                        Remove
                      </button>
                    ) : null}
                  </div>
                </div>

                <div className="mt-5 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                  <h3 className="font-semibold text-white">Configuration</h3>
                  <p className="mt-1 text-sm text-slate-400">Stage settings are saved with the product. Workflow IDs from earlier stages are auto-bound during Run.</p>
                  {stageSchemas[selectedStage.app]?.note ? (
                    <div className="mt-3 rounded-md border border-cyan-500/20 bg-cyan-950/20 px-3 py-2 text-xs leading-5 text-cyan-100">
                      {stageSchemas[selectedStage.app]?.note}
                    </div>
                  ) : null}
                  <div className="mt-4 grid gap-3">
                    {(stageSchemas[selectedStage.app] || FALLBACK_STAGE_SCHEMA).fields.map((field) => {
                      const value = fieldValue(selectedStage, field);
                      if (field.type === "boolean") {
                        return (
                          <label key={field.key} className="flex items-center justify-between gap-3 rounded-lg border border-slate-800 bg-slate-900/60 px-3 py-2">
                            <span className="text-sm text-slate-200">{field.label}</span>
                            <input
                              type="checkbox"
                              checked={Boolean(value)}
                              onChange={(event) => updateStageSetting(selectedStage.id, field.key, event.target.checked)}
                              className="h-4 w-4 accent-cyan-400"
                            />
                          </label>
                        );
                      }
                      if (field.type === "text" && isRichTextField(field)) {
                        return (
                          <SpecTextBox
                            key={field.key}
                            label={field.label}
                            value={String(value)}
                            onChange={(nextValue) => updateStageSetting(selectedStage.id, field.key, nextValue)}
                            rows={field.key.includes("spec") || field.key.includes("plan") || field.key.includes("intent") ? 7 : 4}
                            required={Boolean(field.required)}
                            voiceTitle={`${selectedStage.label}: ${field.label}`}
                            voiceLoopType={voiceLoopTypeForApp(selectedStage.app)}
                            voiceTarget={`${selectedStage.label} ${field.label}`}
                            uploadLabel={`Upload ${field.label}`}
                            uploadHelper="Use Replace or Append to control how uploaded text is applied."
                            placeholder={field.helper || field.label}
                            textareaClassName={`w-full resize-y bg-transparent p-1 text-sm text-slate-100 outline-none ${
                              field.required && isBlank(value) ? "ring-1 ring-rose-500/70" : ""
                            }`}
                          />
                        );
                      }
                      if (field.type === "select") {
                        const options = field.options?.length ? field.options : [String(field.defaultValue)];
                        return (
                          <label key={field.key} className="grid gap-2">
                            <span className="text-sm font-medium text-slate-200">
                              {field.label}{field.required ? <span className="text-rose-300"> *</span> : null}
                            </span>
                            <select
                              value={String(value)}
                              onChange={(event) => updateStageSetting(selectedStage.id, field.key, event.target.value)}
                              className={`rounded-lg border bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400 ${
                                field.required && isBlank(value) ? "border-rose-500/70" : "border-slate-700"
                              }`}
                            >
                              {options.map((option) => (
                                <option key={optionValue(option)} value={optionValue(option)} disabled={optionDisabled(option)}>
                                  {optionLabel(option)}
                                </option>
                              ))}
                            </select>
                            {field.helper ? <span className="text-xs text-slate-500">{field.helper}</span> : null}
                          </label>
                        );
                      }
                      return (
                        <label key={field.key} className="grid gap-2">
                          <span className="text-sm font-medium text-slate-200">
                            {field.label}{field.required ? <span className="text-rose-300"> *</span> : null}
                          </span>
                          <input
                            type={field.type}
                            value={String(value)}
                            onChange={(event) => updateStageSetting(selectedStage.id, field.key, field.type === "number" ? Number(event.target.value) : event.target.value)}
                            className={`rounded-lg border bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400 ${
                              field.required && isBlank(value) ? "border-rose-500/70" : "border-slate-700"
                            }`}
                          />
                          {field.helper ? <span className="text-xs text-slate-500">{field.helper}</span> : null}
                        </label>
                      );
                    })}
                  </div>
                </div>

                <div className="mt-5 rounded-lg border border-cyan-500/25 bg-cyan-950/15 p-4 text-sm leading-6 text-cyan-100">
                  Product Run uses existing App workflows and passes generated workflow IDs between stages. Existing standalone Apps remain available.
                </div>
              </>
            ) : (
              <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">Select a stage to configure it.</div>
            )}
          </section>
        </div>

        <section className="mt-5 rounded-lg border border-slate-800 bg-slate-900/45 p-5">
          <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase tracking-wide text-cyan-300">Step 3: Run</div>
              <h2 className="mt-2 text-xl font-semibold text-white">Product run dashboard</h2>
              <p className="mt-1 max-w-3xl text-sm leading-6 text-slate-400">
                This launches supported enabled stages in order, passes workflow IDs between stages, stops on failures, and shows product-level results.
              </p>
            </div>
            <button
              onClick={() => runProduct()}
              disabled={running || activeRun || missingRequirements.length > 0}
              className="rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300 disabled:cursor-not-allowed disabled:bg-slate-800 disabled:text-slate-500"
            >
              {running || activeRun ? "Running..." : "Run Product"}
            </button>
          </div>
          {missingRequirements.length ? (
            <div className="mt-4 rounded-lg border border-rose-500/30 bg-rose-950/25 p-4">
              <div className="text-sm font-semibold text-rose-100">Required inputs missing</div>
              <div className="mt-2 grid gap-2">
                {missingRequirements.map((item) => (
                  <button
                    key={`${item.stageId}-${item.fieldLabel}`}
                    onClick={() => setSelectedStageId(item.stageId)}
                    className="rounded-md border border-rose-500/20 bg-slate-950/50 px-3 py-2 text-left text-xs text-rose-100 hover:border-rose-400/60"
                  >
                    {item.stageLabel}: {item.fieldLabel}
                  </button>
                ))}
              </div>
            </div>
          ) : null}
          {productRun ? (
            <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="flex flex-col gap-2 sm:flex-row sm:items-center sm:justify-between">
                <div>
                  <div className="text-sm font-semibold text-white">Run {productRun.id}</div>
                  <div className="mt-1 text-xs text-slate-500">
                    Updated {formatDate(productRun.updated_at)} | Completed {formatDate(productRun.completed_at)}
                  </div>
                  <div className="mt-2 flex flex-wrap gap-2 text-xs">
                    <span className="rounded-md bg-emerald-500/10 px-2 py-1 text-emerald-200">{runCounts.completed} completed</span>
                    <span className="rounded-md bg-cyan-500/10 px-2 py-1 text-cyan-200">{runCounts.running} active</span>
                    <span className="rounded-md bg-rose-500/10 px-2 py-1 text-rose-200">{runCounts.failed} failed</span>
                  </div>
                  <div className="mt-1 text-xs text-slate-400">Status: {productRun.status}{productRun.current_stage ? ` · Current: ${productRun.current_stage}` : ""}</div>
                </div>
                <div className="flex flex-wrap items-center gap-2">
                  {activeRun ? (
                    <button onClick={cancelRun} className="rounded-md border border-rose-500/50 px-3 py-2 text-xs font-semibold text-rose-100 hover:bg-rose-950/50">
                      Cancel
                    </button>
                  ) : null}
                  {productRun.status === "failed" && failedStageRun ? (
                    <button
                      onClick={() => runProduct(failedStageRun.stage_id, productRun.id)}
                      className="rounded-md border border-cyan-500/50 px-3 py-2 text-xs font-semibold text-cyan-100 hover:bg-cyan-950/50"
                    >
                      Rerun From Failed Stage
                    </button>
                  ) : null}
                  {productRun.status === "failed" && failedStage && !failedStage.required ? (
                    <button
                      onClick={skipFailedOptionalStage}
                      className="rounded-md border border-slate-600 px-3 py-2 text-xs font-semibold text-slate-200 hover:bg-slate-800"
                    >
                      Skip Optional Stage
                    </button>
                  ) : null}
                  {productRun.error ? <div className="text-xs text-rose-300">{productRun.error}</div> : null}
                </div>
              </div>
              {stageRuns.length ? (
                <div className="mt-4 space-y-4">
                  <div className="rounded-lg border border-slate-800 bg-slate-900/70 p-4">
                    <div className="flex flex-col gap-3 sm:flex-row sm:items-start sm:justify-between">
                      <div>
                        <div className="text-sm font-semibold text-white">Overall Summary</div>
                        <div className="mt-1 text-xs text-slate-500">
                          Aggregated from completed Product stage workflow runs. Open individual dashboards for detailed evidence.
                        </div>
                      </div>
                      <div className="flex flex-wrap gap-2 text-xs">
                        <span className={`rounded-md px-2 py-1 font-semibold ${stageSummaryTone(overallRunSummary.status)}`}>
                          {overallRunSummary.status}
                        </span>
                        <span className="rounded-md bg-slate-950 px-2 py-1 text-slate-300">
                          Total Agents: {overallRunSummary.knownAgentCounts ? overallRunSummary.totalAgents : "not reported"}
                        </span>
                      </div>
                    </div>
                    <div className="mt-4 overflow-x-auto rounded-lg border border-slate-800">
                      <table className="min-w-[720px] w-full divide-y divide-slate-800 text-left text-sm">
                        <thead className="bg-slate-950/80 text-xs font-semibold uppercase text-slate-400">
                          <tr>
                            <th scope="col" className="px-3 py-2">Workflow</th>
                            <th scope="col" className="px-3 py-2">Stage</th>
                            <th scope="col" className="px-3 py-2">Summary</th>
                            <th scope="col" className="px-3 py-2">Agents Executed</th>
                            <th scope="col" className="px-3 py-2">Details</th>
                          </tr>
                        </thead>
                        <tbody className="divide-y divide-slate-800 bg-slate-950/40">
                          {stageRunSummaries.map(({ stageRun, name, summary, agentCount }) => (
                            <tr key={`summary-${stageRun.id}`} className="align-middle">
                              <th scope="row" className="px-3 py-3 font-semibold text-white">{name}</th>
                              <td className="px-3 py-3 text-slate-300">{stageRun.stage_label || stageRun.stage_id}</td>
                              <td className="px-3 py-3">
                                <span className={`rounded-md px-2 py-1 text-xs font-semibold ${stageSummaryTone(summary)}`}>
                                  {summary}
                                </span>
                              </td>
                              <td className="px-3 py-3 text-slate-300">{agentCount === null ? "not reported" : agentCount}</td>
                              <td className="px-3 py-3">
                                {stageRun.workflow_id ? (
                                  <div className="flex flex-wrap gap-2">
                                    <a
                                      href={stageRunDashboardLink(stageRun)}
                                      target="_blank"
                                      rel="noreferrer"
                                      className={STAGE_ACTION_BUTTON_CLASS}
                                    >
                                      Open Dashboard
                                    </a>
                                    <a
                                      href={`/api/workflow/${stageRun.workflow_id}/download_zip?full=1`}
                                      className={STAGE_ACTION_BUTTON_CLASS}
                                    >
                                      Download ZIP
                                    </a>
                                  </div>
                                ) : (
                                  <span className="text-xs text-slate-500">No workflow</span>
                                )}
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="grid gap-2">
                  {stageRuns.map((stageRun) => (
                    <div key={stageRun.id} className="flex flex-col gap-2 rounded-lg border border-slate-800 bg-slate-900/60 px-3 py-2 sm:flex-row sm:items-center sm:justify-between">
                      <div>
                        <div className="text-sm font-semibold text-white">{stageRun.stage_label}</div>
                        <div className="text-xs text-slate-500">{stageRun.app}</div>
                      </div>
                      <div className="flex items-center gap-2">
                        {stageRun.workflow_id ? (
                          <>
                            <a
                              href={stageRunDashboardLink(stageRun)}
                              target="_blank"
                              rel="noreferrer"
                              className={STAGE_ACTION_BUTTON_CLASS}
                            >
                              Open Dashboard
                            </a>
                            <button
                              onClick={() => router.push(appLink(stageRun.app, stageRun.workflow_id, stageRun.run_id))}
                              className={STAGE_ACTION_BUTTON_CLASS}
                            >
                              Open App Form
                            </button>
                            <a
                              href={`/api/workflow/${stageRun.workflow_id}/download_zip?full=1`}
                              className={STAGE_ACTION_BUTTON_CLASS}
                            >
                              Download ZIP
                            </a>
                          </>
                        ) : null}
                        <span className={`rounded-md px-2 py-1 text-xs ${
                          stageRun.status === "completed"
                            ? "bg-emerald-500/10 text-emerald-200"
                            : stageRun.status === "failed"
                            ? "bg-rose-500/10 text-rose-200"
                            : "bg-cyan-500/10 text-cyan-200"
                        }`}>
                          {stageRun.status}
                        </span>
                      </div>
                      <div className="text-xs text-slate-500 sm:basis-full">
                        Started {formatDate(stageRun.started_at)} | Completed {formatDate(stageRun.completed_at)} | Agents {stageRunAgentCount(stageRun) ?? "not reported"}
                      </div>
                      {stageRun.error ? <div className="text-xs text-rose-300 sm:basis-full">{stageRun.error}</div> : null}
                    </div>
                  ))}
                  </div>
                </div>
              ) : null}
              <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950 p-4">
                <div className="flex items-center justify-between gap-3">
                  <div>
                    <div className="text-sm font-semibold text-white">Run Log</div>
                    <div className="mt-1 text-xs text-slate-500">Product-level orchestration log for queued, running, completed, and failed stages. Scroll to review long agent lists.</div>
                  </div>
                  <span className="rounded-md bg-slate-900 px-2 py-1 text-xs text-slate-400">{productRunLogLines.length} lines</span>
                </div>
                <div className="mt-3 max-h-96 overflow-y-auto overflow-x-auto rounded-md bg-black/50 p-3 font-mono text-xs leading-5 text-slate-200">
                  {productRunLogLines.length ? productRunLogLines.map((line, index) => (
                    <div key={`${index}-${line}`} className={line.includes("Failed") || line.includes("failed") ? "text-rose-300" : line.includes("Completed") ? "text-emerald-300" : "text-slate-300"}>
                      {line}
                    </div>
                  )) : (
                    <div className="text-slate-500">No product run log lines yet. The log appears after the run is queued.</div>
                  )}
                </div>
              </div>
            </div>
          ) : null}
          {runHistory.length ? (
            <div className="mt-4 rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Run history</div>
              <div className="mt-3 grid gap-2">
                {runHistory.slice(0, 8).map((run) => (
                  <div
                    key={run.id}
                    className={`flex flex-col gap-1 rounded-lg border px-3 py-2 text-left transition sm:flex-row sm:items-center sm:justify-between ${
                      productRun?.id === run.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-900/60 hover:border-slate-600"
                    }`}
                  >
                    <button
                      type="button"
                      onClick={() => {
                        setProductRun(run);
                        setStageRuns(run.stage_runs || []);
                      }}
                      className="min-w-0 flex-1 text-left"
                    >
                      <span className="block truncate text-xs text-slate-300">{run.id}</span>
                    </button>
                    <div className="flex items-center gap-2">
                      <span className={`rounded-md px-2 py-1 text-xs ${
                        run.status === "completed"
                          ? "bg-emerald-500/10 text-emerald-200"
                          : run.status === "failed"
                          ? "bg-rose-500/10 text-rose-200"
                          : "bg-cyan-500/10 text-cyan-200"
                      }`}>
                        {run.status}
                      </span>
                      <button
                        type="button"
                        title="Delete run history entry"
                        aria-label="Delete run history entry"
                        onClick={() => deleteRunHistory(run)}
                        disabled={deletingRunId === run.id}
                        className="rounded-md border border-slate-700 px-2 py-1 text-xs font-semibold text-slate-300 transition hover:border-rose-400 hover:bg-rose-500/10 hover:text-rose-100 disabled:cursor-not-allowed disabled:opacity-50"
                      >
                        {deletingRunId === run.id ? "Deleting" : "Delete"}
                      </button>
                    </div>
                  </div>
                ))}
              </div>
            </div>
          ) : null}
          <div className="mt-4 grid gap-3 sm:grid-cols-3">
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Automatic handoff</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">RTL, verify, firmware, software, validation, and product app workflow IDs will be bound automatically.</p>
            </div>
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Gated execution</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">Required stages must pass before dependent stages run. Optional stages can be skipped.</p>
            </div>
            <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
              <div className="text-sm font-semibold text-white">Integrated results</div>
              <p className="mt-2 text-xs leading-5 text-slate-400">The product dashboard will link each stage dashboard and summarize coverage, artifacts, and blockers.</p>
            </div>
          </div>
        </section>
      </div>
    </main>
  );
}
