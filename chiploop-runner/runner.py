import time
import yaml
import requests
import subprocess
import os
import glob
from pathlib import Path

CONFIG_FILE = Path("config.yaml")

# -------------------------------------------------------------------
# Configuration Loader
# -------------------------------------------------------------------
def load_config():
    if not CONFIG_FILE.exists():
        print("❌ config.yaml not found. Please create one.")
        return None
    with open(CONFIG_FILE, "r") as f:
        return yaml.safe_load(f)

# -------------------------------------------------------------------
# Runner Registration
# -------------------------------------------------------------------
def register_runner(config):
    """Register this runner instance with the backend."""
    payload = {
        "runner_name": config["runner_name"],
        "email": config["email"],
        "token": config["supabase_token"]
    }
    try:
        r = requests.post(f"{config['backend_url']}/register_runner", json=payload)
        if r.status_code == 200:
            print(f"✅ Runner registered: {config['runner_name']}")
        else:
            print(f"⚠️ Runner registration failed ({r.status_code}): {r.text}")
    except Exception as e:
        print(f"❌ Error registering runner: {e}")

# -------------------------------------------------------------------
# Job Fetcher
# -------------------------------------------------------------------
def get_job(config):
    """Poll backend for a queued simulation job."""
    try:
        r = requests.get(f"{config['backend_url']}/get_job?runner={config['runner_name']}")
        if r.status_code == 200 and r.json().get("job"):
            job = r.json()["job"]
            print(f"🎯 Job {job['workflow_id']} assigned to {config['runner_name']}")
            return job
        return None
    except Exception as e:
        print(f"⚠️ Error fetching job: {e}")
        return None

# -------------------------------------------------------------------
# Upload Results
# -------------------------------------------------------------------
def upload_results(config, workflow_id, status, logs, artifacts=None):
    """Upload simulation results back to backend."""
    url = f"{config['backend_url']}/upload_results"
    payload = {
        "workflow_id": workflow_id,
        "status": status,
        "logs": logs,
        "artifacts": artifacts or {},
        "runner_name": config["runner_name"],
    }
    try:
        response = requests.post(url, json=payload)
        if response.status_code == 200:
            print(f"✅ Results uploaded for job {workflow_id}")
        else:
            print(f"❌ Upload failed: {response.status_code} {response.text}")
    except Exception as e:
        print(f"❌ Upload exception: {e}")

# -------------------------------------------------------------------
# Questa Simulation
# -------------------------------------------------------------------
def run_questa_simulation(config, workflow_id, design_dir, top_module):
    sim_dir = Path(f"sim_{workflow_id}")
    sim_dir.mkdir(exist_ok=True)

    questa_path = config.get("questa_path", "")
    if questa_path:
        os.environ["PATH"] += os.pathsep + questa_path

    try:
        print(f"🧠 Launching Questa simulation + coverage for {workflow_id}...")

        # Collect all SV/V files recursively — fully generic
        sv_files = glob.glob(f"{design_dir}/**/*.sv", recursive=True)
        v_files = glob.glob(f"{design_dir}/**/*.v", recursive=True)
        cmd_compile = ["vlog", "-cover", "bcest", "+acc=rn"] + v_files + sv_files

        print(f"📘 Compiling {len(cmd_compile) - 4} design/testbench files...")
        subprocess.run(cmd_compile, check=True)

        # Run Questa simulation with coverage
        subprocess.run(
            ["vsim", "-c", "-coverage", top_module, "-do", "run -all; exit"],
            check=True
        )

        # Generate coverage report
        subprocess.run(
            ["vcover", "report", "-details", "coverage.ucdb"],
            check=False  # don’t fail if UCDB missing
        )

        coverage_file = Path("coverage_report.txt")
        coverage_logs = (
            coverage_file.read_text()
            if coverage_file.exists()
            else "⚠️ coverage_report.txt not found — possible Questa path issue."
        )

        upload_results(
            config,
            workflow_id,
            "completed",
            coverage_logs,
            {"coverage_report": "coverage_report.txt", "ucdb": "coverage.ucdb"},
        )

        print(f"✅ Questa simulation + coverage completed for {workflow_id}")
        return True

    except subprocess.CalledProcessError as e:
        print(f"⚠️ Questa simulation failed for {workflow_id}: {e}")
        upload_results(config, workflow_id, "failed", f"❌ Questa simulation failed: {e}")
        return False

# -------------------------------------------------------------------
# Verilator / Icarus Fallback
# -------------------------------------------------------------------
def run_fallback_simulation(config, workflow_id, design_dir, top_module):
    sim_dir = Path(f"sim_{workflow_id}_fallback")
    sim_dir.mkdir(exist_ok=True)
    print(f"🔁 Running fallback simulation (Verilator → Icarus) for {workflow_id}...")

    try:
        subprocess.run([
            "verilator", "--cc", f"{design_dir}/{top_module}.sv",
            "--exe", "--build", "--trace"
        ], check=True)
        upload_results(config, workflow_id, "completed", "✅ Verilator simulation succeeded.")
        print("✅ Verilator fallback succeeded.")
        return True
    except Exception:
        print("⚠️ Verilator failed, switching to Icarus...")

    try:
        subprocess.run([
            "iverilog", "-g2012", "-o", f"{sim_dir}/sim.out",
            *[str(f) for f in Path(design_dir).rglob("*.sv")],
            *[str(f) for f in Path(design_dir).rglob("*.v")]
        ], check=True)
        subprocess.run([f"{sim_dir}/sim.out"], check=True)
        upload_results(config, workflow_id, "completed", "✅ Icarus Verilog simulation succeeded.")
        print("✅ Icarus fallback succeeded.")
        return True
    except subprocess.CalledProcessError as e:
        upload_results(config, workflow_id, "failed", f"❌ All simulations failed: {e}")
        print(f"❌ All simulations failed for {workflow_id}")
        return False

# -------------------------------------------------------------------
# Artifact Fetcher
# -------------------------------------------------------------------
def fetch_artifacts(config, workflow_id, retries=3, delay=3):
    """Download all design/testbench artifacts from backend."""
    base_url = config["backend_url"]
    out_dir = Path("downloads") / workflow_id
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"📦 Fetching all artifacts for workflow {workflow_id}...")

    for attempt in range(retries):
        try:
            index_url = f"{base_url}/list_artifacts/{workflow_id}"
            resp = requests.get(index_url, timeout=10)
            if resp.status_code != 200:
                print(f"⚠️ Attempt {attempt+1}: Failed to get file index (HTTP {resp.status_code})")
                time.sleep(delay)
                continue

            files = resp.json().get("files", [])
            if not files:
                print(f"⚠️ No files found yet (Attempt {attempt+1}/{retries})")
                time.sleep(delay)
                continue

            download_list = [f for f in files if f.lower().endswith((".v", ".sv", ".json", ".txt", ".log"))]
            for rel_path in download_list:
                rel_path = rel_path.replace("\\", "/")
                url = f"{base_url}/download_artifacts/{workflow_id}/{rel_path}"
                dest = out_dir / Path(rel_path).name
                try:
                    resp2 = requests.get(url, timeout=15)
                    if resp2.status_code == 200:
                        with open(dest, "wb") as f:
                            f.write(resp2.content)
                        print(f"✅ Downloaded {rel_path}")
                    else:
                        print(f"⚠️ Skipped {rel_path} (HTTP {resp2.status_code})")
                except Exception as e:
                    print(f"❌ Error fetching {rel_path}: {e}")

            if download_list:
                print(f"✅ All artifacts downloaded ({len(download_list)} files).")
                return out_dir

        except Exception as e:
            print(f"❌ Attempt {attempt+1}: Error listing artifacts: {e}")
            time.sleep(delay)

    print(f"🚫 Failed to fetch artifacts after {retries} attempts.")
    return out_dir

# -------------------------------------------------------------------
# Main Loop
# -------------------------------------------------------------------
def main():
    config = load_config()
    if not config:
        return

    register_runner(config)
    print("🔁 Polling for jobs... (Ctrl+C to stop)")

    while True:
        job = get_job(config)
        if job:
            workflow_id = job["workflow_id"]
            top_module = job.get("top_module", "tb_counter_4b")
            design_dir = fetch_artifacts(config, workflow_id)
            print(f"\n🚀 Executing job {workflow_id} ...")

            success = run_questa_simulation(config, workflow_id, design_dir, top_module)
            if not success:
                run_fallback_simulation(config, workflow_id, design_dir, top_module)
        else:
            print("⏳ No job available. Sleeping...")
            time.sleep(10)

if __name__ == "__main__":
    main()
