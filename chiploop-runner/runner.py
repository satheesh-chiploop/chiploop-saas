import time
import yaml
import requests
import subprocess
import os
from pathlib import Path

CONFIG_FILE = Path("config.yaml")

def load_config():
    if not CONFIG_FILE.exists():
        print("❌ config.yaml not found. Please create one.")
        return None
    with open(CONFIG_FILE, "r") as f:
        return yaml.safe_load(f)

def register_runner(config):
    payload = {
        "runner_name": config["runner_name"],
        "email": config["email"],
        "token": config["supabase_token"]
    }
    r = requests.post(f"{config['backend_url']}/register_runner", json=payload)
    print("✅ Runner registered:", r.text)

def get_job(config):
    r = requests.get(f"{config['backend_url']}/get_job?runner={config['runner_name']}")
    if r.status_code == 200 and r.json().get("job"):
        return r.json()["job"]
    return None

# -------------------------------------------------------------------
# Updated upload_results function
# -------------------------------------------------------------------
def upload_results(config, workflow_id, status, logs, artifacts=None):
    """
    Upload simulation results back to backend.
    Includes runner_name for backend tracking.
    """
    url = f"{config['backend_url']}/upload_results"
    payload = {
        "workflow_id": workflow_id,
        "status": status,
        "logs": logs,
        "artifacts": artifacts or {},
        "runner_name": config["runner_name"],  # 🆕 added
    }
    response = requests.post(url, json=payload)
    if response.status_code == 200:
        print(f"✅ Results uploaded for job {workflow_id}")
    else:
        print(f"❌ Upload failed: {response.status_code} {response.text}")

# -------------------------------------------------------------------
# Simulation logic
# -------------------------------------------------------------------
def run_questa_simulation(config, workflow_id, design_dir, top_module):
    sim_dir = Path(f"sim_{workflow_id}")
    sim_dir.mkdir(exist_ok=True)

    questa_path = config.get("questa_path", "")
    if questa_path:
        os.environ["PATH"] += os.pathsep + questa_path

    try:
        print(f"🧠 Launching Questa simulation for {workflow_id}...")
        subprocess.run(
            ["simulate.bat", str(design_dir), top_module, str(sim_dir)],
            check=True, shell=True
        )
        coverage_path = sim_dir / "coverage_report.txt"
        coverage_text = coverage_path.read_text() if coverage_path.exists() else "⚠️ Coverage report not found."
        upload_results(config, workflow_id, "completed", coverage_text, {"report": str(coverage_path)})  # 🆕 passed config
        print(f"✅ Questa simulation completed for {workflow_id}")
        return True
    except subprocess.CalledProcessError as e:
        print(f"⚠️ Questa simulation failed for {workflow_id}: {e}")
        return False

def run_fallback_simulation(config, workflow_id, design_dir, top_module):
    sim_dir = Path(f"sim_{workflow_id}_fallback")
    sim_dir.mkdir(exist_ok=True)
    print(f"🔁 Running fallback simulation (Verilator → Icarus) for {workflow_id}...")

    try:
        # Try Verilator first
        subprocess.run([
            "verilator", "--cc", f"{design_dir}/{top_module}.sv",
            "--exe", "--build", "--trace"
        ], check=True)
        upload_results(config, workflow_id, "completed", "✅ Verilator simulation succeeded.")  # 🆕 passed config
        print("✅ Verilator fallback succeeded.")
        return True
    except Exception:
        print("⚠️ Verilator failed, switching to Icarus...")

    try:
        subprocess.run([
            "iverilog", "-g2012", "-o", f"{sim_dir}/sim.out",
            *[str(f) for f in Path(design_dir).glob("*.sv")],
            *[str(f) for f in Path(design_dir).glob("*.v")]
        ], check=True)
        subprocess.run([f"{sim_dir}/sim.out"], check=True)
        upload_results(config, workflow_id, "completed", "✅ Icarus Verilog simulation succeeded.")  # 🆕 passed config
        print("✅ Icarus fallback succeeded.")
        return True
    except subprocess.CalledProcessError as e:
        upload_results(config, workflow_id, "failed", f"❌ All simulations failed: {e}")  # 🆕 passed config
        print(f"❌ All simulations failed for {workflow_id}")
        return False

# -------------------------------------------------------------------
# Runner main loop
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
            design_dir = Path(job.get("design_dir", f"backend/workflows/{workflow_id}"))
            top_module = job.get("top_module", "tb_counter_4b")

            print(f"\n🚀 Executing job {workflow_id} ...")
            success = run_questa_simulation(config, workflow_id, design_dir, top_module)
            if not success:
                run_fallback_simulation(config, workflow_id, design_dir, top_module)
        else:
            print("⏳ No job available. Sleeping...")
            time.sleep(10)

if __name__ == "__main__":
    main()
