import time
import yaml
import requests
import subprocess
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

def upload_results(config, job_id, result_path):
    files = {"file": open(result_path, "rb")}
    r = requests.post(f"{config['backend_url']}/upload_results/{job_id}", files=files)
    print("📤 Uploaded results:", r.status_code)

def run_local_sim(job):
    print(f"🧠 Running simulation for job {job['id']}...")
    time.sleep(2)
    # Simulate log generation
    log_path = Path(f"results/job_{job['id']}.log")
    log_path.write_text("Simulation completed successfully\nCoverage: 85%")
    return log_path

def main():
    config = load_config()
    if not config:
        return

    register_runner(config)
    print("🔁 Polling for jobs... (Ctrl+C to stop)")

    while True:
        job = get_job(config)
        if job:
            print("🚀 Received job:", job["id"])
            result = run_local_sim(job)
            upload_results(config, job["id"], result)
        else:
            print("⏳ No job available. Sleeping...")
        time.sleep(10)

if __name__ == "__main__":
    main()
