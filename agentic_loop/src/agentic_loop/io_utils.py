import json
from pathlib import Path

def save_tlc_log(log_dir, attempt_id, tlc_output):
    log_dir = Path(log_dir)
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / f"attempt_{attempt_id}_tlc_output.txt"
    with open(log_file, "w", encoding="utf-8") as f:
        f.write(tlc_output)
    return str(log_file)

def load_skills(skills_json_path="skills.json"):
    with open(skills_json_path, encoding="utf-8") as f:
        return json.load(f)
