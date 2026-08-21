from __future__ import annotations

from pathlib import Path
from typing import Any, Dict

import yaml

from .models import TaskSpec


REQUIRED_KEYS = ["name", "module_name", "cfg_file", "system_text", "requirement_text"]


def load_task_spec(task_file: str) -> TaskSpec:
    path = Path(task_file)
    if not path.exists():
        raise FileNotFoundError(f"Task file not found: {task_file}")

    with path.open("r", encoding="utf-8") as handle:
        raw: Dict[str, Any] = yaml.safe_load(handle)

    missing = [key for key in REQUIRED_KEYS if key not in raw]
    if missing:
        joined = ", ".join(missing)
        raise ValueError(f"Task file missing required keys: {joined}")

    return TaskSpec(
        name=str(raw["name"]),
        module_name=str(raw["module_name"]),
        cfg_file=str(raw["cfg_file"]),
        system_text=str(raw["system_text"]),
        requirement_text=str(raw["requirement_text"]),
    )
