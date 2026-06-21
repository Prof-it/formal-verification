from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass
class TaskSpec:
    name: str
    module_name: str
    cfg_file: str
    system_text: str
    requirement_text: str


@dataclass
class LoopConfig:
    tla_jar_path: str
    module_dir: str
    output_dir: str
    prompt_mode: str = "one_shot"
    max_iterations: int = 3
    timeout_seconds: int = 180


@dataclass
class AttemptRecord:
    attempt_id: int
    phase: str
    prompt_name: str
    module_file: str
    status: str
    parse_ok: bool
    semantic_ok: bool
    invariants_violated: bool
    error_count: int
    feedback_excerpt: str


@dataclass
class RunResult:
    task_name: str
    prompt_mode: str
    terminal_status: str
    attempts: List[AttemptRecord] = field(default_factory=list)
    metadata: Dict[str, str] = field(default_factory=dict)

    @property
    def parse_success_rate(self) -> float:
        if not self.attempts:
            return 0.0
        ok = sum(1 for a in self.attempts if a.parse_ok)
        return ok / len(self.attempts)

    @property
    def semantic_success_rate(self) -> float:
        if not self.attempts:
            return 0.0
        ok = sum(1 for a in self.attempts if a.semantic_ok)
        return ok / len(self.attempts)
