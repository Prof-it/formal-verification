from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional


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
    module_dir: Path | str
    output_dir: Path | str
    prompt_mode: str = "one_shot"
    max_iterations: int = 3
    timeout_seconds: int = 180
    log_dir: Optional[Path | str] = None
    violation_dir: Optional[Path | str] = None
    seed: Optional[int] = None
    checkpoint_gated: bool = False

    def __post_init__(self) -> None:
        self.module_dir = Path(self.module_dir).expanduser().resolve()
        self.output_dir = Path(self.output_dir).expanduser().resolve()
        if self.log_dir is not None:
            self.log_dir = Path(self.log_dir).expanduser().resolve()
        if self.violation_dir is not None:
            self.violation_dir = Path(self.violation_dir).expanduser().resolve()


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
    counterexamples_seen: int = 0
    counterexamples_resolved: int = 0
    skills_applied: List[str] = field(default_factory=list)
    skills_successful: bool = False
    human_intervention: bool = False
    timing: Dict[str, float] = field(default_factory=dict)


@dataclass
class RunResult:
    task_name: str
    prompt_mode: str
    terminal_status: str
    attempts: List[AttemptRecord] = field(default_factory=list)
    metadata: Dict[str, str] = field(default_factory=dict)
    generation_success: bool = False
    initial_verification_success: bool = False
    repair_iterations: int = 0
    counterexamples_seen: int = 0
    counterexamples_resolved: int = 0
    skills_applied: List[str] = field(default_factory=list)
    skills_successful: int = 0
    learning_step_index: Optional[int] = None
    human_intervention: bool = False

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

    @property
    def final_verification_success(self) -> bool:
        return self.terminal_status == "success"

    @property
    def gsr_indicator(self) -> int:
        """Indicator contribution for Generation Success Rate (GSR)."""
        return 1 if self.generation_success else 0

    @property
    def ivsr_indicator(self) -> int:
        """Indicator contribution for Initial Verification Success Rate (IVSR)."""
        return 1 if self.initial_verification_success else 0

    @property
    def verification_gap_contribution(self) -> int:
        """Difference between GSR and IVSR contributions."""
        return self.gsr_indicator - self.ivsr_indicator

    @property
    def rsr_indicator(self) -> int:
        """Contribution to Repair Success Rate (RSR)."""
        if self.initial_verification_success:
            return 0
        return 1 if self.final_verification_success else 0

    @property
    def ari_contribution(self) -> int:
        """Number of repair iterations used by this run."""
        return self.repair_iterations

    @property
    def crr_numerator(self) -> int:
        """Resolved counterexamples contributed by this run."""
        return self.counterexamples_resolved

    @property
    def crr_denominator(self) -> int:
        """Total counterexamples observed by this run."""
        return self.counterexamples_seen

    @property
    def srr_numerator(self) -> int:
        """Successful skill reuse events contributed by this run."""
        return self.skills_successful

    @property
    def srr_denominator(self) -> int:
        """Total skill reuse attempts (any applied skills) contributed by this run."""
        return len(self.skills_applied)

    @property
    def learning_accuracy(self) -> int:
        """Final verification accuracy indicator (1=success, 0 otherwise)."""
        return 1 if self.final_verification_success else 0

    @property
    def hir_indicator(self) -> int:
        """Indicator contribution for Human Intervention Rate (HIR)."""
        return 1 if self.human_intervention else 0

    def iter_attempts_with_skills(self) -> Iterable[AttemptRecord]:
        """Yield attempts where any skill key was applied."""
        return (attempt for attempt in self.attempts if attempt.skills_applied)
