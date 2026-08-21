#!/usr/bin/env python3

"""Validate YAML task specifications against available TLA+ modules and TLC configs."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import yaml


@dataclass
class FileMatch:
    """Represents a located file candidate."""

    path: Path
    score: int
    justification: str

    def to_json(self) -> Dict[str, object]:
        return {
            "path": self.path.as_posix(),
            "score": self.score,
            "justification": self.justification,
        }


@dataclass
class MappingRecord:
    task_file: Path
    module_name: str
    cfg_file: str
    module_matches: List[FileMatch] = field(default_factory=list)
    cfg_matches: List[FileMatch] = field(default_factory=list)
    module_status: str = "MISSING"
    cfg_status: str = "MISSING"
    notes: List[str] = field(default_factory=list)

    def to_json(self) -> Dict[str, object]:
        return {
            "task_file": self.task_file.as_posix(),
            "module_name": self.module_name,
            "cfg_file": self.cfg_file,
            "module_status": self.module_status,
            "cfg_status": self.cfg_status,
            "module_matches": [m.to_json() for m in self.module_matches],
            "cfg_matches": [m.to_json() for m in self.cfg_matches],
            "notes": self.notes,
        }


def discover_search_roots(workspace_root: Path) -> List[Path]:
    """Return directories that are likely to contain TLA/TLC artefacts."""

    candidates = [
        workspace_root / "tla_modules",
        workspace_root / "external",
        workspace_root / "agentic_loop",
        workspace_root / "gdpr",
        workspace_root / "blockchain",
        workspace_root / "iot",
        workspace_root / "p2p",
        workspace_root / "smart_contract",
    ]
    return [candidate for candidate in candidates if candidate.exists()]


def score_match(candidate: Path, desired_suffix: Sequence[str]) -> Tuple[int, str]:
    """Compute a heuristic score for how well candidate ends with desired suffix."""

    rel = candidate.as_posix()
    suffix_posix = "/".join(desired_suffix)
    if rel.endswith(suffix_posix):
        justification = f"path endswith '{suffix_posix}'"
        return 100, justification

    # Penalise distance between basename and any suffix component matches
    basename = candidate.name
    if desired_suffix and basename == desired_suffix[-1]:
        justification = "basename match"
        return 75, justification

    if desired_suffix and desired_suffix[-1] in rel:
        justification = f"contains '{desired_suffix[-1]}'"
        return 40, justification

    justification = "fallback candidate"
    return 10, justification


def normalise_to_workspace(path: Path, workspace_root: Path) -> Path:
    try:
        return path.relative_to(workspace_root)
    except ValueError:
        return path


def find_candidates(
    workspace_root: Path,
    search_roots: Sequence[Path],
    desired_suffix: Sequence[str],
    preferred_dirs: Optional[Sequence[Path]] = None,
) -> List[FileMatch]:
    """Return candidate files whose relative path ends with desired suffix components."""

    if not desired_suffix:
        return []

    suffix_path = Path(*desired_suffix)
    target_name = desired_suffix[-1]
    seen: Dict[Path, FileMatch] = {}

    preferred_dirs_resolved: List[Path] = []
    if preferred_dirs:
        for directory in preferred_dirs:
            abs_dir = directory if directory.is_absolute() else workspace_root / directory
            if abs_dir.exists():
                preferred_dirs_resolved.append(abs_dir.resolve())

    # Direct relative path resolution first
    direct_path = workspace_root / suffix_path
    if direct_path.exists():
        score, justification = score_match(direct_path.relative_to(workspace_root), desired_suffix)
        seen[direct_path.resolve()] = FileMatch(direct_path.relative_to(workspace_root), score, justification)

    # Search across candidate roots
    for root in search_roots:
        if not root.exists():
            continue
        for candidate in root.rglob(target_name):
            if any("SnapShot" in part for part in candidate.parts):
                continue
            try:
                rel = candidate.relative_to(workspace_root)
            except ValueError:
                rel = candidate

            score, justification = score_match(rel, desired_suffix)
            bonus_justification = None
            absolute_candidate = candidate.resolve()

            for preferred_dir in preferred_dirs_resolved:
                try:
                    absolute_candidate.relative_to(preferred_dir)
                    score += 50
                    rel_pref = normalise_to_workspace(preferred_dir, workspace_root)
                    bonus_justification = f"{justification}; preferred dir {rel_pref.as_posix()}"
                    break
                except ValueError:
                    continue

            if bonus_justification:
                justification = bonus_justification

            existing = seen.get(absolute_candidate)
            if existing is None or score > existing.score:
                seen[absolute_candidate] = FileMatch(rel, score, justification)

    return sorted(seen.values(), key=lambda entry: entry.score, reverse=True)


MODULE_DECL_RE = re.compile(r"^-+\s+MODULE\s+([A-Za-z0-9_']+)\s+-+$")


def status_from_matches(matches: Sequence[FileMatch]) -> Tuple[str, int]:
    if not matches:
        return "MISSING", 0
    top_score = matches[0].score
    top_count = sum(1 for match in matches if match.score == top_score)
    if top_count == 1:
        return "OK", top_score
    return "AMBIGUOUS", top_score


def validate_module_declaration(module_path: Path, expected_name: str, workspace_root: Path) -> Optional[str]:
    """Ensure the module declares the expected name."""

    try:
        with (workspace_root / module_path).open("r", encoding="utf-8") as handle:
            for line in handle:
                match = MODULE_DECL_RE.match(line.strip())
                if match:
                    declared = match.group(1)
                    if declared != expected_name:
                        return (
                            f"Declared module '{declared}' does not match expected '{expected_name}'"
                        )
                    return None
    except FileNotFoundError:
        return "Module file not found"
    except UnicodeDecodeError:
        return "Module file is not UTF-8 encoded"

    return "Module declaration not found"


def collect_task_files(tasks_root: Path) -> List[Path]:
    return sorted(tasks_root.rglob("*.yaml"))


def load_task_spec(task_path: Path) -> Dict[str, str]:
    try:
        with task_path.open("r", encoding="utf-8") as handle:
            data = yaml.safe_load(handle)
    except yaml.YAMLError as exc:  # pragma: no cover - defensive
        raise ValueError(f"Failed to parse YAML at {task_path}: {exc}") from exc

    required_keys = {"name", "module_name", "cfg_file"}
    missing = required_keys.difference(data)
    if missing:
        missing_list = ", ".join(sorted(missing))
        raise ValueError(f"Task {task_path} missing keys: {missing_list}")

    return {
        "module_name": str(data["module_name"]),
        "cfg_file": str(data["cfg_file"]),
    }


def analyse_task(
    workspace_root: Path,
    search_roots: Sequence[Path],
    task_path: Path,
) -> MappingRecord:
    spec = load_task_spec(task_path)
    module_name = spec["module_name"]
    cfg_file = spec["cfg_file"]

    record = MappingRecord(
        task_file=task_path.relative_to(workspace_root),
        module_name=module_name,
        cfg_file=cfg_file,
    )

    cfg_suffix = cfg_file.split("/")
    cfg_matches = find_candidates(workspace_root, search_roots, cfg_suffix)
    record.cfg_matches = cfg_matches
    cfg_status, _ = status_from_matches(cfg_matches)
    record.cfg_status = cfg_status

    module_suffix = [f"{module_name}.tla"]
    preferred_module_dirs: List[Path] = []
    if cfg_matches:
        top_cfg_score = cfg_matches[0].score
        preferred_module_dirs = [
            (workspace_root / Path(match.path)).parent
            for match in cfg_matches
            if match.score == top_cfg_score
        ]

    module_matches = find_candidates(
        workspace_root,
        search_roots,
        module_suffix,
        preferred_dirs=preferred_module_dirs,
    )
    record.module_matches = module_matches
    module_status, _ = status_from_matches(module_matches)
    if module_status != "MISSING" and module_matches:
        declaration_issue = validate_module_declaration(module_matches[0].path, module_name, workspace_root)
        if declaration_issue:
            record.notes.append(f"Module validation: {declaration_issue}")
            module_status = "INVALID"
    record.module_status = module_status

    if record.cfg_status == "AMBIGUOUS":
        record.notes.append("Multiple TLC configuration candidates located")

    if record.module_status == "AMBIGUOUS":
        record.notes.append("Multiple TLA module candidates located")

    return record


def summarise_records(records: Sequence[MappingRecord]) -> Dict[str, int]:
    summary: Dict[str, int] = {
        "tasks": len(records),
        "module_ok": 0,
        "module_ambiguous": 0,
        "module_missing": 0,
        "module_invalid": 0,
        "cfg_ok": 0,
        "cfg_ambiguous": 0,
        "cfg_missing": 0,
    }

    for record in records:
        if record.module_status == "OK":
            summary["module_ok"] += 1
        elif record.module_status == "AMBIGUOUS":
            summary["module_ambiguous"] += 1
        elif record.module_status == "INVALID":
            summary["module_invalid"] += 1
        else:
            summary["module_missing"] += 1

        if record.cfg_status == "OK":
            summary["cfg_ok"] += 1
        elif record.cfg_status == "AMBIGUOUS":
            summary["cfg_ambiguous"] += 1
        else:
            summary["cfg_missing"] += 1

    return summary


def print_report(records: Sequence[MappingRecord], summary: Dict[str, int]) -> None:
    divider = "=" * 88
    print(divider)
    print("YAML Task Mapping Report")
    print(divider)
    for record in records:
        print(f"Task: {record.task_file.as_posix()}")
        print(f"  Module '{record.module_name}' status: {record.module_status}")
        for match in record.module_matches[:5]:
            print(f"    - {match.path.as_posix()} (score={match.score}, {match.justification})")
        print(f"  Config '{record.cfg_file}' status: {record.cfg_status}")
        for match in record.cfg_matches[:5]:
            print(f"    - {match.path.as_posix()} (score={match.score}, {match.justification})")
        if record.notes:
            for note in record.notes:
                print(f"  Note: {note}")
        print("-" * 88)

    print("Summary:")
    print(f"  Total tasks: {summary['tasks']}")
    print(f"  Modules - OK: {summary['module_ok']}, Ambiguous: {summary['module_ambiguous']}, Invalid: {summary['module_invalid']}, Missing: {summary['module_missing']}")
    print(f"  Configs - OK: {summary['cfg_ok']}, Ambiguous: {summary['cfg_ambiguous']}, Missing: {summary['cfg_missing']}")
    print(divider)


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workspace-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Root directory of the repository (defaults to two levels above this script)",
    )
    parser.add_argument(
        "--tasks-dir",
        type=Path,
        default=None,
        help="Root directory containing YAML tasks (defaults to <workspace>/agentic_loop/tasks)",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        help="Write detailed mapping results to the specified JSON file",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit with non-zero status if any mapping is missing, ambiguous, or invalid",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    workspace_root = args.workspace_root.resolve()
    tasks_dir = args.tasks_dir or workspace_root / "agentic_loop" / "tasks"
    tasks_dir = tasks_dir.resolve()

    if not tasks_dir.exists():
        print(f"Tasks directory not found: {tasks_dir}", file=sys.stderr)
        return 2

    search_roots = discover_search_roots(workspace_root)

    records: List[MappingRecord] = []
    for task_path in collect_task_files(tasks_dir):
        try:
            record = analyse_task(workspace_root, search_roots, task_path)
        except Exception as exc:  # pragma: no cover - defensive
            relative_task = task_path.relative_to(workspace_root)
            record = MappingRecord(
                task_file=relative_task,
                module_name="<error>",
                cfg_file="<error>",
                module_status="ERROR",
                cfg_status="ERROR",
                notes=[f"Exception while analysing: {exc}"],
            )
        records.append(record)

    summary = summarise_records(records)
    print_report(records, summary)

    if args.output_json:
        output_path = args.output_json.resolve()
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with output_path.open("w", encoding="utf-8") as handle:
            json.dump([record.to_json() for record in records], handle, indent=2, sort_keys=True)

    if args.strict:
        has_failures = any(
            record.module_status not in {"OK"}
            or record.cfg_status not in {"OK"}
            for record in records
        )
        return 1 if has_failures else 0

    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    sys.exit(main())
