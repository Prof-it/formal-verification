"""Module/directory staging logic, refactored."""

import warnings
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional
import json
import shutil
import tempfile

# Path to task mapping JSON
TASK_MAPPINGS_PATH = Path("results/task_mappings.json")

class StagedModule:
    def __init__(self, root: Path, task_name: str, module_root: Path, cleanup: Optional[Callable[[], None]] = None):
        self.root = root
        self.task_name = task_name
        self.module_root = module_root
        self.cleanup = cleanup
        self._closed = False

    def close(self):
        self._run_cleanup()

    def _run_cleanup(self):
        if self._closed:
            return
        self._closed = True
        if self.cleanup:
            try:
                self.cleanup()
            except Exception as exc:
                warnings.warn(f"Failed to cleanup staged module directory '{self.root}': {exc}")

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


# _MappingCandidate data class
class _MappingCandidate:
    def __init__(self, score: float, path: Path, source: str, justification: str):
        self.score = score
        self.path = path
        self.source = source
        self.justification = justification

    def __lt__(self, other):
        return self.score < other.score

def _load_task_mapping() -> List[Dict[str, Any]]:
    if not TASK_MAPPINGS_PATH.exists():
        return []
    try:
        return json.loads(TASK_MAPPINGS_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []

def _find_mapping_entry(task_path: Path) -> Optional[Dict[str, Any]]:
    entries = _load_task_mapping()
    task_path_str = str(task_path)
    for entry in entries:
        recorded = entry.get("task_file")
        if not recorded:
            continue
        if recorded.endswith(task_path_str) or task_path_str.endswith(recorded):
            return entry
    return None

def _collect_mapping_candidates(mapping: Dict[str, Any]) -> List[_MappingCandidate]:
    candidates: List[_MappingCandidate] = []

    def _append_from_match(match: Dict[str, Any], source: str) -> None:
        raw_path = match.get("path")
        if not raw_path:
            return
        score_raw = match.get("score", 0)
        try:
            score = float(score_raw)
        except (TypeError, ValueError):
            score = 0.0
        justification = match.get("justification", "")
        candidate_path = Path(raw_path)
        for base in (Path.cwd(), Path.cwd().parent):
            resolved = (base / candidate_path).resolve()
            if resolved.exists():
                candidates.append(_MappingCandidate(score=score, path=resolved, source=source, justification=justification))
                break

    for match in mapping.get("cfg_matches") or []:
        _append_from_match(match, "cfg")
    for match in mapping.get("module_matches") or []:
        _append_from_match(match, "module")

    candidates.sort(key=lambda c: c.score, reverse=True)
    return candidates

def _infer_toolbox_root(path: Path) -> Path:
    current = path
    if current.is_file():
        current = current.parent
    for ancestor in (current, *current.parents):
        if ancestor.name.endswith(".toolbox"):
            return ancestor
    return current

def _stage_module_dir(task: Path, task_spec: Any, module_root: Path) -> Optional[StagedModule]:
    module_root = module_root.expanduser().resolve()
    module_root.mkdir(parents=True, exist_ok=True)
    # NOTE: purge_temp_modules should be called by caller, not here, in new design
    mapping = _find_mapping_entry(task)
    if not mapping:
        return None

    candidates = _collect_mapping_candidates(mapping)
    if not candidates:
        return None

    selected = candidates[0]
    toolbox_root = _infer_toolbox_root(selected.path)
    stage_source = toolbox_root.parent if toolbox_root.parent != toolbox_root else toolbox_root

    # PROTECTION: Prevent recursive or project-root copy!
    project_root = Path(__file__).resolve()
    for parent in project_root.parents:
        if parent.name == 'agentic_loop':
            project_root = parent.resolve()
            break
    if project_root in stage_source.resolve().parents or stage_source.resolve() == project_root:
        warnings.warn(
            f"Refusing to recursively stage/copy project root directory '{project_root}' (source: '{stage_source}') for task '{getattr(task_spec, 'name', str(task_spec))}'."
        )
        return None

    tmp_parent = Path(tempfile.mkdtemp(prefix=f"{getattr(task_spec, 'name', 'task')}_", dir=str(module_root.resolve())))
    staged_source = tmp_parent / stage_source.name
    try:
        shutil.copytree(stage_source, staged_source, dirs_exist_ok=True)
    except Exception as exc:
        shutil.rmtree(tmp_parent, ignore_errors=True)
        warnings.warn(
            f"Failed to stage module directory '{stage_source}' for task '{getattr(task_spec, 'name', str(task_spec))}': {exc}"
        )
        return None

    staged_toolbox = staged_source / toolbox_root.name if stage_source != toolbox_root else staged_source
    if len(candidates) > 1:
        alt_details = ", ".join(
            f"{cand.path} (score={cand.score}, source={cand.source})" for cand in candidates[1:]
        )
        print(
            f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score}) while other candidates were: {alt_details}"
        )
    else:
        print(f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score})")

    return StagedModule(
        root=staged_toolbox.resolve(),
        task_name=getattr(task_spec, 'name', str(task_spec)),
        module_root=module_root,
        cleanup=None
    )

def _resolve_module_dir(args, task_path: Path, task_spec: Any) -> StagedModule:
    """Given CLI args, return a staged or resolved module directory binding (refactored logic)."""
    module_root = Path(args.module_root).expanduser().resolve()
    if args.module_dir:
        module_dir = Path(args.module_dir)
        if not module_dir.exists():
            raise FileNotFoundError(f"Module directory '{module_dir}' not found.")
        module_dir = module_dir.expanduser().resolve()
        return StagedModule(
            root=module_dir,
            task_name=getattr(task_spec, 'name', str(task_spec)),
            module_root=module_root,
            cleanup=None,
        )
    candidate = module_root / getattr(task_spec, 'name', str(task_spec))
    if candidate.exists():
        candidate = candidate.expanduser().resolve()
        return StagedModule(
            root=candidate,
            task_name=getattr(task_spec, 'name', str(task_spec)),
            module_root=module_root,
            cleanup=None,
        )
    staged_result = _stage_module_dir(task_path, task_spec, module_root)
    if staged_result and staged_result.root.exists():
        return staged_result
    # If no module directory is found or mapped, create a fresh temp dir and let the bootstrap take over
    fresh_moduledir = Path(tempfile.mkdtemp(prefix=f"{getattr(task_spec, 'name', 'task')}_", dir=str(module_root.resolve())))
    print(f"[Bootstrap-Module] No input module-dir given; created temp dir: {fresh_moduledir}")
    return StagedModule(
        root=fresh_moduledir,
        task_name=getattr(task_spec, 'name', str(task_spec)),
        module_root=module_root,
        cleanup=None,
    )