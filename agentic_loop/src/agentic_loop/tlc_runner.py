from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import List
import logging

import os


logging.basicConfig(level=logging.INFO)

PARSE_PATTERNS = [
    re.compile(r"Parse Error", re.IGNORECASE),
    re.compile(r"Was expecting", re.IGNORECASE),
    re.compile(r"Unable to parse", re.IGNORECASE),
    re.compile(r"beginning of module", re.IGNORECASE),
]

SEMANTIC_PATTERNS = [
    re.compile(r"Unknown operator", re.IGNORECASE),
    re.compile(r"Semantic error", re.IGNORECASE),
    re.compile(r"attempted to apply", re.IGNORECASE),
    re.compile(r"identifier .* undefined", re.IGNORECASE),
]


@dataclass
class TLCResult:
    status: str
    parse_ok: bool
    semantic_ok: bool
    invariants_violated: bool
    output: str
    errors: List[str]


def _collect_matches(output: str, patterns: List[re.Pattern]) -> List[str]:
    matches: List[str] = []
    for pattern in patterns:
        for found in pattern.findall(output):
            matches.append(str(found))
    return matches


def run_tlc(
    tla_jar_path: str,
    module_dir: str,
    module_name: str,
    cfg_file: str,
    metadir: str,
    timeout_seconds: int,
) -> TLCResult:
    jar = Path(tla_jar_path).expanduser().resolve()
    if not jar.exists():
        return TLCResult(
            status="tool_missing",
            parse_ok=False,
            semantic_ok=False,
            invariants_violated=False,
            output=f"Missing tla2tools.jar at {jar}",
            errors=["missing_tla2tools_jar"],
        )

    command = [
        "java",
        "-XX:+IgnoreUnrecognizedVMOptions",
        "-cp",
        str(jar),
        "tlc2.TLC",
        "-nowarning",
        "-metadir",
        os.path.abspath(metadir),
        "-config",
        os.path.abspath(cfg_file),
        "-modelcheck",
        module_name,
    ]
    # Debug: print full command and working directory
    logging.info(f"[TLC] Command: {' '.join(command)} | cwd={os.path.abspath(module_dir)}")

    try:
        proc = subprocess.run(
            command,
            cwd=os.path.abspath(module_dir),
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        output = f"{exc.stdout or ''}\n{exc.stderr or ''}"
        logging.info(f"TLC Timeout Output:\n{output}")
        return TLCResult(
            status="timeout",
            parse_ok=False,
            semantic_ok=False,
            invariants_violated=False,
            output=output,
            errors=["timeout"],
        )

    output = (proc.stdout or "") + "\n" + (proc.stderr or "")

    parse_errors = _collect_matches(output, PARSE_PATTERNS)
    semantic_errors = _collect_matches(output, SEMANTIC_PATTERNS)

    parse_ok = len(parse_errors) == 0
    semantic_ok = len(semantic_errors) == 0
    invariants_violated = bool(
        re.search(r"Invariant .* is violated|Invariant violated", output, re.IGNORECASE)
    )

    if proc.returncode == 0 and "No error has been found" in output:
        return TLCResult(
            status="success",
            parse_ok=True,
            semantic_ok=True,
            invariants_violated=False,
            output=output,
            errors=[],
        )

    if not parse_ok:
        return TLCResult(
            status="parse_error",
            parse_ok=False,
            semantic_ok=False,
            invariants_violated=False,
            output=output,
            errors=parse_errors,
        )

    if invariants_violated:
        return TLCResult(
            status="invariant_violation",
            parse_ok=True,
            semantic_ok=True,
            invariants_violated=True,
            output=output,
            errors=["invariant_violation"],
        )

    if not semantic_ok:
        return TLCResult(
            status="semantic_error",
            parse_ok=True,
            semantic_ok=False,
            invariants_violated=False,
            output=output,
            errors=semantic_errors,
        )

    return TLCResult(
        status="tlc_error",
        parse_ok=parse_ok,
        semantic_ok=semantic_ok,
        invariants_violated=invariants_violated,
        output=output,
        errors=[f"exit_code_{proc.returncode}"],
    )
