from __future__ import annotations


from pathlib import Path
from typing import Callable, Dict, Optional

from .models import AttemptRecord, LoopConfig, RunResult, TaskSpec
from .prompting import load_prompt_template, render_prompt
from .providers import LLMProvider
from .reporting import persist_run_result, write_violation_report
from .tlc_runner import run_tlc

import logging
import json
import time
import os
import re
import random
import numpy as np
from .utils.io_utils import (
    save_tlc_log, 
    load_skills, 
    _coerce_module_dir,
    validate_module_layout,
    _write_module,
    generate_cfg_for_tla,
    generate_cfg_via_llm,
    get_failure_classes_from_attempt
    )
from .utils.tlc_error_utils import classify_tlc_error
from .utils.trace_utils import parse_tlc_trace
from .utils.repair_utils import (
    clear_skill_attempt_session,
    try_register_candidate_rule, 
    apply_known_skill
)
from .utils.llm_policy_utils import first_undefined_operator
from .utils.llm_error_analysis import llm_analyze_tlc_error
from .user_approval_utils import prompt_human_for_skill_approval
from .utils.tla_patch_utils import (
    sanitize_quantifier_bounds,
    remove_invariants_if_undefined,
    patch_cfg_with_constants,
    extract_invariant_code,
)
from .utils.general_utils import print_source_with_line_numbers, is_multi_operator_issue

MAX_SUGGESTIONS = 2


    



def run_experiment(
    task: TaskSpec,
    config: LoopConfig,
    prompts_dir: str,
    provider: LLMProvider,
    mode: str,
    *,
    human_intervention_callback: Optional[Callable[[AttemptRecord], bool]] = None,
    learning_step_index: Optional[int] = None,
    apply_patch: bool = True,
    initial_spec_override: Optional[str] = None  # NEW: for paired experiment initial spec injection
) -> Dict[str, str]:
    overall_start_time = time.time()

    unpatched_attempts = []


    if mode not in {"baseline", "loop"}:
        raise ValueError("mode must be 'baseline' or 'loop'")

    module_dir = _coerce_module_dir(config.module_dir)
    validate_module_layout(task, module_dir)

    # Optionally set random seed for reproducibility if supported by provider/backend
    seed = getattr(config, "seed", None)
    if seed is not None:
        random.seed(seed)
        try:
            np.random.seed(seed)
        except ImportError:
            pass

    initial_prompt_name = config.prompt_mode
    initial_template = load_prompt_template(prompts_dir, initial_prompt_name)

    current_prompt = render_prompt(
        initial_template,
        {
            "system_text": task.system_text,
            "requirement_text": task.requirement_text,
            "module_name": task.module_name,
            "previous_spec": "",
            "tool_feedback": "",
        },
    )

    # Eagerly load baseline LLM .cfg generation prompt up front if patching is OFF (for baseline mode)
    cfg_generation_template = None
    if not apply_patch:
        try:
            cfg_generation_template = load_prompt_template(prompts_dir, "cfg_generation")
        except Exception as e:
            raise RuntimeError(f"[ConfigGen] Could not load prompt 'cfg_generation' from {prompts_dir}: {e}")


    result = RunResult(
        task_name=task.name,
        prompt_mode=config.prompt_mode,
        terminal_status="unknown",
        learning_step_index=learning_step_index,
    )
    # --- PATCH: clear skill/session tracking for this repair session ---
    clear_skill_attempt_session()

    max_iterations = 1 if mode == "baseline" else config.max_iterations
    latest_spec = ""
    outstanding_counterexamples = 0

    # Checkpoint gated logic for loop mode
    checkpoint_gated = getattr(config, "checkpoint_gated", False)
    total_counterexamples_seen = 0
    total_counterexamples_resolved = 0
    applied_skill_keys: list[str] = []
    successful_skill_uses = 0
    human_intervention_flag = False
    pending_session_rule = None

    for attempt_id in range(1, max_iterations + 1):
        phase = "generate" if attempt_id == 1 else "repair"
        # --- Timing: attempt overall ---
        attempt_timing = {}
        attempt_timing["start_attempt"] = time.time()

        # --- Timing: LLM call ---
        attempt_timing["start_llm"] = time.time()

        # Paired experiment: for loop mode, attempt 1, use the override if provided
        if (
            mode == "loop"
            and attempt_id == 1
            and initial_spec_override is not None
            and os.path.exists(initial_spec_override)
        ):
            with open(initial_spec_override, "r", encoding="utf-8") as f:
                generated = f.read()
        else:
            generated = provider.generate(current_prompt, {"attempt_id": str(attempt_id), "phase": phase})



        if apply_patch:
            # Patch the SPEC only here (one-pass)
            latest_spec = generated
            latest_spec = re.sub(r"([a-zA-Z_][a-zA-Z0-9_]*)''", r"\1'", latest_spec)
            latest_spec = sanitize_quantifier_bounds(latest_spec)
            # Optionally: auto-stub missing invariants (if you want), or skip if you want pure removal instead
            # latest_spec = ensure_invariants(latest_spec, ...)  

        else:
            latest_spec = generated
            unpatched_attempts.append(latest_spec)

        # Now write the fully patched spec to disk
        module_snapshot = _write_module(module_dir, task.module_name, latest_spec, attempt_id)
        module_snapshot_str = str(module_snapshot)
        snapshot_name = f"{task.module_name}_attempt_{attempt_id}"

        if apply_patch:
            # Standard deterministic config gen logic:
            bootstrap_cfg_path = Path(__file__).resolve().parent.parent.parent / "default_bootstrap/BootstrapModule.cfg"
            out_cfg_path = module_dir / f"{snapshot_name}.cfg"
            generated_cfg_path = generate_cfg_for_tla(str(module_snapshot), str(bootstrap_cfg_path), str(out_cfg_path))
            remove_invariants_if_undefined(latest_spec, str(generated_cfg_path))
            generated_cfg_path = patch_cfg_with_constants(latest_spec, str(generated_cfg_path), str(attempt_id))
        else:
            # Use preloaded LLM-generated config prompt
            generated_cfg_path = generate_cfg_via_llm(
                module_snapshot, task, provider, attempt_id, prompts_dir, cfg_generation_template=cfg_generation_template
            )

        attempt_timing["end_llm"] = time.time()
        attempt_timing["duration_llm"] = attempt_timing["end_llm"] - attempt_timing["start_llm"]


        metadir = str(module_dir / f".tlc_{task.name}_attempt_{attempt_id}")
        # Instead of module_name, always use the actual snapshot file (w/o .tla extension) as TLC main module

        # --- Timing: TLC call ---
        attempt_timing["start_tlc"] = time.time()
        tlc = run_tlc(
            tla_jar_path=config.tla_jar_path,
            module_dir=str(module_dir),
            module_name=snapshot_name,  # <--- always match file's MODULE header and filename
            cfg_file=generated_cfg_path,
            metadir=metadir,
            timeout_seconds=config.timeout_seconds,
        )
        attempt_timing["end_tlc"] = time.time()
        attempt_timing["duration_tlc"] = attempt_timing["end_tlc"] - attempt_timing["start_tlc"]



        # Checkpoint gated: if enabled and TLC passes, break early (loop mode only)
        if tlc.status == "success":
            print("[DEBUG] Using new TLC-pass gate logic!")
            result.terminal_status = tlc.status
            attempt_record = AttemptRecord(
                attempt_id=attempt_id,
                phase=phase,
                prompt_name=initial_prompt_name if attempt_id == 1 else "repair",
                module_file=module_snapshot_str,
                status=tlc.status,
                parse_ok=tlc.parse_ok,
                semantic_ok=tlc.semantic_ok,
                invariants_violated=tlc.invariants_violated,
                error_count=len(tlc.errors),
                feedback_excerpt="Early stop: checkpoint gated TLC success.",
            )
            result.attempts.append(attempt_record)
            break

        # Improved feedback_excerpt: prioritize real TLC errors/warnings/violations:
        lines = [line for line in tlc.output.splitlines() if line.strip()]
        error_lines = [
            l
            for l in lines
            if (
                "Error:" in l
                or "error" in l.lower()
                or "Exception" in l
                or "violation" in l.lower()
                or "violated" in l.lower()
            )
        ]
        if error_lines:
            excerpt = "\n".join(error_lines)
        else:
            excerpt = "\n".join(lines[:8])

        logging.info(f"[TLC Error] Attempt {attempt_id}: TLC error lines (up to 10):\n" + "\n".join(error_lines[:10]))

        attempt_record = AttemptRecord(
            attempt_id=attempt_id,
            phase=phase,
            prompt_name=initial_prompt_name if attempt_id == 1 else "repair",
            module_file=module_snapshot_str,
            status=tlc.status,
            parse_ok=tlc.parse_ok,
            semantic_ok=tlc.semantic_ok,
            invariants_violated=tlc.invariants_violated,
            error_count=len(tlc.errors),
            feedback_excerpt=excerpt,
        )

       # --- TLC Log handling ---
        attempt_log_dir = Path(config.output_dir) / "logs"
        tlc_log_path = save_tlc_log(attempt_log_dir, attempt_id, tlc.output)

        if "constant parameter" in tlc.output and "not assigned a value" in tlc.output:
            patched_cfg_path = patch_cfg_with_constants(latest_spec, str(generated_cfg_path), str(attempt_id))
            if str(patched_cfg_path) != str(generated_cfg_path):
                logging.info(f"[Auto-Config-Repatch] Detected unassigned constant, patched config: {patched_cfg_path}")
                generated_cfg_path = patched_cfg_path
                attempt_timing["start_tlc_patch"] = time.time()
                tlc = run_tlc(
                    tla_jar_path=config.tla_jar_path,
                    module_dir=str(module_dir),
                    module_name=snapshot_name,
                    cfg_file=generated_cfg_path,
                    metadir=metadir,
                    timeout_seconds=config.timeout_seconds,
                )
                attempt_timing["end_tlc_patch"] = time.time()
                attempt_timing["duration_tlc_patch"] = attempt_timing["end_tlc_patch"] - attempt_timing["start_tlc_patch"]
                tlc_log_path = save_tlc_log(attempt_log_dir, f"{attempt_id}_autofill", tlc.output)


        # --- Skill classification ---
        skills_db = load_skills("skills.json")
        skill = classify_tlc_error(tlc.output, skills_db)
        logging.info(f"[Skill Match] Attempt {attempt_id}: Error classified as key '{skill['key']}', strategy: '{skill['strategy']}'")


        #Loop for LLM/human-in-the-loop rule suggestion until accepted


        diagnosis_context = ""
        suggestion_count = 0


        # Guarantee: Skill (rule) application is only possible with explicit user approval. No auto-accept is permitted.
        # (Any auto-approve logic has been removed to guarantee the user always sees and approves new skills.)

        # Save original skill for checking post-loop
        original_skill = skill

        # Loop to propose/approve/apply new rule suggestion if unknown
        # Only analyze and prompt for unknown skills
        if skill["key"] == "unknown":
            diagnosis_context = ""
            suggestion_count = 0
            while skill["key"] == "unknown" and suggestion_count < MAX_SUGGESTIONS:
                matches = re.findall(r"Unknown operator: `([^`]+)`", tlc.output)
                first_undefined = matches[0] if matches else None
                first_undef_statement = f"First undefined operator to address: {first_undefined}" if first_undefined else ""
                first_undefined = first_undefined_operator(tlc.output)
                first_undef_statement = f"First undefined operator to address: {first_undefined}" if first_undefined else ""
                diagnosis = llm_analyze_tlc_error(
                    provider,
                    task,
                    latest_spec,
                    tlc.output + diagnosis_context + "\n" + first_undef_statement
                )
                repair_skill_text = diagnosis.get('repair_skill', "") or ""
                candidate_rule = diagnosis.get('new_rule')

                print(f"\n--- UNKNOWN TLC ERROR ---")
                print(tlc.output)
                print(f"\n--- CURRENT MODULE ---")
                print_source_with_line_numbers(module_snapshot_str)
                print(f"\n--- LLM ANALYSIS ---\n{diagnosis.get('diagnosis')}")
                print(f"\n--- PROPOSED REPAIR ---")
                # Show the repair plan as empty if not provided
                if repair_skill_text:
                    print(repair_skill_text)
                else:
                    print("No proposal from LLM.")

                modular_issue = is_multi_operator_issue(candidate_rule, repair_skill_text)
                decision, suggestion_count, diagnosis_context_update = prompt_human_for_skill_approval(
                    candidate_rule, repair_skill_text,
                    modular_issue=modular_issue,
                    suggestion_count=suggestion_count
                )
                if decision == 'pass':
                    if candidate_rule:
                        if 'key' not in candidate_rule:
                            candidate_rule['key'] = (
                                candidate_rule.get('pattern') or
                                candidate_rule.get('suggested_skill') or
                                f"unnamed_{abs(hash(json.dumps(candidate_rule)))}"
                            )
                        success, pending_session_rule = try_register_candidate_rule(candidate_rule, skills_db, pending_session_rule)
                        if not success:
                            break
                        skill = classify_tlc_error(tlc.output, skills_db)
                        logging.info(f"[Skill Match] Attempt {attempt_id}: Error classified as key '{skill['key']}', strategy: '{skill['strategy']}'")
                        break
                    else:
                        break
                elif decision == 'continue':
                    diagnosis_context += diagnosis_context_update
                    suggestion_count += 1
                    continue
                elif decision == 'break':
                    break

                   

        if skill["key"] != "unknown":
            logging.info(f"[Skill Patch] Attempt {attempt_id}: Applying skill '{skill['key']}' with strategy '{skill['strategy']}'")

            attempt_record.skills_applied.append(skill["key"])
            applied_skill_keys.append(skill["key"])

            # →→ NEW: Actually apply the strategy to the spec! ←←
            # (pseudo-code, you need to implement apply_known_skill)
            logging.debug("[Skill Patch] Before patch:\n" + latest_spec)
            new_spec = apply_known_skill(latest_spec, skill)
            logging.debug("[Skill Patch] After patch:\n" + new_spec)
            # Update the spec for next TLC attempt
            latest_spec = new_spec
            # Write out the spec, same as you do after LLM edits
            module_snapshot = _write_module(module_dir, task.module_name, latest_spec, attempt_id)
            module_snapshot_str = str(module_snapshot)


        # Attempt final time
        attempt_timing["end_attempt"] = time.time()
        attempt_timing["duration_total"] = attempt_timing["end_attempt"] - attempt_timing["start_attempt"]
        attempt_timing["duration_engineering_overhead"] = (
            attempt_timing["duration_total"]
            - attempt_timing["duration_llm"]
            - attempt_timing["duration_tlc"]
        )
                # Attach to attempt_record (only works if it's mutable/dataclass)
        if hasattr(attempt_record, "__dict__"):
            attempt_record.timing = attempt_timing
        # For all runs with any error, write violation/error report with trace, skill info, and TLC log
        report_needed = tlc.status != "success" or skill["key"] != "unknown"
        if report_needed:
            trace_data = parse_tlc_trace(tlc.output)
            if trace_data:
                violated_inv = trace_data["violated_invariant"]
                trace_raw = trace_data["raw_trace"]
                tla_inv_code = (
                    extract_invariant_code(latest_spec, violated_inv)
                    if violated_inv
                    else "[definition not found]"
                )
                trace_lines = trace_data["trace_lines"]
                attempt_record.counterexamples_seen = 1
                outstanding_counterexamples += 1
                total_counterexamples_seen += 1
            else:
                violated_inv, trace_raw, tla_inv_code, trace_lines = None, "", "", []
            nl_req = task.requirement_text

            violations_dir = Path(config.output_dir) / "violations"
            violations_dir.mkdir(parents=True, exist_ok=True)
            report_path = violations_dir / f"attempt_{attempt_id}_error_report.md"

            write_violation_report(
                report_path,
                attempt_id,
                violated_inv,
                tla_inv_code,
                nl_req,
                trace_raw,
                trace_lines,
                skill,
                tlc_log_path,
                llm_explanation=None,
                llm_plan=None,
            )
            logging.info(f"[AgenticLoop] Error/violation report written: {report_path}\n")

        if attempt_id == 1:
            result.generation_success = attempt_record.parse_ok and attempt_record.semantic_ok
            result.initial_verification_success = tlc.status == "success"

        if tlc.status == "success" and outstanding_counterexamples > 0:
            attempt_record.counterexamples_resolved = outstanding_counterexamples
            total_counterexamples_resolved += outstanding_counterexamples
            outstanding_counterexamples = 0

        if tlc.status == "success" and attempt_record.skills_applied:
            attempt_record.skills_successful = True
            successful_skill_uses += 1

        if human_intervention_callback is not None:
            try:
                attempt_record.human_intervention = bool(
                    human_intervention_callback(attempt_record)
                )
            except Exception:
                attempt_record.human_intervention = False

        result.attempts.append(attempt_record)
        if attempt_record.human_intervention:
            human_intervention_flag = True

        if tlc.status in {"success", "invariant_violation", "tool_missing", "timeout"}:
            result.terminal_status = tlc.status
            break

        if attempt_id == max_iterations:
            result.terminal_status = tlc.status
            break

        repair_prompt_name = "fix_parse" if tlc.status == "parse_error" else "fix_semantic"
        repair_template = load_prompt_template(prompts_dir, repair_prompt_name)
        current_prompt = render_prompt(
            repair_template,
            {
                "system_text": task.system_text,
                "requirement_text": task.requirement_text,
                "module_name": task.module_name,
                "previous_spec": latest_spec,
                "tool_feedback": tlc.output,
            },
        )

    if result.terminal_status == "unknown":
        result.terminal_status = "incomplete"

    if result.attempts:
        first_attempt = result.attempts[0]
        if not result.generation_success:
            result.generation_success = first_attempt.parse_ok and first_attempt.semantic_ok
        if not result.initial_verification_success:
            result.initial_verification_success = first_attempt.status == "success"

    result.repair_iterations = max(0, len(result.attempts) - 1)
    result.counterexamples_seen = total_counterexamples_seen
    result.counterexamples_resolved = total_counterexamples_resolved
    result.skills_applied = applied_skill_keys
    result.skills_successful = successful_skill_uses
    result.human_intervention = human_intervention_flag

    # Patch: Persist rule only if repair was actually successful!
    # Patch: Persist rule immediately upon approval (not just on TLC success)
    if pending_session_rule:
        SKILLS_DB_FILE = "skills.json"
        file_db = load_skills(SKILLS_DB_FILE)
        found = any(r.get('key') == pending_session_rule['key'] for r in file_db)
        if not found:
            file_db.append(pending_session_rule)
            with open(SKILLS_DB_FILE, "w", encoding="utf-8") as f:
                json.dump(file_db, f, indent=2)
            print(f"\n[Rule Persisted] New rule '{pending_session_rule.get('key', '')}' added to skills DB.")
        else:
            print("\n[Avoided duplicate - rule already present in DB.]\n")


    result.metadata = {
        "module_dir": str(module_dir),
        "cfg_file": task.cfg_file,
        "mode": mode,
        "max_iterations": str(max_iterations),
    }

    if learning_step_index is not None:
        result.metadata["learning_step_index"] = str(learning_step_index)


    path_dict = persist_run_result(result, str(config.output_dir))


    case_metrics = {}
    try:
        case_id = f"{task.name}_trial_{getattr(config, 'seed', 'na')}"
        initial_candidate = result.attempts[0].module_file if result.attempts else None
        initial_status = {
            "parse": result.attempts[0].parse_ok if result.attempts else None,
            "semantic": result.attempts[0].semantic_ok if result.attempts else None,
            "tlc": result.attempts[0].status == "success" if result.attempts else None
        }
        final_status = {
            "parse": result.attempts[-1].parse_ok if result.attempts else None,
            "semantic": result.attempts[-1].semantic_ok if result.attempts else None,
            "tlc": result.terminal_status == "success"
        } if result.attempts else {}


        # No filtering of "unknown" here!
        initial_fail_classes = get_failure_classes_from_attempt(result.attempts[0]) if result.attempts else []
        final_fail_classes = get_failure_classes_from_attempt(result.attempts[-1]) if (result.attempts and result.terminal_status != "success") else []

        repair_success = (not (initial_status.get("tlc") or False)) and final_status.get("tlc", False)
        repair_success = bool(repair_success)
        case_metrics = {
            "case_id": case_id,
            "mode": config.prompt_mode,
            "initial_candidate": initial_candidate,
            "initial_status": initial_status,
            "final_status": final_status,
            "repair_attempts": result.repair_iterations,
            "repair_success": repair_success,
            "initial_failure_classes": initial_fail_classes,
            "resolved_failure_classes": [c for c in initial_fail_classes if c not in final_fail_classes] if initial_fail_classes else [],
            "remaining_failure_classes": final_fail_classes,
            "artifact_dir": str(config.output_dir)
        }
    except Exception as err:
        logging.info(f"[CaseMetrics-Error] {err}")


    # Call persist_run_result as before, getting the returned dict (contains file paths including output JSON file)

    run_result_paths = persist_run_result(result, str(config.output_dir))
    # Patch the JSON on disk to add case_metrics, only if that file exists
    run_json_path = run_result_paths.get("json")
    if run_json_path and os.path.exists(run_json_path):
        with open(run_json_path, "r", encoding="utf-8") as f:
            run_json = json.load(f)
        run_json["case_metrics"] = case_metrics
        with open(run_json_path, "w", encoding="utf-8") as f:
            json.dump(run_json, f, indent=2)
    else:
        logging.info(f"[WARN] Output JSON not found for patching case_metrics: {run_json_path}")


    overall_end_time = time.time()
    result.metadata["overall_duration"] = str(overall_end_time - overall_start_time)
    result.metadata["per_attempt_timings"] = json.dumps(
        [getattr(a, "timing", {}) for a in result.attempts]
    )
    return run_result_paths




