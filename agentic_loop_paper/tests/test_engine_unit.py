import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

# Make src importable when running from project root.
PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = PROJECT_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

from agentic_loop.engine import (
    _write_module,
    classify_tlc_error,
    extract_invariant_code,
    parse_tlc_trace,
    run_experiment,
    save_tlc_log,
    tlc_trace_to_markdown_table,
)
from agentic_loop.models import LoopConfig, TaskSpec
from agentic_loop.tlc_runner import TLCResult


class DummyProvider:
    def __init__(self, generated_text):
        self.generated_text = generated_text

    def generate(self, prompt, metadata=None):
        _ = prompt
        _ = metadata
        return self.generated_text


class EngineUnitTests(unittest.TestCase):
    def test_save_tlc_log_writes_file(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            log_path = save_tlc_log(tmp_dir, 7, "hello tlc")
            self.assertTrue(Path(log_path).exists())
            self.assertIn("attempt_7_tlc_output.txt", log_path)
            self.assertEqual(Path(log_path).read_text(encoding="utf-8"), "hello tlc")

    def test_classify_tlc_error_matches_pattern_and_groups(self):
        skills = [
            {
                "key": "semantic",
                "strategy": "Fix unknown operator",
                "pattern": r"Unknown operator (?P<op>\w+)",
            }
        ]
        result = classify_tlc_error("Semantic error: Unknown operator Foo", skills)
        self.assertEqual(result["key"], "semantic")
        self.assertEqual(result["groups"].get("op"), "Foo")

    def test_classify_tlc_error_returns_unknown_when_no_match(self):
        skills = [{"key": "x", "strategy": "y", "pattern": r"does-not-match"}]
        result = classify_tlc_error("all good", skills)
        self.assertEqual(result["key"], "unknown")

    def test_parse_tlc_trace_extracts_trace_and_invariant(self):
        tlc_output = "\n".join(
            [
                "Invariant Safety is violated",
                "Trace:",
                "State 1:",
                "/\\ x = 0",
                "State 2:",
                "/\\ x = 1",
                "Finished in 0.1s",
            ]
        )
        parsed = parse_tlc_trace(tlc_output)
        self.assertIsNotNone(parsed)
        self.assertEqual(parsed["violated_invariant"], "Safety")
        self.assertEqual(parsed["trace_lines"], ["State 1:", "/\\ x = 0", "State 2:", "/\\ x = 1"])

    def test_parse_tlc_trace_returns_none_when_missing_trace(self):
        self.assertIsNone(parse_tlc_trace("Invariant Safety is violated\nNo trace present"))

    def test_tlc_trace_to_markdown_table_formats_states(self):
        table = tlc_trace_to_markdown_table([
            "State 1:",
            "/\\ x = 0",
            "State 2:",
            "/\\ x = 1",
        ])
        self.assertIn("| Step | Variable Assignments |", table)
        self.assertIn("| State 1 | x = 0 |", table)
        self.assertIn("| State 2 | x = 1 |", table)

    def test_extract_invariant_code_returns_definition(self):
        spec = "\n".join(
            [
                "---- MODULE M ----",
                "Safety == x >= 0",
                "====",
            ]
        )
        extracted = extract_invariant_code(spec, "Safety")
        self.assertTrue(extracted.startswith("Safety =="))

    def test_write_module_creates_snapshot_and_rewrites_header(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            spec = "\n".join([
                "---- MODULE OldName ----",
                "VARIABLE x",
                "====",
            ])
            snapshot = _write_module(tmp_dir, "MySpec", spec, 3)
            self.assertTrue(Path(snapshot).exists())

            snapshot_text = Path(snapshot).read_text(encoding="utf-8")
            self.assertIn("---- MODULE MySpec_attempt_3 ----", snapshot_text)

            latest_text = (Path(tmp_dir) / "MySpec.tla").read_text(encoding="utf-8")
            self.assertIn("---- MODULE MySpec_attempt_3 ----", latest_text)

    def test_run_experiment_calls_module_level_write_violation_report(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            module_dir = Path(tmp_dir)
            cfg_path = module_dir / "Test.cfg"
            cfg_path.write_text("INVARIANT Safety\n", encoding="utf-8")

            task = TaskSpec(
                name="test_task",
                module_name="Test",
                cfg_file="Test.cfg",
                system_text="sys",
                requirement_text="req",
            )
            config = LoopConfig(
                tla_jar_path="/tmp/does-not-matter.jar",
                module_dir=str(module_dir),
                output_dir=str(module_dir / "out"),
                prompt_mode="one_shot_nl_to_tla",
                max_iterations=1,
                timeout_seconds=1,
            )

            provider = DummyProvider(
                "\n".join(
                    [
                        "---- MODULE Test ----",
                        "VARIABLE x",
                        "Init == x = 0",
                        "Next == x' = x",
                        "Safety == x >= 0",
                        "====",
                    ]
                )
            )

            tlc_result = TLCResult(
                status="invariant_violation",
                parse_ok=True,
                semantic_ok=True,
                invariants_violated=True,
                output="\n".join(
                    [
                        "Invariant Safety is violated",
                        "Trace:",
                        "State 1:",
                        "/\\ x = 0",
                        "Finished in 0.1s",
                    ]
                ),
                errors=["invariant_violation"],
            )

            with patch("agentic_loop.engine.load_prompt_template", return_value="template"), patch(
                "agentic_loop.engine.render_prompt", return_value="prompt"
            ), patch("agentic_loop.engine.run_tlc", return_value=tlc_result), patch(
                "agentic_loop.engine.load_skills",
                return_value=[{"key": "inv", "strategy": "repair", "pattern": "violated"}],
            ), patch("agentic_loop.engine.save_tlc_log", return_value="results/logs/mock.txt"), patch(
                "agentic_loop.engine.persist_run_result",
                return_value={"json": "out.json", "csv": "out.csv"},
            ), patch("agentic_loop.engine.write_violation_report") as report_mock:
                artifacts = run_experiment(
                    task=task,
                    config=config,
                    prompts_dir=str(module_dir / "prompts"),
                    provider=provider,
                    mode="baseline",
                )

            self.assertEqual(artifacts, {"json": "out.json", "csv": "out.csv"})
            report_mock.assert_called_once()


if __name__ == "__main__":
    unittest.main()
