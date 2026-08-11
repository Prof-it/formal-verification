import pytest
import tempfile
from pathlib import Path
import sys

# Import the module under test
import trace2mermaid_llm

def test_build_mermaid_prompt_contains_fake_date_instructions():
    """Test that the build_mermaid_prompt includes the fake date spacing instructions."""
    sample_trace = "State 1: ..."
    prompt = trace2mermaid_llm.build_mermaid_prompt(sample_trace)
    assert "Ignore the actual time intervals between milestones" in prompt
    assert "assign each milestone a 'fake' date" in prompt
    assert "equally spaced" in prompt
    assert sample_trace in prompt

def test_extract_tlc_trace_extracts_trace():
    """Test extract_tlc_trace extracts lines after the error marker and stops at summary."""
    content = """
Header
Error: The behavior up to this point is:
State 1: foo
State 2: bar
states generated: 123
Summary line
"""
    with tempfile.NamedTemporaryFile("w+", delete=False) as tf:
        tf.write(content)
        tf.flush()
        tf_path = Path(tf.name)
    try:
        result = trace2mermaid_llm.extract_tlc_trace(tf_path)
        assert "State 1: foo" in result
        assert "State 2: bar" in result
        assert "states generated" not in result
    finally:
        tf_path.unlink()

def test_load_env_and_get_key_missing(monkeypatch, tmp_path):
    """Test load_env_and_get_key raises if .env missing or key missing."""
    # File does not exist
    missing_path = tmp_path / "noenv.env"
    with pytest.raises(RuntimeError):
        trace2mermaid_llm.load_env_and_get_key(missing_path)
    # File exists but no key
    env_path = tmp_path / ".env"
    env_path.write_text("")
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    with pytest.raises(RuntimeError):
        trace2mermaid_llm.load_env_and_get_key(env_path)

def test_main_help_runs(monkeypatch):
    """Test that the Typer app exposes help and does not crash."""
    from typer.testing import CliRunner
    runner = CliRunner()
    result = runner.invoke(trace2mermaid_llm.app, ["--help"])
    assert result.exit_code == 0
    assert "Usage" in result.output
