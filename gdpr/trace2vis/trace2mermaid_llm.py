import os
import re
from pathlib import Path
import typer

import subprocess
from openai import OpenAI
from dotenv import load_dotenv

app = typer.Typer()

def extract_tlc_trace(out_path: Path) -> str:
    """
    Extracts the full TLC counterexample trace (all State N blocks and relevant variables).
    Ignores headers and summary info.
    """
    lines = out_path.read_text(encoding="utf-8").splitlines()
    trace_lines = []
    in_trace = False
    for i, line in enumerate(lines):
        if line.strip().startswith("Error: The behavior up to this point is:"):
            in_trace = True
            continue
        # heuristically stop at summary/statistics or next Error
        if in_trace and (
            line.strip().startswith("states generated")
            or "Finished" in line
            or line.strip().startswith("Error:")
        ):
            break
        if in_trace:
            trace_lines.append(line)
    return "\n".join(trace_lines).strip()

def load_env_and_get_key(dotenv_path: Path):
    """
    Loads environment variables from a dotenv file and returns the OpenAI API Key.
    """
    if not dotenv_path.exists():
        raise RuntimeError(f".env file does not exist at {dotenv_path}")
    load_dotenv(dotenv_path=dotenv_path)
    key = os.environ.get("OPENAI_API_KEY")
    if not key:
        raise RuntimeError(f"OPENAI_API_KEY missing in {dotenv_path}")
    return key

def build_mermaid_prompt(tlc_trace: str) -> str:
    return (
        "You are an expert TLA+ trace and GDPR scenario visualizer.\n"
        "Given the following TLC counterexample trace, generate a valid Mermaid Gantt chart showing the logical event order and event periods.\n"
        "\n"
        "Requirements:\n"
        "- Your Mermaid diagram MUST always include, in this exact order, these four sections:\n"
        "  section Milestones\n"
        "  section Legal Bases\n"
        "  section Processing\n"
        "  section Breach\n"
        "- Every section must be present, even if some bars are placeholders (e.g., 'No Breach').\n"
        "- All milestones must go inside section Milestones, using label [Event Name YYYY-MM-DD HH_mm] :milestone, id, YYYY-MM-DD HH:mm, 0d.\n"
        "- The milestone label must always include the full timestamp in label (with _ between hour and minute).\n"
        "- Each bar or milestone line must use ONLY these allowed Mermaid types for the type field:\n"
        "    :active, :done, :crit, :milestone\n"
        "- Map as follows:\n"
        "    Legal Bases and Consent bars: :active\n"
        "    Processing bars: :done\n"
        "    Breach bars (including 'No Breach'): :crit (for red/alerting)\n"
        "    Milestones: :milestone\n"
        "- Never use custom types like :contract, :consent, :processing, or :breach—these are invalid and will break rendering.\n"
        "- All bars (contract, consent, processing, breach) must be in format:\n"
        "    [Label text] :[type], [id], [start], [end]\n"
        "  Where times are 'YYYY-MM-DD HH:mm'.\n"
        "- Set dateFormat and axisFormat at the top.\n"
        "- Output valid Mermaid Gantt ONLY (no Markdown, no explanation, no comments, and absolutely no code fences or triple backticks).\n"
        "\n"
        "IMPORTANT: Ignore the actual time intervals between milestones. Instead, group all milestones by their real timestamp. Assign each unique timestamp an artificial, equally spaced date (e.g., increment by 1 day or 1 hour for each unique timestamp, regardless of the real time difference). If multiple milestones share the same timestamp, they must be assigned the same artificial date and appear aligned at the same horizontal position on the Gantt chart. This ensures that all unique milestone times are distributed evenly across the timeline, and milestones with identical timestamps are visually aligned. Keep the real timestamp in the milestone label for reference, but use the artificial dates for the chart positions. Ensure each milestone group appears in a separate 'zone' of the timeline, making section differences visually obvious.\n"
        "\n"
        "Here is the TLC trace:\n"
        "---\n"
        f"{tlc_trace}\n"
        "---"
    )





# Typer command definition
@app.command()
def main(
    infile: Path = typer.Argument(..., exists=True, help="TLC .out file"),
    o: Path = typer.Option(None, "-o", help="Output file (default stdout)"),
    dotenv: Path = typer.Option(".env", "--dotenv", help="Path to .env file with OPENAI_API_KEY"),
    export_png: Path = typer.Option(None, "--export-png", "-p", help="Optional: Path to save PNG export via mermaid-cli"),
):
    """
    Generate a Mermaid flowchart of a TLC counterexample trace via LLM (OpenAI), optionally exporting to PNG.
    """
    api_key = load_env_and_get_key(dotenv)
    client = OpenAI(api_key=api_key)
    trace = extract_tlc_trace(infile)
    if not trace:
        typer.echo("No TLC trace found in this file.", err=True)
        raise typer.Exit(1)
    prompt = build_mermaid_prompt(trace)
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[{"role": "user", "content": prompt}],
        temperature=0,
        max_tokens=1500,
    )
    code = response.choices[0].message.content
    # Remove markdown code fence if present for writing/exporting
    raw_code = code
    code_strip = code.strip()
    if code_strip.startswith('```mermaid') and code_strip.endswith('```'):
        raw_lines = code_strip.splitlines()
        raw_code = '\n'.join(raw_lines[1:-1])
    mmd_file = None
    # Decide output Mermaid file
    if o:
        mmd_path = o
    else:
        mmd_path = infile.with_suffix('.mmd')

    # Always write Mermaid file
    mmd_path.write_text(raw_code)
    typer.echo(f"Mermaid diagram saved to {mmd_path}")

    # Print code to console if no `-o` was given
    if not o:
        print(code)

    # Set default PNG output if option not provided
    if export_png is None:
        export_png = infile.with_suffix('.png')
        typer.echo(f"No PNG file name given, will export PNG to: {export_png}")

    # Export PNG if requested (always from mmd_path)
    if export_png:
        result = subprocess.run([
            "mmdc",
            "-i", str(mmd_path),
            "-o", str(export_png)
        ], capture_output=True, text=True)
        if result.returncode != 0:
            typer.echo(f"Error running mmdc: {result.stderr}", err=True)
        else:
            typer.echo(f"PNG exported to {export_png}")


if __name__ == "__main__":
    app()
