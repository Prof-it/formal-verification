
import os
import re
from pathlib import Path
import typer
import subprocess
from openai import OpenAI
from dotenv import load_dotenv
import sys
from datetime import datetime, timedelta
from remove_time_from_bar_labels import remove_time_from_bar_labels

DEFAULT_INFINITY_TIME = "2500-12-31 23:59"  # Used as a marker for 'no deadline' or open-ended bars


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
        "  section DataBreach\n"
        "- Every section must be present, even if some bars are placeholders (e.g., [No data] as label when no data exists).\n"
        "- All milestones must go inside section Milestones, using label [Event Type, Subject, Data, YYYY-MM-DD HH_mm] :milestone, id, YYYY-MM-DD HH:mm, 0d.\n"
        "- The milestone label must always include the full timestamp in label (with _ between hour and minute).\n"
        "- Each bar or milestone line must use ONLY these allowed Mermaid types for the type field:\n"
        "    :active, :done, :crit, :milestone\n"
        "- Map as follows:\n"
        "    Legal Bases and Consent bars: :active\n"
        "    Processing bars: :done\n"
        "    DataBreach bars (including [No data] as label placeholder when no data exists): :crit (for red/alerting)\n"
        "    Milestones: :milestone\n"
        "- Never use custom types like :contract, :consent, :processing, or :breach... these are invalid and will break rendering.\n"
        "- All bars (contract, consent, processing) must be in format:\n"
        "    [Type, Subject, Data, YYYY-MM-DD HH_mm - YYYY-MM-DD HH_mm] :[type], [id], [start], [end]\n"
        "  Where times are 'YYYY-MM-DD HH:mm'.\n"
        "- For Consent legal basis bars, the start time MUST be the time of the corresponding GiveConsent event, and the end time MUST be the time of the corresponding WithdrawConsent event (if present). Do NOT use any other time points for Consent bars.\n"
        "- For DataBreach bars, the start time MUST be the time of the corresponding DataBreachDetected event, and the end time MUST be the time of the corresponding DataBreachReported event (if present). Do NOT use any other time points for DataBreach bars.\n"
        "- Set dateFormat and axisFormat at the top.\n"
        "- Output valid Mermaid Gantt ONLY (no Markdown, no explanation, no comments, and absolutely no code fences or triple backticks).\n"
        "\n"
        "Here is the TLC trace:\n"
        "---\n"
        f"{tlc_trace}\n"
        "---"
    )

def extract_final_current_time(tlc_trace: str) -> str:
    """
    Extract the final state's currentTime from the TLC trace as a string 'YYYY-MM-DD HH:MM'.
    Returns None if not found.
    """
    # Find all lines like '/\ currentTime = [year |-> 2025, month |-> 7, day |-> 12, hour |-> 8, minute |-> 25]'

    # Fix regex to match lines like '/\ currentTime = [ ... ]' robustly
    current_time_lines = re.findall(r'/\\\s*currentTime\s*=\s*\[(.*?)\]', tlc_trace)
    if not current_time_lines:
        return None
    last_fields = current_time_lines[-1]
    # Parse fields into dict
    kv = dict(re.findall(r'(year|month|day|hour|minute)\s*\|->\s*(\d+)', last_fields))
    try:
        dt = datetime(
            int(kv.get('year', 0)),
            int(kv.get('month', 1)),
            int(kv.get('day', 1)),
            int(kv.get('hour', 0)),
            int(kv.get('minute', 0))
        )
        return dt.strftime('%Y-%m-%d %H:%M')
    except Exception as e:
        print(f"[extract_final_current_time] Failed to parse currentTime: {e}", file=sys.stderr)
        return None
    
def insert_deadline_milestone(mmd_code: str, deadline_time: str) -> str:
    """
    Insert a synthetic 'Deadline' milestone (as :milestone) at deadline_time into the Milestones section.
    deadline_time: string 'YYYY-MM-DD HH:MM'
    Returns the modified Mermaid code.
    """
    # Format for label: [Current Time, -, -, YYYY-MM-DD HH_MM] :milestone, deadline, YYYY-MM-DD HH:MM, 0d
    label_time = deadline_time.replace(':', '_')
    milestone_line = f"        [Current Time, {label_time}] :milestone, ct, {deadline_time}, 0d"
    lines = mmd_code.splitlines()
    # Find the Milestones section
    out_lines = []
    inserted = False
    for idx, line in enumerate(lines):
        out_lines.append(line)
        if not inserted and line.strip().startswith('section Milestones'):
            # Insert after section header, but before any other milestones
            # Find next non-section line or end
            insert_idx = idx + 1
            # Insert after any existing milestones, but before next section
            while insert_idx < len(lines) and (lines[insert_idx].strip() == '' or not lines[insert_idx].strip().startswith('section')):
                insert_idx += 1
            # Actually insert after section header
            out_lines.append(milestone_line)
            inserted = True
    # If no Milestones section found, append at end
    if not inserted:
        out_lines.append('    section Milestones')
        out_lines.append(milestone_line)
    return '\n'.join(out_lines)


# --- Insert minimal axisFormat as final post-processing step ---
def set_minimal_axis_format(mmd_code: str, axis_format: str = ".") -> str:
    """
    Ensure a minimal axisFormat is present at the top of the Mermaid Gantt code.
    If axisFormat is already present, replace it with the minimal one.
    Otherwise, insert it after dateFormat (if present), or after gantt.
    """
    lines = mmd_code.splitlines()
    found_axis = False
    for i, line in enumerate(lines):
        if line.strip().startswith("axisFormat"):
            lines[i] = f"axisFormat {axis_format}"
            found_axis = True
            break
    if not found_axis:
        # Try to insert after dateFormat if present
        for i, line in enumerate(lines):
            if line.strip().startswith("dateFormat"):
                lines.insert(i+1, f"axisFormat {axis_format}")
                found_axis = True
                break
    if not found_axis:
        # Try to insert after gantt if present
        for i, line in enumerate(lines):
            if line.strip().startswith("gantt"):
                lines.insert(i+1, f"axisFormat {axis_format}")
                found_axis = True
                break
    if not found_axis:
        # Otherwise, insert at the top
        lines.insert(0, f"axisFormat {axis_format}")
    return "\n".join(lines)

def equally_space_milestones(mmd_code: str, fit_days: int = 7) -> str:
    """
    Postprocess Mermaid Gantt code so that all milestones are assigned synthetic, equally spaced dates.
    The spacing is auto-detected to fit all unique milestone timestamps within `fit_days` days.
    Keeps the real timestamp in the label, but rewrites the date fields for milestones.
    """

    lines = mmd_code.splitlines()
    # --- NEW LOGIC: Collect all real time points from label times for both milestones and bars ---
    all_times = set()
    milestone_times = set()
    bar_times = set()
    deadline_time = None
    # Look for a synthetic deadline milestone (label starts with [Deadline, ...])
    for idx, line in enumerate(lines):
        # Milestone: extract last field from label
        if ":milestone" in line or ":crit" in line:
            m = re.match(r"^\s*\[(.*?)\]\s*:(milestone|crit),", line)
            if m:
                label_fields = m.group(1).split(',')
                if label_fields:
                    label_time = label_fields[-1].strip()
                    label_time_std = label_time.replace('_', ':')
                    # If this is the Deadline milestone, remember for axis
                    if m.group(1).strip().startswith('Deadline'):
                        deadline_time = label_time_std
                    try:
                        dt = datetime.strptime(label_time_std, "%Y-%m-%d %H:%M")
                        all_times.add(label_time_std)
                        milestone_times.add(label_time_std)
                    except Exception:
                        pass
        # Bar: extract last field from label, split on ' - '
        elif ':' in line and '[' in line and ']' in line:
            m = re.match(r"^\s*\[(.*?)\]\s*:[^,]+,", line)
            if m:
                label_fields = m.group(1).split(',')
                if label_fields:
                    label_time_range = label_fields[-1].strip()
                    if ' - ' in label_time_range:
                        start_label_time, end_label_time = label_time_range.split(' - ')
                        for label_time in [start_label_time, end_label_time]:
                            label_time_std = label_time.replace('_', ':')
                            try:
                                dt = datetime.strptime(label_time_std, "%Y-%m-%d %H:%M")
                                all_times.add(label_time_std)
                                bar_times.add(label_time_std)
                            except Exception:
                                pass

    if not all_times:
        return mmd_code

    # Find min and max real time
    dt_list = [datetime.strptime(ts, "%Y-%m-%d %H:%M") for ts in all_times]
    min_dt = min(dt_list)
    max_dt = max(dt_list)

    # If DEFAULT_INFINITY_TIME is present anywhere, add (max_dt + 1 day) as the final axis point
    DEFAULT_INFINITY_TIME = "2500-12-31 23:59"
    infinity_present = any(DEFAULT_INFINITY_TIME in line for line in lines)
    if infinity_present:
        axis_dt_list = sorted(dt_list + [max_dt + timedelta(days=1)])
    else:
        axis_dt_list = sorted(dt_list)

    # Build the ordered list of axis points (for mapping)
    axis_points = [dt.strftime("%Y-%m-%d %H:%M") for dt in axis_dt_list]

    # Map each axis point to a synthetic, equally spaced date
    n = len(axis_points)
    base_dt = min_dt
    if n == 1:
        step = timedelta(days=1)
    else:
        total_seconds = (axis_dt_list[-1] - axis_dt_list[0]).total_seconds()
        step = timedelta(seconds=total_seconds/(n-1))
    axis_to_synth = {}
    for i, ts in enumerate(axis_points):
        synth_dt = axis_dt_list[0] + i * step
        synth_dt = synth_dt.replace(second=0, microsecond=0)
        axis_to_synth[ts] = synth_dt.strftime("%Y-%m-%d %H:%M")

    # Rewrite milestone lines using the label time for mapping
    new_lines = list(lines)
    for idx, line in enumerate(new_lines):
        # Rewrite both :milestone and :crit (deadline) lines
        if ":milestone" in line or ":crit" in line:
            # Extract label time from the label
            label_match = re.match(r"^\s*\[(.*?)\]\s*:(milestone|crit),", line)
            label_time_std = None
            if label_match:
                label_fields = label_match.group(1).split(',')
                if label_fields:
                    label_time = label_fields[-1].strip()
                    label_time_std = label_time.replace('_', ':')
            # Debug output
            print(f"DEBUG: Milestone line: {line}")
            print(f"DEBUG: Extracted label_time_std: {label_time_std}")
            print(f"DEBUG: axis_to_synth keys: {list(axis_to_synth.keys())}")
            # Replace the milestone time field with the synthetic time
            m = re.search(r"(\[.*?\]\s*:(milestone|crit),\s*[^,]+,\s*)([0-9\-]+ [0-9:]+)(, 0d)", line)
            if m:
                print(f"DEBUG: Regex groups: {m.groups()}")
            if m and label_time_std and label_time_std in axis_to_synth:
                print(f"DEBUG: Replacing milestone time {m.group(3)} with {axis_to_synth[label_time_std]}")
                new_lines[idx] = line[:m.start(3)] + axis_to_synth[label_time_std] + line[m.end(3):]
            else:
                print(f"DEBUG: No replacement for milestone time {label_time_std}")
    # Rewrite bar lines (using the original regex logic)
    bar_re = re.compile(r"^\s*\[.*?\]\s*:[^,]+,\s*[^,]+,\s*([0-9\-]+ [0-9:]+),\s*([0-9\-]+ [0-9:]+)")
    for idx, line in enumerate(new_lines):
        if ":milestone" in line:
            continue
        m = bar_re.match(line)
        if m:
            # Find the label times for this bar
            label_match = re.match(r"^\s*\[(.*?)\]\s*:[^,]+,", line)
            start_label_time_std = end_label_time_std = None
            if label_match:
                label_fields = label_match.group(1).split(',')
                if label_fields:
                    label_time_range = label_fields[-1].strip()
                    if ' - ' in label_time_range:
                        start_label_time, end_label_time = label_time_range.split(' - ')
                        start_label_time_std = start_label_time.replace('_', ':')
                        end_label_time_std = end_label_time.replace('_', ':')
            orig_start, orig_end = m.group(1), m.group(2)
            new_start = axis_to_synth.get(start_label_time_std, orig_start)
            new_end = axis_to_synth.get(end_label_time_std, orig_end)
            def repl_fn(mb):
                return mb.group(0).replace(orig_start, new_start).replace(orig_end, new_end)
            new_lines[idx] = bar_re.sub(repl_fn, line)
    return "\n".join(new_lines)



def replace_colon_in_label_times(mmd_code: str) -> str:
    """
    Replace all ':' with '_' in time substrings of the form HH:MM inside labels (inside [...]) only.
    Does not affect the actual Gantt chart date fields.
    """
    def repl_label(match):
        label = match.group(1)
        # Replace all HH:MM inside the label with HH_MM
        label = re.sub(r'(\d{2}):(\d{2})', r'\1_\2', label)
        return f'[{label}]'
    # Replace content inside [...] for each line
    return re.sub(r'\[(.*?)\]', repl_label, mmd_code)


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

    # Extract final state's currentTime as deadline
    deadline_time = extract_final_current_time(trace)
    print(f"[DEBUG] Extracted deadline_time: {deadline_time}", file=sys.stderr)

    prompt = build_mermaid_prompt(trace)
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[{"role": "user", "content": prompt}],
        temperature=0,
        max_tokens=1500,
    )
    code = response.choices[0].message.content
    # Crop any non-Mermaid content from LLM output
    if code is None:
        raw_code = ''
    else:
        code_lines = code.strip().splitlines()
        # Remove first line if it's a code fence
        if code_lines and code_lines[0].strip().startswith('```'):
            code_lines = code_lines[1:]
        # Remove last line(s) if they are code fences or non-mermaid explanations
        # Find the last line that looks like valid Mermaid code (heuristic: section, bar, or gantt block)
        mermaid_keywords = (
            'gantt', 'dateFormat', 'axisFormat', 'title', 'section',
        )
        last_mermaid_idx = -1
        for idx, line in enumerate(code_lines):
            lstr = line.strip()
            if (
                lstr.startswith(mermaid_keywords)
                or (lstr.startswith('No Breach') or lstr.startswith('Consent') or lstr.startswith('Processing'))
                or (lstr.startswith('Event') and ':milestone' in lstr)
                or (line.startswith('    ') or line.startswith('\t'))
            ):
                last_mermaid_idx = idx
        # Only keep up to the last valid Mermaid line
        if last_mermaid_idx != -1:
            cropped_lines = code_lines[:last_mermaid_idx+1]
        else:
            cropped_lines = code_lines
        raw_code = '\n'.join(cropped_lines).rstrip()
    mmd_file = None
    # Decide output Mermaid file
    if o:
        mmd_path = o
    else:
        mmd_path = infile.with_suffix('.mmd')

    # First, replace : with _ in label times inside [...] to normalize label format
    normalized_code = replace_colon_in_label_times(raw_code)

    # Insert the deadline milestone BEFORE mapping so it is included in the synthetic timeline
    if deadline_time:
        print(f"[DEBUG] Inserting deadline milestone for time: {deadline_time}", file=sys.stderr)
        before_insert = normalized_code
        normalized_code = insert_deadline_milestone(normalized_code, deadline_time)
        print("[DEBUG] Mermaid code after inserting deadline milestone (pre-mapping):\n" + normalized_code, file=sys.stderr)
    else:
        print("[DEBUG] No deadline_time found, skipping deadline milestone insertion.", file=sys.stderr)

    # Now postprocess for equally spaced milestones (auto-fit within 7 days)
    processed_code = equally_space_milestones(normalized_code, fit_days=7)


    # Remove time info from all bar labels as the very last postprocessing step
    final_code = remove_time_from_bar_labels(processed_code)


    # Apply minimal axisFormat as unobtrusive as possible
    final_code = set_minimal_axis_format(final_code, ".")

    # Always write Mermaid file
    mmd_path.write_text(final_code)
    typer.echo(f"Mermaid diagram saved to {mmd_path} (milestones equally spaced, deadline visualized, bar label time removed, minimal axisFormat)")

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
