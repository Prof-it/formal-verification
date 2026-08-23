import re

def parse_tlc_trace(tlc_output: str):
    lines = tlc_output.splitlines()
    violated_invariant = None
    for line in lines:
        m = re.match(r"^Invariant (\\w+) is violated", line)
        if m:
            violated_invariant = m.group(1)
            break
    trace_start = None
    for i, line in enumerate(lines):
        if re.match(r"^Trace:", line):
            trace_start = i
            break
    if trace_start is None:
        return None
    trace_lines = []
    for line in lines[trace_start+1:]:
        if line.strip() == "" or line.startswith("Finished"):
            break
        trace_lines.append(line)
    return {
        "violated_invariant": violated_invariant,
        "trace_lines": trace_lines,
        "raw_trace": "\\n".join(trace_lines)
    }

def tlc_trace_to_markdown_table(trace_lines):
    out = []
    current_state = ""
    current_vals = []
    for line in trace_lines:
        if line.lstrip().startswith("State "):
            if current_state:
                out.append([current_state, "<br>".join(current_vals)])
            current_state = line.strip(":").strip()
            current_vals = []
        elif line.lstrip().startswith("/\\"):
            current_vals.append(line.strip("/\\ ").replace('"', ''))
    if current_state:
        out.append([current_state, "<br>".join(current_vals)])
    header = "| Step | Variable Assignments |\n|------|----------------------|\n"
    body = "\n".join([f"| {step} | {vals} |" for step, vals in out])
    return header + body
