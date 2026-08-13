import re
import sys
from pathlib import Path
import typer

app = typer.Typer()

def parse_time_point(fields):
    """ Given field string like 'year |-> 2025, month |-> 7, day |-> 12, hour |-> 8, minute |-> 25', produce (2025, 7, 12, 8, 25) as tuple"""
    kv = dict(re.findall(r"(year|month|day|hour|minute)\s*\|->\s*(\d+)", fields))
    return tuple(int(kv.get(f, 0)) for f in ["year","month","day","hour","minute"])
def parse_tlc_set_block(lines, set_var_names):
    """
    Robustly extracts only the two named TLC sets (events and legalBases) from a list of TLC state lines.
    Returns dict {var_name: [raw_record_str, ...], ...}
    Ignores everything else. Each record can be multiline, supports arbitrary whitespace/newline.
    """
    text = '\n'.join(lines)
    blocks = {name: [] for name in set_var_names}
    for name in set_var_names:
        # Regex for: /\ name = { ... }
        pat = re.compile(r'/\\\s*' + re.escape(name) + r'\s*=\s*\{(.*?)\}', re.DOTALL)
        m = pat.search(text)
        if not m:
            continue
        records_content = m.group(1)
        # Extract all bracket-balanced records (robust to multiline, multiple per block)
        recs = []
        buf = ''
        depth = 0
        for ch in records_content:
            buf += ch
            if ch == '[':
                if depth == 0:
                    buf = ch  # New record starts here
                depth += 1
            elif ch == ']':
                depth -= 1
                if depth == 0:
                    recs.append(buf)
                    buf = ''  # Reset for next record
        # Only keep records that start with a bracket (real event/period records)
        blocks[name].extend(rec for rec in recs if rec.strip().startswith('['))
    return blocks
    return blocks
                            record_lines.append(nl)
                            bracket_level += nl.count('[')
                            bracket_level -= nl.count(']')
                        blocks[name].append('\n'.join(record_lines))
    return blocks



def parse_event_line(evstr):
    """
    Parse a TLA+ record string for events, legal basis, or processing.
    Extracts type, subject, data, time, end_time, start, end (where present),
    handling inner records across newlines and brackets.
    """
    print("RECORD RAW:", evstr, file=sys.stderr)
    evstr_flat = ' '.join(evstr.split())
    print("RECORD FLAT:", evstr_flat, file=sys.stderr)
    ty = re.search(r'type\s*\|->\s*"([^"]+)"', evstr_flat)
    subject = re.search(r'subject\s*\|->\s*"([^"]+)"', evstr_flat)
    data = re.search(r'data\s*\|->\s*"([^"]+)"', evstr_flat)
    time = re.search(r'time\s*\|->\s*\[([^\[\]]+)\]', evstr_flat)
    end_time = re.search(r'end_time\s*\|->\s*\[([^\[\]]+)\]', evstr_flat)
    start = re.search(r'start\s*\|->\s*\[([^\[\]]+)\]', evstr_flat)
    end = re.search(r'end\s*\|->\s*\[([^\[\]]+)\]', evstr_flat)
    out = {
        "type": ty.group(1) if ty else None,
        "subject": subject.group(1) if subject else None,
        "data": data.group(1) if data else None,
        "time": parse_time_point(time.group(1)) if time else None,
        "end_time": parse_time_point(end_time.group(1)) if end_time else None,
        "start": parse_time_point(start.group(1)) if start else None,
        "end": parse_time_point(end.group(1)) if end else None
    }
    print("DEBUG parse_event_line:", out, file=sys.stderr)
    return out




def collect_set_block(startidx, lines):
    """Collect lines making up a balanced {...} set. Returns lines in set and new index after set."""
    collected = []
    idx = startidx
    brace_count = 0
    in_set = False
    while idx < len(lines):
        l = lines[idx]
        if '{' in l and not in_set:
            in_set = True
            brace_count += 1
        elif '{' in l:
            brace_count += l.count('{')
        if in_set:
            collected.append(l)
            brace_count += l.count('{') if not ('{' in l and not in_set) else 0
            brace_count -= l.count('}')
            if brace_count == 0:
                idx += 1
                break
        idx += 1
    return collected, idx


def parse_multiline_set_block(lines, set_var_name):
    """Parse multi-line TLC sets supporting cascaded/nested records."""
    inside_set = False
    records = []
    in_record = False
    current_record = []
    bracket_level = 0
    for l in lines:
        l_stripped = l.strip()
        # Start of set
        if not inside_set and l_stripped.startswith(f'/\\ {set_var_name} = {{'):
            inside_set = True
            continue
        if inside_set:
            if l_stripped == '}':
                inside_set = False
                continue
            # Record parsing
            if '[' in l_stripped and not in_record:
                # The start of a new record
                in_record = True
                current_record = [l_stripped]
                bracket_level = l_stripped.count('[') - l_stripped.count(']')
                if bracket_level == 0:
                    in_record = False
                    records.append('\n'.join(current_record))
                    current_record = []
            elif in_record:
                current_record.append(l_stripped)
                bracket_level += l_stripped.count('[')
                bracket_level -= l_stripped.count(']')
                if bracket_level == 0:
                    in_record = False
                    records.append('\n'.join(current_record))
                    current_record = []
    return records





def parse_state_vars(state_lines):
    blocks = parse_tlc_set_block(list(state_lines), ['events', 'legalBases'])
    # Defensive logging and filtering
    print("PARSED BLOCKS:", {k: len(v) for k,v in blocks.items()}, file=sys.stderr)
    events = [parse_event_line(rec) for rec in blocks['events'] if rec.strip().startswith('[')]
    legal_bases = [parse_event_line(rec) for rec in blocks['legalBases'] if rec.strip().startswith('[')]
    # ...construct lanes/periods/events from these dicts as desired...
    print("DEBUG events:", events, file=sys.stderr)
    print("DEBUG legal_basis:", legal_bases, file=sys.stderr)
    state = {"events": events, "legalBases": legal_bases}
    # Collect now as before
    for l in state_lines:
        if l.strip().startswith('/\\ now = ['):
            tp = re.search(r'\\[(.*?)\\]', l)
            if tp:
                state['now'] = parse_time_point(tp.group(1))
    return state


def parse_tlc_out_states(path):
    """
    Parse a TLC .out file. Get all 'State N:' chunks, parse each with parse_state_vars.
    """
    with open(path) as f:
        lines = list(f)
    states = []
    buf = []
    for l in lines:
        if l.strip().startswith('State'):
            if buf:
                state = parse_state_vars(buf)
                if state: states.append(state)
            buf = []
        elif l.lstrip().startswith('/\\'):
            buf.append(l)
    if buf:
        state = parse_state_vars(buf)
        if state: states.append(state)
    return states


def merge_intervals(intervals):
    """ Merge overlapping or adjacent intervals (tuple(start,end)), used for valid bar consolidation. """
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = [intervals[0]]
    for curr in intervals[1:]:
        prev = merged[-1]
        if curr[0] <= prev[1]:
            merged[-1] = (prev[0], max(prev[1], curr[1]))
        else:
            merged.append(curr)
    return merged

@app.command()
def main(
    outfile: Path = typer.Argument(..., exists=True, help="Path to TLC .out file"),
    o: Path = typer.Option(None, "-o", help="Output file (default stdout)")
):
    """
    Parse the .out file from TLA+ TLC and output a Mermaid Gantt chart for event periods.
    """
    states = parse_tlc_out_states(outfile)
    # Collect periods for each (subject, data) - Consent, Contract, Processing etc.
    subject_periods = {}
    for st in states:
        # Legal bases
        for lb in st.get('legalBases', []):
            k = (lb['subject'], lb['data'], lb['type'])
            period = (lb['start'], lb['end']) if lb.get('start') and lb.get('end') else None
            if period:
                subject_periods.setdefault(k, set()).add(period)
        # Processes
        for p in st.get('processes', []):
            k = (p['subject'], p['data'], 'Processing')
            period = (p['start'], p['end']) if p.get('start') and p.get('end') else None
            if period:
                subject_periods.setdefault(k, set()).add(period)


    # Compose Mermaid
    print("DEBUG FINAL subject_periods:", subject_periods, file=sys.stderr)
    out = ["gantt", "    title GDPR Data Processing Timeline", "    dateFormat HH:mm"]
    # For each subject, data, type, print periods
    print("DEBUG subject_periods:", subject_periods, file=sys.stderr)
    # For each subject, data, type, print periods
    for (subject, data, typ), periods in subject_periods.items():
        out.append(f"    section {subject} {data} {typ}")
        for (start, end) in merge_intervals(list(periods)):
            label = f'{typ}\\n{format_time_2line(start)} -- {format_time_2line(end)}'
            # Show as bar with icon per type
            out.append(f'        {label} :active, {typ.lower()}{subject}{data}, {start[3]:02d}:{start[4]:02d}, {(end[3]-start[3])*60 + (end[4]-start[4])}m')
    mmd = "\n".join(out)
    if o:
        with open(o, 'w') as f:
            f.write(mmd)
    else:
        print(mmd)

if __name__ == "__main__":
    app()