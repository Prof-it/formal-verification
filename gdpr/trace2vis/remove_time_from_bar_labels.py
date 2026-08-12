import re

def remove_time_from_bar_labels(mmd_code: str) -> str:
    """
    Remove all time information from the label of all bars (not milestones), i.e., for any label of the form
    [Type, Subject, Data, ...] -> [Type, Subject, Data]
    Only applies to lines inside any section except Milestones, and only for labels with 4+ fields.
    """
    lines = mmd_code.splitlines()
    in_milestones = False
    for i, line in enumerate(lines):
        if line.strip().startswith('section Milestones'):
            in_milestones = True
            continue
        if line.strip().startswith('section') and not line.strip().startswith('section Milestones'):
            in_milestones = False
        if not in_milestones:
            def repl(match):
                label = match.group(1)
                fields = [f.strip() for f in label.split(',')]
                if len(fields) >= 4:
                    return f"[{' , '.join(fields[:3])}]"
                return match.group(0)
            lines[i] = re.sub(r'\[(.*?)\]', repl, line)
    return '\n'.join(lines)
