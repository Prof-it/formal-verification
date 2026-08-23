import re

def classify_tlc_error(tlc_output, skills_db):
    for skill in skills_db:
        m = re.search(skill["pattern"], tlc_output, re.DOTALL)
        if m:
            return {"key": skill["key"], "strategy": skill["strategy"], "match": m.group(), "groups": m.groupdict()}
    return {"key": "unknown", "strategy": "No skill defined for this error type.", "match": "", "groups": {}}
