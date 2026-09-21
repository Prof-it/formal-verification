import json

def llm_analyze_tlc_error(llm_provider, task, tla_code, tlc_output):
    """
    Query the LLM to analyze TLC errors and suggest repair skills and new rules.
    Returns a dict: {'diagnosis', 'error_type', 'repair_skill', 'new_rule'}
    """
    prompt = f"""You are a TLA+ troubleshooting expert.

    TASK:
    {task}

    TLA+ SPEC:
    {tla_code}

    TLC OUTPUT:
    {tlc_output}

    INSTRUCTIONS:
    - Diagnose and briefly explain the error.
    - Classify the error type (e.g., parse_error, semantic_error, invariant_violation).
    - Suggest the best repair skill for this error, focusing on a single root cause or undefined operator at a time (e.g., always the first undefined operator if multiple).
    - For the repair skill, provide:
        - "strategy": a one-line summary of the fix (e.g., "Define missing recursive function as bracket-domain."),
        - "suggested_skill": a detailed, actionable fix (e.g., code to insert, exact text, or step-by-step guidance).
    - Propose a regex/string rule for classifying this error in the future, with:
        - "pattern": regex for the error,
        - "key": unique id,
        - "strategy": one-line summary,
        - "suggested_skill": copy the detailed fix above.

    Return a valid JSON object with the following fields:
    - "diagnosis"
    - "error_type"
    - "repair_skill": an object with "strategy" and "suggested_skill" fields
    - "new_rule": an object with "pattern", "key", "strategy", and "suggested_skill"
    """

    result_str = llm_provider.generate(prompt)
    try:
        result = json.loads(result_str)
    except Exception:
        return {"diagnosis": result_str, "error_type": "llm_parse_failure", "repair_skill": None, "new_rule": None}

    # Double check non-informative repair_skill
    if (
        "repair_skill" in result
        and (
            not isinstance(result["repair_skill"], dict)
            or len(str(result["repair_skill"].get("suggested_skill", "")).strip()) < 40
        )
    ):
        print("[WARNING] LLM returned a non-informative repair_skill! Prompt the LLM again or escalate.")

    return result
