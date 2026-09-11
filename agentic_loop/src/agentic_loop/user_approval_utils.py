import json

MAX_REJECTIONS = 2  # User approval/fix cycles before escalation

def prompt_human_for_skill_approval(
    candidate_rule,
    repair_skill_text,
    modular_issue=False,
    suggestion_count=0
):
    """
    Handles all user approval interaction for a candidate rule/proposed plan.
    Returns:
      decision: one of 'pass', 'continue', 'break'
      suggestion_count: updates (increment on rejection/invalid)
      diagnosis_context_update: context string to add for LLM if rejected
    """

    diagnosis_context_update = ""
    if modular_issue:
        print("[AGENTIC LOOP FEEDBACK] The suggested fix tries to address multiple unknown operator/root causes at once.")
    if repair_skill_text:
        print("\n--- Proposed Repair Skill/Prompt ---")
        print(repair_skill_text)
        print("------------------------------------\n")
    if candidate_rule:
        print(f"\nSuggested new rule for this session only (not yet saved to DB):\n{json.dumps(candidate_rule, indent=2)}\n")

    if suggestion_count >= MAX_REJECTIONS:
        print("[AGENTIC LOOP] Exceeded maximum attempts to get LLM to isolate a single-operator fix.")
        print("Manual intervention required.")
        print("[Candidate Rule]:", json.dumps(candidate_rule, indent=2))
        print("[Candidate Plan]:", repair_skill_text)
        user_override = input("Type 'y' to accept this suggestion anyway, 'n' to abort, or anything else to retry: ").strip().lower()
        if user_override == 'y':
            return 'pass', suggestion_count, ""
        elif user_override == 'n':
            return 'break', suggestion_count, ""
        else:
            suggestion_count = 0  # Reset counter for more tries
            return 'continue', suggestion_count, ""
        
    user_resp = input("Approve this plan/rule for session repair? (y/approve, n/reject+advice, d/skip): ").strip().lower()
    if user_resp.startswith("y"):
        return 'pass', suggestion_count, ""
    elif user_resp.startswith("n"):
        rej_reason = input("Please specify reason/advice for LLM: ").strip()
        suggestion_count += 1
        diagnosis_context_update = (
            f'\nREJECTED_RULE: {json.dumps(candidate_rule)}'
            f'\nREJECTED_PLAN: {json.dumps(repair_skill_text)}'
            f'\nREJECTION_REASON: {rej_reason}\n'
        )
        return 'continue', suggestion_count, diagnosis_context_update
    elif user_resp.startswith("d"):
        print("Skipping this proposal. (Skill will remain as 'unknown')")
        return 'break', suggestion_count, ""
    else:
        print("Invalid response. Use y/n/d.")
        suggestion_count += 1
        return 'continue', suggestion_count, ""
