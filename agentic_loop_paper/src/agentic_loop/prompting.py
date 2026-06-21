from pathlib import Path
from typing import Dict


PROMPT_FILES = {
    "zero_shot": "zero_shot_nl_to_tla.txt",
    "one_shot": "one_shot_nl_to_tla.txt",
    "fix_parse": "fix_parse.txt",
    "fix_semantic": "fix_semantic.txt",
}


def load_prompt_template(prompts_dir: str, prompt_name: str) -> str:
    if prompt_name not in PROMPT_FILES:
        raise ValueError(f"Unsupported prompt name: {prompt_name}")

    prompt_path = Path(prompts_dir) / PROMPT_FILES[prompt_name]
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt template not found: {prompt_path}")

    return prompt_path.read_text(encoding="utf-8")


def render_prompt(template: str, values: Dict[str, str]) -> str:
    return template.format(**values)
