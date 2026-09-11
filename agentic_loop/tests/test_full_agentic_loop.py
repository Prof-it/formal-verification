import os
import unittest
from pathlib import Path
from agentic_loop.engine import run_experiment
from agentic_loop.models import TaskSpec, LoopConfig
from agentic_loop.providers import OpenAICompatibleProvider

# === BEGIN: Change these variables to target a different task/example ===
TASK_YAML_PATH = "tasks/beginner/car_talk_puzzle.yaml"
MODULE_DIR = "modules/car_talk_puzzle__d4dhkb_/CarTalkPuzzle"
PROMPTS_DIR = "prompts"
OUTPUT_DIR = "results/comparison"
TLA_CFG = "CarTalkPuzzle.toolbox/Model_1/MC.cfg"
MODULE_NAME = "MC"
TLA_JAR_PATH = "tla/tla2tools.jar"
LLM_MODEL = "gpt-4o"
# === END: Change here for other examples! ===

def read_task_yaml(task_yaml_path):
    # Simple/unsafe YAML-like parser for your examples. Use PyYAML for true YAML spec if you want!
    data = {}
    lines = Path(task_yaml_path).read_text(encoding="utf-8").splitlines()
    block = None
    text_blocks = {}
    for i, line in enumerate(lines):
        if ":" in line and not line.strip().startswith("#") and not line.strip().endswith(": |"):
            k, v = line.split(":", 1)
            data[k.strip()] = v.strip().strip('"').strip("'")
        # Block-style text (YAML multiline)
        if line.strip().endswith(": |"):
            block = line.split(":")[0].strip()
            text_blocks[block] = []
            for subline in lines[i+1:]:
                if subline.startswith("  "):
                    text_blocks[block].append(subline.strip())
                else:
                    break
            data[block] = "\n".join(text_blocks[block])
            block = None
    return TaskSpec(
        name=data.get("name", MODULE_NAME),
        module_name=data.get("module_name", MODULE_NAME),
        cfg_file=data.get("cfg_file", TLA_CFG),
        system_text=data.get("system_text", ""),
        requirement_text=data.get("requirement_text", ""),
    )

class AgenticLoopIntegrationTest(unittest.TestCase):
    def test_repair_loop_generic(self):
        task = read_task_yaml(TASK_YAML_PATH)
        config = LoopConfig(
            tla_jar_path=TLA_JAR_PATH,
            module_dir=MODULE_DIR,
            output_dir=OUTPUT_DIR,
            prompt_mode="one_shot",
            max_iterations=5,
            timeout_seconds=180,
        )
        config.autoapprove_new_skills = False  # Set to True for non-interactive CI or always-accept-test
        prompts_dir = PROMPTS_DIR
        provider = OpenAICompatibleProvider(model=LLM_MODEL)
        result = run_experiment(
            task=task,
            config=config,
            prompts_dir=prompts_dir,
            provider=provider,
            mode="loop",
        )
        print("Agentic loop outputs:", result)
        # Minimal check: output should include those fields if the tool chain did not raise
        self.assertIn("json", result)
        # You can add asserts about successful repair, or that skills DB is updated after session

if __name__ == "__main__":
    unittest.main()
