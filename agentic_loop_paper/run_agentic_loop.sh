#!/bin/zsh

# Load OpenAI API key from .env file in project root (using grep and export)
if [[ -f .env ]]; then
    export OPENAI_API_KEY=$(grep '^OPENAI_API_KEY=' .env | cut -d '=' -f2-)
    if [[ -z $OPENAI_API_KEY ]]; then
        echo "OPENAI_API_KEY set in .env, but value is empty."
        exit 1
    fi
else
    echo ".env file not found in project root!"
    exit 1
fi

# Path to TLA tools JAR and project layout
TLA_JAR="tla/tla2tools.jar"

# Run the agentic_loop comparison experiment
PYTHONPATH=src python -m agentic_loop.compare_cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar $TLA_JAR \
  --module-dir tla \
  --output-dir results/comparison \
  --prompts-dir prompts \
  --prompt-mode one_shot \
  --max-iterations 3 \
  --provider openai \
  --model gpt-4o

# Display a helpful finish message
echo "Agentic loop baseline vs loop experiment completed."