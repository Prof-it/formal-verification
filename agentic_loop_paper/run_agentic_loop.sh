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

# Run the agentic_loop comparison experiment for each beginner task
for TASK_FILE in tasks/beginner/*.yaml; do
  TASK_NAME=$(basename "$TASK_FILE" .yaml)
  RESULTS_ROOT="results/$TASK_NAME"
  COMPARISON_DIR="$RESULTS_ROOT/comparison"
  FIGURES_DIR="figures/$TASK_NAME"

  echo "Running comparison for task: $TASK_NAME"
  PYTHONPATH=src python -m agentic_loop.compare_cli \
    --task "$TASK_FILE" \
    --tla-jar $TLA_JAR \
    --output-dir "$COMPARISON_DIR" \
    --prompts-dir prompts \
    --prompt-mode one_shot \
    --max-iterations 3 \
    --provider openai \
    --model gpt-4o

  echo "Generating plots for task: $TASK_NAME"
  PYTHONPATH=src python -m agentic_loop.plot_results \
    --results-root "$RESULTS_ROOT" \
    --task "$TASK_NAME" \
    --output-dir "$FIGURES_DIR"
done

# Display a helpful finish message
echo "Agentic loop experiment and plotting completed."
