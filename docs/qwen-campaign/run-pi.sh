#!/usr/bin/env bash
# Usage: run-pi.sh N   -> one Pi task run, log in runs/run-NN.log
set -uo pipefail
C=/Users/ert/proj/stafford38-formal/docs/qwen-campaign
n=$(printf '%02d' "$1")
PI_RUN_FIRST_OUTPUT_TIMEOUT=14400 $HOME/code/prompts/scripts/pi-run.sh --dir /Users/ert/proj/stafford38-formal \
  --prompt-file $C/prompt.md --log $C/runs/run-$n.log --thinking high
echo "pi-run exit=$?"
