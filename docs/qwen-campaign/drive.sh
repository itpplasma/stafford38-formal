#!/usr/bin/env bash
# Serial driver: one Pi run per task; commit/push ledger after each; stop on
# non-done results, owner gates, or after a review checkpoint task.
# Usage: drive.sh START_RUN_NUMBER "T13 T22 T36"   (checkpoint ids to stop after)
set -uo pipefail
C=/Users/ert/proj/stafford38-formal/docs/qwen-campaign
M=/Users/ert/proj/stafford38-formal
W=/Users/ert/proj/stafford38-qwen
n=$1; stops=" $2 "
while true; do
  $C/run-pi.sh $n >/dev/null 2>&1
  log=$C/runs/run-$(printf '%02d' $n).log
  task=$(grep -m1 '^TASK:' $log | awk '{print $2}')
  res=$(grep -m1 '^RESULT:' $log | awk '{print $2}')
  echo "run $n: task=${task:-?} result=${res:-NONE}"
  git -C $M add docs/qwen-campaign/STATE.md docs/qwen-campaign/notes 2>/dev/null
  git -C $M commit -q -m "Campaign ledger: ${task:-run $n} ${res:-no-report}" 2>/dev/null
  git -C $M push -q origin main 2>&1 | tail -1
  git -C $W push -q origin qwen/paper-route 2>&1 | tail -1
  [[ "$res" == "done" ]] || { echo "STOP: result=${res:-NONE}"; exit 1; }
  [[ "$stops" == *" $task "* ]] && { echo "CHECKPOINT after $task"; exit 0; }
  n=$((n+1))
done
