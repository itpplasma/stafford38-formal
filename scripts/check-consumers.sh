#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/verification
log=.lake/verification/independent-consumers.log
: > "$log"
for source in tests/CorollaryConsumer.lean tests/LocalizedDifferentialConsumer.lean; do
  lake env lean --trust=0 "$source" >> "$log" 2>&1
done
python3 - "$log" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
expected = {
    'orePaperConsumer', 'exactDegreePaperConsumer', 'leftPaperConsumer',
    'evolutionConsumer', 'Stafford38.Evolution.tensorEvolutionaryCorollary',
    'actualLocalizedOperatorConsumer', 'actualPrincipalOpenConsumer',
    'actualPartialLaurentConsumer', 'actualRationalOperatorConsumer',
}
reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S))
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    reports[name] = ''
if expected - reports.keys():
    raise SystemExit(f'Missing independent consumers: {expected - reports.keys()}')
for name in expected:
    axioms = {x.strip() for x in reports[name].split(',') if x.strip()}
    if axioms - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit(f'Forbidden consumer axioms: {name}: {axioms}')
if re.search(r'sorryAx|admitAx|Lean\.ofReduceBool|declaration uses .sorry|(^|:) error:', text):
    raise SystemExit('Forbidden proof mechanism or Lean error in consumer output')
print(f'Independent literal consumers: {len(expected)} axiom reports passed')
PY
