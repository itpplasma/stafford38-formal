#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/verification
python3 - <<'PY'
import json
from pathlib import Path
manifest = json.loads(Path('docs/paper-lean-audit/linked-declarations.json').read_text())
entries = manifest['declarations']
# The snapshot is the independent input to the name/axiom audit.
import hashlib
import re
snapshot = Path('docs/paper-lean-audit/manuscript')
provenance = json.loads((snapshot / 'provenance.json').read_text())
for entry in provenance['files']:
    actual = hashlib.sha256((snapshot / entry['path']).read_bytes()).hexdigest()
    if actual != entry['sha256']:
        raise SystemExit('Manuscript snapshot hash mismatch: ' + entry['path'])
paper = (snapshot / 'human_readable_main.tex').read_text()
paper = re.sub(r'(?m)^\s*%.*$', '', paper)
linked = {(('library' if macro == 'leanlib' else 'formal'), file, name)
          for macro, file, line, name in re.findall(
              r'\\(leandecl|leanlib)\{([^}]+)\}\{(\d+)\}\{([^}]+)\}', paper)}
recorded = {(entry['repo'], entry['file'], entry['name']) for entry in entries}
if linked != recorded:
    raise SystemExit('Declaration manifest differs from the manuscript snapshot')
modules = sorted({entry['file'].removesuffix('.lean').replace('/', '.') for entry in entries})
names = sorted({entry['name'] for entry in entries})
source = '\n'.join('import ' + module for module in modules) + '\n\n'
source += '\n'.join('#check ' + name + '\n#print axioms ' + name for name in names) + '\n'
Path('.lake/verification/PaperDeclarations.lean').write_text(source)
PY
lake env lean --trust=0 .lake/verification/PaperDeclarations.lean \
  > .lake/verification/paper-declarations.log 2>&1
python3 - <<'PY'
import json
import re
from pathlib import Path
manifest = json.loads(Path('docs/paper-lean-audit/linked-declarations.json').read_text())
expected = {entry['name'] for entry in manifest['declarations']}
text = Path('.lake/verification/paper-declarations.log').read_text()
found = {name: {x.strip() for x in body.split(',') if x.strip()}
         for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S)}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
if expected - found.keys():
    raise SystemExit('Missing declaration reports: ' + ', '.join(sorted(expected - found.keys())))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in sorted(expected):
    if found[name] - allowed:
        raise SystemExit(f'Forbidden axioms for {name}: {sorted(found[name] - allowed)}')
if re.search(r'sorryAx|admitAx|Lean\.ofReduceBool|(^|:) error(\([^)]*\))?:', text):
    raise SystemExit('Forbidden proof mechanism or Lean error in paper declarations')
print(f'Paper-linked declarations: {len(expected)} exact names and axiom reports passed')
PY
