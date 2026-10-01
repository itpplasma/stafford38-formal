#!/usr/bin/env python3
"""Build the publication review from public, pinned inputs without a Lean build."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
mapping = json.loads((root / 'tools/paper_lean_audit/paper-lean-map.json').read_text())
output = root / 'public-review'
with tempfile.TemporaryDirectory(prefix='stafford-review-inputs-') as scratch:
    arguments = []
    for key, flag in [('library', '--library'), ('global', '--global'), ('mathlib', '--mathlib')]:
        source = mapping['sources'][key]
        destination = Path(scratch) / key
        subprocess.run(['git', 'init', '-q', str(destination)], check=True)
        subprocess.run(['git', '-C', str(destination), 'remote', 'add', 'origin',
                        'https://github.com/' + source['repo'] + '.git'], check=True)
        subprocess.run(['git', '-C', str(destination), 'fetch', '--filter=blob:none',
                        '--depth=1', 'origin', source['commit']], check=True)
        arguments.extend([flag, str(destination)])
    subprocess.run(['node', str(root / 'tools/paper_lean_audit/build.mjs'), '--check',
                    '--paper', str(root), '--formal', str(root), '--out', str(output),
                    *arguments], check=True)
shutil.copyfile(output / 'stafford38-paper-lean-audit.html', output / 'index.html')
for filename in ['human_readable_main.pdf', 'lean_proof_details.pdf']:
    shutil.copyfile(root / 'docs/paper-lean-audit' / filename, output / filename)
(output / '.nojekyll').write_text('')
print('Publication review built with pinned inputs and both readable PDFs.')
