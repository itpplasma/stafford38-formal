#!/usr/bin/env python3
"""Build the publication review from public, pinned inputs without a Lean build.

The PDF receipt must identify paper_source (repo, commit, file, sha256),
formal_source and library_source (repo, commit), source_hashes for every source_files entry,
and the two PDF hashes. Regenerate that receipt with the PDFs from the
selected pins; changing metadata alone does not establish PDF provenance.
--check-assets runs only this packaging gate, without network or output.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def check_review_assets(root, mapping):
    """Reject PDFs whose recorded frozen inputs differ from the rendered map."""
    if mapping.get('candidate', {}).get('status') == 'pending-final-source-pins':
        raise ValueError('Candidate map awaits final source pins; publication is pending')
    paper = mapping['sources']['paper']
    formal = mapping['sources']['formal']
    library = mapping['sources']['library']
    if paper['repo'] != formal['repo']:
        raise ValueError('Review site requires the public manuscript snapshot in the formal repository')
    audit = root / 'docs/paper-lean-audit'
    receipt = json.loads((audit / 'review-pdfs.json').read_text())

    def pinned_bytes(file):
        return subprocess.check_output(
            ['git', '-C', str(root), 'show', paper['commit'] + ':' + file],
            stderr=subprocess.PIPE)

    def digest(data):
        return hashlib.sha256(data).hexdigest()

    expected_paper = {key: paper[key] for key in ['repo', 'commit', 'file']}
    expected_paper['sha256'] = digest(pinned_bytes(paper['file']))
    if receipt.get('paper_source') != expected_paper:
        raise ValueError('PDF receipt does not match the pinned manuscript source')
    if receipt.get('paper_commit') != paper.get('origin_commit', paper['commit']):
        raise ValueError('PDF receipt does not match the manuscript origin commit')
    if receipt.get('formal_source') != {key: formal[key] for key in ['repo', 'commit']}:
        raise ValueError('PDF receipt does not match the pinned formal source')
    if receipt.get('library_source') != {key: library[key] for key in ['repo', 'commit']}:
        raise ValueError('PDF receipt does not match the pinned library source')

    source_files = receipt.get('source_files', [])
    required = {Path(paper['file']).name, 'ai_review.tex', 'references.bib', 'lean_proof_details.tex'}
    if (not isinstance(source_files, list) or any(not isinstance(name, str) for name in source_files)
            or not required.issubset(source_files)):
        raise ValueError('PDF receipt omits required manuscript compilation inputs')
    source_hashes = receipt.get('source_hashes', {})
    source_bytes = {}
    for filename in source_files:
        if not isinstance(filename, str) or Path(filename).name != filename:
            raise ValueError('PDF receipt source_files must name snapshot files')
        file = str(Path(paper['file']).parent / filename)
        data = pinned_bytes(file)
        if source_hashes.get(filename) != digest(data):
            raise ValueError('PDF receipt source hash differs from the pinned input: ' + filename)
        source_bytes[filename] = data
    # Both PDF accounts load these macros. A correctly hashed source receipt
    # must not conceal hyperlinks to a different Lean/library revision.
    annotations = source_bytes['ai_review.tex'].decode('utf-8')
    active_lines = []
    for line in annotations.splitlines():
        for match in re.finditer('%', line):
            preceding = line[:match.start()]
            slashes = len(preceding) - len(preceding.rstrip('\\'))
            if slashes % 2 == 0:
                line = preceding
                break
        active_lines.append(line)
    annotations = '\n'.join(active_lines)
    for macro, source in [('leanrepo', formal), ('leanlibrepo', library)]:
        values = re.findall(r'\\(?:newcommand|renewcommand|providecommand)\s*\{\\'
                            + macro + r'\}\s*\{([^{}]*)\}', annotations)
        expected_url = 'https://github.com/' + source['repo'] + '/blob/' + source['commit']
        if values != [expected_url]:
            raise ValueError('Pinned manuscript link macro differs from the map source: ' + macro)
    frozen_pdfs = {}
    for filename in ['human_readable_main.pdf', 'lean_proof_details.pdf']:
        data = (audit / filename).read_bytes()
        if receipt.get('pdfs', {}).get(filename) != digest(data):
            raise ValueError('PDF bytes differ from the frozen receipt: ' + filename)
        frozen_pdfs[filename] = data
    return frozen_pdfs


def main():
    root = Path(__file__).resolve().parent.parent
    mapping = json.loads((root / 'tools/paper_lean_audit/paper-lean-map.json').read_text())
    frozen_pdfs = check_review_assets(root, mapping)
    if '--check-assets' in sys.argv[1:]:
        print('Review PDFs and compilation inputs match the exact map pins.')
        return
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
    for filename, data in frozen_pdfs.items():
        (output / filename).write_bytes(data)
    (output / '.nojekyll').write_text('')
    print('Publication review built with pinned inputs and both readable PDFs.')


if __name__ == '__main__':
    main()
