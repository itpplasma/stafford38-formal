"""Behavioral packaging oracles using independently frozen Git/PDF fixtures."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'build-review-site.py'
spec = importlib.util.spec_from_file_location('review_site', SCRIPT)
review_site = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review_site)


class ReviewAssetGateTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='review-asset-fixture-')
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.audit = self.root / 'docs/paper-lean-audit'
        self.snapshot = self.audit / 'manuscript'
        self.snapshot.mkdir(parents=True)
        self.git('init', '-q')
        (self.root / 'Formal.lean').write_text('theorem checked : True := by trivial\n')
        self.git('add', 'Formal.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Frozen formal source F')
        self.formal_commit = self.git('rev-parse', 'HEAD').strip()
        self.formal = {'repo': 'example/formal', 'commit': self.formal_commit}
        self.library = {'repo': 'example/library', 'commit': self.formal_commit}
        self.files = {
            'human_readable_main.tex': 'Author proof A: every integer is even.\n',
            'ai_review.tex': ('Visible author-review annotations A.\n'
                              '\\newcommand{\\leanrepo}{https://github.com/example/formal/blob/'
                              + self.formal_commit + '}\n'
                              '\\newcommand{\\leanlibrepo}{https://github.com/example/library/blob/'
                              + self.formal_commit + '}\n'),
            'references.bib': 'Bibliography A.\n',
            'lean_proof_details.tex': 'Formal comparison A.\n',
        }
        for filename, text in self.files.items():
            (self.snapshot / filename).write_text(text)
        self.git('add', 'docs')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Frozen source A')
        self.commit_a = self.git('rev-parse', 'HEAD').strip()
        self.paper = {'repo': 'example/formal', 'commit': self.commit_a,
                      'file': 'docs/paper-lean-audit/manuscript/human_readable_main.tex',
                      'origin_commit': 'a' * 40}
        self.mapping = {'sources': {'paper': self.paper, 'formal': self.formal, 'library': self.library}}
        # These independently chosen bytes stand for the frozen PDF exports;
        # the gate audits provenance and bytes, not mathematical PDF content.
        self.pdf_bytes = {
            'human_readable_main.pdf': b'%PDF-1.7\nAuthor review A\n%%EOF\n',
            'lean_proof_details.pdf': b'%PDF-1.7\nComparison A\n%%EOF\n',
        }
        for filename, data in self.pdf_bytes.items():
            (self.audit / filename).write_bytes(data)
        self.receipt = {
            'paper_commit': 'a' * 40,
            'paper_source': {'repo': 'example/formal', 'commit': self.commit_a,
                             'file': self.paper['file'],
                             'sha256': self.sha(self.files['human_readable_main.tex'].encode())},
            'formal_source': dict(self.formal),
            'library_source': dict(self.library),
            'source_files': list(self.files),
            'source_hashes': {name: self.sha(text.encode()) for name, text in self.files.items()},
            'pdfs': {name: self.sha(data) for name, data in self.pdf_bytes.items()},
        }
        self.write_receipt()

    @staticmethod
    def sha(data):
        return hashlib.sha256(data).hexdigest()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args], text=True)

    def write_receipt(self):
        (self.audit / 'review-pdfs.json').write_text(json.dumps(self.receipt))

    def test_accepts_one_frozen_source_and_exact_pdf_exports(self):
        # Later checkout edits cannot alter the source objects chosen by pins.
        (self.snapshot / 'human_readable_main.tex').write_text('Uncommitted draft C.\n')
        review_site.check_review_assets(self.root, self.mapping)

    def test_rejects_pdfs_attested_to_a_different_manuscript(self):
        (self.snapshot / 'human_readable_main.tex').write_text('Author proof B: every integer is odd.\n')
        self.git('add', 'docs/paper-lean-audit/manuscript/human_readable_main.tex')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Frozen source B')
        self.receipt['paper_source']['commit'] = self.git('rev-parse', 'HEAD').strip()
        self.receipt['paper_source']['sha256'] = self.sha((self.snapshot / 'human_readable_main.tex').read_bytes())
        self.write_receipt()
        with self.assertRaisesRegex(ValueError, 'pinned manuscript source'):
            review_site.check_review_assets(self.root, self.mapping)

    def test_rejects_source_input_or_formal_pin_changes(self):
        self.receipt['source_hashes']['ai_review.tex'] = self.sha(b'Annotations B')
        self.write_receipt()
        with self.assertRaisesRegex(ValueError, 'source hash.*ai_review.tex'):
            review_site.check_review_assets(self.root, self.mapping)
        self.receipt['source_hashes']['ai_review.tex'] = self.sha(self.files['ai_review.tex'].encode())
        self.receipt['formal_source']['commit'] = 'b' * 40
        self.write_receipt()
        with self.assertRaisesRegex(ValueError, 'pinned formal source'):
            review_site.check_review_assets(self.root, self.mapping)

    def test_rejects_swapped_pdf_even_with_matching_source_metadata(self):
        (self.audit / 'lean_proof_details.pdf').write_bytes(b'%PDF-1.7\nComparison B\n%%EOF\n')
        with self.assertRaisesRegex(ValueError, 'PDF bytes.*lean_proof_details.pdf'):
            review_site.check_review_assets(self.root, self.mapping)

    def test_rejects_different_library_receipt_and_wrong_source_hyperlinks(self):
        self.receipt['library_source']['commit'] = 'b' * 40
        self.write_receipt()
        with self.assertRaisesRegex(ValueError, 'pinned library source'):
            review_site.check_review_assets(self.root, self.mapping)
        self.receipt['library_source'] = dict(self.library)
        for macro, repository in [('leanrepo', 'formal'), ('leanlibrepo', 'library')]:
            with self.subTest(macro=macro):
                stale = self.files['ai_review.tex'].replace(
                    'example/' + repository + '/blob/' + self.formal_commit,
                    'example/' + repository + '/blob/' + 'b' * 40)
                (self.snapshot / 'ai_review.tex').write_text(stale)
                self.git('add', 'docs/paper-lean-audit/manuscript/ai_review.tex')
                self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                         '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Snapshot with stale ' + macro)
                snapshot_commit = self.git('rev-parse', 'HEAD').strip()
                self.paper['commit'] = snapshot_commit
                self.receipt['paper_source']['commit'] = snapshot_commit
                self.receipt['source_hashes']['ai_review.tex'] = self.sha(stale.encode())
                self.write_receipt()
                with self.assertRaisesRegex(ValueError, 'link macro.*' + macro):
                    review_site.check_review_assets(self.root, self.mapping)

    def test_legacy_receipt_and_pending_candidate_cannot_publish(self):
        del self.receipt['paper_source']
        self.write_receipt()
        with self.assertRaisesRegex(ValueError, 'pinned manuscript source'):
            review_site.check_review_assets(self.root, self.mapping)
        self.mapping['candidate'] = {'status': 'pending-final-source-pins'}
        with self.assertRaisesRegex(ValueError, 'publication is pending'):
            review_site.check_review_assets(self.root, self.mapping)

    def test_stale_bundle_is_rejected_before_publication_output(self):
        del self.receipt['paper_source']
        self.write_receipt()
        scripts = self.root / 'scripts'
        scripts.mkdir()
        local_script = scripts / SCRIPT.name
        shutil.copyfile(SCRIPT, local_script)
        map_path = self.root / 'tools/paper_lean_audit/paper-lean-map.json'
        map_path.parent.mkdir(parents=True)
        map_path.write_text(json.dumps(self.mapping))
        result = subprocess.run([sys.executable, str(local_script)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('PDF receipt does not match the pinned manuscript source', result.stderr)
        self.assertFalse((self.root / 'public-review').exists(), 'a rejected bundle cannot create publication output')


if __name__ == '__main__':
    unittest.main()
