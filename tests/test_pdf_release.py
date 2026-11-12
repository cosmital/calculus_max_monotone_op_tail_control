"""Regression checks for the PDF-only distribution and review binding."""
from pathlib import Path
import json
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import verify
from refresh_checksums import distributable_files
from export_release import export


class PDFReleaseTests(unittest.TestCase):
    def copy_package(self, root):
        for source in distributable_files(ROOT):
            target = root / source.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        shutil.copyfile(ROOT / 'SHA256SUMS.txt', root / 'SHA256SUMS.txt')

    def test_pdf_only_copy_runs_metadata_and_author_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'package'
            self.copy_package(root)
            self.assertFalse(list(root.rglob('*.tex')))
            self.assertEqual(verify.metadata_gate(root)['numbered_items'], 62)
            self.assertEqual(verify.coverage_gate(root)['status'], 'COVERAGE_REVIEW_RECORDED')

    def test_changed_pdf_or_correspondence_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'package'
            self.copy_package(root)
            pdf = root / 'manuscript/monotone_calculus.pdf'
            original = pdf.read_bytes()
            pdf.write_bytes(original + b'changed')
            with self.assertRaises(verify.GateError):
                verify.metadata_gate(root)
            with self.assertRaises(verify.GateError):
                verify.coverage_gate(root)
            pdf.write_bytes(original)
            dictionary = root / 'docs/result_dictionary.json'
            data = json.loads(dictionary.read_text(encoding='utf-8'))
            data['results'][0]['declarations'].pop()
            dictionary.write_text(json.dumps(data), encoding='utf-8')
            with self.assertRaisesRegex(verify.GateError, 'claim/mapping changed'):
                verify.metadata_gate(root)
            with self.assertRaisesRegex(verify.GateError, 'correspondence changed'):
                verify.coverage_gate(root)

    def test_revoked_review_and_changed_lean_sources_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'package'
            self.copy_package(root)
            path = root / 'docs/supplemental_results.json'
            original = path.read_bytes()
            records = json.loads(original)
            records[0]['semantic_certified'] = False
            path.write_text(json.dumps(records), encoding='utf-8')
            with self.assertRaisesRegex(verify.GateError, 'review pending'):
                verify.coverage_gate(root)
            path.write_bytes(original)
            proof = root / 'PaperChecks.lean'
            proof.write_bytes(proof.read_bytes() + b'\n-- changed after review\n')
            with self.assertRaisesRegex(verify.GateError, 'Lean sources changed'):
                verify.coverage_gate(root)

    def test_export_has_no_private_tex_archives_or_dangling_tex_links(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'upload'
            export(root)
            self.assertFalse(list(root.rglob('*.tex')))
            self.assertFalse((root / 'historical').exists())
            for filename in ('RESULT_DICTIONARY.md', 'LABEL_INDEX.md', 'PROOF_DETAILS.md', 'index.html'):
                content = (root / 'docs' / filename).read_text(encoding='utf-8')
                self.assertNotIn('.tex#', content)
                self.assertIn('.pdf', content)
            with self.assertRaises(ValueError):
                export(root)


if __name__ == '__main__':
    unittest.main()
