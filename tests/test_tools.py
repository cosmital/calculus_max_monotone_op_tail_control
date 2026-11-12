"""Tests of Python indexing/gates only. These do NOT execute or verify Lean proofs."""
from pathlib import Path
import io
import json
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import verify
import refresh_metadata
import refresh_checksums
import checked_packet

class ToolTests(unittest.TestCase):
    def test_checked_packet_rejects_changed_bodies_wrong_order_and_failed_receipt(self):
        # Receipt fixtures test staging integrity; they do not certify Lean proofs.
        import hashlib
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            drafts = root/'historical/proof_drafts'
            logs = root/'verification/current'
            drafts.mkdir(parents=True)
            logs.mkdir(parents=True)
            base, step = drafts/'Base.lean', drafts/'Step.lean'
            original = 'import Mathlib.Data.Nat.Basic\n\n/- Documentation:\nimport EndOfPaper.CommentOnly\n-/\ndef base : Nat := 1\n'
            base.write_text(original, encoding='utf-8')
            step.write_text('import EndOfPaper.Base\n\ntheorem step : base = 1 := rfl\n', encoding='utf-8')
            bundle = drafts/'Bundle.lean'
            bundle.write_text(checked_packet.compose_packet([base, step]), encoding='utf-8')
            self.assertIn('import EndOfPaper.CommentOnly', bundle.read_text(encoding='utf-8'))
            hashes = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in [base, step]}
            bundle.with_suffix('.sources.json').write_text(json.dumps(hashes), encoding='utf-8')
            log = logs/'native-lean-20990101T000000000-abcd.log'
            command = '$ lake env lean historical/proof_drafts/Bundle.lean\n'
            log.write_text(command+'Exit code: 0\n', encoding='utf-8')
            packet = {'file': bundle.relative_to(root).as_posix(), 'sources': list(hashes),
                'source_sha256': hashes, 'log': log.relative_to(root).as_posix()}
            self.assertEqual(checked_packet.validate_checked_packet(root, packet), {'Base', 'Step'})
            base.write_text(original.replace(':= 1', ':= 2'), encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'source hashes differ'):
                checked_packet.validate_checked_packet(root, packet)
            base.write_text(original, encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'dependency must precede'):
                checked_packet.compose_packet([step, base])
            log.write_text(command+'Exit code: 1\n', encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'No successful Lean check'):
                checked_packet.validate_checked_packet(root, packet)

    def test_staged_structure_is_indexed_without_comment_or_string_decoys(self):
        source = '''/- theorem commentDecoy : False -/
structure Point where
  coordinate : ℝ
@[simp] theorem Point.coordinate_eq (p : Point) : p.coordinate = p.coordinate := rfl
def description : String := "theorem stringDecoy : False"
private theorem internal : True := by trivial
'''
        self.assertEqual(refresh_metadata.staged_declaration_names(source),
            ['Point','Point.coordinate_eq','description'])

    def test_metadata_inventory(self):
        r=verify.metadata_gate(ROOT)
        self.assertEqual(r['numbered_items'],62)
        self.assertEqual(r['source_modules'],335)
        self.assertEqual(r['supplemental_items'],56)
        self.assertEqual(r['status'],'METADATA_ONLY_OK')
        for item in verify.read_dictionary(ROOT)['results']:
            self.assertTrue(item['number'].startswith(str(item['section'])+'.'))

    def test_author_acceptance_is_explicitly_recorded(self):
        d=verify.read_dictionary(ROOT)
        self.assertTrue(all(r['release_complete'] and r['semantic_certified'] for r in d['results']))
        from collections import Counter
        self.assertEqual(d['summary'],dict(Counter(r['scope'] for r in d['results'])))

    def test_following_moment_claims_are_preserved_outside_corollary(self):
        cor=next(r for r in verify.read_dictionary(ROOT)['results'] if r['key']=='cor:moments')
        extras=json.loads((ROOT/'docs/supplemental_results.json').read_text(encoding='utf-8'))
        following=next(r for r in extras if r['key']=='eq:moment')
        self.assertGreater(following['statement_line'],cor['end_line'])
        self.assertNotIn(r'\label{eq:moment}',cor['statement_tex'])
        self.assertIn(r'\label{eq:moment}',following['statement_tex'])
        self.assertEqual({c['id'] for c in cor['conclusions']},{'cor:moments:1','cor:moments:2'})
        self.assertEqual({c['id'] for c in cor['relocated_conclusions']},
                         {'cor:moments:3','cor:moments:4'})
        self.assertTrue(all(c['current_inventory_key']=='eq:moment' for c in cor['relocated_conclusions']))
        self.assertEqual(len(following['conclusions']),2)
        self.assertEqual(following['scope'],'complete')
        self.assertIn('ScalarMonotone.EndOfPaper.centered_moment_operator_cap',
                      {d['name'] for d in following['declarations']})
        self.assertTrue(following.get('semantic_certified',False))

    def test_coverage_rejects_incomplete_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'docs').mkdir()
            (root/'docs/result_dictionary.json').write_text(json.dumps({'results': [{
                'key':'fixture:incomplete','scope':'partial','declarations':[],
                'semantic_certified':True,'release_complete':True}]}),encoding='utf-8')
            (root/'docs/supplemental_results.json').write_text('[]',encoding='utf-8')
            with self.assertRaises(verify.GateError) as ctx:
                verify.coverage_gate(root)
            self.assertEqual(ctx.exception.code,2)
            self.assertIn('fixture:incomplete',str(ctx.exception))
        self.assertEqual(verify.coverage_gate(ROOT)['status'],'COVERAGE_REVIEW_RECORDED')

    def test_following_quantile_assertions_preserved(self):
        extras=json.loads((ROOT/'docs/supplemental_results.json').read_text(encoding='utf-8'))
        row=next(r for r in extras if r['key']=='eq:comonotonequantilesharp')
        private_source=ROOT/'manuscript/monotone_calculus.tex'
        following=row['following_assertions']
        self.assertEqual({f['id'] for f in following},
                         {'failure_without_comonotonicity','singleton_and_attainment'})
        self.assertEqual(len(row['conclusions']),3)
        if private_source.exists():
            source=private_source.read_text(encoding='utf-8')
            for claim in following:
                self.assertIn(claim['source_text'],source)
                pos=source.index(claim['source_text'])
                self.assertEqual(claim['source_line'],source.count('\n',0,pos)+1)
        else:
            index=json.loads((ROOT/'docs/PDF_INDEX.json').read_text(encoding='utf-8'))
            self.assertEqual(verify.correspondence_hash(row),
                index['claims'][row['key']]['correspondence_sha256'])
            self.assertTrue(all(claim['source_text'] for claim in following))
        if any(c['status']=='not_certified_as_full_current_statement' for c in row['conclusions']):
            self.assertNotEqual(row['scope'],'complete')
        self.assertTrue(row.get('semantic_certified'))
        self.assertTrue(row.get('release_complete'))

    def test_supplemental_approval_does_not_replace_missing_proof_mapping(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'docs').mkdir()
            (root/'docs/result_dictionary.json').write_text('{"results": []}',encoding='utf-8')
            (root/'docs/supplemental_results.json').write_text(json.dumps([{
                'key':'fixture:no_proof','scope':'complete','declarations':[],
                'semantic_certified':True,'release_complete':True}]),encoding='utf-8')
            with self.assertRaisesRegex(verify.GateError,'fixture:no_proof'):
                verify.coverage_gate(root)

    def test_missing_compiler_is_not_success(self):
        with patch('verify.shutil.which',return_value=None):
            with self.assertRaises(verify.GateError) as ctx:
                verify.compilation_gate(ROOT,io.StringIO(),False,False)
        self.assertEqual(ctx.exception.code,127)

    def test_compile_command_failure_is_propagated(self):
        # Mocked control-flow test, not compiler execution.
        with patch('verify.shutil.which',return_value='/nonexistent/test-only-lake'):
            with patch('verify.run_logged',return_value=23):
                with self.assertRaises(verify.GateError) as ctx:
                    verify.compilation_gate(ROOT,io.StringIO(),False,False)
        self.assertEqual(ctx.exception.code,23)

    def test_nested_comments_are_not_proof_tokens(self):
        text='/- outer /- sorry -/ inner -/\ntheorem x : True := by trivial -- admit\n'
        clean=verify.strip_lean_comments_and_strings(text)
        self.assertNotIn('sorry',clean)
        self.assertNotIn('admit',clean)
        self.assertEqual(clean.count('\n'),text.count('\n'))
        self.assertIn('theorem x',clean)

    def test_real_placeholder_survives_scan(self):
        clean=verify.strip_lean_comments_and_strings('theorem x : False := by\n  sorry\n')
        self.assertIn('sorry',clean)

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(verify.GateError):
            verify.strip_lean_comments_and_strings('/- incomplete')

    def test_dictionary_declarations_exist_in_inventory(self):
        d=verify.read_dictionary(ROOT)
        names={r['name'] for r in json.loads((ROOT/'docs/declarations.json').read_text())}
        self.assertGreaterEqual(len(names),2480)
        supplemental=json.loads((ROOT/'docs/supplemental_results.json').read_text(encoding='utf-8'))
        for r in d['results']+supplemental:
            for decl in r.get('declarations',[]):
                self.assertIn(decl['name'],names)

    def test_superseded_changevariables_is_not_current_coverage(self):
        current=verify.read_dictionary(ROOT)
        self.assertNotIn('prop:changevariables',{r['key'] for r in current['results']})
        old=json.loads((ROOT/'tests/fixtures/superseded_result_keys.json').read_text(encoding='utf-8'))
        self.assertIn('prop:changevariables',old['result_keys'])

    def test_arbitrary_product_not_hidden_by_old_cubic_proof(self):
        r=next(r for r in verify.read_dictionary(ROOT)['results'] if r['key']=='ex:productmultilevel')
        names={d['name'] for d in r['declarations']}
        prefix='ScalarMonotone.EndOfPaper.'
        self.assertTrue({prefix+'product_deviation_bound',
                         prefix+'productCoefficient_top_positive'} <= names)
        self.assertIn(r['scope'],{'partial','complete'})
        if r['scope']=='complete':
            required={prefix+n for n in (
                'product_deviation_bound','product_polynomial_expansion',
                'productProfile_root_representation','productProfile_parallel_monomials',
                'multilevel_product_operator_bound','multilevel_product_gaussian_bound')}
            self.assertTrue(required <= names)
            self.assertEqual(len(r['conclusions']),5)
            self.assertTrue(all(c['status']=='proof_supplied_author_review_recorded'
                                for c in r['conclusions']))
            self.assertTrue(all(d['file'].startswith('EndOfPaper/Product')
                                for d in r['declarations'] if d['name'] in required))
        self.assertIn('arbitrary-n',r['notes'])

    def test_unlabelled_items_have_keys(self):
        d=verify.read_dictionary(ROOT)
        for r in d['results']:
            if not r['labels']:
                self.assertTrue(r['key'].startswith(('statement:',r['kind']+':')))

    def test_comment_stripping_preserves_escaped_string(self):
        t='def s := "not a \\\" sorry"\n'
        self.assertNotIn('sorry',verify.strip_lean_comments_and_strings(t))

    def test_source_hashes_match_current_math(self):
        current=json.loads((ROOT/'docs/current_source_hashes.json').read_text())
        self.assertEqual(len(current),335)
        for file,digest in current.items():
            self.assertEqual(verify.sha256(ROOT/file),digest)

    def test_appendix_numbering(self):
        text=r'\section{Main}\begin{lemma}A\end{lemma}\appendix\section{First}\begin{lemma}B\end{lemma}\section{Second}\begin{lemma}C\end{lemma}'
        self.assertEqual([r['number'] for r in verify.parse_numbered_statements(text)],['1.1','A.1','B.1'])

    def test_compilation_includes_all_reader_and_audit_files(self):
        with patch('verify.shutil.which',return_value='lake'):
            with patch('verify.run_logged',return_value=0):
                commands=verify.compilation_gate(ROOT,io.StringIO(),False,False)
        self.assertEqual(commands[1]['command'],['lake','build','MonotoneOperators','EndOfPaper','Paper'])
        self.assertEqual({c['command'][-1] for c in commands[2:]},
                         {'EndSmokeTests.lean','AxiomAudit.lean','AxiomAuditEnd.lean','PaperChecks.lean'})

    def test_failed_command_history_is_retained(self):
        results=[]
        with patch('verify.shutil.which',return_value='lake'):
            with patch('verify.run_logged',side_effect=[0,23]):
                with self.assertRaises(verify.GateError):
                    verify.compilation_gate(ROOT,io.StringIO(),False,False,results)
        self.assertEqual([r['exit_code'] for r in results],[0,23])

    def test_compilation_rejects_sources_changed_during_checks(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            proof=root/'Proof.lean'
            proof.write_text('theorem original : True := by trivial',encoding='utf-8')
            def simulated_command(command,log,cwd):
                if command[-1]=='PaperChecks.lean':
                    proof.write_text('theorem changed : True := by trivial',encoding='utf-8')
                return 0
            with patch('verify.shutil.which',return_value='lake'):
                with patch('verify.run_logged',side_effect=simulated_command):
                    with self.assertRaisesRegex(verify.GateError,'changed during compilation'):
                        verify.compilation_gate(root,io.StringIO(),False,False)

    def test_refresh_preserves_review_and_pdf_pages_without_parent_aux(self):
        from copy import deepcopy
        data=verify.read_dictionary(ROOT)
        data['results'][0]['semantic_certified']=True
        data['results'][0]['release_complete']=True
        data['results'][0]['review_status']='fixture_review_status_do_not_overwrite'
        expected=deepcopy(data)
        with tempfile.TemporaryDirectory() as directory:
            target=Path(directory)/'standalone'; target.mkdir()
            for name in ('docs','manuscript','MonotoneOperators','EndOfPaper'):
                shutil.copytree(ROOT/name,target/name)
            (target/'docs/result_dictionary.json').write_text(json.dumps(data),encoding='utf-8')
            with patch.object(refresh_metadata,'ROOT',target):
                with patch('sys.stdout',new=io.StringIO()):
                    refresh_metadata.main()
            refreshed=json.loads((target/'docs/result_dictionary.json').read_text(encoding='utf-8'))
            self.assertTrue(refreshed['results'][0]['semantic_certified'])
            self.assertTrue(refreshed['results'][0]['release_complete'])
            self.assertEqual(refreshed['results'][0]['review_status'],
                             expected['results'][0]['review_status'])
            self.assertEqual([r['pdf_page'] for r in refreshed['results']],
                             [r['pdf_page'] for r in expected['results']])

    def test_unicode_supplemental_coverage_is_read_as_utf8(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'docs').mkdir()
            (root/'docs/result_dictionary.json').write_text('{"results": []}',encoding='utf-8')
            (root/'docs/supplemental_results.json').write_text(
                '[{"key":"claim:é≥", "release_complete":false}]',encoding='utf-8')
            with self.assertRaises(verify.GateError) as ctx:
                verify.coverage_gate(root)
            self.assertIn('claim:é≥',str(ctx.exception))

    def test_source_collection_keeps_nested_project_sources_and_prunes_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for file in ('Paper.lean','EndOfPaper/Nested/Proof.lean','.lake/packages/Dependency.lean','historical/Old.lean','dist/upload/Exported.lean'):
                path=root/file; path.parent.mkdir(parents=True,exist_ok=True); path.touch()
            self.assertEqual({p.relative_to(root).as_posix() for p in verify.project_lean_sources(root)},
                             {'Paper.lean','EndOfPaper/Nested/Proof.lean'})

    def test_distributable_checksums_exclude_ignored_run_artifacts(self):
        for name in ('verification/current/compile.json','historical/run.log',
                     'historical/run.olean','tools/__pycache__/verify.pyc',
                     'ReaderCheck_fixture.lean','.lake/build/File.lean'):
            self.assertTrue(refresh_checksums.generated_artifact(Path(name)),name)
        for name in ('EndOfPaper/FamilyIntegral.lean','verification/evidence/compile.json',
                     'verification/evidence/compile-output.txt','manuscript/monotone_calculus.pdf'):
            self.assertFalse(refresh_checksums.generated_artifact(Path(name)),name)

    def test_refresh_refuses_unreconciled_manuscript_without_overwriting_review(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'docs').mkdir(); (root/'manuscript').mkdir()
            path=root/'docs/result_dictionary.json'
            original=json.dumps({'manuscript':'manuscript/paper.tex',
                'manuscript_sha256':'unreconciled', 'semantic_certified':True})
            path.write_text(original,encoding='utf-8')
            (root/'manuscript/paper.tex').write_text('changed statement',encoding='utf-8')
            with patch.object(refresh_metadata,'ROOT',root):
                with self.assertRaisesRegex(ValueError,'explicitly reconcile'):
                    refresh_metadata.main()
            self.assertEqual(path.read_text(encoding='utf-8'),original)

if __name__=='__main__':
    unittest.main()
