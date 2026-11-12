#!/usr/bin/env python3
"""Locate a paper result. --check builds and inspects existing declarations, not missing claims."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from verify import ROOT, GateError, metadata_gate, read_dictionary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('query', help='Printed PDF result number, description, stable key or Lean declaration fragment')
    parser.add_argument('--check', action='store_true', help='Build necessary modules; show types and axiom dependencies')
    args = parser.parse_args()
    try:
        metadata_gate()
    except GateError as error:
        print(error, file=sys.stderr); return error.code
    records = read_dictionary()['results']
    supplemental = json.loads((ROOT / 'docs/supplemental_results.json').read_text(encoding='utf-8'))
    records += [dict(r, kind='supplemental claim', number='unnumbered',
        labels=[r['label']] if r.get('label') else [], all_labels=[],
        declarations=r.get('declarations', []), compiler_evidence=r.get('compiler_evidence', 'none'),
        line=r.get('line', 'see claim inventory')) for r in supplemental]
    exact = [r for r in records if args.query in [r['key'], r['number'], *r['labels'], *r['all_labels']]]
    selected = exact or [r for r in records if args.query.lower() in json.dumps(r,ensure_ascii=False).lower()]
    if not selected:
        print('No result found. Check docs/LABEL_INDEX.md for active labels.', file=sys.stderr)
        return 2
    for result in selected:
        print(f"\n{result['kind'].capitalize()} {result['number']}: {result['title']}")
        print(f"Key: {result['key']}\nCoverage: {result['scope']}\nCompiler evidence: {result['compiler_evidence']}")
        print(f"PDF: {read_dictionary()['manuscript']}#page={result.get('pdf_page', 1)}")
        print(result['notes'])
        for declaration in result['declarations']:
            print(f"  {declaration['name']}\n    {declaration['file']}:{declaration['line']}")
    if not args.check:
        return 0
    if len(selected) != 1:
        print('--check requires one exact result label/number.',file=sys.stderr);return 2
    declarations = selected[0]['declarations']
    if not declarations:
        print('NOT CHECKABLE: no proof script for this result. Nothing was sent to Lean.', file=sys.stderr)
        return 2
    lake = shutil.which('lake')
    if lake is None:
        print('NOT COMPILED: Lake/Lean executable unavailable.', file=sys.stderr); return 127
    modules = sorted({d['module'] for d in declarations})
    command = [lake, 'build', *modules]
    print('$ ' + ' '.join(command), flush=True)
    code = subprocess.call(command, cwd=ROOT)
    if code:
        return code
    source = '\n'.join('import '+m for m in modules)+'\n\n'
    source += 'set_option pp.universes true\n'
    for d in declarations:
        source += '#check '+d['name']+'\n#print axioms '+d['name']+'\n'
    with tempfile.NamedTemporaryFile('w',suffix='.lean',prefix='ReaderCheck_',dir=ROOT,delete=False,encoding='utf-8') as stream:
        stream.write(source); path=Path(stream.name)
    try:
        code=subprocess.call([lake,'env','lean',str(path)],cwd=ROOT)
    finally:
        path.unlink(missing_ok=True)
    print('This inspection does not certify a partial/missing manuscript result as complete.')
    return code

if __name__=='__main__':
    raise SystemExit(main())
