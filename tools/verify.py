#!/usr/bin/env python3
"""Reproducible verification gates. Python 3.11+. No third-party packages.

--metadata checks indexing only; --compile additionally invokes Lean on ALL
supplied modules and the axiom audits; --release also requires explicit complete
coverage. Nothing in this program fills in or proves a missing theorem.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = 'leanprover/lean4:v4.19.0'
EXPECTED_MATHLIB = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
ENVIRONMENTS = 'theorem|proposition|lemma|corollary|definition|example|remark'

class GateError(RuntimeError):
    def __init__(self, message: str, code: int = 2):
        super().__init__(message)
        self.code = code


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def project_lean_sources(root: Path):
    """Include all project sources without traversing downloaded dependencies."""
    for directory, subdirectories, files in os.walk(root):
        subdirectories[:] = [name for name in subdirectories
                             if name not in {'.lake', '.git', 'historical', 'dist', '__pycache__'}]
        for name in files:
            if name.endswith('.lean'):
                yield Path(directory) / name


def strip_lean_comments_and_strings(text: str) -> str:
    """Lexical aid only, not a Lean parser. Preserve line offsets; handle nested comments."""
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2
            elif pair == '-/':
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif in_string:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  '); i += 2
            elif text[i] == '"':
                in_string = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            in_string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or in_string:
        raise GateError('Unterminated Lean comment/string found by the lexical scan.')
    return ''.join(out)


def parse_numbered_statements(text: str) -> list[dict[str, Any]]:
    """Read this paper's shared section theorem counter; not a general TeX interpreter."""
    clean = re.sub(r'(?<!\\)%[^\n]*', '', text)
    if re.search(r'\\(?:setcounter|addtocounter)\{(?:section|theorem)\}', clean):
        raise GateError('Manual theorem counter changes require updating the index parser.')
    pattern = (r'\\section(\*)?\{([^}]+)\}|\\begin\{(' + ENVIRONMENTS +
               r')\}(?:\[([^\]]*)\])?')
    section = count = 0
    section_title = ''
    result: list[dict[str, Any]] = []
    for match in re.finditer(pattern, clean):
        if match.group(2):
            section_title = match.group(2)
            if not match.group(1):
                section += 1; count = 0
            continue
        count += 1
        kind = match.group(3)
        end = clean.find('\\end{' + kind + '}', match.end())
        if end < 0:
            raise GateError('Unterminated manuscript environment: ' + kind)
        block = clean[match.start():end]
        appendix = clean.rfind('\\appendix', 0, match.start())
        if appendix >= 0:
            appendix_sections = len(re.findall(r'\\section\{', clean[appendix:match.start()]))
            section_number = chr(ord('A') + appendix_sections - 1)
        else:
            section_number = str(section)
        result.append({
            'number': f'{section_number}.{count}', 'kind': kind,
            'section': int(section_number) if section_number.isdigit() else section_number,
            'section_title': section_title,
            'line': clean.count('\n', 0, match.start()) + 1,
            'end_line': clean.count('\n', 0, end) + 1,
            'title': match.group(4) or '(untitled)',
            'labels': [x for x in re.findall(r'\\label\{([^}]+)\}', block)
                       if not x.startswith('eq:')],
        })
    return result


def read_dictionary(root: Path = ROOT) -> dict[str, Any]:
    return json.loads((root / 'docs/result_dictionary.json').read_text(encoding='utf-8'))


def canonical_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
        separators=(',', ':')).encode('utf-8')).hexdigest()


def correspondence_hash(record: dict[str, Any]) -> str:
    """Bind review to the actual claim and its declaration mapping, not status prose."""
    return canonical_hash({
        'key': record['key'], 'number': record.get('number'),
        'pdf_page': record.get('pdf_page'), 'scope': record.get('scope'),
        'statement_tex': record.get('statement_tex'),
        'conclusions': [{k: c.get(k) for k in ('id', 'statement')}
                        for c in record.get('conclusions', [])],
        'following_assertions': record.get('following_assertions', []),
        'declarations': [{k: d[k] for k in ('name', 'module', 'file')}
                         for d in record.get('declarations', [])]})


def check_pdf_correspondence(root: Path, data: dict[str, Any], version: dict[str, Any]):
    """Check a frozen PDF and the author-reviewed inventory without publishing TeX."""
    index = json.loads((root / 'docs/PDF_INDEX.json').read_text(encoding='utf-8'))
    statements = json.loads((root / 'docs/manuscript_statements.json').read_text(encoding='utf-8'))
    if canonical_hash(index) != version['pdf_index_sha256']:
        raise GateError('PDF index changed: reconcile it with the submitted PDF.')
    if canonical_hash(statements) != version['statement_inventory_sha256']:
        raise GateError('Numbered statement inventory changed since PDF reconciliation.')
    if index['pdf_sha256'] != sha256(root / data['manuscript']):
        raise GateError('PDF index identifies a different manuscript PDF.')
    extras = json.loads((root / 'docs/supplemental_results.json').read_text(encoding='utf-8'))
    items = data['results'] + extras
    if set(index['claims']) != {r['key'] for r in items}:
        raise GateError('PDF index omits or adds manuscript claims.')
    for record in items:
        entry = index['claims'][record['key']]
        if correspondence_hash(record) != entry['correspondence_sha256']:
            raise GateError('PDF claim/mapping changed: ' + record['key'])
        if not isinstance(record.get('pdf_page'), int) or not 1 <= record['pdf_page'] <= index['page_count']:
            raise GateError('Invalid PDF page for ' + record['key'])
        for key in ('pdf_page', 'pdf_reference', 'short_description'):
            if record.get(key) != entry.get(key):
                raise GateError('PDF index mismatch for ' + record['key'] + ': ' + key)
    return statements


def metadata_gate(root: Path = ROOT) -> dict[str, Any]:
    data = read_dictionary(root)
    manuscript = root / data['manuscript']
    if sha256(manuscript) != data['manuscript_sha256']:
        raise GateError('Manuscript hash differs from the dictionary: update the correspondence explicitly.')
    version = json.loads((root / 'docs/MANUSCRIPT_VERSION.json').read_text(encoding='utf-8'))
    pdf_only = data.get('artifact_format') == 'pdf'
    if pdf_only:
        parsed = check_pdf_correspondence(root, data, version)
        private_source = root / version['private_source_snapshot']
        source_text = private_source.read_text(encoding='utf-8') if private_source.exists() else None
        if source_text is not None:
            if sha256(private_source) != version['source_sha256']:
                raise GateError('Private manuscript changed since PDF reconciliation.')
            if parse_numbered_statements(source_text) != parsed:
                raise GateError('Private source and PDF statement inventory disagree.')
    else:
        source_text = manuscript.read_text(encoding='utf-8')
        parsed = parse_numbered_statements(source_text)
    records = data['results']
    if len(parsed) != len(records):
        raise GateError('A numbered manuscript statement is missing from the dictionary.')
    keys: set[str] = set()
    for expected, record in zip(parsed, records, strict=True):
        for key, value in expected.items():
            if record[key] != value:
                raise GateError(f'Dictionary mismatch for {record["key"]}: {key}')
        if record['key'] in keys:
            raise GateError('Duplicate dictionary key: ' + record['key'])
        keys.add(record['key'])
        for d in record['declarations']:
            if not re.fullmatch(r'[A-Za-z_][\w.]*', d['name']):
                raise GateError('Unexpected declaration name syntax.')
            if d['file'] != d['module'].replace('.', '/') + '.lean':
                raise GateError('Declaration/module path mismatch: ' + d['name'])
            path = root / d['file']
            if not path.is_file():
                raise GateError('Missing source file: ' + d['file'])
            lines = path.read_text(encoding='utf-8').splitlines()
            if not 1 <= d['line'] <= len(lines):
                raise GateError('Stale declaration line: ' + d['name'])
            leaf = d['name'].rsplit('.', 1)[-1]
            if not re.search(r'\b' + re.escape(leaf) + r'\b', lines[d['line']-1]):
                raise GateError('Declaration no longer found at indexed line: ' + d['name'])
    # Every mathematical module must be imported by its library root.
    module_count = 0
    for library in ('MonotoneOperators', 'EndOfPaper'):
        library_root = root / (library + '.lean')
        imported = set(re.findall(r'^import\s+(\S+)', library_root.read_text(encoding='utf-8'), re.M))
        for path in sorted((root / library).glob('*.lean')):
            module_count += 1
            module = library + '.' + path.stem
            if module not in imported:
                raise GateError('Module omitted from library root: ' + module)
            code = strip_lean_comments_and_strings(path.read_text(encoding='utf-8'))
            if re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque|partial)\b', code):
                raise GateError('Forbidden proof placeholder/declaration in ' + str(path.relative_to(root)))
    config = tomllib.loads((root / 'lakefile.toml').read_text(encoding='utf-8'))
    defaults = set(config['defaultTargets'])
    if not {'MonotoneOperators', 'EndOfPaper', 'Paper'} <= defaults:
        raise GateError('Default build omits a required library.')
    mathlib = next(x for x in config['require'] if x['name'] == 'mathlib')
    if mathlib['rev'] != EXPECTED_MATHLIB:
        raise GateError('Mathlib revision differs from the audited pin.')
    if (root / 'lean-toolchain').read_text(encoding='utf-8').strip() != EXPECTED_TOOLCHAIN:
        raise GateError('Lean toolchain differs from the audited pin.')
    # Supplemental unnumbered claims are tracked separately and also block release.
    supplement = json.loads((root / 'docs/supplemental_results.json').read_text(encoding='utf-8'))
    if not supplement:
        raise GateError('Supplemental result inventory is empty.')
    for item in supplement:
        if source_text is not None and item['label'] and ('\\label{' + item['label'] + '}') not in source_text:
            raise GateError('Supplemental label absent from manuscript: ' + item['label'])
    # Helpers and newly added declarations must remain navigable too.
    inventory = json.loads((root / 'docs/declarations.json').read_text(encoding='utf-8'))
    inventory_names = set()
    for declaration in inventory:
        path = root / declaration['file']
        lines = path.read_text(encoding='utf-8').splitlines()
        line = declaration['line']
        leaf = declaration['name'].rsplit('.', 1)[-1]
        if not 1 <= line <= len(lines) or not re.search(r'\b' + re.escape(leaf), lines[line-1]):
            raise GateError('Stale declaration inventory location: ' + declaration['name'])
        if declaration['name'] in inventory_names:
            raise GateError('Duplicate declaration inventory entry: ' + declaration['name'])
        inventory_names.add(declaration['name'])
    for record in records:
        for declaration in record['declarations']:
            if declaration['name'] not in inventory_names:
                raise GateError('Mapped declaration omitted from inventory: ' + declaration['name'])
    statements = json.loads((root / 'docs/manuscript_statements.json').read_text(encoding='utf-8'))
    if statements != parsed:
        raise GateError('Standalone manuscript statement inventory is stale.')
    if not pdf_only and version['source_sha256'] != sha256(manuscript):
        raise GateError('Version manifest and manuscript snapshot disagree.')
    if version.get('pdf_snapshot') and sha256(root / version['pdf_snapshot']) != version['pdf_sha256']:
        raise GateError('PDF snapshot differs from the recorded manuscript version.')
    authoritative = root / version['source']
    if authoritative.exists() and sha256(authoritative) != version['source_sha256']:
        raise GateError('Parent manuscript changed since the correspondence review.')
    return {'status': 'METADATA_ONLY_OK', 'numbered_items': len(records),
            'supplemental_items': len(supplement), 'source_modules': module_count,
            'note': 'No mathematical proof is validated by this metadata gate.'}


def coverage_state(root: Path = ROOT) -> dict[str, Any]:
    """Describe proof mappings and human review separately; certify neither."""
    records = read_dictionary(root)['results']
    extras = json.loads((root / 'docs/supplemental_results.json').read_text(encoding='utf-8'))
    state: dict[str, Any] = {}
    for name, items in (('numbered', records), ('supplemental', extras)):
        groups: dict[str, list[str]] = {}
        for item in items:
            groups.setdefault(item.get('scope', 'missing'), []).append(item['key'])
        state[name + '_scope_groups'] = groups
        state[name + '_proof_mapping_pending'] = [r['key'] for r in items
            if r.get('scope') != 'complete' or not r.get('declarations')]
        state[name + '_author_review_pending'] = [r['key'] for r in items
            if not r.get('semantic_certified') or not r.get('release_complete')]
    return state


def coverage_gate(root: Path = ROOT) -> dict[str, Any]:
    """A manually maintained correspondence gate, NOT an automated semantic proof."""
    state = coverage_state(root)
    proofs = state['numbered_proof_mapping_pending'] + state['supplemental_proof_mapping_pending']
    reviews = state['numbered_author_review_pending'] + state['supplemental_author_review_pending']
    if proofs or reviews:
        raise GateError('WHOLE-PAPER RELEASE BLOCKED.\n'
            'Full proof correspondence not established: ' + (', '.join(proofs) or 'none') + '\n'
            'Author semantic/release review pending: ' + (', '.join(reviews) or 'none'), 2)
    data = read_dictionary(root)
    if data.get('artifact_format') == 'pdf':
        review = json.loads((root / 'docs/AUTHOR_REVIEW.json').read_text(encoding='utf-8'))
        if review['pdf_sha256'] != sha256(root / data['manuscript']):
            raise GateError('Author review identifies a different PDF.')
        extras = json.loads((root / 'docs/supplemental_results.json').read_text(encoding='utf-8'))
        items = data['results'] + extras
        if review['claims'] != {r['key']: correspondence_hash(r) for r in items}:
            raise GateError('Author-reviewed correspondence changed.')
        sources = {p.relative_to(root).as_posix(): sha256(p)
            for library in ('MonotoneOperators', 'EndOfPaper')
            for p in (root / library).glob('*.lean')}
        sources.update({p.name: sha256(p) for p in root.glob('*.lean')
                        if not p.name.startswith('ReaderCheck_')})
        if sources != review['lean_source_sha256']:
            raise GateError('Lean sources changed since author correspondence review.')
    return {'status': 'COVERAGE_REVIEW_RECORDED',
            'note': 'This records human semantic review; it does not mechanize that review.'}


def run_logged(command: list[str], log, root: Path = ROOT) -> int:
    line = '$ ' + ' '.join(command)
    print(line, flush=True); log.write(line + '\n'); log.flush()
    process = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace')
    assert process.stdout is not None
    for output in process.stdout:
        print(output, end='', flush=True); log.write(output); log.flush()
    return process.wait()


def compilation_gate(root: Path, log, fresh: bool, fetch_cache: bool,
                     results: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    lake = shutil.which('lake')
    if lake is None:
        raise GateError('NOT COMPILED: Lake/Lean executable unavailable. No Lean process was started.', 127)
    source_before = {f.relative_to(root).as_posix(): sha256(f)
                     for f in project_lean_sources(root)}
    if fresh:
        build_dir = root / '.lake/build'
        if build_dir.is_symlink():
            raise GateError('Refusing to remove a symlinked build directory.')
        if build_dir.exists():
            shutil.rmtree(build_dir)  # Generated project build files only; dependencies remain.
    commands = [[lake, 'env', 'lean', '--version']]
    if fetch_cache:
        commands.append([lake, 'exe', 'cache', 'get'])
    commands += [
        [lake, 'build', 'MonotoneOperators', 'EndOfPaper', 'Paper'],
        [lake, 'env', 'lean', 'EndSmokeTests.lean'],
        [lake, 'env', 'lean', 'AxiomAudit.lean'],
        [lake, 'env', 'lean', 'AxiomAuditEnd.lean'],
        [lake, 'env', 'lean', 'PaperChecks.lean'],
    ]
    if results is None:
        results = []
    for command in commands:
        code = run_logged(command, log, root)
        results.append({'command': command, 'exit_code': code})
        log.write(f'Exit code: {code}\n'); log.flush()
        if code:
            raise GateError('Lean/build command failed; see the log. No verification success is recorded.', code)
    source_after = {f.relative_to(root).as_posix(): sha256(f)
                    for f in project_lean_sources(root)}
    if source_before != source_after:
        changed = sorted(name for name in source_before.keys() | source_after.keys()
                         if source_before.get(name) != source_after.get(name))
        raise GateError('Lean sources changed during compilation; rerun the gate: ' + ', '.join(changed))
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--metadata', action='store_true')
    modes.add_argument('--coverage', action='store_true')
    modes.add_argument('--compile', action='store_true')
    modes.add_argument('--release', action='store_true')
    parser.add_argument('--fresh', action='store_true', help='Remove only generated local project build files before compiling.')
    parser.add_argument('--fetch-cache', action='store_true', help='Request official Mathlib cache before compiling.')
    args = parser.parse_args()
    mode = next(k for k in ('metadata','coverage','compile','release') if getattr(args, k))
    output = ROOT / 'verification/current'
    output.mkdir(parents=True, exist_ok=True)
    report: dict[str, Any] = {'mode': mode, 'started_utc': datetime.now(timezone.utc).isoformat(),
                              'status': 'NOT_COMPLETED', 'lean_compiled': False,
                              'whole_paper_verified': False}
    status_file = output / (mode + '.json')
    log_file = output / (mode + '.log')
    status_file.write_text(json.dumps(report, indent=2) + '\n')  # invalidate a stale success first
    exit_code = 0
    with log_file.open('w', encoding='utf-8') as log:
        try:
            report['metadata'] = metadata_gate()
            print(report['metadata']['status'])
            if mode in ('compile', 'release'):
                report['commands'] = []
                compilation_gate(ROOT, log, args.fresh, args.fetch_cache, report['commands'])
                report['lean_compiled'] = True
            if mode in ('coverage', 'release'):
                report['coverage_review_state'] = coverage_state()
                report['coverage'] = coverage_gate()
            report['status'] = {'metadata':'METADATA_ONLY_OK', 'coverage':'COVERAGE_REVIEW_RECORDED',
                                'compile':'SUPPLIED_DECLARATIONS_ACCEPTED',
                                'release':'BUILD_AND_RECORDED_COVERAGE_ACCEPTED'}[mode]
            if mode == 'release':
                report['whole_paper_verified'] = True
                report['semantic_caveat'] = 'Correspondence still relies on the explicit human review recorded in the dictionary.'
            print(report['status']); log.write(report['status'] + '\n')
        except (GateError, OSError, ValueError, KeyError, StopIteration) as error:
            exit_code = error.code if isinstance(error, GateError) else 2
            report['status'] = 'BLOCKED' if exit_code in (2,127) else 'FAILED'
            report['error'] = str(error)
            print(str(error), file=sys.stderr); log.write(str(error) + '\n')
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    report['exit_code'] = exit_code
    report['manuscript_sha256'] = sha256(ROOT / read_dictionary()['manuscript'])
    report['source_sha256'] = {f.relative_to(ROOT).as_posix(): sha256(f)
        for f in sorted(project_lean_sources(ROOT))}
    status_file.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return exit_code

if __name__ == '__main__':
    raise SystemExit(main())
