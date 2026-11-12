#!/usr/bin/env python3
"""Refresh locations and render existing reviews; never grant semantic approval."""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
import hashlib
import html
import json
import re
from pathlib import Path
from verify import ROOT, parse_numbered_statements, strip_lean_comments_and_strings, check_pdf_correspondence


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def write(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')


def staged_declaration_names(source):
    """Read the public declaration kinds supported by the reader inventory."""
    code = strip_lean_comments_and_strings(source)
    return re.findall(r'^\s*(?:@\[[^]]+\]\s*)?(?:def|theorem|lemma|abbrev|structure)\s+([\w\'.]+)',
        code, flags=re.MULTILINE)


@lru_cache(maxsize=128)
def source_locations(path, modified_ns, size):
    """Scan each unchanged module once, including when many declarations map to it."""
    code = strip_lean_comments_and_strings(path.read_text(encoding='utf-8'))
    locations = {}
    for i, line in enumerate(code.splitlines(), 1):
        match = re.search(r'\b(?:def|theorem|lemma|abbrev|structure|class|instance)\s+([\w\'.]+)', line)
        if match:
            locations.setdefault(match[1].rsplit('.', 1)[-1], []).append(i)
    return locations


def relocate(declaration):
    path = ROOT / declaration['file']
    stat = path.stat()
    leaf = declaration['name'].rsplit('.', 1)[-1]
    candidates = source_locations(path, stat.st_mtime_ns, stat.st_size).get(leaf, [])
    if len(candidates) == 1:
        declaration['line'] = candidates[0]
    elif declaration['line'] not in candidates:
        raise ValueError(f'Ambiguous/missing source declaration: {declaration["name"]}')
    return declaration


def render(data, extras):
    lines = ['# Paper-to-Lean dictionary', '',
        ('**All current manuscript claims have agent-reviewed proof mappings. Human semantic approval is pending.**'
         if all(r.get('scope')=='complete' for r in data['results']+extras) else
         '**Incomplete formalization. Human semantic approval is pending.**'), '',
        f"Current manuscript: `{data['manuscript']}`; SHA-256 `{data['manuscript_sha256']}`.", '',
        f"{len(data['results'])} numbered items; {len(extras)} supplemental claims. "
        'Compilation and mathematical correspondence are separate checks. '
        'Read `CODEX_PROGRESS.md` for current command outcomes.', '',
        'The `inherited_mapping` category is a candidate correspondence awaiting review; '
        '`partial_source` supplies only the described ingredients; `missing` has no proof mapping. '
        'None of these categories certifies the full statement.', '',
        '| Paper | Stable key | Result | Coverage |', '|---|---|---|---|']
    rows = []
    sections = []
    for r in data['results']:
        lines.append(f"| {r['number']} | `{r['key']}` | {r['title']} | {r['scope']} |")
        source = f"../{data['manuscript']}#L{r['line']}"
        details = [f"## {r['number']}: {r['title']}", '',
            f"**Key:** `{r['key']}`. **Scope:** {r['scope']}. "
            f"**PDF page:** {r.get('pdf_page', 'unavailable')}.", '',
            f"[Manuscript line {r['line']}]({source}).", '', r['notes'], '',
            f"Compiler evidence: {r['compiler_evidence']}. "
            'Human semantic approval: ' + ('recorded.' if r['semantic_certified'] else 'pending.'), '',
            '| Lean declaration | Module/source location |', '|---|---|']
        links = []
        for d in r['declarations']:
            link = f"../{d['file']}#L{d['line']}"
            details.append(f"| `{d['name']}` | [{d['file']}:{d['line']}]({link}) |")
            links.append(f'<a href="{html.escape(link)}"><code>{html.escape(d["name"])}</code></a>')
        if not links:
            details.append('| — | No corresponding declaration |')
        if r.get('conclusions'):
            details += ['', 'Separate conclusions requiring correspondence:', '']
            details += [f"- `{claim['id']}`: {claim['statement']} ({claim['status']})."
                        for claim in r['conclusions']]
        sections += ['', *details]
        rows.append('<tr data-search="' + html.escape(json.dumps(r).lower(), quote=True) + '">'
            + f'<td>{r["number"]}<br>p. {r.get("pdf_page", "?")}</td>'
            + f'<td><a href="{source}">{html.escape(r["title"])}</a><br>'
            + f'<code>{html.escape(r["key"])}</code><p>{html.escape(r["notes"])}</p></td>'
            + f'<td>{r["scope"]}<br>{html.escape(r["compiler_evidence"])}</td>'
            + '<td>' + '<br>'.join(links) + '</td></tr>')
    (ROOT / 'docs/RESULT_DICTIONARY.md').write_text('\n'.join(lines + sections) + '\n', encoding='utf-8')
    for e in extras:
        links = [f'<a href="../{html.escape(d["file"])}#L{d["line"]}"><code>{html.escape(d["name"])}</code></a>'
                 for d in e.get('declarations', [])]
        location = (f'<a href="../{data["manuscript"]}#L{e["line"]}">line {e["line"]}</a>'
                    if e.get('line') else 'source location pending')
        rows.append('<tr data-search="' + html.escape(json.dumps(e).lower(), quote=True) + '">'
            + f'<td>Supplemental<br>p. {e.get("pdf_page", "?")}</td>'
            + f'<td><strong>{html.escape(e["title"])}</strong><br><code>{html.escape(e["key"])}</code>'
            + f'<p>{html.escape(e["notes"])}</p>{location}</td>'
            + f'<td>{e["scope"]}<br>{html.escape(e.get("compiler_evidence", "none"))}</td>'
            + '<td>' + ('<br>'.join(links) or 'No corresponding declaration') + '</td></tr>')
    document = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Proof dictionary</title>
<style>body{font:16px/1.5 system-ui;margin:30px auto;max-width:1400px;padding:20px}
table{border-collapse:collapse;width:100%}td,th{padding:12px;border-bottom:1px solid #ccc;
text-align:left;vertical-align:top}code{overflow-wrap:anywhere}input{padding:12px;width:80%}</style>
<h1>Paper-to-Lean dictionary</h1><p><strong>Incomplete. Semantic approval pending.</strong>
See CODEX_PROGRESS.md for compiler evidence. This index is not a proof certificate.</p>
<p><a href="RESULT_DICTIONARY.md">Markdown</a> · <a href="result_dictionary.json">JSON</a> ·
<a href="LABEL_INDEX.md">Supplemental claims</a> · <a href="LOCAL_RUN.md">Reproduction</a></p>
<input id="q" aria-label="Search results" placeholder="Label, number, title, declaration"><span id="count"></span>
<table><thead><tr><th>Paper</th><th>Statement and qualification</th><th>Coverage</th><th>Lean</th></tr></thead><tbody>
'''
    document += '\n'.join(rows) + '''</tbody></table><script>
const q=document.getElementById('q'),rows=[...document.querySelectorAll('tbody tr')];
function filter(){let n=0;for(const r of rows){r.hidden=!r.dataset.search.includes(q.value.toLowerCase());n+=!r.hidden}
document.getElementById('count').textContent=` ${n} / ${rows.length}`}
q.addEventListener('input',filter);filter();</script></html>'''
    (ROOT / 'docs/index.html').write_text(document, encoding='utf-8')


def main():
    data = read(ROOT / 'docs/result_dictionary.json')
    manuscript = ROOT / data['manuscript']
    if hashlib.sha256(manuscript.read_bytes()).hexdigest() != data['manuscript_sha256']:
        raise ValueError('Manuscript changed: explicitly reconcile and archive the correspondence before refreshing locations.')
    if data.get('artifact_format') == 'pdf':
        extras = read(ROOT / 'docs/supplemental_results.json')
        check_pdf_correspondence(ROOT, data, read(ROOT / 'docs/MANUSCRIPT_VERSION.json'))
        for item in data['results'] + extras:
            item['declarations'] = [relocate(dict(d)) for d in item['declarations']]
        inventory = [relocate(dict(d)) for d in read(ROOT / 'docs/declarations.json')]
        write(ROOT / 'docs/result_dictionary.json', data)
        write(ROOT / 'docs/supplemental_results.json', extras)
        write(ROOT / 'docs/declarations.json', inventory)
        from pdf_readers import render as render_pdf
        render_pdf(ROOT, data, extras)
        print(f"Rendered {len(data['results'])} numbered PDF results and {len(extras)} supplemental claims; review preserved.")
        return
    text = manuscript.read_text(encoding='utf-8')
    clean = re.sub(r'(?<!\\)%[^\n]*', '', text)
    parsed = parse_numbered_statements(text)
    old_records = data['results']
    aliases = {'prop:pointwisemaximality': 'prop:fibers',
               'lem:resolventvalue': 'lem:resolventfiber',
               'prop:finitevalues': 'prop:finitefibers'}
    old_by_label = {label: r for r in old_records for label in r['labels']}
    old_by_key = {r['key']: r for r in old_records}
    aux = ROOT.parent / 'build/monotone_calculus.aux'
    aux_text = aux.read_text(encoding='utf-8') if aux.exists() else ''
    pages = {m[1]: (m[2], int(m[3])) for m in re.finditer(
        r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{(\d+)\}', aux_text)}
    records = []
    for parsed_item in parsed:
        r = dict(parsed_item)
        block = '\n'.join(clean.splitlines()[r['line']-1:r['end_line']])
        labels = re.findall(r'\\label\{([^}]+)\}', block)
        r['all_labels'] = labels
        key = r['labels'][0] if r['labels'] else (
            'statement:1.1' if r['number'] == '1.1' else
            r['kind'] + ':' + re.sub(r'[^a-z0-9]+', '_', r['title'].lower()).strip('_'))
        previous = old_by_key.get(key) or next((old_by_label.get(aliases.get(label, label))
            for label in r['labels'] if aliases.get(label, label) in old_by_label), None)
        if previous:
            r = {**previous, **r}
        else:
            r.update(scope='missing', declarations=[],
                notes='No faithful full-statement Lean counterpart has been established.',
                compiler_evidence='none', semantic_certified=False, release_complete=False)
        r['key'] = key
        r['statement_tex'] = block
        r['statement_sha256'] = hashlib.sha256(block.encode()).hexdigest()
        r.setdefault('review_status', 'pending_current_manuscript_review')
        r['declarations'] = [relocate(dict(d)) for d in r['declarations']]
        r['pdf_page'] = next((pages[label][1] for label in labels if label in pages), r.get('pdf_page'))
        if r['pdf_page'] is None and r['number'] == '1.1':
            r['pdf_page'] = 4
        for label in r['labels']:
            if label in pages and pages[label][0] != r['number']:
                raise ValueError(f'Source/PDF numbering mismatch: {label}')
        records.append(r)
    data.update(results=records, manuscript_sha256=hashlib.sha256(manuscript.read_bytes()).hexdigest(),
        summary=dict(Counter(r['scope'] for r in records)), release_status='INCOMPLETE',
        numbering='Current TeX shared section counter, including appendix letters; checked against current AUX/PDF labels.')
    extras = read(ROOT / 'docs/supplemental_results.json')
    active_labels = set(re.findall(r'\\label\{([^}]+)\}', clean))
    removed = [e['key'] for e in extras if e.get('label') and e['label'] not in active_labels]
    if removed:
        raise ValueError('Archive and explicitly reconcile removed supplemental claims: ' + ', '.join(removed))
    tracked = {e['label'] for e in extras}
    for match in re.finditer(r'\\label\{(eq:[^}]+)\}', clean):
        label = match[1]
        line = clean.count('\n', 0, match.start()) + 1
        if label in tracked or any(r['line'] <= line <= r['end_line'] for r in records):
            continue
        extras.append(dict(key=label, label=label, title=label, scope='missing',
            notes='Standalone mathematical assertion; full correspondence pending.', release_complete=False))
    for e in extras:
        e['declarations'] = [relocate(dict(d)) for d in e.get('declarations', [])]
        if e.get('label'):
            match = re.search(r'\\label\{' + re.escape(e['label']) + r'\}', clean)
            e['line'] = clean.count('\n', 0, match.start()) + 1
            e['pdf_page'] = pages.get(e['label'], (None, e.get('pdf_page')))[1]
        elif e.get('source_anchor'):
            index = clean.find(e['source_anchor'])
            if index < 0:
                raise ValueError('Supplemental source anchor disappeared: ' + e['key'])
            e['line'] = clean.count('\n', 0, index) + 1
    write(ROOT / 'docs/result_dictionary.json', data)
    write(ROOT / 'docs/manuscript_statements.json', parsed)
    write(ROOT / 'docs/supplemental_results.json', extras)
    inventory = [relocate(d) for d in read(ROOT / 'docs/declarations.json')]
    indexed_names = {d['name'] for d in inventory}
    for path in sorted((ROOT / 'EndOfPaper').glob('*.lean')):
        code = strip_lean_comments_and_strings(path.read_text(encoding='utf-8'))
        namespace = re.search(r'^namespace\s+(\S+)', code, re.M)[1]
        for i, line in enumerate(code.splitlines(), 1):
            match = re.search(r'^\s*(?:@\[[^]]+\]\s*)?(def|theorem|lemma|abbrev|structure)\s+([\w\'.]+)', line)
            if match:
                name = namespace + '.' + match[2]
                if name not in indexed_names:
                    inventory.append(dict(name=name, kind=match[1], line=i,
                        file=path.relative_to(ROOT).as_posix(),
                        module='EndOfPaper.' + path.stem, validation='awaiting_current_compile'))
                    indexed_names.add(name)
    write(ROOT / 'docs/declarations.json', inventory)
    write(ROOT / 'docs/current_source_hashes.json', {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for library in ('MonotoneOperators', 'EndOfPaper')
        for path in sorted((ROOT / library).glob('*.lean'))})
    render(data, extras)
    lines = ['# Active manuscript labels and supplemental claims', '',
        'Locations identify assertions, not completed proof mappings.', '',
        '| Label | Source line | PDF page | Numbered owner |', '|---|---|---|---|']
    for match in re.finditer(r'\\label\{([^}]+)\}', clean):
        label = match[1]
        line = clean.count('\n', 0, match.start()) + 1
        owner = next((r['number'] for r in records if r['line'] <= line <= r['end_line']), '—')
        lines.append(f'| `{label}` | [line {line}](../manuscript/monotone_calculus.tex#L{line}) '
                     f'| {pages.get(label, (None, None))[1]} | {owner} |')
    lines += ['', '## Supplemental claims', '', '| Key | Claim | Source / PDF page | Coverage/qualification |', '|---|---|---|---|']
    for e in extras:
        source = (f"[line {e['line']}](../manuscript/monotone_calculus.tex#L{e['line']})"
                  if e.get('line') else 'pending')
        lines.append(f"| `{e['key']}` | {e['title']} | {source}; p. {e.get('pdf_page')} | {e['scope']}: {e['notes']} |")
    for e in extras:
        if not e.get('declarations'):
            continue
        lines += ['', f"## {e['key']}: {e['title']}", '', e['notes'], '',
            'Compiler evidence: ' + e.get('compiler_evidence', 'none') + '.', '',
            '| Lean declaration | Module/source location |', '|---|---|']
        for d in e['declarations']:
            lines.append(f"| `{d['name']}` | [{d['file']}:{d['line']}](../{d['file']}#L{d['line']}) |")
    (ROOT / 'docs/LABEL_INDEX.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    print(f"Indexed {len(records)} numbered items, {len(extras)} supplemental claims, {len(inventory)} declarations.")


if __name__ == '__main__':
    main()
