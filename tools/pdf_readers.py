"""Render the public correspondence using the submitted PDF's printed numbering."""
from pathlib import Path
import html
import json


def anchor(item):
    return 'result-' + item['number'].replace('.', '-') if 'number' in item else 'claim-' + str(item['pdf_index'])


def render(root: Path, data, extras):
    pdf = '../' + data['manuscript']
    approved = all(r.get('semantic_certified') and r.get('release_complete')
                   for r in data['results'] + extras)
    status = 'Author correspondence review recorded.' if approved else 'Author correspondence review pending.'
    intro = ['# Paper-to-Lean dictionary', '',
        f'[Article PDF for submission]({pdf}). References below use its printed result numbers and pages.', '',
        f'{len(data["results"])} numbered items and {len(extras)} supplemental claims have proof mappings. {status}', '',
        'Use the short descriptions to locate results. Full declaration mappings are in '
        '[PROOF_DETAILS.md](PROOF_DETAILS.md); unnumbered statements and equations are in '
        '[LABEL_INDEX.md](LABEL_INDEX.md). The manuscript TeX is private and is not needed to run the checks.', '',
        '| Result in the PDF | Page | Short description | Lean correspondence |',
        '|---|---:|---|---|']
    details = ['# Detailed Lean correspondence', '',
        'Result numbers and pages refer to the [submitted PDF](' + pdf + '). ' + status, '',
        'These are existing proofs and supporting declarations. Routine helpers are kept out of the main reader index.', '']
    labels = ['# Supplemental PDF claims', '',
        'These equations and unnumbered assertions supplement the numbered result dictionary. ' + status, '',
        '| Location in the PDF | Page | Short description | Lean correspondence |',
        '|---|---:|---|---|']
    rows = []
    for item in data['results'] + extras:
        page = item['pdf_page']
        link = f'{pdf}#page={page}'
        reference = item['pdf_reference']
        description = item['short_description'].replace('|', '\\|').replace('\n', ' ')
        location = f'PROOF_DETAILS.md#{anchor(item)}'
        target = intro if 'number' in item else labels
        target.append(f'| [{reference}]({link}) | {page} | {description} | [Proofs]({location}) |')
        details += [f'<a id="{anchor(item)}"></a>', '', f'## {reference}', '',
            f'[PDF page {page}]({link}). {item["short_description"]}', '', item['notes'], '',
            '| Lean declaration | Source |', '|---|---|']
        links = []
        for declaration in item['declarations']:
            source = f'../{declaration["file"]}#L{declaration["line"]}'
            details.append(f'| `{declaration["name"]}` | [{declaration["file"]}:{declaration["line"]}]({source}) |')
            links.append(f'<a href="{html.escape(source)}"><code>{html.escape(declaration["name"])}</code></a>')
        search = html.escape(json.dumps(item, ensure_ascii=False).lower(), quote=True)
        rows.append(f'<tr data-search="{search}"><td><a href="{html.escape(link)}">'
            f'{html.escape(reference)}</a><br>p. {page}</td><td>{html.escape(item["short_description"])}</td>'
            f'<td><details><summary>Lean proofs ({len(links)})</summary>' + '<br>'.join(links) + '</details></td></tr>')
    for filename, lines in [('RESULT_DICTIONARY.md', intro), ('LABEL_INDEX.md', labels), ('PROOF_DETAILS.md', details)]:
        (root / 'docs' / filename).write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
    document = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Paper-to-Lean dictionary</title>
<style>body{font:16px/1.5 system-ui;max-width:1300px;margin:30px auto;padding:20px}
table{border-collapse:collapse;width:100%}td,th{padding:12px;border-bottom:1px solid #ccc;text-align:left;vertical-align:top}
code{overflow-wrap:anywhere}input{padding:12px;width:80%}details{max-width:650px}</style>
<h1>Paper-to-Lean dictionary</h1>'''
    document += f'<p><a href="{pdf}">Article PDF for submission</a>. {status}</p>'
    document += '''<p>References use the printed PDF numbering. Existing supporting proofs are available under each result.</p>
<p><a href="RESULT_DICTIONARY.md">Numbered results</a> · <a href="LABEL_INDEX.md">Supplemental claims</a> ·
<a href="PROOF_DETAILS.md">Full correspondence</a> · <a href="LOCAL_RUN.md">Reproduction</a></p>
<input id="q" aria-label="Search results" placeholder="Result number, description or Lean declaration"><span id="count"></span>
<table><thead><tr><th>PDF result</th><th>Short description</th><th>Lean correspondence</th></tr></thead><tbody>'''
    document += '\n'.join(rows) + '''</tbody></table><script>
const q=document.getElementById('q'),rows=[...document.querySelectorAll('tbody tr')];
function filter(){let n=0;for(const r of rows){r.hidden=!r.dataset.search.includes(q.value.toLowerCase());n+=!r.hidden}
document.getElementById('count').textContent=` ${n} / ${rows.length}`}
q.addEventListener('input',filter);filter();</script></html>'''
    (root / 'docs/index.html').write_text(document, encoding='utf-8', newline='\n')
