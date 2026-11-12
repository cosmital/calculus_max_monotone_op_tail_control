"""Check exact modular proof bodies against a successful combined Lean check.

This is staging evidence only. The installed modules, their dependents,
independent readers and complete axiom audits must still pass normally.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
from verify import strip_lean_comments_and_strings


def compose_packet(sources, readers=()):
    sources = list(sources)
    names = [p.stem for p in sources]
    if len(set(names)) != len(names):
        raise ValueError('Duplicate module in proof packet')
    imports, bodies, seen = [], [], set()
    for source in sources:
        raw = source.read_text(encoding='utf-8')
        code = strip_lean_comments_and_strings(raw)
        if re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque|partial|native_decide)\b', code):
            raise ValueError('Forbidden proof token in packet: '+source.name)
        body, header = [], True
        for line in raw.splitlines():
            if header and line.startswith('import '):
                parts = line.split()
                if len(parts) != 2:
                    raise ValueError('Packet imports must use one module per line')
                imported = parts[1].removeprefix('EndOfPaper.')
                if parts[1].startswith('EndOfPaper.') and imported in names:
                    if imported not in seen:
                        raise ValueError('Packet dependency must precede its user: '+imported)
                elif line not in imports:
                    imports.append(line)
            else:
                body.append(line)
                if line.strip():
                    header = False
        bodies.append('\n'.join(body))
        seen.add(source.stem)
    for reader in readers:
        raw = reader.read_text(encoding='utf-8')
        code = strip_lean_comments_and_strings(raw)
        if re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque|partial|native_decide)\b', code):
            raise ValueError('Forbidden proof token in packet reader: '+reader.name)
        bodies.append(raw)
    return '\n'.join(imports)+'\n\n'+'\n\n'.join(bodies)+'\n'


def validate_checked_packet(root, packet):
    root = Path(root).resolve()

    def local(name):
        path = (root/name).resolve()
        path.relative_to(root)
        return path

    sources = [local(name) for name in packet['sources']]
    readers = [local(name) for name in packet.get('readers', [])]
    bundle = local(packet['file'])
    files = sources+readers
    actual = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    if actual != packet['source_sha256']:
        raise ValueError('Checked packet source hashes differ')
    manifest = bundle.with_suffix('.sources.json')
    if json.loads(manifest.read_text(encoding='utf-8')) != actual:
        raise ValueError('Packet pre-check source manifest differs')
    if compose_packet(sources, readers) != bundle.read_text(encoding='utf-8'):
        raise ValueError('Checked packet is not the exact ordered modular bodies and readers')
    log = local(packet['log'])
    text = log.read_text(encoding='utf-8')
    command = ' env lean '+bundle.relative_to(root).as_posix()
    if command not in text.splitlines()[0] or not text.rstrip().endswith('Exit code: 0'):
        raise ValueError('No successful Lean check of this exact packet')
    match = re.fullmatch(r'native-lean-(\d{8}T\d{9,12})-[a-f0-9]+\.log', log.name)
    if not match:
        raise ValueError('Expected an actual uniquely named native Lean receipt')
    started = datetime.strptime(match[1], '%Y%m%dT%H%M%S%f').replace(tzinfo=timezone.utc).timestamp()
    if started < max(p.stat().st_mtime for p in files+[bundle,manifest]):
        raise ValueError('Packet sources changed after the recorded check started')
    return {p.stem for p in sources}
