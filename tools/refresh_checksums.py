#!/usr/bin/env python3
"""Record distributable project files; exclude caches, credentials and run output."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
DIRECTORIES = ('MonotoneOperators', 'EndOfPaper', 'docs', 'tools', 'tests',
               'manuscript', '.github', '.vscode', 'verification')
ROOT_FILES = ('AGENTS.md', 'README.md', 'CODEX_START_HERE.md', 'END_COVERAGE.md',
              'CITATION.cff', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
              '.gitignore', '.gitattributes')


def generated_artifact(relative: Path) -> bool:
    return (any(p in {'.lake', '.elan', '__pycache__'} for p in relative.parts)
        or relative.parts[0] == 'historical'
        or (relative.parts[0] == 'verification' and relative.parts[1:2] != ('evidence',))
        or relative.suffix.lower() in {'.tex', '.bib', '.pyc', '.pyo', '.log', '.aux', '.out', '.toc', '.olean', '.ilean'}
        or relative.name in {'.DS_Store', 'Thumbs.db'}
        or (relative.name.startswith('ReaderCheck_') and relative.suffix == '.lean'))


def distributable_files(root=ROOT):
    files = {root / name for name in ROOT_FILES}
    files.update(root.glob('*.lean'))
    for directory in DIRECTORIES:
        for path in (root / directory).rglob('*'):
            relative = path.relative_to(root)
            if path.is_file() and not generated_artifact(relative):
                files.add(path)
    return sorted(path for path in files if path.is_file()
                  and not generated_artifact(path.relative_to(root)))


def main():
    lines = [hashlib.sha256(path.read_bytes()).hexdigest() + '  ' +
             path.relative_to(ROOT).as_posix() for path in distributable_files(ROOT)]
    (ROOT / 'SHA256SUMS.txt').write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
    print(f'Recorded {len(lines)} distributable file checksums. This is not a proof certificate.')


if __name__ == '__main__':
    main()
