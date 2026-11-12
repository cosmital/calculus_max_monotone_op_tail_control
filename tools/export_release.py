#!/usr/bin/env python3
"""Export a standalone GitHub-ready package with the article PDF and no TeX."""
import argparse
from pathlib import Path
import shutil
import zipfile
from refresh_checksums import ROOT, distributable_files
from verify import metadata_gate, coverage_gate


def export(destination: Path, root=ROOT):
    metadata_gate(root)
    coverage_gate(root)
    if destination.exists():
        raise ValueError('Choose a new export directory; existing files will not be overwritten.')
    paths = distributable_files(root) + [root / 'SHA256SUMS.txt']
    if any(path.suffix.lower() in {'.tex', '.bib'} for path in paths):
        raise ValueError('Private manuscript sources must not be exported.')
    for source in paths:
        target = destination / source.relative_to(root)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--zip', action='store_true', help='Also create a ZIP beside the exported directory.')
    args = parser.parse_args()
    destination = args.destination.resolve()
    archive = destination.with_suffix('.zip')
    if args.zip and archive.exists():
        parser.error('ZIP already exists; choose a new destination.')
    paths = export(destination)
    if args.zip:
        with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as stream:
            for source in paths:
                relative = source.relative_to(ROOT)
                stream.write(destination / relative, Path(destination.name) / relative)
    print(f'Exported {len(paths)} files to {destination}; no manuscript TeX or development archives included.')


if __name__ == '__main__':
    main()
