"""Launch the existing Windows runner through a lightweight native Python host.

This avoids WSL timing out while it starts PowerShell itself. All actual Lean
and Python work still runs in the existing native Windows environment, with
the working directory, environment restoration, exit codes and logs supplied
by run_windows.ps1.
"""
from pathlib import Path
import argparse
import os
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MODES = ('environment', 'core', 'build', 'module', 'lean', 'python', 'metadata',
         'compile', 'coverage', 'fresh', 'tests', 'processes', 'lookup')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=MODES)
    parser.add_argument('target', nargs='?', default='')
    args = parser.parse_args()
    if os.name != 'nt':
        parser.error('Invoke this script with the installed native Windows python.exe.')
    powershell = Path(os.environ.get('SystemRoot', 'C:/Windows')) / (
        'System32/WindowsPowerShell/v1.0/powershell.exe')
    command = [str(powershell), '-NoProfile', '-ExecutionPolicy', 'Bypass',
               '-File', str(ROOT / 'tools/run_windows.ps1'), '-Mode', args.mode]
    if args.target:
        command += ['-Target', args.target]
    try:
        return subprocess.call(command, cwd=ROOT)
    except OSError as error:
        print(f'Native runner could not start: {error}', file=sys.stderr)
        return 127


if __name__ == '__main__':
    raise SystemExit(main())
