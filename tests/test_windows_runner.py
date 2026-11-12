"""Exercise the native runner's evidence isolation with concurrent real processes."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile
import unittest
import uuid


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.name == 'nt' and shutil.which('powershell.exe'),
                     'requires the installed native Windows execution environment')
class WindowsRunnerLogTests(unittest.TestCase):
    def test_concurrent_checks_keep_separate_complete_logs(self):
        directory = ROOT / 'verification/current'
        directory.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='runner-log-test-', dir=directory) as tmp:
            tokens = ['RUNNER_TOKEN_' + uuid.uuid4().hex for _ in range(2)]
            processes = []
            for index, token in enumerate(tokens):
                script = Path(tmp) / f'job_{index}.py'
                script.write_text(
                    'import time\ntime.sleep(0.5)\nprint(' + repr(token) + ')\n',
                    encoding='utf-8')
                processes.append(subprocess.Popen(
                    ['powershell.exe', '-NoProfile', '-ExecutionPolicy', 'Bypass',
                     '-File', 'tools/run_windows.ps1', '-Mode', 'python',
                     '-Target', script.relative_to(ROOT).as_posix()],
                    cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, encoding='utf-8'))
            outputs = []
            try:
                for process in processes:
                    output, _ = process.communicate(timeout=180)
                    self.assertEqual(process.returncode, 0, output)
                    outputs.append(output)
            finally:
                for process in processes:
                    if process.poll() is None:
                        process.kill()
                        process.communicate()
            paths = []
            for index, output in enumerate(outputs):
                match = re.search(r'^Log: (native-python-[^\r\n]+\.log)\r?$',
                                  output, flags=re.MULTILINE)
                self.assertIsNotNone(match, output)
                path = directory / match.group(1)
                paths.append(path)
                log = path.read_text(encoding='utf-8')
                self.assertIn(tokens[index], log)
                self.assertNotIn(tokens[1-index], log)
                self.assertTrue(log.rstrip().endswith('Exit code: 0'), log)
            self.assertNotEqual(paths[0], paths[1])
            latest = (directory / 'native-python.log').read_bytes()
            self.assertIn(latest, [path.read_bytes() for path in paths])


if __name__ == '__main__':
    unittest.main()
