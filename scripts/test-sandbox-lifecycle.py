#!/usr/bin/env python3
"""Organizer-controlled hostile execution, deliberately bypassing source scanning."""
import os
from pathlib import Path
import subprocess
import tempfile
from sandbox_profile import landrun_args, systemd_command
from verify_submission import ROOT, COMPARATOR, run


def main():
    lean = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    exporter = COMPARATOR / '.lake/packages/lean4export/.lake/build/bin/lean4export'
    landrun = ROOT / '.benchmark-tools/landrun/landrun'
    with tempfile.TemporaryDirectory(prefix='leansphincs-lifecycle-') as directory:
        root = Path(directory)
        output = root / '.lake/build/lib/lean/LeanSphincs/Submission'
        output.mkdir(parents=True)
        (root / '.lake/build/ir/LeanSphincs/Submission').mkdir(parents=True)
        (root / '.lake/packages').mkdir()
        (root / 'home').mkdir()
        script = root / 'hostile.py'
        script.write_text('''import os, signal, time
from pathlib import Path
root = Path('.lake/build/lib/lean/LeanSphincs/Submission')
read, write = os.pipe()
if os.fork() == 0:
    os.close(read)
    os.setsid()
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    (root / 'child.pid').write_text(str(os.getpid()))
    os.write(write, b'1')
    os.close(write)
    time.sleep(12)
    (root / 'delayed.olean').write_bytes(b'late substitution')
    os._exit(0)
os.close(write)
assert os.read(read, 1) == b'1'
os._exit(0)
''')
        command = landrun_args(landrun, root, lean, exporter,
                              ['/usr/bin/python3', str(script)], build=True)
        env = {'PATH': f'{lean}/bin:/usr/bin:/bin', 'HOME': str(root / 'home')}
        code = run(systemd_command(command, root, env, runtime_seconds=30),
                   root, dict(os.environ), root / 'lifecycle.log', timeout=45)
        pid = int((output / 'child.pid').read_text())
        proc = Path(f'/proc/{pid}/stat')
        if proc.exists() and proc.read_text().split(') ')[1].split()[0] != 'Z':
            raise RuntimeError('compiler descendant survived service cleanup')
        assert not (output / 'delayed.olean').exists()
        print(f'Strict lifecycle probe passed (service exit {code}): setsid child outlived parent, ignored TERM, was killed before delayed write.')

if __name__ == '__main__':
    main()
