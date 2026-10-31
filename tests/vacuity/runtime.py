"""Execute native evidence without accepting a swallowed Lean panic."""
from pathlib import Path
import subprocess


def run_checked(command, cwd, log: Path, timeout=120):
    try:
        run = subprocess.run(command, cwd=cwd, text=True, capture_output=True,
                             timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        def decoded(value):
            return value.decode(errors='replace') if isinstance(value, bytes) else value or ''
        log.write_text(decoded(exc.stdout) + decoded(exc.stderr) + '\nTIMEOUT\n')
        raise RuntimeError(f'native evidence timed out; see {log}') from exc
    log.write_text(run.stdout + run.stderr)
    if run.returncode or 'PANIC' in run.stdout + run.stderr:
        raise RuntimeError(f'native evidence failed (exit {run.returncode}); see {log}')
    return run.stdout
