"""Negative controls at once: each mutant in a copy of its own of a built
snapshot, MUTANT_JOBS (6) at once. Nothing is restored and nothing is
rebuilt after: the copy is thrown away.

    mutants.each(base, cases, one)

copies `base` (a snapshot, tests/snapshot.sh) to a sibling directory for
each case, calls `one(case, work)` there, prints what it returns, and
removes the copy. A failed assertion in any case fails the run, after
the cases already started finish. Put `base` inside the script's own
scratch directory, so that the copies are removed with it."""
import concurrent.futures
import os
import pathlib
import shutil


def each(base, cases, one, name=lambda case: case[0]):
    base = pathlib.Path(base)

    def go(case):
        work = base.parent / ("mutant-" + name(case))
        if work.exists():
            shutil.rmtree(work)
        shutil.copytree(base, work, symlinks=True)
        try:
            return one(case, work)
        finally:
            shutil.rmtree(work, ignore_errors=True)

    jobs = int(os.environ.get("MUTANT_JOBS", "6"))
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        for result in pool.map(go, cases):
            print(result, flush=True)
