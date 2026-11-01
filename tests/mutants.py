"""Negative controls at once: each mutant in a copy of its own of a built
snapshot, MUTANT_JOBS (6) at once. Nothing is restored and nothing is
rebuilt after: the copy is thrown away.

    mutants.each(base, cases, one)

copies `base` (a snapshot, tests/snapshot.sh) to a sibling directory for
each case, calls `one(case, work)` there, prints what it returns, and
removes the copy. A failed assertion in any case fails the run, after
the cases already started finish. Put `base` inside the script's own
scratch directory, so that the copies are removed with it.

The box is shared: a mutant holds one of MUTANT_SLOTS (12) slots, lock
files in $TMPDIR/lean-quiet-slots that every run on the box takes from
(`slot`; shell runners use tests/slot.sh), so the box never builds more
mutants at once than that, however many runs there are."""
import concurrent.futures
import contextlib
import fcntl
import os
import pathlib
import random
import shutil
import time

SLOTS = pathlib.Path(os.environ.get("TMPDIR", "/mnt/storage/holmes-tmp")) / "lean-quiet-slots"


@contextlib.contextmanager
def slot():
    """Hold one of the box's MUTANT_SLOTS slots while the body runs."""
    n = int(os.environ.get("MUTANT_SLOTS", "12"))
    SLOTS.mkdir(parents=True, exist_ok=True)
    order = list(range(n))
    while True:
        random.shuffle(order)
        for i in order:
            f = open(SLOTS / f"{i}.lock", "a")
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                f.close()
                continue
            try:
                yield
            finally:
                fcntl.flock(f, fcntl.LOCK_UN)
                f.close()
            return
        time.sleep(0.5)


def each(base, cases, one, name=lambda case: case[0]):
    base = pathlib.Path(base)

    def go(case):
        with slot():
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
