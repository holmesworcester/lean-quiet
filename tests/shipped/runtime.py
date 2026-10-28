#!/usr/bin/env python3
"""Check the runtime artifacts actually linked, including a prebuilt control."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
out = root / 'out/phone-runtime'
toolchain = Path(subprocess.check_output(
    [Path(os.environ.get('ELAN_HOME', '/mnt/storage/elan')) / 'bin/lean', '--print-prefix'],
    cwd=root, text=True).strip())


def symbols(archive):
    return subprocess.check_output(['nm', '-g', archive], text=True, stderr=subprocess.DEVNULL)


def check_runtime(archive):
    syms = symbols(archive)
    assert not re.search(r'\bmi_\w+', syms), 'mimalloc found in runtime'
    assert not re.search(r'\b__gmp\w*', syms), 'GMP found in runtime'
    assert not re.search(r'\b(?:SSL_|OPENSSL_|X509_|BIO_)\w+', syms), 'OpenSSL found in runtime'


check_runtime(out / 'libleanrt.a')
for exe in sorted((out / 'bin').iterdir()):
    if exe.suffix:
        continue
    needed = subprocess.check_output(['readelf', '-d', exe], text=True)
    assert not re.search(r'NEEDED.*(?:leanshared|libInit|libsqlite|libgmp|libssl|libcrypto)', needed), exe
print('runtime artifacts: allocator, bignums, TLS stubs and linkage: 4 passed')

# Substituting the toolchain's runtime must be refused, even though many
# behavioral checks would still pass. Never replace a live build artifact.
with tempfile.TemporaryDirectory(prefix='runtime-nc-') as scratch:
    mutant = Path(scratch) / 'libleanrt.a'
    shutil.copyfile(toolchain / 'lib/lean/libleanrt.a', mutant)
    try:
        check_runtime(mutant)
    except AssertionError as exc:
        assert 'mimalloc' in str(exc), exc
        print('negative control: substituted prebuilt runtime rejected (mimalloc); copy discarded')
    else:
        raise AssertionError('prebuilt-runtime control survived')
