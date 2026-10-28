#!/usr/bin/env bash
# Cross-checks with independent implementations (tools/xcheck/xcheck.py):
# qrencode -> Lean, Lean -> zbarimg, segno -> Lean, Lean == qrencode and
# qrcodegen module for module; and QOI against Pillow (tools/xcheck/qoi.py). Tools come from PATH (and Python's path),
# else from out/xtools, which tools/xcheck/fetch.sh fills without root; a
# tool still missing is skipped and said so.
set -euo pipefail
cd "$(dirname "$0")/.."
x=out/xtools
have() { command -v "$1" >/dev/null 2>&1 || [ -x "$x/root/usr/bin/$1" ]; }
pyhas() { python3 -c "import $1" 2>/dev/null || [ -e "$x/py/$1" ] || [ -e "$x/py/$1.py" ]; }
if ! have qrencode || ! have zbarimg || ! pyhas segno || ! pyhas qrcodegen; then
  tools/xcheck/fetch.sh >/dev/null 2>&1 || echo "note: tools/xcheck/fetch.sh could not fetch everything"
fi
tool() { command -v "$1" 2>/dev/null || { [ -x "$x/root/usr/bin/$1" ] && echo "$x/root/usr/bin/$1"; } || true; }
pydir() {  # the directory to import $1 from
  python3 -c "import $1, os; f = $1.__file__; print(os.path.dirname(os.path.dirname(f)) if f.endswith('__init__.py') else os.path.dirname(f))" 2>/dev/null ||
    { { [ -e "$x/py/$1" ] || [ -e "$x/py/$1.py" ]; } && echo "$x/py"; } || true
}
args=()
for t in qrencode zbarimg; do
  p=$(tool $t); [ -n "$p" ] && args+=(--$t "$p") || echo "SKIP $t: not installed"
done
for m in segno qrcodegen; do
  d=$(pydir $m); [ -n "$d" ] && args+=(--$m "$d") || echo "SKIP $m: not installed"
done
python3 tools/xcheck/xcheck.py .lake/build/bin/qr_tool out/xcheck "${args[@]}"
# QOI, the composer's storage format, against Pillow's codec
python3 tools/xcheck/qoi.py .lake/build/bin/qr_tool out/xcheck/qoi
