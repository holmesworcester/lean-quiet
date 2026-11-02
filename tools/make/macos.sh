#!/bin/sh
# `make install` and `make run` on macOS: not yet. The Mac app builds today
# from a Linux machine over SSH (platforms/macos/README.md, mise run
# macos:build); a native make install is still to come.
cat >&2 <<'EOF'
make: macOS is not yet supported by `make install` and `make run`.
Lean Quiet's make targets build the Linux (x86-64, X11) desktop app today.
The Mac app currently builds from a Linux machine over SSH; see
platforms/macos/README.md.
EOF
exit 1
