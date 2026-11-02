# Lean Quiet: `make install && make run` builds the desktop app and opens it.
# Linux (x86-64, X11 or XWayland; Debian, Ubuntu and their kin) today;
# macOS prints that it is not yet supported.
#
#   make install   any missing system packages (apt-get, after saying so),
#                  Lean (elan) and Rust (rustup) in your home folder, the
#                  app's assets (a pinned download), then the build
#   make run       open the app with a demo: two seeded communities, no network
#   make online    open the app with networking on, its own database
#   make check     list what make install still needs; installs nothing
#   make assets    only the app's assets
#   make verify    lake check and lake comparator (they need Lean 4.35)
#
# The build stays in this folder (.lake, out, assets). ELAN_HOME, CARGO_HOME,
# RUSTUP_HOME and TMPDIR are honoured if set; ARGS passes more arguments to
# the app.

UNAME := $(shell uname -s)
ifeq ($(UNAME),Linux)
PLATFORM := tools/make/linux.sh
else ifeq ($(UNAME),Darwin)
PLATFORM := tools/make/macos.sh
else
PLATFORM := printf 'make: Lean Quiet builds on Linux (x86-64); this is %s.\n' "$(UNAME)" >&2; false
endif

export ELAN_HOME ?= $(HOME)/.elan
export CARGO_HOME ?= $(HOME)/.cargo
export RUSTUP_HOME ?= $(HOME)/.rustup
export TMPDIR ?= /tmp

.DEFAULT_GOAL := help
.PHONY: help install run online check assets

install run online check assets:
	@$(PLATFORM) $@ $(ARGS)

# Lean's checkers, on every platform: tools/make/verify.sh says what it needs.
.PHONY: verify
verify:
	@tools/make/verify.sh

help:
	@sed -n '1,/^$$/{s/^# \{0,1\}//;p;}' Makefile
