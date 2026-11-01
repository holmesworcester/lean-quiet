# Desktop publication receipts

The desktop driver now stages App layers without claiming completion.
`DesktopMain` calls `Desktop.publish` around the actual native frame call.
The wrapper qualifies the final composed content band, including hover paint
and decoded photo previews; a popup covering that band cannot acknowledge it.
One tracked callback candidate remains owned while newer untracked redraws and
input continue. Refused geometry discards stale positional input and cancels
its gesture, while text, keys and close remain usable.

Linux acknowledges checked drawing requests plus a server round trip and current
map/geometry queries. Input pressure cannot make cached Map/Configure state
suffice. Windows checks GDI drawing/flush and current visibility/geometry.
Mac uses a single tracked CATransaction callback; reset, focus or translation
can invalidate its receipt without losing callback ownership. These receipts
mean native API completion, not physical display scanout.

The named `host:desktop` gate passed again in the integrated worktree with 292 existing checks and 27 renders,
four hover proof controls, 20 actual App/SQLite/publication checks and nine
compiled controls with a restored positive run. Cases cover delayed/refused
completion, accepted untracked redraws, stale positional input, covered body,
actual hover, photo-only sends and signed reaction changes during a delayed
callback. `linux:e2e` passed 45 native-input checks, 28 presentation checks in
each of MIT-SHM and PutImage modes, and the existing 84 checks in three Xvfb
sessions. The integrated full proof gate, README inventory and Windows UTF-16/LF input
checks also pass. The Windows shell cross-compiles with pinned headers; Mac/Windows
native runtime validation remains outstanding here.

`host:desktop` invokes `host:desktop-presentation`; `linux:e2e` invokes
`linux:presentation`. They build their prerequisites and retain artifacts under
`out/desktop-presentation` and `out/desktop-native-presentation`. The app CI gate
uses the same enclosing tasks. All Lean/Lake builds use the 48 GB systemd scope.
The controls require compilation, the exact failed assertion and a normal
failure exit; crashes and unrelated failures are rejected.

This closes the premature desktop staging acknowledgement. It does not prove
bounded compositor/worker completion, total frame work, or a universal
write-to-display deadline. A callback that never returns can retain its one
tracking slot. Counter exhaustion fails closed. Native scheduling and the
remaining renderer/history work bounds stay explicit.
