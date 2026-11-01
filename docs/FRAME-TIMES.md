# Bounded frame timing diagnostics

The non-chat branch of the actual App frame appended a timing sample on every
frame without trimming. The chat branch already kept at most 600 samples,
discarding the oldest 300 when the buffer filled. The real 650-frame regression
reproduced three non-chat failures; its chat case retained a signed conversation
row and passed the existing policy checks.

Both frame branches now call `FrameTimes.push`
(`engine/renderer/FrameTimes.lean`). Its kernel theorem
`FrameTimes.bounded` gives an unconditional output count of at most 600.
For histories already within that bound, the helper preserves the existing
chat policy and sample order. It also normalizes an oversized input to the
newest 300 samples before appending. Nonempty 600- and 900-entry kernel
witnesses apply that theorem and check the resulting 301-entry size.

`mise run test:app-frame-times` will build the actual App/SQLite fixture,
run 650 consecutive non-chat frames and 650 chat frames, restore raw append
at each call site as a compiling control, and change the threshold to 601
as a kernel control. A control must fail its exact completed assertions or
capacity obligation; compiler/setup failures, crashes and timeouts do not
count. The restored source must pass all nine native checks again.

The private source passes all nine checks, both compiling runtime controls,
the kernel capacity control, and the restored baseline.
Combined primary-source validation is pending. The engine suite and ready
bootstrap-progress workflow will invoke this named task; hosted activation
remains pending. It requires the repository toolchains, fonts, Linux user
systemd and native SQLite/crypto. Every Lean/Lake build uses a 48 GiB/no-swap
scope. Logs and databases remain in `out/app-frame-times`.

This is a bound on retained diagnostic entries. It is not a proof of total
heap use, Nat payload size, frame-counter growth or every application cache.
Native milliseconds remain observations, separate from completed-stage counts.
