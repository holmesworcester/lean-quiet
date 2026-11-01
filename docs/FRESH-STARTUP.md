# Fresh startup ordering: exact evidence and scope

The complete frozen `62f88c5` engine gate failed at Fresh TCP after 1,605 seconds: 46 passed, 5 failed. S had 0 queued bytes, no observed close, and read no bytes before the existing 10-second diagnostic read timeout. P received the concurrent write in 19 ms. The exact engine log is `out/ci/engine-62f88c5-fresh-failure.log`. Full vacuity then passed in 48 seconds (660/660 inventory, native Store certificates, dependency audit and controls). All 1,598 tracked source blobs still matched the frozen commit after both gates.

Seven subsequent logging-only native executions passed 51/0. Those traces admitted S before opening its synthetic session. The original failed run had no internal event trace, so its exact event history is not known.

A controlled 250 ms acceptor scheduling delay reproduced the same 46/5 failure without changing any protocol, stall, idle or assertion deadline. In `out/fresh-cause/delayed-accept-run.log`:

- 216716388: the fixture publishes S's synthetic established session.
- 216716408: the actual acceptor holds S's accepted socket/quota before event delivery.
- 216716591: the runner opens the session and starts an outbound dial to S's ephemeral port 51282.
- 216716596: that dial fails; `.dialed addr none` calls the actual Node close path, retiring the session.
- 216716662: the inbound socket is admitted with zero live connections and one dropped session.
- 216716989 onward: S sends its requests; every observed frame names the already dropped session. S gets no output, while P's write arrives in 24 ms.

This is a finite reachable runtime ordering with the fixture's synthetic `established` hook. It establishes a concrete failure path matching the original symptoms, not the unrecorded history of that run, and not a counterexample involving authenticated honest app bootstrap or infinite fair loss. No bytes are transferred between closed and replacement sockets.

The fixture repair waits for the actual inbound S address in `Runner.lanes` before publishing that synthetic session. It snapshots the existing runner tick counter before publication, then requires two further completed ticks before sending wants. Every successful production tick ends in `Node.finish`/`Node.follow` and reads `hooks.established`; the counter advances only after the actual handler, effect application and expiry complete. Two ticks cover one already in flight at publication. S still never reads during setup or the stalled phase. All original stall limits start after the wants and are unchanged. The repaired fixture passes 53/0 under the 250 ms delayed-accept diagnostic (P26ms, S close1543ms).

The committed regression injects no production API. Its scratch-only mutation temporarily gives the acceptor a callback backed by that same runner's real completed tick counter. Accepted-event delivery waits for two completed ticks. The fixed fixture leaves its synthetic established list empty during that gate; the compiling old-order control publishes during the gate and must fail the intended stall assertion. The source is restored before all 18 prior controls and the final restoration run. This control uses actual completed turns instead of relying on a fixed sleep. Logs are retained by the existing named engine task. Full control-suite completion is reported separately.

Production `engine/wire/Tcp.lean` was restored byte-for-byte to frozen blob `ebe12da043b546719fe6f53f9e198f0174f2121a` before running the controls. The only proposed committed changes are the Fresh fixture and its regression runner. The ordinary failed-dial→session-retirement transition remains a protocol/liveness question; this setup repair does not change authenticated erasure or claim to solve it.

Final focused gate: baseline 53/0; same-runner two-tick gated positive 53/0; compiling old-order control 48/5 with the intended five assertions; all 18 previous controls rejected; restored production source 53/0 (P26ms, S close1536ms). Thus 19 controls pass in total. `out/fresh-cause/all-fresh-controls.log` and `out/fresh-negative` retain the evidence. The final source audit finds only the two intended test files changed among all1,598 frozen tracked blobs; every production blob is unchanged.

The original full engine command stopped at Fresh, so later engine stages did not run in that attempt. A complete engine rerun against the committed repaired source is still required; these focused checks do not replace it.
