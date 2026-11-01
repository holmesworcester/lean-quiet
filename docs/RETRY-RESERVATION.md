# Reserved retry transport

This change separates catalog retry progress from ordinary sync traffic.
The running Node, TCP runner and socket writer use the same small queue
functions whose bounds are checked in `Reserved.lean` and `OutboxLaws.lean`.
It does not establish the complete arbitrary-execution liveness theorem.

Each socket has bounded normal and protected-control queues, plus one
reserved retry frame. Local urgent frames remain first in a native write;
protected controls follow, then the reserved retry, then the normal serving
burst. A continuously replenished normal queue cannot consume that retry
slot or postpone an admitted retry beyond the next writer take.

The normal and control queues each obey `sockCap` bytes and `sockFrames`
frames. The retry payload is at most `maxFrame`. Consequently the exact
length-prefixed native batch is at most
`2 * sockCap + maxFrame + 4 * (2 * sockFrames + 1)` bytes. This bounds
admitted queues and writer batches, not the work or allocations performed
before Node output admission. Large historical blobs and whole-table scans
remain outside the bounded-work result.

Ordinary overflow rejects that optimization batch without closing the
socket or erasing retries. Bare handshakes and notice-bearing output use
the independent protected queue. A removal notice therefore survives an
ordinary backlog. Exhaustion of the protected queue still explicitly closes
the transport; universally bounded notice generation and completion/failure
reporting remain separate obligations. A notice's entire prerequisite closure
can currently be materialized before admission and needs incremental service.

Wanted hot data is also limited to one selected urgent op per service call.
Other wanted hot ids remain in the FIFO. `serveOwed_hot_count` proves this
bound; `serveOwed_hot` now explicitly refers to the selected hot id. The
ordinary FIFO progress theorem remains checked under continuing arrivals.

## Durable cursor acknowledgment

Preparing or queueing a retry does not advance the durable peer cursor.
The one retry slot remains occupied through queued, writing and completed
states. Only completion of the actual native send produces a completion
ticket. On the next retry tick, the loop compare-and-swaps the stored cursor
from the ticket's exact prior value to its next value, then releases the slot.
No SQLite operation runs while holding the socket queue mutex.

Closing before completion, refusing transport admission, or crashing before
the metadata save leaves the old position retryable. A late ticket from an
old socket cannot overwrite a cursor whose value has changed. Missing or
unauthorized rows need no network attempt and still advance immediately.

The storage/authorization proof continues to cover every actual emitted
frame: reserved frames remain in `Effects.send`; retry markers are filtered
against the already authorized serve payloads and sealed individually.

## Remaining connection-lifetime counterexample

**Fair loss of wire messages alone does not imply accepted data delivery.**
Consider an authenticated epoch whose key is deleted after an idle timeout.
Emit its data frame at time `t`, close that epoch at `t + timeout`, and
deliver the unchanged frame at `t + 2 * timeout`. Do this to every replacement
epoch. Every emitted wire copy is delivered after a finite delay, and every
process and worker can continue running, yet each delayed frame names a key
the receiver has already discarded. Native delivery is reliable in this
execution; authenticated payload acceptance still fails forever.

Calling the link "semantically fair" so that one retry must already decrypt
would hide this application obligation inside the environment assumption.
The current reservation work does not make that substitution.

A possible next protocol change is to distinguish transport loss from
authenticated-session retirement. Keep the latest authenticated peer session
and its transport keys durably across ordinary socket close/idle timeout;
retry its self-identifying sealed frames when a new socket connects. Purge
keys only for actual revocation, explicit retirement, or a checked replacement
protocol that cannot discard all in-flight progress indefinitely. This can
avoid retaining an unbounded history of old keys, but needs an audit of
restart, duplicate handshakes, session replacement, key rotation and removal
notices before implementation. No claim that this design is yet proved is
made here.

Multiple distinct authenticated sessions sharing one socket also need a
proved rotating admission policy. The reserved slot presently bounds and
serves admitted retries; a fixed earlier session may take every newly vacant
slot. Neither repeated native completion nor the UI-first selector alone
discharges that multiplexing obligation.

## Regression boundary

The native fixture uses the real Runner, SQLite, Node and writer with a raw
TCP peer. Plain session sealing isolates queue admission; the existing
JoinFair suite retains production Noise coverage. The peer continuously wants
seventeen individually fitting roughly 1 MB hot ops, ordinary serving has
zero window, posting continues, and the first two target payloads are lost.
Success requires actual TCP receipt and a valid identical derived fact.

Cursor checks distinguish prepared output from completed native attempts.
The retirement and stalled-writer fixtures exercise actual socket ownership,
including a full event queue and a peer which never reads. Linux/POSIX native
abort tests are runtime evidence at the pinned SDK boundary; Windows pending
write cancellation is not claimed by this patch.

The one-hot policy also changes the old JoinFair fixture's setup: a throttled
relay can drain faster than the newly bounded sender emits. The fixture now
first holds A-to-B forwarding while still allowing reverse wants, and waits
for both its actual bounded-buffer read-pause signal and a real runner output
backlog. This finite setup has an explicit 10-second failure deadline. It
then runs the original 2.5-second throttle sample; the 3-second starvation
marker and subsequent recovery deadlines are unchanged. The full JoinFair
task passes 38 checks and retains the strict write-first, deferred-hint and
network-first mutation controls.

The retry fixture stops its runner before inspecting that runner's SQLite
handle. The pinned `THREADSAFE=2` build permits separate concurrent connections,
not concurrent access to one handle. Production SQLite behavior is unchanged;
this ownership repair passed the complete 12-check suite and all five controls.
