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

## Remaining connection-lifetime proof obligation

`Sweep.FairLoss` names delivery of semantic operations. There is not yet a
proof projecting the actual encrypted TCP attempts, socket teardown and key
retirement onto that predicate. A fresh encryption nonce also means that
repeated attempts need not repeat an identical ciphertext; fairness must name
the logical message and its actual wire attempts precisely.

An earlier version described every old-epoch frame being delivered after its
socket closed and called that a reliable native execution. That was an
illustrative message-delay argument, **not a demonstrated TCP execution**.
TCP does not move queued bytes from a closed socket onto a replacement.
The stronger wording was incorrect and has been removed. A separate actual
TCP/Noise/SQLite trace did demonstrate that control-close or completed-writer
reaping could discard an already-admitted signed notice. The bounded one-frame
repair and its exact limits are documented in [CLOSE-INGRESS.md](CLOSE-INGRESS.md).
This finite repair does not establish arbitrary replacement/delivery progress.

The missing proof cannot be replaced by assuming that a retry eventually
arrives already authenticated and accepted: that would hide the application
obligation inside the link assumption. Any protocol repair must first identify
an actual failing execution and preserve key erasure, revocation and removal
notice behavior. No change to those security semantics is claimed here.

Distinct authenticated sessions sharing a socket now use the actual stable
retry admission queue described in [RETRY-ADMISSION.md](RETRY-ADMISSION.md).
A concrete fixed-order starvation execution is repaired, and the shared core
proves service or retirement within p+1 eligible vacant-slot opportunities.
Composing those opportunities with every full Node/Sweep/native execution
and semantic delivery remains open; repeated native completion or the
UI-first selector alone does not establish that composition.

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
