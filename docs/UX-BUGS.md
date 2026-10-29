# Dogfood UX bug triage

The libquiet 0.7 dogfood reports apply unevenly to Lean Quiet. Three
present analogues are fixed here: arrivals moving a reader's visible
messages, compact labels with no complete view, and stored sessions
painted as presence. The source is the supplied
`/mnt/storage/holmes-wt/lq-tonight/bugs-channel.txt`, read on 2026-10-28.
Each distinct report or requested interaction is below; follow-up replies
about the same behaviour are grouped with it. No network history was
fetched.

The app currently has one channel (`general`) per community, member
profiles, photo attachments, reactions, a reaction sheet with Copy, and
community switching by acceptance. `PageId` in `Quiet/App.lean` is the
page inventory; `onEvent` is the input inventory. `Kinds/Message.read`
reads messages, profiles, attachments and reactions, in its unchanged
proved order. There are no threads, edits, DMs, unread tracking,
notification dispatch, voice playback, hover events or synced presence.
The home section headed “Direct messages” currently opens profiles.

## Every report

“Future law” means an acceptance condition for an unimplemented feature,
not a theorem claimed to be proved today. Native-only observations remain
unverified without devices; loopback tests do not simulate Wi-Fi changes.

| # | Report | Lean Quiet feature or analogue | Finding, fix, or future law |
|---|---|---|---|
| 1 | Thread notification checkbox and “inherit reply settings” undo each other confusingly | No notification preference UI or threads | Future law: an explicit override displays its value; selecting Inherit displays both its inherited source and effective value, and never silently changes an explicit override. |
| 2 | Scrolling up jerks on iOS, even after a partial patch | Bottom-anchored list with lazy measurement, `App.step` | Present arrival analogue: the anchor was captured **after** replacing the list's ids, so new messages changed the row at the old offset. Capture before refresh, grow the fetch window by the increase in total rows while scrolled back, publish the enlarged scroll range, restore by message id without waiting for native vsync, then retain existing measurement compensation. UX tests cover pending arrivals, filing, incoming writer notices and a burst larger than the old fetch window. Native frame pacing is unverified. |
| 3 | Thread unread does not reset reliably or is unclear | No read receipts or unread state | Future law: after a visible thread is read through message m, its unread set contains exactly later unread messages, excluding every message through m; closing and reopening preserves that boundary. |
| 4 | Tapping an iOS notification opens the wrong page | No notification payload/dispatch path in `Platform.Event` | Future law: opening a notification selects its authorized acceptance, channel, thread and message id; missing or revoked targets produce an explicit fallback, never an unrelated conversation. |
| 5 | Another user's mobile profile lacks their avatar image | Profiles store names; `Kinds/Profile.lean` has no avatar image data. All profiles paint initials | No photo-avatar implementation to regress. Future law: given the same available avatar content, self and other profile paths paint that content; a missing image has the same explicit fallback on both. |
| 6 | Reconnect after completing a captive portal is too slow | Native TCP runner; no Iroh/cloud connection UI | Unverified on actual networks. Future law: after a network-ready event and a reachable peer, retry within a documented bound, reset stale dial backoff, and show a truthful reconnecting state until a live exchange succeeds. |
| 7 | Cannot react by long-pressing an image | `onTap` handles a long press on any part of a message row | Not present: UX test presses inside an actual photo box, selects that message, taps a reaction, and checks the stored tally. |
| 8 | “New” divider appears above the first message when everything is new | No unread dividers | Future law: a divider appears only between a read prefix and an unread suffix, never before an all-unread history. |
| 9 | Thread “New” marker uses a different colour | No threads or unread markers | Future law: channel and thread read boundaries use the same semantic token in each theme. |
| 10 | Small unread circle is invisible in dark mode | No active unread circles; switcher has dormant `Entry.unread` rendering but App always passes zero | Future law: every active unread indicator meets the agreed contrast threshold against its actual background in both themes; test painted pixels, including dark mode. |
| 11 | “New” divider splits the author name from the first message in a clump | Every message is a separate row; no grouping or divider | Future law: place a boundary before the entire author/message group it introduces, and never between the group's author and body. |
| 12 | Cannot swipe between photos in a channel (reported as out of scope) | Photo rows exist; no gallery/lightbox | Future law: gallery next/previous traverses the channel's stable ordered photo ids exactly once, preserves the selected photo across arrivals, and stops at either end. |
| 13 | Waiting-to-join screen should show a name and avatar | Waiting and join-request pages exist; invitations carry no community profile, and request rows carry device/approval data without the requester’s chosen profile or avatar | Missing data/feature. Future law: show authenticated community and requester identities when available; otherwise show their ids and label unknown identity honestly. Never invent a name from an untrusted hint. |
| 14 | Sending in a large thread makes the message disappear from the thread view | No threads; ordinary messages have an optimistic outbox | Thread feature absent. Future law: a successfully submitted reply remains visible under the same id through pending → stored, independently of thread/community size and mention contents. Ordinary pending → stored arrivals are covered here and by `host:app`. |
| 15 | Cannot mark many threads read | No thread list or bulk read action | Future law: bulk mark-read advances every selected thread to its displayed boundary, changes no unselected thread and is idempotent. |
| 16 | Desktop channel/settings panes collapse into one panel too early | App always uses one panel; no responsive multi-pane breakpoint | Future law: preserve multiple panes while every pane's measured minimum width fits, and collapse only when the sum plus dividers exceeds available width. |
| 17 | “Message retention limit” truncated to “li…” in sidebar | No retention setting; community/member/action labels are compact in `Pages` | Present analogue: long names were ellipsized on home, switcher and profile, with no full view. Long-press compact navigation labels or the community header to open **Full label**, with wrapping, Next/Previous and Copy full text. Profile body long press also exposes the name. Existing `Text.oneLine_prefix` is unchanged. |
| 18 | Yellow avatar dot and Bluetooth error under Connection are unclear | No yellow/error dot or Connection page; home painted green dots from stored sessions | Present analogue: remove session-derived avatar dots. The app state, page key and home painter no longer carry session flags; a pixel regression checks the former dot locations. Future connection UI must describe an actual transport/error in words and offer a relevant action. |
| 19 | Presence and connectivity traffic lights can contradict one another | Session state belongs to the Runner’s Connection hooks; the app no longer polls or caches peer status | Present analogue fixed with #18. Future law: presence depends only on synced activity; transport health never changes a member's presence indicator. Connectivity has a separately named, truthful status. |
| 20 | Settings groupings with a single item add complexity; community avatar is grounding | No grouped settings UI; community avatar and name already appear in `Pages.homeBand` | Design concern, not an executable regression. Future layout condition: retain current community identity in settings and avoid an extra group level with no navigation benefit. |
| 21 | Leave screen has not been tested and needs the approved design | No leave-community flow; removal and stop-waiting are different actions | Future law: Leave cannot run before the tested confirmation path completes, Cancel writes nothing, and the resulting screen cannot still act as a member of the departed entry. |
| 22 | DM settings persist across channel switch; Close returns to old DM | No DMs or settings pane; reaction sheet and back stack are the nearest analogue | Not present on community switching: `switchToAcc` already clears sheet, selection and back stack. UX test opens a sheet, switches by acceptance and checks Back remains in the selected community. Future law: channel switch clears channel-scoped settings; dismissing settings never changes the selected conversation. |
| 23 | Missing GStreamer produces a voice playback error when scrolling, before Play | No voice playback (composer action says “Not yet.”) | Future law: mounting or scrolling a voice row cannot emit a playback error; only an attempted playback may fail, and the error belongs to that message. |
| 24 | Community unread marker should count only other communities | `Entry.unread` is dormant; `drawPage` supplies zero for every entry | Not present in running UI. Future law: aggregate unread for the community-switcher affordance is the sum over entries other than the current acceptance; switching removes the newly current entry's contribution without marking other entries read. |
| 25 | Up-arrow edit highlight flashes, fades, then appears again | No edit operation or keyboard-arrow event | Future law: entering edit has one stable selected state until send/cancel; intermediate animation frames never deselect then reselect the same message. |
| 26 | Hover menus cover other hover menus | No hover events; one `Option SheetSt` | Not present. Long pressing chooses a single message sheet; a tap outside dismisses it. Future law: at most one interactive message menu is visible; opening another dismisses the first and all hit regions match the visible z-order. |
| 27 | Mobile thread edit, including a mention, is not visible immediately | No edit operation, thread or mention semantics | Future law: accepting edit(m, text) immediately projects that text and parsed mentions at m, and pending → stored cannot restore the old revision. Test mobile and thread views against the same revision id. |
| 28 | Lost ability to select and copy text | Whole-message Copy exists in the long-press sheet; no arbitrary text-range selection | Whole-message regression absent: UX test verifies exact clipboard text and sheet dismissal. Range selection is missing. Future law: selecting [i,j) copies precisely those source characters, independently of wrapping, bidi placement, images or overlays; touch selection has visible endpoints. |
| 29 | Unexpected unstyled “mark as read / unfollow thread” dropdown | Neither action nor dropdown exists | Future law: this menu can open only through its documented trigger; its controls use the shared menu component, focus and dismissal rules. |
| 30 | Non-standard tooltip on thread mark-read | No tooltips or thread actions | Future law: every mark-read tooltip uses the shared tooltip style, delay, keyboard trigger and dismissal behaviour. |
| 31 | Quote looks like part of the preceding message; insufficient separation | No quote/Markdown blocks; plain text in separately laid-out rows | Exact feature absent. `Row.layout` places each author's body below its own name; there is no shared quote group. Future law: a quote's bounds are inside its owning message, visually separated from the preceding message by the standard inter-message gap and a quote marker. |
| 32 | Airplane mode leaves connections shown open and labelled Bluetooth | No Connection page or Bluetooth transport; stored sessions did influence dots | Misleading session-to-presence analogue fixed by #18. Future law: after transport loss, connection health becomes disconnected within a stated bound; transport labels come from the actual socket, never a default Bluetooth label. Real airplane-mode timing is unverified. |
| 33 | Inline reply pushes visible thread messages away because only latest two remain | No thread/reply preview; ordinary chat retains a paged list | Thread cap absent. Future law: while a thread preview is open, sending a reply preserves its visible anchor and does not evict already visible replies merely to enforce a two-message cap; collapse may reset the preview. Ordinary arrival displacement is fixed/tested under #2. |
| 34 | Iroh unreliable across airport Wi-Fi, tethering and VPN transitions | Lean Quiet uses `Engine.Sync.Tcp`, not Iroh | No same transport implementation. Actual route changes remain unverified. Future law: after connectivity returns, a reachable trusted peer eventually syncs, with bounded retry scheduling and no stale socket suppressing redial indefinitely. `host:cross`/`host:attach` test real loopback TCP only. |

## Laws over the running code

These exact statements are in the app axiom audit. The functions are
called by `App.step` and the label painter/clipboard handler. They
supplement the twin tests; they do not claim a native compositor or
clipboard proof.

```lean
Anchor.pinned {α : Type} [BEq α] (b : Nat) (saved : Option (α × Nat))
  (rows : List (α × Nat)) (pad : Nat) (h : b ≤ 4) :
  Anchor.restore b saved rows pad = b

Anchor.restored {α : Type} [BEq α] (b off y pad : Nat) (key : α)
  (rows : List (α × Nat)) (hb : 4 < b)
  (h : Anchor.base key rows pad = some y) :
  Anchor.restore b (some (key, off)) rows pad = y + off

Anchor.possible :
  Anchor.capture [(7, 100)] 16 40 = some (7, 24) ∧
  Anchor.base 7 [(8, 60), (7, 100)] 16 = some 76 ∧
  Anchor.restore 40 (Anchor.capture [(7, 100)] 16 40)
    [(8, 60), (7, 100)] 16 = 100

Label.copy_exact (text : String) : Label.copied text = text

Label.line_reachable (ls : Array Text.Line) (i count : Nat)
  (hc : 0 < count) (hi : i < ls.size) :
  (Label.window ls count (i / count))[i % count]? = ls[i]?
```

`Anchor.possible` witnesses the unpinned restoration premises with an
actual insertion. The twin exercises positive label capacity, multiple
nonempty pages in a short, narrow window using a valid 61-byte name, and
real visible people whose avatar corners have no connection dots. The
old `Text.oneLine_prefix`, `wrap_keeps`, `wrap_fits`, `ViewLaws.message_read`
and Switch laws retain their statements and proofs. Ellipsis remains at
the renderer's shaped-codepoint boundary; this does not claim full
Unicode grapheme segmentation or shaping support beyond the existing
renderer. The full label and clipboard preserve the source string.

## Verification

Run `cd app && mise run host:ux`; it builds the executable before running.
`ci/local.sh app` includes it alongside the existing suites and axiom
audit. Screenshots and logs are under `app/out/ux/`. Required owner gates
are `mise run check`, `mise run host:cross` and `mise run host:attach`.

Results on 2026-10-28:

The lead gated commit `2db91a0` green outside this sandbox. This follow-up
removes the unused session fields and polling, drops the now-obsolete
`sessions_not_presence` theorem, and checks the absence of dots in the
painted people rows. NetJoin reads `Connection.sessions` and its peer
facts directly from the Runner's store instead of an app cache. Anchor
and Label code and laws are unchanged. Follow-up logs are under
`app/out/prune/`; TCP tests still require the lead’s unrestricted runner.

| Gate | Result |
|---|---|
| `mise run host:ux` | 54 checks pass: 27 with immediate clamping (as the C twin), 27 with shifts queued until the frame (as native vsync). Valid Unicode labels across two pages, exact clipboard effects, a painted scroll anchor through pending/filing/incoming/burst arrivals, bottom pinning, photo reactions and switch/back behaviour. |
| `mise run check` | All 92 audited app theorems pass on standard axioms; the original 87 statements/proofs are unchanged. |
| Existing `host` / `two_nodes` | 29 / 49 checks pass. The host exercised 500 messages, 200 more arriving later, and a fling with zero unpainted viewport rows. |
| `mise run host:arrival` | 24 checks pass, including an 11-chunk photo and a 21-size formatting comparison. |
| `ci/local.sh readme` | Proof links and the repository total of 280 audited theorems pass. |
| `ci/local.sh app` | Fails at `net_join`: 2 checks pass, 8 fail after both nodes cannot start. Later suites were run separately. |
| `mise run host:cross` | Attempted: 6 checks pass, 12 fail after both TCP nodes cannot start. |
| `mise run host:attach` | Attempted: 6 checks pass, 8 fail after both TCP nodes cannot start. Local sender photo checks pass; network admission/delivery cannot run. |

The TCP failures are an environment limitation: even a standalone Python
`socket(AF_INET, SOCK_STREAM)` for `127.0.0.1` is denied with errno 1,
`Operation not permitted`. No network assertions were weakened or
skipped. The owner's required TCP gate is **not green** in this sandbox
and must be rerun in an environment allowing loopback sockets. Mise was
run offline with this worktree trusted and its state/cache redirected to
`/mnt/storage/holmes-tmp`.

Negative controls are reproducible with `python3 tests/ux_negative.py`
from `app/`. It temporarily mutates source, requires a failing proof or
suite, restores in `finally`, and rebuilds/runs the restored suite. Run it
without concurrent builds or source edits. Logs are in
`app/out/ux/negative/`.

| Control | Mutation and rejection |
|---|---|
| `pinned` | Add one to a pinned offset: `Anchor.pinned` fails. |
| `anchor-restored` | Add one to the restored offset: `Anchor.restored` and the concrete witness fail. |
| `capture-witness` | Capture one pixel past the real offset: `Anchor.possible` is false. |
| `copy-exact` | Append `?` to copied text: `Label.copy_exact` fails. |
| `line-reachable` | Start each page one line late: `Label.line_reachable` fails. |
| `sessions-presence` | Restore a green dot in the home painter: the avatar-corner pixel assertion fails. |
| `arrival-hook` | Disconnect restoration from `App.step`: pending, filed and incoming scroll-position tests fail. |
| `arrival-window` | Keep the old fetch limit after a burst: the visible-message retention test fails. |
| `arrival-vsync` | Reread the unshifted native offset before vsync: the queued-seam first-frame arrival assertion fails. |
| `label-hook` | Disconnect the header's full-label action: header access, paging and clipboard checks fail. |

The original run rejected all ten mutations and reverted them. In this
pruning follow-up, the changed dot control was rerun against the pixel
assertion; both restored UX runs pass all 27 checks (54 total).
The full-label screenshots (`label-0.ppm`, `label-1.ppm`) were visually
inspected as well as checked through touch events and clipboard output.

## Limits

No phones, emulators, Mac, internet access or pushes were used. Native
scroll pacing, notification integration, system text selection,
captive-portal recovery and airplane/Wi-Fi/VPN transitions are not
verified. Whole-message and full-label clipboard effects are checked at
the `Io.copy` seam, not against an OS pasteboard. Missing features above
remain future work, with their acceptance laws stated in the table.
