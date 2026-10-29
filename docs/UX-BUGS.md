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
community switching by acceptance. `PageId` in `AppTypes.lean` is the
page inventory; `onEvent` in `App.lean` is the input inventory.
`Kinds.Message.read` (`ops/community/message/View.lean`) reads messages,
profiles, attachments and reactions, in its unchanged proved order. There are no threads, edits, DMs, unread tracking,
notification dispatch, voice playback, hover events or synced presence.
The home section headed “Direct messages” currently opens profiles.

## Every report

“Future law” means an acceptance condition for an unimplemented feature,
not a theorem claimed to be proved today. Native-only observations remain
unverified without devices; loopback tests do not simulate Wi-Fi changes.

| # | Report | Lean Quiet feature or analogue | Finding, fix, or future law |
|---|---|---|---|
| 1 | Thread notification checkbox and “inherit reply settings” undo each other confusingly | No notification preference UI or threads | Future law: an explicit override displays its value; selecting Inherit displays both its inherited source and effective value, and never silently changes an explicit override. |
| 2 | Scrolling up jerks on iOS, even after a partial patch | Bottom-anchored list with lazy measurement; the reader's window of rows about an anchor (`chatFrame` in `App.lean`) | Present arrival analogue. The frame already keeps the row at the viewport's bottom edge still across a new window, without waiting for native vsync; two holes remained. Away from the bottom the window stayed "the newest", so a burst of arrivals larger than the window pushed the row being read out of it: the window's next anchor is now `Lifecycle.follow`, about a row whenever the view isn't pinned (`follow_away`). And the shift was clamped to the scroll range the shell was last told: the frame now publishes the new range before `scrollBy`. UX tests cover pending arrivals, filing, incoming writer notices and a burst larger than the window, on both scroll seams. Native frame pacing is unverified. |
| 3 | Thread unread does not reset reliably or is unclear | No read receipts or unread state | Future law: after a visible thread is read through message m, its unread set contains exactly later unread messages, excluding every message through m; closing and reopening preserves that boundary. |
| 4 | Tapping an iOS notification opens the wrong page | No notification payload/dispatch path in `Platform.Event` | Future law: opening a notification selects its authorized acceptance, channel, thread and message id; missing or revoked targets produce an explicit fallback, never an unrelated conversation. |
| 5 | Another user's mobile profile lacks their avatar image | Profiles store names; `ops/community/profile/` has no avatar image data. All profiles paint initials | No photo-avatar implementation to regress. Future law: given the same available avatar content, self and other profile paths paint that content; a missing image has the same explicit fallback on both. |
| 6 | Reconnect after completing a captive portal is too slow | Native TCP runner; no Iroh/cloud connection UI | Unverified on actual networks. Future law: after a network-ready event and a reachable peer, retry within a documented bound, reset stale dial backoff, and show a truthful reconnecting state until a live exchange succeeds. |
| 7 | Cannot react by long-pressing an image | `onTap` handles a long press on any part of a message row | Not present: UX test scrolls back to a photo as a reader would, presses inside its laid-out box, selects that message, taps a reaction, and checks the stored tally. |
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
| 18 | Yellow avatar dot and Bluetooth error under Connection are unclear | No yellow/error dot or Connection page; home painted green dots from stored sessions | Present analogue: remove session-derived avatar dots. The app state, page key and home painter no longer carry session flags, and the reader no longer polls the session list; a pixel regression checks the former dot locations. Future connection UI must describe an actual transport/error in words and offer a relevant action. |
| 19 | Presence and connectivity traffic lights can contradict one another | Session state belongs to the Runner’s Connection hooks; the app no longer polls or caches peer status | Present analogue fixed with #18. `net_join` reads A's kept sessions with Bea's node from the store, as the Runner's hooks do. Future law: presence depends only on synced activity; transport health never changes a member's presence indicator. Connectivity has a separately named, truthful status. |
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
| 34 | Iroh unreliable across airport Wi-Fi, tethering and VPN transitions | Lean Quiet uses its own TCP (`engine/wire/Tcp.lean`), not Iroh | No same transport implementation. Actual route changes remain unverified. Future law: after connectivity returns, a reachable trusted peer eventually syncs, with bounded retry scheduling and no stale socket suppressing redial indefinitely. `host:cross`/`host:attach` test real loopback TCP only. |

## Laws over the running code

These are in the axiom audit (`tests/Axioms.lean`), and each is about a
function the app calls: `Lifecycle.follow` from `chatFrame`,
`Label.window` from the Full label page's painter, `Label.copied` from
its Copy full text. They supplement the twin tests; they don't claim a
native compositor or clipboard proof.

```lean
Lifecycle.follow_away (cur : Option α) (newer : Nat) (near : Bool)
  (atView nearEnd : Option α) (h : nearEnd.isSome) :
  (Lifecycle.follow cur newer false near atView nearEnd).isSome

Label.copy_exact (text : String) : Label.copied text = text

Label.line_reachable (ls : Array Text.Line) (i count : Nat)
  (hc : 0 < count) (hi : i < ls.size) :
  (Label.window ls count (i / count))[i % count]? = ls[i]?
```

`follow_away` says the window is about a row whenever the view isn't
pinned (`pinned = false`), given a row to take. That the window about a
row holds it is the reader's read (the row and those older, then those
newer), tested here and not yet a law. `copy_exact` is definitional: it
pins the function the handler calls. uxbugs' `Anchor` laws are not
ported, since the reader's window replaced the fetch limit they were
about and nothing would call them. The old `Text.oneLine_prefix`,
`wrap_keeps`, `wrap_fits`, `ViewLaws.message_read` and Switch laws keep
their statements and proofs. `NavLaws.depth` now says fewer than 19
backs reach a root, as there are 19 pages. The label page's text and
page are in the lifecycle checkpoint (page code 18), so `page_round`
and `restore_page_anchor` hold unchanged.

## Verification

`mise run host:ux` builds `ux`, runs it on both scroll seams and then
its negative controls; `tests/app/run.sh` (the `app` gate of
`ci/local.sh`) runs the same. Screenshots and logs are under `out/ux/`.

| Suite | Checks |
|---|---|
| `ux out/ux` | 27, with shifts clamped at once (as the C twin): Unicode labels across two pages, exact clipboard effects, a painted scroll anchor through pending, filed, incoming and burst arrivals, bottom pinning, photo reactions, and switch/back. |
| `ux out/ux-queued queued` | The same 27, with shifts queued until the frame (as native vsync). |
| `net_join` | A holds a session with Bea's node, read from its store. |

`tests/app/ux_negative.sh` mutates a scratch copy, never this tree. The
copy must pass on both seams first; then each mutant must fail its law,
or the suite at the named check.

| Control | Mutation | Refused by |
|---|---|---|
| copy | Copy appends `?` | `Label.copy_exact` |
| label pages | Each page starts a line late | `Label.line_reachable` |
| follow | The window may stay "the newest" away from it | `Lifecycle.follow_away` |
| dot | A green dot on home's avatars | home avatars have no connection dots |
| header | The header's long press opens nothing | long press on the header opens its complete label |
| rows | A page row's long press opens nothing | switcher long press discloses without switching |
| window | The window's old rule: "the newest" until an edge comes near | a burst larger than the reader's window |
| range | The shift is clamped to the shell's old range | a burst larger than the reader's window |
| anchor | The frame keeps no anchor | pending arrival keeps the visible row |
| vsync | The frame paints at the offset before its queued shift lands | pending arrival keeps the visible row (queued seam) |

## Limits

No phones, emulators or the Mac were used. Native scroll pacing,
notification integration, system text selection, captive-portal
recovery and airplane/Wi-Fi/VPN transitions are not verified.
Whole-message and full-label clipboard effects are checked at the
`Io.copy` seam, not against an OS pasteboard. Missing features above
remain future work, with their acceptance laws stated in the table.
