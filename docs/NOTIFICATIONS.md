# Notifications

Android only, for now. This is the user's decision of 2026-11-01: "don't
worry about iOS for now, just android". The desktop has no notifications.

Lean Quiet ports libquiet's rich notifications (#844):
- one native card per conversation, grouped by community, with its unread
  count and the latest five messages;
- libquiet's levels, and its reply and follow rules;
- the conversation on screen is quiet;
- a card's link opens its exact message;
- inline photo previews and placeholder avatars.

It also adds libquiet's optional **Sync in the background**. The user's
words: "don't stop sync in background. a foreground service on android
makes sense. make it optional and follow quiet's designs."

The prior art was a3/notify 5a1b343, written before the op-tree layout. It
was ported, not merged; see "What changed from a3/notify" below.

## Sources followed

libquiet's `origin/main` (ab3d244cf) is the reference, read with
`git show`:
- `crates/quiet-core/src/notify/policy.rs`: the policy;
- `DESIGN.md`: "Notification policy", "Reply notifications", "Notification
  preferences";
- `app/src/SettingsDrawer.svelte`, `app/src/NotificationSettingsPage.svelte`
  and `notifications.ts`: the settings, their copy and defaults;
- the Android app (`app/src-tauri/gen/android/app/src/main/`):
  `SyncService.kt`, `Notifications.kt`, `ConversationNotifications.kt` and
  `AndroidManifest.xml`.

Classic Quiet (`/home/holmes/quiet`, packages/mobile) differs. Where it
does, libquiet is followed, because it is the current design:

| | libquiet (followed) | classic Quiet |
|---|---|---|
| Background mechanism | `SyncService`: a plain dataSync foreground service, `START_NOT_STICKY`, `stopWithTask=false`, no wake lock; stops on Android 15's `onTimeout` | WorkManager `BackendWorker` with `setForegroundAsync` (dataSync) |
| Setting | You > **On this device** > **Sync in the background**, with the sub "Keeps Quiet connected while it is off screen."; Android only; **off** by default | A Community menu item, "Enable background Tor", with no copy; only with push enabled |
| Ongoing notification | "Quiet is syncing", channel `sync` ("Syncing", "Shown while Quiet keeps syncing in the background."), LOW importance, silent; a tap opens the app | "Backend is running", channel "Backend", HIGH importance; a tap does nothing |
| Off | The service is stopped; Android freezes the process after it leaves the screen | A 30-second hibernation grace, then hibernation; FCM push wakes it |
| Message channel | `messages`: "Messages", "New messages in channels you are not reading.", HIGH; MessagingStyle with Person and shortcuts | "Incoming messages", InboxStyle, no Person |
| Levels | "All messages", "Only @ mentions and DMs", "Off" (Community settings > Notifications) | Desktop only: "Every new message" or "Nothing" |

Classic's 30-second grace bought time for a push wake path. Lean Quiet has
no push service, so with the setting off it stops sync on background, as
before.

## The policy (`app/community/Screen.lean`, `Notify`)

`Notify.policy` is libquiet's `decide`, over the user's `Notice.Settings`
and a post's `Subject`:
- **Level.** The conversation's level, then the community's, then All. Off
  silences everything.
- **Top-level posts.** A post alerts at All, or when it mentions the user,
  or when it is a direct message.
- **Replies.** All alone is not enough. A reply never alerts in an
  unfollowed thread. Otherwise it alerts on:
  - a mention;
  - the replies setting (the conversation's, then the community's; on by
    default in one-to-one direct messages);
  - a followed thread, a one-to-one DM, being the root's author, or having
    replied.

The app has no direct messages, mentions or threads yet, so those inputs
are false.

`tests/app/notify-policy.txt` holds 20,736 cases computed by libquiet's
own `policy.rs` at ab3d244cf, over every policy input. Only its serde
derives are stripped. `tests/app/notify_oracle.py` regenerates the file
byte for byte from the local libquiet clone, and the `notify` test checks
`Notify.policy` against every case.

**Delivery gates** (`Notify.eligible`). A post can alert only when all of
these hold:
- it comes from another device and another user;
- this device is a member;
- it is news;
- it is not on screen;
- it is not read;
- the policy admits it.

`notifies_iff` states this rule exactly, and `own_silent` and `can_alert`
are its two edges.

## Where candidates come from

The reader's `notify c u` want, one per community, is session-owned like
`maintenance`. It reads (`Kinds.Notify.read`):
- c's newest 16 readable posts, keeping only committed, Valid ones (outbox
  rows are not candidates);
- each post's text, opened under its key, its author's name and its first
  picture's preview;
- this device's `caughtUp` mark;
- the user's private state (`noticeState`).

The reader reads it again only on an exact window notice. A turn never
polls the store.

**News.** A post is news when its claimed time is at or above the
community's newest `caughtUp` mark. That mark is this device's local
watermark, Body 21 / Fact 19.
- **The first mark** is written the first time the app reads the
  community, which is when the device starts joining it. So history
  written before the join stays silent, while a welcome posted after
  admission alerts.
- **Later marks** follow the newest post considered, capped at now.
  `marks_le` proves a mark never runs ahead of the clock, so a post
  claiming a future time cannot silence later ones.
- **Restarts.** Within a process, a seen-set keeps a post from alerting
  twice (`once`). Across restarts, the mark keeps posts already considered
  from alerting again.
- **Limits.** A post that syncs in late claiming an old time (from an
  offline writer) is silent, as it is under libquiet's gates. Across a
  restart, posts of the mark's own minute can alert again.

This replaces a3/notify's per-process `caughtUp` epoch, written by the
runner's `settled` hook. Main has no such hook. It also replaces a3's
ledger file of seen ids, which was state outside ops.

## The turn (`Notify.step`) and its laws

Every turn (`App.notifyStep`), in front and in the background, the app:
1. collects each community's snapshot;
2. runs `Notify.step` over the tracker, this device's communities, the
   conversation on screen and the inputs;
3. hands the card packets to the shell;
4. writes new marks;
5. sends what the conversation on screen withdrew, as read, to the user's
   other devices.

These laws are over `step`, the running code:
- `step_post`: every card posted is of a post in a snapshot that the rule
  admits.
- `step_quiet`: the conversation on screen posts nothing and keeps no card.
- `step_read`: a read message has no card.
- `step_removed`: no card stands for a community this device left or was
  removed from.
- `step_keeps`: a card stands unless the turn's `gone` names it, so a
  partial read keeps newer unread messages.

## Read state across a user's devices

The user wants read state and notification settings shared across a
user's linked devices. `notice` will carry them; `caughtUp` never
travels.

**Today, notices are local** (`notice_local`), like the caught-up mark
(`caughtUp_local`), and never leave the device that wrote them. A shared
notice, even sealed, would tell every member's node that user u wrote one
at time t: when u reads, when u changes a setting, and how many devices u
has. With linking a stub, every settings change would also go to the
whole community for nothing. So settings and reads stay on the device
until there are other devices to tell.

Some laws are already stated for when notices travel:
- `notice_signed`: a notice about user u is signed, as that exact op, by
  a device admitted into u.
- `noticeRecipients_own`: `noticeWrite` seals one copy per device
  admitted into the user (`admission.byUser [c, u]`), and every key a
  notice is sealed to is one of those admissions' node keys. A read is
  never sealed back to the writing node.

**Follow-on, with device linking: a per-user room.** Notices travel only
in a room of their own per user, carried only by sessions between that
user's own devices.
- **Scope.** A notice's scope becomes `.shared (userRoom c u)`, not the
  community's room. The room is typed: its id is derived from the
  community and the user (hashed under a domain tag), so it is never a
  community id.
- **Carriage.** `hooks.rooms` (the rooms a connection carries; app/Commands
  and the trust rule) adds `userRoom c u` to a session exactly when both
  ends are admitted devices of user u in c.
- **The law to prove:** no session whose peer is not an admitted device of
  u carries `userRoom c u`. That is, for every connection `cid` and every
  room `r ∈ rooms cid`, if `r = userRoom c u`, then the peer's admission is
  u's. With `notice_signed`, it gives: only u's devices hold u's notices,
  and only u's devices write them.
- **Privacy then.** Other members' nodes never receive the ops, so the
  timing (when u reads, when u changes a setting) and u's device count stay
  private from them. Only the network-level fact that two of u's devices
  talk is visible, as it is today.
- **What stays.** The sealing (`noticeRecipients_own`) stays as
  defence in depth.
- **What changes.** Read acks start going out once a second device is
  linked. Its reads reach the first device, and the first device's cards
  for those messages are withdrawn (`step_read`).

**`caughtUp`'s tag.** Like main's other local Community ops (secret 15,
accept 13, joining 14, abandon 17, key 18, endpoint 22, receipt 24),
`caughtUp` holds a tag in the family's closed sum, so the store can file
and judge it beside the shared ops. The tag never appears on the wire.
Keeping it a Community op type is the user's decision of 2026-11-01.

## Private state: the `notice` op (Body 20 / Fact 18)

A notice is a user's reads and notification level, sealed to one of that
user's devices.
- **Signing.** It cites the community and the writer's admission, and the
  writer's device signs it. `notice_signed` proves that a notice about user
  u was signed, as that exact op, by a device admitted into u.
- **Sealing.** The payload is X25519-boxed to the recipient device's node
  key. Its associated data binds it to the community and the user.
- **Payload.** Each notice carries:
  - the reads, as exact message ids;
  - the writer's current levels;
  - the revision those levels were set at.

  The settings with the highest revision win, so a read written at the same
  time as a settings change cannot undo it.
- **Bounded read.** A device reads only the newest 64 notices sealed to it.
- **Read acks** are sealed only to the user's other devices. Today every
  user has one device (linking is a stub), so none are written. Notices
  are local today in any case (see above).
- **Settings** are sealed to every own device, this one included.

The two op tags (approved by the user as a wire change; agreed with
holmes-80, alongside one-approval, which adds no tags) are both local
today, so nothing new reaches the wire yet. Notices start travelling,
in the per-user room, with device linking.

## Cards: the native seam

`Notify.packets` turns a turn's effects into one JSON packet per
conversation it touched. A packet carries:
- the tag (the conversation id) and the group (the community);
- the title, `#general (community)`, and the body;
- whether it alerts, and the count;
- the photo, as RGBA (at most 128 px a side, from the attachment's
  preview);
- the latest five messages, oldest first, each with its sender, an
  identity-palette colour and initial, and the time in ms.

A post alerts; a read or a removal re-renders silently, or cancels.

`Io.notify` hands the packet to the shell, which queues it on its own
thread and returns at once, so the frame never waits on it. On Android:
- `Notifications.java` renders `Notification.MessagingStyle` with `Person`
  and a long-lived shortcut;
- `NotificationImages` is a read-only content provider for the photo PNG;
- a card's tap is `ACTION_VIEW leanquiet://open/…`.

The headless twin appends packets to `notifications.jsonl`, or to the
`Sim`'s ref.

**Links.** `Target.uri` is `leanquiet://open/` followed by the base62 of
`(version, community, conversation, message, root)`, beside the invites'
`leanquiet://join/`. `target_roundtrip` proves a link parses back to
exactly its target. `openTarget` waits until the message is held, then:
- selects this device's admitted entry in the community
  (`targetOf_member`);
- opens the conversation anchored at the message (`target_opens`).

The `notify` test checks that the message is then wholly on screen, with
125 newer posts below it.

## Sync in the background

`St.keepSync` is the setting. It is saved in checkpoint slot 14, and
`St.canKeep` is whether the platform has the service.
- **One guard.** `St.syncs` is `active && surface || keepSync`. It is the
  single guard of `netStep`, `flushNode` and `resumeReader` (`syncs_kept`,
  `syncs_off`).
- **Going to the background with it on** (`keepAwake`): input is captured,
  the page is left, and the checkpoint is saved. The node is not stopped
  (`unmount_keeps_node`).
- **Each background step** (`backgroundStep`):
  1. reaps finished tasks;
  2. keeps the node and its parked writes moving;
  3. remounts the session (not a page) for its own wants;
  4. runs notifications;
  5. lets the reader pass.

  It draws nothing.
- **Toggling** changes nothing else of the node (`keepSync_keeps`).
- **Starting the service.** The service starts while the app is in front
  (at launch with the setting on, or on toggle), because Android forbids
  starting a foreground service from the background. It runs until the
  setting is turned off.
- **Swiping the app away stops sync** (the user: "swipe away stop is
  fine"). Lean's loop runs on the NativeActivity's thread. With the
  setting on, the service keeps the process syncing and notifying while
  the activity is merely stopped: home, another app, or the screen off.
  When the app is swiped away from recents, the activity is destroyed,
  Lean's main returns and the process exits, as it always has. Sync
  resumes the next time Quiet is opened.

## Tests

- `platforms/headless/Notify.lean` (`lake build notify`), on the gate in
  `tests/app/headless.sh`. Two apps are joined by link, with ops carried
  between them as sync carries them. It checks:
  - the 20,736 reference cases;
  - own posts are silent;
  - one card per conversation, with its count, and no repeat alerts;
  - opening the conversation withdraws its card, and it stays quiet;
  - Off silences;
  - a card's link opens its message wholly on screen;
  - with the setting on, a post arriving in the background alerts and
    nothing is drawn;
  - with it off, nothing runs in the background, and the post alerts once
    the app is in front;
  - removal withdraws the standing card.
- `tests/app/notify_negative.py` (`mise run host:notify-negative`, in
  `--full`) works in a snapshot:
  - ten runtime mutants, each of which must fail its named check;
  - eight proof mutants, each of which must break its law.
- **Android:** `mise run android:apk` builds the APK. It was not installed
  on any device here; device checks are holmes-1e's.

## What changed from a3/notify

**Dropped:**
- The per-frame poll of every community's readable list. Main's reader
  wants and exact notices replace it.
- The ledger file of seen ids. The `caughtUp` mark replaces it.
- The bespoke anchored window and scroll laws. Main's anchored window and
  checkpoint restore replace them.
- The in-app banner. On Android a card posted while the app is in front
  shows as a heads-up.
- The iOS files: out of scope.

**Not yet:**
- Mentions, DMs and threads (the app has none).
- Thread replies and pending-admission settings.
- Per-conversation exceptions.
- A notification-permission prompt in the app. Android 13+ asks at
  launch.
- Cards from a process that died are withdrawn at the next launch, not
  adopted.
