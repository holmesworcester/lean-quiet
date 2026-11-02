# Linked devices

A user's second device, as libquiet links one: a device link, approved
by one of the user's own devices. One way only (the user's call,
2026-11-01): the existing device shows the link, and the new device
scans or opens it. There is no second scan back; libquiet's needs one
only for Iroh endpoint discovery.

## The flow

1. **Show.** On a device in the community, You > Link a device (or
   Linked devices) opens Link devices. It writes a device link, an
   invitation with `link` (`Community.issue … (link := true)`), once per
   session, and shows it as a QR code with Share and Copy. Under it are
   this user's devices in the community, this one marked.
2. **Scan or paste.** On the new device, Get started > Link devices
   offers Scan QR code and Paste link. A device link skips Choose a
   name: Agree & join reads "This device will join the community as
   another device of the person who made this link", and its button is
   Link device.
3. **Ask.** The new device joins as a member's device does
   (`Community.join`): its own device key, its request, signed by it and
   by the link's bearer key, and a pending join with no name
   (`joinOps_link_unnamed`). Its node dials the issuer's node key at the
   link's hints with the request in its hello (`dialOne`). The
   issuer's node takes only that join from the bare hello
   (`bare_takes_only_join`). Waiting reads "Your other device has to let
   this one in."
4. **Approve.** Only devices of the issuer's user are asked
   (`asks_link`): under Waiting to join, the request reads Your device.
   Approving is `approveReq`, as for a member: the approval, the
   admission it gives, and the community key wrapped to the new node.
5. **In.** The new device is admitted into the issuer's user
   (`link_admits_issuer`), syncs, and writes no profile: its user has
   one (`introduce_named`). Both devices post as the same user, so one
   user's posts clump under one header.
6. **Removed.** Removing the user cuts every device admitted into it
   (`removal_cuts_off`), linked ones included.

Links are per community, as libquiet's are for now (libquiet #567 is
linking once for every community).

## The link

The fields a member's link has: the community, the invitation, the
issuer's node key, at most 8 dial hints, and the invitation's bearer
seed. A device link's code leads with kind 2 where a member's leads with
1, so member links are unchanged. Its page and scheme are its own:
`https://holmesworcester.github.io/lean-quiet/link#<code>` (site/build.py
writes link.html from the join page) and `leanquiet://link/<code>` (the
Android intent filter takes host `link`). A prefix of the other kind is
refused (`parse_other_kind`), as libquiet's scheme must match its offer.
Any entry (a deep link, Join's paste or scan, Link devices' paste or
scan) routes by the kind.

The bearer seed admits nobody by itself. It signs the request; an
admission needs one approval, signed by a device admitted into the
issuer's user, other than the new one (`link_approved_by_issuer`,
`admission_needs_approval`). The poc's device link (poc-19) carried the
user's root seed and enrolled with no approval. That is the open link
Lean Quiet does not have.

## Laws and controls

| Law | Over | Control |
|---|---|---|
| `link_approved_by_issuer` | the validators (`Approve.check`, `Request.check`) | `Approve.checkAnyUser` (`anyUser_approves_link`) |
| `link_admits_issuer` | the validators | `Request.checkNewUser` (`newUser_links`) |
| `issue_link` | `issue` | |
| `parse_text`, `parse_uri`, `parse_other_kind` | `Invite.parse` | linkcheck's mutants |
| `asks_link` | `asks`, which the requests page reads | |
| `joinOps_link_unnamed`, `introduce_named` | `joinOps`, `introduce` | `introduceShipped` (`shipped_introduce_unnamed`) |

Key material reaches only admitted devices through `approveReq`'s wraps
(holmes-80's signed wraps own that law).

## Tests

- `link_devices` (tests/app/headless.sh, `mise run host:link-devices`):
  four apps by memory transport. Ann links A2, Bea links B2; only the
  issuer's user is asked; posts cross; removing Bea cuts both her devices
  and not Ann's second.
- `net_link` (`mise run host:net-link`, tests/app/run.sh's network
  stage): the same over TCP, four nodes on loopback.
- `linkcheck`: device links parse back, are refused under a member's
  prefix, and no mutant turns one into a member's link; the engine
  judges another user's approval invalid.
- site/test.py: link.html opens `leanquiet://link/` with the fields.

## Not yet

- **A linked device whose only session is with its sibling is not told
  of its user's removal** over TCP: once the sibling learns it is cut,
  `mine c` drops the community and its rooms give nothing, so it closes
  the session silently. The rule that a cut node gives its removal to
  the peers the same removal cuts comes with the pre-admission rooms
  (holmes-80's `preadmit`). Until then `net_link` prints GAP for it
  (`--strict` fails it).
- **Read state across a user's devices**: notices in a per-user room
  `userRoom c u`, carried only between u's admitted devices
  (docs/NOTIFICATIONS.md, with the notifications port).
- iOS.
