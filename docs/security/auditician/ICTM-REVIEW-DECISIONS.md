# ICTM review decisions

Approved by the engagement owner on 2026-08-31 and clarified on 2026-09-01.
These decisions are normative for the client 9.0.0 audit and refine the initial
Quint/user invariants without claiming that the implementation already
satisfies them.

1. **Removal semantics:** Backdating and strict rejection of content concurrent
   with removal are not priority guarantees. Removal is intended to converge to
   loss of community connectivity, authority to write new accepted data, and
   access to replacement keys once the removal is universally known in valid
   group state. Already produced or retained data is not retroactively erased.
2. **Cross-system ordering:** Gaps between OrbitDB content and LFA authorization
   are relevant but not currently high priority. Nevertheless, content that
   arrives before the LFA state needed to authorize it must not be surfaced or
   used until that proof is available (ICTM D6).
3. **Private channels:** Every current community admin is a member/participant
   of every private channel and receives all channel history. The authenticated
   participant state, participant display, application authorization, and key
   distribution must agree on that fact; merely making channel keys
   decryptable to an admin without representing the admin as a participant is
   insufficient. A newly added non-admin participant also receives all channel
   history. Adding and removing private-channel participants are admin-only
   actions, and an admin cannot be removed from one private channel while
   remaining an admin. This implication does not apply to direct messages:
   community admins are not implicit DM participants. This clarification does
   not decide whether losing the admin role retains or removes existing
   private-channel memberships; that lifecycle choice remains TBD, but it must
   be authenticated, admin-authorized, consistent with the participant view,
   and accompanied by the required replacement-key transitions.
4. **Account/device recovery:** Admin status does not permit recovery, linking,
   key publication, or key changes for another user's account or devices. Users
   may manage only their own account/device recovery material.
5. **Role self-grant:** There is no general role self-grant. The only intended
   self-grant is for an invited member to acquire exactly the roles and keys
   preauthorized by the admin-issued invitation during admission.
6. **Offline admission:** An invited member should be able to join and obtain
   all promised history using data retained by QSS when no other member is
   online. QSS executes, but does not enlarge, the invitation's authority.
7. **QSS/third-party metadata:** Hiding protocol/traffic metadata such as time,
   hashes, opaque identifiers, sizes, and routing relationships from QSS is out
   of scope. No user-created field—including user, community, or channel names,
   profile text, filenames, file metadata, messages, or previews—may be
   disclosed in plaintext to QSS or another third party.
8. **Notification delivery and local display:** Push infrastructure receives a
   wake-up free of user-created content—not a user-created author, channel,
   message, filename, or preview. It is silent/data-only where the platform
   supports that pattern; a fixed generic iOS NSE envelope is allowed where
   needed. A trusted on-device notification service then performs the background
   fetch and local decryption; Android uses the analogous background service.
   After successful authentication, the notification displays at least the
   message author and channel. This decision neither requires nor forbids
   additional locally decrypted message text. Whether and how the resulting
   local notification appears on a locked screen is controlled by the user's
   operating-system notification settings.
9. **Admission acceptance:** Admission uses Option A. An existing member device
   or registered QSS must validate and sign the exact `ADMIT_MEMBER` or
   `ADMIT_DEVICE` link, atomically append it to the accepted sigchain, and
   durably persist that state before releasing an accepted graph, keyring, or
   other member-only key/history material. No second online member is required,
   so QSS-only admission remains supported. A witnessed/admin-approval gate is
   reserved as a possible future optional community setting for communities
   that choose to require joiner approval; it is not part of current acceptance.
10. **Protocol versions:** There is no backwards-compatibility mode for breaking
   protocol changes. A main/major version mismatch must fail closed.
11. **Nomenclature:** Documentation and APIs should consistently distinguish a
    user principal, community membership/member record, device, and the
    conventional `member` role. The audit records ambiguity in the immutable
    target; cleanup belongs in later remediation work.
