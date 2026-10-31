# Engagement-specific invariants

## Sigchain and authorization

1. Sigchain links are signed. Only data cryptographically covered inside the
   ciphertext is treated as link-body data. Every signature is verified and its
   signer is authorized for the action.
2. Signatures are domain separated and cannot be reused across identity
   challenges, sigchain actions, server actions, or any other domain.
3. Validators bind identifying link-body data, including
   `payload.device.userId`, to the signature over the ciphertext.
4. A user cannot create, replace, or update lockboxes they have not been granted
   authority over. The same complete-mediation rule applies to every
   admin-relevant action, which the audit must enumerate.
5. No user can promote themselves or another user to a role they do not already
   have authority to grant. In particular, `SET_METADATA` cannot make `ADMIN`
   self-assignable and only admins—not merely private-channel members—can add
   users to private channels. Every current admin is itself a member of every
   private channel and receives its complete history; the authenticated
   membership view and application authorization must reflect the same set as
   key distribution. This rule is specific to private channels and does not
   make admins participants in direct messages.

## Admission and server authority

6. Admission has one durable acceptance moment. Before graph, keyring, keys, or
   history are shared, the admitting member device or registered QSS has
   validated and signed the exact `ADMIT_MEMBER` or `ADMIT_DEVICE`, atomically
   appended it to the accepted sigchain, and durably persisted that state. A
   second online member is not required for QSS-only admission. A witnessed
   administrator-approval gate may be designed later as an optional community
   setting, but is not the current acceptance rule.
7. Observing or receiving an invite proof is insufficient for admission. The
   proof is cryptographically bound to possession of the admitted device ID
   keypair and cannot be replayed for another device or user.
8. Server actions are validated as server actions. Replaying proofs, harvesting
   signatures, substituting keys, or confusing action domains cannot give a
   server user-level authority or give a user server authority.

## General confidentiality, integrity, and authenticity

9. Confidential content is decryptable only by the intended current recipients
   under the documented history-sharing/removal semantics; metadata and error
   paths do not expose plaintext, keys, membership, or relationship information
   beyond the intended audience.
10. Replicated state, messages, membership, roles, profiles, channels, DMs,
    attachments, and keys cannot be created, changed, reordered, replayed, or
    deleted in a security-significant way without detection and authorization.
11. Every security-relevant object and action is attributable to the verified
    user/device/server identity that created it; displayed attribution never
    comes from an unsigned or differently signed field.
12. QSS, Firebase/APNS, and equivalent push infrastructure receive a wake-up
    free of user-created content: silent/data-only where supported, with a fixed
    generic iOS NSE envelope allowed where needed. A trusted on-device service
    fetches, authenticates, and decrypts notification history locally, then
    displays at least the authenticated message author and channel.
    Any lock-screen presentation follows the user's operating-system settings.

## Required follow-up scopes

- Derive and check specific invariants for private channels.
- Derive and check specific invariants for direct messages.
- Derive and check specific invariants for device linking.
- Explain concurrent and out-of-order grant/use behavior in local-first auth.
