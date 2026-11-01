# Quint invariant input

Source: `formal/quint-auth-model:packages/quint-auth-model/INVARIANTS.md` at
commit `bdba8d822353504f6ba33145541e1cb4703c9c9b`.

The source models the earlier plaintext-authorship production design. Its
counterexamples are hypotheses/regression targets for this client 9.0.0 audit;
they are not copied forward as findings without validation against the exact
target revisions.

## Security invariants

1. **Authenticity**: no link takes effect unless its cryptographic signer speaks
   for the claimed author.
2. **No silent drop**: a validly admitted member who was not explicitly removed
   remains a member in converged state.
3. **No split brain**: no user is simultaneously a member and a removed member.
4. **Admin authorization**: every non-founder admin was granted that authority
   by an authorized admin; metadata cannot redefine an ordinary role into a
   self-assignable admin role.
5. **No stuck graph / progress under merge**: no reachable or honestly produced
   graph causes reduction to throw, including concurrent grant/use/removal.
6. **Key availability**: every current member can decrypt all surfaced content
   they are intended to receive, including shared history.
7. **Forward secrecy after removal**: a removed, non-readded member cannot read
   content that is not causally before removal.
8. **Member-key confinement**: no non-member, including a silently dropped
   invitee, can decrypt current members' surfaced content.

## Explicit non-goal

Removal is forward-only. Content already replicated before removal is not
retroactively erased and may remain visible. The audit must not misreport this
as an implementation defect, but must check the boundary between old and new
content and whether user expectations are accurately set.

## Positive control

A benign linear all-honest history must satisfy every safety invariant. This
prevents vacuous success in which nothing is admitted, surfaced, or reducible.

## Quiet-layer regression invariants reported as holding in the source model

- Membership admission gates member-only activity.
- Message attribution is strongly authenticated.
- Channel metadata ownership and immutability are enforced.
- Channel authorization and private-channel read confidentiality are enforced.
- Profile and notification-token updates are self-owned.
- Community metadata changes are owner/admin-only.

The current target must be checked independently for all of the above.

For this audit, the owner clarification in `ICTM-REVIEW-DECISIONS.md` defines
every current community admin as a participant in every private channel. Thus
private-channel confidentiality excludes ordinary nonparticipants and
infrastructure, not admins; admin membership must still be represented
consistently in authenticated participant state, application authorization,
and key distribution. Direct messages do not inherit this admin-participation
rule.
