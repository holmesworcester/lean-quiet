# Auditician threat model provenance and Lean applicability

The requirements specification adopts the owner-approved invariant-centric
threat model from the Quiet client 9.0.0 Auditician run in
`TryQuiet/quiet-private`. The model was approved on 2026-08-31 and clarified on
2026-09-01. The files under `auditician/` are byte-for-byte source snapshots.
They preserve the historical target, original invariant IDs, approved decisions,
and non-goals. They are intended requirements, not a claim that Quiet Lean meets
them.

- Source repository: `TryQuiet/quiet-private`
- Source branch at import: `codex/auditician-client-9.0.0`
- Source snapshot: `3a168fb7a36d4c0179b7e9f8f9b60afc803cbea9`
- Last model and review-decision change:
  `9c5d804c894d2a43290de8dc4758978903d6261e`
- Original paths: `security-audits/client-9.0.0-auditician/audit-state/THREATMODEL.md`
  and `security-audits/client-9.0.0-auditician/audit-context/` for the other inputs.
- [Pinned original threat model](https://github.com/TryQuiet/quiet-private/blob/3a168fb7a36d4c0179b7e9f8f9b60afc803cbea9/security-audits/client-9.0.0-auditician/audit-state/THREATMODEL.md)
- [Requirements and Lean applicability](../OP_WORKSPACE_REQUIREMENTS.md#threat-model-requirements)

## Source integrity

| Source snapshot | SHA256 |
| --- | --- |
| [THREATMODEL.md](auditician/THREATMODEL.md) | `989f61bb4379436ad93b48a161103585825488084796248c709817f6439c3fa9` |
| [ICTM-REVIEW-DECISIONS.md](auditician/ICTM-REVIEW-DECISIONS.md) | `196787433b16598b77db58e854436837d1b2028bc7bc8b5882ca78e769f77b8e` |
| [USER-INVARIANTS.md](auditician/USER-INVARIANTS.md) | `2fa374cfe5e8a7c91d0f11e946791d94bb4aba71a6c31dd759ddddc7093ee43c` |
| [QUINT-INVARIANTS.md](auditician/QUINT-INVARIANTS.md) | `1a9af59fd431c398769983f88636b76200bd16ac00654d4789d89d5ce7d008ae` |

## Reading the source snapshots

Read the model together with its approved review decisions. The model's original
references to `PROGRESS.md`, findings, and reports refer to the source audit tree;
those artifacts are not included here. Its user and Quint invariant inputs are
included. Older Quint assumptions are refined by the approved review decisions.

The source's claims concern its exact historical client, auth, and QSS revisions.
Original audit reports and executable regression probes are not Lean proofs.
Completion requires a checked theorem tied to the actual Lean runtime definitions
and the displayed source revision.

## Applying the model to Lean

Preserve the original IDs as `ICTM.A1` through the source's A-I families. For each
invariant, record its Lean owner, applicability, runtime targets, scenarios,
assumptions, proof obligations, evidence, and gaps. Planned features remain
planned; architecture replacements need an explicit mapping. New workspace
threats extend this model under separate identities.

The inspected Lean baseline uses mandatory admission approvals, while source
C3/C8 and review decision 9 use durable Option A admission with QSS-only support
and no second online member. Source B1 requires admin-issued member invitations;
the current Lean invitation validator requires an admitted issuer. Record these
policy differences for reconciliation; this import changes no runtime behavior.

Historical-validity proofs do not alone prove converged removal's future write,
connectivity, or key exclusion guarantees. Private channels, DMs, QSS, native
notifications, and transport guarantees must be assessed against what Lean
actually implements. In particular, preserve the original partial LOCAL attacker,
content-confidential user-created metadata, content-free push provider leg, and
explicit limits on removal and traffic-metadata confidentiality.

Keep the imported snapshots unchanged. Record later Lean-specific policy
revisions and their rationale in the requirements and evidence records, with a
link back to the affected source invariant.
