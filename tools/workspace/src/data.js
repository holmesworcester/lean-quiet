export const proofs = [
  {
    id: "waits_for_dependency",
    name: "waits_for_dependency",
    title: "Wait for the message",
    description:
      "Without the required message, validation returns waiting for every other fixture input.",
    check: "Dependency available",
    target: "validate",
    threat: "ICTM.D6",
    code: "theorem waits_for_dependency (v m c s : UInt32) :\n    validate 0 v m c s = 0 := by\n  simp [validate]",
    hint: "Unfold the validator. Its first branch already decides this case.",
    tactic: "simp [validate]",
    goal: "v m c s : UInt32\n⊢ validate 0 v m c s = 0",
  },
  {
    id: "rejects_invalid_dependency",
    name: "rejects_invalid_dependency",
    title: "Reject an invalid dependency",
    description:
      "An arrived but invalid message never authorizes a reaction in this kernel.",
    check: "Dependency valid",
    target: "validate",
    threat: "ICTM.D6",
    code: "theorem rejects_invalid_dependency (m c s : UInt32) :\n    validate 1 0 m c s = 2 := by\n  simp [validate]",
    hint: "Simplification can resolve both fixed input branches.",
    tactic: "simp [validate]",
    goal: "m c s : UInt32\n⊢ validate 1 0 m c s = 2",
  },
  {
    id: "rejects_wrong_community",
    name: "rejects_wrong_community",
    title: "Keep community boundaries",
    description:
      "This concrete counterexample is rejected when the same-community guard is enabled.",
    check: "Same community",
    target: "validate",
    threat: "ICTM.A4",
    code: "theorem rejects_wrong_community :\n    validate 1 1 1 0 1 = 2 := by\n  decide",
    hint: "This is a decidable proposition over concrete inputs. Ask Lean to evaluate it.",
    tactic: "decide",
    goal: "⊢ validate 1 1 1 0 1 = 2",
  },
  {
    id: "accepts_valid_reaction",
    name: "accepts_valid_reaction",
    title: "Keep the honest path usable",
    description:
      "A valid fixture is accepted. Rejecting every input would not meet this property.",
    check: "Positive control",
    target: "validate",
    threat: "ICTM.H4",
    code: "theorem accepts_valid_reaction :\n    validate 1 1 1 1 1 = 1 := by\n  decide",
    hint: "The inputs are concrete; the proposition can be decided.",
    tactic: "decide",
    goal: "⊢ validate 1 1 1 1 1 = 1",
  },
  {
    id: "explicit_dark_overrides_os",
    name: "explicit_dark_overrides_os",
    title: "Respect explicit appearance",
    description: "An explicit dark preference wins for every OS input.",
    check: "Preference precedence",
    target: "theme",
    threat: null,
    code: "theorem explicit_dark_overrides_os (os : UInt32) :\n    theme 2 os = 1 := by\n  simp [theme]",
    hint: "Unfold theme and simplify the preference comparisons.",
    tactic: "simp [theme]",
    goal: "os : UInt32\n⊢ theme 2 os = 1",
  },
];
proofs.push({
  id: "rejects_nonmember",
  name: "rejects_nonmember",
  title: "Require an authorized author",
  description:
    "A missing membership fixture fact rejects the reaction for every community and policy input.",
  check: "Author authorized",
  target: "validate",
  threat: "ICTM.A2",
  code: "theorem rejects_nonmember (c s : UInt32) :\n    validate 1 1 0 c s = 2 := by\n  simp [validate]",
  hint: "Unfold the validator and simplify the membership check.",
  tactic: "simp [validate]",
  goal: "c s : UInt32\n⊢ validate 1 1 0 c s = 2",
});
export const threats = [
  {
    id: "ICTM.D6",
    title: "No content before authorization",
    family: "Causal authorization",
    status: "Partial demonstration",
    summary:
      "Do not surface or use content before the authorizing facts it requires are available.",
    proofs: ["waits_for_dependency", "rejects_invalid_dependency"],
    gaps: [
      "Connect the full engine judgement to all render queries.",
      "Cover persistence, replay, notifications, and every ingestion path.",
    ],
  },
  {
    id: "ICTM.A4",
    title: "Signatures and proofs cannot cross domains",
    family: "Authenticity and context",
    status: "Partial demonstration",
    summary:
      "An authenticated action must remain bound to its intended context; a reference from another community cannot supply authority here.",
    proofs: ["rejects_wrong_community"],
    gaps: [
      "Prove the general context-binding property over actual op bytes and signatures.",
      "Connect this scalar fixture to production constructors and validators.",
    ],
  },
  {
    id: "ICTM.H4",
    title: "Preserve honest operation",
    family: "Positive controls",
    status: "Partial demonstration",
    summary:
      "Security checks must retain usable, authorized paths. A system that rejects everything does not satisfy the model.",
    proofs: ["accepts_valid_reaction"],
    gaps: [
      "Cover every legitimate action and recovery path with realistic scenarios.",
    ],
  },
  {
    id: "ICTM.A2",
    title: "Verification and authorization precede effect",
    family: "Action authorization",
    status: "Partial demonstration",
    summary:
      "Before an action has a security-relevant effect, verify its signature and exact causal authority.",
    proofs: ["rejects_nonmember"],
    gaps: [
      "Membership is a fixture boolean here. Prove signature verification and exact action authority in the production path.",
    ],
  },
  {
    id: "ICTM.E3",
    title: "Exclude removed members from future keys",
    family: "Key confinement",
    status: "Open",
    summary:
      "Converged removal must exclude a removed member from replacement keys. It does not erase previously received secrets.",
    proofs: [],
    gaps: [
      "Key management is not implemented in this prototype.",
      "Historical validity alone does not establish future exclusion.",
    ],
  },
  {
    id: "ICTM.F11",
    title: "Keep user-created metadata confidential",
    family: "Application confidentiality",
    status: "Open",
    summary:
      "User-created names, text, filenames, metadata, and previews are confidential from QSS and third parties.",
    proofs: [],
    gaps: ["No encryption, QSS, or notification transport is modeled here."],
  },
];
