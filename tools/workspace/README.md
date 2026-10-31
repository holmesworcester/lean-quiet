# The workspace

A browsable page of the project as an op tree: the target layout of `app/`,
drawn from main's real sources, beside `engine/` and `platforms/`.

- **One folder per op.** An op nests under the op it cites. Folders that group
  ops are families. The dotted name is the path: `community.channel.message.reaction`.
- **Eight file names**: `Op`, `Validate`, `View`, `Commands`, `Screen`, `Proofs`,
  `Tests`, `Family` (`.lean`). Every op has `Op`, `Validate`, `Proofs` and `Tests`;
  every folder with child folders has `Family`.
- **Placement by what a declaration names.** A law, command or screen lives in the
  common ancestor of the deepest ops it names; a folder sees its subtree and the
  ops it cites above it.

Each file shows the code from main that moves there, with where it is today.
`layout/tree.json` names the folders and where each of main's files goes;
`tools/plan.py` cuts `ops/community/Facts.lean` and `ops/connection/Types.lean`
by constructor and the shared intent and law files by declaration, and writes
`docs/OP_TREE.txt`. The requirements are in `docs/OP_WORKSPACE_REQUIREMENTS.md`.

The previews run one fixture store through every view (two clients only on
`network`), painted by a small Lean kernel compiled to WASM (`lean/Kernel.lean`),
whose validator you can edit and check in the browser.

## Run

Needs Lean 4.34.0, Node 24, Python 3, and Clang with a wasm32 backend.

```sh
mise run workspace:serve        # http://127.0.0.1:4173
mise run workspace:layout       # after changing layout/tree.json or the sources it cuts
mise run workspace:e2e          # the plan's tests and the browser tests (ci/local.sh workspace)
```

For tailnet access keep the server and add an HTTPS port without replacing an
existing mapping: `tailscale serve --bg --https=8443 http://127.0.0.1:4173`.
