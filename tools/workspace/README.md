# The workspace

A browsable page of the project as an op tree: the folders and files of `app/`
as they are on disk, beside `engine/` and `platforms/`.

- **One folder per op.** An op nests under the op it cites. Folders that group
  ops are families. The dotted name is the path: `community.channel.message.reaction`.
- **Eight file names**: `Op`, `Validate`, `View`, `Commands`, `Screen`, `Proofs`,
  `Tests`, `Family` (`.lean`). Every op has `Op`, `Validate`, `Proofs` and `Tests`;
  every folder with child folders has `Family`.
- **Planned entries.** A file those rules require that is not on disk yet, and the
  ops and families `layout/tree.json` names that do not exist yet, are drawn in
  italics and marked planned.

Each file shows its code; a folder shows all of its files, long ones folded.
`tools/plan.py` reads every tracked file under `app/` and `layout/tree.json`,
which gives folders their summaries and previews and names the planned ones
(it names no code), and writes `docs/OP_TREE.txt`. Where each file of the old
layout went is `ci/optree-map.tsv`. The requirements are in
`docs/OP_WORKSPACE_REQUIREMENTS.md`.

The previews run one fixture store through every view (two clients only on
`network`), painted by a small Lean kernel compiled to WASM (`lean/Kernel.lean`),
whose validator you can edit and check in the browser.

## Run

Needs Lean 4.35.0, Node 24, Python 3, and Clang with a wasm32 backend.

```sh
mise run workspace:serve        # http://127.0.0.1:4173
mise run workspace:layout       # after adding or removing a file under app/, or changing layout/tree.json
mise run workspace:e2e          # the tree's tests and the browser tests (ci/local.sh workspace)
```

For tailnet access keep the server and add an HTTPS port without replacing an
existing mapping: `tailscale serve --bg --https=8443 http://127.0.0.1:4173`.
