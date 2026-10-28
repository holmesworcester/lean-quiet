# Lean Quiet

Quiet's engine, op families, apps and their proofs in Lean 4, in one
repository. Every part builds against the others at the same commit.

| directory | what |
|---|---|
| `engine/` | the op engine (store, judging, lists, sync, the node and its TCP runner), the Community and Connection families, the Rust crypto (`engine/native/crypto`) and their laws |
| `app/` | the Quiet app (`Quiet/`), its headless twin and tests, and its Android and iOS shells |
| `qr/` | QR encoding and decoding, and pictures (QOI) |
| `mdns/` | mDNS/DNS-SD discovery |
| `net/` | the connection bootstrap model (being ported to this engine; not yet gated) |

Each directory is its own Lake package with its own `mise.toml` tasks;
`mise run check` here runs every gated part. The layout this repository
is moving to (engine for everything that holds for every op type; ops
by family and domain; platforms by name) is
[engine/docs/LAYOUT.md](engine/docs/LAYOUT.md); sync's design is
[engine/docs/SYNC.md](engine/docs/SYNC.md).

The history of each part is its former repository's (lean-engine,
lean-quiet, lean-qr, lean-mdns, lean-net), rewritten into its directory;
their other branches are kept as `import/<dir>/<branch>`.
