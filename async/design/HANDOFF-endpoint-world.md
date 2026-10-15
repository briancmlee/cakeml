# Handoff: endpoint socket world (endpoint-world)

Write-up and decisions for review: `35-endpoint-world.md`.

- Worktree `~/Programming/cakeml-worktrees/endpoint-world` (sparse `/async/`),
  branch `spike/endpoint-world` (from `spike/close-v2-sim`, merged with
  `spike/http-kv` for HttpSpecBodies and HttpKvSpec).
- `async/endpoint-world/`: statements only (spec first). Trusted:
  `endpointWorld`, `endpointFair`. Claims are definitions of propositions;
  proved so far: `rg_spec_mono`, `rg_spec_weaken`, `ep_*_spec_simple`.
- STOPPED for user review: no proofs of the claims until the statements are
  approved.

## How to build

    ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc \
      "cd async/endpoint-world && ~/HOL/bin/Holmake -j1"

(needs `async/spec` etc. built; Holmake builds the INCLUDES.)

## Gotchas

- Record fields shared with version 2 (`future`, ...): annotate `(w:eworld)`.
- Theory dependencies on HttpKvSpec come from the merge of `spike/http-kv`.
