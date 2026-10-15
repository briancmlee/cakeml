# Handoff: endpoint socket world (endpoint-world)

Write-up and decisions for review: `35-endpoint-world.md`.

- Worktree `~/Programming/cakeml-worktrees/endpoint-world` (sparse `/async/`),
  branch `spike/endpoint-world` (from `spike/close-v2-sim`, merged with
  `spike/http-kv` for HttpSpecBodies and HttpKvSpec).
- `async/endpoint-world/`. Trusted: `endpointWorld`, `endpointFair`.
  Claims are definitions of propositions.
- Round 2 (user decisions on PR #67: 5–6 approved, 1–4 parked):
  - proved: `endpointSemantics` (`evaluate_ffi_rel`,
    `semantics_prog_same_answers`), `same_answers_semantics`,
    `v2_instance_thm` (`endpointV2Sim`), `not_v1_instance`,
    `never_polls_bite`;
  - drafted: fd discipline for version 1 (pending decision);
    `endpointOpen` (`rg_spec_term`, `sys_spec`, `buffer_closure`).
- Next: `echo2_sym_equiv`. It needs Drains per tick in the constructed
  world, and prefix determinism (async-spike is writing a restricted
  same-answers lemma on top of `endpointSemantics`).
- `endpointV2Sim`'s relation `v2rel` (core + al_rel of the futures) is the
  template for the version-1 disciplined instance.

## How to build

    ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc \
      "cd async/endpoint-world && ~/HOL/bin/Holmake -j1"

(needs `async/spec` etc. built; Holmake builds the INCLUDES.)

## Gotchas

- Record fields shared with version 2 (`future`, ...): annotate `(w:eworld)`.
- Theory dependencies on HttpKvSpec come from the merge of `spike/http-kv`.
- `bytes_fds_def` loops under simp: use `Once`, or a lemma for `bytes_fds []`.
- Several theories define `ticks_def`, `step_ok_def`, ...: qualify them
  (`ffiSpikeSocketFairTheory.ticks_def`).
- Type-changing record updates (`s with ffi := f2`): state helper lemmas
  with `∀f : 'b ffi_state`, or simp will not use them.
- `semantics_prog_def`: use `semanticsTheory.semantics_prog_def`.
- LUPDATE lemmas: state them first-order (`LUPDATE c j l`), since higher-order
  `irule` patterns fail.
