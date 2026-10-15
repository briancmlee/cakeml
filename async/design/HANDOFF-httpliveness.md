# Handoff: HTTP liveness (spike/http-liveness)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/http-liveness`, branch
  `spike/http-liveness`, from `origin/spike/http-impl`; merged
  `origin/spike/async-closed-loop` (closed-loop world model, asyncLiveness).
  PR base: `spike/http-impl`.
- `async/http-liveness/`:
  - `asyncSWProgress`: the generic `server_with hf` from the handler's side
    (`sw_handler_view`: each accepted fd is served by its own handler on a
    view of the history; `sw_accept_progress`).
  - `asyncSWClosedLoop`: closed-loop facts for `server_with hf`
    (`sw_consistent`, `sw_fresh`, `sw_round_conn`, `sw_eof`, ...).
  - `asyncHttpMachine`: the HTTP handler as a three-state machine
    (HA/HB/HD), `hmachine_trans`, the accounting invariant `hmachine_inv`.
  - `asyncHttpDrain`: machine-level liveness `hmachine_live` (MAIN).

## How to build

    timeout 3000 arch -arm64 /bin/zsh -lc "cd async/http-liveness && ~/HOL/bin/Holmake -j2"

## Status

- DONE (headline): `http_prog_h_spec : ⊢ http_spec_h 3w demo_files http_prog_h`
  (async/http-liveness-h/asyncHttpSpecH): the header-tolerant program meets
  HttpSpecHeaders' whole spec, safety and liveness, with no extra
  hypotheses. Write-up `26-http-liveness-h.md`. Holmake green, no cheats,
  tag DISK_THM only.
- DONE (model level, strict HTTP): `closed_loop_http_liveness` etc.
  (async/http-liveness/), write-up `25-http-liveness.md`.
- Merged: origin/spike/http-headers, origin/spike/m4-liveness (both clean).
- Not done (archive/optional): program-level link for the strict HttpSpec.

## How to build (headline)

    timeout 3000 arch -arm64 /bin/zsh -lc "cd async/http-liveness-h && ~/HOL/bin/Holmake -j2"

## Assumptions made

See 25 §4. In addition: the machine-level theorem takes the environment
facts as hypotheses, and the closed-loop file discharges them from the
world model.

## Tool feedback

- hol-lsp: a looping `gvs`/`simp` keeps the server busy ("checking for
  Nm") with no hint which tactic loops; `goalState` at successive lines
  (walker times out at the looping step) located it. Causes found here:
  two assumptions `LENGTH rq = LENGTH (parse_all b)` and
  `parse_all b = rq ++ ...` together, and a pair of symmetric equations.
- `simp[GSYM APPEND_ASSOC]` loops (simp normalises with APPEND_ASSOC).
- hol-lsp `eval` has no theory context (Ancestors not loaded).
- After Holmake rebuilds, hol-lsp sometimes needs `restart` (twice) to
  load dependencies.
- `qspecl_then` quantifier order surprises; `I`, `T`, `K` are constants;
  `outcome`/`response`/`action` type names clash between HttpSpec and
  semantics.
- `Q.INST` on a polymorphic theorem fails with "No consistent parse";
  use `Q.GEN … |> Q.ISPEC …` for the polymorphic variable, then
  `Q.SPECL`. `Q.INST [‘M’ |-> ‘n + 2 * K + 2’]` needs a `: num`
  annotation (and `K` is the combinator constant).
- `drule_all` picks the first matching assumption; with several
  `closed_loop … = …` assumptions it often picks the wrong round. Explicit
  instantiation, or a wrapper lemma, avoids it.
- Two different `bytes`: HttpSpec's constant (bytes_def) and
  asyncM4EchoSafe's overload `MAP (n2w o ORD)`; they print identically, so
  rewrites silently fail to match. Normalise with `bytes_def`.
- `drule` on a theorem with free variables gives a ∀-quantified result in an
  unpredictable order; `Q.GEN … |> Q.ISPEC …` then `Q.SPECL`/`Q.INST` is
  reliable for polymorphic lemmas (hf, m).
- gvs expands Abbrevs; use fs to keep them.
- hol-lsp `goalState` was the most useful tool for finding looping
  tactics; `metis_tac` with many arithmetic-shaped assumptions
  (`a + j + 1` vs `a + (j + 1)`) loops.
