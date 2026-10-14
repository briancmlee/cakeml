# Handoff: async semantics spike (M1 design spike)

Written by the first agent when the coordinator asked it to stop. A fresh agent
should be able to continue from this file alone. The original task brief, which
lists the deliverables, the user's priorities and the git/PR rules, is in the
coordinator's prompt. In short:

- deliverables: `async/model/` (HOL-only prototype, Holmake, no cheats),
  `async/design/01-semantics.md` (the design note) and `async/README.md`;
- a PR from `spike/async-semantics` against `async-io` on `briancmlee/cakeml`;
- mark the proposed user-owned main theorems with `(* MAIN: ... *)`.

Worktree: `~/Programming/cakeml-worktrees/async-semantics`, branch
`spike/async-semantics`, based on `async-io` (f73189499).
Don't build in `~/Programming/cakeml`: another agent is using it.

## 1. Build status (at the time of handoff)

- `async/model/asyncCoreScript.sml`: the committed part built OK. The
  **uncommitted tail** has since been committed as WIP (the section headed
  "More about freeze" and everything after it). It has **not been verified to
  build**. The last Holmake run hung for more than 10 minutes inside
  `asyncCoreTheory`, almost certainly in `first_prefix_cong`. The current
  script ends that proof with `TRY (metis_tac[]) >> CCONTR_TAC >> ‘x < x' ∨ x' < x’
  by decide_tac >> metis_tac[]`, and the `TRY (metis_tac[])` (or the final
  metis) probably loops.
  Interactively, after `rpt strip_tac >> Cases_on ‘first_prefix P h’ >> Cases_on ‘first_prefix Q h’ >> gvs[first_prefix_SOME, first_prefix_NONE]`
  only ONE goal remains: `x = x'`, with hypotheses that both are minimal
  prefixes (`Q (TAKE x h)`, `∀k. k < x ⇒ ¬Q (TAKE k h)`, the same for x', and
  `∀k. k ≤ LENGTH h ⇒ (P (TAKE k h) ⇔ Q (TAKE k h))`). The NONE/SOME cases are
  already closed by gvs. **Fix**: drop `TRY (metis_tac[])` and use
  `>> CCONTR_TAC >> ‘x < x' ∨ x' < x’ by decide_tac >> res_tac` (or
  `>> spose_not_then assume_tac >> Cases_on ‘x < x'’ >> res_tac >> gvs[]`).
  The other new core lemmas (`new_actions_cong`, `par_views_cong`,
  `par_actions_cong`, `freeze_agree`, `freeze_not_done`, `skip_results_SNOC`,
  `par_views_SNOC_exists`, `par_views_world`) are untested.
- `async/model/asyncLevel1Script.sml`: everything in it built and was
  committed in 24bd630bb (before the core WIP was added). It depends on core,
  so it is blocked until core builds again.
- No `cheat` anywhere. `async/model/Holmakefile` is empty: the repo-root
  `holproject.toml` supplies paths. Holmake scans about 314 directories every
  run and prints an harmless `.hol_preexec` line from HOL's arm8 example.
  About 7 s of overhead per run.

## 2. Files

- `async/model/asyncCoreScript.sml` (theory `asyncCore`). This is the shared
  machinery, which doesn't depend on what a "result" is:
  - `snapshot = <| ready : 'e set ; now : num ; results : 'r list |>`
  - `outcome = <| actions : 'act list ; result : 'x |>`
  - `first_prefix P h`: the length of the shortest prefix of h satisfying P.
    Lemmas: `_SOME`, `_NONE`, `_exists`, `_APPEND`, `_SNOC`, `_TAKE`,
    `_TAKE_NONE`.
  - `new_actions acts h`: the actions emitted in round `LENGTH h`. Lemmas:
    `_NIL`, `_SNOC`, `_prefix`.
  - `skip_results k h`: drops the first k results of h's first snapshot.
    Lemmas: `_0`, `LENGTH_`, `_skip_results`, `TAKE_`, `DROP_`, `_APPEND`.
  - `par_views acts1 acts2 h`: the pair of views for running two computations
    side by side. It is defined by recursion through FRONT/LAST. Lemmas:
    `_NIL`, `_SNOC`, `LENGTH_par_views`, `par_views_TAKE`.
  - `par_actions acts1 acts2 h`: per round, the left side's new actions, then
    the right side's. Lemmas: `_NIL`, `_SNOC`, `par_actions_grows`.
  - `freeze is_done m h`: m until it is first done, frozen afterwards. Lemma:
    `freeze_SNOC`.
  - Guarded recursion:
    - `agree_below n m1 m2` (equal on histories shorter than n);
    - `guarded G`, `nonexpansive G`, `contractive body`;
    - `fix body p h = FUNPOW body (SUC (LENGTH h)) ARB p h`.
    - Proved: `FUNPOW_agree`, `fix_agree_FUNPOW`, **`fix_unfold`** (MAIN:
      `contractive body ⇒ fix body = body (fix body)`), **`fix_unique`** (MAIN:
      `contractive body ∧ body r = r ⇒ r = fix body`), `closed P`,
      `fix_preserves` (`contractive body ∧ closed P ∧ P m0 ∧ (∀r. (∀p. P (r p)) ⇒ ∀p. P (body r p)) ⇒ ∀p. P (fix body p)`),
      `nonexpansive_const`, `nonexpansive_call`, `guarded_const`,
      `guarded_nonexpansive`.
  - WIP (described above): congruence lemmas and freeze lemmas.
- `async/model/asyncLevel1Script.sml` (theory `asyncLevel1`), all proved:
  - definitions: `log_of`, `wf`, `first_done m h x` (m's result first appears
    after exactly h), `return`, `first_some`, `wait`, `emit`, `bind`, `map`,
    `left_view`, `right_view`, `par_log`, `both`, `race`,
    `choose = freeze (λout. out.result ≠ NONE) (race m1 m2)`,
    `never = wait (λs. NONE)`;
  - theorems:
    - `wf_SNOC_actions`, `wf_SNOC_finished`;
    - **`wf_actions_grow`** (MAIN): `wf m ∧ h1 ≼ h2 ⇒ (m h1).actions ≼ (m h2).actions`;
    - **`wf_finished_stays`** (MAIN): `wf m ∧ (m h1).result = SOME x ∧ h1 ≼ h2 ⇒ m h2 = m h1`;
    - `wf_unfinished_before`, `first_prefix_done_SOME`,
      `first_prefix_done_APPEND`, `history_split`, `first_done_finished`,
      `first_done_NIL`;
    - **`bind_running`** (MAIN), `bind_running_wf`;
    - **`bind_continues`** (MAIN): `first_done m h1 x ⇒ ∀f h2. bind m f (h1 ++ h2) = let next = f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2) in <| actions := (m h1).actions ++ next.actions; result := next.result |>`;
    - `bind_continues_actions`/`_result`, `bind_before_first_done`,
      `first_done_bind`, `new_actions_bind_after`, `new_actions_bind_at`
      (needs wf m), `bind_running_TAKE`, `bind_unfinished_after`;
    - **`bind_left_identity`** (MAIN): `bind (return x) f = f x`;
    - **`bind_right_identity`** (MAIN): `wf m ⇒ bind m return = m`;
    - **`bind_assoc`** (MAIN): `wf m ⇒ bind (bind m f) g = bind m (λx. bind (f x) g)`.

    The proof of bind_assoc is long but commented by case.
- `async/model/.gitignore`: ignores build products.
- Not written yet: `asyncLevel2Script.sml`, `asyncEchoScript.sml` (or
  examples), `async/design/01-semantics.md`, `async/README.md`.

EVAL sanity checks done by hand (not yet in a script). On snapshots with
results `[1]`, `[2]`:
- `bind (emit "a") (λx. bind (emit "b") (λy. return (x,y)))` gives
  `<| actions := ["a";"b"]; result := SOME (1,2) |>`;
- the same program after one snapshot gives actions `["a";"b"]`, result NONE;
- `both (emit "a") (emit "b")` on `[s [1;2]]` gives `SOME (1,2)`;
- `both (bind (emit "a") (λx. emit "c")) (emit "b")` on `[s[1;2]; s[3]]` gives
  actions `["a";"b";"c"]` and `SOME (3,2)`;
- `choose (wait ready-3) (emit "b")` on one snapshot with ready {3} gives
  `SOME 3` with actions `["b"]`.

EVAL needs `load "stringTheory"` for string literals. Put these in an examples
theory as `Theorem ... = EVAL ...` or `Theorem foo: ... Proof EVAL_TAC QED`.

## 3. Decisions and rationale (for the design note)

1. **Representation.** A computation is a plain HOL function
   `m : ('e,'r) snapshot list -> ('act, 'x) outcome`. The history is a list
   of snapshots, chronological with the oldest first. The empty history is the
   first poll, round 0. At Level 1, `'x = 'a option`. This follows the user's
   Level 1 `'w list -> 'a option`, extended with the action log. The
   step/resumption type was rejected (see the brief), as were interaction
   trees, which need coinduction.
2. **Snapshot = readiness + time + responses**, following the user's words:
   `ready : 'e set`, `now : num`, `results : 'r list`. `wait p` sees the whole
   snapshot, but because of routing its `results` are always `[]` in a
   well-behaved world.
3. **Action log and responses (request tagging), the key new decision.**
   - Every action emitted in round n gets exactly one response, which arrives
     in snapshot n+1's `results`, at the action's position within round n's
     batch. Tags are therefore positional, with no ids.
   - Combinators route responses down the program tree:
     - `bind`: when m finishes in round n, the continuation starts in round n,
       and the first `|new actions of m in round n|` results of the next
       snapshot are dropped (`skip_results`), because they belong to m.
     - `both`/`choose`: the left side gets `TAKE k1`, the right side gets
       `DROP k1` of each snapshot's results, where k1 is the left side's batch
       size in the previous round (`par_views`).
   - This is compositional, needs no global ids, needs no extra parameters,
     and keeps the monad laws exact equalities.
   - It is the pure counterpart of the implementation delivering each result
     straight to the requester's ref cell. That should make the CF refinement
     relation natural.
   - Rejected alternatives:
     - user-chosen tags, because freshness would become a load-bearing
       discipline;
     - address/path parameters, which break the exact left-identity law (the
       address changes) and grow without bound in loops;
     - keying by (round, action), which collides when two tasks issue the same
       read in the same round;
     - global log indices, because sub-computations can't know their offset.
   - The right side gets `DROP` rather than `TAKE k2 (DROP k1)` so that laws
     like `both (return x) m = map (λy. (x,y)) m` hold exactly even when the
     world sends extra responses.
   - World assumption, to be named in M3: each snapshot carries exactly one
     response per action of the previous round.
4. **emit waits for its response.** `emit a` emits a in its first round and
   finishes at the next snapshot with `oHD s.results`. If the world delivered
   no response, it stays unfinished forever, which is still well-formed. So
   the minimal primitives are `wait` and `emit`. A fire-and-forget send costs
   one round.
5. **bind's snapshot convention.** The continuation starts in the *same* round
   in which m finished, so `return`, `map` and further pure steps cost nothing
   and emits happen immediately. It only *sees* snapshots after that point.
   So a `wait`/`emit` in the continuation needs a fresh snapshot. This matches
   the 2024 OCaml prototype's spirit, where the 2024 `bind` deferred the
   continuation to the next poll.
6. **Recursion rule.** Use guarded recursion via `fix`/`contractive`
   (core): a body is OK if each recursive call is reached only after something
   that needs at least one snapshot, which formally means
   `(m []).result = NONE` for the first computation in a bind. Then r on
   histories of length n depends only on r on lengths < n, and `fix` is the
   unique solution (`fix_unfold`, `fix_unique`). Loops are parameterised
   (`'p -> computation`), so a loop can carry state such as a buffer. The echo
   loop `echo fd = bind (wait readable) (λ_. bind (emit (Read fd)) (λres. case res of Data s => bind (emit (Write fd s)) (λ_. echo fd) | WouldBlock => echo fd | Eof => return ()))`
   is guarded because `wait` and `emit` never finish on `[]`. The CF side
   (POSTd) proves the CakeML loop refines `fix`.
7. **Well-formedness** (`wf`, one-step): the log only grows, and once
   finished nothing changes. `choose` is made well-formed by `freeze`.
8. **Equality notion.** The laws are *exact equalities of functions*. Right
   identity, associativity and `map_as_bind` need `wf m` (frozen after
   finishing, logs monotone). No equivalence relation was needed.
9. **choose** has left priority when both finish in the same round. The loser
   is abandoned and its in-flight responses are lost. *Finding for the
   design note*: cancelling an in-flight read loses data. The library should
   keep long-lived reader tasks with buffers rather than `choose` against a
   raw read.
10. **Level 2 (planned, not written).**
    - `status = Done 'a | Waiting ('e set)`, with outcome result
      `('a,'e) status`.
    - `erase` maps `Done x` to `SOME x` and `Waiting _` to `NONE`, keeping the
      actions.
    - `wait_on e p` looks only at snapshots where `e ∈ s.ready`, i.e.
      `erase (wait_on e p) = wait (when_ready e p)`.
    - `emit2` is `Waiting ∅` until the response arrives.
    - In `bind2`/`both2`/`choose2`, the waiting set is the union of the sets of
      the unfinished sides (`waiting_set (Done _) = ∅`).
    - `quiet m ⇔ ∀h s. DISJOINT (waiting_set (m h).result) s.ready ∧ s.results = [] ⇒ m (h ++ [s]) = m h`
      (no progress unless a declared event is ready or a response arrived).
      `wf2 m ⇔ wf (erase m) ∧ quiet m`.
    - Prove that erase commutes with each combinator, including
      `fix` (via `fix_unique`: erase∘fix F2 is a fixpoint of F1), transfer the
      laws, and prove that every combinator preserves wf2. The escape hatch is
      an `Always` event in the concrete world model, plus the lemma
      `(∀s. MEM s h ⇒ e ∈ s.ready) ⇒ erase (wait_on e p) h = wait p h`.
    - The waiting sets and Level 2 status use the same `outcome` record and
      the same `par_views`/`new_actions`/`freeze`/`first_prefix` machinery.

## 4. Dead ends and HOL gotchas found

- `F` can't be a variable name (it means false); use `body`. `o` can't be a
  lambda variable (it is composition); use `out`.
- **`++` is left-associative** in HOL4, and simp's normal form is left-assoc:
  `h1 ++ q ++ [s]` means `(h1 ++ q) ++ [s]`. Rewriting with
  `bind m f (h1 ++ h2)` didn't fire on `h1 ++ q ++ [s]`. Instantiate h2 by
  hand and simp both sides.
- `drule` plus a ∀-conclusion whose type variables are free (e.g. `∀f.` in
  `bind_running_wf`) fails to rewrite: the assumption is ASSUMEd, so its type
  variables can't be instantiated. Robust patterns:
  - `qpat_assum ‘first_done m h1 x’ (fn th => simp[MATCH_MP bind_continues th])`;
  - conditional rewriting such as `simp[bind_running_wf]`;
  - `irule` on a `by` subgoal.
  Don't use `Q.INST` on theorem variables.
- `by`-subgoals mentioning polymorphic constants that no goal variable pins
  down (e.g. `‘first_done (return x) [] x’`) get fresh type variables.
  `bind_left_identity` was proved by unfolding the definitions instead.
- `irule` on a theorem whose conclusion is `∀n. n ≤ … ⇒ …` treats the `n ≤ …`
  as an antecedent. Do `rpt strip_tac` first.
- `gvs`/`fs` can loop when assumptions like `skip_results k h2 = p1 ++ p2`
  and `TAKE j (skip_results k h2) = p1` coexist. Use targeted
  `SUBST_ALL_TAC`/`REWRITE_TAC`, and remove `Abbrev`s with
  `REWRITE_RULE[markerTheory.Abbrev_def]`.
- `snapshot_component_equality` isn't SML-bound inside its own theory; use
  `theorem "snapshot_component_equality"`. In later theories the plain name
  works (`outcome_component_equality`).
- The `Theory X / Ancestors / Libs` header style is used, as in recent CakeML.
  No `export_theory` is needed.

## 5. Next steps (in order)

1. Fix `first_prefix_cong` (above), then get the rest of the core WIP
   building. Watch for `pairarg_tac` and FST/SND issues in
   `par_views_cong`/`par_actions_cong`. In `freeze_agree`, the goal after
   `CASE_TAC` needs `LENGTH (TAKE x h) < n`.
2. Level 1 remaining lemmas. Planned statements:
   - `map_id`, `map_map`, `map_as_bind` (wf), `bind_map` (no wf needed).
   - `first_some_SNOC`, `wait_result_NONE` (`(wait p h).result = NONE ⇔ EVERY (λs. p s = NONE) h`),
     `wait_result_first`, `wait_needs_snapshot`/`emit_needs_snapshot`
     (`(_ []).result = NONE`).
   - wf preservation: `wf_return`, `wf_wait`, `wf_emit`, `wf_never`,
     `wf_map`, `wf_bind` (case split on `history_split m (h ++ [s])`, then on
     h2 by SNOC_CASES, using `skip_results_SNOC`), `wf_both` (children frozen
     ⇒ `new_actions` = [] via `new_actions_SNOC`, using `par_views_SNOC_exists`),
     and `wf_choose` via a generic `wf_freeze` (needs only monotone actions,
     from `freeze_SNOC` + `freeze_not_done` + `par_actions_grows`).
   - `wf_closed` and `wf_fix` (`irule fix_preserves`, m0 = `never`).
   - Characterisations:
     - `both_result` (`= SOME (x,y) ⇔` both sides finished on their views);
     - `both_actions_SNOC` (per round, left then right);
     - `views_world` (from `par_views_world`);
     - `choose_result` (first n where race finished, via `freeze_def` +
       `first_prefix_SOME`);
     - `choose_finished` (wf sides: finished ⇔ one side finished; needs
       `par_views_TAKE` and `wf_unfinished_before`);
     - optionally `both_return_left : both (return x) m = map (λy.(x,y)) m`.
   - Agreement lemmas:
     - `bind_agree` (agree_below n on m and on each f x ⇒ agree on bind);
     - `bind_agree_guard` (`(m []).result = NONE` ⇒ agree_below (n+1); the
       first finish point is ≥ 1, so the continuation sees < n snapshots);
     - `map_agree`, `both_agree`, `race_agree`, `choose_agree` (via
       `freeze_agree`, `par_views_cong`, `par_actions_cong`).

     Then the guarded/nonexpansive corollaries, with MAIN = the recursion
     rule `bind_guarded`:
     `(m []).result = NONE ∧ (∀x. nonexpansive (λr. G x r)) ⇒ guarded (λr. bind m (λx. G x r))`.
3. `asyncLevel2Script.sml` as in §3.10. MAIN statements:
   - `erase_*` commute (return, wait_on, emit, bind, map, both, choose, fix);
   - `wf2_*` preservation;
   - `no_progress_without_ready_event`:
     `wf2 m ∧ (m h).result = Waiting E ∧ DISJOINT E s.ready ∧ s.results = [] ⇒ m (h ++ [s]) = m h`;
   - the transferred laws, e.g.
     `wf2 m ⇒ erase (bind2 (bind2 m f) g) = erase (bind2 m (λx. bind2 (f x) g))`.
4. `asyncEchoScript.sml`:
   - concrete types: `event = Readable num | Writable num | Timer num | Always`,
     `action = Read num | Write num string`,
     `response = Data string | WouldBlock | Eof | Written`;
   - `echo_body`, a `contractive echo_body` proof (unfold `contractive_def`/
     `guarded_def`, apply `bind_agree_guard`, `bind_agree`, and case on the
     response);
   - `echo = fix echo_body`, `echo_unfold`, `wf_echo`;
   - Level 2 `echo2` with `wf2` (never busy-polls) and `erase echo2 = echo`;
   - EVAL examples on concrete histories, e.g. read "hi" then emit
     `Write 0 "hi"`. EVAL of `fix` unfolds `LENGTH h + 1` times from `ARB`;
     check that ARB is never forced.
5. Write `async/design/01-semantics.md` and `async/README.md` (outline in §7),
   commit in logical steps, push, and open the PR as the brief specifies.

## 6. Research findings (open problem 3), from an Explore subagent

Paths are relative to the repository root.

- **Non-termination CF (ITP 2019)**
  - `characteristic/cfHeapsBaseScript.sml`:
    `res = Val | Exn | FFIDiv … | Div (io_event llist)` (l.102) and
    `POST Qv Qe Qf Qd` (l.180), with binders `POSTv/POSTe/POSTf/POSTd`,
    `POSTve`, `POSTvd`, `POSTed`. Heap parts: `FFI_part`, `FFI_full`,
    `FFI_split`.
  - `characteristic/cfAppScript.sml` `evaluate_to_heap_def`: the `Div io` case
    means every clock times out and `io` is the `lprefix_lub` of the
    io_events.
  - `characteristic/cfDivScript.sml`:
    - `repeat_clos`/`repeat_v` (l.~4032);
    - `repeat_POSTd`;
    - `repeat_POSTd_one_FFI_part` (l.3772);
    - **`repeat_POSTd_one_FFI_part_FLATTEN`** (l.4600), the most usable: the
      conclusion is `Q (LFLATTEN (LGENLIST (fromList o events) NONE))`;
    - the Recclosure rules `IMP_app_POSTd` (l.3711),
      `IMP_app_POSTd_one_FFI_part_FLATTEN` (l.4830) and `tailrec_POSTd`
      (l.1945);
    - tactics in `characteristic/cfDivLib.sml`: `xcf_div`, `xcf_div_rule`,
      `xcf_div_FFI_full`.
  - Examples:
    - `examples/divScript.sml`: `yes_spec_lemma`, `catLoop_spec`, and
      `myRepeat_spec`, a higher-order repeat whose step spec is carried in
      `&(...)`;
    - `examples/filterProgScript.sml`: `forward_matching_lines_div_spec`
      l.828, and `semantics_diverge_filter` l.1486, which builds
      `semantics_prog … (Diverge events)` by hand.
  - There is **no generic POSTd → Diverge whole-program theorem**:
    `cfMainScript` has only `call_main_thm2` (POSTv) and `_ffidiv`, and
    `basis_ffi` has no POSTd `whole_prog_spec`. M3 will need to add one.
- **fsFFI** (`basis/fsFFIScript.sml`, `basis/fsFFIPropsScript.sml`,
  `basis/TextIOProofScript.sml`):
  - `IO_fs` has `inode_tbl`, `files`, `infds`, `numchars : num llist` and
    `maxFD`.
  - `numchars` is the oracle's nondeterminism: read returns
    `MIN n (… SUC strm)`, and write may write 0.
  - Fairness is `live_numchars ns ⇔ ¬LFINITE ns ∧ always (eventually (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0)) ns`
    (l.187), which `liveFS`/`wfFS` build on.
  - `encode` uses `cfFFIType`; the FFI part is `fs_ffi_part = (encode, decode, [(«open_in»,…),…])`.
  - `STDIO fs = (SEP_EXISTS ll. IOFS (fs with numchars := ll)) * …` hides the
    schedule.
  - Recipe to reuse for sockets/time: a state record with an llist schedule,
    a `live_*` always-eventually predicate, encode/decode, a `*_ffi_part`,
    and an IOx hprop that hides the schedule existentially.
- **basis_ffi** (`basis/basis_ffiScript.sml`):
  - `basis_ffi_oracle ext` falls through to `ext`;
  - `basis_proj1`/`basis_proj2` list `cl_ffi_part`, `fs_ffi_part` and
    `runtime_ffi_part`;
  - other names: `extract_fs*`, `IOFS_precond`, `STDIO_precond`,
    `parts_ok_basis_st`, `whole_prog_spec*`, used by
    `basis_ffiLib.prove_sem_thm`.
  - Adding a component means touching all of the following: the state tuple,
    the oracle, `is_basis_ffi_name`, the projections, the length/part defs,
    `oracle_parts`, `parts_ok_basis_st`, a `*_precond` lemma, an
    `FFI_part_hprop` lemma, every `whole_prog_spec*`, the `IMP_STDIO*`
    lemmas, `basis_ffiLib`, and `basis_ffi.c`.
  - archive/2024-project:
    - new `basis/tsFFIScript.sml`
      (`IO_ts = <| latest_time; microseconds_elapsed : num -> int option |>`,
      `ts_ffi_part`, `ffi_now`);
    - `TimeProgScript.sml` and `TimeProofScript.sml` (`TIME ts`,
      `now_spec`);
    - `cfFFIType` gained `Option`;
    - the basis state became `(cls,fs,ts)`, and every `whole_prog_spec*`
      gained `* TIME ts`;
    - the C side gained `ffinow`, `ffiselect`, `ffiopen_listenfd`,
      `ffiaccept` and others.
    - There is no monotonicity or fairness predicate for time.
- **CF for higher-order and stateful code**:
  - `basis/ListProofScript.sml` `app_spec` takes the closure spec as a premise
    with an indexed effect invariant `eff`. The Array `app` specs follow the
    same style.
  - The translator's `-->` (`ml_translatorScript.sml`, `Arrow`/`AppReturns`)
    is pure only.
  - `basis/TextIOProofScript.sml` `sub_spec_def` (l.7190) is the existing
    pattern for "returned closure satisfies an app spec", carried as a pure
    fact `&(sub_spec f …)`. `divScript.myRepeat_spec` is similar.
  - Refs: there is no refinement for closures stored in refs. A promise ref
    holding a callback whose spec mentions the same ref needs something new,
    such as a stratified invariant or step-indexing. **This is a major risk
    for the CF `FUTURE m h v` plan and should go in the risks section.**
- **2024 work**:
  - `unverified/async/PromisedCake.cml` is a callback/promise event loop with
    a global job list and `select`. `promises.cml` is an earlier version.
  - `unverified/async/pure_async/lib/promise.ml` is the pure poll model
    (`'a t = World.t -> 'a option`, with a cached `bind`/`create`).
  - `examples/promiseScript.sml` is an incomplete monadic-translator attempt.
  - There is no `callbacks.cml`.

## 7. Outline for 01-semantics.md and README

The design note should follow the brief's list:
- the model at both levels, with key definitions quoted from the scripts;
- decisions with alternatives (§3), including why step/interaction trees were
  rejected;
- the recursion rule (§3.6) and echo;
- outputs and responses (§3.3–3.4), with a worked example of routing (the
  EVAL examples in §2);
- the ownership discipline as an optional M3 theorem (under ownership, a read
  issued after readiness never returns WouldBlock);
- the world model:
  - fds as byte streams with schedule llists, listeners, a clock;
  - snapshot = ready + now + results;
  - named assumptions: one response per action, monotone clock, and liveness
    in the style of `live_numchars`;
  - non-vacuity via a concrete always-ready schedule;
- the refinement plan:
  - `FUTURE m h v` and CF specs for poll, return, wait, emit, bind, both,
    choose and fix;
  - the event loop with `repeat_POSTd_one_FFI_part_FLATTEN`;
  - the hard parts: closures in refs, the missing POSTd whole-program
    theorem, adding a basis_ffi component;
- findings (§6), the MAIN list, an M2 sketch (scheduler step function, tasks
  not lost, progress, results match M1, a Level 2 select-blocking theorem),
  risks, and decisions needed from the user. Candidate decisions:
  - positional response routing;
  - emit waiting for its response;
  - the same-round continuation convention;
  - left priority and loss of responses in `choose`;
  - laws that require `wf`.

The README should be short: what is here, how to build
(`~/HOL/bin/Holmake` in `async/model`), and the status.

## 8. Tool feedback

- I didn't have the hol-lsp MCP tools. I used the CLI
  (`arch -arm64 ~/Programming/hol-lsp-mcp/.venv/bin/python -m hol_lsp_mcp goalState FILE LINE COL`
  with `HOL_BIN` set).
  - It worked, about 4 s per call, but a position inside a tactic sometimes
    showed the state before that tactic rather than after it.
  - Each call recompiles, and there is no persistent session to step through
    tactics.
- The most productive loop was:
  1. run Holmake;
  2. on failure, take the auto-saved `*.dumpedheap`;
  3. run `hol --holstate=<heap> --zero < script` with `g`/`e` steps.

  Helpers are in `/tmp/holtest/`: `mk.sh` (filtered Holmake), `try.sh HEAP N`
  and `goal.sh`. They aren't committed and are trivial to recreate.
- Friction:
  - Holmake scans about 314 directories per run because of the repo's
    `holproject.toml`.
  - A looping metis/gvs hangs Holmake silently, so a per-theorem timeout
    would help.
  - The Bash tool runs under Rosetta, so everything needs `arch -arm64`.
