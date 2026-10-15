# HANDOFF: blocking loop selecting on the live connections (spike/m4-blocking-live)

PR: https://github.com/briancmlee/cakeml/pull/46

The write-up is `async/design/24-blocking-runnable.md` §6 (the fix) and
§3 (the numbers).

## State

- Branch `spike/m4-blocking-live`, pushed, stacked on
  `spike/blocking-runnable` (PR #29).
- `async/m4-blocking-live/` holds 6 theories. `Holmake -j2` is green and
  there are no cheats.
  - `asyncM4LiveServer` (model): the Level 2 server's declared interest
    is contained in the listener plus the connections accepted more often
    than they hit EOF (`server_live`), by counting accepts and EOFs in the
    transcript. No freshness assumption.
  - `asyncM4LiveWorld`: asyncM4BlkWorld/Trace generalised. The loop
    selects on `sel h`, for any quiet Level 2 computation whose interest
    `sel` covers (`sel_covers`); two outcomes, echo transfer.
  - `asyncM4LiveEcho`: the live list (`lstep`, `live_of`), `quiet_secho`,
    `sel_covers_echo`.
  - `asyncM4LiveLoop`: the CakeML loop with a live list (`upd_live`,
    `step_l`, `run_l`), its specs, `run_l_two_outcomes`.
  - `asyncM4LiveMain`: `main = run_l ([3], [3], server 3)`,
    `echo_live_semantics`, `echo_live_spec`.
- `async/blocking-runnable/` gains `asyncEchoLiveExportScript.sml`
  (exports `echo_live.sexp`), the `build/echo_live` target, and a demo
  transcript `demo-transcript-live.txt`.

## Design choice (recorded under assumptions in 24 §6)

The loop prunes its select set from the transcript (accept adds, EOF
removes one). It does not read the computation's Level 2 interest out of
the CakeML value. Reading it would need the Async library (both/map) at
Level 2 in CakeML and the server re-proved over it. The proof still uses
the Level 2 interest: the pruned set covers it.

## Tool feedback

- `drule`/`irule` lose type information when the matched premise does not
  mention a polymorphic argument (e.g. the continuation `f` of a bind),
  which leaves goals that cannot be closed.
  - Fix: abbreviate the term from the goal (`qmatch_goalsub_abbrev_tac`)
    and instantiate explicitly with `qspecl_then`.
  - Alternatively, `MATCH_MP_TAC` sometimes works where `irule` says
    "No match".
- My own theorem names shadowed same-named theorems of an ancestor
  (`bind_interest_running`/`_continues` in asyncLevel2). That made REPL
  tests misleading. Use distinct names.
- A `[simp]` rule `(secho lfd).run = …` made goals stop matching specs
  stated with `(secho 3).run`. I dropped the attribute.
- `xapp_spec` sometimes instantiates the frame existentials itself and
  sometimes leaves them. The robust pattern is
  `rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> …`, rather than fixed
  `qexistsl` lists.
- Unconstrained `MAP w2n fds` in a spec gets a generic word size; annotate
  it as `word64`.
- `rw[]` looped on a small list lemma with equations between variables.
  Explicit `Cases_on` fixed it.
- This background session runs niced (background QoS). CPU measurements
  need the busy-loop calibration row (see 24 §3).
