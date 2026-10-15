# 11: cfDiv's FFI-part loop rules in worlds with several FFI parts

Branch `spike/cfdiv-multipart`, stacked on `spike/socket-model` (PR #11).
Code: `async/ffi-spike/ffiSpikeDivMulti{Script,Lib}.sml` (the rule) and
`ffiSpikeSocketLogDivScript.sml` (the demo). Nothing in the base's
`characteristic/` was edited. Full `Holmake -j1` is green with no cheats.

## Result in one paragraph

The single-part restriction of cfDiv's FFI-part loop rules is **not
fundamental**. `limited_parts ns p` is used in exactly one step of
`repeat_POSTd_one_FFI_part`. In a world with one part, a part's events
are the whole I/O trace, so the rule can conclude `Q io` about that trace.
With several parts, a part's events are only the trace **filtered to its
names**: this is `FFI_part_IN_st2heap_IMP`, which needs no
`limited_parts`. The generalised rule therefore concludes about
`LFILTER (ffi_has_index_in ns) io`. The only new mathematics is a
lazy-list lemma: filtering commutes with the limit of a chain of finite
lists. A never-ending loop in the composed world (command line + file
system + clock + sockets) that polls a socket **and** prints to stdout
every round is proved down to `Diverge` (`logserve_semantics`).

## Where cfDiv needed a single part

`repeat_POSTd_one_FFI_part` runs the loop for every clock. It shows that,
after the n-th iteration's clock, the run times out with
`st'.ffi.io_events = events n`, where `events n` are the tracked part's
events. It then identifies the program's divergence trace (the limit over
clocks of the I/O events) with the limit `io` of `events`.
`limited_parts` is used only to get that equation, via
`limited_FFI_part_IN_st2heap_IMP` (`FILTER (has_index ns) evs = evs`
when ns covers every name).

The FLATTEN variants (`repeat_POSTd_one_FFI_part_FLATTEN`, used by the
`IMP_app_..._FLATTEN` rule and by cf-spike/cf-actions) use
`limited_parts` more deeply, in their history-irrelevance step. That step
resets `io_events` to `[]` per iteration, which would be wrong for the
events that other parts have in the frame. They are not generalised here
(see "Not done").

## The generalised rules (`ffiSpikeDivMulti`)

```
repeat_POSTd_FFI_part_filter:            (* = repeat_POSTd_one_FFI_part, minus limited_parts *)
  (∃Hs events vs ss u io.
     vs 0 xv ∧ H ==>> Hs 0 ∧
     (∀i. ∃P. Hs i = P * one (FFI_part (ss i) u ns (events i))) ∧
     (∀i xv. vs i xv ⇒ app p fv [xv] (Hs i) (POSTv v'. &vs (SUC i) v' * Hs (SUC i))) ∧
     lprefix_lub (IMAGE (fromList o events) UNIV) io ∧
     (∀io'. LFILTER (ffi_has_index_in ns) io' = io ⇒ Q io'))      (* was: Q io *)
  ⇒ app p (some_repeat_clos env) [fv; xv] H ($POSTd Q)

IMP_app_POSTd_FFI_part_filter:           (* = IMP_app_POSTd_one_FFI_part, minus limited_parts *)
  make_stepfun_closure env fname farg fbody = SOME stepv ∧ fname ≠ farg ∧
  (∃Hs events vs ss u io. … same shape …,
     (∀io'. LFILTER (ffi_has_index_in ns) io' = io ⇒ Q io'))
  ⇒ app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)

lprefix_lub_LFILTER:                     (* the lazy-list lemma *)
  (∀n. w n ≼ w (SUC n)) ∧ lprefix_lub (IMAGE (fromList o w) UNIV) io ⇒
  lprefix_lub (IMAGE (fromList o FILTER P o w) UNIV) (LFILTER P io)
```

The loop body may use any part. Other parts live in the frame `Hs i`
with whatever events they accumulate; only the tracked part's events
appear in the conclusion.

**How the proof differs from cfDiv's.** The body is cfDiv's proof,
copied; about 75 of its ~215 lines changed or were added.
1. In the per-iteration claim, `st'.ffi.io_events = events n` becomes
   `FILTER (ffi_has_index_in ns) st'.ffi.io_events = events n`
   (`FFI_part_IN_st2heap_IMP`).
2. The divergence result is no longer the given `io`. It is
   `Div (build_lprefix_lub …)`: the limit, over all clocks, of the run's
   own I/O events. That limit exists because the events grow with the
   clock.
3. To show that this limit is a lub, cfDiv's `lprefix_lub_skip`
   (subsequence of iterations ⇒ all clocks) is applied to the sampled
   events `smp n`, the events at the clock of iteration n.
4. `Q` follows from `lprefix_lub_LFILTER` on `smp` (filtered, `smp`
   gives `events`), uniqueness of lubs, and the premise.

`lprefix_lub_LFILTER` needs three helper lemmas (~70 lines):
- every element of `LFILTER P io` comes from a finite prefix of `io`;
- every finite prefix of the limit of a chain is a prefix of some chain
  element;
- `fromList l ≼ ll ⇒ fromList (FILTER P l) ≼ LFILTER P ll`.

**Tactic.** `ffiSpikeDivMultiLib.xcf_div_filter ns name st` is cfDiv's
`xcf_div_rule` for the new rule. The caller names the tracked part's
`ns`, instead of the tactic reading it off a `limited_parts` assumption.
The two local conversions it needs were copied from `cfDivLib`.

## Demo: a logging server in the composed world (`ffiSpikeSocketLogDiv`)

```
fun logpoll u = let val r = Socket.poll [3] in TextIO.print "polled\n" end
fun serve u = serve (logpoll u)
```
- `logpoll_spec` (generic `p`): from `STDIO fs * SOCKETS_EV s evs`, it
  gives `STDIO (add_stdout fs "polled\n") * SOCKETS_EV (tick s) (evs ++
  [poll_event [3w] s])`. Two FFI parts are used in one round.
- `serve_spec` (the composed world's projections `socket_proj1/2`): from
  `COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS_EV sk []`, the result
  is `POSTd io. LFILTER (ffi_has_index_in socket_names) io = LGENLIST
  (λi. poll_event [3w] (ticks i sk)) NONE`. The loop invariant is
  `Hs i = COMMANDLINE cl * STDIO (logs fs i) * CLOCK clk`, where the
  stdout log grows by one line per round. The socket part's events after
  i rounds are `GENLIST (poll events) i`.
- **MAIN `logserve_semantics`**: assume `wfcl cl ∧ wfFS fs ∧ STD_streams
  fs`. Then the whole program (basis + Socket + logpoll + serve + a call
  to serve) has `semantics_dec_list (init_state (socket_world_ffi cl fs
  clk sk)) init_env … (Diverge io)`, and the socket-filtered trace is the
  infinite poll sequence. It goes through `call_main_thm_div` (PR #11)
  and a variant of the composed world's initial-heap lemma that exposes
  the socket part's empty event list (`socket_world_init_heap_ev`, a copy
  with one line changed).

This closes the main gap of 07-socket-model.md (§6.1). The composed
world's diverging theorem now has a real instance: a server that also
uses the file system.

## Not done (and how hard)

- **Tracking several parts at once.** `Q` sees one part's filtered trace,
  and the other parts' traces are not characterised. The same proof
  works per part, so a rule over a list of tracked parts (each with its
  own `events_k`, conclusion `∀k. LFILTER ns_k io = io_k`) is a
  mechanical extension: ~50 more lines. It still says nothing about how
  the parts' events interleave; that would need the per-round whole
  events, i.e. an `FFI_full`-style formulation.
- **FLATTEN variants.** These are the per-iteration-events form that
  cf-spike and cf-actions use, and they would need the
  history-irrelevance step redone for several parts. The non-FLATTEN
  rule here covers the same programs: state the cumulative events
  (`GENLIST …` as in the demo). Estimate for a FLATTEN version: 1–2
  days.
- **`socket_whole_prog_div_spec`** (PR #11) has `SOCKETS sk`, which hides
  the part's events. A program proved with this rule must state its
  precondition with `SOCKETS_EV sk []`. The demo therefore uses its own
  initial-heap lemma; a `SOCKETS_EV` variant of the whole-program
  definition would tidy this (~20 lines).

## Would this be a sensible upstream contribution to `characteristic/`?

Yes, and it is small and additive. A patch would look like this:

1. **`cfDivScript.sml`**: add `repeat_POSTd_FFI_part_filter` and
   `IMP_app_POSTd_FFI_part_filter` next to their `_one_` versions,
   ~260 lines (the copied proof plus the changes above).
   - Better, refactor: prove the general rule once and derive the
     `limited_parts` versions as corollaries. Under `limited_parts`,
     every event of the trace has an index in `ns` (`parts_ok`'s `EVERY
     ffi_has_index_in` clause), so `LFILTER … io = io`. This needs a
     small lemma that the limit of traces that all satisfy `EVERY P`
     satisfies `every P` (~30 lines). It would avoid duplicating the
     ~215-line proof.
2. **The lazy-list lemma** `lprefix_lub_LFILTER` and its helpers (~90
   lines) belong in HOL's `examples/pl-semantics/lprefix_lub` theory (a
   HOL PR) or in cfDiv if kept local.
3. **`cfDivLib.sml`**: let `xcf_div_rule` take the part's names
   explicitly when there is no `limited_parts` assumption. Its TODO
   already says "give an error if 'limited_parts' is not present".
   ~10 lines.
4. Optionally, **`cfMainScript.sml`**: `call_main_thm_div` from PR #11
   (the `POSTd` analogue of `call_main_thm2`, ~250 lines). With it, a
   user can go from a `POSTd` spec of main to `semantics_dec_list …
   (Diverge io)`, which basis_ffi currently only offers in the
   single-decl, single-part style of `examples/filterProg`.

Risks: low. The new rules are strictly more general, and existing users
of the `_one_` rules are unaffected. If the refactor in item 1 is chosen,
the existing statements stay identical.

## Tool and CF-tactic observations

- `xapp_spec logpoll_spec` raised `List.Empty` (no HOL error) on the loop
  step's `app` goal, in both hol-lsp and Holmake. The workaround was
  `xapp_prepare_goal`, then `app_wgframe` with the instantiated spec.
  This looks like a cfTacticsLib bug, perhaps in frame inference with an
  explicit `one (FFI_part …)` next to `STDIO` in the precondition. It is
  worth a minimal reproduction later.
- hol-lsp kept reporting `logpoll_spec` as failing
  (`optionSyntax.dest_some`) even after a server restart, while Holmake
  proved it. It seems to be the same family of problem as the
  `add_cakeml`/translator staleness noted in HANDOFF-socket.md, so
  Holmake was the authority for this file.
- After a looping `metis_tac`, the hol-lsp server kept checking the old
  text after edits ("still compiling"). `restart` was needed.
- Several user variable names clash with HOL constants and give
  "markerSyntax.Abbr: Ill-formed quotation" in `qabbrev_tac`: `W` (the W
  combinator), `part`, `flags`. `EXP` is a parser token (exponent), so
  `ENV EXP` failed with "No rule for [EXP]".
- `A \\ B THEN1 C` parses as `(A \\ B) THEN1 C`. A `cheat` placed inside
  A therefore makes `THEN1` fail with "goal completely solved by first
  tactic".

## Time

Commit times: branch from `5069b0d87`; the rule at 11:30 (about 35 min,
most of it on the final trace argument); the demo at 11:45 (15 min);
then this write-up. Check-waiting: hol-lsp diagnostics 30–110 s per edit
on `ffiSpikeDivMulti`, plus about 10 Holmake runs of 10–60 s for the
demo.

## Assumptions made

1. Generalise the non-FLATTEN rules (`repeat_POSTd_one_FFI_part`,
   `IMP_app_POSTd_one_FFI_part`) rather than the FLATTEN ones; cumulative
   events are enough for the demo.
2. The conclusion is about the trace filtered to one part
   (`LFILTER (ffi_has_index_in ns)`), stated as a premise `∀io'. LFILTER …
   io' = io ⇒ Q io'` so that `POSTd Q` keeps its shape.
3. The demo logs to stdout (a second FFI part, via `TextIO.print`) rather
   than reading the clock. The brief's example was "e.g. … reads the
   clock". Logging needs no second copy of the Clock module, because the
   Socket and Clock modules live in separate translation chains, and it
   is the more relevant "server that logs" case.
4. The demo uses its own `SOCKETS_EV` initial-heap lemma rather than
   changing PR #11's `socket_whole_prog_div_spec`.
5. cfDiv's proof and two cfDivLib conversions are copied into this
   branch, as an additive change, not by editing the base.
