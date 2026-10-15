# Handoff: QuietSpec and option C (quiescence), async-spike

Kept current at every milestone. The full state (review series, folds,
rules, gotchas) is in ~/.cache/async-spike/STATE.md.

## Where things are
- spike/quiet-spec (PR #57):
  - `spec/QuietSpec` (user-approved): `echo_quiet`, `http_quiet`,
    `http_quiet_b`, `select_ffi`, `arrivals_finite`, `asleep`;
  - `QuietSpecBite`;
  - `design/33-option-c-quiescence.md` (the costing; approved).
- spike/quiet-spec also has the SPEC CHANGE (user-approved) cccfddec4:
  select fails on an fd that is not a socket of the model (`sel_ok`).
- spike/quiet-echo (stacked on it), `async/quiet/echo/`, all proved, no
  cheats. **Q1 is done.**
  - `asyncEchoCause`: `handler_cause`.
  - `asyncEchoServerCause`: `both_cause`, `server_cause` (the server acts
    only on: readable listener; a readable fd it accepted more often than
    it read EOF; Data).
  - `asyncStaticRounds`: `static_after` (arrivals_finite ⇒ static from
    some N), `static_round` (exact per-round accounting).
  - `asyncEchoReadySoon`: `read_ready_soon_s`.
  - `asyncEchoMeasure`: `meas_mono`, `meas_progress`, `meas_zero`.
  - `asyncEchoStable`: **`echo_stable`** (Q1): with arrivals_finite, from
    some round on the polling run has no actions, and nothing in
    `(server2 lfdn).interest` is ready. Also `conns_no_listener`,
    `eofr_eofs`, `accs_le_one`, `zero_no_actions`, `zero_interest`.

## Echo: DONE, ⊢ echo_quiet 3w (SNOC (main_call «main») echo_l_prog)
`async/quiet/echo/asyncEchoQuiet`, `echo_l_quiet` (no cheats). This is the
shipped blocking echo program (layer 8, #46), proved quiet by the agreed
shortcut: echo's live list is exactly what the server waits for
(echo_live_list_covers), so option C's declared-interest loop is not needed
for echo.
- Q2 `echo_sleeps` (asyncEchoSleeps): with arrivals_finite the select loop
  blocks forever. Generic `lbgrounds_sleeps`; `live_inv`, `kept_live`.
- Select bridge: QuietSpec's select fails on non-sockets, #46's does not.
  - async/quiet/ffi/ffiAgreeUpto (generic CakeML): `semantics_prog_upto`
    (same behaviours if the FFI states agree on the calls of each clocked
    run), `call_FFI_rel_answers`.
  - asyncEchoBridgeWorld: `oracle_agree`, `answers_agree(_prefix)`.
  - asyncEchoQuietTrace: `good`, `ok_of_good`, `trace_good` (selects name
    only the listener and accepted fds).
- HTTP still needs option C (its live list is not the interest, #56).

## Plan (design/33 §2.5), echo first
1. Q1 `echo_stable`: DONE (above).
2. Q2 (NEXT): a generic loop lemma (stable polling ⇒ the declared-interest
   select loop ends asleep), via #46's `lbgrounds`.
3. Q3: the finite trace is safe and live.
4. The L2 CF library, the loop, echo at Level 2 in CF, the bridge, and
   ⊢ `echo_quiet 3w` <program>.

HTTP waits for cf-actions' generic pipeline (design/32). Its cause lemma
has a third disjunct (an answered Write) and consumes `handler_live`'s
buffered-requests term (agreed with cf-actions).

## Build
`~/Programming/cakeml-worktrees/review-series-tools/hm.sh async/quiet/echo`
(holslot, -j1). No cheats.
