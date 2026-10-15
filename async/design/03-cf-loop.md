# 03: Packaging the limit argument, and a never-ending event loop with cfDiv

Status: **both parts done.** No cheats, and `Holmake -j2` in
`async/cf-spike/` succeeds. Branch `spike/cf-loop`, stacked on
`spike/cf-feasibility` (see `02-cf-feasibility.md` for the background:
the residual design, `STEP`, and the approximation trick).

## (a) "Approximations, then the limit" as one reusable lemma

In 02, `wait_spec` and `bind_spec` each repeated their closure reasoning:
once in the `_n` lemma (by induction on n), and again in the main proof
(to pass to the limit for the specific closure stored in `Pending`). The
limit step only worked for *one-argument* calls, because the determinism
lemma `app_basic_forall` only covered `app_basic`.

The fix is to lift determinism to curried applications:

```
(* asyncCfDetScript.sml *)
Theorem app_forall:
  ∀p P xs f H.
    xs ≠ [] ∧ (∀i. app p f xs H (POSTv v. &P i v)) ⇒
    app (p:'ffi ffi_proj) f xs H (POSTv v. &(∀i. P i v))
```

In words: if a call (with any non-empty argument list and any precondition)
returns a value satisfying `P i` for every `i`, it returns a value
satisfying all of them at once.

The proof is by induction on the arguments. A partial application returns
the same closure and the same heap in every run (determinism,
`evaluate_to_heap_Val_det`), but CF lets each postcondition choose its own
split of that heap into kept and garbage parts. So the proof restarts the
remaining applications from exactly the union of both parts
(`SPLIT3_merge`, `app_exact_pre`).

From it, the packaged lemma:

```
(* asyncCfProgScript.sml *)
(* To prove a STEP spec, prove its n-th approximation for every n. *)
Theorem app_STEP_of_approx:
  args ≠ [] ∧ (∀n. app p f args H (POSTv v. &STEPn p A WORLD n m v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &STEP p A WORLD m v)
```

`wait_spec` and `bind_spec` keep their statements, and their proofs are now
two lines each:

```
  rpt strip_tac >> irule app_STEP_of_approx >> simp[] >>
  metis_tac[wait_spec_n]
```

**Recipe for a future combinator `c`** (e.g. `both`, `choose`):

1. Prove `c_spec_n`: `∀n. ... ⇒ app p c_v args H (POSTv v. &STEPn ... n (model_c ...) v)`
   by induction on n. The closure it puts in `Pending` calls recursive
   callees, and each of those uses its own `_n` spec at `n` (or the
   induction hypothesis).
2. Prove `c_spec` with `irule app_STEP_of_approx` and `c_spec_n`.

Only step 1 involves any reasoning about the closure.

## (b) A toy never-ending event loop

### Code (`asyncCfLoopScript.sml`)

```sml
fun get_snapshot u =
  let
    val a = Word8Array.array 1 (Word8.fromInt 0)
    val _ = #(get_snapshot) "" a
  in Word8Array.sub a 0 end;
fun step s = poll s (get_snapshot ());
fun run s = run (step s);
```

### A minimal FFI model (`asyncCfSnapScript.sml`)

This is self-contained. It doesn't use `basis_ffi` or anything else in the
base.

- The world is a stream of one-byte snapshots `s : num -> word8`. The FFI
  state is `snap_state s = Stream (LGENLIST (λi. w2n (s i)) NONE)`, using
  the `Stream` constructor of CakeML's generic FFI state type.
- `snap_update` implements `get_snapshot` (empty config, one-byte buffer).
  It writes the next snapshot into the buffer and drops it from the stream
  (`snap_update_get`).
- `snap_event w = IO_event (ExtCall «get_snapshot») [] [(0w, w)]` is the I/O
  event that one call produces.
- `SNAP s evs = one (FFI_part (snap_state s) snap_update snap_names evs)` is
  the separation-logic assertion for this FFI.
- `after_list ws m` is the model `m` after being polled with the snapshots
  `ws`.

### What was proved

```
(* get_snapshot returns the next snapshot and records one event. *)
Theorem get_snapshot_spec:
  limited_parts snap_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) get_snapshot_v [uv] (SNAP s evs)
    (POSTv v. &WORD (s 0) v * SNAP (stail s) (evs ++ [snap_event (s 0)]))

(* MAIN: one loop iteration.  If the residual sv implements m, then after
   reading the next snapshot w = s 0 and polling, the new residual
   implements m after w, and exactly one get_snapshot event happened. *)
Theorem step_spec:
  limited_parts snap_names p ∧ STEP p A WORD m sv ⇒
  app (p:'ffi ffi_proj) step_v [sv] (SNAP s evs)
    (POSTv v. &STEP p A WORD (after (s 0) m) v *
              SNAP (stail s) (evs ++ [snap_event (s 0)]))

(* MAIN: the event loop never terminates, and its I/O trace is the infinite
   sequence of get_snapshot events, one per snapshot of the stream s.
   (The residual after i iterations implements after_list (GENLIST s i) m;
   see step_spec, which is the loop invariant.) *)
Theorem run_spec:
  limited_parts snap_names p ∧ STEP p A WORD (m : word8 list -> 'a option) sv ⇒
  app (p:'ffi ffi_proj) run_v [sv] (SNAP s [])
    (POSTd io. io = LGENLIST (λi. snap_event (s i)) NONE)
```

`POSTd io. Q io` is cfDiv's postcondition for divergence: the call does not
terminate, and the (possibly infinite) I/O trace `io` satisfies `Q`. So
`run_spec` says that `run` diverges and that its trace is exactly one
`get_snapshot` event per snapshot, forever.

The proof uses `xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN`. It is
cfDiv's "tail-recursive loop over one FFI part" rule, with the trace given
as the flattening of per-iteration event lists. The loop invariant (`vs`
in that rule) is `STEP p A WORD (after_list (GENLIST s i) m)`: after i
iterations, the residual implements the model after the first i
snapshots. Each iteration is discharged by `step_spec`. The trace equation
needs one lazy-list lemma, `LFLATTEN_LGENLIST_singletons`.

### Where the statement is weaker than one might want (the honest gap)

- **`run_spec`'s postcondition only mentions the trace.** `POSTd` can only
  constrain the I/O trace, so the fact that the residual stays correct
  appears as the loop invariant (proved via `step_spec`), not in
  `run_spec`'s statement. That is inherent to a loop that never returns
  and never acts on the computation's result. In this toy the result is
  never observed. A real event loop would *act* on the computation (perform
  its actions, which then appear in the trace), and the trace would then
  carry the model's meaning. That needs the actions/responses version of
  `STEP` (out of scope here).
- The loop polls a `Done` computation forever (`poll` leaves `Done`
  unchanged). That is fine for a toy, and it is what the model says too.
- The world is one byte, which keeps the FFI trivial. A richer snapshot only
  changes the FFI model and the refinement relation for snapshots (here
  `WORD`), not the shape of the proof.

### Did cfDiv cause any difficulties?

No fundamental ones. The divergence rule took the per-iteration spec
directly, and the `STEP` invariant fitted its `vs i` slot unchanged. The
only friction was tooling (see `HANDOFF-cf.md`, "Tool feedback"). In
particular, `xapp` inside the `xcf_div` goal works under Holmake but
not in hol-lsp, so that proof was developed by replaying it in a dumped
Holmake heap.

## Assumptions made

I made these choices without asking. Each one is the simplest option,
and none of them commits the project to anything:

1. The world snapshot is a single byte (`word8`), returned by one FFI call
   `get_snapshot` with an empty config and a one-byte buffer.
2. The FFI state is an infinite stream (`Stream` of an infinite `LGENLIST`).
   Running out of snapshots isn't modelled: on an empty stream `snap_update`
   returns `NONE`, i.e. the FFI call fails. That never happens for the
   infinite streams used here.
3. The loop never stops, even after the computation finishes (`poll` of
   `Done` is `Done`).
4. `step` is a separate top-level function, so its spec is the loop
   invariant. `run` is `fun run s = run (step s)`, the shape cfDiv's
   `xcf_div` expects (a tail call of itself).
5. The pure HOL parts of the loop are in a separate theory
   (`asyncCfSnap`), because editing above `Quote add_cakeml` in hol-lsp
   makes it re-run the declaration and fail ("Out-of-date conclusion to
   theorem").
