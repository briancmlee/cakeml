# 02: Can we implement polled futures in CakeML and prove them with CF?

Status: **spike done, Option A works.** All specs are proved with no cheats.
Holmake succeeds for `async/cf-spike/` (branch `spike/cf-feasibility`).

## 1. The question

The library's meaning is a HOL *history model*. A computation is a function
from the list of world snapshots it has been polled with to its status
(finished with a result, or not yet). The implementation has to be CakeML
code, proved correct with CakeML's characteristic formulae (CF), a
separation logic for CakeML.

The worry: a future is naturally a mutable cell holding a closure, and that
closure's spec mentions the cell again. In separation logic that needs
step-indexing or impredicativity, and CakeML's CF has neither. The
hypothesis was that the *polling* design avoids the problem. Instead of
storing continuations in cells, each poll *returns* the residual
computation as a fresh value. This spike tests that hypothesis on a minimal
model with results only (no actions or responses), an abstract world, and
`return`, `wait`, `bind` and `poll`.

## 2. Option A: residuals, no refs

### The CakeML code (`asyncCfProgScript.sml`)

```sml
datatype ('w, 'a) step = Done 'a | Pending ('w -> ('w, 'a) step)

fun return x = Done x;
fun poll s w = case s of Done x => s | Pending k => k w;
fun wait p =
  Pending (fn w => case p w of Some a => Done a | None => wait p);
fun bind m f =
  case m of
    Done x => f x
  | Pending k => Pending (fn w => bind (k w) f);
```

This is an OCaml-style "resumption" monad: a computation is either finished,
or a function that, given the next snapshot, returns the rest of the
computation. There are no refs anywhere.

### The HOL model (`asyncCfModelScript.sml`)

```
Type comp = “:'w list -> 'a option”         (* history (oldest first) ↦ status *)
finished m x  ⇔ ∀h. m h = SOME x
after w m     = λh. m (w :: h)               (* m, after one more poll with w *)
mret x        = λh. SOME x
mwait f       : NONE on [], then the first a with f w = SOME a
mbind m g     : run m; at the poll where m finishes with x, continue as g x
```

`mbind` is defined by recursion on the history. If `m` hasn't finished, then
`mbind m g (w :: h) = mbind (after w m) g h`. Each needed fact about the
model is a one-line lemma: `after_mwait_NONE`, `after_mwait_SOME`,
`mbind_finished`, `after_mbind_pending`, and so on.

### The representation predicate, in prose

`STEP p A WORLD m v` says that the CakeML value `v` implements the model
computation `m`. Here `A` relates results to CakeML values, `WORLD`
relates snapshots to CakeML values, and `p` is CF's FFI projection.

- `Done xv` implements `m` if `m` has finished with some `x`, and `xv`
  represents `x` (`A x xv`).
- `Pending kv` implements `m` if `m` has not finished yet (`m [] = NONE`),
  and for every snapshot `w` represented by `wv`, calling `kv wv` terminates
  and returns a value that implements `after w m`.

"Calling `kv wv` returns a value satisfying R" is CF's
`app p kv [wv] emp (POSTv v. &R v)`, packaged as `returns p kv [wv] R`.

```
CoInductive STEP:
  (∀m x xv. finished m x ∧ A x xv ⇒ STEP p A WORLD m (DoneV xv)) ∧
  (∀m kv. m [] = NONE ∧
        (∀w wv. WORLD w wv ⇒ returns p kv [wv] (STEP p A WORLD (after w m))) ⇒
        STEP p A WORLD m (PendingV kv))
End
```

It is **coinductive**, because a computation that waits forever (e.g.
`wait (fn _ => None)`) is an infinitely deep chain of `Pending`s. HOL accepts
the definition once it knows that `returns` is monotone in its postcondition
(`returns_mono`, from CF's `app_weaken`, registered with `[mono]`).

Note what is *not* here: no heap cells and no `STEP` inside a heap
assertion. `STEP` appears only inside the *pure* postcondition of a closure
call. This is why ordinary coinduction is enough and CF needs no
higher-order (impredicative) heap.

### The proof technique: approximations, then the limit

`return` and `poll` are direct. `wait` and `bind` are recursive: the closure
they put in `Pending` calls `wait` or `bind` again. A direct coinductive
proof would need a "coinduction hypothesis" about the values these
recursive calls return, but CF only tells us about values through `app`
postconditions.

The fix is a standard trick, applied once, outside the specs:

1. `STEPn p A WORLD n m v` is `STEP` cut off after `n` polls (defined by
   recursion on `n`, with `STEPn 0 = T`).
2. Prove `wait_spec_n` and `bind_spec_n` (the result satisfies `STEPn n`) by
   ordinary induction on `n`. The recursive call inside the closure uses the
   induction hypothesis at `n`.
3. Pass to the limit with `STEPn_IMP_STEP`: if a value satisfies `STEPn n`
   for every `n`, it satisfies `STEP`. The proof is by coinduction. Its one
   non-trivial step needs this: if calling `kv wv` returns a value satisfying
   `P i` for each `i`, then it returns a value satisfying all of them at
   once.
4. That step is `app_basic_forall` (`asyncCfDetScript.sml`). It holds because
   CakeML's semantics is deterministic: in a given state, the call returns
   one value (runs with different clocks agree, by
   `evaluate_add_to_clock`).

So step-indexing appears only as a proof device in two `_n` lemmas. The
**statements** of the specs use plain `STEP`, and a client never sees `n`.

### What was proved (all in `async/cf-spike/`, no cheats)

The user-owned main statements (`MAIN` in the script):

```
(* MAIN: return x builds a finished computation. *)
Theorem return_spec:
  A x xv ⇒
  app (p:'ffi ffi_proj) return_v [xv] emp
    (POSTv v. &STEP p A WORLD (mret x) v)

(* MAIN: polling a computation with snapshot w returns its residual,
   which implements the model computation after w. *)
Theorem poll_spec:
  STEP p A WORLD m sv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll_v [sv; wv] emp
    (POSTv v. &STEP p A WORLD (after w m) v)

(* MAIN: wait f is a computation that finishes at the first polled
   snapshot w with f w = SOME a, with result a.  f may be any CakeML
   function that implements the HOL function f. *)
Theorem wait_spec:
  (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE A (f w))) ⇒
  app (p:'ffi ffi_proj) wait_v [fv] emp
    (POSTv v. &STEP p A WORLD (mwait f) v)

(* MAIN: bind m g implements the model's bind, given that m is implemented
   by mv and that, for every result x, g x is implemented by what the
   CakeML function gv returns on (a representation of) x. *)
Theorem bind_spec:
  STEP p A WORLD m mv ∧
  (∀x xv. A x xv ⇒ returns p gv [xv] (STEP p B WORLD (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &STEP p B WORLD (mbind m g) v)

(* MAIN: binding a finished computation adds no wrapper: bind (Done x) g
   is exactly g x, whatever g does (any pre/postcondition). *)
Theorem bind_Done_spec:
  app (p:'ffi ffi_proj) gv [xv] H Q ⇒
  app p bind_v [DoneV xv; gv] H Q
```

`bind_spec` is higher-order in the usual CF way: it assumes a spec for the
user's continuation `gv`.

Supporting lemmas: `returns_mono`, `returns_forall`, `STEP_IMP_STEPn`,
`STEPn_0`, `STEPn_IMP_STEP`, `wait_spec_n`, `bind_spec_n`
(`asyncCfProgScript.sml`); `evaluate_ck_Rval_det`, `app_basic_forall`
(`asyncCfDetScript.sml`); and the model lemmas (`asyncCfModelScript.sml`).

### Memory: finished binds don't accumulate

`bind_Done_spec` says that `bind (Done x) g` behaves *exactly* like `g x`,
under any pre- and postcondition. It returns whatever `g x` returns, with no
wrapper. Together with the code for the pending case (`poll` of
`Pending (fn w => bind (k w) f)` is just `bind (k w) f`), this means that
once the first part of a bind finishes, the residual is just the
continuation's residual. A server written as
`fun loop () = bind (handle_one ()) (fn _ => loop ())` keeps a constant-size
residual between requests. As in any monad, binds that are still *pending*
do nest. A left-nested chain `bind (bind (bind m f) g) h` holds three
closures until `m` finishes, so a loop must not left-nest unboundedly
(`fun loop m = loop (bind m f)` would leak).

### What failed, and friction

Nothing in Option A failed. Option B (refs as caches) was **not tried**,
because A worked. The friction, for the record:

- `W` is HOL's W combinator (`combin$W`). With `W` as my name for the world
  relation, the definitions parsed with the wrong meaning, and the error only
  showed up later as a strange type error. Renamed to `WORLD`.
- `CoInductive` treats a free variable that has the same name in every rule's
  conclusion as a *fixed parameter*. A free `m` therefore silently became a
  parameter, and the recursive occurrence `STEP ... (after w m)` turned the
  coinduction principle into nonsense. Fix: quantify `m` explicitly in each
  rule.
- `irule`/`ho_match_mp_tac` couldn't higher-order match `returns_forall`
  against `λv. ∀n. STEPn ... n ... v`; I instantiated it explicitly.
- The hol-lsp goal walker timed out (>1500 ms) on goals after `xmatch`. I
  wrote those steps blind and checked them with `diagnostics`.

## 3. Caveats (what this spike does not show)

1. **Closures are pure.** `returns` has an empty precondition and a
   postcondition that keeps no heap, so user callbacks (`fv` in `wait`,
   `gv` in `bind`) cannot own refs or perform I/O across a poll. If they
   must, `returns` needs an invariant: `app p f args I (POSTv v. I * &R v)`.
   Then `app_basic_forall` must also be generalized. Determinism still
   gives one returned value per state, but CF's postcondition picks a heap
   split (kept part vs garbage) *per postcondition*, so we would need `I` to
   be precise or a different argument. I expect this to be doable but
   haven't done it. The recommended design (section 4) avoids needing it.
2. **Each poll terminates** (CF `app` is total correctness). This is right
   for per-poll steps. The never-ending event loop is a separate matter
   (section 4).
3. The model is minimal: results only, an abstract world, and `wait` only
   looks at snapshots it is polled with (it is pending before the first
   poll, by design).
4. The `_n` proofs repeat the closure reasoning of the main proofs (about 15
   lines each for `wait` and `bind`). For the full library this should be
   packaged once: a lemma or tactic of the form "to prove `STEP` of
   `Pending k`, prove each approximation using the `_n` spec of the
   recursive callee". *(Done on `spike/cf-loop`: `app_STEP_of_approx`, see
   `03-cf-loop.md`.)*

## 4. Implications for the implementation plan

**Use Option A (residual style, no refs) for the library's core.** It
avoids the higher-order-store problem entirely, the specs are first-order
in shape, and the proofs are routine CF.

Expected difficulty of the full library:

- **Actions and responses.** Make the model's outcome carry the actions
  emitted, and make `Pending` closures return `(actions, residual)` (or
  `step` gets a third constructor). Actions are *data* that the runtime
  performs, so user closures stay pure, which sidesteps caveat 1. `STEP`
  grows a clause relating the emitted actions to `new_actions` of the model
  (as in `async-spike`'s `asyncCore`). Same coinduction, same
  approximation trick. Expected: **easy to moderate**. Most of the work is
  the model's bookkeeping, not CF.
- **`both` / `choose` with resumable losers.** In residual style, a
  resumable loser is just a value: `choose` returns the winner's result
  together with the loser's current residual, which `STEP` relates to the
  model "after" the shared history. Polling two residuals per poll is plain
  code. The hard part is the model side: how each branch sees the snapshot
  and the responses to its own actions (`par_views` in `async-spike`). The
  CF proofs should follow the same pattern as `bind` (two recursive
  approximations instead of one). Expected: **moderate, dominated by the
  model**.
- **The never-ending event loop.** The loop is
  `fun run s = run (poll s (get_snapshot ()))`, plus performing actions. Its
  body is total, with `poll_spec` and a terminating FFI call to get the
  snapshot. The loop itself diverges, so it needs the non-termination CF of
  Åman Pohjola, Rostedt and Myreen (ITP 2019), already in
  `characteristic/cfDivScript.sml` (`POSTd` postconditions; loop rules
  `repeat_POSTd`, `repeat_POSTd_one_FFI_part`, `tailrec_POSTd`, used via
  `xcf_div`).
  The loop invariant is `STEP p A WORLD m s` for the model after the
  snapshots seen so far, plus the FFI trace. Expected: **moderate**. The CF
  side is a standard "repeat" proof. The real work is the FFI model of
  snapshots and actions, and stating the end-to-end trace theorem.
- **Memory behaviour.** `bind_Done_spec` already gives what long-running
  servers need: finished binds leave no wrapper. Library combinators should
  be written so that loops are right-nested.

**Recommendation:** proceed with the residual-style design and CF. The
biggest technical risk (higher-order store) does not arise. The next
risks to retire are, in order: (1) the actions/responses version of `STEP`
together with `asyncCore`'s model; (2) the divergent event loop with
`cfDiv`; (3) packaging the approximation-then-limit argument as a reusable
lemma, so each new combinator proof is just its closure reasoning.
