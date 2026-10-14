# 04: Adding a new FFI component to CakeML, modularly (clock spike)

Status: done, 2026-10-15. Branch `spike/ffi-integration`, code in
`async/ffi-spike/` (876 lines in 6 files). Everything builds with
`Holmake -j1` against the shared base in 74 s from clean (about 30 s
incremental), with no cheats.

## The question

CakeML gives a program its meaning relative to an *FFI oracle*. That is a
function that answers each foreign call `#(name) conf bytes` given an
abstract FFI state, and records an I/O event. For separation-logic (CF)
reasoning, the FFI state is cut into *parts* (`ffi_part` in
`characteristic/cfHeapsBaseScript.sml`). Each part is a triple
`(encode, decode, [(name, ffi_fun)])`. Its heap assertion is
`IOx part s`: "the program owns this part, and the part's state is `s`".
Library specs (`app p f args P Q`) are generic in the world `p : 'ffi ffi_proj`.
They only need their own part to be present.

The world itself is fixed in `basis/basis_ffiScript.sml`:

- the state is `(command line, file system)`;
- `basis_ffi_oracle` answers 9 names;
- `basis_proj1` and `basis_proj2` describe the parts;
- the whole-program theorems (`whole_prog_spec_*`, `prove_sem_thm` in
  `basis_ffiLib`) turn a CF spec of `main` into a statement about
  `semantics_dec_list`, i.e. the program's observable behaviour.

In 2024 a clock was added by changing that file, which rippled into ~30
files (branch `archive/2024-project`).

**Hypothesis:** a new component can instead be added *beside* basis_ffi,
with its own composed world and its own whole-program theorem, and with no
change upstream.

**Answer: yes.** It was done here for a clock with no upstream change, and
it was cheap: ~400 lines for the composed world. Most of basis_ffi's lemmas
were reused unchanged, and only the top-level theorems had to be restated.

## What was built

| theory | lines | content |
|---|---|---|
| `ffiSpikeClockFFI` | 107 | the clock model: state, `ffi_now`, assumptions, `clock_ffi_part` |
| `ffiSpikeClockProg` | 46 | CakeML module `Clock` with `now : unit -> int` |
| `ffiSpikeClockProof` | 96 | heap predicate `CLOCK`, CF spec `Clock_now_spec` |
| `ffiSpikeClockWorld` | 460 | composed world, `parts_ok`, whole-program theorem |
| `ffiSpikeClockWorldLib` | 68 | `prove_sem_thm` for the composed world |
| `ffiSpikeClockExample` | 99 | two-reading program and its end-to-end theorem |

### 1. The clock model (`ffiSpikeClockFFI`)

- The state is `clk : num llist`, the readings the clock will return, in
  order. It is an arbitrary schedule chosen by the environment, like fsFFI's
  `numchars`.
- `ffi_now conf bytes clk` needs an 8-byte buffer and a non-empty schedule.
  It writes the head of the schedule as `n2w8 t` (big-endian, as in
  `Marshalling`) and drops it. Otherwise it returns `NONE`, which the oracle
  turns into `FFI_failed`. It never diverges, and it keeps buffer lengths.
- The assumptions on a schedule are:
  - `clock_fits`: every reading is < 2^64;
  - `clock_mono`: each reading is ≥ the previous one;
  - `clock_ok` is the conjunction of the two.
- The part is `clock_ffi_part = (clock_encode, clock_decode, [(«now», ffi_now)])`.
  The encoding uses the existing `Stream` constructor of the universal `ffi`
  type, so it is injective for free.

### 2. The CakeML wrapper and its CF spec (`ffiSpikeClockProg`, `ffiSpikeClockProof`)

```sml
fun now u = case u of () =>
  let val b = Word8Array.array 8 (Word8.fromInt 0)
      val u = #(now) "" b
  in bytes_to_num (Word8Array.sub b 0) ... (Word8Array.sub b 7) end
```

`bytes_to_num` is `Marshalling.w82n` on 8 bytes. It is translated, not
written by hand, so its spec comes from the translator. The helper is
module-local.

```
CLOCK clk = IOx clock_ffi_part clk

(* MAIN *) Clock_now_spec:
  t < 256 ** 8 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) Clock_now_v [uv]
    (CLOCK (t ::: rest))
    (POSTv v. &NUM t v * CLOCK rest)
```

The proof follows the pattern of the basis specs that make FFI calls
(`CommandLineProof`): unfold `CLOCK` to `IO`, `xpull`, `xffi`, choose the
frame and events, then read the 8 bytes back (a 4-line ML helper for the
8 `Word8Array.sub` calls) and apply the translated decoder.

### 3. The composed world (`ffiSpikeClockWorld`)

- **State:** `((cl, fs), clk)`, the basis state paired with the clock's
  schedule.
- **Oracle:** `clock_world_oracle` handles «now» itself. It passes every
  other name to `basis_ffi_oracle no_ext` on the first component and leaves
  `clk` alone. It *wraps* the basis oracle rather than copying its 9 cases.
- **Projections:**
  - `clock_proj1 (st, clk) = basis_proj1 st |++ mk_proj1 clock_ffi_part clk`
  - `clock_proj2 = basis_proj2 ++ [mk_proj2 clock_ffi_part]`

  Both *extend* basis_ffi's projections.
- **`parts_ok_clock_world_ffi`:** the projections agree with the oracle. It
  is proved from small lemmas:
  - on a basis name, our projection and oracle reduce to basis_ffi's;
  - for those names, basis_ffi's `oracle_parts` and `oracle_parts_div` are
    reused (restated as `basis_oracle_parts` and `basis_oracle_parts_div`);
  - the clock's own entry is handled by `clock_part_return`;
  - the clock entry commutes with basis updates (`FUPDATE_LIST_APPEND_COMMUTES`).
- **The basis view of a run.** `basis_view s` keeps the basis half of the
  state and drops the clock's I/O events (`is_clock_event`), under the basis
  oracle. `call_FFI_rel_basis_view` shows that each FFI step of our world is
  either invisible to the basis (a clock call) or *a step of the basis
  world*. So basis_ffi's `RTC_call_FFI_rel_IMP_basis_events` applies
  unchanged, and gives `clock_world_extract`: replaying the non-clock events
  from `(cl, fs)` with basis_ffi's `extract_fs_with_numchars` reproduces the
  basis state. The observable result is
  `clock_extract_fs cl fs events = extract_fs no_ext (cl,fs) (FILTER ($¬ o is_clock_event) events)`.
- **Heaps:**
  - `clock_world_init_heap`: right after the basis library's declarations,
    the heap satisfies `COMMANDLINE cl * STDIO fs * CLOCK clk`. It is built
    compositionally from the exported `COMMANDLINE_precond`,
    `STDIO_precond` and the new `CLOCK_precond`, joined with `append_hprop`.
  - `clock_world_STDIO_heap`: a heap fragment satisfying `STDIO fs'` pins
    the state's file system to `fs'` (up to `numchars`).
- **Whole-program theorem:**

```
clock_whole_prog_spec fv cl fs clk post ⇔
  ∃fs'. app (clock_proj1, clock_proj2) fv [Conv NONE []]
          (COMMANDLINE cl * STDIO fs * CLOCK clk)
          (POSTv uv. &UNIT_TYPE () uv * STDIO fs') ∧
        post (fs' with numchars := fs.numchars)

(* MAIN *) clock_whole_prog_spec_semantics:
  clock_whole_prog_spec main_v cl fs clk post ∧
  Decls init_env (init_state (clock_world_ffi cl fs clk)) decs res_env res_st ⇒
  ∀main_name.
    let all_decs = SNOC (Dlet NoLocs (Pcon NONE [])
                     (App Opapp [Var (Short main_name); Con NONE []])) decs in
    nsLookup res_env.v (Short main_name) = SOME main_v ⇒
    res_st.ffi = clock_world_ffi cl fs clk ⇒
    is_refs_basis res_st.refs ⇒
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
    ∃io_events fs'.
      semantics_dec_list (init_state (clock_world_ffi cl fs clk)) init_env
        all_decs (Terminate Success io_events) ∧
      clock_extract_fs cl fs io_events = SOME fs' ∧ post fs'
```

  The statement has exactly the shape of basis_ffi's `whole_prog_spec_IMP`,
  so the copied `prove_sem_thm` can discharge its side conditions the same
  way (by `EVAL`). The proof is 30 lines: `call_main_thm2` from `cfMain`,
  then the four lemmas above.

### 4. End to end (`ffiSpikeClockExample`)

```sml
fun main u =
  let val t1 = Clock.now ()
      val t2 = Clock.now ()
  in TextIO.print (Int.toString t1 ^ "\n" ^ Int.toString t2 ^ "\n") end
```

The proof chain:

1. `main_spec` is a CF spec, generic in the world: it uses two
   `Clock_now_spec`s, the translator's `toString`/`^` and `print_spec`.
2. `main_whole_prog_spec` is the whole-program spec. The parts that `main`
   doesn't use are framed away with `app_wgframe`.
3. `prove_sem_thm` from `ffiSpikeClockWorldLib` produces the semantics
   theorem.
4. The main result is:

```
(* MAIN *) clock_example_semantics:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ clock_ok (t1 ::: t2 ::: rest) ⇒
  ∃io_events.
    semantics_dec_list (init_state (clock_world_ffi cl fs (t1 ::: t2 ::: rest)))
      init_env clock_example_prog (Terminate Success io_events) ∧
    clock_extract_fs cl fs io_events =
      SOME (add_stdout fs (clock_example_output t1 t2)) ∧
    t1 ≤ t2

clock_example_output t1 t2 =
  mlint$toString (&t1) ^ «\n» ^ mlint$toString (&t2) ^ «\n»
```

In words: if the first two readings fit in 8 bytes and the clock is
monotone, the whole program `clock_example_prog` (basis library, `Clock`,
`main`, and the call to `main`) terminates successfully. Replaying its
file-system events appends exactly `"<t1>\n<t2>\n"` to standard output, and
t1 ≤ t2. This is the full requested statement. The only gap is the usual
one: this is the *source* semantics. Getting to the compiled binary needs
the compiler-correctness theorem instantiated for this new oracle (see
"Upstream" below).

## Copied, adapted, or reused from basis_ffi

**Reused unchanged** (used by name, not copied):

- from `basis_ffi`: `basis_ffi_oracle`, `no_ext`, `is_basis_ffi_name`,
  `basis_ffi`, `basis_proj1`, `basis_proj2`, `basis_ffi_part_defs`,
  `basis_ffi_length_thms`, `oracle_parts`, `oracle_parts_div`,
  `extract_fs_with_numchars`, `extract_fs`,
  `RTC_call_FFI_rel_IMP_basis_events`, `STDIO_precond`, `append_hprop`,
  `SPLIT_exists`, `is_refs_basis`, `basis_refs_eqs`;
- from elsewhere: `COMMANDLINE_precond` (CommandLineProof),
  `IOFS_FFI_part_hprop` (TextIOProof), and `call_main_thm2`,
  `FFI_part_hprop_*` (cfMain);
- all library specs: `print_spec`, the translator specs and the
  `Word8Array` specs.

**Adapted (new statement for our world; proof new unless noted):**

| basis_ffi item (lines there) | ours (lines) | how |
|---|---|---|
| `basis_ffi_oracle_def` (42) | `clock_world_oracle_def` (12) | wraps the basis oracle, not a copy |
| `basis_ffi_def` (6) | `clock_world_ffi_def` (6) | same shape |
| `basis_proj1_def`, `basis_proj2_def` (14) | `clock_proj1_def`, `clock_proj2_def` (8) | extend the basis ones |
| `parts_ok_basis_st` (21) | `parts_ok_clock_world_ffi` + 11 lemmas (~150) | structured, reuses `oracle_parts*`; the 4-line length tactic is copied (`basis_parts_length`) |
| `IMP_STDIO_general` (78, **local**) | `clock_world_init_heap`, `clock_world_part_in_heap`, `STDIO_precond_1`, `CLOCK_precond` (~60) | rewritten compositionally (the original is local, so it can't be reused) |
| fragment of `whole_prog_spec2_semantics_prog` (~25) | `STDIO_FFI_part`, `FLOOKUP_clock_proj1_write`, `clock_world_STDIO_heap` (~40) | same idea, as lemmas |
| `whole_prog_spec_def` (8) | `clock_whole_prog_spec_def` (9) | copied, add `CLOCK clk` |
| `whole_prog_spec_semantics_prog`, `whole_prog_spec2_semantics_prog`, `whole_prog_spec_IMP` (~110) | `clock_whole_prog_spec_semantics` (46) | statement copied from `whole_prog_spec_IMP`; 6 lines of `FFI_part_hprop` tactic copied |
| (none) | `is_clock_event`, `basis_view`, `call_FFI_rel_basis_view`, `RTC_call_FFI_rel_basis_view`, `clock_extract_fs`, `clock_world_extract` (~65) | new: the projection onto the basis world that makes the RTC lemma reusable |
| `basis_ffiLib.prove_sem_thm` (~75) | `ffiSpikeClockWorldLib.prove_sem_thm` (~55) | copied; timers dropped; the FFI term is taken from the spec (see Friction 6) |

**Not adapted (out of scope):**

- `whole_prog_spec2` and the `_SOME_` variant (extra precondition `p` on
  the remaining store);
- the `ffidiv` variants (programs that end by `Runtime.exit`);
- `RUNTIME` in the precondition.

Each is a similar ~30–50-line restatement.

**Nothing upstream was changed.** basis_ffi and everything else in CakeML
is untouched. The spike builds in a sparse worktree containing only
`async/`, against the frozen shared base.

## Friction

1. **The upstream extension point `ext` doesn't help a stateful
   component.** Since commit `ec8bad373` (Aug 2026), `basis_ffi_oracle ext`
   passes unknown names to `ext`. This is a precise negative result:
   - `ext` has type `ffiname -> mlstring list # IO_fs -> ...`. Its state is
     the basis state, so a clock schedule (or socket buffers) has nowhere to
     live.
   - The extra names are not in `basis_proj2`, so CF cannot reason about
     calls to them: `xffi` needs the part in the world's projection.

   So `ext` gives *semantics* to extra calls, but no state and no CF specs.
   A new component needs its own world, as built here.
2. **Lemmas are stated about semantic states, not oracles.**
   `oracle_parts` and `oracle_parts_div` say
   `st.ffi.oracle = basis_ffi_oracle ext ⇒ ... st.ffi.oracle ...` for an
   arbitrary `st`, with `ext` free. Reusing them meant instantiating a dummy
   state `ARB with ffi := basis_ffi no_ext ARB ARB` and `Q.INST`ing `ext`.
   It's harmless but obscure.
3. **Local theorems.** `IMP_STDIO_general`, `IMP_STDIO` and
   `IMP_STDIO_RUNTIME` are `[local]`, so their 78-line proofs can't be
   reused. They were replaced by a compositional proof built from the
   exported `*_precond` theorems. That proof is shorter, and it is what an
   upstream generalisation should export.
4. **`STDIO_precond` states the I/O buffer's location as a 12-term sum of
   ref-list lengths.** It needs `SIMP_RULE … [basis_refs_eqs]` to become
   `Mem 1`.
5. **Theorems tied to concrete projections** (`basis_proj1_write`). Each
   needed a one-line analogue (`FLOOKUP_clock_proj1_write`).
6. **`basis_ffiLib.prove_sem_thm` hard-codes the world.** It hard-codes the
   FFI term `basis_ffi ext cl fs` and its list of `whole_prog_*` theorems, so
   it had to be copied. The copy also had to compute the FFI term from the
   spec: our example instantiates `clk := t1 ::: t2 ::: rest`, and a fixed
   term `clock_world_ffi cl fs clk` made `MATCH_MP` fail with "double bind
   on variable clk". Basis never hits this because its specs keep `cl`, `fs`
   as variables.
7. Minor tactic surprises:
   - `irule SPLIT_exists` produced its two conjuncts in the opposite order
     to the statement;
   - `rw` normalises `256 ** 8` to `18446744073709551616`, which then
     defeats `drule` against a lemma stated with `256 ** 8`;
   - `drule call_main_thm2` re-quantified `h1`, `h2` and merged conjuncts,
     so the basis proof's `qspecl_then` order didn't carry over.

None of these is deep. The integration risk is low; what costs time is
*finding* which basis_ffi lemma is usable as stated.

## Time

Times are from my own timestamps (HKT, 2026-10-15). The hol-lsp MCP tools
**were available**, and all interactive proof work was done with them
(`diagnostics`, `goalState`, `eval`, `restart`).

| step | wall time |
|---|---|
| 0. wait for the shared base rebuild | 02:41–03:15 (34 min). Overlapped with reading basis_ffi/cfMain/cfStore/2024 code and drafting all six files (02:41–02:55) |
| 1. clock model | 03:15–03:17 (2 min to green) |
| 2. `Clock.now` + CF spec | 03:17–03:20 (3 min) |
| 3+4. composed world + whole-program theorem | 03:21–03:28 (7 min) |
| 5. end-to-end example + Lib | 03:28–03:34 (6 min) |
| 6. write-up, PR | 03:35–~03:55 |

From a built base to the end-to-end theorem took **19 minutes**. Writing the
drafts during the base build (14 min) took the design decisions off the
critical path.

**Waiting on checks:**

- **Holmake:** 10 runs, 134 s in total (4.7–30 s each). About 4.5 s of each
  run is fixed overhead: scanning 322 directories of the base project plus
  the `asl-equiv` preexec.
- **hol-lsp `diagnostics`:** about 35 calls, not timed one by one. Small
  files answered in under ~15 s. `ffiSpikeClockWorld` (460 lines) and the
  example (which loads basisProg's translator state) took roughly 20–60 s
  per call.

  A fair upper bound for all check-waiting is ~10 of the 19 minutes. That
  is about half the active time, which makes it the main cost after the
  design.

Using `basis/basis-heap` as `HOLHEAP` (instead of `misc/cakeml-heap`)
avoided reloading basisProg in every theory (cf-spike measured ~50 s per
theory for that).

## Estimate: a socket/network component on the same route

A component with:

- file descriptors as byte streams;
- `accept`, `select`, nonblocking `read`/`write`;
- arrival schedules chosen by the environment, with fairness assumptions.

**What this spike gives for free.** The integration pattern is the same, so
plan ~400–500 lines and well under a day of agent time:

- the composed world (wrapped oracle, extended projections);
- `parts_ok` via reused basis lemmas, plus per-name lemmas for the new part;
- the `basis_view` trick for reusing the file-system extraction;
- the compositional initial-heap lemma;
- the whole-program theorem and the Lib.

The new part's own lemmas grow with its number of FFI names; everything
else carries over almost line for line.

**What is genuinely new, and where the cost is:**

1. **The model** (fsFFI is 410 lines, fsFFIProps 1510). For each socket,
   the state is: incoming bytes as a schedule (an `llist` of chunks, like
   `numchars`), outgoing bytes written so far, pending connections as a
   schedule, and the fd table. There are about 6–8 FFI functions with byte
   encodings for results and errors (EAGAIN). Estimate: 500–1000 lines, and
   1–3 days for an agent with review.
2. **The CF library** (TextIOProof is ~5500 lines, much of it about line
   buffering). A minimal `Socket` module (accept, read-some, write-some,
   select over a list) with specs: 1000–2500 lines, several days.
3. **Fairness.** Fairness assumptions on the schedules (e.g. "every
   selected fd eventually becomes ready") are plain predicates on the
   schedule, like `clock_mono`, so they fit into the model easily. *Using*
   them is the hard part, because liveness needs program-level arguments:
   a loop terminates or makes progress because the schedule is fair. That
   is proof-engineering in the application, not integration.
4. **Servers don't terminate.** All of basis_ffi's whole-program theorems
   (and ours) are about `Terminate`. A server needs a whole-program theorem
   about `Diverge io_events` (an infinite trace) from a CF spec with
   `POSTd` / `cfDiv`. cfMain has no `call_main_thm` for divergence, so that
   is new framework work: estimate 300–800 lines and the riskiest part.
   Extracting "what was sent on each connection" from an infinite trace
   also needs a coinductive or prefix-wise analogue of `extract_fs`.

**Total:** roughly 2–4 kLOC, 1–3 weeks of supervised agent work. Of that,
integration (what this spike measured) is under 10%; most of the cost is the
model, the specs and divergence.

## Would a more modular basis_ffi be worth upstreaming?

**Yes, at modest cost.** The spike's world lemmas are already nearly generic:
only `clock_part_return` and the name lists mention the clock. A
parameterised version could replace today's `ext` (which, as shown, can't
carry state or support CF):

```
basis_ffi_with (ns, part : 'x ffi_part) ext cl fs x
  state      : (mlstring list # IO_fs) # 'x
  oracle     : names of part → part's ffi functions on the 'x component,
               other names → basis_ffi_oracle ext (lifted)
  proj1/proj2: basis_proj1/2 extended with mk_proj1/2 part
assumptions on part:
  its names are disjoint from the basis names and non-empty,
  its functions preserve buffer lengths,
  encode is injective (decode ∘ encode = SOME)
theorems:
  parts_ok_basis_ffi_with, extract via a basis_view as here,
  whole_prog_spec_with (precondition COMMANDLINE * STDIO * IOx part x)
  and a prove_sem_thm that takes the world from the spec
```

Iterating it (one extra part whose state is itself a product) covers
several components. Cheap, independent improvements worth upstreaming on
their own:

- state `oracle_parts*` about the oracle, not a semantic state;
- export `IMP_STDIO_general`, or the compositional `*_precond` route used
  here;
- state `STDIO_precond` with `Mem 1`;
- make `prove_sem_thm` take the FFI term and theorem list as parameters.

Estimate: 300–500 lines of change in basis_ffi and basis_ffiLib, no change
to any library spec. The ripple is limited to the ~6 files that already
mention `ext` (ag32 proofs, repl, bootstrap), because the default instance
(no extra part, `'x = unit`) can keep today's statements as corollaries.

## Assumptions made

1. The clock's state is a schedule of readings (`num llist`), with no time
   unit specified. Monotonicity is an *assumption* (`clock_mono`), not
   built into the model.
2. Readings must be < 2^64 (`clock_fits`). Larger readings are excluded by
   assumption rather than modelled as a failure.
3. Encoding: an exactly 8-byte buffer, big-endian `n2w8`, and `conf`
   ignored. An exhausted schedule or a wrong buffer size makes the call
   `FFI_failed`.
4. `now : unit -> int` returns a non-negative integer (`NUM`).
5. The composed world uses the basis oracle with `no_ext`, so it has no
   further components.
6. Only the main whole-program shape was adapted: successful termination,
   `post` on the file system, no extra precondition. The `spec2`, `SOME`
   and `ffidiv` variants were not.
7. The whole-program result talks only about the file system. Clock events
   are filtered out before replay (`clock_extract_fs`), and the final clock
   state isn't exposed.
8. stdout is stated as in basis's hello example: the final file system is
   `add_stdout fs out`, i.e. `out` was appended to stdout.
9. `basis/basis-heap` is the build heap (the recipe suggests
   `misc/cakeml-heap`), to avoid reloading basisProg per theory.
10. Theory names are prefixed `ffiSpike`.
