# 44. A translator for the async monad

The goal: write a handler once, in idiomatic bind style, as a HOL model term.
From that term, generate two things automatically:

- its CakeML code, as calls to the verified async library;
- the CF theorem that the code implements the model term.

Today each server has two hand-written parts:

- the CakeML code: the `Quote` blocks in asyncM4ServerProg, asyncChatProg and asyncProtoProg;
- the CF proof that walks it: handler_spec_d (~80 lines) and sproto_handler_spec_d (~100 lines).

Both parts mirror the model term one combinator at a time. This note gives the design and a working prototype for the echo server (`async/translate/`). It ends with a plan for HTTP through the generic proto handler.

## 1. The judgment

The translator proves this for a model function `f : τ1 → … → τk → α M`:

    ∀n x1 v1 … xk vk. INV1 x1 v1 ∧ … ∧ INVk xk vk ⇒
      app p f_v [v1; …; vk] emp
        (POSTv v. &COMPd p ACT B SNAP n (f x1 … xk) v)

- INVi and B are the standard translator's refinement invariants (`get_type_inv`).
- ACT and SNAP fix the vocabulary of actions and snapshots.
- COMPd is the depth-indexed predicate of asyncM4Approx.

`app_COMP_of_approxd` turns this into the real COMP statement, which is exactly what the hand proofs state.

**Why depth-indexed.** The model defines recursion with `fix`, and the CakeML code uses ordinary recursion. Induction on the depth n bridges the two:

- each guarded bind (one whose first part cannot finish before a poll) costs one level of depth;
- so a recursive call under a guarded bind is needed only at depth < n, which is the induction hypothesis.

This is the approximation lemma, applied mechanically.

## 2. Architecture

The input is the model's unfolding equation, `⊢ ∀xs. f xs = BODY`, with `f` free to occur in BODY. Usually this is `handler_unfold` with the body definition rewritten in.

BODY is walked twice, once by each of two functions in `asyncTranslateLib`.

**`gen`** builds the CakeML code. Every combinator becomes a call to the library, and non-variable arguments become explicit `let`s, so the code is already in the A-normal form that `xcf` produces.

| model term                 | CakeML                                                      |
|----------------------------|-------------------------------------------------------------|
| `bind m (λx. k)`           | `let val k = fn x => ⟦k⟧ val m = ⟦m⟧ in bind m k end`       |
| `map (λx. e) m`            | `let val f = fn x => e val m = ⟦m⟧ in map f m end`          |
| `both m1 m2`               | `let val b = ⟦m2⟧ val a = ⟦m1⟧ in both a b end`             |
| `case x of C ys => …`      | `case x of C ys => …` (registered datatype)                 |
| primitive `P a1 … ak`      | `let val ai = ai (non-variables) in P a1 … ak end`          |
| recursive call `f as`      | `f as` (ordinary CakeML recursion)                          |

**`prove_tac`** builds the proof. It reads the model term M from the goal's postcondition, `COMPd … d M v`, and applies one step per combinator:

| M                          | proof step                                                                     |
|----------------------------|--------------------------------------------------------------------------------|
| `bind m g`, m a guarded primitive | `xfun k`; `xlet` m at COMP; the continuation at depth `d − 1` under `0 < d`; then `bind_guarded_any` |
| `bind m g`, otherwise      | the same, at depth d for both parts; then `bind_spec_d`                         |
| `map f m`                  | `xfun f`; `xlet` m at depth d; f's body as a pure value; then `map_spec_d`      |
| `both m1 m2`               | `xlet` both parts at depth d; then `both_spec_d`                                |
| `case x of …`              | `Cases_on x`; `gvs[INV_def]`; `xmatch`                                          |
| primitive or translated function | `xlet` the constructor arguments (`xcon`); the stored spec; `COMP_IMP_COMPd` |
| recursive call             | the induction hypothesis (complete induction on n) at the current depth `< n`   |

The whole proof is `completeInduct_on n`, `xcf f`, one unfolding of the model equation, and then `prove_tac`.

**The primitive table** is a list of records:

    { const, name, spec : ⊢ H ⇒ app p c_v args emp (POSTv v. &COMP …),
      guard : (⊢ (c args []).result = NONE) option, wf }

`return`, `emit` and `readable` are entries in this table, and so is every function the translator has already produced (the echo server calls the generated handler this way).

**Library wrappers are just more entries.** This is how the design accommodates OCaml-Async-like code: `Reader.read_line`, `Writer.write` and a `Tcp.serve`-style server are each written once in CakeML, with a COMP spec and a guard fact, and then used like `emit`. The table records exactly what the proof of a client needs from a primitive: its spec, whether it is guarded, and that it is well formed.

**Contractiveness** is checked syntactically before anything is generated (`check_guarded`): every recursive call must sit in the continuation of a bind whose first part is guarded. In the proof the same fact appears as the depth decrease, so an unguarded program fails early with a clear message, not deep inside the tactic.

**The front end, `define_async`**, makes the model side from the recursive equation alone. It takes a quotation `‘f x = BODY’` in which f occurs, and produces:

- `f_body` (BODY with f abstracted) and `f = fix f_body`;
- contractiveness, proved by the shape of the body (`guarded_bind` at a guarded first part, then `nonexpansive_bind/map/both/const/call`, with a case split on case scrutinees);
- the unfolding equation `f_unfold : ∀x. f x = BODY`;
- `wf_f`, through `wf_fix` and the `wf_*` rules.

So a handler is written once, as an equation, and `define_async` followed by `translate_async` yields the model, the code and both CF theorems. At the moment `define_async` takes one parameter; several would need tupling.

## 3. Pure subterms

The prototype accepts variables, `()` and constructors applied to variables. Anything else is a pure HOL term that the standard translator can handle. The plan for those:

- lift the subterm t with free variables ys to `aux_i ys = t`;
- `translate aux_i_def`;
- emit `let val a = aux_i ys`;
- prove the `xlet` by `xapp` with the translator's certificate. The chat proofs already do this for translated helpers, e.g. asyncChatGCSpec's `gc_tap_s_TAP`.

Case scrutinees that are not variables get the same treatment.

## 4. Level 2 and option C

Level 2 extends the CF library with STEPA2/COMP2d (design/33). The translator's emission then changes only in its table and lemmas:

- the combinators map to the Level 2 library functions;
- `bind_guarded_any`, `bind_spec_d`, `map_spec_d` and `both_spec_d` are replaced by their COMP2d counterparts;
- the judgment's COMPd becomes COMP2d.

Code and proof generation walk the same model term, because the model's combinators are the same at both levels. That is how option C's quiescence comes along: it is a property of the Level 2 library's specs, and the generated proof inherits it by applying them.

## 5. Where the generated code sits

close-v2 is building one canonical library translation chain:

    asyncM4SockServer → socketV2Prog/SocketClose → asyncHLProg (handle loop)
      → asyncHttpSockProg → … → generic proto server → instances

The translator appends to whatever `translation_extends` state it runs in. So a program on that chain is its pure handler/parse/respond translations (standard translator), then `translate_async` for the monadic handler, then a main. The primitive table entries for the socket vocabulary (sreadable, Read/Write/Close actions, `SACT`/`SSNAP`) come from that chain's specs.

## 6. HTTP through the generic proto handler

asyncProtoServer defines `proto_handler = fix proto_body`. The body is a bind-style loop over the socket primitives, parameterised by a parser and a responder, and asyncProtoSockSpec proves it by hand (`PROTO_IMPL`, `sproto_handler_spec_d`, ~100 lines). The plan:

1. **Functional parameters.** The parser and responder are free variables of the model term. The translator treats each as a primitive whose spec is a hypothesis, the `PROTO_IMPL` premise, rather than a stored theorem:
   - code: an extra curried argument;
   - proof: an `app` assumption.

   That needs one extension, primitives whose spec is an assumption. The `xapp` step is the same.
2. **Socket vocabulary.** The table gets sreadable, the socket emit and the srelabel'd vocabulary, plus the guarded-bind rule for that vocabulary (`Async_bind_guarded_spec_any`, now duplicated in five chat files, becomes the library lemma).
3. **Pure parts** (parse step, response rendering) go through §3.
4. **Instances** (KV, chat-over-HTTP) are then pure translations plus one `translate_async` call.

Estimate: about 1 day for the socket table and the hypothesis primitives, after the close-v2 chain lands.

## 7. Prototype results (async/translate/, Holmake green, no cheats)

**Files:**
- `asyncTranslateScript.sml`: the library lemma `bind_guarded_any` (the five chat files keep a local copy of it), plus `readable_NIL` and `wf_readable`.
- `asyncTranslateLib.sml`: `gen`, `prove_tac`, `check_guarded`, `define_async`, `translate_async`.
- `asyncTranslateEchoScript.sml`: the demo, in two parts.

**Part A** translates the existing model (asyncServer's `handler`, `server`). It produces `handler_g_spec` and `server_g_spec`, whose statements are exactly those of the hand-written `handler_spec` and `server_spec` in asyncM4ServerSpec, plus the `_spec_d` versions.

**Part B** writes the echo server once, as two recursive equations (13 lines, below). `define_async` gives the model, `translate_async` gives the code and `echo_g_spec` and `echo_server_g_spec`, and `echo_is_handler : echo = handler` confirms that the generated model is the hand-written one.

    val echo = define_async "echo"
      ‘echo fd =
         bind (readable fd) (λu.
         bind (emit (Read fd)) (λres.
           case res of
             Data d => bind (emit (Write fd d)) (λw. echo fd)
           | Eof => return ()
           | _ => echo fd))’ guards wfs
    val echo_g = translate_async {name = "echo_g", unfold = #unfold echo, ...}

The generated CakeML is printed in the build log. Every combinator becomes a library call, and every non-variable argument is let-bound.

**Cost:**

| what                    | hand-written echo                                              | translator                                                              |
|-------------------------|----------------------------------------------------------------|-------------------------------------------------------------------------|
| model side              | asyncServer: ~60 lines (body, contractive, unfold, wf)         | 13 lines of equations                                                   |
| CakeML                  | 20 lines of Quote                                              | 0                                                                       |
| CF proofs               | 230 lines (asyncM4ServerSpec)                                  | 0                                                                       |
| one-time                | —                                                              | library 521 lines (generic), lemmas 46, demo 97 (both parts, with comments) |

The demo theory builds in ~3 minutes, all four functions together.

**Lessons:**
- `register_type` renames constructors (`NoConn` → `Noconn`, `WouldBlock` → `Wouldblock`). The generator reads the CakeML name off the `TypeStamp` in the type invariant's definition. The hand-written code never met this because it uses `_ =>`.
- Generating ANF code up front keeps the proof's order of `xfun`/`xlet` fixed and independent of `xcf`'s normaliser.
- A `tr` wrapper that prints the failing step and its goal was the effective debugger, because a `--holstate` heap lacks the theory context.

**Next steps, in order:**
1. pure subterms through the standard translator (§3);
2. hypothesis primitives and the socket table, for proto/HTTP (§6), on top of the close-v2 chain (§5);
3. the Level 2 table (§4), once STEPA2/COMP2d exist;
4. several parameters in `define_async`;
5. stores and taps (`with_store`, `with_tap`) as primitives taking DELTA/TAP hypotheses, in the same way as the parser and responder.

## 8. Phase 2: pure subterms, the socket library, proto and the HTTP bodies server

This work is on close-v2's canonical chain (spike/http-v2-prog 784e9f737), in `async/translate/`. Holmake is green and there are no cheats.

**Pure subterms** (`asyncTranslatePure`: `bang_g_spec`). Any pure term that is not a variable or a constructor over variables is lifted to `auxN ys = t`, translated by the standard translator, and called. The proof is `xapp` with the translator's certificate. `if b then m1 else m2` becomes a CakeML `case` on `True`/`False`: HOL hands it over as a bool case, and the translator names the constructors True/False.

**Vocabulary-parametric library.** A `vocab` record holds the library's names (`Async.bind`, `async_map`, `async_both`) and the four rules the proof applies; `echo_vocab` is the abstract echo library. Other additions:
- functional parameters, i.e. the protocol's parser and responder, called through their Arrow certificates (exactly `PROTO_IMPL`);
- case on non-variable scrutinees;
- type variables, so `'r` gets a relation variable `R`, as in `PROTO_IMPL`;
- a precondition `pre` on the parameters (`fd < dimword(:64)`);
- `define_async name nfixed`: fixed parameters plus up to two varying ones.

**The socket library as primitives** (`asyncTranslateSock`, 165 lines, written once): `swrite fd s` and `sread fd`, Writer.write/Reader.read-style wrappers around `Async.emit`. Each has its model, CakeML, COMP spec, guard and wf. They join `Async.return` and `sreadable` in the primitive table.

**The proto handler, written once** (`asyncTranslateProto`):

    gproto prs resp fd buf =
      case prs buf of
        PComplete req rest => bind (swrite fd (resp req)) (λw. gproto prs resp fd rest)
      | PIncomplete =>
          bind (sreadable fd) (λu.
          bind (sread fd) (λro.
            case ro of
              SOME s => if s = [] then return () else gproto prs resp fd (buf ++ s)
            | NONE => gproto prs resp fd buf))
      | PInvalid => return ()

From this, `define_async` and `translate_async` produce the model, the CakeML `gproto_g`, `gproto_g_spec_d` and `gproto_g_spec`, with no hand-written code or proof.

**Glue** (`asyncTranslateProtoGlue`, hand-written, 103 lines):
- `gproto_eq`: `gproto P.parse resp fd buf = srelabel (proto_handler P resp (fd, buf))`, by `fix_unique` (13 lines);
- `gproto_handler_spec`: the statement of `sproto_handler_spec`, for the generated code (3 lines);
- the server and main, which plug the handler into the chain's `sserver_with` and `run_i` (copies of `sproto_server_spec`/`proto_main_spec`).

**The HTTP bodies server** (`asyncTranslateHttpB`):

    http_prog_gpb_spec : http_spec_b 3w demo_files http_prog_gpb

This is the whole-program theorem of `http_prog_pb_spec`, for the program whose handler is generated. It uses the chain's translated parser and responder (`b_parse`, `bresp_demo`) and asyncProtoSemB's per-program boilerplate.

**Cost (proto handler):**

| what            | hand-written (http-proto)                                                         | translator                                     |
|-----------------|-----------------------------------------------------------------------------------|------------------------------------------------|
| model           | proto_body + contractive + unfold + wf (~60) + socket unfold (~30)                 | 13 lines of equation                           |
| CakeML handler  | 15 lines of Quote                                                                 | 0                                              |
| CF proof        | sproto_handler_spec_d 99 + helpers ~50 + spec 9                                   | 0                                              |
| bridge          | —                                                                                 | 16 (gproto_eq, gproto_handler_spec)            |
| server/main     | 4 Quote + 36 proof                                                                | the same (copied)                              |
| one-time        | —                                                                                 | library 726 (generic), socket wrappers 165     |

**Dead ends and lessons:**
- `parse` is an overloaded HOL name (renamed `prs`).
- The CakeML normaliser binds the last argument first, so `fn` comes after the emit chain in `async_map f (emit ..)`.
- `wf_map` and friends are shadowed by later ancestors, so qualify them as `asyncLevel1Theory`.
- `get_type_inv` rejects type variables.
- `sreadable` is polymorphic in the word size: the model's types are instantiated to the vocabulary's before the spec is stated.
- `simp` can't use a spec with Arrow hypotheses at the limit step (use `metis_tac`).

**Next:** Level 2 (§4), `with_store`/`with_tap` as primitives with DELTA/TAP hypotheses (the KV and chat servers), and generating the server and main glue from a `Tcp.serve`-style primitive.
