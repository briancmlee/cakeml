# 32: Modular parsing: audit, design and progress

**Status:** you approved the design (refined scope). **Phase 1 is done**
(§4): the interface, its derived lemmas, and `proto_ok` for all three
existing parsers. Phase 2 has not started. Branch `spike/modular-parsing`,
from `spike/http-bodies`.

**Your requirement** (from the review of #55):
- whether a part of a request parses should be mostly independent of the
  other parts;
- the format should be extensible (chunked bodies, new methods, new
  header rules);
- changing the supported format should not ripple into the rest of the
  proofs, once the right theorems about it are proved.

**Short answer:** this is achievable, and cheaper than it looks. The
safety and liveness pipelines already use the parser only through four
facts. The `_b` pipeline is a renamed copy of `_h`: of its 2,249
non-parser lines, 64 differ.

**Scope** (refined by you): the goal is (a), principled *separation* of
each server's parsing and format from everything else.
- One generic pipeline (safety, liveness, and KV where it fits) is proved
  once, parametric in a protocol interface.
- Strict, `_h`, `_b` and KV become instances that only discharge the
  interface lemmas.
- §2.4 covers what stays per instance on the CakeML side.
- Grammar-as-components is not a goal (one paragraph, §2.6).
- §2.5 states the limits: the formats the interface excludes.

**The design:** a *framed request protocol* interface (three parameters,
four obligations), plus an answering parameter, with the server, safety,
liveness and CF pipeline proved **once** against it.

## 1. Audit

### 1.1 What the pipelines use about the parser

I grepped every non-parser theory of the three HTTP pipelines, and the KV
spec, for parser and grammar names:
- strict: `http-model`, `http-safety`, `http-liveness`;
- `_h`: `http-headers`, `http-liveness-h`;
- `_b`: `http-bodies`;
- KV: `spike/http-kv`, which has the spec and note 30. The implementation
  branch does not exist yet.

Below, X is `""`, `h` or `b`.

| fact (instance names) | statement shape | used by |
|---|---|---|
| **P1 print → parse** `parse_print` / `parse_hprint` / `parse_bprint` | `valid r ⇒ parse (print r ++ rest) = Complete r rest` | Server (via extend, parse_all), Machine, Drain |
| **P2 parse → print** `parse_complete` / `parse_hcomplete` / `parse_bcomplete` | `parse s = Complete r rest ⇒ valid r ∧ s = print r ++ rest` | Machine, Drain |
| **P3 invalid stays invalid** `parse_invalid` / `parse_hinvalid` / `parse_binvalid` (from `…_invalid_ext`) | `parse s = Invalid ⇒ ∀t r rest. valid r ⇒ s ++ t ≠ print r ++ rest` | Drain (`parse_all_invalid_ext`, `stopped_invalid`) |
| **P4 printed requests are non-empty** `print_hrequest_nonempty` (local, by unfolding `print_…_def`) | `print r ≠ []` | Live (`parse_all_X_printed`), termination of `parse_all_X` (`…_shorter`) |
| derived: `parse_X_extend` | `parse s = Complete r rest ⇒ parse (s ++ t) = Complete r (rest ++ t)` | Server, Safe, Drain |
| derived: `parse_all_X` + `…_Complete`, `…_shorter` | the complete requests at the front | everywhere |
| derived: `parse_all_Xrequests`, `…_print(ed)`, `…_mono`, `…_prefix`, `…_not_complete` | printed requests parse to themselves; monotone | Safe, Machine, Drain, Live |
| spec-level: `Xrequests_def`, `Xresponses_def`, `no_full_Xrequest_def` | `bytes (FLAT (MAP print rs))`, `bytes (FLAT (MAP resp rs))` | Safe, Live (unfolded only to this shape) |
| the response function | `print_response o handle files` / `… o hpath` / `print_response o bhandle files` | Server, Machine, Drain: only as `MAP resp` |

Nothing else is used: no fact about the grammar's internals, the header
block, or the body.

- **Every derived fact follows from P1–P4.**
- **The bite-level `print_Xrequest_unique` also follows from P1 + P2**:
  both sides parse to the same thing.
- **The response function is used only as an arbitrary `'r → string`.**

**KV** (`HttpKvSpec`, note 30 §4 option A) uses the same framing
vocabulary: `valid_brequest`, `brequests`, `no_full_brequest`. It answers
through a `Kv` action that the loop performs on a shared store, so its
*answering step* is a short computation, not a pure function. That is
the one way it departs from the interface below (§2.3).

### 1.2 Where the duplication lives

The table below compares each `_b` file with its `_h` source after
applying the identifier mapping I used to generate it. The "differ"
column counts lines, which are names, ancestors, comments, or the
response function.

| file (`async/http-bodies/`) | lines | differ from renamed `_h` |
|---|---|---|
| asyncHttpServerB | 215 | 7 |
| asyncHttpSafeB | 154 | 8 |
| asyncHttpSockModelB | 57 | 5 |
| asyncHttpSockSpecB | 203 | 15 (the response function, the request constructor) |
| asyncHttpMainB | 72 | 2 |
| asyncHttpSemanticsB | 131 | 9 |
| asyncHeadlineB | 27 | 6 |
| asyncHttpMachineB | 414 | 1 |
| asyncHttpDrainB | 563 | 1 |
| asyncHttpLiveB | 381 | 5 |
| asyncHttpSpecB | 32 | 5 |
| **total** | **2,249** | **64 (2.8%)** |

The strict pipeline is the original these were adapted from (`_h` was
derived from it by hand, with partly different proofs).

| strict file | lines | identical lines in the `_h` version |
|---|---|---|
| asyncHttpServer | 265 | 61% |
| asyncHttpSafe | 169 | 70% |
| asyncHttpSockSpec | 338 | 83% |
| asyncHttpMachine (http-liveness) | 414 | 89% |
| asyncHttpDrain (http-liveness) | 382 | 52% (`_h` grew partial reads) |

**What is genuinely per-instance today:**

| piece | strict | `_h` | `_b` |
|---|---|---|---|
| parser and its P1/P2 proofs | asyncHttpParse (305) | asyncHttpParseH (488) | asyncHttpParseB (531) |
| P3 (invalid stays invalid) | (in asyncHttpParse) | asyncHttpParseHExt (183) | asyncHttpParseBExt (117) |
| translation of parser and responder | asyncHttpSockProg (81) | asyncHttpSockProgH (88) | asyncHttpSockProgB (251, incl. the linear-time fix) |

The generic pieces already shared are `asyncServerWith`,
`asyncServerWithUses`, `asyncRunOkGen`, `asyncSWSock` (any `server_with
hf`), and the M4 loop. That is about **2,500 lines duplicated per
instance**. A fourth instance (KV, or chunked bodies) would add another
copy.

There is also a cost beyond line count: **the linear-time parsing bug
lives in the copies.** It had to be found and fixed per pipeline
(`_b` in 2d54fd809; m4-server is porting it to `_h`).

## 2. Design

### 2.1 The interface: a framed request protocol

```sml
Datatype: presult = PComplete 'r string | PIncomplete | PInvalid End

(* the four parameters *)
Datatype:
  proto = <| valid : 'r -> bool; print : 'r -> string;
             parse : string -> 'r presult |>
End

(* the four obligations (P1–P4 of §1.1) *)
Definition proto_ok_def:
  proto_ok P ⇔
    (∀r rest. P.valid r ⇒ P.parse (P.print r ++ rest) = PComplete r rest) ∧     (* P1 *)
    (∀s r rest. P.parse s = PComplete r rest ⇒ P.valid r ∧ s = P.print r ++ rest) ∧ (* P2 *)
    (∀s t r rest. P.parse s = PInvalid ∧ P.valid r ⇒ s ++ t ≠ P.print r ++ rest) ∧ (* P3 *)
    (∀r. P.valid r ⇒ P.print r ≠ [])                                          (* P4 *)
End
```

- **P3 form.** The obligation is the *never-a-prefix* form: no extension
  of an invalid buffer is a printed valid request followed by anything.
  It is what every Drain uses and what all three parsers prove
  (`parse_invalid`, `parse_hinvalid`, `parse_binvalid`). The stronger
  *extension* form ("`PInvalid` stays `PInvalid`") is proved for `_h` and
  `_b` but not for strict, and nothing needs it. (The proposal first said
  extension form; Phase 1 corrected it, §4.)
- **Response function.** It is a separate parameter, `resp : 'r ->
  string`. The safety and liveness theorems are proved for every `resp`.

**Proved once, from `proto_ok P` alone** (`asyncProtoScript.sml`):
- `proto_extend`;
- `proto_unique`: valid `r1`, `r2` and `print r1 ++ x = print r2 ++ y`
  imply `r1 = r2 ∧ x = y`. This is the bite lemma, for free;
- `proto_all` (with its termination from P2 + P4), `proto_all_printed`,
  `proto_all_mono`, `proto_all_prefix`, `proto_all_invalid_ext`.

**Generic spec vocabulary** (definitions, not trusted):
- `preqs P rs = bytes (FLAT (MAP P.print rs))`;
- `presps resp rs = bytes (FLAT (MAP resp rs))`;
- `no_full P rest`;
- `proto_safe P resp io`, `proto_live P resp sk io`, `proto_spec P resp lfd prog`.

These have exactly the shapes of HttpSpec's, HttpSpecHeaders' and
HttpSpecBodies'. Each trusted spec is then an instance *by a one-line
equality lemma*, for example
`http_spec_b lfd files prog ⇔ proto_spec P_b (print_response o bhandle files) lfd prog`.
**No trusted file changes.**

### 2.2 Everything above the parser, once

| generic theory | from | contents |
|---|---|---|
| asyncProtoServer | asyncHttpServerH | `proto_handler P resp (fd, buf)` (the same `fix` body with `P.parse`, `resp`), wf/settled, `proto_server`, `proto_handler_serves`, `proto_server_safety` |
| asyncProtoSafe | asyncHttpSafeH | `proto_comp_safe` (the trace bridge) |
| asyncProtoMachine, asyncProtoDrain, asyncProtoLive | the `_h` liveness files | the machine, the partial-read drain, `proto_live_rounds` |
| asyncProtoSockModel | asyncHttpSockModelH | `sproto_handler_unfold` |
| asyncProtoProg, asyncProtoSpec | asyncHttpSockProgH/SpecH | the CakeML handler, its CF spec (§2.4) |
| asyncProtoProgram | Main/Semantics/Spec | the whole-program theorem, parametric in the instance's CF facts (§2.4) |

**Each instance then supplies:**
- `P_x` and `resp_x`;
- `proto_ok P_x`, which is P1–P4 from its existing parser lemmas: about
  20 lines each, since all four facts are already proved;
- the spec equality lemma;
- the translation and `main` (§2.4).

**Re-deriving the existing results.** `http_handler_b files =
proto_handler P_b (print_response o bhandle files)` holds by `fix`
uniqueness (both are `fix` of the same body), and likewise for `_h` and
strict. So every existing theorem *statement* is re-derivable from the
generic one, without changing it. I propose to prove those re-derivations
as `…_via_proto` corollaries alongside the existing proofs, and to let
you retire the old proofs later.

### 2.3 KV: the answering step

KV's handler (note 30 §4, A), on a complete request, *emits* `Kv req` and
writes the answer it gets back, one round later. To cover it, the generic
handler takes an **answering computation** instead of a pure response:

```
proto_handler P ans (fd, buf):
  PComplete r rest => bind (ans r) (λresp. bind (emit (Write fd resp)) (λw. … (fd, rest)))
```

- The stateless instances use `ans r = return (resp r)`. By
  `bind_left_identity` this is *equal* to today's handlers, so nothing
  changes for them.
- KV uses `ans r = map answer_of (emit (Kv r))`.

**Obligations on `ans`:**
- *safety*: whatever `ans r` finishes with is written, so the
  per-connection fact becomes "written ≼ the answers `ans` produced". For
  stateless instances that is `MAP resp rs`. For KV it is the answers to
  the performed `Kv` actions, which note 30's global argument then glues.
- *liveness*: `ans r` finishes within a bounded number of rounds and never
  waits on readiness. That holds for `return` (0 rounds) and for one
  `emit` (1 round). It only changes the machine's round bound (K + 3
  becomes K·(1 + a) + 3).

**Recommendation:** do the stateless generic pipeline first, with `ans`
already in the interface but only `return` instantiated. Add the bounded
`ans` obligation when KV needs it. KV's global part (the store invariant
and the timestamped bridge) is outside this interface either way.

### 2.4 The translator and CF side: what stays per instance

**This can be generic.**

- **One CakeML handler, higher-order in the parser and the answerer:**

  ```sml
  fun proto_handler parse ans fd buf =
    case parse buf of
      Pcomplete r rest => Async.bind (ans r) (fn resp =>
                            Async.bind (Async.emit (Write fd (String.implode resp)))
                                       (fn w => proto_handler parse ans fd rest))
    | Pincomplete => (readable; read; proto_handler parse ans fd (buf @ String.explode s))
    | Pinvalid => Async.return ();
  ```

- **Its CF spec is proved once**, with hypotheses on the argument values:
  - `(LIST_TYPE CHAR --> PRESULT_TYPE R) P.parse parse_v`, which is
    exactly the translator's certificate shape;
  - `∀r rv. R r rv ⇒ app ans_v [rv] … (COMP … (srelabel (ans r)))`;
  - a relation `R` for the request type.

  The polymorphic datatype `'r presult` is registered once, as `option`
  is; the translator handles type-parametric datatypes. This is
  `sserver_with_spec`'s pattern (§2 of note 20), one level up.
- **Per instance, what remains:**
  1. translate its parser into `'r presult` and its responder (the
     translator quirks stay per instance, though the linear-time splitting
     helpers can be
     shared once a generic splitting library exists);
  2. instantiate the CF spec (about 20 lines);
  3. `main` and the whole-program theorem.
- **The whole-program theorem.** Every instance's `asyncHttpSemanticsX` is
  the same argument (`call_main_thm_div`, `sonly_init_heap`, the
  `Decls` theorem of the instance's program). The generic part,
  `proto_semantics`, takes as hypotheses the instance's `Decls` theorem,
  the lookup of `main`, and its `main_spec`. What stays per instance is
  computing the `Decls` theorem and `prog_syntax_ok` (EVAL): about 40
  lines of boilerplate.
- **Why not fully generic:** a CakeML program is a concrete declaration
  list, and its `Decls` theorem and `prog_syntax_ok` are computed by
  evaluation per program. That is irreducible but mechanical.

### 2.5 What the interface excludes (the limits, explicitly)

Each obligation rules out a class of formats. Each is listed below with
what lifting it would cost.

1. **Close-delimited or EOF-terminated requests** (P1).
   - P1 says a printed request parses back *followed by anything*. So a
     request must be *self-delimiting*: where it ends is determined by its
     own bytes, and "complete" is decidable from a prefix.
   - This excludes bodies delimited by connection close (RFC 9112 allows
     these only for responses; for requests they are already invalid), and
     any format whose end depends on bytes *after* the request.
   - Lifting it would need the end of stream as part of the parser's input
     (`parse : string → bool (* eof *) → …`) and the handler's EOF branch
     to re-parse. That is a moderate change to the interface and machine.
2. **Lenient parsing of equivalent spellings, unless recorded** (P2).
   - P2 says whatever parses as complete is *exactly* `print r ++ rest`.
     So the request value must determine its bytes, and the parser cannot
     quietly accept a non-canonical spelling (`Content-Length: 007`,
     `get` instead of `GET`, extra whitespace) and normalise it.
   - Such formats are still *expressible*: the request type records the
     raw spelling (for example the raw value string), validity checks it is
     well-formed, and the response function ignores the difference. This
     is a limit on how the spec is written, not on what can be accepted.
3. **Error recovery and resynchronisation** (P3, and the handler).
   - P3 says invalid stays invalid, and the generic handler stops at an
     invalid buffer. So a server that skips a bad line or request and
     carries on is excluded.
   - Lifting it would need `PInvalid` to carry a skip length, and safety
     and liveness to account for skipped bytes (their spec would have to
     say which bytes may be skipped). This is a real extension.
4. **Anything but one ordered request stream with one response each.**
   The interface is FIFO pipelining: the i-th response answers the i-th
   request. Excluded:
   - interim responses (`100 Continue`, written before the body is read);
   - responses that stream while the request is still arriving;
   - out-of-order or multiplexed responses (HTTP/2 streams, server push).

   "No response" can be modelled as an empty response string.
5. **Connection management** (the model has no `close`).
   - `Connection: close`, closing after an invalid request, and timeouts
     are not expressible. The handler keeps the connection open, and
     liveness is per request.
   - This is a limit of the socket model (no close operation), not of the
     interface.
6. **State across requests on a connection** (P1–P3 make `parse` a
   function of the buffer alone).
   - Excluded: protocol switches (`Upgrade` to WebSocket, `CONNECT`
     tunnels), and parsing that depends on earlier requests (negotiated
     encodings).
   - Lifting it would need a per-connection parser state threaded through
     the handler, which is a moderate interface change.
7. **Shared state across connections**, except through the answering
   computation (§2.3). That covers KV-style servers whose answers come
   from an action the loop performs. A server whose *parsing* depends on
   shared state is excluded (item 6).

**Allowed, for contrast:** binary or length-prefixed protocols, any
self-delimiting text format, header continuation lines (`obs-fold`, which
are inside the header block), and `Content-Length` and chunked bodies.
Chunked bodies are self-delimiting by the zero-length chunk.

### 2.6 Grammar components (not a goal, noted for completeness)

The parser *inside* an instance could itself be built from components
(method, request line, header block, body framing given the headers),
each with the same four-fact bundle, composed by a dependent sequencing
combinator with one theorem: bundles compose. A format change such as
chunked bodies would then touch one component's bundle. Per your
scoping, this is not proposed now. The interface in §2.1 does not depend
on it, and it could be added later without touching the generic pipeline.

### 2.7 Estimate

| phase | contents | size | time |
|---|---|---|---|
| 1 | asyncProto: interface, derived lemmas; `proto_ok` for strict, `_h`, `_b` from their existing lemmas (validates the interface) | ~350 lines | 0.5–1 day |
| 2 | generic server and safety (Server, Safe, SockModel); `…_via_proto` re-derivations | ~450 lines | 1 day |
| 3 | generic liveness (Machine, Drain, Live) | ~1,400 lines, mostly a parametric port | 1.5–2 days |
| 4 | generic CakeML handler and CF spec, generic whole-program theorem; a `_b` program re-derived through them (a new program value; the existing one is untouched) | ~600 lines | 1.5–2 days (risk: translator and polymorphic datatype, CF with higher-order arguments) |
| 3b | **cause of actions** (for async-spike's Level 2 / option C): the generic handler emits new actions in round j only if round j−1's snapshot had its fd Readable or a Data response, proved once for `proto_handler` (§2.9) | ~300–500 lines | 1 day |
| optional | a shared linear-time splitting library used by all instances' translations | ~150 lines | 0.5 day |
| KV | bounded-`ans` obligation (§2.3); KV's global part is note 30's | +~200 lines | +1 day |

The total for phases 1–4 is about **2,800 lines, 4.5–6 worker-days**.
After it, a new instance costs about **200–300 lines** (its `proto_ok`
proof, the spec equality, the translation, `main`) instead of ~2,500.

### 2.8 Additive plan

1. **New directories only**: `async/http-proto/` for the generic theories
   and `async/http-proto-inst/` for the instance glue. No existing file is
   edited, and no existing theorem statement changes.
2. **Order:** phase 1 first, because it is cheap. It checks the
   interface against all three existing parsers before anything is built
   on it. If an instance cannot discharge `proto_ok`, the interface is
   wrong and the design is revisited before phase 2.
3. **Re-derivations:** each existing headline (`http_prog_h_spec`,
   `http_prog_b_spec`, and strict's `http_semantics_prog`) gets a twin
   proved through the generic pipeline, about 30 lines each.
4. **Retiring the copies** (`http-headers`, `http-liveness-h`,
   `http-bodies`' non-parser theories) is a later decision of yours. Once
   the twins exist, the old theories can be archived without losing a
   theorem.
5. **Builds:** every Holmake through `holslot`, `-j1`; one hol-lsp.

### 2.9 Later deliverable: the cause-of-actions lemma (requested by async-spike)

Quiescence for HTTP (option C, Level 2 declared interest, on top of this
pipeline) needs, per handler: "the handler emits new actions in round j
only if round j−1's snapshot had its fd Readable or a Data response".
Today that would be one proof per drain machine. In the generic pipeline
it is one proof, about `proto_handler P resp`:

- **Why no new interface fact is needed:** the handler's emissions in a
  round depend only on its buffer. It writes the responses to the
  complete requests at the front (`proto_all`), then either stops
  (`PInvalid`) or waits for readability (`PIncomplete`). The buffer
  changes only when a read returns Data. So between two Data events the
  handler is either stopped or waiting on its fd, and emits nothing new.
  That uses only the handler's structure and P2 (a complete parse
  consumes bytes), not the grammar.
- **Statement shape:** it will mirror async-spike's echo version, the
  same round indexing and snapshot predicate, so that one quiescence
  argument serves both. That version is being proved now and I have asked
  for its exact statement.
- **Where:** after Phase 3 (it reuses the generic machine's rounds), and
  kept friendly to a Level 2 server (`server_with2`, #53).

## 3. Assumptions made

1. The interface obligations are P1–P4 with P3 in the *never-a-prefix*
   form, because that is what every existing parser proves and what the
   Drains use (corrected in Phase 1; see §4).
2. The response is a parameter, not part of the protocol: the same
   framing can serve different servers (files, echo, KV).
3. KV enters through the answering computation (note 30's option A), not
   through shared state in the model.
4. Trusted specs stay monolithic and unchanged. The generic structure
   lives below them, connected by equality lemmas.
5. Per your scoping, grammar components (§2.6) are not part of the plan.

## 4. Progress

### Phase 1: the interface, validated against all three parsers (DONE)

- **`async/http-proto/asyncProtoScript.sml`** (~260 lines, 17 proofs):
  - `presult`, `proto`, `proto_ok` (P1–P4), with accessors
    `proto_print`, `proto_complete`, `proto_invalid`, `proto_nonempty`;
  - derived once: `proto_unique` (the bite lemma), `proto_complete_shorter`,
    `proto_extend`, `proto_prefix` (a proper prefix of a printed request
    is `PIncomplete`);
  - `proto_all` and `proto_all_complete`, `_not_complete`, `_requests`,
    `_print`, `_printed`, `_mono`, `_prefix`, `_invalid_ext`: every
    `parse_all_X` lemma the pipelines use;
  - the generic spec vocabulary: `preqs`, `presps`, `no_full`,
    `proto_safe`, `proto_live`, `proto_spec`.
- **`async/http-proto-inst/`**, one theory per parser (~50 lines each):
  - `proto_ok_strict`, `proto_ok_h`, `proto_ok_b`. Each is P1–P4 from the
    parser's existing `parse_Xprint`, `parse_Xcomplete` and
    `parse_Xinvalid`, plus P4 by unfolding the printer;
  - `http_spec_proto`, `http_spec_h_proto`, `http_spec_b_proto`. Each
    trusted spec equals `proto_spec` for its protocol, by unfolding:
    ```
    http_spec   lfd files prog ⇔ proto_spec P_strict (print_response o handle files) lfd prog
    http_spec_h lfd files prog ⇔ proto_spec P_h (print_response o handle files o hpath) lfd prog
    http_spec_b lfd files prog ⇔ proto_spec P_b (print_response o bhandle files) lfd prog
    ```
- **One correction to the design:** P3 is the never-a-prefix form, not
  the extension form (§2.1). The strict parser proves only the former, and
  the Drains need only the former. This is a *weaker* obligation, so
  future instances get easier, and no generic lemma needed the stronger
  one.
- **Checks:** no cheats; `Holmake -j1` (through holslot) green in both new
  directories. No existing file was changed.

**Verdict:** the interface fits all three parsers without changes beyond
the P3 form. Phase 2 (generic server and safety) can build on it.

