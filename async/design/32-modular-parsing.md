# 32: Modular parsing: audit and design (PROPOSAL, nothing refactored)

**Status:** this is the audit and the design only. No theory has been
changed, and the refactor waits for your OK. Branch
`spike/modular-parsing`, from `spike/http-bodies`.

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

**The design:**
1. A *framed request protocol* interface (four parameters, four
   obligations), with the server, safety, liveness and CF pipeline proved
   **once** against it. Strict, `_h`, `_b` and KV become instances.
2. Inside the grammar, *components*: request line, header block and body
   framing, each with the same four-fact bundle, composed by a sequencing
   combinator that preserves the bundle. Adding chunked encoding then
   touches one component.

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
the one way it departs from the interface below (§2.4).

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
    (∀s t. P.parse s = PInvalid ⇒ P.parse (s ++ t) = PInvalid) ∧               (* P3 *)
    (∀r. P.valid r ⇒ P.print r ≠ [])                                          (* P4 *)
End
```

- **P3 form.** The obligation is the *extension* form. It is what the
  `_h`/`_b` proofs actually establish, and it implies the
  "never-a-prefix" form the Drain uses.
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
| asyncProtoProg, asyncProtoSpec | asyncHttpSockProgH/SpecH | the CakeML handler, its CF spec (§2.5) |
| asyncProtoProgram | Main/Semantics/Spec | the whole-program theorem, parametric in the instance's CF facts (§2.5) |

**Each instance then supplies:**
- `P_x` and `resp_x`;
- `proto_ok P_x`, which is P1–P4 from its existing parser lemmas: about
  20 lines each, since all four facts are already proved;
- the spec equality lemma;
- the translation and `main` (§2.5).

**Re-deriving the existing results.** `http_handler_b files =
proto_handler P_b (print_response o bhandle files)` holds by `fix`
uniqueness (both are `fix` of the same body), and likewise for `_h` and
strict. So every existing theorem *statement* is re-derivable from the
generic one, without changing it. I propose to prove those re-derivations
as `…_via_proto` corollaries alongside the existing proofs, and to let
you retire the old proofs later.

### 2.3 Inside the grammar: components and a sequencing combinator

Each grammar part is a *component parser*: the same four-fact bundle, but
over a part of the request rather than a whole request:

```
comp = <| valid : 'a -> bool; print : 'a -> string; parse : string -> 'a presult |>
```

| component | value | today's code it would replace |
|---|---|---|
| `method_c` | `"GET"` / `"POST"` (`+ " "`) | the `get_sp`/`post_sp` dispatch in `parse_brequest` |
| `line_c` | `(path, version)` up to and including CRLF | `split_path` + `sp_http10/11` (bline) |
| `headers_c` | header list up to and including the blank line | `parse_headers` (already this shape: `HDone hs rest` / `HMore` / `HBad`) |
| `body_c hs` | the body, **depending on the headers** | `bbody` (Content-Length framing) |

**The combinator** is a dependent sequence. The second component may
depend on the first's value, as the body depends on the headers:

```
seq c1 c2 : ('a # 'b) comp
  parse s  = case c1.parse s of
               PComplete a rest => (case (c2 a).parse rest of
                                      PComplete b rest' => PComplete (a, b) rest'
                                    | x => x)
             | x => x
  print (a, b) = c1.print a ++ (c2 a).print b
  valid (a, b) = c1.valid a ∧ (c2 a).valid b
```

**Theorem (once): `comp_ok c1 ∧ (∀a. c1.valid a ⇒ comp_ok (c2 a)) ⇒
comp_ok (seq c1 c2)`.**
- P1, P2: by the components' P1, P2.
- P3: if c1 is invalid, it stays invalid. If c1 is complete and c2 is
  invalid on the rest, then c1 extends (P1 + P2 give extension) and c2
  stays invalid.
- P4: from c1's P4.

So:
- A request protocol is a `seq` of components, plus a map from the nested
  tuple to the request type.
- Its `proto_ok` is the composition theorem plus each component's bundle.
- **Adding chunked encoding** replaces `body_c` by a `body_c'` (length *or*
  chunked framing, chosen from `hs`). Only `body_c'` and its bundle are
  new; nothing above `proto_ok` changes.
- **New methods** extend `method_c`'s value set.
- **New header rules** (like http-nobody's) are a stricter
  `headers_c.valid`, whose bundle proof is the old one plus the new
  conjunct.

**Matching the trusted printers.** The specs (approved, owned by you)
define `print_brequest` monolithically. The instance proves an equality,
`print_brequest r = (seq …).print (to_tuple r)`, by unfolding: about 10
lines per spec.

**The linear-time bug is fixed once.** `line_c` and `headers_c` are
written with the shared-recursion splits, so every instance gets linear
parsing.

### 2.4 KV: the answering step

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

### 2.5 The translator and CF side

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
     translator quirks stay per instance, but the components of §2.3 are
     translated once, so a new instance mostly composes already-translated
     components);
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

### 2.6 Estimate

| phase | contents | size | time |
|---|---|---|---|
| 1 | asyncProto: interface, derived lemmas; `proto_ok` for strict, `_h`, `_b` from their existing lemmas (validates the interface) | ~350 lines | 0.5–1 day |
| 2 | generic server and safety (Server, Safe, SockModel); `…_via_proto` re-derivations | ~450 lines | 1 day |
| 3 | generic liveness (Machine, Drain, Live) | ~1,400 lines, mostly a parametric port | 1.5–2 days |
| 4 | generic CakeML handler and CF spec, generic whole-program theorem; a `_b` program re-derived through them (a new program value; the existing one is untouched) | ~600 lines | 1.5–2 days (risk: translator and polymorphic datatype, CF with higher-order arguments) |
| 5 | grammar components and `seq`; `_b`'s parser re-expressed as a composition (equality with `parse_brequest`); linear splits once | ~700 lines | 2 days |
| optional | chunked bodies as a `body_c'` instance (spec first, as for bodies) | ~400 lines + spec | 1.5 days |
| KV | bounded-`ans` obligation (§2.4); KV's global part is note 30's | +~200 lines | +1 day |

The total for phases 1–5 is about **3,500 lines, 7–9 worker-days**.
After it, a new instance costs about **200–300 lines** (its components'
bundles, the spec equality, the translation, `main`) instead of
~2,500.

### 2.7 Additive plan

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

## 3. Assumptions made

1. The interface obligations are P1–P4 in the *extension* form of P3,
   because that is what every existing parser proves.
2. The response is a parameter, not part of the protocol: the same
   framing can serve different servers (files, echo, KV).
3. KV enters through the answering computation (note 30's option A), not
   through shared state in the model.
4. Trusted specs stay monolithic and unchanged. The modular structure
   lives below them, connected by equality lemmas.
