# programs/translate: generated handlers and glue

The async translator (design note 44 on the spike branches #114/#130/#133) on the final L0 layout. A server's handler is written once as a recursive HOL equation in bind style. The tooling generates everything else, CakeML and CF proof:
- the model;
- the handler's CakeML and its CF proof;
- the server, `with_store`, `main`, and the whole-program semantics.

The trusted specification's theorem then follows in a few lines from the model-level safety and liveness results.

## Headlines

| theorem | statement | what is generated |
|---|---|---|
| `translateKv.gkv_prog_spec` | `kv_spec 3w gkv_prog` | the KV handler (14-line equation), its server (tagged skeleton + `with_store`), `main`, the program |
| `translateHttp.http_gpb_prog_spec` | `http_spec 3w demo_files http_gpb_prog` | the generic proto handler (13-line equation), its server (`sserver_with`), `main` on the bodies protocol, the program |

These are the statements of `kvHeadline.kv_prog_spec` and `httpSemantics.http_prog_spec`, for programs whose handler and glue are generated.

## Files

**Libraries:**
- `translateLib`: `define_async` builds the model (fix, contractiveness, unfold, wf); `translate_async` builds the handler's CakeML and CF proof.
- `translateGlueLib`: `translate_server` (skeleton on the handler), `translate_store` (`with_store`), `translate_main` (`run_i`), `translate_program` (declarations, `main` lookup, `prog_syntax_ok`, `semantics_prog`).

**Socket library wrappers, written once:** `translateSock` (`swrite`, `sread`) and `translateKvSock` (`kswrite`, `ksread`, `kquery` in the `with_store` vocabulary).

**Instances:** `translateProto` and `translateProtoGlue` (proto handler, bridge `gproto_eq`, server), `translateHttp`, `translateKv`.

## What stays hand-written per program

Each program still needs:
- the handler equation;
- a bridge from the generated model to the existing one (`gproto_eq`, `gkv_eq`, by `fix_unique`, about 12 lines);
- the statements given to the glue generator;
- the final theorem (about 5 lines).

The glue's proofs are templates instantiated by the generator; they are not written per program.
