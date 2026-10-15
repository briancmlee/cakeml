# Handoff: HTTP proofs against the header-tolerant spec (spike/http-headers)

- Branch `spike/http-headers` from `spike/presentation` (19009a4fe), which
  has `spec/HttpSpecHeaders`. PR base: `spike/presentation`.
- `async/http-headers/`: see design/24 §Status for the theory list, plus
  `Makefile`, `http_headers_demo.sh`, `http-headers-demo-transcript.txt`, and
  `http_server_h.sexp` (generated, committed).
- Status: DONE. `http_semantics_prog_headers` and `http_prog_h_safe` proved,
  no cheats, Holmake -j1 green; runnable with plain curl. The original
  HttpSpec results are untouched.
- Not done: liveness (`http_live_h`), as for HttpSpec.

## Assumptions made

1. Copies (`_h`), not generalization. The http-safety pipeline is copied
   with the new parser rather than abstracted over the parser, so the
   strict-spec theories are untouched and each option reads on its own.
2. Versions 1.0 and 1.1 only. Responses stay HTTP/1.0.
3. The program keeps the strict `http_server` code (unused) because it
   extends asyncHttpSockProg, whose `sserver_with` and `respond` it reuses.

## Tool feedback

- The translator renames mixed-case constructors (`HComplete` →
  `Hcomplete`, `GetH` → `Geth`). Quote add_cakeml code must use the
  translated names, and an unknown constructor in a pattern is only caught
  at `xmatch` time.
- A recursive definition with a custom termination proof needs
  `translate_no_ind` and a proof of the generated `_ind` obligation
  (`latest_ind ()`). Otherwise the obligation surfaces as a side condition
  of the callers.
- `MEM` in a translated definition can appear as set membership (`IN`),
  which the translator rejects. Use `EXISTS`.
- `X = p ++ DROP k X` facts make simp loop. Use `IS_PREFIX_APPEND` to get
  a fresh suffix variable instead.
- `a >> b >- c` parses as `(a >> b) >- c`. Parenthesize `(b >- c)` when
  several goals are live.
