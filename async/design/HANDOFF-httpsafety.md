# Handoff: HttpSpec's http_safe for the whole HTTP program (spike/http-safety)

Kept current at every commit.

## Where things are

- Branch `spike/http-safety`, from `spike/machine-code` (ff11ab6d2), with
  `origin/spike/http-impl` merged in (286a0a950; clean). PR base:
  `spike/machine-code`.
- `async/http-safety/` holds the theories listed in 23 §table, plus
  `Makefile`, `http_demo.sh`, `http-demo-transcript.txt`, and
  `http_server.sexp` (generated, committed).
- Write-up: `23-http-safety.md`.

## Status

- DONE: `http_semantics_prog` (whole program diverges; trace satisfies
  http_safe), the runnable server, and the curl demo. Holmake -j1 green, no
  cheats. HttpSpec untouched.
- NOT DONE: http_live; the machine-code theorem (blocked, 22 §3).

## Assumptions made

See 23 §7.

## Tool feedback

- Two translation chains define the same CakeML names (`handler_v`,
  `http_handler_v`, …). With both as ancestors, unqualified names in
  statements can resolve to the wrong chain's constant. Qualify them
  (`asyncHttpSockProg$http_handler_v`).
- Overloads from ancestors (`TS` from asyncM4EchoRunOk) capture
  abbreviation names; pick unused names.
- `simp[w2n_lt]` does not prove `w2n c < 18446744073709551616` once
  dimword is evaluated; use `qspec_then ‘c’ assume_tac w2n_lt >> fs[]`.
- In shell demos, a bare `wait` also waits for the background server;
  wait on the client PIDs only.

## Final report (2026-10-15)

- Proved: server_with_uses_accepted; asyncRunOkGen (gen_grun_ok, gen_fresh,
  gen_rounds_bytes); parse_all_mono, http_comp_safe; sserver_with_spec
  (generic) with echo and HTTP instances; shttp_handler_spec,
  shttp_server_spec; main_spec, http_semantics, http_semantics_prog.
- Runnable: release cake v3479 (arm8), same trusted socket_ffi.c; demo
  transcript covers curl (headers stripped), concurrency, pipelining, and
  an out-of-subset request.
