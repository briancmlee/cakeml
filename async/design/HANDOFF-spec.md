# Handoff: the final top-level specifications (spike/final-spec)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/cf-actions`, branch
  `spike/final-spec`, from `spike/m3-assembly` (ebe04b885). PR base:
  `spike/m3-assembly`.
- New work: `async/spec/` (Holmakefile INCLUDES ../ffi-spike; basis heap).
  - `EchoSpecScript.sml` (155 lines, TRUSTED SURFACE, no proofs): the
    sockets-only oracle, `server_world`, per-connection projections of raw
    I/O events (`bytes_read_from`, `bytes_written_to`), `sent_upto`,
    `echo_safe`, `echo_live`, `echo_spec lfd prog` (the statement).
  - `EchoSpecBiteScript.sml` (proved): broken servers violate the spec
    (swap clients, drop/duplicate a byte, write before reading, never
    echo); non-vacuity (`server_world_exists`, `ideal_trace_safe_and_live`).
  - `HttpSpecScript.sml` (115 lines, TRUSTED SURFACE, no proofs): GET over
    a fixed file map, `print_request`/`print_response`/`handle`,
    `http_safe`, `http_live`, `http_spec lfd files prog`.
  - `HttpSpecBiteScript.sml` (proved): wrong order, 200 for a missing
    file, wrong Content-Length, answering a partial request, never
    answering; a fair one-client world; the ideal trace is safe and live
    (with a request-uniqueness lemma).
- Docs: this file; `async/design/16-final-spec.md`.

## Status

- DONE: EchoSpec + bite; Holmake green, no cheats.
- DONE: HttpSpec + bite; Holmake green, no cheats.
- DONE: 16-final-spec.md.

## Assumptions made (so far)

1. The trusted world is the socket worker's model (`ffiSpikeSocketFFI`) and
   fairness predicate (`sched_wf`), imported. The sockets-only oracle is
   restated in EchoSpec (10 lines) rather than imported from
   `ffiSpikeSocketDiv`, so that the spec does not depend on a translator
   theory.
2. The statement is at CakeML's source level (`semantics_prog ... (Diverge
   io)`). Lifting to machine code is CakeML's compiler theorem (trust base).
3. Initial world: exactly one listener `lfd` with an empty queue, no
   connections, and `sched_wf`.
4. Liveness: `sent_upto c n sk ≼ bytes_written_to c evs` for some finite
   prefix `evs` of the trace, for every `c` and `n`.

## Final report (2026-10-15)

- **PR:** https://github.com/briancmlee/cakeml/pull/18 (spike/final-spec → spike/m3-assembly).
- Trusted statements: `echo_spec` (EchoSpec, 155 lines) and `http_spec`
  (HttpSpec, 115 lines); they typecheck and are not proved yet.
- Proved: broken-server counter-traces (5 echo, 5 HTTP) and non-vacuity
  (fair worlds exist; ideal traces are safe and live).
- No cheats; Holmake green. The composition plan is in 16-final-spec.md §5.
