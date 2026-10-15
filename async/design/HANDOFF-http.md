# Handoff: the HTTP server in the async model (spike/http-model)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/cf-actions`, branch
  `spike/http-model`, from `spike/final-spec` (6c1cf6dc1), with
  `origin/spike/async-echo-server` merged in (the model echo server,
  transcripts, `echo_server_safety`; a clean merge). PR base:
  `spike/final-spec`.
- New work: `async/http-model/` (INCLUDES ../model ../spec ../ffi-spike;
  basis heap, because HttpSpec sits on CakeML's semantics).
  - `asyncHttpParseScript.sml`: the incremental parser `parse_request`
    (Complete r rest | Incomplete | Invalid), proved against HttpSpec's
    `print_request`: `parse_print`, `parse_complete`, `parse_prefix`,
    `parse_invalid`, `parse_extend`; `parse_all` and `parse_all_requests`.
  - `asyncServerWithScript.sml`: `server_with h lfd` (the echo server's
    skeleton for any handler), `server_with_handler` (echo is the instance),
    wf/settled, `server_with_isolates` (per-connection isolation).
  - `asyncHttpServerScript.sml`: `http_handler files (fd, buf)` (fix,
    wf, settled), `http_server`, `http_handler_serves`,
    `http_server_safety`, `http_server_safety_requests`, EVAL examples.

## Status

- DONE: parser, server_with, HTTP handler/server, safety (tasks 1-4).
  Holmake green, no cheats.
- NOT DONE (estimated in 18-http-model.md): Level 2 quiet, the world-async
  style closed-system result.
- DONE: 18-http-model.md.

## Assumptions made (so far)

1. The model works on strings (as the echo model does); HttpSpec's bytes
   are `MAP (n2w o ORD)` of them, bridged at the M3 bookkeeping level.
2. The parser uses HttpSpec's printer and validity predicate directly, so
   "proved against the spec's printer" is literal.
3. Garbage is reported as `Invalid`, and `parse_invalid` states its meaning:
   no extension of the input begins with a printed valid request.

## Tool feedback

- `simp[GSYM APPEND_ASSOC]` loops (APPEND_ASSOC is a default rewrite); use
  `REWRITE_TAC[GSYM APPEND_ASSOC]`. Likewise `EXISTS_NOT_EVERY` with simp.
- `isPREFIX` against string literals is evaluated by simp into nested
  `case`s; wrapping the literals in constants (`get_sp`, `after_path`)
  keeps goals readable.
