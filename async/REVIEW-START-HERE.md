# Start here: reviewing verified async I/O for CakeML

**The result.** A concrete CakeML program, a concurrent echo server built
on a verified async library, meets a short trusted specification of what
an echo server must do on raw socket I/O:

```
⊢ echo_spec 3w echo_prog
```

In every fair world with one listening socket, the program:
- runs forever;
- never writes back on a connection more than it has read from it;
- eventually writes back everything every client sends.

Companion results:
- a blocking (`select`) version of the program (a refinement) that idles
  at 0% CPU;
- an HTTP server (GET and POST, with headers and Content-Length bodies)
  meeting a short trusted HTTP specification in full, safety and
  liveness: `⊢ http_spec_b 3w demo_files http_prog_b`;
- both servers compile and run.

**How to read it.** The work is split into 11 stacked PRs, `[review 1/11]`
to `[review 11/11]`. Each is one layer that builds on its own. Read them in
order. In each PR, read only the definitions and the ≤ 5 statements its
description lists; skip all proofs. The layers:

| PR | layer | read | time |
|---|---|---|---|
| 1 | **the trusted surface**: socket world, fairness, EchoSpec, HttpSpecBodies, why they bite | all of `spec/EchoSpecScript.sml`, `spec/HttpSpecBodiesScript.sml`, and the listed model definitions | 30–45 min |
| 2 | the async model: monad laws, `both`, `choose` | 5 statements | 45 min |
| 3 | recursion, Level 2, the scheduler: no busy-waiting | 5 | 45 min |
| 4 | the echo server in the model: safety, closed-loop liveness | 5 | 40 min |
| 5 | the library in CakeML (CF specs) | 5 | 30 min |
| 6 | sockets in CakeML, divergence, the event loop | 5 | 40 min |
| 7 | **the echo program: `echo_spec 3w echo_prog`** | 5 | 40 min |
| 8 | the blocking refinement | 4 | 30 min |
| 9 | **HTTP: `http_spec_b 3w demo_files http_prog_b`** | 5 | 40 min |
| 10 | it runs (`socket_ffi.c` is the C trust item) | 1 file | 15 min |
| 11 | README and design notes | as wanted | 15 min |

Total: about 6 hours at this depth. For a short review, read PR 1 and the
first statement of PRs 7 and 9 (about 1 hour). They contain everything you must
trust and the theorem that rests on it.

**What you must trust.**
- CakeML's semantics.
- The socket model and the fairness assumption `sched_wf` (PR 1).
- The two spec files (PR 1).
- The C implementation of the socket calls (PR 10).

Everything else is proved.

`REVIEW-SERIES-PLAN.md` explains how the series was cut from the spike
branches, what was dropped, and where work still in progress will land.
