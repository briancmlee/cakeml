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
- **HTTP.** An HTTP server (GET and POST, with headers and Content-Length
  bodies) meets a short trusted HTTP specification in full, safety and
  liveness:
  ```
  ⊢ http_spec_b 3w demo_files http_prog_pb
  ```
  The server is an instance of one generic protocol server. The spec is
  checked against an independent RFC 9112 reference.
- **Quiescence.** The blocking echo server and an HTTP server that
  selects on its declared interest both *go to sleep* when the world goes
  quiet (QuietSpec), and stay safe and live:
  ```
  ⊢ echo_quiet 3w echo_l_main
  ⊢ http_quiet_b 3w demo_files (SNOC (main_call «main») http_q_prog)
  ```
- **Close and fd reuse.** An echo server that closes connections and
  reuses fds is safe and live per connection:
  ```
  ⊢ echo_spec2 3w echo2_prog
  ```
- **It runs.** The servers compile with the CakeML release compiler and
  run. The quiet ones idle at 0% CPU.

**How to read it.** The work is split into 14 stacked PRs,
`[review-v2 01/14]` to `[review-v2 14/14]`. Each one is a layer that
builds on its own. Read them in order. In each PR, read only the
definitions and the ≤ 5 statements its description lists, and skip all
proofs.

| PR | # | layer | read | time |
|---|---|---|---|---|
| 01 | #84 | **the trusted surface**: socket world, fairness, EchoSpec, HttpSpecBodies (tokens, RFC character sets), QuietSpec, why they bite; the RFC 9112 agreement | all of `spec/EchoSpecScript.sml`, `spec/HttpSpecBodiesScript.sml`, `spec/QuietSpecScript.sml`, and the listed model definitions | 45–60 min |
| 02 | #85 | the async model: monad laws, `both`, `choose` | 5 statements | 45 min |
| 03 | #86 | recursion, Level 2, the scheduler: no busy-waiting | 5 | 45 min |
| 04 | #87 | the echo server in the model: safety, closed-loop liveness | 5 | 40 min |
| 05 | #88 | the library in CakeML (CF specs) | 5 | 30 min |
| 06 | #89 | sockets in CakeML, divergence, the event loop | 5 | 40 min |
| 07 | #90 | **the echo program: `echo_spec 3w echo_prog`** | 5 | 40 min |
| 08 | #91 | the blocking refinement (and the Level 2 CF library completed) | 4 | 30 min |
| 09 | #92 | liveness from the library (`server_with_live`, `server_v_live`) | 5 | 40 min |
| 10 | #100 | **HTTP as a protocol instance: `http_spec_b 3w demo_files http_prog_pb`** | 5 | 45 min |
| 11 | #109 | **quiescence, and option C: `echo_l_quiet`, `http_q_quiet`** | 5 (and `quiet/README.md` §0, §6) | 45 min |
| 12 | #112 | it runs (`socket_ffi.c` is the C trust item; CPU table) | 1 file | 15 min |
| 13 | #113 | **close and fd reuse: `echo_spec2 3w echo2_prog`** (its own trusted spec and version-2 socket world) | all of `spec-v2/EchoSpec2Script.sml`, `world/sockets-v2/socketV2FFIScript.sml`; 5 statements | 45 min |
| 14 | — | README, design notes, this guide | as wanted | 15 min |

**Short review (about 1 hour):**
1. Layer 01, the trusted surface: what EchoSpec, HttpSpecBodies and
   QuietSpec say, and their bites (20 min).
2. The README's "Why you should believe it" and the headline theorems:
   `echo_prog_spec`, `http_prog_pb_spec`, `echo_l_quiet`, `http_q_quiet`
   (10 min).
3. Layer 03, the Level 2 idea: declared interest, `quiet`,
   `no_busy_waiting` (15 min).
4. Layer 11's design note (`quiet/README.md` §0 and §6): the two spins,
   and select on the declared interest (10 min).
5. The README's "Honest limitations" (5 min).

**Full review (about 8 hours):** layers 01 → 14 in order. Layers 02–08 are
the core: the model, the library and the echo program. Layers 09 → 10 → 11
are the spine added since the first series:
- 09: liveness proved once, from a library;
- 10: protocols as instances of one generic server;
- 11: quiescence by construction.

**What you must trust.**
- CakeML's semantics.
- The socket model and the fairness assumption `sched_wf` (layer 01).
- The three spec files: EchoSpec, HttpSpecBodies and QuietSpec (layer 01).
- The C implementation of the socket calls (layer 12). It has a known gap,
  which is being fixed: see the README's "Honest limitations".
- For layer 13 only: the version-2 socket model with `close` and fd reuse,
  its fairness `sched_wf2`, and EchoSpec2 (all in layer 13), plus
  `sock_close` in the C (layer 12).

The RFC 9112 reference (`spec-rfc/`) need not be trusted: HttpSpecBodies'
agreement with it is proved. Everything else is proved too.

**After the series.** The next-steps PR states, for review, what comes
next:
- the endpoint world (clients and proxies);
- fd discipline;
- buffer closure;
- the KV server.

The chat server (#66, #72, #75, #76, #83) is linked as an appendix, not
reviewed. `REVIEW-SERIES-PLAN.md` explains how the series was cut, what
was retired to `archive/` tags, and what feeds each layer.
