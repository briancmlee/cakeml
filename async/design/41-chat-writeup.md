# 41. A verified chat server: what was built, what it cost

A broadcast chat server, proved safe end to end in HOL4/CakeML. It runs, compiled
by the CakeML v3479 release compiler. Branches, stacked: `spike/chat-spec` (#66), `spike/chat-model` (#72),
`spike/chat-cakeml` (#75), `spike/chat-demo` (this PR). Design and decisions: design/40-chat.md.

## The statement (spec/ChatSpec, trusted, ~60 lines of definitions)

Clients connect to one listener and send lines. The server relays every complete
line, verbatim, to every connected client, the sender included.

- **One global order, fixed by the trace.** `relayed evs` is the list of lines the
  server has completed reading, in the order it completed them.
- **Exact membership.** Client `d` is owed exactly the lines completed after the
  event that accepted `d` (`owed d evs`): no backlog, and no gaps.
- **Safety** (`chat_safe`): at every point of the trace, what has been written to
  `d` is a prefix of `owed d evs`.

Bites (ChatSpecBite, 35 proofs) show that the statement rejects eight plausible broken servers and three non-live ones:
- broken (unsafe) servers drop, duplicate or reorder lines, relay half lines, invent lines, send backlog, or write to a connection never accepted;
- the non-live ones starve a client, never accept, or never read.

A non-vacuity witness shows that the statement can be satisfied.

## The theorem (async/chat/asyncChatHeadline)

```
chat_prog_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env chat_prog (Diverge io) ∧
            chat_safe io
```

The program diverges in every world with one listener 3w, and its trace is `chat_safe`.
`chat_prog` is the program compiled in `make`. Liveness (`chat_live`) is not proved yet (M4).

## How (the one idea)

The chat order is defined by I/O: the order in which reads complete. So the hub
is placed **at the I/O boundary**. `with_tap σ δ s0 m` is a generic effect handler that does two things:
- it answers `m`'s queries with `δ`, as KV's `with_store` does;
- it **observes `m`'s socket (action, response) pairs, in order**, through the tap `σ`.

The hub's log is then `relayed` by construction. Each connection's handler is `both reader writer`:
- the reader only reads, and the tap sees the data;
- the writer asks where it joined, then polls `Fetch i` and writes the new lines.

There is no round reasoning anywhere: no "published in the next round" shift lemma,
and no fiber-order lemma. The trace bridge (asyncChatTrace) is list reasoning:
- polls are invisible;
- the non-poll events are the act_events of the performed pairs;
- each pair corresponds to an entry of the model transcript.

## Demo (`cd async/chat && make && make demo`)

Three clients take part: one joins late, and one sends a line in two pieces. The demo checks what
each client received against ChatSpec's promises (chat-demo-transcript.txt):

```
alice received b'hello from alice\nhi alice, bob here\nhalf a line, now finished\ncarol: two\nlines at once\n'
bob   received (the same, in the same order)
carol received b'half a line, now finished\ncarol: two\nlines at once\n'
RESULT: PASS
```

Interactively: `CAKE_ECHO_PORT=7860 build/chat_server &`, then `nc 127.0.0.1 7860` in several terminals.

## Cost (one autonomous worker, wall-clock about 4 h to M3 + demo)

| milestone | lines | bespoke vs library |
|---|---|---|
| M1 spec + bites | 133 + 450 | all new |
| M2 model safety | with_tap 388 (generic, reusable), server skeleton 385 (copied from KV), model 285, safety 1079 | the library gave the transcript/isolation lemmas |
| M3 CakeML + CF + bridge + headline | ≈2,040 | the library gave the M4 loop, run_i_spec, gen_grun_ok, gen_fresh, the trace prefixes, and the whole-program assembly shape |
| M5 demo | Makefile + 110-line Python | the trusted socket FFI from runnable/ |

Where the time went:
- waiting for build slots (M1);
- hol-lsp iterations on bespoke list lemmas, about 45 for M2 safety and about 20 for the bridge;
- CF friction:
  - nested constructor patterns in CakeML code block `xmatch`;
  - polymorphic basis functions need monomorphic wrappers;
  - CakeML's `+` is on integers.

The single largest proof-engineering sink was `dimword(:64)` against its numeral after `simp`.

## Limitations (honest)

- **Liveness is not proved yet.** The library's `server_v_live`/`server_v_live_a` fit only
  per-connection output (`out D`, which depends on the connection's own data).
  A chat client's output depends on other clients' lines. Accept progress and read progress
  should come from the library; delivery is bespoke. See TRAJECTORY for the analysis and a suggested library change.
- The log grows forever: there is no garbage collection of delivered lines, and no notion of leaving
  (the v1 socket world has no close).
- The writer polls every round, so it spins while idle. The FFI's idle back-off bounds the CPU cost.
- `asyncChatSW` is a copy of KV's `server_with_k`, because KV's file was WIP. It should be reconciled with
  `server_v` from library-liveness.
