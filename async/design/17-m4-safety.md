# 17: M4 safety assembly: the verified echo program satisfies EchoSpec's `echo_safe`

Status: **done.** There are no cheats, and `Holmake -j2` is green in
`async/m4-common/`, `async/m4-safety/` and `async/m4-echospec/`. Branch `spike/m4-safety`,
stacked on `spike/m4-server` (PR #17). It merges:

- `origin/spike/m3-assembly` (M3: the event loop against the socket model);
- `origin/spike/final-spec` (EchoSpec, the user's trusted statement; it
  also brings HttpSpec);
- `spike/m4-liveness` at `ff5f483c0`, the liveness worker's
  dynamic-interest loop `async/m4-common/asyncM4Loop`. That merge also
  brings their model files (`asyncWorld`, `asyncProgress`,
  `asyncLiveness`, `asyncClosedLoop`);
- `spike/machine-code` at `ff11ab6d2` (cf-actions). It contains
  spike/runnable's `asyncEchoMain` (**the** echo program, `echo_prog`) and
  `asyncEchoSemantics` (`echo_semantics_prog`: the program diverges in the
  sockets-only world, with a trace satisfying `echo_safe`). It was proved
  from this branch's a902db27d, and I adopted it instead of re-proving it
  (as the coordinator asked). There is one echo program and one echo_safe
  theorem.

None of the merged files were edited. EchoSpec's definitions are untouched.

## 1. The result

```
(* MAIN: the safety half of EchoSpec for the verified echo program: in
   every server world for listener 3w, the program runs forever, and at
   every point of the run and on every connection, the bytes it has
   written are a prefix of the bytes it has read. *)
Theorem echo_prog_safe:
  server_world 3w sk ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env echo_prog
         (Diverge io) ∧ echo_safe io
```

(`async/m4-echospec/asyncM4EchoSpecSafe`). `server_world`, `socket_ffi`,
`echo_safe` (via `bytes_written_to` / `bytes_read_from` on raw I/O events)
and `semantics_prog` are EchoSpec's and CakeML's own definitions.
`echo_prog` is spike/runnable's concrete CakeML program (`asyncEchoMain`):
the basis, the Socket module, the Async library, the dynamic-interest
event loop, the echo server of this branch, and a call to

```sml
fun main u = run_i ([3], server 3)
```

With liveness (`echo_live`, the liveness worker's half), this gives
`echo_spec 3w echo_prog`.

## 2. The chain

| step | theorem | file |
|---|---|---|
| the CakeML server (socket vocabulary) implements the model's server, translated | `sserver_spec` | m4-safety/asyncM4SockServer |
| translation = relabelling; it distributes over the library | `relabel_bind`, `relabel_both`, `relabel_emit`, …, `sserver_unfold` | m4-common/asyncM4RelabelDist, asyncM4SockModel |
| the loop's trace, for any interest function | `run_i_spec` (liveness worker) | m4-common/asyncM4Loop |
| the history with a history-dependent interest list; M3's is the fixed case | `grounds`, `gstrace_actions_rounds`, `srounds_grounds` | m4-common/asyncM4GRounds |
| **no misuse (M3's `srun_ok`), discharged** | `echo_grun_ok` | m4-common/asyncM4EchoRunOk |
| the world hands out distinct connections | `echo_fresh` | m4-common/asyncM4EchoRunOk |
| transcript ↔ performed pairs ↔ raw-event projections | `trans_ghist`, `bytes_written_to_rounds`, `bytes_read_from_rounds` | m4-common/asyncM4GTrans |
| finite prefixes lie between round boundaries | `LPREFIX_rounds_between` | m4-common/asyncM4GTrans |
| **`echo_safe` for the loop's trace, any interest function** | `echo_comp_safe` | m4-common/asyncM4EchoSafe |
| the whole program diverges with that trace (in the sockets-only world) | `echo_semantics_prog` (cf-actions) | machine-code/asyncEchoSemantics |
| EchoSpec's oracle = the sockets-only oracle; EchoSpec's form | `socket_ffi_socket_only_ffi`, `echo_prog_safe` | m4-echospec/asyncM4EchoSpecSafe |

### 2.1 The server in the socket vocabulary

M3's loop runs computations over socket actions (`sact`: `Accept l`,
`Read c n`, `Write c bs`) and responses (`sresp`). The model server speaks
the model's vocabulary. Instead of a CakeML adapter, the server is written
directly in the socket vocabulary (`asyncM4SockServer`, the same code as
15's with socket constructors). Its model is `relabel sfa sfs (server
lfd)` (`srelabel`). Relabelling distributes over the combinators when the
snapshot translation is pointwise (`snap_map`), so `sserver_unfold` gives
the socket-vocabulary recursion equation that the code mirrors. Then:

```
(* MAIN *) Theorem sserver_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server lfd)) v)
```

The proof follows 15's method: the depth-indexed specs, replayed for the
socket program's `Async` module (`asyncM4SockApprox`; the two translation
chains are separate, as in M3).

### 2.2 No misuse

The real socket FFI fails on misuse. M3's loop theorem assumes there is
none. For the echo server it is now proved:

```
(* MAIN *) Theorem echo_grun_ok:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok ifds (srelabel (server lfdn)) s0
```

It holds for any interest function `ifds`, so it covers both M3's fixed
loop and the dynamic one. The proof is an induction on rounds with the
world invariant `sinv lfd acc s` (asyncM4SockInv): the only listener is
`lfd`; the fds handed out (`acc`) and the queued ones are distinct and are
all connections. `sinv` holds initially, is preserved by arrivals and by
successful operations, and makes every *allowed* action succeed
(`sock_do_ok`, `sock_acts_ok`). The actions of round n are allowed
(`echo_round_actions_ok`) by the model-level `server_uses_accepted` (15).
Through the relabelling, an `Accepted fd` in the model transcript is an
`Accepted (SOME c)` from the world, with `w2n c = fd`
(`TREL_accepted`).

### 2.3 From the model's equality to EchoSpec's prefix

`echo_server_safety` gives `written fd = read fd` on the model transcript.
At the end of round n, the model transcript has round n's writes but not
yet round n's reads' responses. The raw trace up to the end of round n has
both. Hence `echo_rounds_written_read`:

```
bytes_written_to c (rounds 0..n) = bytes_read_from c (rounds 0..n-1)
```

Any finite prefix `evs` of the trace lies between the ends of rounds n and
n+1 (every round ends with a poll event). So

```
written_to c evs ≼ written_to c (rounds 0..n) = read_from c (rounds 0..n-1) ≼ read_from c evs
```

This is `echo_comp_safe`. The bytes match because `sfr`/`sfa` translate
data byte-for-byte (`bytes_round_trip`). The fd numbers match because
every fd the model touches was handed out by the world, so it is below
2^64 (`echo_fds_bounded`).

## 3. What remains for liveness (`echo_live`)

Liveness is out of scope here; the liveness worker owns it (spike/m4-liveness).
What it needs beyond this branch:

1. **The same program**: `echo_prog_semantics` gives the trace, and
   `echo_grun_ok` / `echo_fresh` / `echo_rounds_written_read` are reusable
   as they are.
2. **Schedule accounting**: after n rounds the world has consumed exactly
   n schedule steps, and under `sched_wf` every arrival is effective
   (their `asyncM4Sched`).
3. **Per-connection accounting**: `sent_upto c n = bytes read ++ incoming`,
   `outgoing = bytes written`.
4. **Progress**: a connection with unread data is polled (the dynamic
   interest list includes every accepted connection), reported ready, and
   its handler reads and echoes in the following rounds. In the model,
   this is the handler's progress under fair readiness (08 §4).

## 4. Assumptions made

1. **The server is written in the socket vocabulary** and specified
   against `relabel sfa sfs (server lfd)`, rather than adding a CakeML
   relabelling combinator. This needs no new datatypes in the socket
   program, and the code stays readable.
2. **Read size**: the server reads at most `bufsz = 4096` bytes per read.
3. **Listener 3, fd numbers**: the model's fds are numbers; the socket fds
   are `word64`, translated by `n2w`/`w2n`.
4. **The program uses the liveness worker's dynamic-interest loop**
   (`run_i`), as the coordinator decided, so that `echo_safe` and
   `echo_live` are about one program. Safety itself holds for any interest
   function (`echo_comp_safe`).
5. **Shared files in `async/m4-common/`**, agreed with the liveness worker.
   I own the Holmakefile, `asyncM4GRounds`, `asyncM4RelabelDist`,
   `asyncM4SockModel`, `asyncM4SockInv`, `asyncM4GTrans`,
   `asyncM4EchoRunOk` and `asyncM4EchoSafe`. They own `asyncM4Loop` (and
   `asyncM4Sched`, on their branch).
6. **hol-lsp vs Holmake**: hol-lsp reported `xfun` failures in the
   replayed `Async_bind_spec_d` proofs that Holmake accepts. Holmake wins
   (CONVENTIONS §3).
