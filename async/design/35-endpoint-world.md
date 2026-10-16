# 35: The endpoint socket world (SPEC FIRST, for your review)

Status: **round 2.** Nothing is cheated. Unproved claims are
*definitions* of propositions (`echo_sym_equiv`, `projection`, ...), the
way `echo_spec2` was. Proved in round 2 (§4, "Round 2 results"):
- `same_answers_semantics`;
- `v2_instance`;
- the refutation of `v1_instance`;
- `never_polls_bite`.

Decisions 1–4 are pending. The drafts for decisions 5–6 are in §7.

Branch `spike/endpoint-world`, from `spike/close-v2-sim` merged with
`spike/http-kv`. Directory `async/endpoint-world/`. No existing file or spec
is changed.

| file | role |
|---|---|
| `endpointWorldScript.sml` | **trusted**: the endpoint world (reactive environment) and its FFI calls |
| `endpointFairScript.sml` | **trusted**: the rely `ep_rely`, which has no progress conjuncts |
| `endpointSpecFormsScript.sml` | the `rg_spec` form, world classes, per-episode views of the trace, `reads_fair`, `input_live`; `rg_spec_mono` and `rg_spec_weaken` (proved) |
| `endpointServersScript.sml` | symmetric forms of EchoSpec, EchoSpec2, HttpSpecBodies and HttpKvSpec; the specialisation corollaries (proved); equivalence claims; the bites (claims) |
| `endpointSemanticsScript.sml` | (proved) CakeML evaluation and `semantics_prog` depend on the FFI only through its answers |
| `endpointInstancesScript.sml` | `same_answers_semantics` (proved); `not_v1_instance` (proved: the version-1 claim is false); version-1 fd-discipline claims (draft) |
| `endpointV2SimScript.sml` | (proved) `v2_instance_thm`: version-2 worlds are exactly the simple endpoint worlds |
| `endpointTraceScript.sml` | (proved) prefixes and events of diverging runs; the endpoint views are EchoSpec2's on traces without connects or sends |
| `endpointEcho2Script.sml` | (proved) `echo_spec2_of_endpoint` |
| `endpointV2PrefixScript.sml` | (proved) version-2 worlds that agree on a schedule prefix answer alike |
| `endpointEcho2ConvScript.sml` | (proved) `endpoint_of_echo_spec2`, `echo2_sym_equiv_thm` |
| `endpointOpenScript.sml` | drafts for the next round (§7): `rg_spec_term`, n-ary open systems, buffer closure |
| `endpointClientsScript.sml` | a toy HTTP client spec; a proxy spec (two roles, half-close) |
| `endpointComposeScript.sml` | joint runs of two programs, wired; the projection and composition claims |

## 1. The world

Today's worlds are shaped like a server: a listener, connections that arrive
from nowhere, and written bytes that go nowhere. The endpoint world is
POSIX's view instead.

**Channels.** A **channel** is a byte stream to one peer. It is created when
a peer connects to one of the program's listeners (`Incoming a`), or when the
program connects to an address (`«sock_connect»`). In the second case the
world's `accepts` decides at the next tick whether the peer takes it. Every
channel is read, written, polled, shut down and closed the same way.

**From version 2.** Clients and channels are numbered in order of creation.
The kernel chooses any free fd (`alloc`). There is `«sock_close»` with fd
reuse, and the trace is projected per episode.

**A reactive environment.** At each tick the environment chooses the next
arrivals from the calls the program has made so far: `env n hist`. A fixed
schedule, as in versions 1 and 2, is the instance that ignores `hist`. So a
peer can answer what the program sent.

**Backpressure** (required by your addendum):

- each channel counts the bytes in flight;
- the acceptance policy `takes j b n` says how many of `n` offered bytes
  are accepted, with `b` in flight;
- `«sock_send»` writes that many and returns the count;
- `«sock_writable»` polls writability;
- `Drain j` is the peer reading;
- `«sock_write»` stays version 1's full write. Under backpressure, a full
  write that doesn't fit is a misuse.

**Half-close.** `«sock_shutdown»` closes the sending side, so a relay can
pass a client's EOF on and still read the reply.

**Supported calls.** The world lists the calls it supports (`calls`). Any
other call fails, exactly as version 1 behaves for calls it doesn't know.

## 2. Rely/guarantee

    rg_spec cls guar prog ⇔
      ∀w. cls w ∧ ep_rely w ⇒ ∃io. prog diverges in w with trace io ∧ guar w io

**Rely** (`ep_rely`): `alloc_ok`, `takes_ok`, and `ep_sched_ok`. The last
says that **in every state the program can reach**, the environment's next
arrivals make sense there. It is checked on the actual run, not on the world
left alone. The rely contains **no progress assumption** and nothing that
depends on whether the world has backpressure.

**Class** (`ep_server_world cs lfd a`, `ep_client_world`): the shape of the
world at the start, and the calls it offers.

**Guarantee**, per episode, in two shapes:

- `always P`: P holds of every prefix (safety);
- `eventually P`: P holds of some prefix (liveness).

What a peer has sent is read off the run (`peer_sent_at`), since the world
is reactive.

**Progress assumptions are per-guarantee antecedents:**

- `reads_fair w io c`: in this run, channel c's peer keeps reading.
  Liveness about c assumes it for c only, so a server whose service of c
  depends on another peer reading violates the spec (`starve_bite`). This
  is the per-connection liveness you asked for.
- `input_live` (new, additive) says the program eventually reads what a peer
  sends. It is not implied by the headline guarantees (`input_live_bite`),
  and composition under backpressure needs it.

## 3. Feature as parameter, simple world as instance

Each feature is a **field of the world** that every spec quantifies over:

- backpressure: `takes`;
- fd reuse: `alloc` and close;
- connect: `accepts` and `calls`;
- reactivity: `env`.

The simple worlds are **instances**:

| feature | simple instance | what disappears |
|---|---|---|
| backpressure | `no_backpressure w` (`takes j b n = n`) | writes are always accepted whole; `«sock_writable»` is true; `reads_fair` is never needed (drains change nothing) |
| connect, send, writable, shutdown | `w.calls = v1_calls` | the calls fail, as in version 1 |
| close and reuse | `w.calls = v1_calls` | fds are never freed, so episodes are connections |
| reactivity | `env n hist` ignores `hist` | a fixed schedule |

There is one spec per program, about all worlds of its class. The simple
theorem is a **corollary by instantiation**, plus weakening:

    rg_spec_mono   : rg_spec cls guar prog ∧ (∀w. cls' w ⇒ cls w) ⇒ rg_spec cls' guar prog
    rg_spec_weaken : rg_spec cls guar prog ∧ (∀w io. cls w ∧ guar w io ⇒ guar' w io) ⇒ rg_spec cls guar' prog

`ep_echo_spec_simple`, `ep_http_spec_simple` and `ep_kv_spec_simple` are
proved this way. They drop `input_live` and restrict to `no_backpressure`.
No statement contains an "if backpressure then ... else" case split.

A reader can read only the simple statements and the equivalence claims
(§4). With version 1's calls, these are exactly today's headline specs.

**The limit of the pattern** (from the stress test, adopted): it works for
features whose simple instance satisfies the general rely. A *progress*
assumption (a peer keeps reading, time diverges, an upstream answers) is
false in some simple worlds. So such assumptions must never be conjuncts of
the global rely; they are per-guarantee antecedents. `ep_rely` follows this
rule.

## 4. Statement-level checks

1. **Instances** (`endpointInstances`).
   - `v1_instance`, `v2_instance`: every version-1 (version-2) server world
     answers every sequence of calls exactly like some endpoint server world
     with version 1's (2's) calls, no backpressure, and a fixed schedule
     satisfying the rely; and conversely (`same_answers`).
   - `same_answers_semantics`: equal answers give equal program behaviour.
2. **Symmetric forms** (`endpointServers`).
   - Each headline safety, unchanged, is applied to the trace renamed so
     that episode j's fd is `n2w j` (`sym_safe`), as in close-v2's
     simulation. Liveness is per channel (`sym_live`).
   - `echo_sym_equiv`, `echo2_sym_equiv`, `http_sym_equiv` and
     `kv_sym_equiv`: in the simple class these are the **unamended**
     headline specs `echo_spec`, `echo_spec2`, `http_spec_b` and `kv_spec`.
3. **Clients** (`endpointClients`).
   - `http_client_spec a r`:
     - connect to a and send exactly r;
     - send all of it if the server accepts and reads;
     - read everything (`input_live`);
     - close after reading the server's EOF.
   - `proxy_spec lfd a b`: each accepted episode i is paired with a backend
     episode `pair i`, connected to b.
     - Safety: each side gets a prefix of what the other sent.
     - Liveness: everything is forwarded both ways if the receiving peer
       reads.
     - Half-close: the client's EOF becomes a shutdown of the backend side.
     - `input_live`.
4. **Composition** (`endpointCompose`).
   - `joint_run P1 P2 lfd a w1 w2 m`: each program diverges in its endpoint
     world. m interleaves their traces, and each world's environment is
     **wired** to the other program, prefix by prefix of m:
     - connects are paired with accepts;
     - delivery is causal (a prefix of what was sent) and **unconditionally
       eventual**;
     - **drains are the other program's reads**;
     - EOF comes after the other side shuts down.
   - `projection`: the worlds can be chosen to satisfy the rely.
   - `client_server_compose`: the toy client and an HTTP server meeting
     their specs, joined, give the client the response.
   - **Brock–Ackerman**: composition is over traces *with* their causal order
     (m, prefix by prefix), not over input/output relations. `kv_safe`
     already speaks of causal order (`precedes`), so it composes this way.

### Round 2 results (2026-10-16)

- **`same_answers_semantics`: proved** (`endpointSemantics`), generically:
  if two FFI states answer every sequence of calls alike, CakeML's
  `evaluate` runs alike (`evaluate_ffi_rel`), so a program has the same
  behaviours (`semantics_prog_same_answers`).
- **`v2_instance`: proved, both directions** (`endpointV2Sim`). Version 2's
  server worlds are exactly the endpoint server worlds with version 2's
  calls, no backpressure and a fixed schedule. Two statement fixes:
  - `open_loop w` (the environment ignores the calls) is part of the
    simple class, since a version-2 schedule is fixed;
  - the rely's bound on new channels is version 2's again (one stricter
    than "all fds distinct").
- **`v1_instance`: false, proved** (`not_v1_instance`). In version 1,
  `Connect l c` makes `c` a connection at once, so a program can poll,
  read or write `c` before accepting it. In the endpoint world (as in
  POSIX and version 2) the fd exists only once accepted. Counterexample:
  a schedule connecting fd 5 with data, then the calls poll, read fd 5.
  The same program-level gap makes the version-1 equivalences
  (`echo_sym_equiv`, `http_sym_equiv`, `kv_sym_equiv`) false for programs
  that touch fds they have not accepted. **[DECIDED 2026-10-16: option A]**
  The version-1 claims are stated for **fd-disciplined** programs, a trace
  property (`fd_disciplined lfd io`: every socket event names `lfd` or an
  fd opened and not yet closed; `v1_disciplined`, `v1_instance_disc`,
  drafted). Our programs would then be proved disciplined, which turns
  version 1's idealisation into a theorem about them.
- **Review-driven fix: `ticks_forever`.** Liveness was vacuous for
  programs that never let time pass. A program that never polls receives
  nothing, so `sym_live` held trivially, while the schedule-based
  version-1 and version-2 specs demand that it echo. Every `ep_*_guar` now
  also requires `ticks_forever w io` (the program keeps polling). Bite,
  proved: `never_polls_bite` (a run in which no time passes violates every
  endpoint server guarantee).
- **`echo2_sym_equiv`: the useful direction is proved.** `echo_spec2_of_endpoint`
  (`endpointEcho2`): a program meeting the endpoint form of EchoSpec2 in the
  simple class meets the unamended `echo_spec2`. The proof:
  - builds, from a version-2 world, the endpoint world with the same
    schedule plus a `Drain` for every live channel at each tick;
  - shows along any trace that channel c's peer has sent `sent2_upto c
    clock`, that it reads at every tick, and that accepts are first in,
    first out, so episode j is channel j;
  - then `sym_live` with `ticks_forever` gives `echo_live2`.
  **Completeness check, also proved:** `endpoint_of_echo_spec2`
  (`endpointEcho2Conv`). A program meeting `echo_spec2` meets the endpoint
  form in every simple-class world that does not fill the fd space
  (`nonsat`). Both directions are in `echo2_sym_equiv_thm`.
  - The hypothesis is needed: once about 2^64 clients have come and all
    have closed, nothing more can arrive. A program may then stop polling,
    which `ticks_forever` forbids.
  - The proof that the program keeps polling: if it stopped after k
    polls, it would run alike in a world that agrees on the first k steps
    and then connects a new client sending a byte. That is prefix
    determinism (`endpointV2Prefix`, built on async-spike's
    `ffiAgreeUpto`). `echo_spec2` there forces it to accept that client,
    which takes another poll.

## 5. The stress test (`~/.cache/stress-designs/REPORT.md`): decisions

| finding | decision |
|---|---|
| 1. The rely was checked on the world left alone, so client worlds received nothing and `projection` was false | **Adopted**: reactive `env`, and the rely is checked on every reachable state |
| 1'. Connects shift channel numbers, so an open-loop schedule misroutes | **Adopted** through reactivity: the environment sees the calls, so it knows which channel is which. Separate In/Out ids were not needed; channels keep one numbering |
| 3. Arbitrary oracles and conditional delivery make composition vacuous | **Adopted**: each program runs in an endpoint world; delivery is wired, unconditional and causal; drains = reads. The `keeps_reading` hypotheses are gone |
| 4. Input liveness | **Adopted** as an additive guarantee (`input_live`) with a bite; the headline specs are unchanged |
| Half-close (relay) | **Adopted**: `«sock_shutdown»` |
| 5. Progress relies must be per-guarantee | **Adopted** (§3) |
| Open n-ary systems with an external io_event view; the buffer-closure lemma (proxy ‖ U meets U's spec, and KV stays linearizable behind a proxy) | **Drafted** (§7), after your approval of decision 5; relay closure proved for echo, HTTP and KV |
| Terminating clients (`rg_spec_term`) | **Drafted** (§7), after your approval of decision 6 |
| Select, clock, timers, scopes | **Deferred** |

## 6. Decisions for you

Items 1–4 were decided on 2026-10-16:

1. **[ACCEPTED 2026-10-16]** The acceptance policy `takes j b n` gives one
   number per call. This is the "n accepted" of design/36's single
   non-blocking L0 send. A policy that varies with time, beyond the bytes
   in flight, would need the environment.
2. **[CHANGED 2026-10-16]** A connect's outcome is still the world's
   choice (`accepts a j`), settled at the next tick, but it is now
   three-way: pending, connected or refused. A refused channel does not
   read as EOF. Read, write and poll on it return an **error result** (an
   ordinary return, not `FFI_failed`), and connect's FFI result gains a
   status byte. To follow, coordinated with design/36's error encoding:
   - `http_client_term_spec`: on refusal the client reports it and ends
     cleanly;
   - `proxy_spec`: an upstream refusal closes the client's episode or
     answers an error (our choice, documented with the statement);
   - a bite: a client that treats refusal as success fails its spec;
   - a check that the v1 and v2 instance proofs are unaffected.
3. **[SUPERSEDED by design/36 (pending review)]** The full-write
   `«sock_write»`, and full-write misuse under backpressure, are not
   hard-coded further. Design/36 has an honest, layered FFI: L0 honest
   syscalls with a single non-blocking send, L1 verified wrappers, and L2
   servers proved against L1.
4. **[SUPERSEDED by design/36 (pending review)]** A separate writability
   call (`«sock_writable»`) is not pursued further, for the same reason.
5. **[APPROVED 2026-10-16: go to n-ary open systems + buffer closure]**
   Composition is binary and closed (client + server) in this round. The
   stress test recommends, as the next step:
   - **n-ary open systems**: processes plus routing, open to an environment
     that plays the external addresses, whose external view is an
     `io_event` trace, so the headline predicates apply unamended;
   - the **buffer-closure** lemma, which makes "a verified server behind a
     verified proxy meets its own spec" a corollary.

   Is that the direction you want?
6. **[APPROVED 2026-10-16: add the terminating form]** Clients must diverge (`rg_spec` asks for `Diverge`), so a finished client
   idles. A terminating spec form is a small addition if you want one.

## 7. Drafts for the next round (`endpointOpen`; statements, for review)

**Terminating programs** (decision 6). `rg_spec_term cls guar done prog`:
every run either terminates successfully with a trace meeting `guar`, or
diverges meeting `guar` and never reaches `done`. So a program that is done
must stop. `rg_spec` is the case `done = K F` (`rg_spec_term_rg_spec`,
proved, with `_mono` and `_weaken`). `http_client_term_spec`: the toy
client exits once it has closed its connection.

**N-ary open systems** (decision 5). A system is a list of processes,
each a program with at most one listener on an address. An outside world
`W` plays every address no process owns. `sys_run sys W_lfd W ws link m`:

- each process diverges in its own endpoint world `ws k`;
- `m` interleaves their events;
- `link` pairs each connect to an owned address with the owner's accepted
  episode, and linked episodes are wired exactly as in `endpointCompose`
  (`flows`, `drains_are_reads`);
- every other episode is external, and its peer-side state is `W`'s
  (`peer_view`).

The **external view** `ext_io` is an ordinary `io_event` trace: the
external episodes' opens, reads, writes and closes, with the x-th
external episode on fd `n2w x`.
`sys_spec cls guar sys W_lfd` says that in every outside world of the
class satisfying the rely, there is a run whose external view meets
`guar`. So a headline guarantee applies to a system unamended. The closed
binary joint run is the case with no external episodes.

**Buffer closure.** `buf_rel io io'` says the outside run `io'` relays
the inside run `io`, episode by episode: writes appear outside no earlier
than inside and all eventually; reads happen outside no later than
inside. A guarantee is `buffer_closed` if relaying preserves it.
Claims:
- `buffer_closure`: U behind a proxy meeting `proxy_spec` meets U's own
  buffer-closed guarantee at the proxy's address;
- `guars_buffer_closed`: echo's, HTTP's and KV's guarantees are buffer
  closed (for KV: a relay only widens request intervals, so `precedes`
  outside implies `precedes` inside);
- `kv_behind_proxy`: a verified KV server behind a verified proxy is still
  linearizable.

Not claimed:
- existence of system runs for arbitrary programs (the Kahn fixpoint;
  report §A-7);
- liveness with feedback under backpressure, which needs its own
  induction per application (report §B-6).

**Revision (`endpointBuffer`).** The draft `buf_rel` is too weak. It
relates each outside prefix to *some* inside prefix, independently, so it
loses the common instant a relay works at. At each instant t of the joint
run, per front episode:
- what U has read is a prefix of what the proxy read outside;
- what the proxy wrote outside is a prefix of what U wrote.

A per-connection safety predicate survives relaying if it is closed under
reading more and writing less (`relay_closed`). Then U's safety at every
instant gives the system's (`relay_safety`, proved).
- Echo's predicate is relay-closed (`echo_relay_closed`, proved).
- HTTP's is relay-closed (`http_relay_closed`, proved in
  `endpointBufferHttp`). Request parsing is monotone (`parse_mono`) because
  a printed valid request is never a proper prefix of another
  (`print_prefix_free`).
- KV's is relay-closed too (`kv_relay_closed`, proved in
  `endpointBufferKv`). `kv_safe` is not a per-connection predicate, since
  its real-time `precedes` compares positions across connections. So the
  setting is a **relay run** (`relay_run`): inside and outside traces at
  the instants of a joint run, monotone, every outside prefix observed,
  and `relays` on every connection at every instant. At an outside point,
  the server has read a prefix of each connection's requests
  (`parse_mono`). `kv_safe` inside orders those. The order is extended by
  the unread requests at the end (`extra`). The store is sequential, so
  the earlier replies are unchanged. Real time transfers at the instant of
  the outside witness, since a relay only widens request intervals. An
  appended request cannot have been answered outside, because what was
  written outside is a prefix of what the server wrote.

`buffer_closed` also cannot give the outside world `ticks_forever` from
the relay facts alone. The system's clock is the proxy's, so that part
needs the proxy's own `ticks_forever`.

Decisions (2026-10-16):
- (a) **APPROVED**: the per-instant `relays` relation replaces the draft
  `buf_rel`.
- (b) **DECIDED**: `sys_spec` quantifies over **every** wired, fair system
  run (∀). Each concrete system we compose gets a separate non-vacuity
  (existence) lemma.
