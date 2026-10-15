# 35: The endpoint socket world (SPEC FIRST, for your review)

Status: **statements only; they typecheck, nothing is cheated.** Unproved
claims are *definitions* of propositions (`v1_instance`, `echo_sym_equiv`,
`projection`, ...), the way `echo_spec2` was. They are to be proved after
your review. The theorems proved so far are the specialisation lemmas,
which are easy.

Branch `spike/endpoint-world`, from `spike/close-v2-sim` merged with
`spike/http-kv`. Directory `async/endpoint-world/`. No existing file or spec
is changed.

| file | role |
|---|---|
| `endpointWorldScript.sml` | **trusted**: the endpoint world (reactive environment) and its FFI calls |
| `endpointFairScript.sml` | **trusted**: the rely `ep_rely`, which has no progress conjuncts |
| `endpointSpecFormsScript.sml` | the `rg_spec` form, world classes, per-episode views of the trace, `reads_fair`, `input_live`; `rg_spec_mono` and `rg_spec_weaken` (proved) |
| `endpointServersScript.sml` | symmetric forms of EchoSpec, EchoSpec2, HttpSpecBodies and HttpKvSpec; the specialisation corollaries (proved); equivalence claims; the bites (claims) |
| `endpointInstancesScript.sml` | claims: version-1 and version-2 worlds are endpoint worlds |
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

## 5. The stress test (`~/.cache/stress-designs/REPORT.md`): decisions

| finding | decision |
|---|---|
| 1. The rely was checked on the world left alone, so client worlds received nothing and `projection` was false | **Adopted**: reactive `env`, and the rely is checked on every reachable state |
| 1'. Connects shift channel numbers, so an open-loop schedule misroutes | **Adopted** through reactivity: the environment sees the calls, so it knows which channel is which. Separate In/Out ids were not needed; channels keep one numbering |
| 3. Arbitrary oracles and conditional delivery make composition vacuous | **Adopted**: each program runs in an endpoint world; delivery is wired, unconditional and causal; drains = reads. The `keeps_reading` hypotheses are gone |
| 4. Input liveness | **Adopted** as an additive guarantee (`input_live`) with a bite; the headline specs are unchanged |
| Half-close (relay) | **Adopted**: `«sock_shutdown»` |
| 5. Progress relies must be per-guarantee | **Adopted** (§3) |
| Open n-ary systems with an external io_event view; the buffer-closure lemma (proxy ‖ U meets U's spec, and KV stays linearizable behind a proxy) | **Deferred** (§6) |
| Terminating clients (`rg_spec_term`), select, clock, timers, scopes | **Deferred**; out of this statement round |

## 6. Decisions for you

1. The acceptance policy `takes j b n` gives one number per call. A policy
   that varies with time, beyond the bytes in flight, would need the
   environment.
2. A connect's outcome is the world's choice (`accepts a j`), settled at the
   next tick. A refused channel reads as EOF.
3. `«sock_write»` stays a full write; under backpressure a full write that
   doesn't fit is a misuse.
4. Writability is a separate call (`«sock_writable»`), so `«sock_poll»` is
   unchanged and version 1 is an exact instance.
5. Composition is binary and closed (client + server) in this round. The
   stress test recommends, as the next step:
   - **n-ary open systems**: processes plus routing, open to an environment
     that plays the external addresses, whose external view is an
     `io_event` trace, so the headline predicates apply unamended;
   - the **buffer-closure** lemma, which makes "a verified server behind a
     verified proxy meets its own spec" a corollary.

   Is that the direction you want?
6. Clients must diverge (`rg_spec` asks for `Diverge`), so a finished client
   idles. A terminating spec form is a small addition if you want one.
