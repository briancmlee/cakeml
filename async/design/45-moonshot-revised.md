# 45: Moonshot: multi-program linearizability, revised (DESIGN, statements first, for review)

Status: **design only; decisions recorded (§9, user, 2026-10-16).**
Nothing here is built or proved, and there are no HOL files on this
branch. Every HOL block is a *sketch* of a statement, to
be checked when it is written. Branch `spike/moonshot-design`, from
`spike/honest-connect` (22bc7c717).

Inputs:
- the moonshot brief (AMBITIOUS-TODO, "FRONTIER MOONSHOT");
- the transfer review (`~/.cache/transfer-review/REPORT.md`): items 1, 2, 7
  and 8 are the ones this note answers;
- design/35 §6–§7 and `endpointOpen`/`endpointClients`/`endpointCompose`/
  `endpointBufferKv` at `spike/echo-sym-disc`;
- design/36 §4–§6 and §9, and `honestL0World`/`honestL1PFLive` on this
  branch;
- `HttpKvSpec2` (`kv_safe2`, `kv_spec2`) at `spike/kv-v2-spec`.

---

## 0. Summary

**The system.** Three verified CakeML binaries run on one kernel:
- a **client** `C`: it opens N connections to the proxy's port `a`, sends a
  pipelined list of KV requests on each, reads the replies, and exits;
- a **proxy** `P`: for each connection accepted on `a`, it connects to the
  KV server's port `b` and relays both ways, with half-close;
- the **KV server** `K` on `b`: today's KV v2 (`kv_spec2`).

**The revised headline, in two theorems.**

1. **Safety, for every run.** In every run of the three binaries on the
   modelled kernel in which no outside process uses ports `a` and `b`, the
   client's view (the requests it sent and the reply bytes it read, on all N
   connections) is linearizable with respect to one sequential KV store.
   - There is **no startup-order hypothesis and no fairness**.
   - Startup races, refused or never-accepted connects, backlog drops,
     EMFILE resets, process death and OOM can only make the client observe
     *less*. Linearizability is closed under taking prefixes, so each of
     these runs is still covered.
2. **Liveness, under explicit hypotheses.** The hypotheses are:
   - the processes are started in order (KV listening, then the proxy, then
     the client), or the client retries on refusal;
   - the scheduler and the kernel are fair ([F0]);
   - [F1] and [F2] (approved) hold per process;
   - connect fairness [F4] holds per address;
   - fds and backlog suffice for N;
   - no process runs out of memory;
   - no spurious hard errors occur (D16's corollary form).

   Then every request the client sends is answered on its connection, and
   the client terminates.

**What changed from the brief, and why.**

| brief (as planned) | revised | review item |
|---|---|---|
| proxy on today's L1 (per-fd pausing), with cross-fd backpressure "added later" | the proxy's L1 **never pauses on its own outbox**. The proxy stops reading the *front* fd while the *backend* outbox is over hw, and vice versa (§2.2). It is an L1 policy parameter plus an outbox-level query | 1 |
| S4 "writes don't outrun the client", per fd | the generic **S4g**, over a `feeds` relation, with the relay instance **S4_relay** (§2.3) | 1 |
| `proxy_guar` with unconditional `input_live` | **`proxy_guar'`**: a bounded-buffer *safety* clause, input-live conditional on the paired side draining, and a backend-EOF clause (§2.4) | 1, 7d |
| none | a **no-deadlock lemma** by a rank on wait-for edges, its instance for C→P→K, and a bite: per-fd pausing in a relay deadlocks (§2.6) | 1 |
| "∀ wired system run" (`sys_run`/`sys_spec`) covers the real execution | a **trusted multi-process L0 model** `l0sys`, and two bridges below `sys_run`: a projection (each process sees an L0 world) and a causality bridge. **Safety needs only those two.** Liveness is by induction on the L1 system. `sys_run'`, the revised `sys_run`, becomes an optional compositional layer (§3) | 2 |
| one theorem | **safety ∀ runs** and **liveness under fairness**, separately (§4) | 2.4 |
| connect fairness open (design/36 §6) | **[F4]**, per address, plus L1 retrying transient connect failures (§4.2) | 7 |
| `kv_relay_closed` (per fd) | **`kv_client_view_safe`** (per episode, with the roles swapped), stated directly between KV's trace and the client's (§4.1) | 8 |

**Decisions:** the user answered all nine questions of §8 on 2026-10-16
(§9). The safety path starts when its dependencies land. The coordinator
assigns the implementation.

---

## 1. The two findings, and the shape of the fix

**Finding 1 (deadlock).** Today's L1 pauses fetching on fd f while *f's own*
outbox is over hw (D4). For a server, which writes on f only in reply to
reads on f, that bounds memory and is live as long as the peer drains. A
relay writes on B what it read on A. With per-fd pausing in both the proxy
and KV:

- the proxy's B outbox (requests to KV) goes over hw, so the proxy stops
  fetching B, which is where KV's replies arrive;
- KV's outbox for that connection (replies) goes over hw, so KV stops
  fetching, which is where the proxy's requests arrive;
- the kernel buffers in both directions stay full, and neither side drains.

Each program still meets S1–S3, and both keep polling. **The fix is a rule
about who may wait on whom.** A program may stop reading an fd only on
account of an outbox *further along the reply path*. Reply paths end at the
client, which never pauses. Then the waits are well-founded (§2.6).

**Finding 2 (idealised kernel).** `sys_run` starts every listener at time 0,
links every connect, and delivers unconditionally. A theorem quantified over
`sys_run`s says nothing about real runs that are not `sys_run`s: the startup
race, the never-accepted backlog connection, drops. **The fix is to state
safety where it needs no fairness.** Safety is a property of every finite
prefix, and the kernel gives the one fact it needs at every instant: *no
process reads bytes that its peer did not send* (causality). Fairness, start
order and resources are then hypotheses of the liveness theorem only.

---

## 2. The proxy: bounded buffers that cannot deadlock

### 2.1 Vocabulary

- A **direction** `d = (k, f)` is process k sending on its fd f. Its
  **outbox** is L1's buffer of bytes that L2 wrote and the kernel has not yet
  accepted.
- k **fetches** f when L1 recvs on f (the prefetching L1, D10).
- k **reads** f when L2 takes bytes from f's inbox (a `Read`, which makes no
  syscall).
- `feeds k g f`: bytes that k reads on g may be written by k on f. Per
  program:
  - servers: `feeds k f f` only;
  - the proxy: `feeds P A B` and `feeds P B A` for each pair;
  - the client: nothing. It writes its requests from its own state.

### 2.2 The policy: the pause rule is a parameter

The prefetching L1 fetches f only if f is in L2's poll interest, f's inbox
is empty, f has no EOF, and f is not paused (`honestL1PFModel`, D15). Today
"paused" is fixed: `hw < LENGTH (outbox f)`. It becomes a parameter:

```sml
(* sketch: honestL1PFModel, parametrised *)
pol : pstate -> word64 -> bool                  (* "do not fetch f" *)

pol_self hw st f  ⇔ hw < LENGTH (outbox_of st.b f)    (* today's D4: servers *)
pol_never st f    ⇔ F                                  (* proxy, client *)

pfetch_ok pol st ifds f ⇔
  MEM f ifds ∧ inb_of st f = [] ∧ ¬eof_of st f ∧ ¬pol st f
```

With `pol_never`, the proxy applies its cross-fd backpressure itself,
through its interest. The prefetching L1 already never fetches outside the
interest. L1 gains one non-syscall query:

```sml
Level f  ⟶  Lvl n        (* n = LENGTH (outbox_of st.b f); no syscall *)
```

> **Level is an unconstrained oracle in the abstract layer (step 7, as built;
> `spike/moonshot-level`).** The E1 handle layer (endpointHLModel) has no
> outbox: its writes complete at once. So it answers `ELevel h` with
> `ELvl (lv n k)`, where `lv` is an oracle keyed by (round n, index k of the
> action in the round), and **every** `lv` is allowed. Consequences:
> - **Any claim proved in the abstract layer holds for every answer
>   sequence.** It cannot rely on the answers being true levels.
> - **A claim that needs true levels** (the proxy's bounded buffering,
>   `S4_relay`) is proved **at L1 level**, through `level_true`
>   (honestL1EPRefine): on L1's run, E1 runs the layer with `lv = elv …`,
>   L1's own answers, and the answer to round n's i-th action `ELevel h` is
>   the length of h's outbox in L1's state just before that action.
>   Otherwise it takes an explicit hypothesis on `lv`.
> - endpointWorld is unchanged. L1 answers with no syscall (`elevel`: the
>   outbox length; 0 for an unknown or still-connecting handle).

The proxy's rule, at each round, for each pair (A, B):
- A is in the read interest, and A is read, only if `Level B ≤ hw`;
- B is in the read interest, and B is read, only if `Level A ≤ hw`.

**Options considered:**

| option | how | for | against |
|---|---|---|---|
| **(P2) interest-based, with `Level` (recommended)** | L1 offers `pol_self` and `pol_never`. The relay logic is L2 code with a model-level proof | L1 stays generic, and stays free of L2's pairing. Credit-based flow control is the same code with a different threshold. The `Level` query is the "write-completion interface" that design/36 §6 (E1) deferred | the proxy polls `Level` each round. That costs nothing for safety and liveness, but the blocking variant needs a low-water readiness event instead (not claimed here; §7 R8) |
| (P1) the policy in L1, with a registered pairing | a new action `Pair A B`; L1 pauses A while B > hw | L2 is simpler | L1 must know L2's routing, and its R1 proofs then depend on the pairing |
| (P3) credits | the proxy grants the client k requests at a time | bounds requests, not bytes | needs protocol support (KV has none); it is not a transport-level fix |

### 2.3 S4 for a relay

Today's S4 (`honestL1PFLive.S4_def`) says that f's outbox eventually stays
≤ hw until f is next fetched. That is false for the proxy (review item 1).
It generalises over `feeds`, and splits into an L2 obligation and an L1
consequence:

```sml
(* sketch.  L2 obligation, per program: an outbox grows only by writes
   that follow reads on its feeders *)
Definition writes_follow_feeds_def:
  writes_follow_feeds feeds run ⇔
    ∀n n' f. n ≤ n' ∧
             (∀k g. n ≤ k ∧ k < n' ∧ feeds g f ⇒ ¬read_at run k g) ⇒
             LENGTH (outbox_at run n' f) ≤ LENGTH (outbox_at run n f)
End

(* sketch.  L2 obligation, per program: a feeder of a full outbox is
   paused, by pol or by the interest *)
Definition pauses_feeders_def:
  pauses_feeders pol hw feeds run ⇔
    ∀n g f. feeds g f ∧ hw < LENGTH (outbox_at run n f) ⇒
            ¬read_at run n g ∧ ¬fetch_allowed pol run n g
End

(* S4g: if f's peer drains, f's outbox eventually falls to ≤ hw *)
Definition S4g_def:
  S4g run f ⇔ D run f ⇒ ∀n. ∃n'. n ≤ n' ∧ LENGTH (outbox_at run n' f) ≤ hw
End

(* L1 lemma (generic, proved once): the two obligations, with [F1] and [F2],
   give S4g for every f, and a bound on every outbox *)
Theorem S4g_from_feeds:
  writes_follow_feeds feeds run ∧ pauses_feeders pol hw feeds run ∧
  F1 run ∧ F2 run ⇒
  (∀f. S4g run f) ∧
  (∀n f. LENGTH (outbox_at run n f) ≤ hw + resp_bound feeds f)
```

- **For servers** (`feeds f f`, `pol_self`), `pauses_feeders` is D4 and
  `writes_follow_feeds` is "reply-only writes". This recovers today's S4.
  - `resp_bound` is the largest reply to one fetched chunk.
  - For KV this is *not* `pf_chunk`: one 64 KiB chunk of GETs can ask for
    large values. The bound is a function of the store (§7 R4).
- **For the proxy** (the relay instance):

```sml
(* S4_relay: for a pair (A, B), if the backend drains, B's outbox
   eventually falls to ≤ hw; while it is over, A is neither fetched nor
   read.  Symmetrically for A *)
Theorem S4_relay:
  proxy_run P run ∧ pair A = SOME B ⇒
  (D run B ⇒ ∀n. ∃n'. n ≤ n' ∧ LENGTH (outbox_at run n' B) ≤ hw) ∧
  (∀n. hw < LENGTH (outbox_at run n B) ⇒ ¬fetched_at run n A ∧ ¬read_at run n A) ∧
  (∀n. LENGTH (outbox_at run n B) ≤ hw + pf_chunk)
```

In words: if the backend keeps reading, the backend outbox falls below the
mark again. While it is above the mark, the proxy takes nothing new from
the client. So the outbox never exceeds the mark by more than one chunk.

**As built (honestL1PFS4w, step 8, spike/moonshot-s4g @aa4c7fcd9; deviations approved by the coordinator).**
1. S4g needs no D, and S4g_from_feeds needs no [F1]/[F2]: the D23 write timeout drops an outbox that stops shrinking, so "≤ hw infinitely often" holds unconditionally. *Delivery*, as distinct from the bound, stays with flush_live, under D.
2. `feeds` is per round (`num → word64 → word64 → bool`), because the proxy's pairing changes as fds are reused.
3. `writes_follow_feeds` is eventual: once f's feeders are no longer read, f's writes (`wclean`: Writes on handles naming f at the round's start or end) eventually carry no bytes. The sketch's `outbox_at n' ≤ outbox_at n` is false for a server that replies one round after reading (M4).
4. The `≤ hw + resp_bound` clause is deferred to step 9 (proxy: hw + pf_chunk).
5. `pauses_feeders` constrains reads (`read_at`: a Read on a handle of g while g's inbox is non-empty), not fetches. Fetch belongs to S3c and no_deadlock (steps 15–16).
6. Servers don't meet `pauses_feeders`: they read their own inbox while their outbox is full. They get S4w through `S4w_of_feeds` (S3w + replies only, `feeds` = identity), and the server-side `S4w_of_stop` (05a20ad2a). The proxy gets S4g through `S4g_from_feeds`.

### 2.4 The proxy's spec, revised (`proxy_guar'`)

Changes from `endpointClients.proxy_guar`:
1. **Bounded buffering** is a *safety* clause on the raw trace. It is
   checkable on every prefix and needs no fairness.
2. **input_live is conditional**, per pair, on the paired side draining.
3. **A backend EOF or break** (KV closed, reset, exited) makes the proxy
   pass on the EOF, and then close the front episode (review 7d).
4. **A closed front** makes the proxy eventually close its backend.

```sml
(* sketch; ch_read and ch_sent are raw byte counts (recv'd, send-accepted) *)
Definition proxy_guar'_def:
  proxy_guar' Bnd b w io ⇔
    ∃pair. INJ pair ∧
      (* safety: relay prefixes, as before *)
      always (λevs. ∀i. ep_accepted evs i ⇒
                (pair i < LENGTH (opened_fds evs) ⇒ ep_connected_to evs (pair i) b) ∧
                ch_sent (pair i) evs ≼ ch_read i evs ∧
                ch_sent i evs ≼ ch_read (pair i) evs) io ∧
      (* NEW, safety: bounded buffering (Bnd = hw + 2·pf_chunk) *)
      always (λevs. ∀i. ep_accepted evs i ⇒
                LENGTH (ch_read i evs) ≤ LENGTH (ch_sent (pair i) evs) + Bnd ∧
                LENGTH (ch_read (pair i) evs) ≤ LENGTH (ch_sent i evs) + Bnd) io ∧
      (* liveness, CONDITIONAL: each direction progresses if its far side drains *)
      (∀evs i c c'. LPREFIX (fromList evs) io ∧ ep_chan w evs i = SOME c ∧
                    ep_chan w evs (pair i) = SOME c' ⇒
         (reads_fair w io c' ⇒ ep_input_live w io i ∧
            eventually (λevs'. peer_sent_at w evs c ≼ ch_sent (pair i) evs') io) ∧
         (reads_fair w io c ⇒ ep_input_live w io (pair i) ∧
            eventually (λevs'. peer_sent_at w evs c' ≼ ch_sent i evs') io)) ∧
      (* half-close, front to back (as before) *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ch_eof_read i evs ⇒
               eventually (λevs'. ch_shut (pair i) evs') io) ∧
      (* NEW: backend EOF or break: forward the EOF, then close the front *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ep_accepted evs i ∧
               (ch_eof_read (pair i) evs ∨ ch_broken (pair i) evs) ⇒
               eventually (λevs'. ch_shut i evs' ∧ ch_closed i evs') io) ∧
      (* refused backend: close the front (as before) *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ep_accepted evs i ∧ ch_refused (pair i) evs ⇒
               eventually (λevs'. ch_closed i evs') io) ∧
      (* NEW: a closed front: close the backend *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ch_closed i evs ⇒
               eventually (λevs'. ch_closed (pair i) evs') io)
End
```

- `ep_input_live w io i` is `input_live` restricted to episode i.
- The listener's input-live (accepting) stays unconditional, given [F3].

**A bite to keep us honest**, `unbounded_needed` (stated by the review,
proved here later): in a world where the backend never drains and the
client keeps sending, `proxy_guar` (the old one, with its unconditional
`input_live`) together with the bounded-buffering clause is unsatisfiable.
This is the formal version of "the old spec forces unbounded memory".

### 2.5 The client

The client is the end of every reply path, so it **never pauses its reads**
(`pol_never`, and every open connection always in the read interest). Its
writes are its own pipelined requests. They do not depend on its reads, so
`feeds` is empty.

```sml
(* sketch: N connections to a; connection i sends brequests (rqs i), reads
   replies until EOF, closes; the program exits when all are closed *)
Definition client_guar'_def:
  client_guar' a N rqs w io ⇔
    always (λevs. LENGTH (opened_fds evs) ≤ N ∧
                  ∀i. i < LENGTH (opened_fds evs) ⇒
                      ep_connected_to evs i a ∧ ch_sent i evs ≼ brequests (rqs i)) io ∧
    (∀i. reads_fair_ep w io i ⇒ eventually (λevs. ch_sent i evs = brequests (rqs i)) io) ∧
    (∀i. always_reading w io i) ∧                    (* never pauses: the sink *)
    (∀evs i. ... ch_eof_read i evs ∨ ch_refused i evs ⇒ eventually (ch_closed i)) ∧
    always (λevs. ∀i. ¬(ch_refused i evs ∧ ch_eof_read i evs)) io
Definition client_spec'_def:
  client_spec' a N rqs prog ⇔
    (∀i. EVERY valid_brequest (rqs i)) ∧ 2 ≤ N ∧
    rg_spec_term ep_client_world (client_guar' a N rqs) (all_closed N) prog
```

- `always_reading` says the client is in the fetch interest of every open
  connection at every round. It is what makes the client a sink in §2.6.
- `2 ≤ N`: linearizability with only one connection says almost nothing
  (review item 8).
- **The rely must be run-local, not plain `ep_rely`** (decision, coordinator,
  2026-10-17; from close-v2's E1 statement). E1 transfers the client's
  L1 run to the endpoint handle layer in a world built from that run, as
  R1-safe does. Connects make the world's channel numbering depend on the
  program's calls. So the built world's arrivals (`Settle j b`, `PData j`)
  are sound only along the run's own calls, and `ep_rely` (about *every*
  call sequence) fails as soon as the run connects.
  - `rg_spec_term` here is therefore stated with the rely for programs
    making only given calls (`rely_on Q`, as in the servers' converse,
    endpointEcho2Conv's `rclass Q`), or with the rely along the run.
  - E1 gets a corollary that transfers any spec stated in that form.
  - The environment stays open loop. A history-keyed environment would make
    plain `ep_rely` hold, but it needs the handle layer to record its calls
    and costs `open_loop`, so it was not chosen.
- **The client must handle a failed connect** (decision, user via the
  coordinator, 2026-10-16: option (b)). endpointWorld gains a world choice
  `nosock`, keyed by the connect's number `nconnects`. A connect it marks
  gets no socket (code 10, as L0's EMFILE or a transient error) and opens
  no episode. So `client_guar'` must not assume that its N connects all
  open:
  - its liveness is conditioned on the episodes that did open, or
  - the client retries, and the spec says what it does on a failure (give
    up, or retry within a bound).
  E1 (close-v2, PR #156) is stated meanwhile under `no_socketless` (no
  socketless connect in the run). It is restated without that restriction
  once the endpointWorld PR for (b) lands.

### 2.6 The no-deadlock lemma

**Wait-for edges.** In a run of the L1 system (§3.3), direction d = (k, f)
is linked by the kernel to (k', f'): what k sends on f, k' receives on f'.
d's outbox drains only if k' fetches f'. By `pauses_feeders`, k' may refuse
to fetch f' only while some outbox h with `feeds k' f' h` is over hw:

```sml
Definition waits_def:
  waits r (k, f) (k', h) ⇔
    ∃f'. linked r (k, f) (k', f') ∧ feeds_of r k' f' h ∧ may_pause r k' f' h
End

(* a rank: every wait goes strictly down *)
Definition rank_ok_def:
  rank_ok r rk ⇔ ∀d d'. waits r d d' ⇒ rk d' < rk d
End

(* a sink: a direction whose receiver never refuses to fetch it *)
Definition sink_def:
  sink r d ⇔ ∀d'. ¬waits r d d'
End
```

**The lemma.** Fix a run r of an L1 system (§3.3, `l1sys_run`). Assume the
four groups of hypotheses below. Then every direction's outbox is below the
mark infinitely often, and every byte waiting in a live fd's kernel inbox is
eventually fetched. So R1-live's D(c), S3 and S4 all hold, for every
process.

```sml
Theorem no_deadlock:
  l1sys_run S r ∧ sched_fair r ∧ kernel_fair r ∧
  (∀k. k < LENGTH S ⇒ F1_k r k ∧ F2_k r k ∧ S1_k r k ∧
                     S3c_k r k ∧ writes_follow_feeds_k r k ∧ pauses_feeders_k r k) ∧
  rank_ok r rk ∧
  (∀d. sink r d ⇒ receiver_fetches_io r d) ∧            (* the client, or an external D *)
  (∀k. ¬exits_early r k) ⇒
  (∀d n. ∃n'. n ≤ n' ∧ LENGTH (outbox_at r n' d) ≤ hw) ∧
  (∀k f n. kernel_input_pending r n k f ∧ live_fd r n k f ⇒ ∃n'. n ≤ n' ∧ fetched_at r n' k f)
```

The four groups of hypotheses:
- (a) the scheduler and the kernel are fair ([F0], §4.2);
- (b) each process meets [F1], [F2], S1, `S3c`, and the two feed
  obligations of §2.3;
- (c) the wait-for edges are ranked;
- (d) every sink's receiver fetches infinitely often. Here that is the
  client, by `always_reading`.

`S3c` is S3 made conditional. It reads: "a shown inbox is eventually read,
provided every outbox it feeds is ≤ hw infinitely often". The proxy cannot
meet the unconditional S3.

*Proof idea:* well-founded induction on `rk d`. For d with the smallest rank
(a sink), its receiver fetches. Then [F2] and kernel fairness drain the
kernel buffer, so L1's flushes succeed, so the outbox falls (by
`writes_follow_feeds`, it grows only on reads). For d of larger rank:
- every outbox d' it can wait on has a smaller rank;
- by induction, each such outbox is ≤ hw infinitely often;
- so its receiver is unpaused infinitely often, and [F1] makes the fetches
  happen;
- the rest is as in the base case.

This is the "feedback induction" of design/35 §7 (report §B-6), made
explicit as a rank.

**The instance.** For the moonshot, `rk` is given by the role of the
direction:

| direction | rank | waits on (relay policy) |
|---|---|---|
| C → P (requests, on A) | 3 | P fetching A, paused while P's B outbox > hw: **P → K** |
| P → K (requests, on B) | 2 | K fetching, paused while K's outbox > hw (`pol_self`): **K → P** |
| K → P (replies, on B) | 1 | P fetching B, paused while P's A outbox > hw: **P → C** |
| P → C (replies, on A) | 0 | C fetching: C never pauses. **A sink** |

```sml
Theorem moonshot_rank_ok:
  l1sys_run (moonshot_sys a b N rqs) r ⇒ rank_ok r (role_rank r)
```

**With per-fd pausing in the proxy** (`pol_self` for P), K → P waits on
P → K, since P pauses B on B's own outbox. So K → P (rank 1) waits on a
direction of rank 2, and with P → K waiting on K → P, there is a cycle. No
rank exists:

```sml
Theorem perfd_relay_no_rank:
  l1sys_run (moonshot_sys_with pol_self_for_P ...) r ∧ heavy_burst r ⇒ ¬∃rk. rank_ok r rk
```

**The bite** (review 1.4): `perfd_relay_deadlock`. Take two L1 programs,
both with `pol_self`: a relay in front of echo. There is a run that
satisfies [F0], [F1], [F2], S1–S3 and D for the client. In it, the relay's
backend outbox and echo's outbox both stay > hw forever, and the client's
bytes are never answered. The witness is a small concrete l0sys run that
repeats with period 1, and its kernel buffers are full (`takes = 0`). This
turns finding 1 into a theorem. It needs only the PF L1 model and §3's
`l0sys`; there is no CakeML in it.

---

## 3. The shared kernel

### 3.1 `l0sys`: what the multi-process L0 model must contain (trusted, for review)

`l0sys` is a new trusted theory beside `honestL0World`. It has one kernel
state and n processes. Following design/36's rule, it **over-approximates**:
what is platform-specific or timing-dependent is a world choice.

| component | concrete in the model | as a world choice |
|---|---|---|
| **per-process fd tables** | each process has its own `open_fds`, `reserved`, `fd_limit`, `hist`, and a status (Running, Exited) | — |
| **shared port namespace** | `ports : port ↦ (owner, lfd, backlog, backlog_limit)`. `sys_listen` on a taken port fails (EADDRINUSE). The environment (outside processes) may hold ports | whether TIME_WAIT on a port blocks bind (SO_REUSEADDR is set; `listen_fails` stays a choice) |
| **connect** | to a port with no listener: refused (at once, or as `LConnFail` later). With a listener and room in the backlog: the handshake *may* complete. On completion the connector gets `LConnUp` and the owner's backlog gets the channel (`LIncoming`). With a full backlog: the SYN may be dropped, then the connect stays pending, or fails (ETIMEDOUT) | `connect_now` (at once or pending); when a pending connect settles; EADDRNOTAVAIL (ephemeral ports, TIME_WAIT), ENOBUFS |
| **channels** | one kernel channel per connection, with two ends `(k, f)` and `(k', f')` and a buffer per direction. What one end's `sys_send` accepted reaches the other end's inbox, in order, with nothing invented | `takes` (window, buffer space: may be 0 even after a drain, so silly-window avoidance is covered); `short`; when bytes move |
| **accept** | pops the owner's backlog. With EMFILE, the connection stays queued, or is dropped and its connector reset | `emfile_drops`, `accept_aborts` (as in L0) |
| **close and exit** | close sends FIN, or RST if there is unread input (L8); the peer sees `LEof` or `LBreak`. On process exit (normal, `FFI_failed`, OOM) the kernel closes all its fds | whether a break flushes the peer's unread input (as `LBreak … b`) |
| **shared limits** | — | ENFILE (system-wide, as `transient`), ENOBUFS/ENOMEM |
| **the environment** | outside processes, as a nondeterministic peer on unowned ports and on connections to owned ports | everything about them |
| **the schedule** | an interleaving of process steps, kernel steps (moving bytes, settling connects) and environment steps | which step comes next. Fairness is *not* in the model ([F0], §4.2) |

The run, `l0sys_run S rs`: `rs` is an interleaving of labels
`Call k nm conf out | Kern kev | Env eev | Exit k`, from the initial state in
which process k is the machine code of `EL k S`. Each `Call` label is one L0
C entry point (design/36 §3), answered by the kernel state. Process k's
`Call` labels are an FFI trace of `semantics_prog` for its program, or a
prefix of one if k exited.

**Conformance (as design/36 §4.3)** needs new multi-process probes on
macOS. Linux is the open gap.
- a connect before the listen: refused at once;
- backlog overflow: pending, then ETIMEDOUT or success;
- an EMFILE drop: Up, then RST;
- exit with unread input: the peer sees RST;
- two processes, one loopback channel: byte order, no invention.

### 3.2 The bridges: below `sys_run`, not to it

The brief asked for `l0_system ⇒ sys_run`. **The recommended bridge is two
smaller statements**, and neither mentions `sys_run`:

```sml
(* B1. Honesty of the per-process model: each process sees an L0 world.
   (The world's choice functions are built post hoc from the run, keyed on
   k's history prefixes, which are distinct.) *)
Theorem l0sys_proj:
  l0sys_run S rs ⇒
  ∀k. k < LENGTH S ⇒
      ∃w0. l0_world w0 ∧ l0_rely w0 ∧ w0.reserved = reserved_at_start rs k ∧
           proc_trace rs k = l0_trace (EL k S).prog w0     (* or a prefix, if k exited *)

(* B2. Causality: on every kernel channel, at every instant, what one end
   has received is a prefix of what the other end's sends accepted, and
   each accepted episode is the far end of exactly one connect episode
   (inside the system, or external) *)
Theorem l0sys_causal:
  l0sys_run S rs ⇒
  ∃conn. conn_inj conn ∧
    ∀t k j k' j'. conn (k, j) = SOME (k', j') ⇒
      ep_recvd k' j' (TAKE t rs) ≼ ep_accepted_bytes k j (TAKE t rs) ∧
      ep_recvd k j (TAKE t rs) ≼ ep_accepted_bytes k' j' (TAKE t rs)
```

- **B1** lets every per-process theorem (R1-safe, R1-live, and the per-server
  R4) apply *unchanged* to each process of a system run. The per-process L0
  model is already an over-approximation (the env chooses arrivals before
  every call; the choices are functions of the history), so B1 should be a
  table-lookup construction. **The risk** is any `l0_rely` conjunct that
  rules out a real cross-process effect (§7 R1).
- **B2** is the only system fact that safety needs. It holds of every run,
  with no fairness and no start order: a kernel that drops a connect,
  refuses, or resets simply gives `conn` fewer pairs, or shorter streams.

**For liveness**, the bridge is the L1 system, with no endpoint worlds in
between:

```sml
(* B3. The L1 system: each process's run is a PF-L1 run (B1 + the L1 loop's
   CF spec), and the kernel's pairing links their fds byte-accurately: an
   LDrain j n at the sender is exactly n bytes recv'd by the receiver *)
Definition l1sys_run_def:
  l1sys_run S r ⇔ ∃rs. l0sys_run S rs ∧ (∀k. on_l1 (EL k S)) ∧ r = l1_view rs ∧ ...
End
Theorem l0sys_drains_exact:
  l0sys_run S rs ∧ conn (k, j) = SOME (k', j') ⇒
  ∀t. drained_at k j (TAKE t rs) = LENGTH (ep_recvd k' j' (TAKE t rs))
```

`no_deadlock` (§2.6) and the liveness theorem (§4.2) are stated on
`l1sys_run`.

### 3.3 `sys_run'`: the endpoint-level system, revised (optional layer)

`sys_run`/`sys_spec` stay useful as the *model-level* tool: buffer closure,
and composing verified pieces. They are no longer on the critical path. If
we keep them (Q7), they are revised so that B1–B3 can reach them:

1. **Optional links.** A connect to an owned address is linked, **or**
   refused, **or** never accepted (Up, then nothing, or reset). A link must
   agree with the settle arrival: under Settle-as-arrival (close-v2), Up is
   an arrival, and `accepts` is no longer static.
2. **Listeners appear when created.** The owner's world starts with no
   listener. A refused connect before the listen is an unlinked refusal,
   which item 1 allows.
3. **Byte-accurate drains:** `Drain j n` with `drains_are_reads` counting
   bytes, not read events (review 2.3). Or, as a weaker change, `takes_ok`
   no longer forces a byte after any read.
4. **Processes may stop:** OOM, listen failure, exit. They then
   `Terminate`, and their channels break.
5. **`flows` loses "unconditional eventual delivery".** Delivery becomes a
   fairness hypothesis of the liveness statements (as `kernel_fair`).

```sml
(* sketch: the soundness bridge, if sys_run' is kept *)
Theorem l1sys_sys_run':
  l1sys_run S r ⇒ ∃ws link m. sys_run' S ws link m ∧ instants_agree r m ∧
                              (∀k. ws k = psk_ep_of r k)        (* E1's world from k's run *)
```

Close-v2 owns `sys_run` and is doing Settle-as-arrival. Items 1–5 go to
them as a proposal, not an edit (§6, step 13).

---

## 4. The system theorems

### 4.1 Safety, for every run

**The client's view, with roles swapped** (review item 8):
- `sent_reqs j evs` is the complete requests the client has sent on episode j;
- `ep_read j evs` is the reply bytes it has read there.

```sml
(* real time, client side: the client had read all of x's reply before it
   sent any byte of y *)
Definition precedes_c_def:
  precedes_c rss order evs (j, i) (k, l) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order j)) ≼ ep_read j evs1 ∧
           ep_sent k evs1 ≼ brequests (TAKE l (rss k))
End

(* the client observes one sequential store: some prefix of what it sent on
   each episode took effect, in an order respecting real time, and what it
   read is a prefix of those requests' replies.  (Requests still in flight
   may be in or out: linearizability's pending operations) *)
Definition kv_client_safe_def:
  kv_client_safe io ⇔
    ∀evs. LPREFIX (fromList evs) io ⇒
      ∃rss order.
        (∀j. EVERY valid_brequest (rss j) ∧ brequests (rss j) ≼ ep_sent j evs) ∧
        is_order2 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes_c rss order evs x y ⇒ earlier order x y) ∧
        ∀j. ep_read j evs ≼ reply_bytes (replies rss order j)
End
```

**The transfer lemma** is pure trace reasoning. It is easier than
`kv_relay_closed`, because no "extra" requests are needed: the order is
KV's, restricted.

```sml
(* if at every instant, per paired episode, the client sent at least what KV
   read and read at most what KV wrote, KV's linearizability is the
   client's *)
Theorem kv_client_view_safe:
  (∀t t'. t ≤ t' ⇒ kvs t ≼ kvs t' ∧ cls t ≼ cls t') ∧
  (∀t. LPREFIX (fromList (kvs t)) io_k) ∧ (∀evs. LPREFIX (fromList evs) io_c ⇒ ∃t. cls t = evs) ∧
  INJ e ∧ (∀j. e j = NONE ⇒ ∀t. ep_read j (cls t) = []) ∧
  (∀t j j'. e j = SOME j' ⇒
     ep_read j' (kvs t) ≼ ep_sent j (cls t) ∧ ep_read j (cls t) ≼ ep_written j' (kvs t)) ∧
  closed_kv e io_k ∧                          (* every KV episode is one of the client's *)
  kv_safe2 io_k ⇒
  kv_client_safe io_c
```

The headline needs the following hypotheses, besides the system run:
- `isolated S rs`: no outside process listens on, or connects to, `a` or
  `b`;
- `moonshot_sys a b N rqs` consists of the client program, the proxy
  program and `kv_prog2`;
- each process's spec: `client_spec'`, `proxy_spec'` (with `proxy_guar'`)
  and `kv_spec2`.

```sml
(* THE SAFETY HEADLINE *)
Theorem moonshot_safe:
  l0sys_run (moonshot_sys a b N rqs) rs ∧ isolated (moonshot_sys a b N rqs) rs ⇒
  kv_client_safe (proc_io rs client)
```

In words: whatever the kernel, the schedule and the timing do, the client
never sees an answer that one sequential store, run in an order consistent
with real time, could not have given.

The proof chain (all of it holds in every run):
1. B1 gives each process an L0 world.
2. In K's world: R1-safe, the KV v2 theorem, and an R4-style transfer to
   K's raw trace (review 4: precedes through psk) give `kv_safe2` on K's raw
   trace.
3. In P's world, `proxy_guar'`'s safety clause gives, at every instant, per
   pair:
   - `sent B ≼ read A`;
   - `sent A ≼ read B`.
4. B2 gives the kernel's prefix relations, front and back.
5. Composing by transitivity of ≼ gives `kv_client_view_safe`'s per-instant
   hypothesis, with `e` = (the client's connect episode ↦ P's accepted
   episode ↦ `pair` ↦ K's accepted episode).
6. `isolated` gives `closed_kv`.

**Why no startup hypothesis.**
- A client connect that is refused, never accepted, or reset has no `e`
  pair, and the client reads nothing on it. It is in no order.
- A proxy whose backend is refused closes the front, with nothing written.
- An OOM or exit in any process truncates traces. Safety is quantified over
  prefixes.
- `isolated` is the only real-world hypothesis. Without it, a stranger
  could hold port `b` (the proxy then relays to the stranger), or could
  write to the store.

**Generalisation (later, not headline).** Drop `isolated`'s "connects to"
half, and conclude: "the client's view, together with *some* operations of
other clients, is linearizable". This needs `kv_client_safe` with existential
foreign episodes.

### 4.2 Liveness, under explicit fairness

**The new trusted assumptions, for approval:**

| name | statement (informal) | why it is needed | status |
|---|---|---|---|
| **[F0] scheduling** | `sched_fair`: every process that has not exited takes infinitely many steps. `kernel_fair`: bytes accepted into a channel whose receiver has buffer room are eventually moved; a pending connect is eventually settled | the OS scheduler and the kernel's own progress. Without them nothing moves | **approved** (Q4), trusted, liveness only |
| [F1] | per process, per call kind and fd (D11, as built) | transient errors | approved |
| [F2] | per channel: nothing in flight ⇒ send takes ≥ 1 byte (D12) | window progress | approved |
| [F3] | per process: fds free up (D14) | accept | approved; here discharged by `fds_ok` |
| **[F4] connect fairness, per address** | the weak form of [F1]: a connect to a listening address that is attempted infinitely often succeeds (reaches Up) infinitely often | each connect is a new fd, so [F1] does not cover it; EADDRNOTAVAIL/ENOBUFS | **approved** (Q3), trusted. A one-shot connect gets nothing from a weak form, so the L1 connect wrapper retries transient failures (EADDRNOTAVAIL, ENOBUFS, EINTR) itself, never ECONNREFUSED |
| **H-start** (or H-retry) | `start_order`: every connect to `b` follows K's successful `sys_listen`, and every connect to `a` follows P's. Or **H-retry**: the client retries refused connections with back-off, and P and K eventually listen | the startup race | **new**, a launch obligation (e.g. the launch script waits for each port) |
| **resources** | `fds_ok`: P's `fd_limit` ≥ 2N + 4, C's ≥ N + 4, K's ≥ N + 4. `backlog_ok`: N ≤ backlog. `listen_ok`: no `listen_fails` on a or b | bounded client, so bounds replace [F3] | hypotheses, checkable at launch |
| **no OOM** | `no_oom`: no process exits by heap exhaustion. With §2's bounds, C's and P's memory is O(N · (hw + pf_chunk)); K's grows with the store | the compiler theorem's caveat | hypothesis, plus a stated heap bound |
| D16 | hard errors on a channel only when it really broke | spurious errors are allowed by L0 | approved (corollary form) |

```sml
(* THE LIVENESS HEADLINE *)
Theorem moonshot_live:
  l0sys_run (moonshot_sys a b N rqs) rs ∧ isolated (moonshot_sys a b N rqs) rs ∧
  (start_order rs ∨ client_retries) ∧
  sched_fair rs ∧ kernel_fair rs ∧
  (∀k. F1_k rs k ∧ F2_k rs k) ∧ F4 rs ∧
  fds_ok N rs ∧ backlog_ok N rs ∧ listen_ok rs ∧ no_oom rs ∧ no_spurious_hard_err rs ⇒
  (∀i. i < N ⇒ eventually (λevs. ∃ans. LENGTH ans = LENGTH (rqs i) ∧
                                        reply_bytes ans ≼ ep_read i evs) (proc_io rs client)) ∧
  proc_terminates rs client
```

In words: if the processes are started in order (or the client retries),
the OS is fair, transient errors and connect failures are not permanent,
the limits are large enough for N connections, and nothing runs out of
memory, then every request the client sends gets its reply, and the client
exits.

The proof chain:
1. B1 and B3 give an `l1sys_run`.
2. `start_order`, [F4], `backlog_ok` and kernel fairness: every client
   connect reaches Up and is accepted by P. Then P's backend connect
   reaches Up and is accepted by K. This uses R1-live's (live-conn) per
   process.
3. `moonshot_rank_ok` and `no_deadlock` give D, S3 and S4 for every
   direction.
4. R1-live per process gives `psk` complete.
5. The v2/endpoint liveness of each program in its `psk` world, chained
   along the pairing, gives the result:
   - the client sends everything;
   - P forwards it;
   - K replies (`kv_live2`);
   - P forwards the replies;
   - the client reads them.
6. Half-close and the close clauses give termination:
   - C half-closes after its requests;
   - P passes the EOF on;
   - K closes after the client's EOF (`echo_closes2`);
   - P sees K's EOF, and closes the front;
   - C reads EOF and closes.

**Non-vacuity** (decision (b) of design/35 §7):
`moonshot_live_nonvacuous` exhibits one l0sys run meeting every hypothesis
(a round-robin schedule, with simple choices). The hypotheses are many, and
some (F4 with H-start) interact, so this lemma is not optional.

### 4.3 The machine-code corollary

Per binary, CakeML's compiler theorem says: the machine code's FFI trace is
`semantics_prog`'s, or a prefix of it ending in an out-of-memory exit.
`l0sys_run` is defined with "or a prefix, if k exited". So:
- `moonshot_safe` holds of the binaries as they are, OOM included;
- `moonshot_live` needs `no_oom`.

The whole-program obligations of design/36 §6 apply per binary:
- the L1 loop's CF spec in the same `translation_extends` chain;
- the listener fd taken from `sys_listen`, not hard-coded 3 (review 4.3);
- `reserved_ok`;
- fewer than 2^64 connections.

---

## 5. Reuse and new work

| piece | status | used for |
|---|---|---|
| `kv_spec2` / `kv_safe2` / `kv_live2` (HttpKvSpec2, approved) and the KV v2 program | **reuse** (stacked-pr-continuation) | K's spec |
| `kv_relay_closed`'s proof technique (parse_mono, the store run in pieces) | **reuse** the lemmas; the theorem itself is not used (per-fd) | `kv_client_view_safe` |
| `relays`, `relay_safety` (endpointBuffer) | reuse as model-level tools | optional `sys_run'` route |
| endpoint world with Settle-as-arrival (close-v2), `rg_spec_term` | **reuse** | the specs of C and P |
| E1 endpoint handle layer (honest-ffi, decided) | **reuse**, plus `Level` | C and P on L1 |
| PF L1: `honestL1PFModel`, R1-safe (`psk`), R1-live (`fetch_progress`), [F1] per fd, [F2], [F3], D16 | **reuse**, **generalised** over `pol` (S4 becomes S4g) | per-process transfer |
| L0 C incl. `sys_connect`/`sys_connerr`, `honestL0World` | **reuse** unchanged | B1's target |
| translator (design/44: handlers as pure HOL step functions) | **reuse** | proxy and client code |
| compiler theorem | reuse | §4.3 |
| `pol` parameter and `Level` query in L1 | **new** (small) | §2.2 |
| S4g, `writes_follow_feeds`, `pauses_feeders`, `S4g_from_feeds`, `S4_relay` | **new** | §2.3 |
| `proxy_guar'`, proxy program and its proof; `unbounded_needed` bite | **new** | §2.4 |
| `client_guar'`, client program and its proof | **new** | §2.5 |
| `waits`, `rank_ok`, `no_deadlock`, `moonshot_rank_ok`, `perfd_relay_no_rank`, `perfd_relay_deadlock` bite | **new** | §2.6 |
| `l0sys` (trusted) and its conformance probes | **new**, needs user approval | §3.1 |
| B1 `l0sys_proj`, B2 `l0sys_causal`, B3 `l1sys_run` + `l0sys_drains_exact` | **new** | §3.2 |
| `sys_run'` + `l1sys_sys_run'` | **new, optional** (close-v2) | §3.3 |
| `kv_client_safe`, `kv_client_view_safe` | **new** | §4.1 |
| [F0], [F4], H-start, resources | **new** trusted/hypotheses | §4.2 |
| `moonshot_safe`, `moonshot_live`, non-vacuity, machine-code corollaries | **new** | §4 |

---

## 6. Steps, with dependencies

Each step starts by writing its statement. Effort is in agent-days, rough.

| # | step | depends on | effort |
|---|---|---|---|
| 0 | **review this note**; the user decides Q1–Q9 | — | — |
| 1 | `kv_client_safe` + `kv_client_view_safe` (pure trace lemma) | `kv_safe2` | 2 |
| 2 | `l0sys` statement (trusted) + multi-process conformance probes (macOS) | 0 (Q5) | 4 |
| 3 | B2 `l0sys_causal` | 2 | 2 |
| 4 | B1 `l0sys_proj` | 2 | 3 |
| 5 | `pol` parameter in `honestL1PFModel`; re-check R1-safe (pausing is "a later step", so it should be policy-generic) | R1-safe | 2 |
| 6 | **the bite** `perfd_relay_deadlock` (+ `perfd_relay_no_rank`) | 2, 5 | 3 |
| 7 | `Level` in the E1 handle layer | E1 layer (honest-ffi) | 1 |
| 8 | S4g, `S4g_from_feeds`; per-server instances (echo, HTTP, KV) recover S4 | 5 | 3 |
| 9 | the proxy: `proxy_guar'`, the program as a step function, its proof in the endpoint world; `S4_relay`; `unbounded_needed` | 7, 8, translator | 6 |
| 10 | the client: `client_guar'`, the program, its proof | E1 layer, `rg_spec_term` | 3 |
| 11 | R4-style KV transfer: `kv_safe2` on K's raw trace (through `psk`, the instant map) | R1-safe, KV v2 | 3 |
| 12 | **`moonshot_safe`** (model level, then machine code) | 1, 3, 4, 9 (safety part), 10, 11 | 3 |
| 13 | `sys_run'` revision (proposal to close-v2) + `l1sys_sys_run'` | Q7; close-v2 settle | 3 (optional) |
| 14 | B3 `l1sys_run`, `l0sys_drains_exact` | 4, L1 CF loop (phase 5) | 3 |
| 15 | R1-live generalised over `pol` (S3c, S4g) | R1-live, 8 | 3 |
| 16 | **`no_deadlock`** + `moonshot_rank_ok` | 14, 15 | 5 |
| 17 | [F0]/[F4] statements (trusted) and L1 connect retry | 0 (Q3, Q4), 7 | 2 |
| 18 | **`moonshot_live`** | 9, 10, 16, 17, KV `kv_live2` transfer | 6 |
| 19 | non-vacuity | 18 | 3 |
| 20 | machine-code corollaries, launch script with H-start | 12, 18, compiler | 3 |

The **safety path is 1–4, 9–12**: about 25 days, and independent of all the
fairness work. **I recommend landing it first**, as a headline in its own
right: "three verified binaries; whatever the kernel does, the client sees a
linearizable store". Liveness (14–19) follows, and can fail without taking
safety down with it.

Coordination (each is one message, at the step):
- close-v2: step 13, and Settle-as-arrival's effect on `accepts`;
- honest-ffi: steps 5, 7, 15 (`pol`, `Level`, R1-live over `pol`), and 17's
  connect retry;
- stacked-pr-continuation: step 11 (KV v2's raw-trace transfer).

---

## 7. Risks

- **R1. B1 may fail on a real cross-process effect that `l0_rely` rules
  out.** Example: a rely conjunct relating `takes` to the process's own
  drains, which the peer's behaviour need not respect. *Mitigation:* write
  B1's statement and the trusted `l0sys` together (step 2), and check each
  `l0_rely` conjunct against the kernel steps. If one fails, the per-process
  model was dishonest, and fixing it is a gain anyway.
- **R2. The instant map** for K's `precedes2` through `psk` (review 4) is
  the hardest part of the safety path. Expected fine (raw recv ≤ abstract
  read, abstract write ≤ raw send), but it is an argument about two
  different llists.
- **R3. `no_deadlock` with weak [F1]**: the induction must interleave
  "unpaused infinitely often" with "fetch succeeds infinitely often". If the
  unpaused instants and the successful instants never coincide, weak
  fairness gives nothing. *Mitigation:* show that once the feeders' outboxes
  are ≤ hw they *stay* ≤ hw until a fetch (S4g gives this for reply-only
  writers). If not, [F1] per fd must be strengthened to "attempted
  infinitely often *while enabled*", which is a user decision.
- **R4. KV's outbox bound is not hw + chunk.** GETs of large values make
  `resp_bound` depend on the store. This affects memory only, not liveness,
  but the heap bound in `no_oom` must say so.
- **R5. Trusted-surface growth.** `l0sys`, [F0] and [F4] are new trusted
  items. They are larger than anything trusted so far apart from L0 itself.
  Linux conformance is still open (AMBITIOUS-TODO).
- **R6. Close and RST.** If the proxy closes A or B with unread input, the
  peer sees RST and may lose bytes already sent (L8). L1's lingering close
  handles it in our programs, but the liveness proof must use it. K closes
  only after the client's EOF (`echo_closes2`), which helps.
- **R7. macOS never showed a pending connect** (P13). H-start, [F4] and
  `backlog_ok` are stated so that the theorem is still true when connects
  pend, but that path is untested.
- **R8. Quiescence is out of scope.** The proxy re-checks `Level` each
  round, so it busy-polls. A blocking proxy needs a low-water readiness
  event, plus the HUP side condition (review 3). That is not claimed.
- **R9. Scale.** Steps 1–20 are about 60 agent-days. The brief accepts
  failure. The split into safety first and liveness second is how we keep
  the failure partial.

---

## 8. Questions for the user

1. **Q1, the backpressure mechanism.** (P2) L1 gets a `pol` parameter
   (`pol_self` for servers, `pol_never` for the proxy and the client) and a
   `Level` query, and the proxy manages its interest. Or (P1): L1 is told
   the pairing. Or (P3): credits. *Recommended: P2.*
2. **Q2, startup.** H-start, a launch obligation (the script waits for
   each port before starting the next process), or H-retry (the client
   retries refused connections). *Recommended: H-start for the headline.
   H-retry is a later variant: safety is unaffected, and a retried request
   is just a pending operation.*
3. **Q3, connect fairness [F4].** Per-address weak fairness, plus the L1
   connect wrapper retrying transient failures, as in D11. Or a
   resource-bound hypothesis instead (no transient connect failure while
   the system holds fewer than R connections). *Recommended: [F4] with
   retry.*
4. **Q4, [F0].** Approve "the OS schedules every live process infinitely
   often, and the kernel moves bytes and settles connects eventually" as
   trusted, liveness only.
5. **Q5, the scope of `l0sys` (trusted).** Model the port namespace,
   backlog, channel pairing and close-on-exit concretely. Leave ENFILE,
   EADDRNOTAVAIL, ENOBUFS, TIME_WAIT, window sizes and HUP flavours as
   world choices. *Recommended as in §3.1.*
6. **Q6, `isolated`.** The headline assumes no outside process uses ports
   `a` or `b`. Is that acceptable, with the "∃ foreign operations"
   generalisation later?
7. **Q7, the route.** Safety by B1 + B2 (causality), with no `sys_run`.
   Liveness on `l1sys_run`. `sys_run'` kept only as an optional model-level
   layer (a proposal to close-v2). *Recommended. This departs from the
   brief's "endpoint composition" plan.*
8. **Q8, the client.** One client binary with N ≥ 2 concurrent, pipelined
   connections. Or several client binaries. *Recommended: one binary.* It
   keeps the system at three processes, and the per-connection structure is
   the same either way.
9. **Q9, memory.** Safety tolerates OOM (it only truncates traces).
   Liveness assumes `no_oom`, with a stated heap bound
   O(N · (hw + pf_chunk)) + store for K. Acceptable?

---

## 9. Decisions (user, 2026-10-16)

| Q | decision |
|---|---|
| Q1 backpressure | **APPROVED: (P2).** L1 gets the `pol` parameter (`pol_self` for servers, `pol_never` for the proxy and the client) and the `Level` query, and the proxy manages its interest |
| Q2 startup | **H-start first**, for liveness: a launch obligation. Client retry (H-retry) comes later, as a variant |
| Q3 [F4] | **APPROVED, in the same weak form as [F1]:** a connect to a listening address that is attempted infinitely often succeeds infinitely often. The L1 connect wrapper's retry of transient failures (§4.2) is what makes the attempts recur |
| Q4 [F0] | **APPROVED as trusted** (scheduler and kernel fairness), for liveness only |
| Q5 `l0sys` scope | **APPROVED at the minimal scope:** per-process fd tables, the shared port namespace, backlog, loopback pairing and close-on-exit concrete; everything else a world choice (§3.1). **CONDITIONAL** on conformance probes like L0's (multi-process, on macOS) |
| Q6 `isolated` | **accepted** for the headline. The "∃ foreign operations" generalisation comes later |
| Q7 route | **accepted:** safety via B1 + B2 (causality), without `sys_run`. Liveness on `l1sys_run`. `sys_run'` stays an optional layer |
| Q8 client | **accepted:** one client binary with N ≥ 2 connections first |
| Q9 memory | **accepted:** `no_oom` is a hypothesis of liveness only. Safety tolerates OOM |

**l0sys (step 2, PR #158): APPROVED** (user, via the coordinator, 2026-10-17), as drafted, with:
- (a) several listeners may share a port (SO_REUSEADDR is loose in POSIX), so `isolated` covers our ports;
- (b) a connection may break at any time; liveness takes the D16 form ("… unless a connection broke (observed)"), plus a corollary under an explicit no-break hypothesis;
- (c) `Ack` is the kernel's acknowledgement; B3 (`l0sys_drains_exact`) is restated over moved bytes, not application reads.

l0sys inherits the L0 model's `eof_first` (D21, user-approved; honest-ffi, d20-poll) unchanged, because each process is answered by `l0_call`. The §3.1 table's concrete EADDRINUSE is superseded by (a).

**(d) fds below the limit (user, via the coordinator, 2026-10-17):** `sys_init` adds, per process, `∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit`. This is `fds_lt`, the same startup-contract assumption as `l0_server_world`'s. Without it, an initial `reserved` list covering all 2^64 words leaves `lowest_fd` unspecified, so the model could hand out an fd twice (B2's port clause fails). The per-process theorems also all assume `fds_lt w0`. B1's conclusion adds `fds_lt w0`; B2 is unchanged.

**(e) unblock only a blocking poll (user, via the coordinator, 2026-10-17):** `unblock` rewrites the mode byte to 0w only when it is 1w (blocking). Before, it rewrote any mode, so a poll with an invalid mode (≥ 2w) was answered by l0sys as a valid non-blocking poll, while the L0 world (`l0_call` needs `w2n (HD conf) ≤ 1`) fails it with FFI_failed. A run could then record an event no L0 world produces, and B1 (`l0sys_proj`) would be false. Found while proving B1. A mode-0 poll was already unchanged, and a mode-1 poll is handled as before.

The safety path (§6, steps 1–4 and 9–12) starts when its dependencies land.
The coordinator assigns the implementation.

## 10. Known limitations

- **A socket on fd 0 (coordinator, 2026-10-17).** `close_fd` frees a reserved fd, so a process that closes fd 0 can get fd 0 back from a connect or an accept. The trusted C reports a failed connect's socket in the value field, with 0 meaning "no socket", so an fd-0 socket can't be reported. l0sysEpisodes therefore counts an fd-0 episode but gives it no bytes. Consequences:
  - B2 (`l0sys_causal`) is unchanged: `conn` leaves out every pair with an fd-0 episode on either side.
  - Step 12 needs "no process closes fd 0" (or "no process closes a reserved fd"). It is to be discharged for L1 programs, which close only the connection fds they accepted or connected, so step 12's users never see it.
  - A possible later fix in C is a separate no-socket flag. There is no change now.
