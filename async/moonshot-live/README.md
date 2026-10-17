# Moonshot liveness: statement draft and paper no-deadlock sketch (DRAFT)

Branch `spike/moonshot-live` (off `spike/moonshot-glue` @160d12845). Nothing here is proved.

- `moonshotLiveStmtsScript.sml`: `moonshot_live` (main form, observed excuses) and `moonshot_live_strong`
  (the corollary under "no excuse"), typecheck only. Header: the hypotheses and the excuses.
- This file: the paper argument (stage 2): where a waiting cycle could form, why it cannot, and the lemmas.
- `proto/moonshotLiveProtoScript.sml` (stage 3, PROVED, plain HOL): the model-level prototype of one chain.
  - P1 `moonshot_drains`: every receiver asks infinitely often and every hop's kernel empties infinitely often.
  - P2 `moonshot_served` / `moonshot_served_unless`: all replies are read, unless a Drop (the write timeout) happened.
  - P3 `perfd_deadlock`: with per-fd pausing in the proxy there is a fair run in which the client reads nothing.
  - P4 `moonshot_bounded`: the proxy's outboxes stay ≤ hw + CH.
  The write-timeout rule is a parameter (`dok`).

## 1. The chain of one logical connection i

| end | process | fd | role |
|---|---|---|---|
| Cᵢ | client | the connect fd | requests out, replies in |
| Aᵢ | proxy | the accepted front | |
| Bᵢ | proxy | the backend connect | |
| Kᵢ | KV | the accepted fd | |

Four directions. For each, the RECEIVER must keep *asking* (a recv, or a poll listing the fd for input:
`asks_in`), because the observed kernel fairness delivers only to a receiver that asks (§3, F-obs 1).

| dir | bytes | receiver | the receiver asks on its fd iff | so it waits on | rank |
|---|---|---|---|---|---|
| d3 | C → P (requests, Cᵢ→Aᵢ) | proxy on Aᵢ | its L1 inbox of Aᵢ is empty. Aᵢ is always in the interest (`pifds`) and the proxy's L1 is `pol_never`, so it prefetches one chunk, then stops; L2 empties the inbox by `ERead Aᵢ`, which needs the credit gate *Level Bᵢ + writes ≤ hw* (and `bup`, the backend has answered) | d2 (Bᵢ's outbox) | 3 |
| d2 | P → K (requests, Bᵢ→Kᵢ) | KV on Kᵢ | its L1 inbox is empty, Kᵢ is in the interest (D26: until EOF) and *Kᵢ's outbox ≤ hw* (`pol_self`) | d1 (Kᵢ's outbox) | 2 |
| d1 | K → P (replies, Kᵢ→Bᵢ) | proxy on Bᵢ | its L1 inbox of Bᵢ is empty; L2 empties it by `ERead Bᵢ`, gated on *Level Aᵢ + writes ≤ hw* | d0 (Aᵢ's outbox) | 1 |
| d0 | P → C (replies, Aᵢ→Cᵢ) | client on Cᵢ | always (`pol_never`, every connection in the interest, and its L2 reads whatever is ready each round: **to be stated in the client's claim**) | nothing: **the sink** | 0 |

Every wait goes strictly down in rank, so there is no waiting cycle **inside a chain**.

**Edges that could close a cycle, and why they are absent:**
1. *The proxy pausing B on B's own outbox* (per-fd pausing, design/45 finding 1: the d1 ↔ d2 cycle). Absent: the
   proxy's L1 is `pol_never`; its only pause is the cross gate.
2. *KV pausing on anything but its own outbox.* KV's L1 pauses fetching only on `pol_self`; D17's backoff pauses
   only the listener; D26 drops a handle from the interest only at its EOF.
3. *The client's reads waiting on its writes.* `pol_never`, reads every round (to be stated).
4. *Across chains.* The gate is per pair; KV's pause is per fd; KV's store is shared but each request is answered
   in the same round's processing (reply-only writes); every L1 loop is non-blocking and serves all its fds each
   round, so a stalled fd never stops a round. (A blocking KV — the quiet variant — is still fine: its blocking
   poll lists every fd it asks on, and returns once one is ready: `poll_may_return` + `sched_fair`.)
5. *Through the kernel.* l0sys couples nothing between ends: `takes` is a per-end world choice and [F2] is per
   end (nothing in flight ⇒ a byte is taken). The two directions of one socket are independent.
6. *Setup.* A front is read only after its backend has answered a read (`bup`); the backend is read only when
   ready. The first readiness of a backend is its settle report (Up/Refused), with the gate on Aᵢ open (Aᵢ's
   outbox is empty then). **Check at E1/L1** that a settled connect is reported ready at least once (risk R4).

## 2. The induction (per chain, on rank), and why design/45's R3 does not bite

Write `drains X e` for the per-process hypothesis of the existing claims (`honestL1BStmts.drains`, process X's
channel e: once X stops sending on e, e's bytes in flight reach 0).

- **d0.** The client asks on Cᵢ infinitely often (until it closes Cᵢ, after reading its EOF). By F-obs (1) every
  byte the proxy's kernel accepted on Aᵢ moves; by F-obs (2) moved bytes are acked. So `drains P Aᵢ`.
- **d1.** From `drains P Aᵢ`: Aᵢ's outbox is ≤ hw infinitely often (`flush_live`/S4g, unless D23), so the gate for
  `ERead Bᵢ` is open infinitely often. **Stability** (this is what removes R3): a non-empty L1 inbox of Bᵢ *stays*
  non-empty until L2 reads it, and nothing else reads it; so some round has both "gate open" and "Bᵢ ready", and
  L2 reads. Then the inbox is empty and the proxy's L1 polls Bᵢ for input: an ask. Asks infinitely often ⇒ by
  F-obs, `drains K Kᵢ`.
- **d2.** From `drains K Kᵢ`: Kᵢ's outbox is ≤ hw infinitely often. **Stability:** with its inbox empty, KV reads
  nothing new, so it writes nothing new on Kᵢ (`writes_follow_feeds`, reply-only), so the outbox stays ≤ hw until
  the next fetch; L1 then polls Kᵢ for input. Asks infinitely often ⇒ `drains P Bᵢ`.
- **d3.** As d1, with the gate on Level Bᵢ: `drains C Cᵢ`.

So the four `drains` facts are established **before** any data progress, from the "asks infinitely often"
clauses alone. Only weak, "infinitely often ⇒ infinitely often" fairness is used; the coincidence that design/45
R3 feared (unpaused instants never meeting successful ones) is ruled out by the two stability facts.

**The data chain** then uses the per-process liveness claims, each conditional on a `drains` just proved:
client sends all of rqs i (needs `drains C Cᵢ`) → proxy forwards them (`proxy_live_l0` C→K, needs `drains P Bᵢ`)
→ KV answers every complete request it was sent (KV's raw liveness, needs `drains K Kᵢ`) → proxy forwards the
replies (`proxy_live_l0` K→C, needs `drains P Aᵢ`) → the client reads them (it asks; F-obs (1); it reads what is
ready). **Termination** ([R3], owed): client half-close → F-obs (3) → proxy shuts Bᵢ → KV reads EOF, closes
(no unread input, so a FIN, not a RST: R6) → proxy sees EOF, closes Aᵢ → client reads EOF, closes; after N, exits.

**Setup chain:** the client's connect settles (F-obs (4)): Up, or ConnFail (excuse). If Up, it is paired inside
the system (`isolated`) and queued at the proxy; the proxy accepts it (`conn_live_l0`, unless accepts fail
i.o.: excuse); the proxy connects a backend (`proxy_pairs_l0`), which settles likewise, and KV accepts it
(`conn_live`).

## 3. The kernel fairness the argument needs (now honest-ffi's `l0sysFair.kernel_fair_obs`, step 17, approved)

1. bytes reach a receiver that asks (recv **or poll-in**) infinitely often — a recv alone is not enough, since
   L1 recvs only what a poll showed;
2. moved bytes are acked (no receiver condition needed: they are in the receiver's kernel buffer);
3. the EOF reaches a receiver that asks infinitely often;
4. a pending connect settles (Up or ConnFail).

The receiver condition in (1) and (3) is essential: l0sys inboxes are unbounded, so an unconditional (1) would
make every channel drain whatever the receiver does. That would exclude the realistic run of a reader that stops
reading (against the policy), and would make the deadlock bite (`perfd_relay_deadlock`) unstatable: no fair run
could deadlock.

## 4. Lemmas

| lemma | status | owner (suggested) |
|---|---|---|
| per-process: `flush_live` (outbox delivered under `drains`, unless gone/hard/timeout) | **exists** (honestL1PFOutLive) | — |
| `live_data`, `live_conn` (R1-live), `fetch_progress` | **exist** | — |
| S4g / S4w (`S4g_from_feeds`, `S4w_of_feeds`, `S4w_of_stop`) | **exist** (step 8) | — |
| `proxy_live_l0`, `proxy_pairs_l0`, `conn_live_l0` for the proxy | **stated** (rev 6), not proved | honest-ffi |
| `echo_live_l0` (template for KV) | proved (L3-00) | — |
| N1 `l0sys_proj_inf`: B1 for an infinite run (one world for the whole run; the infinite trace is the program's) | **new**, small (B1's construction is history-keyed already) | m4-server / close-v2 |
| N2 world ↔ system: process k's B1 world's `inflight`/`peer_sent`/`sent` are l0sys's `sent − acked`, `moved` | **new**, small | m4-server |
| N3 `kernel_fair_obs` (trusted) and `kernel_fair ⇒ kernel_fair_obs` | **new** (statement: honest-ffi) | honest-ffi |
| N4 "asks infinitely often" clauses, per program, at L1 then L0: client unconditional; KV under `drains` of its own fd; proxy on Bᵢ under `drains Aᵢ`, on Aᵢ under `drains Bᵢ`. Includes the two stability facts | **new**; the proxy's is the real work (gate + bup), KV's follows from S4w + reply-only | honest-ffi (L1), owners (L0) |
| N5 `drains_of_asks`: asks i.o. + F-obs ⇒ `drains` for the peer's channel (the d-step of §2) | **new**, system-level | this worker |
| N6 KV raw liveness `kv_live_l0` (as `echo_live_l0`: every complete request read is answered, under `drains`) | **new** statement + proof | KV worker / async-spike |
| N7 client raw liveness: sends all under `drains`; asks always; reads all ready; [R3] closes and exits | **new** statement + proof | close-v2 |
| N8 the chain glue (pure trace reasoning, as G4/G5) and excuse transfer (per-process excuses ⊆ `sys_excuse`) | **new** | this worker |
| N9 non-vacuity: one fair run meeting the hypotheses | **new**, hard with real programs (needs evaluation of three CakeML programs); at model level in the prototype | later |

## 5. Risks

- **R1 (high): D23 versus backpressure.** Backpressure stalls are the *intended* behaviour: while KV's outbox is
  full, KV stops reading, so the proxy's sends on Bᵢ make no progress; while the gate is closed the client's sends
  stall. L1 times out any fd after `pf_sendwait` = 8 rounds without send progress, and the proxy busy-polls, so
  a normal backpressure episode longer than 8 proxy rounds kills the connection. The main theorem stays true (the
  timeout is an excuse) but in exactly the regime where backpressure matters, it can promise nothing; and the
  corollary's "no timeout" is a hypothesis about the relative speed of our own processes, not about the
  environment. Options: a timeout in time rather than rounds (needs a clock); no write timeout on fds whose
  peer is one of ours (not observable to L1); count only rounds where the fd was polled with a *blocking* poll; or
  accept it. **User decision.**
- **R2: F4 vs EMFILE.** *(Resolved: the user ruled that `moonshot_live` does not assume F4.)* `connect_try` counts attempts that fail with EMFILE/ENFILE (it requires only a listener
  with room), so F4 forces a connect retried forever at the fd limit to get a socket: it excludes a realistic run.
  In the excuse form F4 also seems **unnecessary**: [F1] already covers a connect's transient retries (its
  `call_fds` is the port's), a hard failure is an excuse, and F-obs (4) settles a pending one. Proposal: drop F4
  from `moonshot_live` (keep it for an H-retry variant), or restrict `connect_try` to attempts below the fd limit.
- **R3: `can_step` and Exit.** `prog_makes` holds of every prefix (the replay oracle ends in FFI_failed, which
  Terminates with io = evs), so `can_step`'s second disjunct is always true and Exit is always schedulable; a
  fair run may kill a process at once. Fine — Exit models a kill — but then "crashed" must be an excuse, as drafted.
  `finished` (Terminate Success) tells a normal end from a kill.
- **R4: bootstrapping the backend** (§1 item 6): the settle report must make the backend ready once at L1.
- **R5: global excuses.** The excuse is any of our ends breaking, not one of chain i's. Localising needs the
  proxy's pairing in the statement.
- **R6: the private port c** is not in `isolated` (aligned with the safety headline: a and b only; the
  conclusion is over the client's connect episodes). A stranger connecting to c could still cost the client fds, so
  EMFILE on its connects is possible: that shows up as an excuse (hard connect failure).
- **R7: [R3] close/shutdown** is owed at HL and L1; termination and the KV-closes-after-EOF step depend on it.
- **R8: N9 non-vacuity with real programs** is expensive; the model-level prototype (stage 3) is the cheap check.

## 6. Obligations per program (what each owner must transfer to)

The system-level glue is proved: `moonshotLiveChain.moonshot_chain_drains` (rank chain),
`moonshotLiveDeliver.sys_delivers` (N5b, kernel delivery), `moonshotLiveServed.chain_served`
(the data chain). `chain_served` takes, for one logical connection, the clauses below as hypotheses.
They are stated over an infinite l0sys run (`ss`, `rs`), for the connection's ends: the client's
`(cl, jc)` paired with the proxy's front `(px, ja)`, the proxy's backend `(px, jb)` paired with KV's
`(kv, jk)`, all paired from instant `m`. Each clause may be weakened by the run's excuse `X` (in the
headline, `sys_excuse`: a break, a hard connect/listen failure, a crash, a D23 window, accepts failing
infinitely often). `sys_drains ss e` is the system form of each process's own `drains` premise.

Each owner proves the per-process form on the process's own L0 trace (as `echo_live_l0`, with
`drains w0 io c` premises). The lift to the system forms below is shared work (N1 + N2: B1 for
infinite runs, and the world ↔ system correspondence for `drains`, `peer_sent`, `sent`).

**Client** (close-v2):
- C-asks: `X ∨ io (asks_in ss rs cl jc)`. The client asks for input on its connection (a recv, or a
  poll listing the fd for input) infinitely often, unconditionally, while the episode is open.
- C-sends: `sys_drains ss (cl, jc) ⇒ X ∨ ∃n. m ≤ n ∧ brequests rq ≼ sent_at ss (cl, jc) n`. Under
  drains, all of the connection's requests are eventually taken by the kernel.
- C-reads: `X ∨ ev_ext m (dlv_at ss (cl, jc)) (λn. l0_ep_recvd jep (ptr rs cl n))`. Everything that
  has arrived at the client's end is eventually returned by its recvs on the episode `jep`.

**Proxy** (honest-ffi; `proxy_live_l0` rev 6 has the forwarding part already):
- P-asks-B: `sys_drains ss (px, ja) ⇒ X ∨ io (asks_in ss rs px jb)`. Once the front drains, the proxy
  asks on its backend infinitely often (the credit gate on the front's Level opens infinitely often,
  and a non-empty inbox stays until read).
- P-asks-A: `sys_drains ss (px, jb) ⇒ X ∨ io (asks_in ss rs px ja)`. The same, mirrored.
- P-fwd-CK: `sys_drains ss (px, jb) ⇒ X ∨ ev_ext m (dlv_at ss (px, ja)) (sent_at ss (px, jb))`.
  Everything that has arrived on the front is eventually taken by the kernel on the backend.
- P-fwd-KC: `sys_drains ss (px, ja) ⇒ X ∨ ev_ext m (dlv_at ss (px, jb)) (sent_at ss (px, ja))`.

**KV** (KV worker / async-spike, on `echo_live_l0`'s template):
- K-asks: `sys_drains ss (kv, jk) ⇒ X ∨ io (asks_in ss rs kv jk)`. Once its own outbox drains, KV
  asks infinitely often (`pol_self`: below hw infinitely often; with an empty inbox it writes nothing
  new, so it stays there until the next fetch).
- K-answers: `sys_drains ss (kv, jk) ⇒ kv_answers m X ss (kv, jk)`. For every complete request list
  that has arrived, eventually that many replies are taken by the kernel (count only; which replies
  is `kv_safe`'s).

**All three** ([R3], with close/shutdown): no end of the chain is closed before the client is served.
- The client closes only after reading the EOF.
- The proxy closes the front only after relaying the backend's EOF.
- KV closes only after reading the EOF and replying.

Breaks are already in `sys_excuse`. In `chain_served` this is the hypothesis
`∀n e. MEM e [chain ends] ∧ lost ss e n ∧ ¬served_by … n ⇒ X`.

**Run forms (moonshotLiveObs, @643b72a56):** the clauses above as `client_open`, `client_conn_ob`,
`proxy_ob` (with the proxy's pairing `bk`, front channel → backend channel), `kv_ob`, `topology_ob`
and the joint `closes_ob`, bundled as `moonshot_obs`. Escapes: "X ∨ the episode is done" (`done_by`:
sent exactly rq, complete replies read) or "X ∨ an own chain end has ended" (`ended`: the end is
frozen, i.e. it has seen its peer's EOF, broken or closed); `closes_ob` turns an end before done into
X. Design requirement on the proxy: a backend connect that fails with a transient error must be retried
(not answered by closing the front): a transient failure is no excuse, and by D41's F1 on connect, keyed by
(process, port), retrying i.o. gives a non-transient outcome i.o. A refusal (ConnFail, or ECONNREFUSED at
once) is kern_broke or hard_fail, so closing the front then is covered.

**Setup chain, the kernel's part (moonshotLiveSetup): `connect_pairs` PROVED.** A connect end to a port
of `isolated` is eventually ended or paired with an end of the only process that listens on the port.
Uses: targets persist (`irun_target`); a pair is only ever made with a process that listened on the
target before (`irun_pair_listens`); and settlement, by (C) and `isolated`'s last clause
(`connect_settles`).

**Lift obligations (inputs to the per-program lifts, not statement changes):** honest-ffi's
`conn_live_l0` needs `accepts_lt (2**62 + 1)` (honest-ffi's corrected exact bound). **System part PROVED
(moonshotLiveAccepts):** `irun_accepts_le`: in an isolated run, at every n, if process k's accepted episodes
are all on port p ∈ ports, then `LENGTH (l0_accepted (ptr rs k n)) ≤ conns_ok p ss rs cl n`, given that no
other process connects to p and ¬free0 for cl (each connect after its check of fd 0, with no close of fd 0 before it; D33). `conns_ok` counts cl's Connected-p episodes whose
channel was not broken right after the connect (`born_broken`), since such an end is never paired
(`irun_bb`). This matches close-v2's narrow D43 fact 1 (X' ∨ count ≤ N, with X' ⇒ kern_broke).
`accepts_lt_lift` then gives `accepts_lt M tr` from `∀n. conns_ok p ss rs cl n ≤ N`, `N < M` and "every
prefix of tr is a prefix of some ptr rs k n". Remaining obligations: the proxy accepts only on a
(honest-ffi); only the client connects to a (system topology: KV and the proxy connect only to b); the
client's trace starts with the check of fd 0 and never closes it (`free0_stdio` reduces ¬free0 to that; stdio_open and no_close_stdio, close-v2) and X' ∨ at most N counted episodes
to a (close-v2, scheduled after (A)). Relating close-v2's per-process count (world_at) to `conns_ok` is part
of the client lift (moonshot-live). io-prefix ⊆ ptr-prefix is PROVED for a proxy calling infinitely often
(`accepts_lt_irun`, via `ptr_of_prefix`, the same premise as `l0sys_proj_drains`). The fd 0 clause is needed
because a connect that gets fd 0 reports "no socket" and makes no episode (D33: fd 0 may start closed). `zinv`
is moonshotW2's `fd0_used`; `tinv`'s second disjunct is `free0`. D43: N < 2^62 kept for now; N ≤ 2^62 (M = 2^62 + 1) is with the user. KV's claim needs F1_io, F2 and accepts_below; the proxy's asks clauses need
`proxy_asks_l0` (honest-ffi rev 9, drafting).

**Composition PROVED (moonshotLiveCompose):** `moonshot_served_of_obs` proves
`moonshot_served_of_obs_claim`: from `moonshot_obs`, unless X, `client_served`. Per connection
(`conn_done_of_obs`): the client's end is paired with a front (`connect_pairs`, topology_ob), the front
gets a backend (proxy_ob), and the backend is paired with KV (`connect_pairs`). No chain end ends before
the connection is done (closes_ob). `chain_served` then runs with X := F under ¬X ∧ ¬done, and served
plus all requests sent gives done, a contradiction. Episode channels come from the run's ghost
(`irun_sinv_css`, `ep_connected_chan`, `ep_sent_le`).

`moonshot_live_of_obs` (PROVED) then gives `moonshot_live` from `moonshot_obs` with X = `sys_excuse`, plus the
termination obligation ([R3]) as an explicit hypothesis.

**Mine (system level), still to do:** N1/N2 lifts; the excuse transfer (per-process excuses ⇒ `sys_excuse`); termination
from F-obs (F) once [R3] lands; and `moonshot_live` from `chain_served` for each i < N.

### Final instantiation (`moonshotLiveFinalScript.sml`)
`moonshot_live_of_run_obs` (proved): `client_run_ob kb cprog ∧ proxy_run_ob kb pprog ∧ kv_run_ob kb kprog ∧
topology_run_ob ∧ closes_run_ob ∧ exits_run_ob ⇒ moonshot_live kb cprog pprog kprog`. Each `_run_ob` is stated
for every run of `moonshot_live_hyps`, with X = `sys_excuse`. At the concrete programs, the headline is this
theorem INSTed at `client_prog`, as in `moonshot_safe_client`. Who delivers what:
- **close-v2**, `client_run_ob kb client_prog`: from `client_live_claim` plus the moonshot-live lift
  (`l0sys_proj_inf`/`l0sys_proj_drains`). Includes `client_open` (one connect episode per logical connection to a)
  and, per episode, `client_conn_ob` (asks, sends under drains, never more than rq, reads what arrives).
- **honest-ffi**, `proxy_run_ob kb proxy_prog`: from `proxy_live_l0` + `proxy_pairs_l0` + `proxy_asks_claim` +
  `conn_live_l0`. Its accepts_lt premise is discharged by `accepts_lt_irun` (moonshot-live), given "the proxy
  accepts only on a" and close-v2's episode bound and "never closes fd 0".
- **KV owner**, `kv_run_ob kb kv_prog`: from `kv_live_claim` plus the lift.
- **CALLS-IO** (`calls_io 1`, `calls_io 2`): the proxy and KV call infinitely often. A premise of the lifts, owed
  per program from its Sem theorem's infinite-trace form (e1-driver's proxySem/KV: Diverge, with io the LFLATTEN of
  rounds that each contain a non-blocking poll).
- **topology_run_ob**: only the proxy listens on a, only KV on b (from the programs' code, through the lifts).
- **[R3]**, `closes_run_ob` and `exits_run_ob`: owed, joint (r3-close).

Shared lift pieces (`moonshotLiveLiftScript.sml`, moonshot-live):
- `proj_world` (proved): the world w0 of each process's projection is an `l0_server_world`, and `F2_sys` gives `F2 w0`.
- **[F1]**: `F1_sys` does not cover polls, since a poll's conf is 1 byte. The L1 proofs use F1 on `«sys_poll» f`
  (`F1_io`/`call_fds`). Q-16 is open with the user: (B) add `F1_poll_sys` to `moonshot_live_hyps` (recommended),
  or (A) re-key `F1_sys`. Listen is covered by `listen_failed`, connect by `F1_connect_sys`, and every other call
  by `F1_sys`.
- KV, G3: honest-ffi's proxy backend cap. Over the proxy trace, `backend_broke ∨ conn_ok_count b ≤ 2^62` gives
  `accepts_lt_irun`'s `conns_ok` premise with cl = 1, p = b, N = 2^62.
- KV, G2 (`peer_valid`, K-asks' premise). System level, `kv_peer_valid_sys` (moonshotLiveRelay, proved). At every
  instant, a KV end paired with a connect to b (kv_ob's ends) has received a prefix of `brequests rqs` for valid
  rqs. The chain:
  - KV's peer_sent ≼ the backend's sent (kinv);
  - the backend's sent = the proxy's episode sent (pinv);
  - ≼ the front's recvd (`relay_ok`);
  - ≼ the client's episode sent (causal_at, with acc_peer pairing the front with the client's connect);
  - ≼ brequests (`csend_ok`).

  Before its pairing such an end had received nothing (`irun_peer_or_empty`).

  Hypotheses still to discharge:
  - `relay_ok`: clauses 3 and 5 of close-v2's `proxy_safe_ep`, through `proxy_safe_bridge` at ft = ptr rs 1 n;
  - `csend_ok`: the client's C-sends;
  - `no_fd0` for client and proxy: moonshotW2's `l0sys_no_fd0` (fd0_checked, no_close0);
  - ¬free0 for client and proxy (`free0_stdio`);
  - only the client connects to a, and only the proxy to b.

  World level, `world_peer_valid` (moonshotLiveRelayWorld, proved, generic in k): the system fact at every instant
  gives `peer_valid w0 tr c`, with the hypotheses of N2's `world_drains`. Uses a temporary copy of `peer_valid_def` (honestKvL0LiveStmts, spike/kv-live-l0 @ bbf45dfe8); remove it when the lines merge. `relay_ok_of_ep` and `csend_ok_of_client` (same theory, proved) give `relay_ok` from proxy_safe_ep's cover and relay clauses (via `proxy_safe_bridge` at ft = ptr rs 1 n) and `csend_ok` from client_safe_l0's connect clause.

  **G2 top, `kv_peer_valid_run` (moonshotLiveG2, proved @0148e71ea):** discharges `relay_ok`, `csend_ok`, `no_fd0`,
  ¬free0 and the topology from per-trace clauses at every n: `start0`/`no_close0` for ptr 0 and ptr 1 (the trace
  starts with the fd 0 check; never closes fd 0), `conns_only a` (client), `conns_only b` (proxy), `no_conns` (KV),
  proxy_safe_ep's cover and relay clauses on ptr rs 1 n, client_safe_l0's connect clause on ptr rs 0 n. Still to lift:
  the programs' claims → those clauses.
- KV, G3 plug-in, `conns_ok_cap` (moonshotLiveConnCap, proved): a cap on the Connected episodes of every finite prefix
  of tr ⊇ every ptr rs cl n caps `conns_ok` at every n. Under (A) G3 becomes honest-ffi's `proxy_conn_kept_cap_run`
  (counts `conn_kept`: Connected episodes whose connect returned Ok or Fail E_INPROGRESS; spike/proxy-r3, SHA to come);
  `conns_ok ≤ #conn_kept` since a fail-at-once connect is `born_broken` (to prove). The pre-(A) `proxy_conn_cap_run`
  (spike/proxy-asks-l0 @66a541c81) stays on the safety line.
- Proxy totality (ptot), a named hypothesis of the G3 use, cited not merged: m4-server's `proxyClaim.proxy_ptot`
  (spike/proxy-transfer @0810a7cfe, moonshot-step9/transfer/proxyClaimScript.sml):
  `proxy_start a w0 pre w4 k ∧ b < 65536 ⇒ (∀n. erounds (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw) (w4, einit) n ≠ NONE) ∧ ∀n. SND (ecm …) + 1 < dimword (:64)`.
  The liveness line re-proves it on the R3 proxy; the real merge is at final integration.
