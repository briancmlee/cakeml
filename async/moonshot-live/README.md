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

## 3. The kernel fairness the argument needs (for honest-ffi's `kernel_fair_obs`)

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
- **R2: F4 vs EMFILE.** `connect_try` counts attempts that fail with EMFILE/ENFILE (it requires only a listener
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
