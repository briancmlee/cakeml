# Layer 11: quiescence, and option C

> **In this repository.** The design note below (design/33) was written as a
> cost estimate on `spike/quiet-spec`; §6 records the result. In the review
> series its files live at:
> - `quiet/ffi/`: `ffiAgreeUpto`, FFI states that answer the same along a
>   run (generic CakeML semantics), used by both bridges to QuietSpec;
> - `quiet/echo/`: the shipped blocking echo (layer 8) is quiet:
>   **`echo_blocking_quiet`** (echoQuiet);
> - `servers/level2-proto/`: `server_with2` (the Level 2 accept/fork
>   skeleton, lifted from #53's `asyncHttpServer2H`) and `proto2`
>   (`proto_server_v2`, erasing to layer 10's `server_v` / `proto_handler_v`);
> - `programs/http-level2/`: the Level 2 protocol server in CakeML
>   (`asyncOC*`, ending in `sproto_server2_spec`);
> - `loop/select-interest/`: the loop that selects on the declared interest
>   (`qsel`, `step_q` / `run_q`, `run_q_two_outcomes`, `qsel_sleeps`,
>   `proto_acc`, `trace_good_q`);
> - `servers/proto-stable/`: the generic protocol server is stable after the
>   last arrival (cf-actions' `proto_stable`);
> - `programs/http-quiet/`: the HTTP-bodies program on that loop
>   (`http_blocking_spec`) and the headline, unconditional:
>   **`http_blocking_quiet : ⊢ http_quiet 3w demo_files (SNOC (main_call «main») http_blocking_prog)`**
>   (httpQuietHeadline).
>
> Paths in §1–§5 refer to the spike layout; the table in §6 gives the
> series paths.

# 33: Option C: select on the declared interest, and quiescence (costing)

Branch `spike/quiet-spec`. **A cost estimate, not an implementation.**
It goes with `spec/QuietSpecScript.sml` (QuietSpec, for review).

## 0. The point

Both spin bugs have one cause. The loop *guesses* the select set from the
trace: #27 used the whole interest list, and #46/#56 the accept/EOF live
list. With option C the loop *asks the computation*. A Level 2
computation declares what it waits for (`comp2.interest`; asyncLevel2).
So the loop selects on exactly that, the project's Future/Waker idea.
- A finished handler declares nothing.
- A handler that stopped on an invalid request declares nothing.
- A closed connection is in the set only while some handler still waits
  on it.

`sel_covers` then holds with equality, by construction. There is no
special case, and no live-list bookkeeping.

## 1. What exists and is reused

| piece | where | lines | reused as |
|---|---|---|---|
| Level 2 model: `comp2`, `bind2`, `both2`, `map2`, `wait_on`, `emit2`, `fix2`, `erase`, `quiet`, `wf2` | model/level2 (layer 3) | ~1,300 | unchanged |
| no busy-waiting: `blocked`, `no_busy_waiting` | model/sched (asyncSched2) | 228 | unchanged |
| echo server at Level 2 (`server2`, `wf2_server2`) | servers/echo/echoServer2 | 194 | unchanged |
| HTTP (headers) at Level 2 (`server_with2`, `http_server2_h`, `wf2_http_server2_h`) | servers/http-quiet (#53) | 230 | unchanged; `server_with2` is generic |
| Level 2 CakeML library: `Pending2 es k`, `STEPA2`, specs of return2, poll2, interest, wait_on, never2, emit2, skip2, bind2 | loop/blocking-l2 (loopBlock2Prog/Spec/Model) | 695 | extended (§2.1) |
| blocking loop over a generic world, `brun_two_outcomes` | loop/blocking-l2 (Loop, Stuck) | 940 | the template for the socket loop |
| select-set loop over sockets: `lbgrounds` (any `sel` with `sel_covers`), two outcomes, transfer of safety/liveness | loopSelectSet (#46), asyncHttpBlkTransfer (#56) | 760 | unchanged; the select set becomes the declared interest |
| relabelling the interest to socket words (`secho`, `shttp`) | echoBlockingSet, asyncHttpLiveSel | ~120 | the same shape |
| server specs in the socket vocabulary (depth-indexed) | programs/echo, programs/http(-h) | ~900 | the template for the Level 2 ones |

## 2. What is new

### 2.1 The Level 2 CakeML library (CF), completed
- `both2` / `map2` specs. The declared interest of `both2` is the union of
  what the *waiting* sides declare (`waiting_on`). The CakeML value carries
  both residuals' event lists, so the spec is the Level 1 `both_spec` plus
  the union, tracked through `STEPA2`. Template: `libBoth` +
  `libBothModel` (238 lines). **Est. 350 lines.**
- Recursion: depth-indexed `STEPA2d` / `COMP2d`, the limit lemma, and the
  depth-n specs of poll2/bind2/both2. Template: `libApprox` (422
  lines). The interest is one more component, equal at every depth.
  **Est. 500 lines.** The limit lemma is where the interest must be shown
  to stabilise per round. It does: at a fixed history it is a function of
  the residual.
- Replay in the socket program (one CakeML program = one translation chain;
  as M3 did for Level 1): the `Async2` module plus specs. **Est. 400
  lines, mostly copied.**

### 2.2 The servers in CakeML at Level 2
- `sserver_with2` (the skeleton, once, for any handler with a Level 2
  spec) and the echo, HTTP-headers and HTTP-bodies handlers.
  - Templates: `asyncHttpSockSpec` (338 lines) and the H/B handler specs
    (~200 each).
  - At Level 2 each `wait_on` declares `Readable fd`, and `emit2` declares
    nothing.
  - **Est. 900 lines** (all three servers).
- Model side: relabelling distributes over the Level 2 combinators
  (`relabel2_bind2`, `relabel2_both2`, …; template `relabelDist`,
  163 lines). The bodies server at Level 2 (as #53 did for headers).
  **Est. 450 lines.**

### 2.3 The loop
- `step_q` / `run_q`: perform the round's actions; if there are none and
  the computation is `Pending2 es _`, select on `es` (mapped to fds),
  otherwise poll the interest list. This is #46's `step_l` minus the
  live-list update, and plus reading `es` from the value.
- Proof:
  - the generic `lbgrounds` results apply with `sel h = declared interest
    at h`;
  - `sel_covers` is the definition;
  - quiet comes from `wf2` of the server.
- **Selects only on model sockets.** QuietSpec's `ffi_select` fails on an
  fd that is not a listener or connection of the model (`sel_ok`, a
  user-approved spec change). The declared interest is `Readable lfd` and
  `Readable fd` for fds returned by accept, which are sockets of the model
  (`deliver1` adds a connection to `conns` when it arrives, and the
  v1 model never removes one). So `step_q`'s select set satisfies `sel_ok`
  by construction. The proof obligation is one invariant of the loop:
  every fd in the interest is the listener or was accepted.
- **Est. 500 lines.** Template: echoBlockingProg (653 lines), with the
  live-list lemmas dropped.

### 2.4 The whole programs, in QuietSpec's world
- A bridge `select_ffi = ssel_ffi`: QuietSpec's select model is #27/#46's
  `ffi_sock_select`. Est. 50 lines.
- `main` and the two-outcome semantics per program. Template:
  echoBlockingMain (203 lines). **Est. 250 lines per program.**

### 2.5 Quiescence: the new mathematics
QuietSpec's extra clause: if `arrivals_finite sk`, the run ends asleep.
- **What asyncSched2 gives.** `no_busy_waiting` says the blocking run
  performs exactly the polling run's actions. That is an *equivalence*.
  It does not say the blocking run ever *stops*, so quiescence needs a
  progress argument too.
- **The argument.** After the last arrival (step N) the world is
  *static*: `tick` changes nothing that `is_ready` sees. In a static
  world:
  1. **Stability:** the computation reaches a round where it has no
     action to perform and none of its declared events is ready. Then
     select blocks forever (`sel_wait = NONE`, because nothing will ever
     become ready), which is `asleep`.
  2. **Progress, to get there:** a measure that strictly decreases within
     every k rounds while some declared event is ready. For example: the
     bytes unread on connections a handler waits on, the handlers'
     buffered complete requests, the pending connections, and the unread
     EOFs on waited-on connections. Each of these only decreases in a
     static world. While one is positive, the server consumes some of it
     within k rounds. That is the existing progress lemmas: `read_soon_s`,
     `accept_soon_s` and `sw_accept_soon_s`, and the HTTP drain machines
     `hmachine_live` / `asyncHttpDrainB`, with k = 3–4.
  3. **Liveness for the finite trace:** what arrived was answered before
     the final select. This follows from the existing liveness
     (`echo_live_rounds`, `http_live_rounds`) and the two-outcome
     transfer, restricted to the finite prefix.
- **The hardest lemma: progress ⇒ stability.** It combines the measure
  (a sum over the connections the server waits on) with the per-handler
  progress lemmas through the handler views (`sw_handler_view`). One
  subtlety: declared-but-not-ready events must not stall the measure
  (they cost nothing). Another: a finished handler's connection drops out
  of the measure exactly when it drops out of the interest. Option C makes
  that alignment true by construction. With the live list it is false,
  which is the #56 bug.
- **Est.** about 400 lines of generic static-world facts (`ticks` on a
  quiet schedule, the measure, "sleeps when stable"), plus about 500 per
  server family for progress ⇒ stability, reusing that family's existing
  progress lemmas.

## 3. Totals

| part | est. lines | template |
|---|---|---|
| 2.1 Level 2 library (both2/map2/recursion, replay) | 1,250 | Level 1 CF layer |
| 2.2 servers at Level 2 (CF + model) | 1,350 | layer 7/9 specs, #53 |
| 2.3 loop | 500 | #46 |
| 2.4 programs + bridge (echo, HTTP bodies) | 550 | #46 / #56 |
| 2.5 quiescence (generic + echo + HTTP bodies) | 1,400 | new; reuses progress lemmas |
| **total** | **≈5,000** (±30%) | |

At the pace of the existing workers (#46 took about 2,000 lines; #56
about 1,800 including replay), this is **4–6 worker-days** for echo plus
HTTP bodies:
- 2.1–2.4 are mostly mechanical, after the templates;
- 2.5 is the research risk, about 2 days on its own.

Echo first (simplest handler), then HTTP bodies. HTTP headers is archive
and need not be redone.

## 4. Does `with_store` (KV) compose?

**Corrected (the user approved the pure `with_store δ s0 m`:
stacked-pr-continuation, `http-kv/withStore`).**

`with_store` answers the inner computation's `Kv` queries itself, from a
store carried in the history. It passes only `Sock` actions out, and its
answers arrive **in the next snapshot**, merged into that round's results
(`inner_hist`).

**The catch for option C.**
- In a round where `m` emits only `Kv` queries, `with_store δ s0 m` emits
  *nothing*, and has no outer response due.
- If its declared interest were just `m`'s socket events, a loop
  selecting on the declared interest would block. The `Kv` answers would
  then wait for an unrelated socket to become ready, possibly forever.
- The model sees the same problem as a failure of `quiet`. That snapshot,
  with nothing declared ready and no outer response due, *does* change
  what `m` sees, because it carries the store's answers. So it cannot be
  deleted.

**The fix: declare "ready now" while answers are pending.**
- Add one event, `Now`, which every snapshot reports ready: the poll
  always includes it.
- `with_store`'s Level 2 interest is `{Now}` (with `m`'s socket events)
  while some `Kv` query has no answer yet, and `m`'s socket events
  otherwise.
- Then `quiet (with_store2 δ s0 m2)` follows from `quiet m2`:
  - a snapshot in which nothing declared is ready can only occur when no
    `Kv` is pending, because `Now` is always ready;
  - so it carries no store answers, and `m2`'s own quietness applies.
- In the loop, a declared `Now` means "do not select; poll". `step_q`
  selects only when the round's actions are `[]` *and* `Now ∉ es`.
- Cost: one event constructor, the interest of `with_store2` (about 150
  lines with `quiet_with_store2`), and one test in `step_q`.
- An alternative is to answer `Kv` queries in the *same* round (no
  pending state at all), but that changes `with_store`'s approved
  semantics, so I don't propose it.

**Quiescence.** The measure needs a term for pending `Kv` answers, but a
trivial one.
- A pending answer is delivered in the very next round, whatever the
  world does. With `Now`, the loop does not sleep in between.
- New queries come only from handling requests: one `Kv` per complete
  request, in the KV handler's `HA → HK → HB` pipeline.
- So the measure's "complete requests not yet answered" term becomes
  lexicographic in the pipeline stage. A request in stage `HK` moves on
  in one round, unconditionally.
- No new progress lemma is needed beyond the handler's: `hmachine_live`'s
  bound becomes 3K+2, as design/30 notes.

The store is no heap object, and the loop and FFI are unchanged, so
nothing else in §2 changes. **Est. +250 lines** on top of §3's total, for
`with_store2`, its interest and `quiet`, and the measure term.

## 5. Risks and alternatives
- **Recursion at Level 2 in CF (2.1)** is the largest mechanical piece.
  If the depth-indexed limit does not lift directly, a fallback is an
  explicit `fix2` in CakeML with an inductive spec over rounds, as
  `brun` does.
- **Quantitative quiescence** (bounding the rounds between the last
  arrival and the final select) would follow from 2.5's measure with the
  progress bounds: about k × (bytes/bufsz + connections) rounds. That is
  extra statement work, not extra proof structure. QuietSpec deliberately
  leaves it out.
- **Option B** (a `Close` action, close-v2) fixes the invalid-request
  spin with less work, but it is still a guess: the loop learns about
  finished handlers only if they close. Option C is the principled fix,
  and makes QuietSpec provable without special cases.

## 6. Result (spike/option-c-int, 2026-10-16)

The plan above has been carried out, with no remaining hypothesis: the
server's stability after the last arrival (PROTO_STABLE) is cf-actions'
`proto_stable`, and the headline `http_blocking_quiet` is unconditional.

**The root cause of both spins.** The blocking loops chose their select
set from the transcript:
- #27 selected on the whole interest list;
- #46 and #56 selected on the accepted connections not yet at EOF.

Neither is what the computation waits for. A handler that stopped early
(invalid request) or finished before EOF leaves an fd in the set; select
returns at once for it and nobody reads it, so the loop spins.

**The fix: select on the declared interest.** Under option C, the loop
reads the declared interest from the Level 2 computation itself
(`interest c`, sorted and deduplicated: `qsel`). So `sel_covers c (qsel c)`
holds by construction (`sel_covers_qsel`). A finished handler declares
nothing, so its fd drops out of the select set automatically. There is no
live-list bookkeeping.

**The chain of results:**

| step | result | where |
|---|---|---|
| library | `both2_specI`, `map2_specI`, depth-indexed recursion; event lists in any order (EVSET) | cakeml/level2 (layer 5), programs/http-level2 |
| server model | `proto_server_v2`, `erase_proto_server_v2` (exactly cf-actions' `server_v`/`proto_handler_v`), `wf2_*` | servers/level2-proto/proto2 |
| server in CakeML | `sproto_server2_spec` | programs/http-level2/proto2SockSpec |
| loop | `run_q_two_outcomes` (#46's rounds, `lbgrounds (qsel c)`) | loop/select-interest/loopInterestRun |
| program | `http_blocking_spec`: both outcomes safe; live when sched_wf | programs/http-quiet/httpBlockingSemantics |
| sleeping | `qsel_sleeps` (generic), `hb_sleeps` | loop/select-interest/loopInterestSleeps, programs/http-quiet/httpQuietStable |
| QuietSpec bridge | `proto_acc`: the server waits only on the listener and accepted fds; `trace_good_q` | loop/select-interest/loopInterestAcc, loopInterestTrace |
| stability | `proto_stable` (any `proto_ok P`), hence PROTO_STABLE P_b resp_b | servers/proto-stable/protoStable |
| headline | `http_blocking_quiet: ⊢ http_quiet 3w demo_files (SNOC (main_call «main») http_blocking_prog)` | programs/http-quiet/httpQuietHeadline |

**Honest scope:**
- Everything is generic in the protocol (P, resp); HTTP bodies is the
  instance proved. KV needs the `Now` event of §4 and is not done.
- The spec is layer 1's HttpSpec, with tchar and H-CHARS (both
  user-approved).
- The shipped blocking *echo* is proved quiet separately, without option C
  (`echo_blocking_quiet`, #77).
