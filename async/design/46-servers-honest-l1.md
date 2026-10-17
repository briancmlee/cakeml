# 46. Servers on the honest FFI's prefetching L1 (CakeML level)

Branch `spike/servers-honest-l1`, PR #147. Worker: KV worker. This note covers P1–P3 for echo.
HTTP and KV (P4) come later, and their statements go to the user first.

## Layers

| Dir | Theory | What it is |
|---|---|---|
| `honest-l0-cf` | honestL0Part | The L0 world as an FFI part, by history replay. `l0_parts_ok` is the adequacy theorem. |
| | honestL0Prog, honestL0Proof | The `L0` wrappers and `L0_x_spec` against `L0_EV w0 w evs`. |
| `honest-l1-cf` | honestL1PFProg, honestL1PFSpec | design/36's prefetching L1 (honestL1PFModel, including D17), in CakeML. Its CF specs end in `run_pf_spec`. |
| `honest-echo` | honestEchoL0Spec | The trusted raw-trace definitions, user-approved: `l0_accepted`, `l0_ep_events`, `l0_read`, `l0_sent`, `l0_server_world`, `echo_safe_l0`. |
| | honestEchoL0Bites | The bites and non-vacuity, done before the proof as the user required. |
| | honestEchoL0Prog, Main, Sem | `echo_l0_prog`. `main` listens on port 8080, then runs `run_pf` with the unchanged v2 echo server on the returned fd. `echo_l0_semantics_prog` gives its whole-program semantics. |

## Decision (A): handle-counter overflow

The model's `pdo` fails (`NONE`) once the handle counter overflows, which happens after about 2^64 handed-out connections. The CakeML loop is made faithful to that:

- `step_pf` first checks `hdl_room lfd ps (LENGTH acts)`: room in the handle counter for the round's actions, plus one for a pending accepted connection.
- If there is no room, the step returns its state unchanged. From then on, the loop spins without I/O.

So **after 2^64 accepted connections the L1 loop stops doing I/O (it spins). This is unreachable in practice.**
**Amended by D40 (user, Q-9, 2026-10-17):** the guard is `nxt + n + 2 < 2^64`, so the loop stops after 2^64−3
handed-out connections (see "P4 gap 2 detail" below). We chose this deliberately over wrapping the counter, because wrapping would reuse handles.

The divergence spec is stated against `prounds_t`:

- `prounds_t` is `prounds` while there is room; after that the state stays fixed.
- It needs only `pt_ok` (the server's actions are `pact_ok`), not a global connection bound.

The coordinator approved this.

## The echo safety transfer: route (d), not (c)

`echo_safe_l0` is proved directly, without R1/psk:

- **Model:** asyncServerSafety's `echo_server_safety` says that, per handle, the server's writes equal its reads in its transcript. It needs the handed-out handles to be distinct, and the `hdl_room` guard gives that.
- **L1 invariant over `prounds_t`, per episode j** (the j-th FConn fd, which is handle j):
  - `raw_sent ++ outbox ≼ writes`;
  - `raw_recv = reads ++ inb`.
- **Round lag:** the writes in round i echo reads answered by round i−1, and those reads come from bytes fetched by round i−1. So `sent(prefix) ≼ recv(prefix)`, as in close-v2's `echo2_safe`.

Route (c), through R1 (`l1pf_refines_hl`, psk) and close-v2's `echo2_safe`, was not taken, for two reasons:

- it needs `sched_wf2 psk` for every step, which requires a global bound;
- it needs an output-side relation that does not exist yet: psk's per-episode bytes ↔ raw L0 send events. `pv_rel` covers only the input side.

**This choice is for echo only. HTTP, KV and the moonshot need the generic output-side relation** (psk's per-episode bytes ↔ raw L0 events, and `precedes` through psk), which is the core of the R4′ template. KV's linearizability compares real-time order across connections, and a per-handle local invariant cannot carry that. After D19, honest-ffi plans to extend `pv_rel` to the output side.

### Tracked near-duplicate: echo's output half

Echo's output half is proved locally in `honest-echo/honestEchoL0Inv`: per episode j, `ep_sn j ++ outbox ≼ hwritten (handle j)`. It mirrors the input half on the same `own_ok` invariant. This is a **tracked near-duplicate** of honest-ffi's `out_rel` and `l1pf_round_sent_upto` (honestL1PFOut). The coordinator approved it, for two reasons:

- consuming `out_rel` needs the per-round connection-count bound on `prounds`, which would make the proof a circular strong induction with this invariant;
- it also needs a key bridge from episodes (accept order) to v2 clients (`cl cm f`) and channels.

KV needs that key bridge anyway (moonshot step 11, the R4-style transfer). **Once the bridge exists, re-derive echo through `out_rel` and delete the local output half.**

**Superseded (2026-10-17, coordinator):** Inv/Out is not deleted. It becomes the shared raw ↔ handle layer for echo, KV and HTTP; move it to a shared directory later. The key bridge is the identity. L1's acq grows only at its tail (pf_fetch) and only pdo Accept pops its head, so raw episode j = client j = handle l1hdl lfd j = v2 episode j. KV goes raw → handle j by ri (generalised as honestKvL0Run's ri_gen, under `writes_accepted m`) and handle j → v2 episode j by asyncKv2Bridge's kv2_rounds_bytes and R1's hhist. Route (b), out_rel and a client key bridge, was rejected: it costs several theories and re-proves what ri gives.

## P4 plan: HTTP and KV by the generic route (draft, 2026-10-17)

The claims are fixed (`honestHttpKvL0Spec`). The route goes from the version-2 handle-layer safety
of the unchanged servers, through R1 (psk), to the raw L0 trace.

**Ingredients that exist.**
- `kv2_safe`: `kv_safe2 (gtrace2 (kv_server lfdn) lfdn s2)` holds for a fresh one-listener `s2` with
  `alloc_ok` and `sched_wf2`. It is on spike/kv-order-generic (asyncKv2Safe), **not on shared/base**.
- `kv_safe2 = kv_safe_g ep_read ep_written` (moonshotKvClient's `kv_safe2_g`, or `kv_safe2_G`):
  safety stated over any pair of projections.
- R1: `l1pf_refines_hl(_upto)` (input side, pv_rel) and `l1pf_refines_hl_out(_upto)` /
  `l1pf_round_sent_upto` (output side). Also `psk_sched_wf2` and `run_alloc_ok`.
- honestL1PFClient / honestL1PFInput: raw episode → client key. Episode j's fd f, accepted in round
  a, is client `cl (pcm a) f` (`client_stable`, `client_since`).

**Gap 1: there is no version-2 HTTP-with-bodies safety theorem.** No branch proves
`http_safe_b2 (gtrace2 (http_server_b files lfdn) lfdn s2)`. It would be about echo2_safe's size,
using the generic sim (asyncHLSimRunGen and its ep-rounds lemma) plus `http_server_safety_b`
(per-fd: written ≼ responses to read).

**Gap 2: the global bound.** `sched_wf2 psk` and the non-`_upto` R1 theorems need
`∀n. SND (pcm n) + 1 < dimword (:64)`. Our loop runs `prounds_t`, which freezes when `hdl_room`
fails (D25). `prounds` keeps going past that point, so the global bound fails there.
- Plan: truncate the schedule. `psk_upto N` is psk with no arrivals after round N.
  - Its handle-layer run agrees with psk's for rounds ≤ N.
  - `sched_wf2 (psk_upto N)` follows from the bound for n ≤ N. Empty arrivals are `step_ok2`, as in
    `psk_sched_wf2`'s NONE case.
  - Every claim is prefix-closed, so any finite raw prefix needs only N rounds.
  - The bound for n ≤ N comes from `hdl_room` along `prounds_t`, which equals `prounds` while there
    is room. This needs a lemma: pcm ≤ nxt + |acq|, with at most one pre-accept per round.
- Rejected: asking for `kv2_safe_upto`. It would reopen close-v2's and kv's proofs; truncation is
  one generic lemma, which echo can reuse.

**Pure trace transfer: kv_server_view_safe (new).** It is server-side, the mirror of
`kv_client_view_safe`. A raw prefix inside round n is paired with the v2 instant SUC n. For a paired
raw episode j and v2 episode e j:
- read: `krd (e j) (v2 (SUC n)) ≼ l0_read j raw`. Round lag: what the server consumes in round n,
  L1 fetched before round n. At boundaries, raw recv = server read ++ inb (pv_rel + Client).
- sent: `l0_sent j raw ≼ kwr (e j) (v2 (SUC n))`, by `l1pf_round_sent_upto`.
- unpaired raw episodes send nothing, and each v2 episode is paired at most once.

The raw side has read ahead, so it may hold complete requests the server has not yet consumed. The
order is extended with those at the end, episode by episode:
- no reply bytes were sent for them, so `wr ≼ replies` survives (replies of an extended order extend);
- `precedes` into them is harmless (they come last);
- `precedes` from them is impossible (no reply sent; needs `reply_bytes ≠ []`).

It also needs request-parse monotonicity: from brequests rs ++ rest ≼ brequests rs' ++ rest' with
both rests `no_full`, conclude rs ≼ rs'. HTTP's transfer is the per-episode special case.

**Episode key bridge** (superseded: identity, see above). e j = the v2 episode whose handle is the client `cl (pcm a) f` of raw
episode j. Expected: e j = SOME j whenever the fd reached the server, because acq is FIFO and
listening = MAP (cl cm) acq. Raw episodes dropped in acq (broken / EMFILE) have e j = NONE; they
sent nothing, by out_rel's acq clause.

**Programs.** `honestHttpKvL0Prog`: the D33 fdok prefix, listen, then `run_pf` on the translated
servers (spike/async-translate-kv: `gkv_server_spec`, asyncTranslateHttpB). Main / Sem / Stdio
follow echo, generalised over the server value and its spec rather than copied. The
`kept` invariant uses only `pact_ok`. Topology comes from the L1 events: listen only on lfd's port,
no connect.

**Then** re-derive echo through the same transfer (echo2_safe + kv_server_view_safe's per-episode
form) and delete honestEchoL0Out / Inv's output half.

### P4 gap 2 detail: the bound for rounds ≤ N (2026-10-17)
R1's `_upto` theorems need `SND (pcm n') + 1 < dimword (:64)` for every n' ≤ N,
including SUC n for a raw prefix that lies in round n.

L1 facts (honestL1PFModel):
- `wants_input lfd` requires acq = [], so pf_fetch adds at most one fd to acq, and only to an empty acq.
- Only `pdo Accept` removes from acq, and it increments nxt.
- So `pcm n = nxt_n + |acq_n|` with |acq_n| ≤ 1. This still needs proving: FConn is the only
  client-creating log entry, and it is only ever added to acq.

A round that runs under the current guard has `nxt + naccepts < 2^64`, so `pcm (SUC n) ≤ nxt + naccepts + 1 ≤ 2^64`.
That is 2 short of `pcm (SUC n) + 1 < 2^64`.

The exact guard is `hdl_room ps n ⇔ ps.b.nxt + n + 2 < dimword (:64)`.
- The two extra are the pending pre-accepted connection and R1's +1.
- It changes the CakeML loop (decision (A) / D25). Echo's proofs only use `nxt + naccepts < dimword`,
  and the new guard implies that.

Alternatives considered:
- Keep the current guard and treat the last 1–2 rounds separately. The bound would be loose and
  the extra case split is not worth it.
- Ask honest-ffi to weaken R1 to `pcm < dimword`. That reopens R1's proofs.

Status 2026-10-17: the coordinator put this on HOLD. D25's cut-off is user-approved, so a change goes to the user.
Analysis sent to the coordinator:
- The source of the +1 is v2's `arrival_ok2 (Connect2)`: reserved + listening + clients + 1 < 2^64. With one
  listener, v2 holds at most 2^64−2 clients.
- The current guard lets pcm (pre-accepted connections) reach 2^64.
- Rejected, proof-only routes:
  - psk_upto truncation: it acts after round N, not in the round that holds the prefix;
  - a bound lemma: the bound is false;
  - withholding the over-limit Connect2: the program may write to that connection, and the episode is then
    unpaired with sent ≠ [];
  - raising v2's capacity: it reopens socket-v2, close-v2, kv2_safe and R1.
- Smallest program change: `nxt + n + 2 < dimword`. With it, at most 2^64−3 connections are handed out
  (2^64−1 today).
