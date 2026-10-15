# 34: Liveness carried by the library: audit and a generic liveness principle

Status: **approved by the user; implementation in progress** on
`spike/sw-live` (theory `asyncServerWithLive` in `async/library-liveness/`).
The library theorem is named `server_with_live`: `sw_live` is already
taken by async-spike's asyncSWLiveServer (PR #56). No existing statement
changes. Branch
`spike/library-liveness`, from `spike/http-bodies`.

User direction: proofs should be carried by the Async library's generic
theorems, so that each new networked program costs little bespoke proof.
Safety is already like that. Liveness is not yet. This note audits where
the per-server liveness work went (§1), and proposes one library-level
principle that turns it into a per-handler obligation (§2). It then places
that principle relative to option C (design/33) and modular parsing
(design/32) (§3), costs it (§4), and lists the library features that real
async programs need next (§5).

**Proposed metric**, per program: *library share* = 1 − (bespoke proof
lines) / (all proof lines the program's headline depends on, excluding the
trusted spec). Today it is roughly 0.75 for HTTP liveness at the socket
level (§1.4). The goal is ≥ 0.9 for a new parse–respond protocol, and the
handler's progress measure should be the only bespoke liveness proof.

---

## 1. Audit

Classification:
- **(i)** already generic;
- **(ii)** generic in disguise: liftable, with the parameter or hypothesis it needs;
- **(iii)** genuinely server-specific.

Line counts are whole files.

### 1.1 Echo (spike/m4-liveness, ~1,460 lines, plus the model's asyncProgress/asyncLiveness)

| file / lemmas | class | notes |
|---|---|---|
| asyncM4Sched (179): `grounds_arrivals`, `sent_upto_SUC`, `grounds_sched_wf`, `grounds_step_ok` | (i) | in `ifds m s0` |
| asyncM4Account (134): `acct`, `grounds_acct` | (i) | sent = read ++ incoming, for any m |
| asyncM4LiveWorld (173): `round_conn_s`, `grounds_eof`, `quiet_rounds_s` | (i) | |
| asyncM4Queue (238): `queued`, `grounds_known`, `rounds_queued` | (i) | listener-shaped hypotheses only |
| asyncM4LiveProg (104): `prompt_ghist`, `ready_EL_ghist`, `interest_accepted` | (i) | |
| asyncM4ReadSoon: `gperf_prefix`, `wacc_prefix`, `sfr_Eof` | (i) | |
| asyncM4ReadSoon: `accepted_TS`, `TS_eof` | (ii), **lifted** | `TSg_accepted`, `TSg_eof` (asyncSWSock), hypothesis `uses_ok` |
| asyncM4ReadSoon: `nreads_step` | (ii) | needs only `wf m` |
| asyncM4ReadSoon: `read_soon_s` | (iii), but its shape is generic | echo's per-handler progress via `handler_progress` |
| asyncM4AcceptSoon: `naccepts_step`, `accept_soon_s`, `queue_progress`, `conn_accepted` | (ii), **lifted** | `sw_*` twins in asyncSWSock, hypotheses `hok hf ∧ uses_ok` |
| asyncM4Drain: `sock_acts_read_nonempty`, prefix lemmas | (i) | |
| asyncM4Drain: `drain_step`, `drain`, `accepted_live` | (ii) | "unread data ⇒ read within k rounds" as a hypothesis; then echo's "written = read" |
| asyncM4EchoLive: `echo_comp_live`, `echo_live_rounds` | (ii) | the same skeleton as `http_live_h_rounds` (§2.4) |
| asyncProgress (1173): `prompt_*`, `nreads`, `count_both`, `readable_*` | (i) | |
| asyncProgress: `server_handler_view`, `server_accept_progress`, `server_*` | (ii), **lifted** | `sw_handler_view`, `sw_accept_progress` (asyncSWProgress) |
| asyncProgress: `handler_*`, `after_read_*`, `handler_progress` | (iii) | echo's handler; this *is* its progress measure |
| asyncLiveness (992): world and closed-loop lemmas in m | (i) | |
| asyncLiveness: `read_soon`, `echo_next`, `closed_loop_echo_accepted`, `closed_loop_liveness` | (ii)/(iii) | everything else has `sw_*` twins (asyncSWClosedLoop, asyncSWQueue) |

### 1.2 HTTP `_h` (spike/http-liveness, `async/http-liveness-h`, ~1,790 lines) and `_b` (spike/http-bodies, a renamed copy)

| file / lemmas | class | notes |
|---|---|---|
| asyncSWProgress (652), asyncSWClosedLoop (207), asyncSWQueue (298), asyncSWSock (218) | (i) | parametric in `hf` with `hok hf` (wf, settled, own fd) and `uses_ok` |
| asyncHttpLiveH: `sent_split` | (i) | |
| asyncHttpLiveH: `http_h_view` | **(ii)** | It is `sw_handler_view` + `gen_trans_split` + `gen_rounds_bytes` for any `server_with hf`. Only the instance `hf = λfd. hcomp files fd (HA "")` is specific. |
| asyncHttpLiveH: the four environment facts inside `http_accepted_live_h` (readiness, read progress, EOF, comparability) | **(ii)** | They follow from `ready_EL_ghist`, `interest_accepted`, `TSg_read_none`, `sock_acts_read_nonempty`, `TSg_eof`, `grounds_eof` and `grounds_acct`. The HTTP machine enters only through `hmachine_reading`/`hmachine_eof` ("state HB ⇒ an unanswered read in the transcript", "state HD ⇒ a read that returned EOF"). Stated on the *transcript* instead of the machine state, they are generic (§2.2). |
| asyncHttpLiveH: `http_accepted_live_h` tail, `http_live_h_rounds` | **(ii)** | Generic given a per-handler theorem of `hmachine_live_p`'s shape: `sw_conn_accepted` → view → handler liveness → bytes. |
| asyncHttpMachineH (414), asyncHttpDrainH (563): `hmachine_inv`, `hdrain`, `drain_after`, `hmachine_live_read`, `hmachine_live_p` | (ii) for parse–respond protocols, (iii) otherwise | design/32's `proto_ok P` + `resp` lifts them (P1–P4) |
| asyncHttpParseHExt (183), ParseBExt (148) | (iii) | discharge P3 for each parser |
| `hok_http_h`, `uses_ok_http_h`, `asyncHttpSpecH` (32) | (iii), small | instance glue |

`_b` duplicates `_h` almost exactly: design/32 counts 64 differing lines out of 2,249, once the renaming is applied.

### 1.3 KV (local spike/http-kv-impl, untracked; no liveness yet)

- `with_store δ s0 m` (asyncWithStore, 586 lines; asyncWithStoreStep, 198) is a generic store-threading effect handler:
  - (i) `new_actions_with_store`, `trans_with_store`, `relabel_with_store`, `prompt_with_store`;
  - (ii) the "a query is answered in the next round" fact, which liveness will need (§2.5).
- `server_with_k` (358) is `server_with` with Sock/Kv tags; its `_isolates`/`_uses_accepted` are (i).
- The kv handler is the `_b` machine plus a state between Complete and the write (design/33 §4: HA → HK → HB). Its progress measure is (iii) for KV, or (ii) under design/32 §2.3's answering computation `ans`.
- Planned liveness (design/30 §4): "bound about 3K+2, rest of the chain unchanged". With §2 below, "the rest of the chain" becomes a library theorem instead of a third copy of asyncHttpLiveH.

### 1.4 Summary

For socket-level HTTP liveness, about 1,250 of the ~1,790 lines in
`http-liveness-h` are, or could be, library code:
- asyncSWSock (218), the asyncSW* model lemmas (in `async/http-liveness`) and the m4-liveness generic theories are already library code;
- `http_h_view` and the environment derivation in asyncHttpLiveH (~300) are generic in disguise;
- the machine and drain (~980) are protocol-generic via design/32.

What is genuinely HTTP-specific is the parser's P1–P4 discharge
(~180 lines per parser) and a few instance lemmas. For echo, the bespoke
part is `handler_progress` and its helpers (~350 lines in asyncProgress),
`read_soon_s` and the drain/assembly (~400).

---

## 2. A generic liveness principle

### 2.1 Shape

> A handler that owns its fd (`hok`), and that, *in every environment
> satisfying four generic facts about its own fd*, eventually writes the
> output owed for data D, is live under `server_with`. Under the event
> loop in any fair socket world, the output owed for every prefix D of
> what a client sent is eventually written to that client.

Each server then proves only the per-handler statement (a progress
measure on its own history). Everything from the handler's history down
to the socket trace is one library theorem, `server_with_live`.

### 2.2 The environment of a handler (generic)

For a handler `h = hf fd` on its history g (from `sw_handler_view`), write
`R j = CONCAT (read fd (trans h (TAKE j g)))` (what it has read after j
snapshots), `W j = written fd (trans h (TAKE j g))`, `L = LENGTH g`, and
let j0 be the round from which D has been sent.

```
henv fd h g j0 D ⇔
  (* comparable: what is read and D are prefixes of what was sent *)
  (∀j. j0 ≤ j ∧ j ≤ L ⇒ R j ≼ D ∨ D ≼ R j) ∧
  (* not reported readable: nothing is unread *)
  (∀j. j0 ≤ j ∧ j < L ∧ Readable fd ∉ (EL j g).ready ⇒ D ≼ R (SUC j)) ∧
  (* an outstanding read, with D not all read, reads something *)
  (∀j. j0 ≤ j ∧ j < L ∧ MEM (Read fd, NONE) (trans h (TAKE j g)) ∧ ¬(D ≼ R j) ⇒
       D ≼ R (SUC j) ∨ LENGTH (R j) < LENGTH (R (SUC j))) ∧
  (* end-of-file comes after all the data *)
  (∀j. j0 ≤ j ∧ j ≤ L ∧ MEM (Read fd, SOME Eof) (trans h (TAKE j g)) ⇒ D ≼ R j)
```

These are exactly the four facts that `http_accepted_live_h` derives from
the socket world, restated on the transcript. The HTTP machine's states
appear only in `hmachine_reading`/`hmachine_eof`, which become the
instance's bridge (§2.6).

### 2.3 The per-handler obligation

```
handler_live hf out B ⇔
  ∀fd g j0 D.
    prompt (hf fd) g ∧ henv fd (hf fd) g j0 D ∧ j0 + B D ≤ LENGTH g ⇒
    ∃j. j ≤ LENGTH g ∧ out D ≼ written fd (trans (hf fd) (TAKE j g))
```

- `out : string → string list` is what is owed for data D:
  - HTTP: `responses_to_h files`;
  - echo: `λD. [D]`, up to splitting, or stated on `FLAT`;
  - KV: the answered responses (§2.5).
- `B : string → num` is any round bound. Only its existence matters for
  the spec's "eventually"; it serves to pick a long enough history.
- **This is the only liveness proof a server owes.** For HTTP it is
  `hmachine_live_p`, restated through the bridge (§2.6).

### 2.4 The library theorem (socket level)

```
(* MAIN (proposed): handler liveness ⇒ the server's socket trace is live *)
Theorem server_with_live:
  hok hf ∧ handler_live hf out B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ∧
  bytes D ≼ sent_upto c n s0 ∧ (D ≠ [] ∨ out D = []) ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (server_with hf lfdn)) s0) N))
```

`uses_ok` comes for free from `hok` (`server_with_uses_accepted`). The proof
is `http_live_h_rounds`'s, with the handler abstracted:
1. `sent_upto ≠ []` ⇒ c is a connection;
2. `sw_conn_accepted` gives the round N0 where c is handed out;
3. the view at round n + N0 (`sw_handler_view` + `gen_trans_split` + `gen_rounds_bytes`, the lifted `http_h_view`);
4. `sw_henv`: the four facts (the lifted environment derivation of `http_accepted_live_h`);
5. `handler_live`;
6. bytes and `rounds_LPREFIX`.

Spec-shaped corollaries, one line each:
- HTTP: `http_live_h_rounds = server_with_live` with `out = responses_to_h files`, using `parse_all_h_printed`;
- echo: `echo_live_rounds = server_with_live` with `out = λD. [D]`.

**Composition with the event loop.** `server_with_live` is stated on `grounds_events
(EI lfdn)`, the dynamic-interest loop `run_i`. `run_i_spec` plus the
existing `*_semantics_prog` lemmas give the program trace, as now. For
another loop (the blocking/select loop of design/31, option C's declared
interest), the only loop-dependent input is the readiness fact: "Readable
fd ∉ ready ⇒ nothing unread" needs fd to be in the loop's interest
(`interest_accepted`, or `sel_covers`). So `server_with_live` should take the loop
as a parameter, with the hypothesis `∀n c. MEM c (wacc …) ⇒ MEM c (ifds
(ghist …))`. That makes it hold for any interest function covering the
accepted fds.

### 2.5 Composition with `with_store` (KV)

`kv_server = with_store δ s0 (server_with_k hf lfd)`.
- `prompt_with_store` and `relabel_with_store` move the view to the inner computation on `inner_hist`.
- `trans_with_store` gives `untag`.

So `server_with_live` applies to `server_with_k` once two generic lemmas exist:
- **`with_store_answers`**: every Kv query emitted in round j is answered in the results of snapshot j+1 of `inner_hist`. This is "the effect is handled promptly", (ii), and it is proved from `inner_hist`'s definition.
- **`server_with_live_k`**: `server_with_live` for `server_with_k`, by the same proof over the tagged transcript.

The KV handler's `handler_live` then has one more state (HK, waiting one
round for the store). Its bound becomes about 3K+2, as design/30 predicts.
The obligation stays per-handler.

### 2.6 What each existing server would prove (the instance)

| server | `out` | per-handler proof | bridge |
|---|---|---|---|
| HTTP `_h` / `_b` | `responses_to_h/_b files` | `hmachine_live_p` (exists) | `hmachine_reading`: HB ⇒ an unanswered read; HD with incomplete ⇒ an EOF read; HA ⇒ R (SUC j) = R j (exists). Restating `henv` into the machine's hypotheses is ~80 lines. |
| echo | `λD. [D]` | new, from `handler_progress` (readable 3 rounds ⇒ nreads grows) and `handler_echoes` (written = read) | ~150 lines |
| KV | answered responses | `hmachine_live_p` + the HK state | `with_store_answers` |

---

## 3. Overlaps, and who owns what

**design/32, modular parsing (cf-actions).**
- Its generic pipeline (`asyncProtoMachine/Drain/Live`) is the natural owner of a *protocol-generic* `handler_live`:
  ```
  proto_handler_live: proto_ok P ⇒ handler_live (λfd. proto_handler P resp (fd, "")) (proto_responses P resp) (B_P)
  ```
- Its asyncProtoLive should then be a two-line instance of `server_with_live`, rather than a re-proof of asyncHttpLiveH.
- KV's answering computation `ans` (32 §2.3) fits as long as `ans` finishes in bounded rounds without waiting, which is exactly what `handler_live` needs.
- **Ownership:** cf-actions owns `proto_*` and `proto_handler_live`. The liveness worker (me) owns `henv`, `handler_live`, `sw_henv` and `server_with_live`.

**design/33, option C (async-spike).**
- Its quiescence argument needs a progress measure that decreases within k rounds. That is the same per-handler fact. Under option C the loop selects on declared interest, so the readiness fact in `henv` comes from `sel_covers` instead of `interest_accepted`; `server_with_live`'s interest parameter (§2.4) covers it.
- Its hardest lemma, progress ⇒ stability, needs the *converse* direction: what makes a handler act at all. That is the cause-of-actions lemma (`handler_cause`, in an untracked echo file). The library generalisation:
  ```
  hok_cause: new actions at round j ⇒ Readable fd ∈ ready_j ∨ a response arrived at j
  ```
  It holds for handlers built only from `readable`, `emit`, `bind`, `both`. It belongs to option C, not to `server_with_live`, which does not need it.
- **Ownership:** async-spike owns Level 2, declared interest, quiescence and `hok_cause`. It should *consume* `handler_live` as its measure, and not define a second one.

**Avoiding duplication.** The four `henv` facts are stated once, in the
library (here). Design/32 proves `handler_live` for protocols, and
design/33 proves stability from `handler_live` plus `hok_cause`. Nobody
re-derives the socket environment again.

---

## 4. Cost, savings and risks

**Additive implementation**, with no existing statement changed:

| piece | lines (est.) | from |
|---|---|---|
| `henv`, `handler_live`, `sw_henv` (environment derivation, generic) | 300 | lift from asyncHttpLiveH |
| `server_with_live` (+ interest parameter) | 200 | lift `http_accepted_live_h`'s tail + `http_live_h_rounds` |
| HTTP `_h` re-derived: bridge + `http_live_h_rounds_via_lib` | 100 | |
| HTTP `_b`: the same, or free via design/32 | 100 / 0 | |
| echo: `handler_live` for `handler` + `echo_live_rounds_via_lib` | 200 | |
| KV: `with_store_answers`, `server_with_live_k`, kv `handler_live` | 500 | new (instead of ~900 for a third asyncHttpLiveH-style copy) |
| **total** | **~1,400** | 3–4 worker-days |

**Savings per future program.**
- Today a new server's socket-level liveness costs ~400 lines (an asyncHttpLiveH copy), plus its handler measure.
- With `server_with_live` the socket part is 0, and the program proves `handler_live` only.
- With design/32 a parse–respond protocol's `handler_live` is also free: ~20 lines of `proto_ok` + a ~30-line instance.
- So the liveness share rises from ~0.75 to ~0.95 for protocols, and to ~0.8 for handlers with their own state machine (KV-like).

**Risks.**
1. **`henv` may be too weak for some handlers.** It talks about one fd. Handlers that wait on timers, other fds or each other (§5) need an extended environment (one per event kind). It should be designed so that conjuncts can be added, not changed.
2. **Echo's measure** is stated as "readable 3 rounds ⇒ nreads grows". Turning it into `handler_live` needs the unread-length induction of `hmachine_live_p`. That is a re-proof, not a restatement, so the 200 lines may be optimistic.
3. **The interest parameter.** Loops whose interest does not cover every accepted fd (the live-fd select loop drops closed fds) need care: the readiness fact is only needed while the handler waits.
4. **Ownership drift.** If design/32 or 33 start before `server_with_live` exists, each may re-derive the environment. Mitigation: land `henv`/`server_with_live` first. It is small and only lifts existing proofs.

---

## 5. Library features for the ambitious line

For each feature: how it fits the model (computations over a history of
snapshots, actions answered in the next snapshot), and the generic theorem
it needs.

**Connect (outgoing connections).**
- New action `Connect addr` with response `Connected fd | Refused`.
- The world gains client-initiated connections: an arrival `Accepted c` resolves a pending connect.
- A combinator `with_conn addr h` (connect, then run `h fd`, like `server_with`'s after-accept).
- Theorems:
  - `with_conn_isolates` (the analogue of `server_with_isolates`);
  - liveness: a connect is resolved within k rounds under a fairness assumption on the peer (a new world assumption, stated in the spec's world, not proved).
- `henv` gains "connected ⇒ the fd behaves as an accepted one".

**Time: a timer event and `with_timeout`.**
- Snapshots already carry `now`. A timer is `wait (λs. if s.now ≥ t then SOME () else NONE)`.
- `with_timeout d m = choose m (sleep d)` uses the existing `choose` (asyncChoose).
- **Cancellation question.** The model's `choose` already *keeps* the loser, as a suspended computation in the result. It also waits for responses to requests the losing left side has in flight. So the library choice is "keep". A `with_timeout` that *drops* the loser simply ignores the suspended value, and its in-flight requests are still answered (no orphan responses). This is the safe default, and it should be documented as such.
- Theorems:
  - `with_timeout_finishes`: in any world where time advances (a fairness assumption on the clock), it finishes within d plus one round;
  - `with_timeout_left`: if m finishes within d, the result is `INL`.
- `henv` gains "time advances".

**Backpressure-aware writes.**
- The model's writes are full (the C loops `send`). A faithful model has `Write fd d` return the count sent, plus a `Writable fd` event.
- The library combinator `write_all fd d` loops until done.
- Theorems:
  - `write_all_written`: the transcript writes exactly d;
  - `write_all_live`: done within k rounds if the peer reads.

  The second needs a new spec-level assumption that clients read. That is honest, but it changes what "live" means for the server.
- Impact: every server's `out D ≼ written` stays the same; only `henv` grows.

**Communication between computations (Pipe / Ivar / Mvar).**
- An internal channel is an effect handled inside the program: emit `Put v` and `Take` against a shared cell.
- `with_store` is already the pattern: a pure effect handler, answering in the next round. A channel is a `with_store` whose state is a queue, with `Take` blocking until non-empty.
- **New combinator** `with_chan`, plus a rely–guarantee rule for `both`. Each side's guarantee bounds its channel traffic, the other side relies on it, and liveness of a `Take` relies on the peer's progress:
  ```
  both_rg: m1 guarantees G1 ∧ relies R1, m2 guarantees G2 ∧ relies R2, G1 ⇒ R2, G2 ⇒ R1
    ⇒ both m1 m2 satisfies the combined spec
  ```
  It generalises `server_with_isolates`, where each handler's guarantee is "only my fd" and the rely is trivial.
- Liveness of a pipe: a `Take` is answered within k rounds once the peer's measure shows a `Put`. This is a cross-handler measure, the main new research piece of the ambitious line.

---

## 6. Decisions for the user

1. Land `henv`/`handler_live`/`server_with_live` (§2, ~500 lines, lifting existing proofs) before design/32 phases 2–4 and option C, so that both consume it.
2. Who owns what (§3): cf-actions owns protocol-generic `handler_live`; async-spike owns option C and `hok_cause`; the liveness worker owns `server_with_live`.
3. `with_timeout` keeps the loser (the existing `choose` semantics).
4. Backpressure needs a spec-level "clients read" assumption, if and when it is modelled.
