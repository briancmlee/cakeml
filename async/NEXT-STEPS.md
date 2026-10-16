# Next steps: statements for review (not part of the series)

*This is the review-v2 "next steps" PR. It stacks on `review-v2/14-docs` and adds this one file, with no theory files. Each item names the spike branch, the commit and the PR where its proofs live. The theorem text is copied verbatim.*

**Evidence key:**
- **built** means a green build was checked here (`Holmake -n` up to date, with no cheat tag in the `.dat`);
- **PR: green** means the PR's author states a green build;
- **stated** means a proposition is defined, and the claim is not yet proved.

No file of any branch below contains a `cheat`, `mk_thm` or `new_axiom`.

## 1. The endpoint world: clients, proxies, backpressure (#67, #104)

`spike/endpoint-world` @ `722f909b1` (#67), and `spike/refused-connect` @ `63ff73507` (#104). The design note is `async/design/35-endpoint-world.md`.

**What it is.** A POSIX-shaped socket world (`endpointWorld`, TRUSTED, with `endpointFair`):
- channels come from accept *or* connect;
- any fd can read, write, send part of its data, poll for writability, shut down and close;
- fds are reused;
- the environment is reactive: `env` sees the calls so far;
- backpressure is a world parameter (`takes`);
- connects are three-way (`Connecting | Up | Refused`, then `Failed`) and use design/36's 13-byte result header (#104).

Each server gets one rely/guarantee spec over all worlds:

```
rg_spec cls guar (prog : dec list) ⇔
  ∀w. cls w ∧ ep_rely w ⇒
      ∃io. semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io) ∧ guar w io

ep_rely w ⇔ alloc_ok w.alloc ∧ takes_ok w.takes ∧ ep_sched_ok w
takes_ok t ⇔ ∀j b n. t j b n ≤ n ∧ (b = 0 ∧ 0 < n ⇒ 0 < t j 0 n)
```

**Proved** (PR: green; #104 states "endpoint-world 16/16, fd-discipline 4/4"):

```
Theorem v2_instance_thm:  v2_instance        (* the version-2 world is an exact instance *)
Theorem not_v1_instance:  ¬v1_instance       (* version 1 is not: a v1 program may touch an fd before accepting it *)

Theorem echo2_sym_equiv_thm:
  ∀lfd a prog.
    (rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       ep_echo2_guar prog ⇒ echo_spec2 lfd prog) ∧
    (echo_spec2 lfd prog ⇒
     rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat lfd a w)
       ep_echo2_guar prog)

Theorem never_polls_bite:
  (∀evs. LPREFIX (fromList evs) io ⇒ (ep_replay w evs).clock = w.clock) ⇒
  ¬ep_echo_guar w io ∧ ¬ep_echo2_guar w io ∧ ¬ep_http_guar files w io ∧ ¬ep_kv_guar w io

Theorem refusal_bite:  ¬client_guar a r w (fromList (refused_trace a f ++ evs))
```

**Stated, not proved yet:**
- `echo_sym_equiv`, `http_sym_equiv`, `kv_sym_equiv`;
- `starve_bite`, `input_live_bite`;
- `projection`, `client_server_compose`;
- `v1_instance_disc`.

**Decisions** (design/35 §6–§7, as recorded on the #104 tip):
- §6.1, acceptance `takes` per call: accepted.
- §6.2, connect outcomes: changed to three-way (#104).
- §6.3 (full write) and §6.4 (writability as a separate call): superseded by design/36.
- v1: **option A**. The v1 claims are restricted to fd-disciplined programs (section 2 below).
- §7 (a): the per-instant `relays` replaces `buf_rel` (section 3 below).
- §7 (b): **∀** over every wired, fair system run, with a separate existence lemma for each concrete system.

## 2. fd discipline: our servers touch only accepted fds (#78)

`spike/fd-discipline` @ `16ffffdcf` (#78; PR: green).

```
fd_disciplined lfd io ⇔
  always (λevs. ∀pre ev. evs = pre ++ [ev] ⇒
                  EVERY (λf. f = lfd ∨ MEM f (open_now (REVERSE pre))) (event_fds ev)) io

v1_disciplined lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            fd_disciplined lfd io

Theorem echo_prog_disciplined:   v1_disciplined 3w echo_prog
Theorem http_prog_b_disciplined: v1_disciplined 3w http_prog_b
Theorem echo2_prog_disciplined:  v2_disciplined 3w echo2_prog
Theorem rounds_disciplined:      (* the generic form, for any server with uses_ok *)
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fd_disciplined (n2w lfdn) (LFLATTEN (LGENLIST (λi. fromList (RE lfdn m s0 i)) NONE))
```

**Plain reading.** Version 1's idealisation lets a program use an fd before accepting it; our servers never do. So restricting the v1 equivalences to disciplined programs (option A) costs nothing for them.

**Open:**
- `http_prog_b` is the retired copy. The series' `http_prog_pb` needs the same one-line instance of `rounds_disciplined`.
- `kv_prog` waits for KV safety.

## 3. Buffer closure: what a relay preserves (#79)

`spike/buffer-closure` @ `0f332e216` (#79; PR: green).

```
relays (r_in, w_in) (r_out, w_out) ⇔ r_in ≼ r_out ∧ w_out ≼ w_in
relay_closed P ⇔ ∀r w r' w'. P r w ∧ r ≼ r' ∧ w' ≼ w ⇒ P r' w'

Theorem relay_safety:
  relay_closed P ∧ (∀t. P (FST (inside t)) (SND (inside t))) ∧
  (∀t. relays (inside t) (outside t)) ⇒
  ∀t. P (FST (outside t)) (SND (outside t))

Theorem echo_relay_closed:  relay_closed (λr w. w ≼ r)
Theorem http_relay_closed:  relay_closed (http_conn_safe files)
Theorem kv_relay_closed:    relay_run ins outs io io' ∧ kv_safe io ⇒ kv_safe io'
```

**Plain reading.** A buffering proxy in front of a server reads at least what the server read, and writes at most what the server wrote, at every instant (`relays`). Each spec's safety survives that:
- echo and HTTP are closed under it, per connection;
- KV is closed under it along a whole relay run, linearizability included.

An earlier draft related the prefixes independently, which lost the common instant; `relays` fixes that.

## 4. The KV server: liveness proved, safety in progress (#52, #73, #80, #95)

**The spec** is `spec/HttpKvSpec` (#52; APPROVED 2026-10-16, 75af705c3): linearizable safety (`kv_safe`), and liveness (`kv_live`). It is in `async/spec/HttpKvSpecScript.sml` on `spike/http-kv` and `spike/kv-live`.

**The library pieces** (all proved):
- `with_store_v_live` and `wrap_ok_with_store`: `spike/kv-wrap` @ `095da8900` (#73);
- `server_v_live_ans` and `proto_handler_live_va`: `spike/proto-kv` @ `239a955d0` (#80);
- `server_v_live_p` and `kv_live_from_goal`: `spike/kv-live` @ `5a72181db` (#95).

```
Theorem server_v_live_ans:     (* stateful servers: output may depend on the store's answers *)
  wrap_ok V Wr inner ∧ vocab_ok V ∧ hokv V hf ∧ handler_live_va V hf out B ∧
  (∀ans. FLAT (out "" ans) = "") ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D (conn_answers V Wr inner hf lfdn (EI lfdn) s0 N c))) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0) (SUC N)))
```

**KV liveness**, built here at `5a72181db` (up to date, no cheat tag):

```
Theorem kv_live_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ⇒
  kv_live s0 (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
                (srelabel (kv_server lfdn)) s0 i)) NONE))
```

**Not proved:**
- KV **safety, CakeML side**. The model-level order construction `kv_comp_safe` is green (c102c2aad, draft #111). What remains is the CakeML side: `kv_semantics_prog` → `kv_prog_safe`.
- The combined `kv_spec 3w kv_prog`.
- **Stateful quiescence** (design/37, `spike/quiet-store`, cf-actions): an additive loop variant with a "now" interest, for `with_store2`.

## 5. The honest FFI (#94, #96, #98)

design/36 (#94) audits the trusted C. It finds 11 behaviours that differ from the model, including fd exhaustion: the v1 echo server stops serving after about 250 clients on macOS. It proposes:
- **L0**, a minimal honest FFI: one syscall per call, a total errno table, and a 13-byte result header (#96: the C, a harness and platform probes; #98: the L0 world model and conformance tests);
- **L1**, verified CakeML wrappers whose spec is today's v1/v2 socket worlds, so no server proof changes;
- refinement statements R1–R4. The present headline theorems become corollaries.

Since then:
- the L1 core (#107) and L1's never-fails invariant (#110) are green;
- the R1/R2 refinement is in progress.

The user's decisions D1–D8 are recorded in design/36 §9.

## Appendix: the chat server (linked, not reviewed)

The proofs are in #66 (spec), #72, #75, #76 and #83:

```
chat_prog_spec : chat_spec 3w chat_prog      (spike/chat-live 7eb3da6b1; PR: green; built at 927009604)
```

Bounded latency, from #97 and #106 (SPEC CHANGE, approved):

```
chat_prog_timely : chat_spec_timely 4 3 4 3w chat_prog    (spike/chat-timely-fix b923a7fbe; PR: green)
gc_prog_timely   : chat_spec_timely 4 3 4 3w chat_prog_gc (bounded memory)
```

The specs are `async/spec/ChatSpecScript.sml` and `ChatSpecTimelyScript.sml` on those branches.
