# The final review series: a proposal (for your decision; no branches changed)

*async-spike, 2026-10-16 (revised with the coordinator's status corrections: KV spec approved 75af705c3; kv_comp_safe green; honest FFI L1 green). It follows your presentation decision: the final series is organised by **concept**, with **no version numbers**, and it opens with the end-product theorems. The review-v2 series (#84–#113, plus layer 14) is kept as the snapshot this cut starts from. Today's headline statements, expanded with the definitions they use and the build evidence for each, are in `~/.cache/async-spike/HEADLINES.md`. Layer H below is that document, finalised.*

## 1. The shape: headlines first, then zoom levels

```
H   Headlines        every end-product theorem, stated in full, with its trusted
                     definitions inlined, a plain-English reading, its bites, and the
                     trust list.  No proofs.  (A reader can judge the target here.)
L0  Core             simple sockets (no close, no peers, the model's C).  The readable
                     spine: specs, the library, Level 2, the scheduler, isolation,
                     library liveness, protocols as instances, quiescence, it runs.
L1  Lifetimes        close and fd reuse; per-connection (episode) specs.
L2  Peers            connect / refusal / half-close; clients and proxies;
                     rely/guarantee specs; buffer closure; fd discipline.
L3  Real kernel      the honest FFI (L0 C, anchored on POSIX and the RFCs), the
                     verified wrappers (L1), and the refinement to the levels above.
```

**The rules:**
- **Each zoom level opens with ONE theorem** linking it to the level above. A reader can stop after any level and still know exactly what was proved.
- **L0 is complete on its own.** Every later level re-uses L0's proofs through its linking theorem, never by copying them.
- **Each level has its own trusted surface:** its world and its spec forms. The surface is short, and Layer H inlines it.

## 2. Layer H: Headlines

Each entry gives:
- the theorem, verbatim;
- every trusted definition it mentions, expanded alongside: the world, fairness and the spec predicates;
- a plain-English reading;
- its bites: broken servers it rejects, and non-vacuity;
- what it trusts;
- its evidence, meaning where it was built green.

There are no proofs and no intermediate lemmas.

| headline | level | status today |
|---|---|---|
| `echo_spec 3w echo_prog` | L0 | proved (review-v2/07) |
| `http_spec 3w demo_files http_prog` (today `http_spec_b … http_prog_pb`) | L0 | proved (review-v2/10) |
| `echo_quiet 3w echo_main`, `http_quiet 3w demo_files http_quiet_prog` | L0 | proved (review-v2/11) |
| `kv_spec 3w kv_prog` (linearizable, live) | L0 | **liveness proved; model-level safety `kv_comp_safe` green (c102c2aad, #111); CakeML side in progress** |
| `chat_spec_timely 4 3 4 3w chat_prog` (bounded latency, prompt accepts and reads) | L0 | proved (spike/chat-timely-fix, #106) |
| `echo_spec 3w echo_prog`, lifetimes form (today `echo_spec2 3w echo2_prog`) | L1 | proved (review-v2/13) |
| `http_spec`, lifetimes form | L1 | **at the CakeML step** (spec #105; close-v2's canonical translation chain 784e9f737 and the generic protocol model result exist) |
| echo, HTTP and KV under rely/guarantee; behind a proxy (`relay_safety`) | L2 | echo proved (`echo2_sym_equiv_thm`); HTTP and KV buffer closure proved; the HTTP and KV equivalences are **stated only** |
| the above on the real kernel | L3 | **in progress**: L0 C (#96), L0 world + conformance (#98), L1 core (#107) and L1's never-fails invariant (#110) are green; the R1/R2 refinement is in progress |

## 3. Naming: concepts instead of version numbers

The renames are a **presentation-level refactor, done on the final branches only**. The spikes and the review-v2 snapshot keep today's names, as the archive. HOL theory names are global and can't contain dots, so the level goes into the name or the directory.

| today | final | why |
|---|---|---|
| `EchoSpec`, `HttpSpecBodies`, `QuietSpec`, `HttpKvSpec`, `ChatSpec(Timely)` | `EchoSpec`, `HttpSpec`, `QuietSpec`, `KvSpec`, `ChatSpec` (timely clauses folded in) | "Bodies" is the only HTTP spec, so the name stays plain |
| `HttpSpec` (GET only), `HttpSpecHeaders` | `HttpVocab` (shared printers and vocabulary); the old statements are archived | they were stepping stones |
| `EchoSpec2`, `echo_spec2`, `echo_safe2` … | `EchoEpisodesSpec`, `echo_episodes_spec`, `echo_safe_ep` … | an episode is the concept |
| `ffiSpikeSocketFFI`, `ffiSpikeSocketFair`, `sched_wf` | `socketWorld`, `socketFair`, `fair` | "spike" is history |
| `socketV2FFI`, `socketV2Fair`, `server_world2`, `sched_wf2` | `lifetimeWorld`, `lifetimeFair`, `lifetime_world`, `lifetime_fair` | |
| `endpointWorld`, `endpointFair` | `peerWorld`, `peerFair` (or keep "endpoint") | your choice |
| honest-ffi L0 world (#98) | `kernelWorld` | |
| `asyncM3*`, `asyncM4*`, `asyncHL*`, `asyncOC*` | named by role: `loopPoll*`, `loopSelect*`, `loopHandles*`, `echo*`, `http*`, `level2*` | milestone prefixes mean nothing to a reader |
| `echo2_prog`, `http_prog_pb`, `http_q_prog`, `echo_l_prog` | `echo_close_prog`, `http_prog`, `http_quiet_prog`, `echo_blocking_prog` | |
| headline theories (`asyncM4EchoSpec`, `asyncProtoSemB`, `asyncOCQuietFinal`, `asyncHLEchoSpec2`) | `headline/echoHeadline`, `httpHeadline`, `quietHeadline`, `echoEpisodesHeadline` | one place for Layer H's theorems |

**How the rename is done:**
- one mechanical commit per level, on the final branches;
- each commit gets a rename table checked into `design/NAMES.md` (old ↔ new), so every spike reference stays traceable;
- the rename is rebuilt green before review.

**Alternative.** Keep the theory names and rename only the statement constants and directories. That is about half the work, but "M4" and "OC" stay visible in file names. I recommend the full rename.

## 4. The layers

### H. Headlines (1 layer)
`headline/` theories that only restate the end products in the specs' terms, plus `HEADLINES.md`, the reading document. No new proofs.

### L0. Core

| # | layer | content | feeds from |
|---|---|---|---|
| 0.1 | trusted surface | socket world and fairness; EchoSpec, HttpSpec (tokens, RFC character sets), QuietSpec, KvSpec, ChatSpec; bites; the RFC 9112 agreement | review-v2/01; #52 (KV); #66, #106 (chat) |
| 0.2 | the async model | monad laws, `both`, `choose` | review-v2/02 |
| 0.3 | recursion, Level 2, the scheduler | no busy-waiting | review-v2/03 |
| 0.4 | servers in the model | echo safety, closed-loop liveness; **isolation** (`server_with_isolates`, `sv_handler_view`) | review-v2/04, /09 |
| 0.5 | the library in CakeML | CF specs, Level 1 and Level 2 | review-v2/05, /08 (`cakeml/level2`) |
| 0.6 | sockets, divergence, loops | polling, blocking, and select on the declared interest | review-v2/06, /08, /11 (`loop/select-interest`) |
| 0.7 | the echo program | `echo_spec 3w echo_prog`; the blocking refinement | review-v2/07, /08 |
| 0.8 | liveness from the library | `server_with_live`, `server_v_live`, `server_v_live_ans` (stateful) | review-v2/09; #80, #95 |
| 0.9 | protocols as instances | `proto_ok`; HTTP (`http_spec`); KV (`kv_spec`, **once the CakeML safety step lands**) | review-v2/10; #95, #111 |
| 0.10 | quiescence | `echo_quiet`, `http_quiet`; stateful quiescence, `quiet_on` (design/37), if it lands | review-v2/11; spike/quiet-store |
| 0.11 | chat (a showcase instance) | `chat_spec_timely 4 3 4 3w chat_prog`; the GC hub | #72–#76, #83, #97, #106 |
| 0.12 | it runs | `socket_ffi.c` (the model's C), demos, CPU tables | review-v2/12 |

### L1. Lifetimes (close and fd reuse)

**The opening theorem** ties the lifetimes world to the core. Today the link is `hrun_sim` (programs/echo-v2): round by round, the handle loop has the core loop's history, so the core proofs are reused unchanged. **Missing:** a world-level statement to open the level with, of the form "a lifetimes program that never closes runs in the core world with the same trace". It is a small theorem to state and prove.

| # | layer | content | feeds from |
|---|---|---|---|
| 1.1 | trusted surface | `lifetimeWorld` and `lifetimeFair`; `EchoEpisodesSpec`; bites (`broken_leaks_across_reuse`, `v1_misses_leak`, `broken_never_closes`) | review-v2/13 |
| 1.2 | the handle loop and the echo program | `echo_episodes_spec 3w echo_close_prog` | review-v2/13 |
| 1.3 | HTTP with lifetimes | **at the CakeML step:** spec #105; the canonical translation chain (784e9f737) and the generic protocol model result exist | #105, close-v2 |

### L2. Peers (connect, refusal, half-close; clients and proxies)

**The opening theorem** links the lifetimes world: `v2_instance_thm`, the lifetimes world is an exact instance of the peer world, together with `echo2_sym_equiv_thm`, which shows the two echo specs agree. The core world links through fd discipline (option A): `not_v1_instance`, then `echo_prog_disciplined` / `http_prog_disciplined`. `v1_instance_disc` is **stated, not proved**.

| # | layer | content | feeds from |
|---|---|---|---|
| 2.1 | trusted surface | `peerWorld` (reactive env, backpressure `takes`, three-way connects), `peerFair`; rely/guarantee forms `rg_spec` | #67, #104 |
| 2.2 | the servers under rely/guarantee | echo (proved); the HTTP and KV equivalences (**stated only**) | #67 |
| 2.3 | fd discipline | `rounds_disciplined`; the instances for echo and echo-episodes; HTTP is to be redone for `http_prog` (one line) | #78 |
| 2.4 | clients, proxies, buffer closure | `relays`, `relay_safety`, `echo_relay_closed` / `http_relay_closed` / `kv_relay_closed`; `refusal_bite`; n-ary systems (∀ over wired fair runs, decided) | #79, #104 |

### L3. The real kernel

**The opening theorem** is design/36's refinement (R1–R4): the verified wrappers (L1 FFI) over the honest L0 FFI implement the **lifetimes** world. The lifetimes-world headlines would then transfer to the kernel: safety, and liveness in its *eventually* form, under R1/R4's antecedents. **Corrected after the transfer-claim review:**
- the L0 (core-world) headlines do not transfer (D5′);
- round bounds become *eventually*;
- quiescence needs a blocking R1 and a fix for the POLLHUP spin;
- chat stays open.

The per-headline table is in final/00's HEADLINES §8. **In progress:** R1 (safe, model level); R2–R4 are open.

| # | layer | content | feeds from |
|---|---|---|---|
| 3.1 | trusted surface | the L0 C (one syscall per call, a total errno table, a 13-byte header) and `kernelWorld`, anchored on POSIX; conformance tests | #96, #98 |
| 3.2 | the verified wrappers | L1 CakeML, whose spec is the lifetimes/core world | L1 core (#107) and the never-fails invariant (#110) are green |
| 3.3 | the refinement and the headlines on the kernel | R1–R4; the per-guarantee antecedents and 5 new bites (design/36 §7) | R1/R2 in progress; R3/R4 to do |
| 3.4 | it runs, honestly | the binaries on the L0 C; fd exhaustion fixed | **missing** |

## 5. What is still missing (before the final series can be built)

| piece | level | state | owner / where |
|---|---|---|---|
| KV safety, CakeML side: `kv_semantics_prog` → `kv_prog_safe`, then `kv_spec 3w kv_prog` (the model-level `kv_comp_safe` is green, c102c2aad, #111) | L0 | in progress | KV worker |
| stateful quiescence (`quiet_on`, `step_q'`) | L0 (optional) | in progress | cf-actions; spike/quiet-store (design/37) |
| the opening theorem for lifetimes (world-level simulation) | L1 | not stated | to do (small) |
| HTTP with lifetimes: the CakeML step against #105's spec | L1 | translation chain (784e9f737) and generic protocol model done | close-v2 |
| `v1_instance_disc`, and the HTTP and KV `sym_equiv`s | L2 | stated only | endpoint-world |
| `http_prog_disciplined` for the series' `http_prog` | L2 | to redo (one line) | fd-discipline |
| honest FFI: the R1–R4 refinement, then the headlines on the kernel | L3 | L0 C (#96), L0 world (#98), L1 core (#107) and never-fails (#110) green; R1/R2 in progress | honest-ffi; days at today's pace |
| the machine-code theorem (compiler correctness composed) | L0.12 | scripts written, not run (memory) | runnable/machine-code |

## 6. Fold effort (worker time at today's pace, builds through holslot)

| item | estimate |
|---|---|
| Layer H (headline restatements + HEADLINES.md finalised) | 0.5 day |
| L0 reorganisation from review-v2 (moving 04/09 isolation, 06/08/11 loops, adding chat and KV) | 1–1.5 days |
| the renames (§3), one commit per level, rebuilt green | 1 day |
| L1 (lifetimes) from review-v2/13, plus the opening theorem | 0.5 day + the theorem (≈0.5 day) |
| L2 (peers) from #67, #78, #79, #104: layout, ancestor INCLUDES, rebuild | 1–1.5 days |
| L3 trusted surface from #96, #98 | 0.5 day |
| docs: README, START-HERE, reading paths, PR bodies | 0.5 day |
| **total, folding what exists** | **≈ 5–6 worker-days**, about 2–3 days across 2–3 workers |
| missing pieces (§5), not included above | KV CakeML safety (in progress); HTTP lifetimes CakeML step (days); honest-FFI R1–R4 (days) |

**Recommendation.** Fold H, L0, L1 and L2 as soon as KV's CakeML safety lands. Add L3 when the honest-FFI refinement (R1–R4) is done. L3 leaves the model-level server proofs unchanged, but each server's CakeML main theorem is re-based on the L1 loop's translation chain, and only the lifetimes-world headlines transfer (see HEADLINES §8).

## 7. Reading paths

- **Fifteen minutes: Layer H only.** Read every end-product theorem with its definitions inlined, the bites, and the trust list. Stop here to judge the *target*.
- **One hour: H, then L0's trusted surface (0.1) and the key ideas.** The ideas are Level 2's declared interest (0.3), library liveness (0.8), protocols as instances (0.9) and select on the declared interest (0.10). Read the opening theorem of each later level, but not its contents.
- **Core in full** (about 6 h): H, then L0 in order. L0 is complete on its own.
- **Everything:** H → L0 → L1 → L2 → L3. Each level starts with its linking theorem, then its own trusted surface, then its proofs.

## 8. Decisions this asks of you

1. The zoom-level structure and the order **H → L0 → L1 → L2 → L3** (above).
2. The naming scheme: the full rename (recommended), or constants and directories only.
3. Whether chat is in L0 as a reviewed instance (proposed), or stays an appendix.
4. "peer" or "endpoint" for the L2 world.
5. When to build: as soon as KV's CakeML safety lands (proposed), with L3 added when R1–R4 are done; or wait for everything.

## 9. Decisions (user, 2026-10-16, via the coordinator): APPROVED

1. **Structure:** H → L0 → L1 → L2 → L3.
2. **Naming:** the FULL rename, with `design/NAMES.md` recording old ↔ new.
3. **Chat:** an APPENDIX for now. It is promoted to an L0 instance after its revised spec has had a clean independent review.
4. **The L2 world:** "peer" (`peerWorld`, `peerFair`).
5. **When to build:** H–L2 as soon as KV's CakeML safety lands (`kv_spec 3w kv_prog`); L3 when the honest-FFI refinement R1–R4 is done.

**Allowed now:** preparatory work that doesn't depend on KV, on NEW branches `final/NN-…`:
- Layer H's restatements;
- the L0 reorganisation;
- the rename tooling and `NAMES.md`.

**Held:** the build of L0's KV part, until `kv_spec` lands.
