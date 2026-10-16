# Review series v2: proposal (for decision; nothing changed yet)

*async-spike, 2026-10-16 night. The current series is 12 stacked PRs, #34–#44 and #68. This note proposes how it should look once tonight's work is folded.*

## 1. What changes, and why

The series still proves each HTTP server with its own copied pipeline. Since it was cut, three generic results have replaced most of those copies:
- **Library liveness** (#59 → #71, #80): `server_with_live` / `server_v_live` prove a server's liveness once, from a per-handler obligation.
- **The generic protocol pipeline** (#58 → #74): `proto_handler` / `proto_server` / `sproto_server_spec`, with the bodies headline re-proved on it. `spec-rfc` adds an agreement with RFC 9112 framing.
- **Quiescence**, in three parts:
  - QuietSpec (#57);
  - `echo_l_quiet` (#77), for the shipped blocking echo;
  - option C (#81, #82, `spike/option-c-int`): select on the declared interest; `http_q_quiet_b` holds, given PROTO_STABLE.

The proposal: keep layers 1–8 as they are (spec, model, library, echo); rebuild HTTP on the generic pipeline; and add quiescence as a new layer.

## 2. Proposed layers

| # | layer | content | change from v1 |
|---|---|---|---|
| 1 | trusted surface | specs: Echo, HttpSpecBodies (+tchar, H-CHARS?), QuietSpec; spec-rfc as a checked agreement | **adds** QuietSpec, the spec changes, and spec-rfc |
| 2–4 | model, recursion/Level 2, echo in the model | as now | none |
| 5 | library in CakeML | as now, plus the Level 2 library completed (`both2`, `map2`, depth recursion, EVSET) | **adds** #81 |
| 6–7 | sockets, loop, echo program | as now | none |
| 8 | blocking refinement | #46 live-list echo, `brun_two_outcomes` | none (#56 is **not** folded; superseded) |
| 9 | **liveness from the library** | `server_with_live`, `server_v` / `server_v_live`; echo and HTTP liveness re-derived through it | **new**; replaces the per-server liveness in 7 and 9 as the primary proof |
| 10 | **HTTP as a protocol instance** | generic `proto_*` (safety, liveness, CakeML); bodies instance `http_prog_pb_spec`; RFC agreement | **replaces** the copied HTTP pipelines (headers, strict, bodies) |
| 11 | **quiescence and option C** | QuietSpec bites; `echo_l_quiet`; Level 2 protocol server (#82); `run_q`; `http_q_quiet_b` | **new** |
| 12 | runnable | C FFI (close, sock_poll without idle wait, select); demos; the option C server binary | updated |
| 13 | close and fd reuse | today's #68 (version 2 world, echo2) | renumbered |
| 14 | docs | README, design notes, START-HERE, reading path | updated |
| — | **next steps (separate PR, not in the series)** | endpoint world (#67), fd-discipline (#78), buffer closure (#79), KV (#52, #73, #80) | statements for review |
| — | **appendix / showcase** | the chat server (#66, #72, #75, #76, #83) | linked, not reviewed |

## 3. Retired to `archive` (tagged, not deleted)

- The header-tolerant HTTP pipeline (HttpSpecHeaders, `http_prog_h_spec`, #31/#32/#48/#54) and the strict one. They are re-derived as instances in layer 10, but the copies go.
- #53 `http-quiet` and #56 `http-blocking` (live-list HTTP select): superseded by option C. #56's DoS caveat stays in a design note as history.
- Per-server liveness proofs that layer 9 re-derives. The echo one is kept only if the reading path needs it.
- `spike/option-c-int`'s `async/pk/` placement is a staging area. Folding moves its files into the layer directories.

## 4. Decisions this depends on

| decision | blocks | default if undecided |
|---|---|---|
| **H-CHARS** (#55, 04be60754: RFC character sets for paths and field values) | layer 1's HttpSpecBodies; layers 10 and 11 | fold without H-CHARS (tchar only) and keep option C on the tchar spec; that needs one revert merge |
| **v1 option A**: restrict the endpoint world's version-1 equivalences (`v1_instance`, and the v1 `sym_equiv`s for echo, http_b and kv) to fd-disciplined programs (`fd_disciplined` / `v1_disciplined`, discharged for our programs in #78). The reason: v1 lets a program touch an fd before accepting it (`¬v1_instance`). Option B instead routes v1 only through v2 simulations. | the next-steps PR (endpoint world, #78) | keep it out of the series |
| **endpoint §6 items 1–4** (parked API decisions): acceptance `takes` per call; a refused connect reads as EOF; full write, with sending as a separate step; writability as a separate call | any client or proxy program; the next-steps PR | parked; nothing in the series needs them |
| **endpoint §7 (a)**: the corrected `relays` relation (buffer closure, #79) | the next-steps PR | statements for review |
| **endpoint §7 (b)**: ∀ vs ∃ over system runs (n-ary open systems) | the next-steps PR | statements for review |
| **PROTO_STABLE** (cf-actions, in progress) | layer 11's headline | fold with the hypothesis made explicit, or wait |
| **QuietSpec as trusted** (already user-approved, incl. the `sel_ok` select change) | layer 1 | approved |

## 5. Effort (worker time, at tonight's pace; builds through holslot)

| item | estimate |
|---|---|
| layer 1 spec fold (QuietSpec, tchar, ±H-CHARS, spec-rfc) | 2–3 h |
| layer 5 (+ Level 2 library) | 1 h |
| layer 9 library liveness (move #62–#71 into the series layout) | 4–6 h |
| layer 10 protocol pipeline replacing the copies, plus retiring them | 6–8 h (largest: dependency rewiring in 10–12 and the runnable demos) |
| layer 11 quiescence (`echo_l_quiet`, option C, `pk/` → layout) | 3–4 h |
| renumber 12–14, docs, reading path, PR bodies | 3 h |
| **total** | **≈ 2–3 worker-days**, in parallel across 2–3 workers along the layer boundaries |

## 6. Reviewer reading path

**One hour (short):**
1. Layer 1: the trusted surface: what EchoSpec, HttpSpecBodies and QuietSpec say, and their bites (20 min).
2. README "Why you should believe it" and the headline theorems: `echo_spec`, `http_prog_pb_spec`, `echo_l_quiet`, `http_q_quiet_b` (10 min).
3. Layer 3: the Level 2 idea (declared interest, `quiet`, `no_busy_waiting`) (15 min).
4. Layer 11's design note: the two spins and select on the declared interest (10 min).
5. "Honest limitations" (5 min).

**Full:** layers 1 → 14 in order. Layers 2–8 are as today; 9 → 10 → 11 is the new spine: liveness once, protocols as instances, quiescence by construction. The next-steps PR and the chat appendix come after the series.
