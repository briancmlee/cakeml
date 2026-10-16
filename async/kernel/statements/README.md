# L3 (the real kernel): the headline statements, drafted for review

`kernelStatementsScript.sml` states L3's headline claims before their
proofs, as L2-00 did for the peers. Each claim is a **definition of a
proposition**, so nothing is assumed. One bite is **proved** now, in the L0
model: `hup_spin_bite`.

The file typechecks and builds (no cheats; `grep -c cheat` on the `.dat`
is 0) against the spike theories, merged on `scratch/l3-stmts` (3ea622312:
`spike/servers-honest-l1` with `spike/honest-connect`). It has no
Holmakefile here, because the honest L0/L1 theories enter the series in the
later L3 layers. The names are the spike names, as in L2-00.

**The user's policy, followed throughout:**
- no new trusted kernel facts;
- where POSIX is loose, weaken the main statement honestly, and give the
  strong form as a corollary under an explicit hypothesis (D16, D18);
- fairness only in the weak, "infinitely often", observed-outcome forms:
  [F1] (D11′) and [F2] (D12).

**Reused, not redefined:**
- the KV worker's raw-trace vocabulary (`honestEchoL0Spec`): `l0_accepted`,
  `l0_read`, `l0_sent`, `l0_server_world`, `echo_safe_l0` (approved);
- honest-ffi's model: `l0_ffi`, `simple_v2`, `sk_of`, `psk`/`parr`,
  `run_ok`, `F1`, `S1`–`S4`, `kept_err`, `ev_on`, `retried`, `winv`,
  `l0_replay`;
- the corollary hypotheses carry honest-ffi's names, read off the trace as
  `F1_io` is `F1`'s: `HD16_io` (`HD16`, honestL1PFD16, in progress), `H1_io`
  and `H3_io` (`H1`, `H3`, honestL1PFConnRun, used by the proved
  `live_conn_cor`).

## The claims

| claim | what | hypotheses | status |
|---|---|---|---|
| `l1pf_simple_claim m` (R2′, **the headline**: user decision Q-L3-2) | in simple L0 worlds, the version-2 world that R1-safe builds from the prefetching L1's run (`psk`) is a **delay** of the kernel's schedule (`sk_of`'s): never ahead of it at each round's instant, and missing nothing | `simple_v2`, `winv`, a fresh listener, `run_ok`, fewer than 2^64 − 1 connections, the server obligations S1–S4 | stated; ⏳ honest-ffi (R2′) |
| `l1pf_simple_eq_claim m` (optional corollary) | with a prompt schedule and a prompt server, no delay: `psk`'s steps **equal** the kernel's | as above, plus `prompt_sched` (≤ 1 connect per step, ≤ 1 arrival per channel per step, each ≤ `pf_chunk` bytes, nothing in a channel's connect step) and `prompt_server` (one poll per round; after each round's actions, no unread input, no unaccepted connection, every outbox ≤ hw) | stated; optional |
| `l0_echo2_claim K prog` (R4′, the template) | the echo server with close on the honest L0 FFI, in every `l0_server_world`: either the listen failed and the program stopped, or it diverges with raw safety `echo_safe_l0` and raw liveness: per episode (`echo_live_l0`: what the peer sent is eventually sent back, and a peer EOF eventually closes the episode) and per connection (`conn_live_l0`: a queued connection is eventually accepted or dropped) | liveness only: [F1] on the trace (`F1_io`), [F2], fewer than 2^64 − 1 accepts in the run (`accepts_below`), and per episode D(c) (`drains`: the peer reads) and D19's `hup_drains K` (after a hang-up, the peer empties what is in flight within K − 1 polls that list the fd for output (user-approved form b″: D19's count runs only while the outbox is not empty); K is L1's `pf_hupwait`; with [F2] this gives D19's per-round send progress). **Weakened** (main form): "unless a hard error was observed on the episode" (D16), and "unless accepts on the listener fail infinitely often" (D18) | stated; safety ⏳ KV worker (`echo_l0_safe`, in progress), liveness ⏳ after R1-live |
| `l0_echo2_strong_claim K prog` | the corollary form. Echo: the only excuse left is a genuine reset that discarded the unread input (`flushed_ch`). Connections: accepted or dropped, with no "accepts fail" disjunct | additionally `HD16_io` (a hard recv error only on a channel that broke and lost its input), `H1_io` (an accept error L1 does not keep really dropped a queued connection) and `H3_io` (the joint weak form over `kept_err`: retried, EMFILE, ENFILE). All are explicit and none is trusted; no [F3] (dropped in design/36 §6, 2026-10-17: L0's transient failure may be a spurious EMFILE) | stated; the model-level D18 corollary `live_conn_cor` is **proved** (honest-ffi) |
| `quiet_on_kernel_claim guar prog` | quiescence on the kernel, through a blocking L1 variant: `guar` holds whether the program runs forever or sleeps; **with finitely many arrivals it ends asleep in a blocking `sys_poll`**, unless [F1] fails. **No POLLHUP disjunct:** under D19 (user decision Q-L3-1) no hung-up fd stays in the blocking set | `l0_server_world`; for sleeping, `arrivals_finite_l0`. The `echo2_guar_l0` instance is the echo's | stated; ⏳ needs the blocking L1 variant and D19 (honest-ffi) |
| `hup_spin_bite` (with `hup_wakes_forever`) | in the L0 model, if fd f's channel is hung up (the peer closed, or it broke) and the world reports POLLHUP for it, which [P poll] allows, then every blocking poll that lists f returns at once, now and after any number of steps, **whatever events it asks for on f** (a paused fd's, too), so the poll call never returns `FFIdiverge` | none beyond the world state | **proved** |

**The 2^64 bound.** After 2^64 − 1 accepted connections the L1 loop stops
making calls; it spins, which was coordinator decision (A), chosen over
wrapping the handle counter. No events follow, so `echo_safe_l0` holds
vacuously from there, and every liveness conclusion carries
`accepts_below io` as a hypothesis.

What the bite means: a blocking L1 that kept a hung-up fd in its wait
set, for example a paused fd whose peer half-closed, could spin forever.
That is why quiescence needs D19.

## User decisions (2026-10-17, via the coordinator)

- **Q-L3-1 → D19, an L1 policy (option 2, the bounded flush).** On
  POLLHUP, L1 reads what is left. A genuinely broken connection's outbox is
  dropped and the fd closed. A half-closed (EOF) one keeps flushing and is
  closed when drained, but is dropped after K rounds without send progress.
  `quiet_on_kernel_claim` has no POLLHUP disjunct; `hup_spin_bite` stays as
  the motivation. The echo's liveness assumes, per episode, that the peer
  reads within K rounds of a hang-up (`hup_drains K`), so a half-closed peer
  that keeps reading gets its whole reply. honest-ffi owns the PF model and
  implements D19.
- **Q-L3-2 → the delay form is the headline.** `l1pf_simple_claim` is the
  delay form; the equality form, `l1pf_simple_eq_claim`, is at most an
  optional corollary.

## Not in this layer

- HTTP and KV on the honest L0 FFI follow `l0_echo2_claim`'s template.
- The machine-code statement, and the memory bound (design/36 §6,
  whole-program obligation 7).
- Clients and connect fairness (the moonshot; design/36 §6 "Open item").
