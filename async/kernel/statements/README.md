# L3 (the real kernel): the headline statements, drafted for review

These files state L3's headline claims before their proofs, as L2-00
did for the peers. Each claim is a **definition of a proposition**, so
nothing is assumed. One bite is **proved** now, in the L0 model:
`hup_spin_bite`.

The statements are split in two (a reorganisation; every definition is
unchanged):
- `kernelStatementsCoreScript.sml` holds what needs no CakeML program
  semantics: R2′'s claims (`l1pf_simple_claim`, `l1pf_simple_eq_claim`)
  with their vocabulary, and `hup_spin_bite`. The kernel layers build
  against it: L3-06 proves `l1pf_simple_claim` from it, without copying
  its definitions.
- `kernelStatementsScript.sml` imports Core and adds the whole-program
  claims (`l0_echo2_claim`, `l0_echo2_strong_claim`,
  `quiet_on_kernel_claim`). They need `semantics_prog` and `honestL0Part`'s
  `l0_replay`, which enter the series with the CakeML layer (L3-07).

Both files typecheck and build (no cheats; `grep -c cheat` on the `.dat`
files is 0) against the spike theories, merged on `scratch/l3-stmts`
(06948b621: `spike/servers-honest-l1` with `spike/honest-connect` and D20's
`spike/d20-poll` @e282d1996). The poll readings (`poll_hup`,
`n_out_polls`, `hup_spin_bite`) use D20's encoding: struct pollfd
records after a 16-byte header, revents at byte 6 of each. `poll_hup`
also requires the poll to succeed, since a failed poll's revents bytes
are unspecified.

In the series, Core builds from L3-06 on, against the final-series theories
and under the final-series names (`design/names.tsv`). The Holmakefile here
builds Core only (its default target); kernelStatements waits for
`honestL0Part` (L3-07).

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
| `l1pf_simple_claim m` (R2′, **the headline**: user decision Q-L3-2) | in simple L0 worlds, the version-2 world that R1-safe builds from the prefetching L1's run (`psk`) is a **delay** of the kernel's schedule (`sk_of`'s): never ahead of it at each round's instant, and missing nothing | `simple_v2`, plus two simple-class conditions: `lifetime_fair` of the kernel's schedule (no arrival the world would drop) and no `emfile_drops` (no reset of a queued connection under EMFILE); `winv`, a fresh listener, `run_ok`, fewer than 2^64 − 1 connections, the server obligations S1–S4, and **`fds_room`**: fewer fds in use than the limit at each round's start (a bound on connections open at once, not on all connections; with it no accept fails) | **proved** in L3-06 (`kernel/r2`: `honestL1PFSimple.l1pf_simple_claim_holds`, from `l1pf_simple`: never ahead, `l1pf_never_ahead`; misses nothing, `l1pf_misses_nothing`) |
| `l1pf_simple_eq_claim m` (optional corollary) | with a prompt schedule and a prompt server, no delay: `psk`'s steps **equal** the kernel's | as above (with `fds_room`), plus `prompt_sched` (≤ 1 connect per step, ≤ 1 arrival per channel per step, each ≤ `pf_chunk` bytes, nothing in a channel's connect step) and `prompt_server` (one poll per round; after each round's actions, no unread input, no unaccepted connection, every outbox ≤ hw) | stated; optional |
| `l0_echo2_claim K prog` (R4′, the template) | the echo server with close on the honest L0 FFI, in every `l0_server_world`: either the listen failed and the program stopped, or it diverges with raw safety `echo_safe_l0` and raw liveness: per episode (`echo_live_l0`: what the peer sent is eventually sent back, and a peer EOF eventually closes the episode) and per connection (`conn_live_l0`: a queued connection is eventually accepted or dropped) | liveness only: [F1] on the trace (`F1_io`), [F2], fewer than 2^64 − 1 accepts in the run (`accepts_below`), and per episode D(c) (`drains`: the peer reads what it was sent; once nothing more is sent on c, its bytes in flight reach 0. Corrected 2026-10-17 from a read-count form that zero-byte reads satisfied) and D19's `hup_drains K` (after a hang-up, the peer empties what is in flight within K − 1 polls that list the fd for output while episode j holds it, i.e. before L1's first close call on the fd (whatever its result: an interrupted close may still free it), since the fd number may be reused (user-approved form b″: D19's count runs only while the outbox is not empty); K is L1's `pf_hupwait`; with [F2] this gives D19's per-round send progress). **Weakened** (main form): "unless a hard error was observed on the episode" (D16), and "unless accepts on the listener fail infinitely often" (D18) | stated; safety ⏳ KV worker (`echo_l0_safe`, in progress), liveness ⏳ after R1-live |
| `l0_echo2_strong_claim K prog` | the corollary form. Echo: the only excuse left is a genuine reset that discarded the unread input (`flushed_ch`). Connections: accepted or dropped, with no "accepts fail" disjunct | additionally `HD16_io` (a hard recv error only on a channel that broke and lost its input), `H1_io` (an accept error L1 does not keep really dropped a queued connection) and `H3_io` (the joint weak form over `kept_err`: retried, EMFILE, ENFILE). All are explicit and none is trusted; no [F3] (dropped in design/36 §6, 2026-10-17: L0's transient failure may be a spurious EMFILE) | stated; the model-level D18 corollary `live_conn_cor` is **proved** (honest-ffi) |
| `quiet_on_kernel_claim guar prog` | quiescence on the kernel, through a blocking L1 variant: `guar` holds whether the program runs forever or sleeps; **with finitely many arrivals it ends asleep in a blocking `sys_poll`**, unless [F1] fails or **accepts fail infinitely often** (`accepts_fail_io`, D18's excuse: under EMFILE/ENFILE the blocking L1 keeps retrying the accept). **No POLLHUP disjunct:** under D19 (user decision Q-L3-1) no hung-up fd stays in the blocking set | `l0_server_world`; for sleeping, `arrivals_finite_l0`. The `echo2_guar_l0` instance is the echo's | stated; ⏳ needs the blocking L1 variant and D19 (honest-ffi) |
| `quiet_on_kernel_strong_claim guar prog` | the corollary form: with finitely many arrivals, it sleeps unless [F1] fails, with no accepts excuse | additionally `H1_io` and `H3_io` (the joint weak form), as in `l0_echo2_strong_claim`. A premise "accepts fail only finitely often" would only restate the main form | stated |
| `hup_spin_bite` (with `hup_wakes_forever`) | in the L0 model, if fd f's channel is hung up (the peer closed, or it broke) and the world reports POLLHUP for it, which [P poll] allows, then every blocking poll that lists f returns at once, now and after any number of steps, **whatever events it asks for on f** (a paused fd's, too), so the poll call never returns `FFIdiverge` | f non-negative as an int32 (`w2n f < 2^31`: [P poll] ignores negative fds; L1's are all below, `psmall`) | **proved** |

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
