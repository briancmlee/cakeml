# L3 (the real kernel): the headline statements, drafted for review

`kernelStatementsScript.sml` states L3's headline claims before their
proofs, as L2-00 did for the peers. Each claim is a **definition of a
proposition**, so nothing is assumed. One bite is **proved** now, in the L0
model: `hup_spin_bite`.

The file typechecks and builds (no cheats; `grep -c cheat` on the `.dat`
is 0) against the spike theories, merged on `scratch/l3-stmts` (a36251555:
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
  `run_ok`, `F1`, `S1`, `S3`, `S4`, `ev_on`, `retried`, `winv`,
  `l0_replay`.
- `S2` is a verbatim copy of honest-ffi's `honestL1PFConnRun.S2`, which is
  not pushed yet. The copy is removed when that theory lands.

## The claims

| claim | what | hypotheses | status |
|---|---|---|---|
| `l1pf_simple_claim m` (R2′) | in simple L0 worlds, the version-2 world that R1-safe builds from the prefetching L1's run (`psk`) is a **delay** of the kernel's schedule (`sk_of`'s): never ahead of it at each round's instant, and missing nothing. With a prompt schedule and a prompt server it **equals** it | `simple_v2`, `winv`, a fresh listener, `run_ok`, fewer than 2^64 − 1 connections, the server obligations S1–S4; for equality, also `prompt_sched` (≤ 1 connect per step, ≤ 1 arrival per channel per step, each ≤ `pf_chunk` bytes, nothing in a channel's connect step) and `prompt_server` (one poll per round; after each round's actions, no unread input, no unaccepted connection, every outbox ≤ hw) | stated; ⏳ honest-ffi (R2′) |
| `l0_echo2_claim prog` (R4′, the template) | the echo server with close on the honest L0 FFI, in every `l0_server_world`: either the listen failed and the program stopped, or it diverges with raw safety `echo_safe_l0` and raw liveness: per episode (`echo_live_l0`: what the peer sent is eventually sent back, and a peer EOF eventually closes the episode) and per connection (`conn_live_l0`: a queued connection is eventually accepted or dropped) | liveness only: [F1] on the trace (`F1_io`), [F2], fewer than 2^64 − 1 accepts in the run (`accepts_below`), and per episode D(c) (`drains`: the peer reads). **Weakened** (main form): "unless a hard error was observed on the episode" (D16), and "unless accepts on the listener fail infinitely often" (D18) | stated; safety ⏳ KV worker (`echo_l0_safe`, in progress), liveness ⏳ after R1-live |
| `l0_echo2_strong_claim prog` | the corollary form, without the D16/D18 disjuncts: "unless the channel really broke" | additionally `hard_errs_real` (D16), and D18's H1 `accept_errs_real`, H2 `F3_io`, H3 `accepts_joint_io` (the joint weak form), all explicit and none trusted | stated |
| `quiet_on_kernel_claim guar prog` | quiescence on the kernel, through a blocking L1 variant: `guar` holds whether the program runs forever or sleeps; **with finitely many arrivals it ends asleep in a blocking `sys_poll`**, unless [F1] fails or POLLHUP keeps waking it (`hup_spin`) | `l0_server_world`; for sleeping, `arrivals_finite_l0`. The `echo2_guar_l0` instance is the echo's | stated; ⏳ needs the blocking L1 variant |
| `hup_spin_bite` (with `hup_wakes_forever`) | in the L0 model, if fd f's channel is hung up (the peer closed, or it broke) and the world reports POLLHUP for it, which [P poll] allows, then every blocking poll that lists f returns at once, now and after any number of steps, **whatever events it asks for on f** (a paused fd's, too), so the poll call never returns `FFIdiverge` | none beyond the world state | **proved** |

**The 2^64 bound.** After 2^64 − 1 accepted connections the L1 loop stops
making calls; it spins, which was coordinator decision (A), chosen over
wrapping the handle counter. No events follow, so `echo_safe_l0` holds
vacuously from there, and every liveness conclusion carries
`accepts_below io` as a hypothesis.

What the bite means: the `hup_spin` disjunct of `quiet_on_kernel_claim` is
real. A blocking L1 that keeps a hung-up fd in its wait set, for example a
paused fd whose peer half-closed, can spin forever, so quiescence needs
either that disjunct or an L1 policy that keeps such fds out of the
blocking set. That is an **open decision** (below).

## Open decisions (for the user)

- **Q-L3-1, the HUP problem.** Keep the `hup_spin` disjunct (honest; the
  theorem is weaker), or adopt an L1 policy for hung-up fds in the blocking
  set? The candidate policy is to stop waiting on a hung-up fd's outbox
  after a bound, like D7's slow-client drop. It would lose a response to a
  half-closed client that stops reading. With the policy, the disjunct
  goes.
- **Q-L3-2.** Is `prompt_server`/`prompt_sched` the right price for
  `l1pf_simple`'s equality form, or should only the delay form be the
  headline? The delay form is enough for every transfer, and equality is
  for the reader.

## Not in this layer

- HTTP and KV on the honest L0 FFI follow `l0_echo2_claim`'s template.
- The machine-code statement, and the memory bound (design/36 §6,
  whole-program obligation 7).
- Clients and connect fairness (the moonshot; design/36 §6 "Open item").
