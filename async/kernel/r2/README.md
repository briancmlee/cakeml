# L3-06: R2′, psk is a delay of the kernel's schedule

`honestL1PFSimple` proves L3-00's headline claim `l1pf_simple_claim`
(`kernelStatementsCore`), as `l1pf_simple_claim_holds`. The claim: in simple
L0 worlds, the version-2 world that R1-safe builds from the prefetching L1's
own run (`psk`) is a **delay** of the kernel's schedule (`sk_of`'s). At each
round's instant it is never ahead of the schedule (`l1pf_never_ahead`), and
it misses nothing (`l1pf_misses_nothing`). The main theorem is
`l1pf_simple`.

Source: `spike/l1pf-simple` @f329fb3fa (on D20, `spike/d20-poll`
@e282d1996), renamed with `design/names.tsv`. The fold changes three things:
- the statement's vocabulary (`upto`, `conns_of`, `data_of`, `within`,
  `delays`, `kernel_steps`, `round_instant`, `fds_room`) is no longer copied
  here; it comes from `kernelStatementsCore`;
- `l1pf_simple_claim_holds` is new: it closes the claim from `l1pf_simple`;
- `tick_hist_ch` and `sys_poll_simple` are plain lemmas here. They began as
  copies from the superseded `honestL1Round`, which the series does not
  fold.

The proof, in sections:
- A: the kernel's version-2 world, left alone (`kworld`, `vinv`).
- B–E: the L0 world against the kernel's, one call, the fetch, and a round
  (`kinv`, `sinv`).
- F: the run, and the first half: `psk` is never ahead.
- G–G7: the second half, `psk` misses nothing. No call is retried and no
  accept fails (`fds_room`; G2); every queued connection is accepted (G3);
  data and EOF follow (G4–G7).
- G8: the delay.

Hypotheses beyond `simple_v2`:
- two simple-class conditions (coordinator-approved): `lifetime_fair` of
  the kernel's schedule, and no `emfile_drops`;
- `winv`, a fresh listener, `run_ok`;
- fewer than 2^64 − 1 connections;
- `fds_room`: fewer fds in use than the limit at each round's start;
- S1–S4.

[F1] is not a hypothesis: simple worlds have no transient failures.
