# L3-01: the trusted surface of the real kernel

What L3 trusts, beside CakeML's semantics:

- `runnable/l0/socket_ffi_l0.c`: the honest L0 C. It makes about one
  syscall per call, has no loops, retries or policy, and reports every
  result in the same 13-byte header.
- `honestL0`: the errno table and that header (`enc_res`/`dec_res`,
  proved inverse), and the readiness flags.
- `honestL0World`: the L0 world. It is a sound over-approximation of the C
  and the kernel (D1), anchored on POSIX.1-2024 and RFC 9293/1122 with cited
  sections (D9). Where the standards are loose, behaviour is a world choice
  (`lchoices`).
- `honestL0Rely`: what is assumed of those choices (`l0_rely`).

**The probes are conformance tests, not justification.** `runnable/l0/tester`
holds them (design/36 §4.3: probes, random tests, mutants), and
`make conformance` runs them in `runnable/l0`.

**Also trusted, in L3-02:** the raw-trace echo spec `honestEchoL0Spec`
(`kernel/spec/`, approved). It sits one layer later only because it needs
`fds_lt` from `honestL0WorldProps`. The fairness definitions [F1]/[F2] and
`hup_spin_bite` are on L3-00 for now.

**Source:** `spike/d20-poll` @e282d1996, verbatim except the renamed
ancestor (`ffiSpikeSocketFFI` → `socketWorld`, names.tsv). It includes
- D20: `sys_poll` polls the caller's `struct pollfd` buffer in place, with no cap;
- D21: a [P] looseness, with user approval: after the peer's EOF, with an
  empty inbox and a reset error pending, `recv` may return 0 and leave the
  error pending (world choice `eof_first`). So an EOF may be seen on a
  channel whose reset error is still pending, and a later send reports it;
- D22: no model change ([X5], Linux's shutdown of a pending connect,
  which L1 never calls).
- D33 (design/50 (c2), user decision; from `spike/stdio-c2` @e083021aa):
  `sys_fdok` asks whether one fd is open (`fcntl(fd, F_GETFD)`; [P fcntl]
  makes the answer exact) and leaves the world unchanged. The C
  constructor no longer checks fds 0-2: the programs ask about them first
  and stop if one is closed (`stdio_closed`, L3-00).

Design: `design/36-honest-ffi.md` (§§3–4, §3.6 for D20, §9 for the decisions). The names
are the spike names, provisionally.
