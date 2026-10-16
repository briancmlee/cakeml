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

**Still to come in this layer:**
- the raw-trace echo spec, `honestEchoL0Spec` (`echo_safe_l0`, approved),
  and its bites. It waits for `fds_lt` to move from the L1 theory
  `honestL1Steps` into `honestL0WorldProps` (honest-ffi).
- the fairness definitions [F1]/[F2] and `hup_spin_bite`, which are on
  L3-00 for now.

Design: `design/36-honest-ffi.md` (§§3–4, §9 for the decisions). The names
are the spike names, provisionally.
