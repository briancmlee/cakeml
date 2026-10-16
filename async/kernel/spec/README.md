# L3-02: the raw-trace echo spec — TRUSTED, despite its layer

**This directory is part of L3's trusted surface.** It sits in L3-02, not in
L3-01, only because it needs `fds_lt` from `honestL0WorldProps` (L3-02).
Review it together with `kernel/surface/` (L3-01).

- `honestEchoL0Spec` (approved by the user): the echo server's safety over the
  raw L0 trace. The episodes are the accepted connections; `l0_read` is what
  each received, `l0_sent` what the kernel took of each send; `echo_safe_l0`
  says that sent ≼ read in every episode (while fewer than 2^64 − 1
  connections are accepted). `l0_server_world` is the startup contract.
- `honestEchoL0Bites`: broken servers fail it. These are proved, not trusted.

Copied verbatim from `spike/servers-honest-l1` fab2640ab (the KV worker's),
renamed with names.tsv.
