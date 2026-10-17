# 50 — Stdio (fds 0–2): why they are reserved, and the cost of sanitising them in the program

Status: ESTIMATE for the user. No code.
Author: honest-ffi, 2026-10-17. Base: spike/l3-quiet @c27f90155.

## (0) Why the claims need 0w/1w/2w reserved today

`l0_server_world` (honest-echo/honestEchoL0SpecScript.sml:102-109) contains
`MEM 0w w0.reserved ∧ MEM 1w w0.reserved ∧ MEM 2w w0.reserved`. In the model
`reserved` means "the process's other open fds" (honest-l0/honestL0WorldScript.sml:192).
It belongs to `l0_used` (:203), so `lowest_fd` never returns a reserved fd.

**No proof uses the three MEM facts.** Every use of `l0_server_world_def` takes
other conjuncts. Every allocation and freshness lemma (`lowest_fd_free_lim`,
`lowest_fd_fresh`, `fds_lt_*`) is generic over `reserved`. The clause exists so
that the model tells the truth: it is lie L9 of design/36 (§2, l.122). With fds
0–2 closed, three things go wrong, and only the first is fd numbering:

1. **Numbering.** POSIX `socket()`/`accept()` return the lowest free fd (POSIX.1-2017 *open*,
   "Allocation of File Descriptors"). A connection could then get fd 0. The model's `alloc`
   never returns it, because 0 is reserved. This also matters for the wire format:
   `sys_connect` uses the value 0 to mean "no fd" (runnable/l0/socket_ffi_l0.c:50-53,
   honestL0World:501-502), which is unambiguous only while fd 0 is open.
2. **The basis writes to fds 1/2.** basis/basis_ffi.c writes to stderr on a nonzero exit
   (:356), heap or stack exhaustion (:363, :366), GC stats (:368) and `cml_err` (:56-60).
   With fd 2 reused as a client socket, those bytes would go to a client. That is not in
   any trace the claims talk about.
3. **Our own `die`** (socket_ffi_l0.c:111) writes to stderr.

Today this is enforced outside the model. The C constructor (socket_ffi_l0.c:162-166, D2)
runs `fcntl(F_GETFD)` on 0, 1 and 2 and calls `die`/`exit(3)` if any is closed, before
`cml_main`. The claims take `l0_server_world` as a precondition, so a run that dies there
is simply not covered.

## (c2) Check and refuse, in the program

Move D2's check into the program, as its first FFI call, so that the refusal becomes an
observable claim outcome instead of a precondition.

- **Trusted model addition.** One query-only call, `sys_stdio` (no conf, a 3-byte result):
  `l0_call «sys_stdio» w` answers, for f ∈ {0,1,2}, whether `MEM f w.reserved`. It leaves
  the world unchanged. C: three `fcntl(f, F_GETFD)` calls. POSIX gives EBADF iff f is not
  open (POSIX.1-2017 *fcntl*, ERRORS), so the answer is exact.
  - Note: POSIX *exec* allows a process to start with 0–2 closed. It also lets
    implementations reopen them ("may open an unspecified file"), so "closed" must be handled.
- **Claim change.** `l0_server_world` drops the three MEM conjuncts (the rest stays). Each
  L0 claim gets a new outcome, alongside `listen_failed`:
  `stdio_closed beh ⇔ ∃bs. beh = Terminate Success [IO_event (ExtCall «sys_stdio») [] bs] ∧ some byte of bs says closed`.
  `listen_failed` becomes a two-event prefix (stdio, then listen).
- **Proof impact.** Small, because nothing used the reservation. After the call answers
  "open" we know `MEM 0w/1w/2w w0.reserved`, which is exactly today's precondition. The
  world is unchanged, so every existing run proof applies to the trace after one leading
  event. The work is that one-event shift in each top-level semantics proof, as was
  already done for `sys_listen`.
- **Per-owner estimate** (≈ 3 days in total):

| Owner | Work | Est. |
|---|---|---|
| honest-l0 model (honest-ffi) | `l0_call` case, `l0_oracle`, the props lemmas' case splits (`fds_lt_call` and friends: one more name) | 0.5 d |
| C (runnable/l0) | `ffisys_stdio`; the constructor keeps only SIGPIPE | 0.1 d |
| honest-l0-cf (KV worker / cf-actions) | `l0_do «sys_stdio»` spec, like `sys_listen_echo` | 0.5 d |
| echo L0 (KV worker), L3-00 statements + bquiet (cf-actions) | program prefix, `stdio_closed ∨` in `echo_safe_l0`/`l0_echo2_claim`/quiet, a one-event shift lemma | 0.75 d |
| HTTP/KV L0 (KV worker) | the same, for its main proof | 0.5 d |
| proxy L0 / client C1 (honest-ffi / async-spike) | statement only (`stdio_closed ∨`); no L0 proofs exist yet | 0.2 d |
| design/36 (D2 → new D), README | text | 0.1 d |

## (c1) Repair, like OpenSSH, plus stdout/stderr as output sinks

There are two separable parts.

- **Repair** (`open("/dev/null", O_RDWR)` until the fd is ≥ 3; OpenSSH's `sanitise_stdfd`).
  If the C constructor does it before `cml_main`, the model needs **no change**: the
  precondition `MEM 0w/1w/2w reserved` becomes true by construction. If the program does it
  instead, `sys_stdio` becomes `sys_stdfix`, which adds 0–2 to `reserved`.
  - POSIX *open* returns the lowest free fd, so the loop fills 0, 1, 2 in order.
  - The cost is ≈ 0.3 d in either form.
- **Writing to fds 1/2** is the larger part.
  - The honest oracle `l0_oracle` fails (FFI_failed) on any call outside its list, and the
    basis' `TextIO.print` goes through basis_ffi, not this oracle. So today an async program
    **cannot print at all** under the honest model.
  - Options:
    - **(i) Our own call** `sys_out fd data` for fd ∈ {1,2}: an opaque sink. The world
      chooses the count taken and an error (stdout may be a pipe, blocking or not, so
      partial writes, EAGAIN and EPIPE are all honest), the way `reserved_rev` already makes
      poll on reserved fds opaque.
      - It touches `l0_call`, its props lemmas, a frame lemma ("`sys_out` changes no
        socket, channel, listener or `l0_used`"), and the trace views.
      - The `l0_event_*`/`pos_*`/`l0_ep_*` functions already default to NONE on other call
        names, so episode views ignore it.
      - Poll and close are untouched if programs never poll or close 1/2. We would forbid
        that in the program, not model it.
      - Cost: ≈ 1.5 d for the model and CF wrapper, plus ≈ 0.25 d per program that prints,
        for the frame step in its loop invariant.
    - **(ii) Compose `l0_oracle` with the basis' fs/stdout model** so that `print` works.
      That is a model-composition project (two oracles over one FFI state): ≈ 1–2 weeks.
      Not recommended.

## (d) (c2) now, (c1) later

(c1) is a strengthening and does not undo (c2):

- With the constructor repair, the world precondition `MEM 0w/1w/2w reserved` holds, so
  `sys_stdio` always answers "open". Every claim's `stdio_closed beh` disjunct is then
  provably false. Drop it, or derive the strong form as a corollary. No proof changes.
- Keep the `sys_stdio` call in the programs. If (c1) instead removed the call, the leading
  event would go and the one-event shift lemmas would have to be redone. Keeping it costs
  three `fcntl`s at startup.
- `sys_out` ((c1), option (i)) is independent of both. It adds events the episode views ignore.
