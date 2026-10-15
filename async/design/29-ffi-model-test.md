# 29: A model-based tester for the trusted socket C layer

Status: **done.** Branch `spike/ffi-model-test`, stacked on
`spike/close-v2-world` (close-v2's PR #45), which has the five-call
`socket_ffi.c` (including `ffisock_close`) and the version-2 socket model
(`async/socket-v2/socketV2FFI`). Files are in `async/ffi-model-test/`.

`async/runnable/socket_ffi.c` is in the trusted base: the proofs end at
the HOL socket model, and the C is assumed to implement it. This tester
gathers evidence for that assumption. It drives the real C functions with
real loopback clients through random scenarios, and checks every call
against the model. The comparison is done both by a Python transcription
and by HOL itself (EVAL of the model's FFI functions on the logged calls).

## 1. Results

| check | calls | divergences |
|---|---|---|
| Python transcription, 60 random scenarios × 500 steps, data up to 3000-byte chunks and 16000-byte writes, reads of 1 to 65536 bytes | 20177 | **0** |
| HOL EVAL of `ffi_sock_*2` on every call of 3 small-data scenarios (`ffiModelCheck`, committed and built by Holmake) | 198 | **0** (198/198 proved) |
| HOL EVAL on every call of 4 full-size scenarios | 735 | not completed (§1.1) |

No divergence was found. That includes the client identity of each
accepted connection (FIFO), the fd chosen at accept (the lowest free fd,
including reuse after `close`), and each client's received bytes (the
model's outgoing log, checked at the end of each scenario). The process's
fd table was also checked against the model's at the end of each run.

### 1.1 Full-size HOL check

The 4 full-size scenarios (735 calls) passed the Python checks. Their HOL
EVAL check was started but stopped by the environment because the
machine was low on memory (5 other workers were building). EVAL on
kilobyte-sized byte lists is far heavier than on the small-data traces.
It has not been re-run: `hol_check.py build/trace-full4.jsonl` regenerates
it, under another theory name. The committed HOL check uses small data
(chunks of at most 12 bytes), which exercises the same code paths of the
model.

The C tested is close-v2-world's `socket_ffi.c`, which still has the idle
wait. PR #50 removes it; that changes only timing, so the results carry
over, and `ffi_model_test.py` can be re-run unchanged after that merge.

## 2. How it works

`ffi_model_test.py`:

- **Server child.** A child process loads `socket_ffi.c`, compiled as a
  shared library. Its constructor creates the listener on fd 3, exactly
  as in the real program. The child then executes `ffisock_poll`,
  `ffisock_accept`, `ffisock_read`, `ffisock_write` and `ffisock_close` on
  command, returning the output buffer. Its command pipes are moved to
  fds 40/41 first, so fd 3 is free. The child's other fds (0, 1, 2, 40,
  41) are the model's `reserved` fds.
- **Driver.** The parent owns the clients (real TCP sockets to the
  listener). It generates random steps: client actions (connect, a chunk
  of data, `shutdown(SHUT_WR)` = EOF) and server calls (poll over the
  listener and a random subset of the open fds in random order; accept;
  read with buffers of 1..65536 bytes; write of 0..16000 bytes; close).
- **Time.** In the model, arrivals come only at `sock_poll`, one step of
  the schedule per poll. So the driver collects client actions and
  performs them just before the poll that delivers them, then waits 10 ms
  for the kernel. The same actions form that poll's schedule step in the
  model.
- **The model.** `ModelV2` is a line-by-line transcription of
  socketV2FFI: `deliver2`, `tick2`, `is_ready2`, `sock_*2`, `ffi_sock_*2`,
  with the HOL list orders (`open_fds` consed onto, `ADELKEY`).
- **Checks per call:** the C's output buffer must equal the model's.
  Accept also asks the child for the accepted socket's peer port, to check
  that it is the client the model hands out. **At the end:** each client's
  received bytes must equal the model's outgoing log, and the child's open
  fds must be the model's `reserved ∪ {3} ∪ open_fds`.
- A scenario stops at its first divergence (the two states no longer
  correspond), and the divergence is reported with the call, its inputs
  and both outputs.

`hol_check.py` turns a trace (`build/*.jsonl`) into a HOL script theory.
For each call it proves

```
ffi_sock_X2 conf bytes s = SOME (FFIreturn out s')
```

by EVAL. Here `out` is the C's real output, and s, s' are the
transcription's states before and after. So one EVAL checks both the C
and the transcription against the HOL model. The model's `lowest_free` is
defined with `LEAST`, so for accepts the script first proves the concrete
instance with `ffiModelTest`'s `lowest_free_intro` (all smaller fds used,
f not used), which EVAL can decide.

To run:

```
python3 ffi_model_test.py --seeds 60 --steps 500      # Python checks
python3 ffi_model_test.py --small --seeds 3 --steps 120 --log build/trace-small.jsonl
python3 hol_check.py build/trace-small.jsonl > ffiModelCheckScript.sml
Holmake -j1                                            # HOL checks
```

## 3. Known gaps between the C and the model (not exercised as divergences)

Each of these is outside what a single-process loopback test can trigger,
or is excluded on purpose:

1. **Misuse aborts.** On misuse (an fd of the wrong kind) the model's call
   fails (NONE) and the C aborts the process. Both "fail", so the tester
   only makes well-formed calls.
2. **Errors.** The model has no errors besides EOF. A read error such as
   ECONNRESET is reported as EOF. The tester's clients only shut down
   their write side, so no resets happen while the server reads.
3. **Writes.** The model's writes always succeed in full. The C loops
   `send` until done, which blocks while the client is not reading. The
   tester keeps writes ≤ 16000 bytes and drains the clients after each
   write. A partial write was never observed.
4. **Read sizes.** A read returns `TAKE n incoming`. On loopback, with the
   data already delivered, `recv` always returned exactly that (up to
   64 KiB of unread data per client were tested). A real network can
   deliver fewer bytes at a time, but that is a difference in *when* data
   arrives, which the model's schedule covers.
5. **Time.** Not a divergence: the 50 ms idle wait that `sock_poll` used
   to have was removed (PR #50, `spike/no-idle-wait`). It was unobservable
   here in any case, since the model has no time inside a poll.

## 4. Assumptions made

1. **Base: close-v2's `socket_ffi.c` and the version-2 model**, to cover
   all five calls. The version-1 model is the special case without close
   (and with fds named by the schedule).
2. **Settling time 10 ms** after client actions, before the poll that
   delivers them (loopback). If the kernel were slower than that, the
   result would be a spurious "not ready" divergence. None occurred.
3. **The HOL check runs on small-data traces in the build.** The
   full-size run was stopped for lack of memory (§1.1).
