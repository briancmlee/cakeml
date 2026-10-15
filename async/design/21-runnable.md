# 21: The verified echo server, running

Status: **tasks 1–6 done.** The verified echo program compiles with the
official CakeML release compiler and runs natively on the M1. Concurrent
clients each get back exactly their own lines. There are no cheats, and
`Holmake` in `async/runnable/` is green. Branch `spike/runnable`, from
`origin/spike/m4-safety` (c304a8159). That is the branch with the most
complete echo program: the socket-vocabulary server with `sserver_spec`,
under M4's dynamic-interest loop from spike/m4-liveness. **PR base:
`spike/m4-safety`.** The new work only depends on that branch, so the diff
is just `async/runnable/` and the write-up.

| file | lines | contents |
|---|---|---|
| `asyncEchoMainScript.sml` | 68 | `main`, the whole program `echo_prog`, the export to `echo_server.sexp` |
| `sexpV3479Lib.sml` | 255 | release v3479's S-expression printer, adapted to the current AST |
| `socket_ffi.c` | 189 | **trusted**: the socket FFI, and the listener |
| `Makefile` | | compile with the release `cake`, link, demo |
| `demo_clients.py` | | demo, benchmark, asyncio baseline (not trusted: it only drives the server) |
| `check_printer.sh` | | cross-check of the printer against the official one |
| `echo_server.sexp` | (20 KB) | the exported program (generated, committed) |
| `demo-transcript.txt` | | the demo artefact |

## 1. The program, and getting it out of HOL (task 1)

The program is spike/m4-safety's `asyncM4SockServer` translation state:

- the basis;
- `Socket` (`ffiSpikeSocketProg`), whose four functions each make one
  FFI call;
- the Async library (`asyncM3Prog`: `return`, `poll`, `wait`, `emit`,
  `bind`, plus `async_both`/`async_map`);
- the event loop with a growing interest list (`asyncM4Loop`:
  `add_accepted`, `step_i`, `run_i`);
- the echo server in the socket vocabulary (`handler`, `server`, which
  implement `relabel sfa sfs (server lfd)`).

The only additions are

```sml
fun main u = run_i ([3], server 3);
main ();
```

`ml_progLib` cannot add `val _ = e` for a non-value `e`, so the call is
appended to the declaration list, as CakeML's examples do. `echo_prog_def`
is the whole program as a HOL term.

**Why an S-expression in v3479's format.** The newest release, v3479
(2026-08-26), is 429 commits behind the frozen base, and the AST changed
in between:

- `Var` was renamed `Ident`;
- locations are a new type;
- `Shift` moved into `arith`;
- new ops (`Aw8subBit`, `Strsub_unsafe`, …) and `Open`/`Dopen` were added.

So neither the base's S-expression printer nor its basis can be fed to
v3479. Concrete source is not a way around it either: translated code
uses primitive ops (`App (Arith Add IntT) …`), which have no concrete
syntax.

What I did:

- Export **only the declarations after the basis**. The script checks
  that the program starts with exactly `basisProg`'s `basis`, then drops
  it. The release compiler adds its own basis.
- Print them with **v3479's own printer**, adapted (`sexpV3479Lib`):
  - `Ident` is printed as `Var`;
  - every location is printed as `(unk unk)`;
  - printing **fails** if the program contains any construct v3479
    lacks. Ours contains none.
- **Cross-check** (`check_printer.sh`): the base's official printer
  (`unverified/sexpr-bootstrap/astToSexprLib.sml`), applied to the same
  declarations, gives byte-identical output once its locations and
  `Ident` are normalised. The release compiler then parses and
  type-checks the result.

## 2. The compiler (task 2)

- The CakeML release **v3479**: https://github.com/CakeML/cakeml/releases/tag/v3479,
  file `cake-arm8-64.tar.gz`.
- Downloaded and extracted into its own fresh directory,
  `~/.cache/cakeml-release/v3479/arm8/cake-arm8-64/`.
- `make cake` there links the release's `cake.S` with its `basis_ffi.c`,
  using the system `cc`.
- The arm8 compiler runs **natively** on the M1 (macOS 26.6.2), and so
  does the code it generates. Rosetta was not needed.
- The 2024 binaries in `~/Downloads` were not used: they predate several
  AST changes.
- Only the compiler binary is run from the extracted directory. Its
  `basis_ffi.c` is compiled as an input file and left unmodified.

## 3. The C side of the FFI (task 3; trusted)

`socket_ffi.c` is a separate file linked next to the release's unmodified
`basis_ffi.c`. Each function must behave as the model's `ffi_sock_*`
(`ffiSpikeSocketFFIScript.sml`) on the byte arrays:

| FFI name | model function | conf (input) | a (in/out) |
|---|---|---|---|
| `sock_poll` | `ffi_sock_poll` | k fds, 8 bytes each | k flags: 1 ready, 0 not |
| `sock_accept` | `ffi_sock_accept` | listener fd (8 bytes) | 9 bytes: status (1 accepted, 0 would block), new fd |
| `sock_read` | `ffi_sock_read` | connection fd (8) | status (0 data, 1 would block, 2 EOF), 8-byte count, data |
| `sock_write` | `ffi_sock_write` | fd (8) ++ data | unused |

- fds are 8-byte big-endian numbers.
- Ready (`is_ready`) maps to POSIX `POLLIN`, `POLLHUP` or `POLLERR`.
- **The listener.** The model's initial world has one listener, and the
  model has no operation that creates one. A constructor function creates
  it before `cml_main` runs, as fd 3 on 127.0.0.1, port
  `$CAKE_ECHO_PORT` (default 7777).
- **Where reality is outside the model.** Each item below is a trust
  assumption, and each is commented in the file.
  - *Errors.* The model has none beyond EOF:
    - a read error (`ECONNRESET`) is reported as EOF;
    - a write error (`EPIPE`) drops the data;
    - other accept errors are reported as "would block";
    - misuse that the model rejects (`EBADF`, `ENOTSOCK`) aborts the
      program, matching the FFI call failing in the model.
  - *Writes always succeed in full* in the model. Accepted sockets are
    blocking and `sock_write` loops until everything is sent. So a client
    that never reads stalls the server.
  - *Time.* The model's poll delivers one step of an arbitrary arrival
    schedule, so how long the real poll waits is unobservable in the
    model.
    - The C side waits only when the program is idle: no socket operation
      since the last poll, and the same ready set for 2 polls in a row.
      Then it waits at most 50 ms for a not-ready fd to become ready.
    - Two rounds are enough for this server: a wait registered in one
      round sees the next snapshot, and the server always follows a wait
      with an emit.
    - The benchmarks show no 50 ms stalls, and an idle server uses ~0%
      CPU.
    - (Later removed: `sock_poll` no longer waits at all, matching the
      model; see 24 §4.)
  - *Closing.* The model has no `close`, so fds are never closed. A
    finished connection stays in the interest list (the loop only adds),
    and it stays ready with EOF.

## 4. Building and running (task 4)

```
cd async/runnable
Holmake          # after ../m4-safety is built; writes echo_server.sexp (~35 s)
make             # cake --sexp=true --target=arm8 (<1 s); cc ... basis_ffi.c socket_ffi.c
make demo        # server + 3 concurrent clients + 1 late client; writes demo-transcript.txt
```

The transcript (`demo-transcript.txt`; timestamps from the start of the
demo):

```
[  0.000s] server   echo server: listening on 127.0.0.1:7777
[  0.000s] alice    connected
[  0.000s] alice    sent     'hello from alice'
[  0.000s] bob      connected
[  0.000s] bob      sent     'bob says hi'
[  0.000s] carol    connected
[  0.000s] carol    sent     'carol here'
[  0.001s] alice    received 'hello from alice'
[  0.001s] bob      received 'bob says hi'
[  0.001s] carol    received 'carol here'
[  0.110s] bob      sent     'bob: second line'
[  0.110s] bob      received 'bob: second line'
[  0.127s] carol    sent     'carol: ünïcödé bytes ✓'
[  0.127s] carol    received 'carol: ünïcödé bytes ✓'
[  0.154s] alice    sent     'alice: line 2'
[  0.154s] alice    received 'alice: line 2'
[  0.211s] bob      sent     'bob: third'
[  0.211s] bob      received 'bob: third'
[  0.253s] carol    sent     'carol: last'
[  0.253s] carol    received 'carol: last'
[  0.314s] alice    sent     'alice: line 3'
[  0.314s] alice    received 'alice: line 3'
[  0.321s] bob      sent     'bob: fourth'
[  0.321s] bob      received 'bob: fourth'
[  0.375s] carol    closed
[  0.430s] bob      closed
[  0.465s] alice    closed
[  0.465s] dave     connected
[  0.465s] dave     sent     'dave arrives after the others left'
[  0.465s] dave     received 'dave arrives after the others left'
[  0.465s] dave     closed
[  0.466s] server   terminated (the server loop runs forever; stopped with SIGTERM)
[  0.466s] check    carol: received exactly its own lines: True
[  0.466s] check    bob: received exactly its own lines: True
[  0.466s] check    alice: received exactly its own lines: True
[  0.466s] check    dave: received exactly its own lines: True
```

Plain `nc 127.0.0.1 7777` works too: every line typed is echoed back.

## 5. Numbers (task 5; indicative only)

Setup:

- Apple M1 Pro, macOS 26.6.2, loopback.
- `demo_clients.py bench`: N client threads, each sending M lines of
  64 bytes, one line in flight per client.
- Baseline: a trivial Python 3.11 asyncio echo server (`demo_clients.py
  asyncio-server`).
- The client is Python threads, so at high load it is probably part of
  the bottleneck. Treat the numbers as a rough comparison, not a
  measurement of the servers alone.

| server | clients × lines | lines/s | round trip median | p99 | max |
|---|---|---|---|---|---|
| CakeML (verified) | 1 × 5000 | 17,161 | 49 µs | 140 µs | 6.4 ms |
| Python asyncio | 1 × 5000 | 28,220 | 34 µs | 54 µs | 0.15 ms |
| CakeML (verified) | 10 × 1000 | 32,204 | 289 µs | 646 µs | 2.1 ms |
| Python asyncio | 10 × 1000 | 52,900 | 166 µs | 488 µs | 2.4 ms |
| CakeML (verified) | 50 × 200 | 35,175 | 1,332 µs | 4,343 µs | 15.7 ms |
| Python asyncio | 50 × 200 | 51,610 | 830 µs | 2,773 µs | 4.9 ms |

The verified server reaches about 60–70% of asyncio's throughput. Known
costs, none of them fundamental:

- one FFI call per action;
- the ready set is a list, scanned per waiting handler;
- the computation value is rebuilt every round;
- the interest list only grows;
- each echoed chunk takes three rounds: read, then write, then the next
  wait.

## 6. Getting CakeML's in-logic machine-code theorem (later)

The base's `examples/compilation/x64/echoCompileScript.sml` and
`proofs/echoProofScript.sml` (for the basis echo, `echo_compiled_thm`)
show the route. For this program it would take:

1. **Compile in the logic, with the base's compiler:**
   `eval_cake_compile_arm8 "" echo_prog_def "echo_server.S"`, or the x64
   variant (`cv_translator/eval_cake_compile_*Lib`). This compiles
   `echo_prog`, basis included, with the base's own verified compiler,
   which replaces both the v3479 release and the S-expression bridge. It
   gives `echo_compiled`: the compiler's output equals specific code and
   data, and the program is syntactically ok.
   - Cost: the basis examples take tens of minutes and a few GB of memory.
   - Estimate: about 20 lines plus build time.
2. **A semantics theorem for the whole program** in the form
   `compile_correct` takes. The server diverges, so this is the
   divergence route of `13-m3-assembly.md` (`m3_semantics`) on the
   dynamic-interest loop: `run_i_spec` lifted to
   `semantics_prog … (Diverge io_trace)` for the program's initial state.
   - One gap: the FFI oracle. `compile_correct` is generic in the FFI,
     but the program also calls the basis's FFI parts (none at run time),
     so the semantics must be stated over the basis oracle combined with
     the socket part (`sockets_ffi_part`, as `basis_ffi` does for its
     parts).
   - This is the same statement the m4-liveness/m4-safety assembly is
     building towards (EchoSpec's `echo_safe` and `echo_live` are about
     this trace).
   - Estimate: about 150–250 lines on top of that assembly.
3. **Compose**, as `echoProof` does: `compile_correct` with
   `arm8_backend_config_ok`, `arm8_machine_config_ok` and `arm8_init_ok`.
   The result is that the machine-code behaviour is the program's
   divergent socket trace, up to running out of resources (`extend_with_resource_limit`).
   - Estimate: about 40 lines.
   - The trusted base would then be: the C side (§3), the assembler and
     linker, the OS, and the hardware model. The release compiler and the
     S-expression bridge drop out.

## 7. Assumptions made

1. **Base branch.** `spike/m4-safety`, which has the dynamic-interest loop
   program (it merges spike/m4-liveness). PR base `spike/m4-safety`;
   `spike/http-impl` is not needed.
2. **The release compiler v3479** compiles the declarations after the
   basis, adding its own basis (the S-expression bridge in §1). The base's
   basis is not used at run time. Our declarations only use basis names
   (`List.length`, `Word8Array.*`, `String.explode`, …) that are the same
   in v3479. Type inference passing on the program shows the names
   resolve.
3. **arm8, native.** It was the simplest route that worked.
4. **The listener is created by C, as fd 3**, so the CakeML program
   matches the model's initial world.
5. **The C side's idle wait** (§3) is a scheduling choice that is
   unobservable in the model. (Later removed; see 24 §4.)
