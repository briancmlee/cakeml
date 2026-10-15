# Handoff: the verified echo server, running (spike/runnable)

Kept current at every commit.

## Where things are

- Branch `spike/runnable`, from `origin/spike/m4-safety` (c304a8159), the
  branch with the most complete echo program: the socket-vocabulary echo
  server (asyncM4SockServer, `sserver_spec`) under the dynamic-interest
  loop (asyncM4Loop, merged in from spike/m4-liveness).
- `async/runnable/`:
  - `asyncEchoMainScript.sml`: adds `fun main u = run_i ([3], server 3)`
    and the call `main ()`. It checks that the program starts with the
    basis, and writes the declarations after the basis to
    `echo_server.sexp` (committed, 20 KB, generated).
  - `sexpV3479Lib.sml`: release v3479's own S-expression printer, adapted
    to the current AST. It fails on constructs v3479 lacks.
  - `socket_ffi.c`: TRUSTED. The four socket FFI calls, plus the listener
    as fd 3, with a mapping table to the model's `ffi_sock_*`.
  - `Makefile`: `make` compiles with the release cake and links;
    `make demo` runs the demo.
  - `demo_clients.py`: the demo (3 concurrent clients plus a late 4th),
    the benchmark, and an asyncio baseline server.
  - `demo-transcript.txt`: the recorded demo.
- Compiler: the CakeML release **v3479**
  (https://github.com/CakeML/cakeml/releases/tag/v3479,
  `cake-arm8-64.tar.gz`), extracted under
  `~/.cache/cakeml-release/v3479/arm8/`. `cake` is built there by the
  release's own Makefile (`make cake`), and runs natively on the M1.

## How to rebuild

    cd async/runnable
    Holmake            # needs ../m4-safety etc. built; writes echo_server.sexp
    make               # cake --sexp=true --target=arm8; cc with basis_ffi.c + socket_ffi.c
    make demo          # writes demo-transcript.txt

## Status

- DONE: export, compile, run, demo transcript.
- IN PROGRESS: benchmarks, 21-runnable.md, PR.

## Assumptions made

1. The compiler is the latest release (v3479, 429 commits behind the
   frozen base). The base's AST has changed since, so the export uses
   v3479's S-expression format for the non-basis declarations, and the
   release compiler adds its own basis.
2. The listener is created by C before `cml_main`, as fd 3. The socket
   model starts with a listener and has no operation for creating one.
3. The arm8 target runs natively; x64 under Rosetta was not needed.

## Tool feedback

- `ml_progLib.add_dec` rejects `val _ = e` with a non-value `e`. Use
  `fun main u = ...` and append the call to the exported program instead.
