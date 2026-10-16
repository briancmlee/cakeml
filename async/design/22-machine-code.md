# 22: Towards the machine-code theorem for the echo server

Status: **the source-level half is proved, and the in-logic compilation is
blocked on memory.**

- **Proved:** the whole echo program diverges, its I/O trace is the
  server's run against the socket model, and that trace satisfies
  EchoSpec's `echo_safe`. It is stated in the `semantics_prog` form that
  CakeML's compiler correctness theorem consumes.
- **Written, not run:** the in-logic compilation and the composition with
  `compile_correct`, as scripts that follow the base's examples
  (`machine-code/compile/`).
- **Why not run:** they need the CakeML compiler's backend proofs and
  cv_translator. Neither is built anywhere on this machine. Building them
  needs more memory than is free: swap was 12.6 GB used before I started
  and 15.6 GB of 16 GB at the end, all of it other processes. §3 has the
  numbers.
- **No CakeML lemma is missing** for the composition (§2): diverging
  programs and custom FFI parts are both covered.

There are no cheats, and `Holmake -j1` in `async/machine-code/` is green.
Branch `spike/machine-code`, from `spike/runnable` (PR #23). It **merges
`origin/spike/m4-safety`** (a902db27d: `echo_grun_ok`, `echo_fresh`,
`echo_comp_safe`). The merge was clean.

| file | contents |
|---|---|
| `runnable/asyncEchoMainScript.sml` (changed) | `echo_decs`, `echo_prog = SNOC (main_call «main») echo_decs` (the m3 shape), `echo_prog_eq` (as an explicit list); the export is unchanged (same S-expression) |
| `machine-code/asyncEchoSemanticsScript.sml` | `main_spec`, `echo_semantics`, `echo_prog_syntax_ok`, `echo_semantics_prog` |
| `machine-code/compile/` (not built) | `echoServerCompileScript.sml` (`eval_cake_compile_arm8`), `echoServerProofScript.sml` (the machine-code theorem), Holmakefile |

## 1. The program's semantics (proved)

The world is `socket_only_ffi s0` (ffiSpikeSocketDiv): the socket FFI
part alone (`sock_poll`, `sock_accept`, `sock_read`, `sock_write`), in
the initial state below. The server's run is the trace of M4's loop:

```
start_world s0 ⇔ s0.listeners = [(3w, [])] ∧ s0.conns = []
echo_trace s0 = LFLATTEN (LGENLIST
                  (λi. fromList (grounds_events (interest [3w]) (srelabel (server 3)) s0 i))
                  NONE)
```

- `start_world`: one listener, 3w, with nothing pending; no connections;
  any future arrivals `s0.sched`.
- `echo_trace`: round `i` performs the server's actions, then polls
  listener 3w and every connection accepted so far.

```
(* MAIN (helper): main () runs the event loop on the server: it never
   terminates, and its I/O trace is the server's run *)
main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app p main_v [uv] (SOCKETS_EV s0 []) (POSTd io. io = echo_trace s0)

(* MAIN: in a sockets-only world whose initial state has one listener, 3w,
   and no connections, the whole echo program diverges; its I/O trace is
   the server's run, and it satisfies EchoSpec's safety: on every
   connection, at every point, the bytes written are a prefix of the bytes
   read. *)
echo_semantics:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         echo_prog (Diverge io) ∧
       io = echo_trace s0 ∧ echo_safe io

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes *)
echo_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env echo_prog
    (Diverge (echo_trace s0)) ∧
  echo_safe (echo_trace s0)
```

How the proofs go:

- **`main_spec`** combines three existing results: `sserver_spec` (the
  server value implements `srelabel (server 3)`), `run_i_spec` (the loop's
  divergence and trace), and `echo_grun_ok` (no misuse: it discharges
  `run_i_spec`'s side condition for the server).
- **`echo_semantics`** follows `asyncM3Example`'s `m3_semantics`
  (`call_main_thm_div`, `sonly_init_heap`), plus `echo_comp_safe` for the
  trace.
- **`echo_semantics_prog`** adds `prog_syntax_ok echo_prog` (by
  evaluation) and `prog_syntax_ok_semantics`.

`echo_prog` is exactly the program exported in `21-runnable.md`: the
basis, then 21 declarations, then `main ()`. `echo_server.sexp` is
unchanged.

## 2. The machine-code theorem (scripts written, not run)

`compile/echoServerCompileScript.sml` follows
`examples/compilation/x64/echoCompileScript.sml` for arm8:

```
Theorem echo_server_compiled = eval_cake_compile_arm8 "" echo_prog_eq "echo_server.S";
```

`compile/echoServerProofScript.sml` follows `proofs/echoProofScript.sml`,
with `semantics_prog_Diverge_not_Fail` in place of
`semantics_prog_Terminate_not_Fail`. The intended final statement has the
shape of CakeML's standard machine-code theorems (`echo_compiled_thm`,
`cake_compiled_thm`):

```
(* MAIN: the arm8 machine code of the echo server, installed in an arm8
   machine and run against the socket world socket_only_ffi s0 (one
   listener 3w, no connections), behaves as the program: it diverges with
   I/O trace echo_trace s0 (or stops early because it ran out of
   resources), and that trace satisfies EchoSpec's echo_safe. *)
echo_server_compiled_thm:
  start_world s0 ∧ is_arm8_machine_config mc ∧
  installed echo_server_code cbspace echo_server_data data_sp
    echo_server_config.lab_conf.ffi_names
    (heap_regs arm8_backend_config.stack_conf.reg_names) mc
    echo_server_config.lab_conf.shmem_extra ms ⇒
  machine_sem mc (socket_only_ffi s0) ms ⊆
    extend_with_resource_limit {Diverge (echo_trace s0)} ∧
  echo_safe (echo_trace s0)
```

`echo_server_code`, `echo_server_data` and `echo_server_config` are the
names `eval_cake_compile_arm8` defines for the compiled bytes, data and
configuration. The exact names come out of the run.

**Nothing is missing from CakeML** for this composition:

- `compile_correct` (backendProof) is generic in the FFI state type, so the
  socket model `socket_only_ffi s0` can be used directly.
- `ffi_names` are computed from the program by the compiler, so the four
  `sock_*` names are included automatically.
- `semantics_prog_Diverge_not_Fail` (semanticsProps) gives `¬Fail` and the
  singleton behaviour for diverging programs.
- `prog_syntax_ok_semantics` (ml_prog) bridges CF's `semantics_dec_list`.
- `arm8_backend_config_ok`, `arm8_machine_config_ok` and `arm8_init_ok`
  (arm8_configProof) are the target facts.

What the theorem still leaves trusted, as for every CakeML machine-code
theorem:

- the C side implementing the socket FFI as `socket_only_ffi`'s oracle
  (`socket_ffi.c`, 21 §3);
- the assembler and linker;
- `is_arm8_machine_config` (the hardware model) and the OS loading the
  code (`installed`).

Two notes on the statement:

- **Resource limits.** Any early stop because resources ran out is a
  prefix of `echo_trace s0`. `echo_safe` holds for every finite prefix by
  definition, so it carries over to those behaviours too.
- **The oracle is sockets only.** The program also contains the basis,
  whose FFI calls are never made in this run (the theorem's trace has
  only socket events). So `socket_only_ffi` is enough, and no combined
  basis+socket oracle is needed.

## 3. Why the compilation was not run, and what it takes

**Needed in the base**, none of it built anywhere on this machine:

- `compiler/backend/proofs` (`backendProof`: `compile_correct`) and its
  ancestors, i.e. the whole compiler backend and its proofs;
- `compiler/backend/arm8/proofs` (`arm8_configProof`) and
  `compiler/encoders/arm8/proofs`;
- `semantics/proofs` (`semanticsProps`);
- `cv_translator` (`backend_arm8_cv`, `cake_compile_heap`).

**Measured costs**, from CakeML's regression job 3479, the build behind
release v3479 (machine "timtam", started Aug 24 21:10):

| step | regression figure |
|---|---|
| compiler proofs closure (`compiler/proofs`, which includes `backendProof` and its ancestors) | finished 1h20m51s after the start, **10 GB** peak |
| `compiler/encoders/arm8/proofs` | 8m03s, 3 GB |
| `cv_translator` | 5m18s, 3 GB |
| in-logic compilation of basis-sized programs (`examples/compilation/x64`, 8 programs) | 9m03s, 4 GB |
| their machine-code theorems (`examples/compilation/x64/proofs`) | 3m44s, 4 GB |

- The regression machine builds directories in parallel on many cores, so
  its wall-clock times understate a `-j1` build. Its memory figures are
  per directory step.
- **Estimate for this machine at `-j1`** (M1 Pro): roughly 6–12 hours for
  the compiler proofs closure, then about 30 minutes for cv_translator plus
  this program's compilation and proof. Peak memory is 4–10 GB for the
  largest single theories.
- This estimate is extrapolated from the figures above, not measured here.

**Memory on this machine during the task** (16 GB, shared with three other
workers):

- `vm.swapusage`: 12.6 GB of 14.3 GB used before I started, which is
  already above the agreed 12 GB stop threshold. It was 15.6 GB of
  16.4 GB at the end.
- `memory_pressure` reported 32–38% free throughout.
- My own builds were small `-j1` theory builds, about 1–2 GB each.

A 10 GB-peak build would push the machine into heavy swapping, so I did
not start it.

**To finish:**

1. On a machine with ≥ 16 GB free (or with the other workers paused),
   build the compiler closure:
   `Holmake -j1` in `cv_translator` (it builds `cake_compile_heap` and
   pulls in the backend), then in `compiler/backend/proofs`,
   `compiler/backend/arm8/proofs` and `semantics/proofs`.
2. Run `Holmake` in `async/machine-code/compile/`. Expect small fixes,
   since the scripts are unrun: the names `eval_cake_compile_arm8`
   defines, and whether it wants `echo_prog_eq` or a plain `_def`.
3. Optionally link `echo_server.S` from step 2 with `socket_ffi.c` and the
   base's `basis_ffi.c`. That would replace the release compiler and the
   S-expression bridge of 21 §1 with the verified in-logic output.

Also noted: CakeML's regression queue currently shows a branch
`didriklundberg:socketio`. Upstream may be adding socket I/O to the basis,
which could later replace this project's socket FFI part.

## 4. Assumptions made

1. **The base branch is `spike/runnable`, merged with
   `origin/spike/m4-safety`** for `echo_grun_ok` and `echo_comp_safe`.
2. **The world is `socket_only_ffi s0`**, M3's oracle with only the socket
   part, because the program makes no basis FFI calls at run time. A
   combined basis+socket oracle would be needed only for programs that
   also use the basis I/O.
3. **The initial world is `start_world s0`**: listener 3w, no
   connections, any schedule. This is EchoSpec's `server_world` shape, and
   it matches what `socket_ffi.c` sets up.
4. **`echo_prog` was restructured** to `SNOC (main_call «main»)
   echo_decs`, the m3 shape. `call_main_thm_div` applies directly, and the
   exported program is unchanged.
5. **The scripts in `compile/` are kept but not built**, with a Holmakefile
   that names their requirements. They are clearly marked as not run.
