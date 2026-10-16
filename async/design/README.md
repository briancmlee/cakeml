# Design notes

The numbered notes record the decisions behind each layer, in the order
they were made. They were written on the spike branches, so the paths
they mention are the spike layout. The table at the end maps old
directories to new ones. The notes are kept unedited, as the "why" behind
the code.

| layer (review-v2 PR) | notes |
|---|---|
| 01. the trusted surface | 16-final-spec, 28-http-bodies §1, 24-http-headers, 27-http-nobody, 07-socket-model §1–3; `spec-rfc/README.md`; QuietSpec: `../quiet/README.md` §0–1 |
| 02. the async model | 01-semantics §1–5, REVIEW-GUIDE (H1–H7) |
| 03. recursion, Level 2, scheduler | 01-semantics §6–7, 06-scheduler, REVIEW-GUIDE (H8–H14) |
| 04. the echo server in the model | 08-echo-server, 09-closed-loop |
| 05. the library in CakeML | 02-cf-feasibility, 03-cf-loop, 05-cf-actions, 10-cf-reactive, 15-m4-server §1 |
| 06. sockets, divergence, the event loop | 04-ffi-integration, 07-socket-model, 11-cfdiv-multipart, 13-m3-assembly |
| 07. the echo program | 15-m4-server, 17-m4-safety, 21-runnable §1, 22-machine-code, 19-m4-liveness |
| 08. the blocking refinement | 14-l2-blocking, 25-l2-blocking-stuck, 17-m4-blocking, 24-blocking-runnable §6 (the live-fd loop) |
| 09. liveness from the library | 34-library-liveness, 25-http-liveness, 26-http-liveness-h (the skeleton's progress) |
| 10. HTTP as a protocol instance | 32-modular-parsing (the generic pipeline), 28-http-bodies (the instance), 18-http-model, 20-http-impl, 23-http-safety, 24-http-headers, 27-http-nobody |
| 11. quiescence, and option C | `../quiet/README.md` (design/33: the two spins, select on the declared interest, the result) |
| 12. it runs | 21-runnable, 24-blocking-runnable, 22-machine-code §3 |
| 13. close and fd reuse | 25-echospec2 |

The notes for layers 09 and 10 that describe the copied HTTP pipelines
(18, 20, 23–28) are the history of the instance: the copies themselves are
retired to `archive/http-copies`.

Three notes share number 25: they were written in parallel.

The trusted C's 50 ms idle wait in `sock_poll` (21 §3, 24 §4) has since
been removed (PR #50), so `socket_ffi.c` does exactly what the model says.
The version of note 24 here is the one from the live-fd fix (#46), written
before that removal; 21's "see 24 §4" refers to #50's revision of note 24,
on `spike/no-idle-wait`.

Design notes for work after the series (on their spike branches): 30-http-kv,
35-endpoint-world, 36-honest-ffi (`spike/honest-ffi`, #94), 37 (stateful
quiescence, `spike/quiet-store`).

Not in the series, but kept on the spike branches: the world-as-async
experiment (note 12, `spike/world-as-async`, `spike/world-async-multi`),
the HANDOFF notes, and the worker conventions.

## Old paths → new paths

The rows for `programs/http`, `programs/http-h`, `programs/http-b` and `runnable/http` describe the first series. In v2 those directories are retired (`archive/http-copies`), and the last rows give the v2 additions.

| spike directory | review layout |
|---|---|
| `spec/` | `spec/` |
| `ffi-spike/ffiSpikeSocket{FFI,Fair}` | `world/sockets/` |
| `ffi-spike/ffiSpikeSocket{Prog,Proof,Select}` | `world/sockets/` |
| `ffi-spike/ffiSpikeClock*` | `world/clock/` |
| `ffi-spike/ffiSpike{SocketWorld,DivMain,DivMulti,SocketDiv}` | `world/composed/` |
| `model/` | `model/{core,level2,sched,examples}/`, `servers/{echo,closed-loop}/` |
| `cf-spike/asyncCfDet`, `cf-actions/`, `cf-reactive/` | `cakeml/library/` |
| `m4-server/asyncM4Approx` | `cakeml/approx/` |
| `m4-server/asyncM4{ServerUses,Relabel}`, `m4-common/asyncM4RelabelDist` | `servers/{echo,relabel}/` |
| `m3-assembly/`, `m4-common/asyncM4{GRounds,Loop,SockInv,GTrans}` | `loop/polling/` |
| `m4-common/asyncM4{SockModel,EchoRunOk,EchoSafe}`, `m4-safety/`, `runnable/asyncEchoMain`, `machine-code/asyncEchoSemantics` | `programs/echo/` |
| `m4-liveness/` | `programs/echo-live/` |
| `m4-echospec/`, `m4-echospec-live/`, `headline/` | `headline/` |
| `l2-blocking/` | `loop/blocking-l2/` |
| `m4-blocking/` | `loop/blocking/`, `programs/echo-blocking/` |
| `m4-blocking-live/` (its `asyncM4LiveWorld` renamed `asyncM4BlkSelWorld`) | `programs/echo-blocking/` |
| `http-model/`, `http-safety/asyncServerWithUses`, `http-headers/asyncHttp{Parse,Server}H` | `servers/http/` |
| `http-impl/asyncHttpImplProg`, `m4-server/asyncM4ServerProg`, `http-safety/` | `programs/http/` |
| `http-headers/` (the rest) | `programs/http-h/` |
| `http-liveness/asyncSWProgress`, `http-liveness-h/` | `servers/http/`, `programs/http-h/`, `headline/` |
| `http-bodies/` | `servers/http/` (parser, server, machine, drain), `programs/http-b/`, `headline/`, `runnable/http-bodies/` |
| `runnable/`, `blocking-runnable/`, `http-headers/` (demo), `machine-code/compile/` | `runnable/{echo,echo-blocking,http,machine-code}/` |
| `library-liveness/`, `http-liveness/asyncSWProgress` (skeleton) | `servers/{skeleton,library-liveness,http}/` |
| `http-proto/`, `http-proto-inst/` | `servers/{proto,proto-inst}/`, `programs/{proto,http-pb}/` |
| `spec-rfc/` | `spec-rfc/` |
| `quiet/`, `option-c/library` | `quiet/{ffi,echo}/`, `cakeml/level2/` |
| `option-c-proto/`, `option-c-loop/`, `option-c-final/`, `proto-stable/` | `servers/{level2-proto,proto-stable}/`, `programs/{http-level2,http-quiet}/`, `loop/select-interest/` |
| `close-v2-*/`, `spec/EchoSpec2`, `world/sockets-v2*` | `spec-v2/`, `world/sockets-v2(-cf)/`, `loop/handles/`, `programs/echo-v2/`, `headline/` |
