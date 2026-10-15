# Design notes

The numbered notes record the decisions behind each layer, in the order
they were made. They were written on the spike branches, so the paths
they mention are the spike layout. The table at the end maps old
directories to new ones. The notes are kept unedited, as the "why" behind
the code.

| layer (review PR) | notes |
|---|---|
| 1. the trusted surface | 16-final-spec, 24-http-headers, 27-http-nobody, 07-socket-model §1–3 |
| 2. the async model | 01-semantics §1–5, REVIEW-GUIDE (H1–H7) |
| 3. recursion, Level 2, scheduler | 01-semantics §6–7, 06-scheduler, REVIEW-GUIDE (H8–H14) |
| 4. the echo server in the model | 08-echo-server, 09-closed-loop |
| 5. the library in CakeML | 02-cf-feasibility, 03-cf-loop, 05-cf-actions, 10-cf-reactive, 15-m4-server §1 |
| 6. sockets, divergence, the event loop | 04-ffi-integration, 07-socket-model, 11-cfdiv-multipart, 13-m3-assembly |
| 7. the echo program | 15-m4-server, 17-m4-safety, 21-runnable §1, 22-machine-code, 19-m4-liveness |
| 8. the blocking refinement | 14-l2-blocking, 25-l2-blocking-stuck, 17-m4-blocking, 24-blocking-runnable §6 (the live-fd loop) |
| 9. HTTP | 18-http-model, 20-http-impl, 23-http-safety, 24-http-headers, 25-http-liveness, 26-http-liveness-h, 27-http-nobody |
| 10. it runs | 21-runnable, 24-blocking-runnable, 22-machine-code §3 |

Two notes share number 25: they were written in parallel. Note 24 §4
describes the trusted C's 50 ms idle wait in `sock_poll`; it has since
been removed (21, update), so `socket_ffi.c` does exactly what the model
says.

Not in the series, but kept on the spike branches: the world-as-async
experiment (note 12, `spike/world-as-async`, `spike/world-async-multi`),
the HANDOFF notes, and the worker conventions.

## Old paths → new paths

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
| `runnable/`, `blocking-runnable/`, `http-headers/` (demo), `machine-code/compile/` | `runnable/{echo,echo-blocking,http,machine-code}/` |
