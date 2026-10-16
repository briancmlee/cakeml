# The final series, L0 (core): the file map

Generated from review-v2/14-docs (c4f5abaeb). Theory names are unchanged here; the rename (design/NAMES.md) is a later, separate commit per level. Each layer `final/NN-<name>` adds the directories below on top of the previous layer. INCLUDES in every Holmakefile are generated from the transitive ancestors.

Not in L0: `spec-v2`, `world/sockets-v2`, `world/sockets-v2-cf`, `loop/handles`, `programs/echo-v2`, `headline/asyncHLEchoSpec2` (L1, lifetimes); `design/` and the review-v2 READMEs (docs); chat (an appendix). The KV part of 0.9 is a placeholder until `kv_spec 3w kv_prog` lands.

Departures from the proposal (§4), forced by the dependency graph:
- `cakeml/level2` is in 06, not 05: it builds on `loop/blocking-l2`.
- `loop/blocking` is in 07, not 06: it builds on the echo program's server model (`asyncM4SockServer`).
- `loop/select-interest` is in 10, not 06: it builds on the HTTP Level 2 programs and the quiet echo theories.
- The generic skeleton is split: model-level (`asyncServerWith`, `asyncServerWithUses`, `asyncSWProgress`, `asyncServerV`, `asyncServerVProgress`, with the strict HTTP model `asyncHttpParse`, `asyncHttpServer` that `asyncServerWithUses` instantiates) in 04 for isolation; socket-level (`asyncRunOkGen`, `asyncSWSock`) in 08 with library liveness.
- `world/sockets` is split: the trusted model (`ffiSpikeSocketFFI`, `ffiSpikeSocketFair`) in 01; its CakeML module (`ffiSpikeSocketProg`, `ffiSpikeSocketProof`, `ffiSpikeSocketSelect`) in 06 as `world/sockets-cf`.

## final/01-trusted-surface: the trusted surface

| new dir | theories | from (review-v2) |
|---|---|---|
| `spec` | `EchoSpec`, `EchoSpecBite`, `HttpSpec`, `HttpSpecBite`, `HttpSpecBodies`, `HttpSpecBodiesBite`, `HttpSpecHeaders`, `HttpSpecHeadersBite`, `QuietSpec`, `QuietSpecBite` | `spec` |
| `spec-rfc` | `HttpSpecBodiesTchar`, `rfc9112Framing`, `rfcAgree`, `rfcAgreeValid` | `spec-rfc` |
| `world/sockets` | `ffiSpikeSocketFFI`, `ffiSpikeSocketFair` | `world/sockets` |

## final/02-model-core: the async model

| new dir | theories | from (review-v2) |
|---|---|---|
| `model/core` | `asyncChoose`, `asyncCore`, `asyncLevel1`, `asyncLoop` | `model/core` |

## final/03-loops-level2-sched: recursion, Level 2, the scheduler

| new dir | theories | from (review-v2) |
|---|---|---|
| `model/examples` | `asyncEcho`, `asyncEcho2`, `asyncIdle`, `asyncIdle2` | `model/examples` |
| `model/level2` | `asyncLevel2`, `asyncLoop2`, `asyncTranscript` | `model/level2` |
| `model/sched` | `asyncSched`, `asyncSched2` | `model/sched` |

## final/04-servers-model: servers in the model (with isolation)

| new dir | theories | from (review-v2) |
|---|---|---|
| `servers/closed-loop` | `asyncClosedLoop`, `asyncLiveness`, `asyncProgress`, `asyncWorld` | `servers/closed-loop` |
| `servers/echo` | `asyncM4ServerUses`, `asyncServer`, `asyncServer2`, `asyncServerSafety` | `servers/echo` |
| `servers/http-model` | `asyncHttpParse`, `asyncHttpServer` | `servers/http` |
| `servers/relabel` | `asyncM4Relabel`, `asyncM4RelabelDist` | `servers/relabel` |
| `servers/skeleton` | `asyncSWProgress`, `asyncServerV`, `asyncServerVProgress`, `asyncServerWith`, `asyncServerWithUses` | `servers/http`, `servers/library-liveness`, `servers/skeleton` |

## final/05-cakeml-library: the library in CakeML

| new dir | theories | from (review-v2) |
|---|---|---|
| `cakeml/approx` | `asyncM4Approx` | `cakeml/approx` |
| `cakeml/library` | `asyncCfActBoth`, `asyncCfActBothModel`, `asyncCfActModel`, `asyncCfActProg`, `asyncCfActSpec`, `asyncCfActWorld`, `asyncCfChoose`, `asyncCfChooseModel`, `asyncCfDet`, `asyncCfReactWorld` | `cakeml/library` |

## final/06-sockets-loops: sockets, divergence, loops

| new dir | theories | from (review-v2) |
|---|---|---|
| `cakeml/level2` | `asyncL2LibApprox`, `asyncL2LibModel`, `asyncL2LibProg`, `asyncL2LibSpec` | `cakeml/level2` |
| `loop/blocking-l2` | `asyncL2BlkFfi`, `asyncL2BlkLoop`, `asyncL2BlkModel`, `asyncL2BlkProg`, `asyncL2BlkSpec`, `asyncL2BlkStuck`, `asyncL2BlkWorld` | `loop/blocking-l2` |
| `loop/polling` | `asyncM3Loop`, `asyncM3Prog`, `asyncM3World`, `asyncM4GRounds`, `asyncM4GTrans`, `asyncM4Loop`, `asyncM4SockInv` | `loop/polling` |
| `world/clock` | `ffiSpikeClockFFI`, `ffiSpikeClockProg`, `ffiSpikeClockProof`, `ffiSpikeClockWorld` | `world/clock` |
| `world/composed` | `ffiSpikeDivMain`, `ffiSpikeDivMulti`, `ffiSpikeSocketDiv`, `ffiSpikeSocketWorld` | `world/composed` |
| `world/sockets-cf` | `ffiSpikeSocketProg`, `ffiSpikeSocketProof`, `ffiSpikeSocketSelect` | `world/sockets` |

## final/07-echo-program: the echo program (and the blocking refinement)

| new dir | theories | from (review-v2) |
|---|---|---|
| `headline` | `asyncM4EchoSpec`, `asyncM4EchoSpecSafe` | `headline` |
| `loop/blocking` | `asyncM4BlkLoop`, `asyncM4BlkTrace`, `asyncM4BlkWorld` | `loop/blocking` |
| `programs/echo` | `asyncEchoMain`, `asyncEchoSemantics`, `asyncM4EchoRunOk`, `asyncM4EchoSafe`, `asyncM4SockApprox`, `asyncM4SockModel`, `asyncM4SockServer` | `programs/echo` |
| `programs/echo-blocking` | `asyncM4BlkEcho`, `asyncM4BlkMain`, `asyncM4BlkSelWorld`, `asyncM4LiveEcho`, `asyncM4LiveLoop`, `asyncM4LiveMain`, `asyncM4LiveServer` | `programs/echo-blocking` |
| `programs/echo-live` | `asyncM4AcceptSoon`, `asyncM4Account`, `asyncM4Drain`, `asyncM4EchoLive`, `asyncM4LiveProg`, `asyncM4LiveWorld`, `asyncM4Queue`, `asyncM4ReadSoon`, `asyncM4Sched` | `programs/echo-live` |

## final/08-library-liveness: liveness from the library

| new dir | theories | from (review-v2) |
|---|---|---|
| `servers/library-liveness` | `asyncEchoLiveLib`, `asyncRunOkGen`, `asyncSWSock`, `asyncServerVLive`, `asyncServerVLiveA`, `asyncServerWithLive`, `asyncServerWithLiveFlat` | `servers/library-liveness`, `servers/skeleton` |

## final/09-protocols: protocols as instances (HTTP; KV placeholder)

| new dir | theories | from (review-v2) |
|---|---|---|
| `programs/http-pb` | `asyncProtoProgB`, `asyncProtoSemB` | `programs/http-pb` |
| `programs/proto` | `asyncProtoMain`, `asyncProtoProg`, `asyncProtoSockModel`, `asyncProtoSockSpec` | `programs/proto` |
| `servers/http` | `asyncHttpParseB`, `asyncHttpParseBExt`, `asyncHttpParseH`, `asyncHttpParseHExt` | `servers/http` |
| `servers/proto` | `asyncProto`, `asyncProtoDrain`, `asyncProtoEnvLive`, `asyncProtoLive`, `asyncProtoMachine`, `asyncProtoSafe`, `asyncProtoServer`, `asyncProtoV` | `servers/proto` |
| `servers/proto-inst` | `asyncProtoB`, `asyncProtoH`, `asyncProtoStrict` | `servers/proto-inst` |
| `programs/kv` | (placeholder) | KV: spike/kv-live (#95: `kv_live_rounds`), the KV worker's `kv_spec 3w kv_prog` |

## final/10-quiescence: quiescence (select on the declared interest)

| new dir | theories | from (review-v2) |
|---|---|---|
| `loop/select-interest` | `asyncOCAcc`, `asyncOCFinite`, `asyncOCLoop`, `asyncOCRun`, `asyncOCSel`, `asyncOCSleeps`, `asyncOCTrace` | `loop/select-interest` |
| `programs/http-level2` | `asyncOCApprox`, `asyncOCModel`, `asyncOCProg`, `asyncOCProtoModel`, `asyncOCProtoProg`, `asyncOCProtoSpec`, `asyncOCRelabel`, `asyncOCSpec` | `programs/http-level2` |
| `programs/http-quiet` | `asyncOCMainB`, `asyncOCQuietB`, `asyncOCQuietFinal`, `asyncOCSemB`, `asyncOCTransfer` | `programs/http-quiet` |
| `quiet/echo` | `asyncEchoBridgeWorld`, `asyncEchoCause`, `asyncEchoLiveInv`, `asyncEchoMeasure`, `asyncEchoQuiet`, `asyncEchoQuietTrace`, `asyncEchoReadySoon`, `asyncEchoServerCause`, `asyncEchoSleeps`, `asyncEchoStable`, `asyncStaticRounds` | `quiet/echo` |
| `quiet/ffi` | `ffiAgreeUpto` | `quiet/ffi` |
| `servers/level2-proto` | `asyncProtoV2`, `asyncServerWith2` | `servers/level2-proto` |
| `servers/proto-stable` | `asyncProtoActs`, `asyncProtoCause`, `asyncProtoMeasure`, `asyncProtoReact`, `asyncProtoStable`, `asyncSWActs` | `servers/proto-stable` |

## final/11-it-runs: it runs

| new dir | theories | from (review-v2) |
|---|---|---|
| `runnable/echo-blocking` | `asyncEchoBlkExport`, `asyncEchoLiveExport` | `runnable/echo-blocking` |
| `runnable/http-bodies` | `asyncProtoBExport` | `runnable/http-bodies` |
| `runnable/http-quiet` | `asyncOCHttpExport` | `runnable/http-quiet` |
| `runnable/machine-code` | `echoServerCompile`, `echoServerProof` | `runnable/machine-code` |
| `runnable` | (non-HOL: `socket_ffi.c`, Makefiles, demos, CPU tables) | `runnable` |
