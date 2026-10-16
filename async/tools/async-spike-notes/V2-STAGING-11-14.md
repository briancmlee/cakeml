# review-v2 layers 11-14: placement plan (staging)

## 11 quiet-option-c (from review-v2/10 once landed)
- quiet/ffi/ffiAgreeUptoScript.sml               (generic CakeML semantics)
- quiet/echo/*  (asyncEchoServerCause, asyncStaticRounds, asyncEchoReadySoon,
  asyncEchoMeasure, asyncEchoStable, asyncEchoLiveInv, asyncEchoSleeps,
  asyncEchoBridgeWorld, asyncEchoQuietTrace, asyncEchoQuiet, asyncEchoCause) -> echo_l_quiet
- servers/level2-proto/: asyncProtoV2 (from pk/option-c-proto)  [needs layer 10's proto + 09's server_v]
- programs/http-level2/: asyncOC{Model,Prog,Spec,Approx,Relabel,ProtoModel,ProtoProg,ProtoSpec}
  [needs layer 10's asyncProtoProg chain]
- loop/select-interest/: asyncOCFinite, asyncOCSel, asyncOCLoop, asyncOCRun, asyncOCSleeps, asyncOCAcc, asyncOCTrace
- programs/http-quiet/: asyncOCTransfer, asyncOCMainB, asyncOCSemB, asyncOCQuietB (+ proto_stable when it lands)
- Holmakefiles: ancestor-based INCLUDES (script in STATE/session history).
- design/33 (incl. §6), design/HANDOFF-quiet -> notes.

## 12 runnable (old 10 + )
- runnable/http-quiet (export, Makefile, cpu bench, results, transcript)
- remove runnable/http (headers) if layer 10 retires the headers program; keep echo, echo-blocking, http-bodies.

## 13 close-v2 (old 12): merge archive/review-v1-12 content forward.

## 14 docs (old 11 + )
- README: option C section, 100-continue limitation (HttpSpecBodies), RFC agreement (spec-rfc) in trust section, stricter-than-RFC list (rfc_subset_exact), headline table: echo_spec, http_prog_pb_spec, echo_l_quiet, http_q_quiet_b.
- START-HERE / REVIEW-GUIDE: v2 reading paths (1 h / full) from the proposal.
- REVIEW-SERIES-PLAN: v2 layer map.

## next-steps PR (off 14): endpoint-world, fd-discipline, buffer-closure, KV (#52/#73/#80); chat appendix link.

## User-approved README addition (Honest limitations, layer 14; also in the layer-12 PR description)
"Known gap in the trusted C (socket_ffi.c), being fixed: writes block until
all bytes are sent, so a client that stops reading can stall the whole
server; a write to a departed peer silently drops data; connection resets
are reported as end-of-file; accept failures such as running out of file
descriptors are reported as 'would block'; and socket errors are reported
as 'readable'. The model has none of these behaviours, so the theorems
don't see them. A redesign is in progress: a minimal, honest FFI (about one
syscall per call), verified CakeML wrappers that absorb the raw semantics,
and refinement proofs so the theorems about the lifetimes world (close and fd reuse) carry over (design/36)." [narrowed, user-approved 2026-10-16]
