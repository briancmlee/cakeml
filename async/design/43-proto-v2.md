# 43: Every protocol server on the version-2 handle layer (plan)

Goal (user decision D5, spec approved in PR #105):
`⊢ http_spec_b2 3w demo_files http_prog_pb2`, where `http_prog_pb2` is the
generic protocol server (`asyncProtoServer.proto_server`) run by the
handle-layer loop (`close-v2-loop`: handles never reused, auto-close on
EOF). The proof is **generic over `proto_ok P`**, so the other protocol
instances (headers, strict) get version 2 for free. KV needs more (below).

Branch `spike/http-v2-prog`: `spike/http-v2` merged with `spike/kv-live`
(the newest proto pipeline and library liveness).

## How: the echo2 simulation, made generic

The echo2 proof (`close-v2-sim`, PR #63) runs the v1 server in a
renamed v1 world (`v1of`). It shows that the handle loop does, per
episode, what the v1 loop does per fd (`hsim`, `hrun_sim`). Then it
carries echo's v1 results over (`ep_rounds`). Most of that is generic in the
server already. What is echo-specific is:

| echo-specific | generic replacement |
|---|---|
| `hrun_sim`, `hrun_ok_echo` (fixed to `server lfdn`) | over any `m` with `wf m`, `uses_ok`; `gen_grun_ok`, `gen_round_actions_ok` |
| `echo_sock_eof_last` (no action on c after its EOF) | `proto_handler_eof_last` (the handler returns at `Eof`), lifted through `server_with` |
| `hrun_events`, `accepted_bound`, `ep_rounds` (stated for echo) | restated over `m` |
| `echo_rounds_written_read`, `echo_comp_live` | `proto_server_safety` per round, `proto_live_rounds` on `v1of s2` |

The spec side is `asyncProto2`: `proto_safe2`, `proto_live2` and
`proto_closes2 = echo_closes2`, with `proto_spec2`, together with
`http_spec_b2 ⇔ proto_spec2 P_b (print_response o bhandle files)`.

## Milestones (one PR each)

1. **Generic simulation.** `hrun_sim_gen` and `sock_eof_last_gen`, then
   `ep_rounds_gen`. Model level only, no CakeML.
2. **Generic v2 spec theorem.** `proto_spec2` holds of the model run
   (`proto2_safe`, `proto2_live`, `proto2_closes`), for any `proto_ok P`.
3. **CakeML.** The handle loop over `asyncProtoProg`'s translation;
   `proto_main2_spec`; `proto_spec2_of_semantics`. HTTP instance:
   `http_prog_pb2_spec : http_spec_b2 3w demo_files http_prog_pb2`.

## Known points

- A connection that stops on `PInvalid` is never closed. The spec allows
  this: it only requires a close after the client's EOF has been read.
  Closing on invalid input is the later server-initiated-close item.
- Proto safety is not monotone in what was read the way echo's is. The
  round-to-prefix argument needs the parse-prefix structure.
- KV (`proto_handler_v`, the store) also needs `eof_last` for the query
  handler, and a v2 story for the store. It is out of scope here.
- honest-ffi's L1 (design/36 §5) targets these v2 programs. The
  handle-layer interface (`asyncHLModel`) is kept unchanged.
