# programs/kv: placeholder (the CakeML half of KV)

The key-value server's headline, `kv_spec 3w kv_prog` (KvSpec: linearizable and
live), lands here once KV's CakeML is ported onto the proto pipeline (KV
worker; it was proved on spike/http-kv-impl 33cb07dd4 over the retired HTTP
translation chain, which L0 does not carry).

Already in this layer (model level):
- servers/kv: the store wrapper, the KV skeleton and handler, the model, and
  model-level safety (`kv_comp_safe`, kvSafe);
- servers/kv-live: liveness, `kv_live_rounds` (kvLive), through the library
  (`server_v_live_p`, layer 08) and the query handler's full liveness
  (`proto_handler_live_va_full`, servers/proto/protoLiveV).
