# programs/kv: placeholder

The key-value server's headline, `kv_spec 3w kv_prog` (KvSpec: linearizable and
live), lands here once its CakeML safety step is proved.

Already proved, to be folded in then:
- liveness: `kv_live_rounds` (spike/kv-live, #95), through the library
  (`server_v_live_p`, layer 08) and the query handler (`proto_handler_live_va_full`, #99);
- model-level safety: `kv_comp_safe` (#111).
