# programs/kv: the verified key-value server

The key-value server's headline, `kv_prog_spec : kv_spec 3w kv_prog` (KvSpec:
linearizable and live), on the generic protocol pipeline (`programs/proto`).

- `asyncKvProg`: the CakeML program. It extends `asyncProtoProg`, and repeats
  `asyncProtoProgB`'s bodies-parser translations, as `asyncOCMainB` does. It
  adds `with_store` (a pure effect handler holding the store, with no refs),
  the association-list store `kv_delta_al`, the tagged skeleton
  `sserver_with_k`, and `kv_handler`.
- `asyncWithStoreSpec`: generic CF specs of `with_store`, for any store
  representation and step function (`DELTA`).
- `asyncKvSpec`: `kv_server_spec`, which says the CakeML `kv_server`
  implements `srelabel (kv_server lfd)`.
- `asyncKvMain`, `asyncKvSemantics`, `asyncKvHeadline`: the program, its
  divergence, and `kv_prog_safe`.
- `asyncKvProgSpec`: `kv_prog_spec`. Safety is `kv_semantics_prog`, whose
  order construction is `servers/kv`'s `kv_comp_safe`; liveness is
  `servers/kv-live`'s `kv_live_rounds`, on the same trace.

## Tracked near-duplicate: `kserver_with_k_spec` vs `sserver_with_spec`

`asyncKvSpec.kserver_with_k_spec` is `asyncProtoSockSpec.sserver_with_spec`'s
argument, repeated in the tagged vocabulary `Sock sact | Kv query`.
`SHANDLER` and `sserver_with_spec` are stated in the plain socket vocabulary
(`SACT`, `SSNAP`). KV's handlers also emit `Kv` queries, which `with_store`
answers, so they do not fit `SHANDLER` as stated. The code is likewise
repeated: `sserver_with_k` is `sserver_with` with `Sock` around the accept and
`Sockr` around its result.

Generalisation sketch (to decide after the final series is assembled):
state `SHANDLER`, `sserver_with` and `sserver_with_spec` over a vocabulary
record, which would give:
- an injection of socket actions (`Accept`), and its refinement;
- a projection of accept results;
- the action and response refinements (`SACT`/`SRESP`, or `KACT SACT Q`/`KRES SRESP A`).

The plain server would be the identity instance, and KV the `Sock`/`Sockr`
instance. moonshot's translator (#133) already carries such a vocabulary
record for generated handlers, which may be the natural shape.
