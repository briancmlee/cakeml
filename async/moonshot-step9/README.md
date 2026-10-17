# Moonshot step 9 (the proxy): DRAFT statements, for review

Nothing here is proved.  Three parts, each typechecked against the base it needs:

| part | file | base | how to typecheck |
|---|---|---|---|
| handle layer (E1 as it stands): `proxy_guar_hl`, `proxy_hl_claim`, `proxy_l1_claim`, the bite `unbounded_needed` | `hl/proxyHLStmtsScript.sml` | `spike/moonshot-client` @151ab274a (built base) | copy `hl/` to `async/moonshot-step9/hl` in that checkout, rename `Holmakefile.draft` to `Holmakefile`, `Holmake proxyHLStmtsTheory.uo` |
| raw L0 trace (echo_live_l0's vocabulary): `proxy_safe_l0`, `proxy_live_l0` (D23 `pos_timed_out` excuse), `proxy_pairs_l0`, `l0_proxy_claim` | `l0/proxyL0StmtsScript.sml` | `spike/echo-live-pol` @332dc5303 (built base) | as above with `l0/` |
| L1: `S4_relay_claim` (+ `gated_writes`, `chunk_writes`, `wbytes`) | `../honest-l1/honestL1PFRelayStmtsScript.sml` | this branch (`spike/moonshot-s4g` @aa4c7fcd9 + this commit) | `cd async/honest-l1; Holmake honestL1PFRelayStmtsTheory.uo` |

The Holmakefiles of `hl/` and `l0/` are named `.draft` so that this branch's project-wide
Holmake scan does not try to follow their INCLUDES (which exist only on their bases).

Marks (see the file headers): [R1] E1 takes `hw` where the PF model takes `pol` (rebase:
`pol_never`); [R2] E1's L1 has no D23, so the timeout excuse is raw-only until the rebase;
[R3] the handle layer has no close/shutdown: the half-close, backend-EOF, refused-backend
and closed-front clauses are OWED, pending the user's ruling (recommended: EClose/EShut in
endpointHLModel, in close-v2's E1 rebase); [R4] the rely is `run_rely` / `eh_round_ok`.
