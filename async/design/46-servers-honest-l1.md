# 46. Servers on the honest FFI's prefetching L1 (CakeML level)

Branch `spike/servers-honest-l1`, PR #147. Worker: KV worker. This note covers P1–P3 for echo.
HTTP and KV (P4) come later, and their statements go to the user first.

## Layers

| Dir | Theory | What it is |
|---|---|---|
| `honest-l0-cf` | honestL0Part | The L0 world as an FFI part, by history replay. `l0_parts_ok` is the adequacy theorem. |
| | honestL0Prog, honestL0Proof | The `L0` wrappers and `L0_x_spec` against `L0_EV w0 w evs`. |
| `honest-l1-cf` | honestL1PFProg, honestL1PFSpec | design/36's prefetching L1 (honestL1PFModel, including D17), in CakeML. Its CF specs end in `run_pf_spec`. |
| `honest-echo` | honestEchoL0Spec | The trusted raw-trace definitions, user-approved: `l0_accepted`, `l0_ep_events`, `l0_read`, `l0_sent`, `l0_server_world`, `echo_safe_l0`. |
| | honestEchoL0Bites | The bites and non-vacuity, done before the proof as the user required. |
| | honestEchoL0Prog, Main, Sem | `echo_l0_prog`. `main` listens on port 8080, then runs `run_pf` with the unchanged v2 echo server on the returned fd. `echo_l0_semantics_prog` gives its whole-program semantics. |

## Decision (A): handle-counter overflow

The model's `pdo` fails (`NONE`) once the handle counter overflows, which happens after about 2^64 handed-out connections. The CakeML loop is made faithful to that:

- `step_pf` first checks `hdl_room lfd ps (LENGTH acts)`: room in the handle counter for the round's actions, plus one for a pending accepted connection.
- If there is no room, the step returns its state unchanged. From then on, the loop spins without I/O.

So **after 2^64 accepted connections the L1 loop stops doing I/O (it spins). This is unreachable in practice.** We chose this deliberately over wrapping the counter, because wrapping would reuse handles.

The divergence spec is stated against `prounds_t`:

- `prounds_t` is `prounds` while there is room; after that the state stays fixed.
- It needs only `pt_ok` (the server's actions are `pact_ok`), not a global connection bound.

The coordinator approved this.

## The echo safety transfer: route (d), not (c)

`echo_safe_l0` is proved directly, without R1/psk:

- **Model:** asyncServerSafety's `echo_server_safety` says that, per handle, the server's writes equal its reads in its transcript. It needs the handed-out handles to be distinct, and the `hdl_room` guard gives that.
- **L1 invariant over `prounds_t`, per episode j** (the j-th FConn fd, which is handle j):
  - `raw_sent ++ outbox ≼ writes`;
  - `raw_recv = reads ++ inb`.
- **Round lag:** the writes in round i echo reads answered by round i−1, and those reads come from bytes fetched by round i−1. So `sent(prefix) ≼ recv(prefix)`, as in close-v2's `echo2_safe`.

Route (c), through R1 (`l1pf_refines_hl`, psk) and close-v2's `echo2_safe`, was not taken, for two reasons:

- it needs `sched_wf2 psk` for every step, which requires a global bound;
- it needs an output-side relation that does not exist yet: psk's per-episode bytes ↔ raw L0 send events. `pv_rel` covers only the input side.

**This choice is for echo only. HTTP, KV and the moonshot need the generic output-side relation** (psk's per-episode bytes ↔ raw L0 events, and `precedes` through psk), which is the core of the R4′ template. KV's linearizability compares real-time order across connections, and a per-handle local invariant cannot carry that. After D19, honest-ffi plans to extend `pv_rel` to the output side.
