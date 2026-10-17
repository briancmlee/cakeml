# D25′: Serve-on at the handle cut-off

Status: **approved (user, via coordinator); scheduled after D26 + echo liveness**

**Serve-on at the handle cut-off** (option (b), design/49-cutoff-serve-on.md). At the D25 cut-off, L1 answers an Accept without room with `Accepted NONE` (no `sys_accept`), drops lfd from the poll set and stops prefetching, and keeps running rounds for the existing connections, instead of the whole-round guard that stops the loop. `pl2_ok` loses its room conjunct; R1-live's connection-level clauses lose the room/`accepts_below` hypothesis (only "a pending connection is eventually accepted" keeps it, as an excuse); the quiet claim's `¬accepts_below` excuse goes. Owners: honest-ffi (model), KV worker (CF loop), cf-actions (quiet, blocking copy), async-spike (echo liveness split)

<!-- split from design/36 §9 (spike/echo-live-pol @e179dae84), 2026-10-17 -->
