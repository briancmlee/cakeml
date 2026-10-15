# 25. The blocking loop without `blk_live` (`asyncL2BlkStuck`)

Status: proved, no cheats. **`brun_two_outcomes` is the l2-blocking
headline** (approved by the user). It replaces `brun_spec`, which is now
its outcome-(a) special case, under the extra assumption `blk_live`.
Note 14 has been updated to match. It is additive: a new theory,
`async/l2-blocking/asyncL2BlkStuckScript.sml`, stacked on #21
(`spike/l2-blocking`). No existing l2-blocking file changes.

## What it does

Note 14 §3a calls `blk_live` (whenever the loop blocks, a declared byte
eventually arrives) the one named assumption of #21's `brun_spec`, and
sketches the honest replacement: a theorem with two outcomes. This note
covers that theorem.

`brun_two_outcomes` assumes the same as `brun_spec` but drops `blk_live`.
It proves that one of these holds:

1. `blk_live c ws`, and #21's `brun_spec` applies. The loop diverges, and
   its trace has the polling loop's actions.
2. There is a first round `n` that is **stuck** (`bstuck`). In that round
   the loop blocks with kept history `kept` at stream position `pos`, and
   no byte the loop is waiting for ever arrives. The program then ends in
   an FFI divergence of `«select»`:
   - The postcondition is `POSTf`, with `IOS2 (sdrop pos ws)` and the
     trace `FLAT (GENLIST (bround_events c ws) n)`.
   - `bfree c ws n` says that no earlier round is stuck.

The "nothing lost" half of outcome 2 is these model lemmas:
- `bstuck_trace_actions`: the trace up to the stuck round has exactly the
  actions in `(c.run kept).actions`.
- `bstuck_polling_quiet`: from that point on, the polling loop's
  computation never changes (`c.run (hist …) = c.run kept` for all later
  steps). So the polling loop performs no further actions either.

## How it is proved

- `brounds_inv_upto` re-proves #21's world invariant, assuming only
  `bfree c ws n` (no stuck round before `n`) instead of `blk_live`.
- `io2_update_select_diverge` and `bselect_stuck_spec`: when no declared
  byte ever arrives, the select FFI call has no next state, so the call
  diverges (`POSTf`).
- `bstep_stuck_spec` covers one iteration that blocks forever.
  `brun_stuck_spec` uses ordinary induction on the number of rounds left,
  with `xapp` on `bstep_spec_ev` / `bstep_stuck_spec`.
- `bfree_first_stuck` finds the first stuck round, by induction.

Note 14 §3a expected a new cfDiv loop rule with a `POSTf` exit. That was
not needed. A loop that ends with an FFI divergence after finitely many
rounds is just finite unfolding, so plain `app` induction suffices.

## What it doesn't do

- `brun_spec` itself is unchanged and is still proved in
  `asyncL2BlkLoop`. It is the outcome-(a) case, and `brun_two_outcomes`
  uses it.
- `bstep_spec_ev` copies #21's `bstep_spec`, generalised to any `evs`
  history (#21 fixes it to `[]`). Folding that into #21 would remove
  the copy, but it would rewrite #21, so I left it alone.
