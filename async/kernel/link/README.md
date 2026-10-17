# L3-04: the link (R1-safe)

L1 refines close-v2's handle layer (`loopHandlesModel`) (design/36 §6).
Source: `spike/d20-poll` @e282d1996 (`honest-l1`). The files are verbatim
apart from the final-series renames (`design/names.tsv`) and the
mapping below. The theory names are still the spike's, for now.

| theory | what |
|---|---|
| `honestL1Refine` | R2's relation `l1v2_rel` in the simple world (`simple_v2`): L1 over the L0 world against the handle layer over a version-2 world; the step of time and the arrivals (`poll_tick_core`) |
| `honestL1Steps` | R2, action by action: each L1 action does what `hdo` does, with the events renamed (`l0_v2_event`) and up to deleted would-block events (`drops`; `act_step`) |
| `honestL1PFRefine` | R1-safe: the prefetching L1, in ANY L0 world, refines the handle layer in the version-2 world `psk` built from its own run (`l1pf_refines_hl`, `l1pf_refines_hl_upto`) |

**One mapping by hand.** The spike's `socketV2Events` has no theory of its
own in the final series: its two definitions (`spoll2_event`,
`close_event`) are in `lifetimes/world-cf/lifetimeProof`, which the
handle layer (`loopHandlesModel`) already imports. So `socketV2Events`
becomes `lifetimeProof` in the Ancestors lines; nothing else changes.

Out of this layer:
- The output-side link (`honestL1PFOut`: `out_rel`, `l1pf_refines_hl_out`,
  `l1pf_refines_hl_out_upto`, `l1pf_round_sent_upto`) is the last theory of
  layer 05. It builds on the R1-live theories (`honestL1PFConnRun`,
  `PFConn`, `PFClient`, `PFLive`, `PFRound`), so it cannot sit below them.
- The superseded drafts (`honestL1Round`, …) are not folded.
