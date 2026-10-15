# Handoff: QuietSpec and option C (quiescence), async-spike

Kept current at every milestone. The full state (review series, folds,
rules, gotchas) is in ~/.cache/async-spike/STATE.md.

## Where things are
- spike/quiet-spec (PR #57):
  - `spec/QuietSpec` (user-approved): `echo_quiet`, `http_quiet`,
    `http_quiet_b`, `select_ffi`, `arrivals_finite`, `asleep`;
  - `QuietSpecBite`;
  - `design/33-option-c-quiescence.md` (the costing; approved).
- spike/quiet-echo (stacked on it): `async/quiet/echo/asyncEchoCause`,
  `handler_cause` (proved).

## Plan (design/33 §2.5), echo first
1. Q1 `echo_stable`: static world after the last arrival; the measure
   (queue + unread bytes / unread EOF on connections not EOF-read) is
   non-increasing and decreases within 4 rounds (`accept_soon_s`, and
   `read_soon_s` generalised to "ready"). Then stability through
   `handler_cause`, a server-level cause lemma, and Level 2 `quiet`.
2. Q2: a generic loop lemma (stable polling ⇒ the declared-interest
   select loop ends asleep), via #46's `lbgrounds`.
3. Q3: the finite trace is safe and live.
4. The L2 CF library, the loop, echo at Level 2 in CF, the bridge, and
   ⊢ `echo_quiet 3w` <program>.

HTTP waits for cf-actions' generic pipeline (design/32). Its cause lemma
has a third disjunct (an answered Write) and consumes `handler_live`'s
buffered-requests term (agreed with cf-actions).

## Build
`~/Programming/cakeml-worktrees/review-series-tools/hm.sh async/quiet/echo`
(holslot, -j1). No cheats.
