# HANDOFF: spike/option-c-int (integration branch for option C §2.3–2.5)

**For proofs only.** Nothing from this branch goes into the review series
while the HttpSpecBodies HOLD is in force (see below).

## What it is
- Based on `spike/option-c` (review lineage: review/11 → #57 QuietSpec → #77
  quiet echo → #81 Level 2 library).
- Merged with `spike/option-c-proto` (#82, on cf-actions' `spike/proto-kv`)
  using `git merge -s ours`. That records the ancestry and keeps the review
  layout.
- The two lineages lay out `async/` differently (review: `model/core`,
  `world/sockets`, …; proto-kv: `model`, `ffi-spike`, `m3-assembly`, …).
  Theory names must be unique project-wide, so the proto-kv tree can't simply
  be checked in alongside.

How the files were combined:
- **121 theories** are byte-identical on both sides. The review copies are
  used.
- **65 theories** exist only on the proto-kv side. They are placed under
  `async/pk/<original dir>/`. These are cf-actions' `http-proto`,
  `http-proto-inst`, `library-liveness`, `spec-rfc`, a few files from
  `cf-spike`, `http-liveness`, etc., and `option-c-proto`.
  - Each `pk` dir's Holmakefile includes exactly the dirs of its theories'
    ancestors, which keeps the INCLUDES graph acyclic.
- **4 files differ**, all HTTP bodies. They take proto-kv's (cf-actions')
  version:
  - `spec/HttpSpecBodiesScript.sml`, `spec/HttpSpecBodiesBiteScript.sml`;
  - `servers/http/asyncHttpParseBScript.sml`;
  - `programs/http-b/asyncHttpSockProgBScript.sml`.

## HOLD: H-CHARS is pending the user's decision
The HttpSpecBodies version here includes cf-actions' three spec commits on
`spike/http-bodies`:
- 524fa9501: header names are RFC tokens. **User-approved.**
- 04be60754: RFC character sets for paths and field values. **H-CHARS,
  pending user approval.**
- 863e8ee0a: `spec-rfc`, the RFC 9112 agreement.

If the user rejects H-CHARS, revert it here additively (a revert commit or
merge), not by rewriting history. The review-series fold of these commits
waits for the decision.

## Next (design/33)
- §2.3: the loop. step_q is #46's step_b with `select` on the sorted
  declared interest (`interest c`) instead of the live list. Polling and
  the live list are unchanged, so `sel_covers` holds by definition (no #56
  spin). It lives in the OC chain after `asyncOCProtoProg`, replaying
  #46's loop proofs with `poll2` and COMPI.
- §2.4: main and the QuietSpec bridge (`select_ffi = ssel_ffi` along runs
  that select only on sockets, as asyncEchoBridgeWorld does).
- §2.5: quiescence for HTTP bodies through the `http_prog_pb` instance.
