# Startup cost per HOLHEAP choice (2026-10-15)

Question: which saved heap should experiment directories use, and would a
custom heap (basis plus the async model theories) help?
Answer: use `$(CAKEMLDIR)/basis/basis-heap`; a custom heap gains nothing.

## Method

Sparse worktree `~/Programming/cakeml-worktrees/infra` (branch
`spike/infra`), HOL `~/HOL` run natively (`arch -arm64`), `Holmake -j2`,
machine shared with other workers (so ±10% noise). Test theories were
local and not committed (`async/heaptest/`):

- CF test: the `cf-spike` smoke theory (`Ancestors ml_translator
  basisProg[qualified]`, `translation_extends "basisProg"`, one
  `Quote add_cakeml` function, one `app` spec by `xcf_with_def`/`xret`/
  `xsimpl`), in three copies differing only in HOLHEAP.
- Model test: the same plus the nine async model theories of
  `spike/async-level2` as ancestors; the custom heap was
  `hol buildheap -b basis-heap -o async-heap <model .uo files>` (3.5 MB,
  built in 5 s).
- Pure test: a one-line theorem over `asyncCore asyncLevel1 asyncLevel2`.

"Holmake clean" = `rm -rf .hol; Holmake -j2`; "no-op" = Holmake again.
"diagnostics" = wall time of the hol-lsp-mcp CLI
`python -m hol_lsp_mcp diagnostics FILE` (fresh `hol lsp` server: heap
load + full check), until "1/1 proofs proved".

## Results (run 1 / run 2, seconds)

| Test | HOLHEAP | Holmake clean | Holmake no-op | diagnostics |
|---|---|---|---|---|
| CF | none (`hol.state`) | 73.2 / 71.3 | 5.3 / 4.8 | 52.2 / 61.4 |
| CF | `misc/cakeml-heap` | 61.8 / 59.2 | 5.0 / 4.9 | 43.0 / 45.2 |
| CF | `basis/basis-heap` | 17.0 / 16.8 | 4.7 / 4.6 | 7.7 / 7.9 |
| CF + model | `basis/basis-heap` | 18.7 / 19.2 | 5.5 / 5.9 | 8.2 / 8.0 |
| CF + model | custom basis + model heap | 19.1 / 19.6 | 6.3 / 5.6 | 8.6 / 8.0 |
| pure HOL | none | 5.9 / 7.5 | 5.6 / 6.6 | 3.2 / 3.5 |
| pure HOL | `basis/basis-heap` | 9.0 / 8.2 | 7.2 / 5.0 | 3.7 / 3.3 |

- basis-heap removes ~55 s of `basisProg`/CF loading per theory and per
  fresh LSP server (the 60–90 s diagnostics workers saw were mostly this).
- The remaining ~5 s per Holmake run is the project scan of ~328
  directories plus the `asl-equiv` preexec; no heap choice affects it.
- The async model theories are small; loading them costs < 1 s.

## Base untouched

Before and after all runs: the mtime/size list of every file under the
base's `.hol/` dirs (2790 files), `git status --porcelain`, and the md5 of
`misc/cakeml-heap` and `basis/basis-heap` were identical.
