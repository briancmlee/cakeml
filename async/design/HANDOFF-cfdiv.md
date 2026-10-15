# HANDOFF: cfDiv FFI-part loop rules for several FFI parts

Branch `spike/cfdiv-multipart`, stacked on `spike/socket-model` (PR #11),
worktree `~/Programming/cakeml-worktrees/ffi-spike`. Write-up:
`async/design/11-cfdiv-multipart.md`.

## State
- 11:30 `0182ebe1f`: `ffiSpikeDivMulti` — `repeat_POSTd_FFI_part_filter`,
  `IMP_app_POSTd_FFI_part_filter`, `lprefix_lub_LFILTER`.
- 11:45 `37cd56823`: `ffiSpikeDivMultiLib.xcf_div_filter`,
  `ffiSpikeSocketLogDiv` (logging poll loop in the composed world,
  MAIN `logserve_semantics`).
- then: write-up, PR (see Report). Nothing in progress.

## Build
```sh
cd ~/Programming/cakeml-worktrees/ffi-spike/async/ffi-spike
timeout 3600 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1'
```

## Assumptions made / tool feedback
See the end of `11-cfdiv-multipart.md`.
