# Worker conventions (CakeML async I/O experiments)

Fixed path: `~/Programming/cakeml-worktrees/CONVENTIONS.md`. Committed copy:
`async/design/conventions.md` on `spike/infra`. Background:
`async/design/shared-base-build.md` (branch `spike/cf-feasibility`).

## 1. Set up an experiment worktree

- The base `~/Programming/cakeml` (branch `async-io`, built up to `basis/`)
  is **frozen and shared**. Never run Holmake in it, never edit it.
- Create a sparse worktree (only `async/` is checked out) with the script,
  which also writes the experiment's Holmakefile:

  ```sh
  sh ~/Programming/cakeml-worktrees/infra/async/design/new-experiment-worktree.sh \
     -e <exp> ~/Programming/cakeml-worktrees/<name> spike/<name> [<start-ref>]
  ```

  `<start-ref>` defaults to `async-io`; use the parent branch for a stacked
  spike. `-H basis` (default) | `cakeml` | `none` picks the heap.
- **Heap: use `HOLHEAP = $(CAKEMLDIR)/basis/basis-heap`** in every directory
  whose theories use CF or the basis (inside `ifdef POLY ... endif`).
  Measured 2026-10-15 for a one-spec CF theory (`translation_extends
  "basisProg"`), mean of 2 runs:

  | HOLHEAP | Holmake (clean) | Holmake (no-op) | hol-lsp `diagnostics` (fresh server) |
  |---|---|---|---|
  | none (`hol.state`) | 72 s | 5 s | 52–61 s |
  | `misc/cakeml-heap` | 60 s | 5 s | 43–45 s |
  | `basis/basis-heap` | **17 s** | 5 s | **8 s** |
  | basis-heap + async model (custom) | 19 s | 6 s | 8 s |

  A custom heap with the async model theories gains nothing (they load in
  well under a second), so don't build one. For pure-HOL directories
  (e.g. `async/model`) the heap doesn't matter (diagnostics ~3.3 s either way).
  Using the base heaps never writes into the base (checked).
- Theory names are global: prefix them (`asyncCf...`, `ffiSpike...`).

## 2. Small theory files

- One topic per `*Script.sml`, a few hundred lines at most. Split when a
  file's check takes more than a minute or so: hol-lsp re-checks per file,
  and Holmake rebuilds every dependant.
- Statements readable on their own (the user reviews `.sig`-level lemmas);
  mark main results `(* MAIN *)` or similar in the handoff.

## 3. Checking

- During development: hol-lsp `diagnostics` (MCP tools, or CLI
  `arch -arm64 ~/Programming/hol-lsp-mcp/.venv/bin/python -m hol_lsp_mcp diagnostics FILE`
  with `HOL_BIN=$HOME/HOL/bin/hol`). It returns INCOMPLETE after `wait`
  seconds; call again to keep waiting. A proof that runs far longer than its
  neighbours is probably looping.
- If hol-lsp disagrees with Holmake (e.g. `xapp` inside `xcf_div` goals),
  Holmake wins; replay in the dumped heap
  (`hol --holstate=<thy>.<thm>.dumpedheap`).
- **Before every push:** in-worktree `Holmake` green in each experiment dir.
- **No cheats** in pushed work. hol-lsp counts `cheat` as `proved`; grep for
  `cheat` yourself.

## 4. Resources (16 GB shared machine)

- `Holmake -j2` at most. Wrap every Holmake/`hol` run in `timeout`.
- At most one or two hol-lsp servers of your own at a time (`restart`/close
  the ones you're done with).
- **Never kill processes you didn't start.** No `pkill`/`killall`/pattern
  kills; kill only PIDs you recorded.
- Never Holmake in the base (always `cd` into your experiment dir first;
  `Holmake -n` must list only `$(cakeml_async_experiments)/...` targets).
  Don't rebuild the base yourself; ask the coordinator.
- Temporary files go in your job's tmp dir, not `/tmp`.

## 5. Git and PRs

- One branch per spike, `spike/<name>`. A follow-up is a **stacked** branch
  whose PR targets the parent branch, not `async-io`.
- Commit trailers (exactly):

  ```
  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  Claude-Session: <your session URL>
  ```
- PRs: `gh pr create --repo briancmlee/cakeml --base <parent> --head spike/<name>`;
  the description ends with the "Generated with Claude Code" line and the
  session URL.
- **Never** push upstream (CakeML/cakeml), force-push, merge, or rewrite
  history. Don't touch other workers' worktrees or branches.
- `async/holproject.toml` is gitignored; never commit it.

## 6. HANDOFF files

- Keep `async/design/HANDOFF-<topic>.md` current at every push: status,
  how to build, assumptions made, dead ends/gotchas, final report.
- Include a **"Tool feedback"** section (hol-lsp, Holmake, scripts: what was
  slow or wrong, with a repro). The coordinator moves items into the
  upstream tracker `~/Programming/hol-lsp-mcp/docs/upstream-issues.md`;
  check it first for known issues and workarounds.

## 7. Run HOL natively

The shell may run under Rosetta (`uname -m` says `x86_64`). HOL is arm64:

```sh
timeout 1800 arch -arm64 /bin/zsh -lc 'cd <dir> && ~/HOL/bin/Holmake -j2'
```

## 8. Known gotchas

- `W` is HOL's W combinator; don't use it as a variable name.
- `CoInductive`: a free variable with the same name in every rule's
  conclusion silently becomes a fixed parameter. Quantify explicitly.
- `bin/hol` is rebuilt only by HOL's `configure`: `bin/build` does not
  notice LSP source edits, so a patched server silently keeps old code. A
  new `bin/hol` invalidates every saved heap ("exported from a different
  executable"), including the base's `cakeml-heap`/`basis-heap`, so the
  base must then be rebuilt (coordinator).
- Holmake's project scan: every run walks ~320 base directories plus the
  `asl-equiv` preexec (~5 s fixed overhead, even when nothing builds). Large
  untracked trees inside a project make it much worse (a 41k-dir opam
  switch took >75 min). Keep checkouts clean of such trees.
- Sparse worktrees are required: a full worktree registers `CAKEMLDIR` as
  itself and collides with the base. A committed nested `holproject.toml`
  overridden by `holproject.local.toml` fails (HOL checks the committed
  path first). Only `async/` is editable; copy CakeML code you need to
  change into `async/` under a new name.
- `MATCH_MP` with a theorem that has free type variables can capture goal
  type variables: `GEN_TYVARIFY` first.
- hol-lsp `goalState`: times out after `xmatch`; returns null in theorems
  whose statement has an antiquotation (write `main_v`, not
  `^(fetch_v ...)`). After rebuilding a dependency, `restart` the server.
