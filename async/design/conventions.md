<!-- Committed copy of ~/projects/cakeml/work/CONVENTIONS.md (the working copy is authoritative; devex re-syncs this on shared/base). Supersedes the copy on spike/infra. -->

# Worker conventions (CakeML async I/O experiments)

Fixed path: `~/projects/cakeml/work/CONVENTIONS.md`. Committed copy:
`async/design/conventions.md` on `shared/base` (devex re-syncs it). Background:
`async/design/shared-base-build.md` (branch `spike/cf-feasibility`).

## 1. Set up an experiment worktree

- The base `~/projects/cakeml/repo` (branch `async-io`, built up to `basis/`)
  is **frozen and shared**. Never run Holmake in it, never edit it.
- Create a sparse worktree (only `async/` is checked out) with the script,
  which also writes the experiment's Holmakefile:

  ```sh
  sh ~/projects/cakeml/worktrees/infra/async/design/new-experiment-worktree.sh \
     -e <exp> ~/projects/cakeml/worktrees/<name> spike/<name> [<start-ref>]
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
  `~/src/hol-lsp-mcp/.venv/bin/python -m hol_lsp_mcp diagnostics FILE`
  with `HOL_BIN=$HOME/toolchains/HOL/bin/hol`). It returns INCOMPLETE after `wait`
  seconds; call again to keep waiting. A proof that runs far longer than its
  neighbours is probably looping.
- If hol-lsp disagrees with Holmake (e.g. `xapp` inside `xcf_div` goals),
  Holmake wins; replay in the dumped heap
  (`hol --holstate=<thy>.<thm>.dumpedheap`).
- **Before every push:** in-worktree `Holmake` green in each experiment dir.
- **No cheats** in pushed work. hol-lsp counts `cheat` as `proved`; grep for
  `cheat` yourself.

## 4. Resources (Sisyphus devbox, ~26 GB container, shared)

- Build through holslot, `-j1`, in the background (recipe in the hol4-proofs skill):
  `~/projects/cakeml/work/orchestrator/holslot timeout N ~/toolchains/HOL/bin/Holmake -j1`.
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
- **Never** push upstream (CakeML/cakeml), force-push, merge a PR on GitHub, or
  rewrite history. Local merges between branches are normal. Don't touch other
  workers' worktrees or branches.
- **Shared changes** (trusted/model definitions, decisions, shared design notes)
  live on `shared/base` (owner: devex). Lines merge it forward (`git merge --no-ff
  pf-model-base-N`, only if the line already contains pf-model-base-1). A new or
  amended decision is `async/design/decisions/Dnn.md` on a branch cut from
  `shared/base`, sent to devex; don't add rows to design/36 §9 (frozen).
- **Cutting branches:** cut a topic branch from the line it will merge into; cut a
  docs/decision branch from `shared/base` (or `git merge-base` of target and
  source), never from a feature line.
- **Strict at the review boundary, pragmatic elsewhere** (user, 2026-10-17). For a
  branch that becomes a PR the user reviews: shared changes come from
  `shared/base`, and `~/projects/cakeml/work/tools/bin/branch-check
  [--docs|--allow D,..] <branch> <target>` passes before the PR or review push.
  For intermediate work these are defaults: a cherry-pick (`-x`) or a recorded
  temporary copy is fine when cheaper; note it in your STATE.md.
- `async/holproject.toml` is gitignored; never commit it.

## 6. HANDOFF files

- Keep `async/design/HANDOFF-<topic>.md` current at every push: status,
  how to build, assumptions made, dead ends/gotchas, final report.
- Include a **"Tool feedback"** section (hol-lsp, Holmake, scripts: what was
  slow or wrong, with a repro). The coordinator moves items into the
  upstream tracker `~/src/hol-lsp-mcp/docs/upstream-issues.md`;
  check it first for known issues and workarounds.

## 7. Run HOL

Linux devbox: no `arch -arm64`, no Rosetta. Use the holslot recipe in §4.

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
