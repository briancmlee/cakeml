# Reusing the shared base build from experiment worktrees

**Goal.** Experiments live in their own git worktrees, but must not rebuild
CakeML (misc → characteristic → basis takes about 70 minutes). They reuse the
theories already built in the *base* checkout `~/Programming/cakeml`. The
base is frozen: nobody runs Holmake in it or edits its files, except when
deliberately rebuilding it (last section).

**Result.** This works and is tested (spike `cf-spike`, 2026-10-15). An
experiment builds only its own theories. The base's build products,
`misc/cakeml-heap` and `git status` were checked before and after, and are
unchanged. The only writes into the base were 65 missing dependency-cache
files, on the first run only (see Pitfalls).

## Recipe

1. Create a **sparse** worktree that checks out only `async/`, plus a
   gitignored `async/holproject.toml` pointing at the base:

   ```sh
   async/design/new-experiment-worktree.sh \
       ~/Programming/cakeml-worktrees/<name> spike/<name> [async-io]
   ```

   (Run it from any checkout that has the script, e.g. the base:
   `sh ~/Programming/cakeml-worktrees/cf-spike/async/design/new-experiment-worktree.sh ...`.)
   By hand, it does:

   ```sh
   git -C ~/Programming/cakeml worktree add --no-checkout <dir> -b <branch> async-io
   git -C <dir> sparse-checkout set --no-cone '/async/' '/.gitignore'
   git -C <dir> checkout <branch>
   cat > <dir>/async/holproject.toml <<'EOF'
   name = "cakeml_async_experiments"

   [projects.cakeml]
   path = "/Users/brian/Programming/cakeml"
   EOF
   ```

   `async/.gitignore` (committed) ignores `/holproject.toml`, so this file is
   never committed.

2. Put the experiment in `async/<dir>/`. Its `Holmakefile` only needs the
   CakeML heap from the base:

   ```make
   ifdef POLY
   HOLHEAP = $(CAKEMLDIR)/misc/cakeml-heap
   endif
   ```

   Theory scripts use `Ancestors`/`Libs` exactly as inside CakeML (for
   example `Ancestors ml_translator basisProg[qualified]` with
   `translation_extends "basisProg"`). Prefix theory names (e.g.
   `asyncCf...`), because HOL theory names are global.

3. Build in the experiment directory only, natively on Apple silicon, with a
   timeout:

   ```sh
   cd <dir>/async/<exp>
   timeout 1800 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j2'
   ```

   Check with `Holmake -n` first if in doubt: it must list only targets
   under `$(cakeml_async_experiments)/...`.

The hol-lsp MCP tools work in such a worktree without extra setup.

## Why this shape

- **Project mode is what makes `$(CAKEMLDIR)` mean the base.** Built `.uo`
  and `.dat` files refer to ancestors as `$(CAKEMLDIR)/...`. Both Holmake and
  the `hol` processes it starts resolve these names through `holpathdb`,
  which is filled by walking *up* from the current directory to collect every
  `holproject.toml`, then following their `[projects.<id>]` entries.
  `async/holproject.toml` declares `[projects.cakeml]` with the base's path,
  so `CAKEMLDIR` is registered as the base, and Holmake sees the base's
  directories (already built) as dependencies, not as targets.
- **The worktree must be sparse.** A full worktree has CakeML's own
  `holproject.toml` at its root (`holpath = "CAKEMLDIR"`). The upward walk
  would register `CAKEMLDIR` as the *worktree*, which collides with the base
  (`holproject.toml ... conflicts with prior registration of CAKEMLDIR`), and
  without `[projects.cakeml]` it would rebuild the whole unbuilt worktree.
  The sparse checkout leaves the root `holproject.toml` out of the working
  tree. Git still tracks it, as "skip-worktree".
- **`async/holproject.toml` is gitignored rather than committed.** In a
  normal full checkout `async/` should simply be part of the CakeML project,
  so nothing special may be committed.

## Pitfalls

- **Don't commit a nested `holproject.toml` that relies on
  `holproject.local.toml`.** I first tried a committed
  `async/cf-spike/holproject.toml` with `[projects.cakeml] path = "../.."`,
  overridden by a gitignored `holproject.local.toml`. HOL (master 652d1f0aa)
  validates the committed path *before* applying the local override
  (`HMProject.externals_from_table` eagerly reads the external's excludes).
  So in the sparse worktree it fails with `no holproject.toml at <worktree>`.
  This is arguably a HOL bug worth reporting upstream.
- **The first Holmake run writes dependency caches into the base.** Holmake
  created 65 missing `.hol/make-deps/*Theory.{sml,sig}.d` files in
  `basis/`, `basis/pure/`, `compiler/printing/` and `translator/monadic/`.
  These are caches for the generated theory files that the base build had
  not written. They are additive and content-determined. No existing file and
  no build product (`.uo`, `.ui`, `.dat`, heap) changed, and later runs wrote
  nothing. If the base is ever made read-only, check that Holmake tolerates
  failing to write them.
- **Fixed overhead of about 6.5 s per Holmake run, even when nothing needs
  building.** Holmake scans the 322 directories of the base project
  (including nested projects such as `pseudo_bool`) and runs
  `$(HOLDIR)/examples/l3-machine-code/arm8/asl-equiv/.hol_preexec` (an
  `external_includes` entry of CakeML's `holproject.toml`). The sparse setup
  doesn't avoid this, and it is about the same as in a full worktree. Loading
  `basisProg` in a theory script costs another ~50 s per theory, in which the
  smoke theory with one trivial spec took 58 s.
- **Only `async/` is editable.** An experiment that needs to patch CakeML
  itself (e.g. `basis/`) can't do it in a sparse worktree without rebuilding
  that part of the base. Copy what you need into `async/` under new names,
  or use a full worktree and pay for a full build in it.
- **Base and experiments must agree.** Experiments compile against whatever
  the base currently has. Never rebuild the base while an experiment
  build or an LSP session is running against it.
- **Never Holmake in the base by accident.** Running Holmake from the base
  (or with `--dirs` pointing into it) would rebuild there. Always `cd` into
  your experiment directory first.
- Shared machine rules: `-j2` at most, wrap Holmake/`hol` in `timeout`, and
  never kill processes by pattern (`pkill -f Holmake` once killed the base
  build). Kill only PIDs you started.

## Verifying that the base is untouched

```sh
cd ~/Programming/cakeml
snap() { find . -path ./.git -prune -o -path '*/.hol/*' -type f -print0 \
           | xargs -0 stat -f '%m %z %N' | sort -k3; }
snap > /tmp/before.txt; git status --porcelain > /tmp/before-git.txt
# ... Holmake in the experiment ...
snap | diff /tmp/before.txt - && git status --porcelain | diff /tmp/before-git.txt -
```

(2689 files under `.hol/` in the base at the time of writing; the check takes
under a second. Use your job's tmp directory instead of `/tmp` on a shared
machine.)

## Rebuilding the base deliberately (when upstream moves)

1. Make sure no experiment Holmake or hol-lsp session is running against the
   base (ask the coordinator), since they will see half-built theories.
2. In the base: update the branch (`git -C ~/Programming/cakeml merge ...` or
   check out the new commit). The base's working tree must stay clean apart
   from build products.
3. Rebuild in stages from the base, natively, with a timeout and logs, e.g.
   `misc`, then `characteristic`, then `basis`, each as
   `timeout 14400 arch -arm64 /bin/zsh -lc 'cd ~/Programming/cakeml/<dir> && ~/HOL/bin/Holmake -j4'`.
   Project mode builds whatever each stage depends on. The 2026-10-15 build
   took 82 s (misc), 576 s (characteristic) and 3651 s (basis).
4. Experiments then rebuild their own theories on their next Holmake, because
   their ancestors changed. Their `async/` sources may need updating if
   upstream changed APIs.

If HOL itself is rebuilt, the base must be rebuilt as well (its theories
depend on HOL's), so do HOL first, then the base.
