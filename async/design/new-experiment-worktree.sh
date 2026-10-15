#!/bin/sh
# Create a sparse experiment worktree that reuses the prebuilt shared base.
# See async/design/shared-base-build.md for the why and the pitfalls.
#
# Usage: new-experiment-worktree.sh <worktree-dir> <new-branch> [<start-ref>]
#   e.g. new-experiment-worktree.sh ~/Programming/cakeml-worktrees/foo spike/foo
#
# Environment: CAKEML_BASE (default ~/Programming/cakeml), the frozen,
# fully built base checkout.  Nothing in the base's working tree is touched;
# `git worktree add` only records the new worktree in the base's .git.
set -eu

[ $# -ge 2 ] || { sed -n '5,6p' "$0"; exit 2; }
WT=$1
BRANCH=$2
REF=${3:-async-io}
BASE=${CAKEML_BASE:-$HOME/Programming/cakeml}

git -C "$BASE" worktree add --no-checkout "$WT" -b "$BRANCH" "$REF"
git -C "$WT" sparse-checkout set --no-cone '/async/' '/.gitignore'
git -C "$WT" checkout -q "$BRANCH"
mkdir -p "$WT/async"
cat > "$WT/async/holproject.toml" <<EOF
# Sparse experiment worktree only (gitignored): reuse the prebuilt base.
name = "cakeml_async_experiments"

[projects.cakeml]
path = "$BASE"
EOF
# Branches that predate async/.gitignore: make sure the file is never committed.
if ! git -C "$WT" check-ignore -q async/holproject.toml; then
  printf '/holproject.toml\nholproject.local.toml\n' >> "$WT/async/.gitignore"
  echo "Added async/.gitignore (commit it with your first commit)."
fi
echo "Created $WT (branch $BRANCH, sparse: async/ only)."
echo "Put experiments in $WT/async/<dir>/ with a Holmakefile containing:"
echo "  ifdef POLY"
echo "  HOLHEAP = \$(CAKEMLDIR)/misc/cakeml-heap"
echo "  endif"
