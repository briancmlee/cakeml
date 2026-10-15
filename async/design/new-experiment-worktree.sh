#!/bin/sh
# Create a sparse experiment worktree that reuses the prebuilt shared base.
# See async/design/shared-base-build.md for the why and the pitfalls, and
# async/design/conventions.md for the working rules.
#
# Usage: new-experiment-worktree.sh [-e <exp-dir>] [-H basis|cakeml|none] <worktree-dir> <new-branch> [<start-ref>]
#   e.g. new-experiment-worktree.sh -e foo ~/Programming/cakeml-worktrees/foo spike/foo
#
# Options:
#   -e <exp-dir>  also create async/<exp-dir>/ with a Holmakefile template
#                 (not committed; the script never commits).
#   -H <heap>     HOLHEAP for that Holmakefile (default: basis):
#                   basis  = $(CAKEMLDIR)/basis/basis-heap (basis + CF loaded;
#                            recommended, ~4x faster startup for CF theories)
#                   cakeml = $(CAKEMLDIR)/misc/cakeml-heap (preamble only)
#                   none   = no HOLHEAP (plain hol.state; fine for pure-HOL dirs)
#
# Environment: CAKEML_BASE (default ~/Programming/cakeml), the frozen,
# fully built base checkout.  Nothing in the base's working tree is touched;
# `git worktree add` only records the new worktree in the base's .git.
set -eu

usage() { sed -n '6,7p' "$0"; exit 2; }
EXP=
HEAP=basis
while getopts e:H: opt; do
  case $opt in
    e) EXP=$OPTARG ;;
    H) HEAP=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
case $HEAP in
  basis)  HEAPLINE='HOLHEAP = $(CAKEMLDIR)/basis/basis-heap' ;;
  cakeml) HEAPLINE='HOLHEAP = $(CAKEMLDIR)/misc/cakeml-heap' ;;
  none)   HEAPLINE= ;;
  *) echo "unknown heap: $HEAP (basis|cakeml|none)" >&2; exit 2 ;;
esac

[ $# -ge 2 ] || usage
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

if [ -n "$EXP" ]; then
  D="$WT/async/$EXP"
  mkdir -p "$D"
  if [ -e "$D/Holmakefile" ]; then
    echo "$D/Holmakefile exists; left unchanged."
  else
    {
      echo "# Built against the prebuilt shared base (async/design/shared-base-build.md)."
      if [ -n "$HEAPLINE" ]; then
        echo "# $HEAP heap: see async/design/conventions.md for the measurements."
        echo "ifdef POLY"
        echo "$HEAPLINE"
        echo "endif"
      fi
    } > "$D/Holmakefile"
    echo "Wrote $D/Holmakefile (heap: $HEAP)."
  fi
else
  echo "Put experiments in $WT/async/<dir>/ with a Holmakefile containing:"
  echo "  ifdef POLY"
  echo "  HOLHEAP = \$(CAKEMLDIR)/basis/basis-heap"
  echo "  endif"
  echo "(or rerun with -e <dir> to have it written for you)."
fi
