# Final-series tools (not part of any review layer)

- `rename.py names.tsv ASYNC_DIR [--apply --git]`: the table-driven rename (see NAMES.md). It is not idempotent: run it once per file; on a stacked tree, pass only the new layer's directories (it refuses a tree that already contains renamed theories).
- `names.tsv`: the single source for names; `mknames.py names.tsv NAMES.md` regenerates the human view (copied into final/00's async/design/).
- `genhm.py dir1,dir2 ['dir=$(CAKEMLDIR)/…']`: run inside async/; writes each dir's Holmakefile with INCLUDES = the dirs of its theories' transitive ancestors (a Holmakefile.hdr in a dir supplies its header comment), and reports include cycles.
- `watch_build.sh LOG DIR…`: run inside async/; Holmake -j1 per dir through holslot (timeout 3600), killing any process of this tree whose memory footprint reaches 4 GB.
