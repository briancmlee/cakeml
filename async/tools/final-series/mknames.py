#!/usr/bin/env python3
"""names.tsv -> NAMES.md (the human view of the final-series rename)."""
import sys
rows=[l.rstrip('\n').split('\t') for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
out=['# Names: what each theory and constant was called before the final series','',
'The final series names things by **concept**, without version numbers or milestone prefixes (`M3`, `M4`, `HL`, `OC`, `ffiSpike`, `V2`). The rename is mechanical: `rename.py` applies `names.tsv` (this table, machine-readable) to every theory, library, comment and Markdown file. Design notes `design/NN-*.md` are kept as written, so use this table to read them. The spike branches and the review-v2 snapshot keep the old names.','',
'Rules: theory renames apply everywhere, including `XTheory.`, `X$c` and translator names (`OLDTHY_X_TYPE`). Constant renames apply in HOL and ML code and comments, but never inside CakeML source (`Quote add_cakeml`). String literals are data and are never changed, except a string that is exactly one name (`new_definition ("old_def", …)`, `translation_extends "Old"`). CakeML datatype names derived by the translator from theory names change with the theory (e.g. `HttpSpecBodies_brequest` becomes `HttpSpec_brequest`); nothing else in the exported programs changes. A *prefix* rule also renames derived names (`old_def`, `old_thm`, `old_spec` …).','',
'## Constants','','| old | new | rule |','|---|---|---|']
for r in rows:
    if r[0]=='const': out.append(f'| `{r[1]}` | `{r[2]}` | {r[3] if len(r)>3 else "exact"} |')
out+=['','## Libraries','','| old | new |','|---|---|']
for r in rows:
    if r[0]=='lib': out.append(f'| `{r[1]}` | `{r[2]}` |')
out+=['','## Theories (by review-v2 directory)','','| directory | old | new |','|---|---|---|']
for r in sorted([r for r in rows if r[0]=='theory'], key=lambda r:(r[4] if len(r)>4 else '', r[1])):
    out.append(f'| {r[4] if len(r)>4 else ""} | `{r[1]}` | `{r[2]}` |')
out+=['','Unchanged, because they already name their concept: the async model (`asyncCore`, `asyncLevel1`, `asyncLevel2`, `asyncChoose`, `asyncLoop`, `asyncLoop2`, `asyncTranscript`, `asyncSched`, `asyncSched2`, `asyncEcho`, `asyncEcho2`, `asyncIdle`, `asyncIdle2`), `EchoSpec`, `QuietSpec` and their bites, `rfc9112Framing`, `rfcAgree`, `rfcAgreeValid`, `ffiAgreeUpto`, and `echoServerCompile` / `echoServerProof`. A `2` in a name means Level 2 (declared interest), which is a concept, not a version.','']
open(sys.argv[2],'w').write('\n'.join(out)+'\n')
