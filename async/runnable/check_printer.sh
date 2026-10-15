#!/bin/sh
# Cross-check sexpV3479Lib against the current repository's official
# printer (unverified/sexpr-bootstrap/astToSexprLib.sml): print the same
# declarations with both, normalise the two documented differences
# (locations -> (unk unk); Ident -> Var), and compare.  Run after Holmake.
set -e
CAKEMLDIR=${CAKEMLDIR:-$HOME/Programming/cakeml}
TMP=$(mktemp -d)
# the official printer opens fromSexpTheory, which it does not use
sed 's/^open preamble mlstringSyntax fromSexpTheory/open preamble mlstringSyntax/' \
  "$CAKEMLDIR/unverified/sexpr-bootstrap/astToSexprLib.sml" > "$TMP/astToSexprLib.sml"
cat > "$TMP/check.sml" <<SML
load "asyncEchoMainTheory";
use "$TMP/astToSexprLib.sml";
val (ds, ty) = listSyntax.dest_list (rhs (concl asyncEchoMainTheory.echo_prog_eq));
val n = length (fst (listSyntax.dest_list (rhs (concl basisProgTheory.basis_def))));
val _ = astToSexprLib.write_ast_to_file "$TMP/current.sexp"
          (listSyntax.mk_list (List.drop (ds, n), ty));
SML
"$HOME/HOL/bin/hol" --holstate="$CAKEMLDIR/basis/basis-heap" < "$TMP/check.sml" > "$TMP/hol.log" 2>&1
python3 - "$TMP/current.sexp" echo_server.sexp <<'PY'
import re, sys
cur, mine = open(sys.argv[1]).read(), open(sys.argv[2]).read()
n = re.sub(r'\("?Locs"? \(-?\d+ -?\d+\) \(-?\d+ -?\d+\)\)|\("?NoLocs"?\)', '(unk unk)', cur)
n = re.sub(r'(?<=[ (])Ident(?= \()', 'Var', n)
print("printers agree (modulo locations and Var/Ident):", n == mine)
sys.exit(0 if n == mine else 1)
PY
