#!/usr/bin/env bash
set -eu
: "${CAKEMLDIR:?}" "${HOLDIR:?}"
# Share the installed lexer, nonterminal datatype and combinators. Replay
# the pinned grammar definition and its own well-formedness derivation.
git -C "$CAKEMLDIR" show 48ee98a7:pancake/parser/panPEGScript.sml |
  sed -n '/^Definition pancake_peg_def/,$p' |
  sed -e 's/pancake_peg/old_pancake_peg/g' -e 's/^  parse s =/  parse_old s =/' -e 's/^Definition parse_def:/Definition parse_old_def:/' > oldPan.body
cat > oldPanScript.sml <<'HOL'
Theory oldPan
Ancestors panPEG peg pegexec panLexer combin
Libs stringLib numLib intLib ASCIInumbersLib
open panPEGTheory
HOL
cat oldPan.body >> oldPanScript.sml
"$HOLDIR/bin/Holmake" --no_prereqs oldPanTheory.uo
