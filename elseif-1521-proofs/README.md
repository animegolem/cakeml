# Proofs about the Pancake `else if` change (CakeML #1521)

These HOL4 theories prove two properties of the grammar change in #1521.

## What is proved

- **Old programs parse the same** (`elseifTokensTheory.B`): every token list that the old grammar accepts parses to
  the same located tree under the new grammar.

      parse_old s = INL e ⇒ panPEG$parse s = INL e

  It follows from two theorems:
  - `B1`: on token lists with no `else` immediately followed by `if`, the two grammars accept the same trees, in both
    directions.
  - `B2`: the old grammar accepts no token list that has `else` immediately followed by `if`.

  `elseifAstTheory.AST_conservativity` lifts `B` to source text. If the front end with the old grammar returns an
  AST, the current front end returns the same AST. The lexer, the tree conversion and the localisation pass are
  shared.
- **A chain means the nested form** (`elseifMeaningTheory.A_chain`): for any chain of conditionals, the tree with
  each `else` followed directly by the next `if` converts (`conv_Prog`) to the same program as the tree with each
  inner `if` alone in a braced block. The two trees also have the same source span. Nothing is erased.
  `elseifArmsTheory.direct_arm` and `braced_arm` show that these are the trees the new `IfNT` rule builds for
  `else if …` and for `else { if … }`. `if_rule_with_arm` reads that rule from `pancake_peg` itself.

`old_pancake_peg` is the grammar before the change. `build-old.sh` takes it from `panPEGScript.sml` at the base
revision with `git show`, and renames `pancake_peg` to `old_pancake_peg` and `parse` to `parse_old`. The grammar's
datatypes and combinators come from the installed `panPEGTheory`, because the change does not touch them.

## What is not proved

- Error messages. Both statements are about successful parses only.
- A token-level form of the chain theorem. That form would insert braces into a token list and show that the parsed
  program does not change. It needs to show where the inner statement ends.

## How to rerun

You need HOL4 and a CakeML tree that contains the #1521 change, with `pancake/parser` and its dependencies built
by Holmake. We checked these proofs at 48ee98a7 plus the change, with HOL4 9783a499 on Linux x86-64.
`pancake/parser/` and `pancake/panLangScript.sml` are identical at 48ee98a7 and at master 2874b664.

Copy this folder to a scratch directory, then run:

    export CAKEMLDIR=/path/to/cakeml HOLDIR=/path/to/HOL
    bash build-old.sh
    "$HOLDIR/bin/Holmake" --no_prereqs auditElseifTheory.uo

`build-old.sh` reads the old grammar from revision `48ee98a7`. In a clone that lacks that commit, change the
revision in the script to the parent of the #1521 commit.

`auditElseifTheory` checks each principal theorem: no hypotheses, and no oracle other than the one for theorems
loaded from disk. It also checks that the only axioms in the ancestry are `bool`'s four. No proof uses `cheat`.
