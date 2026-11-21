Theory elseifAst
Ancestors elseifTokens panPtreeConversion

(* Instantiate the installed front-end definition with just the PEG entry
   point replaced. The lexer, conversion, localising pass and errors are shared. *)
val front = SPEC_ALL panPtreeConversionTheory.parse_topdecs_to_ast_def
val (arg,body) = (rand (lhs (concl front)),rhs (concl front))
val old_body = subst [“panPEG$parse” |-> “parse_old”] body
val _ = if free_in “parse_old” old_body andalso not (free_in “panPEG$parse” old_body)
        then () else raise Fail "old front-end substitution did not replace parse"
val parse_topdecs_to_ast_old_def = Define
  ‘parse_topdecs_to_ast_old ^arg = ^old_body’

Theorem AST_conservativity:
  parse_topdecs_to_ast_old s = INL ast ⇒ parse_topdecs_to_ast s = INL ast
Proof
  simp[parse_topdecs_to_ast_old_def,parse_topdecs_to_ast_def,AllCaseEqs()] >>
  metis_tac[B]
QED
