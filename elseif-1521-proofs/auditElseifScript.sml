Theory auditElseif
Ancestors elseifAst elseifArms

fun audit th =
  if null (hyp th) andalso #1 (Tag.dest_tag (Thm.tag th)) = ["DISK_THM"]
  then () else raise Fail "unexpected hypotheses or oracle";
val _ = List.app audit [oldPanTheory.PEG_wellformed,
  elseifTheory.unchanged_rule_lookups, elseifTheory.no_else_if_suffix,
  elseifTheory.if_success_head, elseifTheory.if_rejects_after_else,
  elseifTheory.choice_success_ignoring_error, elseifTheory.else_tail_success,
  elseifContextTheory.if_bodies_agree, elseifSimTheory.simulation, elseifSimTheory.B1,
  elseifTokensTheory.old_rules_typed, elseifTokensTheory.old_guarded,
  elseifTokensTheory.B2, elseifTokensTheory.B, elseifAstTheory.AST_conservativity,
  elseifMeaningTheory.A_step, elseifMeaningTheory.A_chain,
  elseifArmsTheory.singleton_if_body, elseifArmsTheory.if_rule_with_arm,
  elseifArmsTheory.direct_arm, elseifArmsTheory.braced_arm];
val axioms = List.concat (map (fn t => map (fn (n,_) => t ^ "." ^ n)
  (DB.axioms t)) (Lib.mk_set (List.concat (map (fn t => t :: Theory.ancestry t)
                                   ["elseifAst","elseifArms"]))));
val _ = if Lib.set_eq axioms ["bool.BOOL_CASES_AX","bool.ETA_AX",
  "bool.SELECT_AX","bool.INFINITY_AX"] then () else raise Fail "unexpected axioms";
