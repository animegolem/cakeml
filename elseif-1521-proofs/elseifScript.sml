Theory elseif
Ancestors oldPan panPEG peg pegexec panLexer

Theorem unchanged_rule_lookups =
  let
    val olds = CONJUNCTS oldPanTheory.old_pancake_peg_applied
    val news = CONJUNCTS panPEGTheory.pancake_peg_applied
    fun key th = rand (lhs (concl th))
    fun same (a,b) = if aconv (key a) (key b) then TRANS a (SYM b)
                     else raise Fail "rule enumeration mismatch"
  in
    LIST_CONJ (map same (List.filter (fn (a,_) => not (aconv (key a) “INL IfNT : pancakeNT inf”))
                                     (ListPair.zipEq (olds,news))))
  end

Definition no_else_if_def:
  no_else_if xs ⇔
    ¬∃p l m s. xs = p ++ (KeywordT ElseK,l)::(KeywordT IfK,m)::s
End

Theorem no_else_if_suffix:
  no_else_if (p ++ s) ⇒ no_else_if s
Proof
  rw[no_else_if_def] >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem if_success_head:
  peg_eval pancake_peg (s,mknt IfNT) (Success rest v err) ⇒
  ∃l t. s = (KeywordT IfK,l)::t
Proof
  simp[mknt_def, peg_eval_NT_SOME, panPEGTheory.pancake_peg_applied,
       panPEGTheory.FDOM_pancake_peg, panPEGTheory.seql_def,
       panPEGTheory.pegf_def, peg_eval_seq_SOME, consume_kw_def,
       consume_tok_def, peg_eval_tok_SOME] >> metis_tac[]
QED

Theorem if_rejects_after_else:
  no_else_if ((KeywordT ElseK,l)::s) ⇒
  ∃fl fe. peg_eval pancake_peg (s,mknt IfNT) (Failure fl fe)
Proof
  strip_tac >>
  ‘∃fl fe. peg_eval pancake_peg (s,consume_kw IfK) (Failure fl fe)’ by
    (Cases_on ‘s’ >> simp[consume_kw_def,consume_tok_def,peg_eval_tok_NONE] >>
     PairCases_on ‘h’ >> gvs[no_else_if_def] >> metis_tac[listTheory.APPEND]) >>
  simp[mknt_def, Once peg_eval_cases, panPEGTheory.FDOM_pancake_peg,
       panPEGTheory.pancake_peg_applied, panPEGTheory.seql_def,
       panPEGTheory.pegf_def, peg_eval_seq_NONE] >> metis_tac[]
QED

Theorem choice_success_ignoring_error:
  (∃d. peg_eval G (s,choice a b f) (Success r v d)) ⇔
  (∃x d. peg_eval G (s,a) (Success r x d) ∧ v = f (INL x)) ∨
  (∃l e x d. peg_eval G (s,a) (Failure l e) ∧
             peg_eval G (s,b) (Success r x d) ∧ v = f (INR x))
Proof
  simp[peg_eval_choice, EXISTS_result, pairTheory.UNCURRY_DEF] >>
  metis_tac[]
QED

Theorem dead_choice:
  ¬peg_eval G (s,not (empty []) []) (Success r v d)
Proof
  simp[Once peg_eval_cases]
QED

Theorem single_choice:
  (∃d. peg_eval G (s,choice b (not (empty []) []) extract_sum) (Success r v d)) ⇔
  ∃d. peg_eval G (s,b) (Success r v d)
Proof
  simp[choice_success_ignoring_error, dead_choice, extract_sum_def]
QED

Theorem else_tail_success:
  no_else_if ((KeywordT ElseK,l)::s) ⇒
  ((∃d. peg_eval pancake_peg (s,panPEG$choicel [mknt IfNT; b]) (Success r v d)) ⇔
   (∃d. peg_eval pancake_peg (s,b) (Success r v d)))
Proof
  strip_tac >> drule_then strip_assume_tac if_rejects_after_else >>
  drule_then assume_tac (cj 1 peg_deterministic) >>
  asm_simp_tac (srw_ss()) [panPEGTheory.choicel_def, choice_success_ignoring_error,
                            panPEGTheory.extract_sum_def, single_choice]
QED
