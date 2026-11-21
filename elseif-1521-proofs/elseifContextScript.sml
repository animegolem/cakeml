Theory elseifContext
Ancestors elseif oldPan panPEG peg pegexec panLexer

Definition accepts_def:
  accepts G s a r v ⇔ ∃d. peg_eval G (s,a) (Success r v d)
End

Definition rejects_def:
  rejects G s a ⇔ ∃l e. peg_eval G (s,a) (Failure l e)
End

Theorem seq_accept:
  accepts G s (seq a b f) r v ⇔
    ∃i x y. accepts G s a i x ∧ accepts G i b r y ∧ v = f x y
Proof
  simp[accepts_def, peg_eval_seq_SOME] >> metis_tac[]
QED

Theorem seq_reject:
  rejects G s (seq a b f) ⇔ rejects G s a ∨
    ∃i x. accepts G s a i x ∧ rejects G i b
Proof
  simp[accepts_def,rejects_def,peg_eval_seq_NONE] >> metis_tac[]
QED

Theorem failure_pair:
  ∀p. ∃l e. Failure l e = UNCURRY Failure p
Proof Cases >> simp[]
QED

Theorem choice_reject:
  rejects G s (choice a b f) ⇔ rejects G s a ∧ rejects G s b
Proof
  simp[rejects_def,peg_eval_choice,EXISTS_result] >> metis_tac[failure_pair]
QED

Theorem sentinel_reject:
  rejects G s (not (empty []) [])
Proof
  simp[rejects_def,Once peg_eval_cases]
QED

Theorem else_tail_reject:
  no_else_if ((KeywordT ElseK,l)::s) ⇒
  (rejects pancake_peg s (panPEG$choicel [mknt IfNT;b]) ⇔ rejects pancake_peg s b)
Proof
  strip_tac >> drule_then strip_assume_tac if_rejects_after_else >>
  simp[panPEGTheory.choicel_def,choice_reject] >>
  ‘rejects pancake_peg s (mknt IfNT)’ by metis_tac[rejects_def] >>
  simp[sentinel_reject]
QED

Theorem empty_obs[simp]:
  (accepts G s (empty x) r v ⇔ s = r ∧ x = v) ∧ ¬rejects G s (empty x)
Proof simp[accepts_def,rejects_def] >> metis_tac[]
QED

Theorem list_wrap:
  (accepts G s (panPEG$pegf a f) r v ⇔ ∃x. accepts G s a r x ∧ v = f x) ∧
  (rejects G s (panPEG$pegf a f) ⇔ rejects G s a)
Proof simp[panPEGTheory.pegf_def,seq_accept,seq_reject]
QED

Theorem seq_nil:
  (accepts G s (seq a (empty []) (++)) r v ⇔ accepts G s a r v) ∧
  (rejects G s (seq a (empty []) (++)) ⇔ rejects G s a)
Proof simp[seq_accept,seq_reject]
QED

Definition agrees_def:
  agrees G s a b ⇔ (rejects G s a ⇔ rejects G s b) ∧
    ∀r v. accepts G s a r v ⇔ accepts G s b r v
End

Theorem seq_right:
  (∀i x. accepts G s a i x ⇒ agrees G i b c) ⇒
  agrees G s (seq a b f) (seq a c f)
Proof
  simp[agrees_def,seq_reject,seq_accept] >> metis_tac[]
QED

Theorem wrap_cong:
  agrees G s b c ⇒ agrees G s (panPEG$pegf b f) (panPEG$pegf c f)
Proof simp[agrees_def,list_wrap]
QED

Theorem else_choice_agrees:
  no_else_if ((KeywordT ElseK,l)::i) ⇒
  agrees pancake_peg i b (panPEG$choicel [mknt IfNT;b])
Proof
  simp[agrees_def,accepts_def] >> metis_tac[else_tail_success,else_tail_reject]
QED

Theorem else_alternatives:
  no_else_if s ⇒ agrees pancake_peg s
    (seql [consume_kw ElseK; c; d] I)
    (seql [consume_kw ElseK; panPEG$choicel [mknt IfNT; seql [c;d] I]] I)
Proof
  strip_tac >>
  ‘∀i x. accepts pancake_peg s (consume_kw ElseK) i x ⇒
     ∃l. s = (KeywordT ElseK,l)::i’ by
    simp[accepts_def,consume_kw_def,consume_tok_def,peg_eval_tok_SOME,PULL_EXISTS] >>
  simp[panPEGTheory.seql_def] >> irule wrap_cong >> irule seq_right >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  ‘agrees pancake_peg i
     (panPEG$pegf (seq c (seq d (empty []) (++)) (++)) I)
     (panPEG$choicel [mknt IfNT; panPEG$pegf (seq c (seq d (empty []) (++)) (++)) I])’
    by metis_tac[else_choice_agrees] >>
  fs[agrees_def,list_wrap,seq_nil]
QED

Theorem accepts_safe:
  no_else_if s ∧ accepts G s a i x ⇒ no_else_if i
Proof
  simp[accepts_def,PULL_EXISTS] >>
  metis_tac[cj 1 peg_eval_suffix, rich_listTheory.IS_SUFFIX_APPEND,no_else_if_suffix]
QED

Theorem safe_seq_right:
  (∀i. no_else_if i ⇒ agrees G i b c) ⇒
  ∀s. no_else_if s ⇒ agrees G s (seq a b f) (seq a c f)
Proof metis_tac[seq_right,accepts_safe]
QED

Theorem choice_left:
  agrees G s a b ⇒ agrees G s (choice a c f) (choice b c f)
Proof
  simp[agrees_def,choice_reject,accepts_def,choice_success_ignoring_error,
       rejects_def] >> metis_tac[]
QED

Theorem default_cong:
  agrees G s a b ⇒ agrees G s (try_default a t) (try_default b t)
Proof simp[try_default_def,panPEGTheory.choicel_def,choice_left]
QED

Theorem seq_nil_cong:
  agrees G s a b ⇒ agrees G s (seq a (empty []) (++)) (seq b (empty []) (++))
Proof simp[agrees_def,seq_nil]
QED

Theorem if_bodies_agree:
  no_else_if s ⇒ agrees pancake_peg s (old_pancake_peg.rules ' (INL IfNT))
                                      (pancake_peg.rules ' (INL IfNT))
Proof
  PURE_REWRITE_TAC [oldPanTheory.old_pancake_peg_applied,panPEGTheory.pancake_peg_applied] >>
  strip_tac >>
  PURE_ONCE_REWRITE_TAC [panPEGTheory.seql_def] >>
  simp[listTheory.FOLDR] >> irule wrap_cong >>
  NTAC 4 (irule seq_right >> rpt strip_tac >>
          drule_all_then assume_tac accepts_safe) >>
  irule seq_nil_cong >> irule default_cong >> simp[else_alternatives]
QED
