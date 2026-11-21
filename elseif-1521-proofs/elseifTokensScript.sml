Theory elseifTokens
Ancestors elseifSim elseifContext elseif oldPan panPEG peg pegexec panLexer

Definition guarded_def:
  guarded p s ⇔ no_else_if s ∧ (p ⇒ ∀l t. s ≠ (KeywordT IfK,l)::t)
End

Theorem split_prefix:
  (∀p. P p) ⇔ P [] ∧ ∀h t. P (h::t)
Proof metis_tac[listTheory.list_CASES]
QED

Theorem adjacent_cons:
  no_else_if ((k,l)::s) ⇔ guarded (k = KeywordT ElseK) s
Proof
  simp[guarded_def,no_else_if_def] >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV split_prefix)) >>
  simp[] >> metis_tac[]
QED

(* p and q are obligations on the first token of the input and remainder.
   An old ElseK may introduce the obligation; its following LCurT clears it. *)
Definition typed_def:
  (typed p (empty v) q ⇔ p = q) ∧
  (typed p (tok P f) q ⇔ ∀k. P k ⇒
       (p ⇒ k ≠ KeywordT IfK) ∧ (k = KeywordT ElseK ⇒ q)) ∧
  (typed p (any f) q ⇔ F) ∧
  (typed p (nt n f) q ⇔ ¬p ∧ ¬q) ∧
  (typed p (seq a b f) q ⇔
       typed p a F ∧ typed F b q ∨ typed p a T ∧ typed T b q) ∧
  (typed p (choice a b f) q ⇔ typed p a q ∧ typed p b q) ∧
  (typed p (rpt a f) q ⇔ p = q ∧ typed p a p) ∧
  (typed p (not a v) q ⇔ p = q) ∧
  (typed p (error e) q ⇔ T)
End

Theorem token_step:
  P (FST h) ∧ typed p (tok P f) q ∧ guarded q t ⇒ guarded p (h::t)
Proof
  Cases_on ‘h’ >> simp[typed_def,guarded_def,adjacent_cons] >>
  rw[] >> fs[guarded_def] >> metis_tac[]
QED

Theorem typed_tok:
  typed p (tok P f) q ⇔ (p ⇒ ¬P (KeywordT IfK)) ∧ (P (KeywordT ElseK) ⇒ q)
Proof simp[typed_def] >> metis_tac[]
QED

Theorem old_rules_typed:
  ∀n. n ∈ FDOM old_pancake_peg.rules ⇒ typed F (old_pancake_peg.rules ' n) F
Proof
  Cases >> simp[oldPanTheory.FDOM_old_pancake_peg] >>
  rename1 ‘INL k’ >> Cases_on ‘k’ >>
  simp[oldPanTheory.old_pancake_peg_applied, panPEGTheory.choicel_def,
       panPEGTheory.seql_def,panPEGTheory.pegf_def,try_ProgNT_def,
       try_default_def,try_def,mknt_def,consume_kw_def,keep_kw_def,
       consume_tok_def,keep_tok_def,keep_nat_def,keep_int_def,keep_ident_def,
       keep_ffi_ident_def,keep_annot_def,typed_tok,typed_def]
QED

Theorem old_guarded:
  (∀s a r. peg_eval old_pancake_peg (s,a) r ⇒
    ∀p q i v d. r = Success i v d ∧ typed p a q ∧ guarded q i ⇒ guarded p s) ∧
  (∀s a i vs err. peg_eval_list old_pancake_peg (s,a) (i,vs,err) ⇒
    ∀p. typed p a p ∧ guarded p i ⇒ guarded p s)
Proof
  ho_match_mp_tac peg_eval_strongind' >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[typed_def,resultmap_EQ_Success] >>
  rpt strip_tac >> gvs[] >>
  TRY (Cases_on ‘MAXerr (fl1,fe1) (fl2,fe2)’ >> gvs[] >> NO_TAC) >>
  gvs[typed_def] >~ [‘P (FST e)’] >-
    (irule (SIMP_RULE std_ss [typed_def] token_step) >> metis_tac[]) >>
  metis_tac[old_rules_typed]
QED

Theorem B2:
  ∀s e. parse_old s = INL e ⇒ no_else_if s
Proof
  rpt gen_tac >> qspec_then ‘s’ strip_assume_tac (GEN_ALL old_total) >>
  drule_then assume_tac pegexec >>
  Cases_on ‘q’ >> simp[parse_old_def,AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_then (qspecl_then [‘F’,‘F’] mp_tac) (cj 1 old_guarded) >>
  simp[mknt_def,typed_def,guarded_def,no_else_if_def]
QED

Theorem B:
  ∀s e. parse_old s = INL e ⇒ panPEG$parse s = INL e
Proof metis_tac[B1,B2]
QED
