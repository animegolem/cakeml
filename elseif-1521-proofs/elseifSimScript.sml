Theory elseifSim
Ancestors elseifContext elseif oldPan panPEG peg pegexec panLexer

Definition replay_def:
  (replay G s a (Success r v d) ⇔ accepts G s a r v) ∧
  (replay G s a (Failure l e) ⇔ rejects G s a)
End

Theorem all_bodies:
  n ∈ FDOM old_pancake_peg.rules ∧ no_else_if s ⇒
  agrees pancake_peg s (old_pancake_peg.rules ' n) (pancake_peg.rules ' n)
Proof
  Cases_on ‘n’ >> simp[oldPanTheory.FDOM_old_pancake_peg] >>
  rename1 ‘INL k’ >> Cases_on ‘k’ >>
  simp[unchanged_rule_lookups,if_bodies_agree,agrees_def] >>
  metis_tac[if_bodies_agree,agrees_def]
QED

Theorem domains:
  FDOM old_pancake_peg.rules = FDOM pancake_peg.rules
Proof simp[oldPanTheory.FDOM_old_pancake_peg,panPEGTheory.FDOM_pancake_peg]
QED

Theorem obs_nt:
  n ∈ FDOM old_pancake_peg.rules ∧ no_else_if s ∧
  replay pancake_peg s (old_pancake_peg.rules ' n) r ⇒
  replay pancake_peg s (nt n f) (resultmap f r)
Proof
  strip_tac >> drule_all_then assume_tac all_bodies >>
  Cases_on ‘r’ >> fs[replay_def,agrees_def,accepts_def,rejects_def,domains] >>
  metis_tac[peg_eval_nt,resultmap_def]
QED

Theorem safe_rest:
  no_else_if s ∧ peg_eval G (s,a) (Success i x d) ⇒ no_else_if i
Proof metis_tac[accepts_safe,accepts_def]
QED

Theorem simulation:
  (∀s a r. peg_eval old_pancake_peg (s,a) r ⇒
           no_else_if s ⇒ replay pancake_peg s a r) ∧
  (∀s a i vs err. peg_eval_list old_pancake_peg (s,a) (i,vs,err) ⇒
           no_else_if s ⇒ ∃d. peg_eval_list pancake_peg (s,a) (i,vs,d))
Proof
  ho_match_mp_tac peg_eval_strongind' >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> fs[replay_def] >>
  TRY (irule obs_nt >> simp[] >> NO_TAC) >>
  TRY (drule_all_then assume_tac safe_rest) >>
  TRY (qpat_x_assum ‘isFailure r’ mp_tac >> Cases_on ‘r’ >> simp[replay_def] >> strip_tac) >>
  TRY (qpat_x_assum ‘isSuccess r’ mp_tac >> Cases_on ‘r’ >> simp[replay_def] >> strip_tac) >>
  gvs[replay_def,accepts_def,rejects_def] >>
  TRY (FIRST (map (fn th => irule_at Any th >> first_assum ACCEPT_TAC ORELSE
                             irule_at Any th >> simp[] >> TRY (first_assum ACCEPT_TAC) >> NO_TAC)
                  (CONJUNCTS peg_eval_rules))) >>
  TRY (simp[Once peg_eval_cases] >> metis_tac[]) >~
  [‘isFailure r’] >- (Cases_on ‘r’ >> gvs[replay_def,rejects_def] >>
                       simp[Once peg_eval_cases,EXISTS_result] >> metis_tac[]) >~
  [‘isSuccess r’] >- (Cases_on ‘r’ >> gvs[replay_def,accepts_def] >>
                       simp[Once peg_eval_cases,EXISTS_result] >> metis_tac[]) >>
  Cases_on ‘MAXerr (fl1,fe1) (fl2,fe2)’ >>
  simp[replay_def,choice_reject,rejects_def] >> metis_tac[]
QED

Theorem old_start:
  old_pancake_peg.start = mknt TopDecListNT
Proof simp[old_pancake_peg_def]
QED

Theorem old_total:
  ∃q. peg_eval old_pancake_peg (s,mknt TopDecListNT) q
Proof
  metis_tac[old_start,oldPanTheory.PEG_wellformed,start_IN_Gexprs,peg_eval_total]
QED

Theorem B1:
  ∀s e. no_else_if s ⇒ (parse_old s = INL e ⇔ panPEG$parse s = INL e)
Proof
  rpt strip_tac >>
  qspec_then ‘s’ strip_assume_tac (GEN_ALL old_total) >>
  drule_then assume_tac pegexec >>
  drule_all_then assume_tac (cj 1 simulation) >>
  Cases_on ‘q’ >> gvs[replay_def,accepts_def,rejects_def] >>
  drule_then assume_tac pegexec >>
  simp[parse_old_def,panPEGTheory.parse_def] >>
  simp[AllCaseEqs()]
QED
