Theory elseifArms
Ancestors elseif elseifContext elseifMeaning panPEG peg pegexec

Theorem nt_accepts:
  accepts pancake_peg s (mknt n) r v ⇔
  INL n ∈ FDOM pancake_peg.rules ∧ accepts pancake_peg s (pancake_peg.rules ' (INL n)) r v
Proof simp[accepts_def,mknt_def,peg_eval_NT_SOME] >> metis_tac[]
QED

Theorem nt_rejects:
  rejects pancake_peg s (mknt n) ⇔
  INL n ∈ FDOM pancake_peg.rules ∧ rejects pancake_peg s (pancake_peg.rules ' (INL n))
Proof simp[rejects_def,mknt_def,Once peg_eval_cases] >> metis_tac[]
QED

Theorem choices:
  (accepts G s (panPEG$choicel (a::as)) r v ⇔ accepts G s a r v ∨
     rejects G s a ∧ accepts G s (panPEG$choicel as) r v) ∧
  (rejects G s (panPEG$choicel (a::as)) ⇔ rejects G s a ∧ rejects G s (panPEG$choicel as)) ∧
  ¬accepts G s (panPEG$choicel []) r v ∧ rejects G s (panPEG$choicel [])
Proof
  simp[panPEGTheory.choicel_def,choice_reject,sentinel_reject] >> simp[accepts_def,
       choice_success_ignoring_error,panPEGTheory.extract_sum_def,rejects_def,dead_choice] >>
  metis_tac[]
QED

Theorem observe_tok:
  (accepts G ((k,l)::s) (tok P f) r v ⇔ P k ∧ s = r ∧ f (k,l) = v) ∧
  (rejects G ((k,l)::s) (tok P f) ⇔ ¬P k)
Proof simp[accepts_def,rejects_def,peg_eval_tok_SOME,peg_eval_tok_NONE] >> metis_tac[]
QED

Theorem rejection_excludes_success:
  rejects G s a ⇒ ¬accepts G s a r v
Proof
  simp[rejects_def,accepts_def,PULL_EXISTS] >> rpt strip_tac >>
  drule_then assume_tac (cj 1 peg_deterministic) >> gvs[]
QED

Theorem reject_first:
  rejects G s a ⇒ rejects G s (seql (a::bs) f)
Proof simp[panPEGTheory.seql_def,list_wrap,seq_reject]
QED

Theorem reject_second:
  accepts G s a i v ∧ rejects G i b ⇒ rejects G s (seql (a::b::bs) f)
Proof simp[panPEGTheory.seql_def,list_wrap,seq_reject] >> metis_tac[]
QED

val grammar_rw = [panPEGTheory.seql_def,list_wrap,seq_accept,seq_reject,seq_nil,
                  choices,observe_tok,consume_kw_def,consume_tok_def,keep_kw_def,
                  keep_tok_def,keep_ident_def,keep_ffi_ident_def,keep_annot_def,
                  try_default_def,panPEGTheory.try_def]

(* Unfold only the nonterminal under inspection. Its children can be
   recursive, and remain opaque except where a previously checked lemma applies. *)
fun nt_rw obs n =
  SIMP_RULE (srw_ss()) [FDOM_pancake_peg,panPEGTheory.pancake_peg_applied]
            (Q.INST [‘n’ |-> [ANTIQUOTE n]] obs)

val closing_rejects = let
  val nts = [“HandleNT”,“IfNT”,“WhileNT”,“BlockNT”,“DecCallNT”,“DecNT”,
             “RetNT”,“AssignNT”,“StoreNT”,“StoreByteNT”,“Store32NT”,
             “SharedLoadByteNT”,“SharedLoad16NT”,“SharedLoad32NT”,“SharedLoadNT”,
             “SharedStoreByteNT”,“SharedStore16NT”,“SharedStore32NT”,“SharedStoreNT”,
             “ExtCallNT”,“ThrowNT”,“RetCallNT”,“ReturnNT”,“CallNT”,“StmtNT”]
  fun step (n,prev) = let
    val th = Q.prove(‘rejects pancake_peg ((RCurT,l)::s) (mknt ^n)’,
                     PURE_ONCE_REWRITE_TAC [nt_rw nt_rejects n] >>
                     (if aconv n “CallNT” then
                        irule reject_second >> simp[keep_ident_def,observe_tok] >>
                        qexists_tac ‘(RCurT,l)::s’ >>
                        simp (prev @ grammar_rw)
                      else simp (reject_first :: choices :: prev @
                                 [consume_kw_def,consume_tok_def,keep_kw_def,keep_tok_def,
                                  keep_ident_def,keep_ffi_ident_def,keep_annot_def,observe_tok])))
    in th :: MATCH_MP rejection_excludes_success th :: prev end
in List.foldl step [] nts end

Theorem closing_brace:
  accepts pancake_peg ((RCurT,l)::s) (mknt ProgNT) s []
Proof
  PURE_ONCE_REWRITE_TAC [nt_rw nt_accepts “ProgNT”] >>
  simp (choices :: reject_first :: closing_rejects @
        [keep_annot_def,observe_tok,consume_tok_def])
QED

Theorem block_if:
  accepts pancake_peg s (mknt IfNT) i v ⇒ accepts pancake_peg s (mknt BlockNT) i v
Proof
  strip_tac >>
  ‘∃l t. s = (KeywordT IfK,l)::t’ by metis_tac[accepts_def,if_success_head] >>
  gvs[] >>
  PURE_ONCE_REWRITE_TAC [nt_rw nt_accepts “BlockNT”] >>
  simp[choices] >>
  disj2_tac >>
  PURE_ONCE_REWRITE_TAC [nt_rw nt_rejects “HandleNT”] >>
  simp[reject_first,consume_kw_def,consume_tok_def,observe_tok]
QED

Theorem singleton_if_body:
  accepts pancake_peg s (mknt IfNT) ((RCurT,l)::rest) [inner] ⇒
  accepts pancake_peg s try_ProgNT rest [mknode ProgNT [inner]]
Proof
  strip_tac >>
  drule_then assume_tac block_if >>
  ‘∃k t. s = (KeywordT IfK,k)::t’ by metis_tac[accepts_def,if_success_head] >>
  gvs[] >> simp[try_ProgNT_def,choices] >> disj2_tac >>
  conj_tac >- simp[reject_first,consume_tok_def,observe_tok] >>
  PURE_ONCE_REWRITE_TAC [nt_rw nt_accepts “ProgNT”] >>
  simp[choices] >> disj1_tac >>
  simp[panPEGTheory.seql_def,list_wrap,seq_accept,mksubtree_def] >>
  metis_tac[closing_brace,listTheory.APPEND_NIL]
QED

Definition else_arm_def:
  else_arm = try_default
    (seql [consume_kw ElseK;
           panPEG$choicel [mknt IfNT; seql [consume_tok LCurT; try_ProgNT] I]] I)
    (KeywordT SkipK)
End

Theorem if_rule_with_arm:
  pancake_peg.rules ' (INL IfNT) =
    seql [consume_kw IfK; mknt ExpNT; consume_tok LCurT; try_ProgNT; else_arm]
         (mksubtree IfNT)
Proof simp[panPEGTheory.pancake_peg_applied,else_arm_def]
QED

Theorem direct_arm:
  accepts pancake_peg s (mknt IfNT) rest [inner] ⇒
  accepts pancake_peg ((KeywordT ElseK,k)::s) else_arm rest [inner]
Proof
  strip_tac >> simp[else_arm_def,try_default_def,choices] >> disj1_tac >>
  simp[panPEGTheory.seql_def,list_wrap,seq_accept,consume_kw_def,consume_tok_def,
       choices,observe_tok]
QED

Theorem braced_arm:
  accepts pancake_peg s (mknt IfNT) ((RCurT,l)::rest) [inner] ⇒
  accepts pancake_peg ((KeywordT ElseK,k)::(LCurT,b)::s) else_arm rest
    [mknode ProgNT [inner]]
Proof
  strip_tac >> drule_then assume_tac singleton_if_body >>
  ‘rejects pancake_peg ((LCurT,b)::s) (mknt IfNT)’ by
    (PURE_ONCE_REWRITE_TAC [nt_rw nt_rejects “IfNT”] >>
     simp[reject_first,consume_kw_def,consume_tok_def,observe_tok]) >>
  simp[else_arm_def,try_default_def,choices] >> disj1_tac >>
  simp[panPEGTheory.seql_def,list_wrap,seq_accept,consume_kw_def,consume_tok_def,
       choices,observe_tok]
QED
