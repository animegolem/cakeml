Theory elseifMeaning
Ancestors panPtreeConversion panPEG grammar location

(* BlockNT returns its IfNT child directly. ProgNT adds this one-child
   wrapper when the next ProgNT consumes the closing brace and returns []. *)
Theorem singleton_block:
  conv_Prog (mknode ProgNT [t]) = conv_Prog t
Proof simp[mknode_def,Once conv_Prog_def,isNT_def]
QED

Theorem singleton_span:
  ptree_loc (mknode ProgNT [t]) = ptree_loc t
Proof simp[mknode_def,ptree_loc_def,ptree_list_loc_def,merge_list_locs_def]
QED

Theorem if_else_cong:
  ptree_loc a = ptree_loc b ∧ conv_Prog a = conv_Prog b ⇒
  conv_Prog (mknode IfNT [c;t;a]) = conv_Prog (mknode IfNT [c;t;b])
Proof
  simp[mknode_def,ptree_list_loc_def,Once conv_Prog_def,isNT_def,
       add_locs_annot_def,parsetree_locs_def] >>
  simp[Once conv_Prog_def,isNT_def,add_locs_annot_def,parsetree_locs_def]
QED

Theorem A_step:
  conv_Prog (mknode IfNT [c;t;inner]) =
  conv_Prog (mknode IfNT [c;t;mknode ProgNT [inner]])
Proof irule if_else_cong >> simp[singleton_block,singleton_span]
QED

(* Each frame is the condition and then-branch of an enclosing IfNT.
   The tail is shared and can itself be any completed conditional. *)
Definition if_chain_def:
  if_chain braced [] tail = tail ∧
  if_chain braced ((c,t)::frames) tail =
    mknode IfNT [c;t;
      if braced then mknode ProgNT [if_chain braced frames tail]
      else if_chain braced frames tail]
End

Theorem A_chain:
  ∀frames tail.
    ptree_loc (if_chain F frames tail) = ptree_loc (if_chain T frames tail) ∧
    conv_Prog (if_chain F frames tail) = conv_Prog (if_chain T frames tail)
Proof
  Induct >> simp[if_chain_def] >> Cases >>
  simp[if_chain_def] >> rpt strip_tac
  >- simp[mknode_def,ptree_loc_def,ptree_list_loc_def,merge_list_locs_def]
  >> irule if_else_cong >> simp[singleton_block,singleton_span]
QED
