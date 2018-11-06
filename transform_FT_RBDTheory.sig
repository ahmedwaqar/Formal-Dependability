signature transform_FT_RBDTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val UNIONL_def : thm
  
  (*  Theorems  *)
    val AND_OR_to_series_parallel : thm
    val AND_to_series : thm
    val IN_UNIONL : thm
    val Inhibit_gate_transform : thm
    val NAND_gate_transform : thm
    val NOR_gate_transform : thm
    val OR_AND_to_parallel_series : thm
    val OR_to_parallel : thm
    val comp_gate_transform : thm
    val k_out_N_to_majority_voting_gate : thm
  
  val transform_FT_RBD_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ASN_gateway] Parent theory of "transform_FT_RBD"
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [AND_OR_to_series_parallel]  Theorem
      
      ⊢ ∀p L.
            FTree p ((AND of (λa. OR (gate_list a))) L) =
            rbd_struct p ((series of (λa. parallel (rbd_list a))) L)
   
   [AND_to_series]  Theorem
      
      ⊢ ∀p L.
            FTree p (AND (gate_list L)) =
            rbd_struct p (series (rbd_list L))
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [Inhibit_gate_transform]  Theorem
      
      ⊢ ∀p A B C.
            prob_space p ∧ C ∈ events p ⇒
            (FTree p (AND [OR [atomic A; atomic B]; NOT (atomic C)]) =
             rbd_struct p (parallel [atomic A; atomic B]) ∩
             (p_space p DIFF rbd_struct p (atomic C)))
   
   [NAND_gate_transform]  Theorem
      
      ⊢ ∀L1 L2 n p.
            FTree p (AND (gate_list (compl_list p L1 ⧺ L2))) =
            rbd_struct p (series (rbd_list (compl_list p L1 ⧺ L2)))
   
   [NOR_gate_transform]  Theorem
      
      ⊢ ∀p L.
            p_space p DIFF FTree p (OR (gate_list L)) =
            p_space p DIFF rbd_struct p (parallel (rbd_list L))
   
   [OR_AND_to_parallel_series]  Theorem
      
      ⊢ ∀p L.
            FTree p ((OR of (λa. AND (gate_list a))) L) =
            rbd_struct p ((parallel of (λa. series (rbd_list a))) L)
   
   [OR_to_parallel]  Theorem
      
      ⊢ ∀p L.
            FTree p (OR (gate_list L)) =
            rbd_struct p (parallel (rbd_list L))
   
   [comp_gate_transform]  Theorem
      
      ⊢ ∀p A B.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ⇒
            (FTree p
               (OR
                  [AND [atomic A; atomic B]; NOT (OR [atomic A; atomic B])]) =
             rbd_struct p (series [atomic A; atomic B]) ∪
             (p_space p DIFF rbd_struct p (parallel [atomic A; atomic B])))
   
   [k_out_N_to_majority_voting_gate]  Theorem
      
      ⊢ ∀p X k n. majority_voting_FT_gate p X k n = K_out_N_struct p X k n
   
   
*)
end
