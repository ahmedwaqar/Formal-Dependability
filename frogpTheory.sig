signature frogpTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val UNIONL_def : thm
    val pipeline_def : thm
    val rel_pipeline_z2_def : thm
    val rel_pipeline_z4_def : thm
  
  (*  Theorems  *)
    val IN_UNIONL : thm
    val len_mem_list_le_def : thm
    val len_mem_list_le_ind : thm
    val rel_pipeline_series : thm
    val rel_pipeline_z1_def : thm
    val rel_pipeline_z1_ind : thm
    val rel_pipeline_z1_thm : thm
    val rel_pipeline_z2_thm : thm
    val rel_pipeline_z3_THM : thm
    val rel_pipeline_z3_lemma4 : thm
    val rel_pipeline_z4_THM : thm
    val rel_pipeline_z4_lemma2 : thm
    val series_exp_list_sum : thm
  
  val frogp_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ASN_gateway] Parent theory of "frogp"
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [pipeline_def]  Definition
      
      ⊢ ∀p L. pipeline p L = prob p (rbd_struct p (series (rbd_list L)))
   
   [rel_pipeline_z2_def]  Definition
      
      ⊢ ∀p L t.
            rel_pipeline_z2 p L t =
            prob p
              (rbd_struct p
                 ((series of
                   (λa. parallel (rbd_list (rel_event_list p a t)))) L))
   
   [rel_pipeline_z4_def]  Definition
      
      ⊢ ∀p L1 L2 L3 t.
            rel_pipeline_z4 p L1 L2 L3 t =
            prob p
              (rbd_struct p ((series of (λa. parallel (rbd_list a))) L1) ∩
               rbd_struct p ((series of (λa. parallel (rbd_list a))) L2) ∩
               rbd_struct p ((series of (λa. parallel (rbd_list a))) L3))
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [len_mem_list_le_def]  Theorem
      
      ⊢ len_mem_list_le 3 L ⇔ ∀x. MEM x L ⇒ LENGTH x ≤ 3
   
   [len_mem_list_le_ind]  Theorem
      
      ⊢ ∀P. (∀L. P 3 L) ∧ (∀v5 v6. P v5 v6) ⇒ ∀v v1. P v v1
   
   [rel_pipeline_series]  Theorem
      
      ⊢ ∀p L t C.
            0 ≤ t ∧ prob_space p ∧ exp_dist_list p L C ∧
            (LENGTH C = LENGTH L) ∧ ¬NULL (rel_event_list p L t) ∧
            mutual_indep p (rel_event_list p L t) ∧
            (∀x. MEM x (rel_event_list p L t) ⇒ x ∈ events p) ⇒
            (pipeline p (rel_event_list p L t) = exp (-list_sum C * t))
   
   [rel_pipeline_z1_def]  Theorem
      
      ⊢ rel_pipeline_z1 p X 2 3 =
        prob p
          (BIGUNION
             (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                {x | 2 ≤ x ∧ x < SUC 3}))
   
   [rel_pipeline_z1_ind]  Theorem
      
      ⊢ ∀P.
            (∀p X. P p X 2 3) ∧ (∀v14 v13 v12. P v14 v13 2 v12) ∧
            (∀v18 v17 v15 v16. P v18 v17 v15 v16) ⇒
            ∀v v1 v2 v3. P v v1 v2 v3
   
   [rel_pipeline_z1_thm]  Theorem
      
      ⊢ ∀p p' X C L t.
            prob_space p ∧ prob_space p' ∧
            (∀x. MEM x (rel_event_list p' L t) ⇒ x ∈ events p') ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC 3) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial 3 x *
                 pipeline p' (rel_event_list p' L t) pow x *
                 (1 − pipeline p' (rel_event_list p' L t)) pow (3 − x)) ∧
            ¬NULL (rel_event_list p' L t) ∧ 0 ≤ t ∧ exp_dist_list p' L C ∧
            (LENGTH C = LENGTH L) ∧ mutual_indep p' (rel_event_list p' L t) ⇒
            (rel_pipeline_z1 p X 2 3 =
             3 * exp (2 * -(list_sum C * t)) *
             (1 − exp (-(list_sum C * t))) + exp (3 * -(list_sum C * t)))
   
   [rel_pipeline_z2_thm]  Theorem
      
      ⊢ ∀L C p t.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (FLAT (two_dim_rel_event_list p L t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p (FLAT (two_dim_rel_event_list p L t)) ∧
            (LENGTH C = LENGTH L) ∧
            (∀n. LENGTH (EL n L) = LENGTH (EL n C)) ∧
            two_dim_exp_dist_list p L C ∧ len_mem_list_le 3 L ⇒
            (rel_pipeline_z2 p L t =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
   
   [rel_pipeline_z3_THM]  Theorem
      
      ⊢ ∀L1 L2 C1 C2 p t.
            (∀z. MEM z (L1 ⧺ L2) ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (FLAT (two_dim_rel_event_list p (L1 ⧺ L2) t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p (FLAT (two_dim_rel_event_list p (L1 ⧺ L2) t)) ∧
            (LENGTH C1 = LENGTH L1) ∧ (LENGTH C2 = LENGTH L2) ∧
            (∀n. LENGTH (EL n L1) = LENGTH (EL n C1)) ∧
            (∀n. LENGTH (EL n L2) = LENGTH (EL n C2)) ∧
            two_dim_exp_dist_list p L1 C1 ∧ two_dim_exp_dist_list p L2 C2 ∧
            len_mem_list_le 2 L1 ∧ len_mem_list_le 2 L2 ⇒
            (prob p
               (rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L1) ∩
                rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L2)) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C1 *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C2)
   
   [rel_pipeline_z3_lemma4]  Theorem
      
      ⊢ ∀L1 L2 p.
            (∀z. MEM z (L1 ⧺ L2) ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT (L1 ⧺ L2)) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (L1 ⧺ L2)) ⇒
            (prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L1) ∩
                rbd_struct p ((series of (λa. parallel (rbd_list a))) L2)) =
             prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L1)) *
             prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L2)))
   
   [rel_pipeline_z4_THM]  Theorem
      
      ⊢ ∀L1 L2 L3 C1 C2 C3 p t.
            (∀z. MEM z (L1 ⧺ L2 ⧺ L3) ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (FLAT (two_dim_rel_event_list p (L1 ⧺ L2 ⧺ L3) t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p
              (FLAT (two_dim_rel_event_list p (L1 ⧺ L2 ⧺ L3) t)) ∧
            (LENGTH C1 = LENGTH L1) ∧ (LENGTH C2 = LENGTH L2) ∧
            (LENGTH C3 = LENGTH L3) ∧
            (∀n. LENGTH (EL n L1) = LENGTH (EL n C1)) ∧
            (∀n. LENGTH (EL n L2) = LENGTH (EL n C2)) ∧
            (∀n. LENGTH (EL n L3) = LENGTH (EL n C3)) ∧
            two_dim_exp_dist_list p L1 C1 ∧ two_dim_exp_dist_list p L2 C2 ∧
            two_dim_exp_dist_list p L3 C3 ∧ len_mem_list_le 2 L1 ∧
            len_mem_list_le 2 L2 ∧ len_mem_list_le 2 L3 ⇒
            (prob p
               (rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L1) ∩
                rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L2) ∩
                rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L3)) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C1 *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C2 *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C3)
   
   [rel_pipeline_z4_lemma2]  Theorem
      
      ⊢ ∀L1 L2 L3 p.
            (∀z. MEM z (L1 ⧺ L2 ⧺ L3) ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT (L1 ⧺ L2 ⧺ L3)) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (L1 ⧺ L2 ⧺ L3)) ⇒
            (prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L1) ∩
                rbd_struct p ((series of (λa. parallel (rbd_list a))) L2) ∩
                rbd_struct p ((series of (λa. parallel (rbd_list a))) L3)) =
             prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L1)) *
             prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L2) ∩
                rbd_struct p ((series of (λa. parallel (rbd_list a))) L3)))
   
   [series_exp_list_sum]  Theorem
      
      ⊢ ∀p t L C.
            0 ≤ t ∧ prob_space p ∧ exp_dist_list p L C ∧
            (LENGTH C = LENGTH L) ∧
            (∀z. MEM z (rel_event_list p L t) ⇒ z ∈ events p) ⇒
            (list_prod (list_prob p (rel_event_list p L t)) =
             exp_func t (list_sum C))
   
   
*)
end
