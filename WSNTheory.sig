signature WSNTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val RMST_fail_rate_list_def : thm
    val UNIONL_def : thm
  
  (*  Theorems  *)
    val E2W_WSN : thm
    val ESRT_WSN : thm
    val IN_UNIONL : thm
    val RMST_WSN : thm
    val RMST_fail_rate_list_def_compute : thm
    val one_minus_exp_equi : thm
    val parallel_series_exp_fail_rate : thm
    val parallel_series_struct_rbd_v2 : thm
    val rel_parallel_series_exp_fail_rate : thm
  
  val WSN_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [smart_grid] Parent theory of "WSN"
   
   [RMST_fail_rate_list_def]  Definition
      
      ⊢ (∀a b. RMST_fail_rate_list a b 0 = []) ∧
        ∀a b n.
            RMST_fail_rate_list a b (SUC n) =
            [a; b]::RMST_fail_rate_list a b n
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [E2W_WSN]  Theorem
      
      ⊢ ∀p t X_fil X_aggr X_rout C_fil C_aggr C_rout.
            0 ≤ t ∧ prob_space p ∧
            exp_dist_list p [X_fil; X_aggr; X_rout] [C_fil; C_aggr; C_rout] ∧
            mutual_indep p (rel_event_list p [X_fil; X_aggr; X_rout] t) ∧
            (∀x.
                 MEM x (rel_event_list p [X_fil; X_aggr; X_rout] t) ⇒
                 x ∈ events p) ⇒
            (prob p
               (rbd_struct p
                  (series
                     (rbd_list (rel_event_list p [X_fil; X_aggr; X_rout] t)))) =
             exp (-list_sum [C_fil; C_aggr; C_rout] * t))
   
   [ESRT_WSN]  Theorem
      
      ⊢ ∀p t X_routing_list C_routing_list.
            0 ≤ t ∧ prob_space p ∧
            ¬NULL (rel_event_list p X_routing_list t) ∧
            exp_dist_list p X_routing_list C_routing_list ∧
            (LENGTH X_routing_list = LENGTH C_routing_list) ∧
            mutual_indep p (rel_event_list p X_routing_list t) ∧
            (∀x. MEM x (rel_event_list p X_routing_list t) ⇒ x ∈ events p) ⇒
            (prob p
               (rbd_struct p
                  (parallel (rbd_list (rel_event_list p X_routing_list t)))) =
             1 − list_prod (one_minus_exp t C_routing_list))
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [RMST_WSN]  Theorem
      
      ⊢ ∀p t X_rout X_MLD C_rout C_MLD n.
            (∀z. MEM z (RMST_fail_rate_list X_rout X_MLD n) ⇒ ¬NULL z) ∧
            0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (two_dim_rel_event_list p
                         (RMST_fail_rate_list X_rout X_MLD n) t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p
              (FLAT
                 (two_dim_rel_event_list p
                    (RMST_fail_rate_list X_rout X_MLD n) t)) ∧
            (LENGTH (RMST_fail_rate_list C_rout C_MLD n) =
             LENGTH (RMST_fail_rate_list X_rout X_MLD n)) ∧
            (∀n'.
                 n' < LENGTH (RMST_fail_rate_list X_rout X_MLD n) ∧
                 n' < LENGTH (RMST_fail_rate_list C_rout C_MLD n) ⇒
                 (LENGTH (EL n' (RMST_fail_rate_list X_rout X_MLD n)) =
                  LENGTH (EL n' (RMST_fail_rate_list C_rout C_MLD n)))) ∧
            two_dim_exp_dist_list p (RMST_fail_rate_list X_rout X_MLD n)
              (RMST_fail_rate_list C_rout C_MLD n) ⇒
            (prob p
               (rbd_struct p
                  ((parallel of (λa. series (rbd_list a)))
                     (two_dim_rel_event_list p
                        (RMST_fail_rate_list X_rout X_MLD n) t))) =
             1 −
             (list_prod ∘ one_minus_list of
              (λa. list_prod (exp_func_list a t)))
               (RMST_fail_rate_list C_rout C_MLD n))
   
   [RMST_fail_rate_list_def_compute]  Theorem
      
      ⊢ (∀a b. RMST_fail_rate_list a b 0 = []) ∧
        (∀a b n.
             RMST_fail_rate_list a b (NUMERAL (BIT1 n)) =
             [a; b]::RMST_fail_rate_list a b (NUMERAL (BIT1 n) − 1)) ∧
        ∀a b n.
            RMST_fail_rate_list a b (NUMERAL (BIT2 n)) =
            [a; b]::RMST_fail_rate_list a b (NUMERAL (BIT1 n))
   
   [one_minus_exp_equi]  Theorem
      
      ⊢ ∀t c. one_minus_list (exp_func_list c t) = one_minus_exp t c
   
   [parallel_series_exp_fail_rate]  Theorem
      
      ⊢ ∀p t L C.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (FLAT (two_dim_rel_event_list p L t)) ⇒
                 x' ∈ events p) ∧ (LENGTH C = LENGTH L) ∧
            (∀n.
                 n < LENGTH L ∧ n < LENGTH C ⇒
                 (LENGTH (EL n L) = LENGTH (EL n C))) ∧
            two_dim_exp_dist_list p L C ⇒
            (1 −
             (list_prod ∘ one_minus_list of (λa. list_prod (list_prob p a)))
               (two_dim_rel_event_list p L t) =
             1 −
             (list_prod ∘ one_minus_list of
              (λa. list_prod (exp_func_list a t))) C)
   
   [parallel_series_struct_rbd_v2]  Theorem
      
      ⊢ ∀p L.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT L) ⇒
            (prob p
               (rbd_struct p ((parallel of (λa. series (rbd_list a))) L)) =
             1 −
             (list_prod ∘ one_minus_list of (λa. list_prod (list_prob p a)))
               L)
   
   [rel_parallel_series_exp_fail_rate]  Theorem
      
      ⊢ ∀p t L C.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (FLAT (two_dim_rel_event_list p L t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p (FLAT (two_dim_rel_event_list p L t)) ∧
            (LENGTH C = LENGTH L) ∧
            (∀n.
                 n < LENGTH L ∧ n < LENGTH C ⇒
                 (LENGTH (EL n L) = LENGTH (EL n C))) ∧
            two_dim_exp_dist_list p L C ⇒
            (prob p
               (rbd_struct p
                  ((parallel of (λa. series (rbd_list a)))
                     (two_dim_rel_event_list p L t))) =
             1 −
             (list_prod ∘ one_minus_list of
              (λa. list_prod (exp_func_list a t))) C)
   
   
*)
end
