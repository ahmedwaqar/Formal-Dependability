signature smart_gridTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val G1_FT_def : thm
    val G2_FT_def : thm
    val G3_FT_def : thm
    val G4_FT_def : thm
    val K_out_N_struct_list_def : thm
    val SABP_FT_def : thm
    val UNIONL_def : thm
    val binomial_conds_def : thm
    val binomial_distr_def : thm
    val binomial_event_def : thm
    val binomial_event_list_def : thm
    val casc_series_RBD_def : thm
    val in_events_def : thm
    val in_events_k_out_n_def : thm
    val k_out_n_event_def : thm
    val not_null_def : thm
    val rbd_conds_def : thm
    val redund_star_ring_RBD_def : thm
  
  (*  Theorems  *)
    val IN_UNIONL : thm
    val SABP_FT_alt_form : thm
    val SABP_FT_alt_form1 : thm
    val bigunion_in_events : thm
    val fail_prob_SABP_FT : thm
    val fail_prob_SABP_FT_lem1 : thm
    val k_out_n_RBD_v2 : thm
    val k_out_n_alt : thm
    val len_EL_lem1 : thm
    val parallel_rbd_indep_k_out_n_rbd : thm
    val parallel_rbd_indep_k_out_n_rbd_v1 : thm
    val rel_casc_seriesRBD : thm
    val rel_redund_star_ringRBD : thm
    val series_parallel_rbd_indep_k_out_n_rbd_exp_dist : thm
    val series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval : thm
    val series_rbd_indep_k_out_n_rbd : thm
  
  val smart_grid_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ASN_gateway] Parent theory of "smart_grid"
   
   [G1_FT_def]  Definition
      
      ⊢ ∀p t SW1 L1_220 L2_220 L3_220 L4_220.
            G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
            AND
              (gate_list
                 (fail_event_list p [SW1; L1_220; L2_220; L3_220; L4_220] t))
   
   [G2_FT_def]  Definition
      
      ⊢ ∀p t SW1 L1_220 L2_220 L3_220 L4_220.
            G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
            AND
              (gate_list
                 (fail_event_list p [SW1; L1_220; L2_220; L3_220; L4_220] t))
   
   [G3_FT_def]  Definition
      
      ⊢ ∀p t SW2 T1_220 T2_220 BUS_220 SS_220.
            G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
            AND
              (gate_list
                 (fail_event_list p [SW2; T1_220; T2_220; BUS_220; SS_220]
                    t))
   
   [G4_FT_def]  Definition
      
      ⊢ ∀p t SW2 T1_220 T2_220 BUS_220 SS_220.
            G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
            AND
              (gate_list
                 (fail_event_list p [SW2; T1_220; T2_220; BUS_220; SS_220]
                    t))
   
   [K_out_N_struct_list_def]  Definition
      
      ⊢ ∀p L k n.
            K_out_N_struct_list p L k n =
            MAP (λa. K_out_N_struct p a k n) L
   
   [SABP_FT_def]  Definition
      
      ⊢ ∀p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220
            SS_220.
            SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220
              BUS_220 SS_220 =
            FTree p
              (AND
                 [OR
                    [G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220;
                     G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220];
                  OR
                    [G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220;
                     G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220]])
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [binomial_conds_def]  Definition
      
      ⊢ ∀p X X1 k n L t.
            binomial_conds p X X1 k n L t ⇔
            k < SUC n ∧
            (∀x. x < SUC n ⇒ in_events p (binomial_event_list L x)) ∧
            ∀x.
                distribution p X {Normal (&x)} =
                &binomial n x * Reliability p X1 t pow x *
                (1 − Reliability p X1 t) pow (n − x)
   
   [binomial_distr_def]  Definition
      
      ⊢ ∀p X n pr.
            binomial_distr p X n pr ⇔
            ∀x.
                distribution p X {Normal (&x)} =
                &binomial n x * pr pow x * (1 − pr) pow (n − x)
   
   [binomial_event_def]  Definition
      
      ⊢ ∀X a. binomial_event X a = PREIMAGE X {Normal (&a)}
   
   [binomial_event_list_def]  Definition
      
      ⊢ ∀L m. binomial_event_list L m = MAP (λa. binomial_event a m) L
   
   [casc_series_RBD_def]  Definition
      
      ⊢ ∀p PIED ESW_list CIED t.
            casc_series_RBD p PIED ESW_list CIED t =
            rbd_struct p
              (series
                 (rbd_list
                    (rel_event_list p ([PIED] ⧺ ESW_list ⧺ [CIED]) t)))
   
   [in_events_def]  Definition
      
      ⊢ ∀p L. in_events p L ⇔ ∀x. MEM x L ⇒ x ∈ events p
   
   [in_events_k_out_n_def]  Definition
      
      ⊢ ∀p X n.
            in_events_k_out_n p X n ⇔
            (λx. PREIMAGE X {Normal (&x)}) ∈ (count (SUC n) -> events p)
   
   [k_out_n_event_def]  Definition
      
      ⊢ ∀p X k n.
            k_out_n_event p X k n =
            PREIMAGE X (BIGUNION {{Normal (&x)} | k ≤ x ∧ x < SUC n})
   
   [not_null_def]  Definition
      
      ⊢ ∀L. not_null L ⇔ ∀x. MEM x L ⇒ ¬NULL x
   
   [rbd_conds_def]  Definition
      
      ⊢ ∀p L.
            rbd_conds p L ⇔ prob_space p ∧ in_events p L ∧ mutual_indep p L
   
   [redund_star_ring_RBD_def]  Definition
      
      ⊢ ∀p PIED list_ESW_list CIED t.
            redund_star_ring_RBD p PIED list_ESW_list CIED t =
            rbd_struct p
              ((series of (λa. parallel (rbd_list (rel_event_list p a t))))
                 ([[PIED]] ⧺ list_ESW_list ⧺ [[CIED]]))
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [SABP_FT_alt_form]  Theorem
      
      ⊢ ∀A B C D. (A ∪ B) ∩ (C ∪ D) = A ∩ C ∪ A ∩ D ∪ B ∩ C ∪ B ∩ D
   
   [SABP_FT_alt_form1]  Theorem
      
      ⊢ ∀p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220
            SS_220.
            prob_space p ⇒
            (SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220
               BUS_220 SS_220 =
             rbd_struct p
               ((parallel of (λa. series (rbd_list a)))
                  (list_fail_event_list p
                     [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                       T2_220; BUS_220; SS_220];
                      [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                       T2_220; BUS_220; SS_220];
                      [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                       T2_220; BUS_220; SS_220];
                      [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                       T2_220; BUS_220; SS_220]] t)))
   
   [bigunion_in_events]  Theorem
      
      ⊢ ∀p n k X.
            prob_space p ∧
            (λx. PREIMAGE X {Normal (&x)}) ∈ (count (SUC n) -> events p) ⇒
            BIGUNION
              (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                 {x | k ≤ x ∧ x < SUC n}) ∈ events p
   
   [fail_prob_SABP_FT]  Theorem
      
      ⊢ ∀p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220
            SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220
            C_T2_220 C_BUS_220 C_SS_220.
            0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x'
                   (fail_event_list p
                      [SW1; SW2; L1_220; L2_220; L3_220; L4_220; T1_220;
                       T2_220; BUS_220; SS_220] t) ⇒
                 x' ∈ events p) ∧
            mutual_indep p
              (FLAT
                 (list_fail_event_list p
                    [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                      T2_220; BUS_220; SS_220];
                     [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                      T2_220; BUS_220; SS_220];
                     [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                      T2_220; BUS_220; SS_220];
                     [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                      T2_220; BUS_220; SS_220]] t)) ∧
            list_exp p
              [C_SW1; C_SW2; C_L1_220; C_L2_220; C_L3_220; C_L4_220;
               C_T1_220; C_T2_220; C_BUS_220; C_SS_220]
              [SW1; SW2; L1_220; L2_220; L3_220; L4_220; T1_220; T2_220;
               BUS_220; SS_220] ⇒
            (prob p
               (SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220
                  T2_220 BUS_220 SS_220) =
             1 −
             list_prod
               (one_minus_exp_prod t
                  [[C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220]]))
   
   [fail_prob_SABP_FT_lem1]  Theorem
      
      ⊢ ∀p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220
            SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220
            C_T2_220 C_BUS_220 C_SS_220.
            0 ≤ t ∧ prob_space p ∧
            list_exp p
              [C_SW1; C_SW2; C_L1_220; C_L2_220; C_L3_220; C_L4_220;
               C_T1_220; C_T2_220; C_BUS_220; C_SS_220]
              [SW1; SW2; L1_220; L2_220; L3_220; L4_220; T1_220; T2_220;
               BUS_220; SS_220] ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p
                        [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                          T2_220; BUS_220; SS_220];
                         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                          T2_220; BUS_220; SS_220];
                         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                          T2_220; BUS_220; SS_220];
                         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220;
                          T2_220; BUS_220; SS_220]] t))) =
             list_prod
               (one_minus_exp_prod t
                  [[C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220];
                   [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2;
                    C_T1_220; C_T2_220; C_BUS_220; C_SS_220]]))
   
   [k_out_n_RBD_v2]  Theorem
      
      ⊢ ∀p n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)}) ∈ (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (prob p (K_out_N_struct p X k n) =
             sum (k,SUC n − k)
               (λx. &binomial n x * pr pow x * (1 − pr) pow (n − x)))
   
   [k_out_n_alt]  Theorem
      
      ⊢ ∀p X k n.
            prob_space p ∧
            (λx. PREIMAGE X {Normal (&x)}) ∈ (count (SUC n) -> events p) ⇒
            (K_out_N_struct p X k n =
             BIGUNION
               (IMAGE (PREIMAGE X) {{Normal (&x)} | k ≤ x ∧ x < SUC n}))
   
   [len_EL_lem1]  Theorem
      
      ⊢ ∀h1 h2 c1 c2 L C n.
            (LENGTH L = LENGTH C) ∧ n < LENGTH L + 2 ∧
            (∀n.
                 n < LENGTH L ∧ n < LENGTH C ⇒
                 (LENGTH (EL n L) = LENGTH (EL n C))) ⇒
            (LENGTH (EL n ([h1]::(L ⧺ [[h2]]))) =
             LENGTH (EL n ([c1]::(C ⧺ [[c2]]))))
   
   [parallel_rbd_indep_k_out_n_rbd]  Theorem
      
      ⊢ ∀p L1 L n k pr.
            prob_space p ∧
            mutual_indep p (FLAT (K_out_N_struct_list p L1 k n::L)) ∧
            in_events p (FLAT L) ∧
            (∀k. k < SUC n ⇒ in_events p (binomial_event_list L1 k)) ∧
            not_null L ∧ ¬NULL (K_out_N_struct_list p L1 k n) ⇒
            (prob p
               (rbd_struct p
                  (parallel (rbd_list (K_out_N_struct_list p L1 k n))) ∩
                rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))) =
             (1 −
              list_prod
                (one_minus_list
                   (list_prob p (K_out_N_struct_list p L1 k n)))) *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (list_prob p a)))) L)
   
   [parallel_rbd_indep_k_out_n_rbd_v1]  Theorem
      
      ⊢ ∀p L1 L n k pr.
            prob_space p ∧
            mutual_indep p (FLAT (K_out_N_struct_list p L1 k n::L)) ∧
            in_events p (FLAT L) ∧
            (∀k. k < SUC n ⇒ in_events p (binomial_event_list L1 k)) ∧
            not_null L ∧ ¬NULL (K_out_N_struct_list p L1 k n) ⇒
            (prob p
               (rbd_struct p
                  (parallel (rbd_list (K_out_N_struct_list p L1 k n))) ∩
                rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))) =
             (1 −
              list_prod
                (one_minus_list
                   (list_prob p (K_out_N_struct_list p L1 k n)))) *
             prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L)))
   
   [rel_casc_seriesRBD]  Theorem
      
      ⊢ ∀p t PIED ESW_list CIED C_PIED C_ESW_list C_CIED.
            0 ≤ t ∧ prob_space p ∧ ¬NULL ESW_list ∧
            exp_dist_list p ([PIED] ⧺ ESW_list ⧺ [CIED])
              ([C_PIED] ⧺ C_ESW_list ⧺ [C_CIED]) ∧
            (LENGTH C_ESW_list = LENGTH ESW_list) ∧
            mutual_indep p
              (rel_event_list p ([PIED] ⧺ ESW_list ⧺ [CIED]) t) ∧
            (∀x.
                 MEM x (rel_event_list p ([PIED] ⧺ ESW_list ⧺ [CIED]) t) ⇒
                 x ∈ events p) ⇒
            (prob p (casc_series_RBD p PIED ESW_list CIED t) =
             list_prod (exp_func_list ([C_PIED] ⧺ C_ESW_list ⧺ [C_CIED]) t))
   
   [rel_redund_star_ringRBD]  Theorem
      
      ⊢ ∀p t PIED list_ESW_list CIED C_PIED C_list_ESW_list C_CIED.
            (∀z. MEM z list_ESW_list ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (two_dim_rel_event_list p
                         ([[PIED]] ⧺ list_ESW_list ⧺ [[CIED]]) t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p
              (FLAT
                 (two_dim_rel_event_list p
                    ([[PIED]] ⧺ list_ESW_list ⧺ [[CIED]]) t)) ∧
            (LENGTH C_list_ESW_list = LENGTH list_ESW_list) ∧
            (∀n.
                 n < LENGTH list_ESW_list ∧ n < LENGTH C_list_ESW_list ⇒
                 (LENGTH (EL n list_ESW_list) =
                  LENGTH (EL n C_list_ESW_list))) ∧
            two_dim_exp_dist_list p ([[PIED]] ⧺ list_ESW_list ⧺ [[CIED]])
              ([[C_PIED]] ⧺ C_list_ESW_list ⧺ [[C_CIED]]) ⇒
            (prob p (redund_star_ring_RBD p PIED list_ESW_list CIED t) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t))))
               ([[C_PIED]] ⧺ C_list_ESW_list ⧺ [[C_CIED]]))
   
   [series_parallel_rbd_indep_k_out_n_rbd_exp_dist]  Theorem
      
      ⊢ ∀p PIED ESW1 ESW2 ESW3 ESW4 ESWs CIED C_PIED C_ESW1 C_ESW2 C_ESW3
            C_ESW4 C_ESWs C_CIED pr t.
            0 ≤ t ∧ prob_space p ∧
            mutual_indep p
              (FLAT
                 (K_out_N_struct_list p [ESWs; ESWs] 3 4::
                      two_dim_rel_event_list p
                        [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ∧
            in_events p
              (FLAT
                 (two_dim_rel_event_list p
                    [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ∧
            (∀x.
                 x < SUC 4 ⇒
                 in_events p (binomial_event_list [ESWs; ESWs] x)) ∧
            (∀x.
                 distribution p ESWs {Normal (&x)} =
                 &binomial 4 x * pr pow x * (1 − pr) pow (4 − x)) ∧
            two_dim_exp_dist_list p
              [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]
              [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] ⇒
            (prob p
               (rbd_struct p
                  (parallel
                     (rbd_list (K_out_N_struct_list p [ESWs; ESWs] 3 4))) ∩
                rbd_struct p
                  (series
                     (MAP (λa. parallel (rbd_list a))
                        (two_dim_rel_event_list p
                           [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)))) =
             (1 −
              (1 −
               sum (3,SUC 4 − 3)
                 (λx. &binomial 4 x * pr pow x * (1 − pr) pow (4 − x))) *
              (1 −
               sum (3,SUC 4 − 3)
                 (λx. &binomial 4 x * pr pow x * (1 − pr) pow (4 − x)))) *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t))))
               [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]])
   
   [series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval]  Theorem
      
      ⊢ ∀p PIED ESW1 ESW2 ESW3 ESW4 ESWs CIED X_bino C_PIED C_ESW1 C_ESW2
            C_ESW3 C_ESW4 C_ESWs C_CIED t.
            0 ≤ t ∧ prob_space p ∧
            mutual_indep p
              (FLAT
                 (K_out_N_struct_list p [X_bino; X_bino] 3 4::
                      two_dim_rel_event_list p
                        [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ∧
            in_events p
              (FLAT
                 (two_dim_rel_event_list p
                    [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ∧
            (∀x.
                 x < SUC 4 ⇒
                 in_events p (binomial_event_list [X_bino; X_bino] x)) ∧
            (∀x.
                 distribution p X_bino {Normal (&x)} =
                 &binomial 4 x * Reliability p ESWs t pow x *
                 (1 − Reliability p ESWs t) pow (4 − x)) ∧
            exp_dist p ESWs C_ESWs ∧
            two_dim_exp_dist_list p
              [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]
              [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] ⇒
            (prob p
               (rbd_struct p
                  (parallel
                     (rbd_list (K_out_N_struct_list p [X_bino; X_bino] 3 4))) ∩
                rbd_struct p
                  (series
                     (MAP (λa. parallel (rbd_list a))
                        (two_dim_rel_event_list p
                           [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)))) =
             (1 −
              (1 −
               sum (3,SUC 4 − 3)
                 (λx.
                      &binomial 4 x * exp (-C_ESWs * t) pow x *
                      (1 − exp (-C_ESWs * t)) pow (4 − x))) *
              (1 −
               sum (3,SUC 4 − 3)
                 (λx.
                      &binomial 4 x * exp (-C_ESWs * t) pow x *
                      (1 − exp (-C_ESWs * t)) pow (4 − x)))) *
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t))))
               [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]])
   
   [series_rbd_indep_k_out_n_rbd]  Theorem
      
      ⊢ ∀p L n k X pr.
            prob_space p ∧ ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧
            mutual_indep p
              (L ⧺
               [PREIMAGE X (BIGUNION {{Normal (&x)} | k ≤ x ∧ x < SUC n})]) ∧
            k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)}) ∈ (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (prob p
               (rbd_struct p (series (rbd_list L)) ∩ K_out_N_struct p X k n) =
             list_prod (list_prob p L) *
             sum (k,SUC n − k)
               (λx. &binomial n x * pr pow x * (1 − pr) pow (n − x)))
   
   
*)
end
