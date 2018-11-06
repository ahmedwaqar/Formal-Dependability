signature AvailabilityTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val AND_unavail_FT_gate_def : thm
    val NAND_unavail_FT_gate_def : thm
    val NOR_unavail_FT_gate_def : thm
    val OR_unavail_FT_gate_def : thm
    val UNIONL_def : thm
    val XOR_unavail_FT_gate_def : thm
    val avail_event_def : thm
    val avail_event_list_def : thm
    val cdf_def : thm
    val compl_steady_state_avail_def : thm
    val expec_avail1_def : thm
    val expec_avail_def : thm
    val expec_def : thm
    val inst_avail_exp1_def : thm
    val inst_avail_exp2_def : thm
    val inst_avail_exp3_def : thm
    val inst_avail_exp_def : thm
    val inst_avail_exp_list1_def : thm
    val inst_avail_exp_list2_def : thm
    val inst_avail_exp_list_def : thm
    val inst_unavail_exp_def : thm
    val inst_unavail_exp_list_def : thm
    val list_union_avail_event_list_def : thm
    val rel_event1_def : thm
    val reliability_def : thm
    val steady_state_avail_def : thm
    val steady_state_avail_list_def : thm
    val steady_state_avail_prod_def : thm
    val steady_state_unavail_def : thm
    val steady_state_unavail_list_def : thm
    val two_dim_inst_avail_exp_def : thm
    val two_dim_inst_unavail_exp_def : thm
    val two_dim_steady_state_avail_list_def : thm
    val two_dim_steady_state_avail_prod_def : thm
    val unavail_event_def : thm
    val union_avail_event_list1_def : thm
    val union_avail_event_list_def : thm
    val union_avail_events1_def : thm
    val union_avail_events_def : thm
    val union_unavail_event_list_def : thm
    val union_unavail_events_def : thm
  
  (*  Theorems  *)
    val AND_gate_unavail : thm
    val AND_inst_avail_prod_tends_steady : thm
    val EXT_LE_LT : thm
    val IN_UNIONL : thm
    val LET_ANTISYM : thm
    val NAND_steady_state_avail : thm
    val OR_steady_state_unavail : thm
    val PERM_refl : thm
    val XOR_steady_unavail : thm
    val avail_ge_rel : thm
    val avail_ge_rel1 : thm
    val compl_fail_event_eq_rel_event1 : thm
    val compl_rel_event_eq_fail_event1 : thm
    val compl_steady_state_avail_equi : thm
    val in_events_normal_events : thm
    val inst_XOR_tends_steadty : thm
    val lim_inst_OR_tend_steady : thm
    val lim_inst_parall_series_tend_steady : thm
    val lim_inst_parall_tend_steady : thm
    val lim_inst_series_parall_tend_steady : thm
    val neg_exp_tend0_new : thm
    val not_null_leng : thm
    val parallel_rbd_avail : thm
    val series_expec_tends_prod_avail : thm
    val series_rbd_avail : thm
    val steady_avail_temp : thm
    val steady_state_NOR_unavail_FT_gate : thm
    val steady_state_avail : thm
    val steady_state_avail1 : thm
    val steady_state_parallel_series_ABD : thm
    val steady_state_series_parallel_avail : thm
  
  val Availability_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [FT_deep] Parent theory of "Availability"
   
   [VDC] Parent theory of "Availability"
   
   [AND_unavail_FT_gate_def]  Definition
      
      ⊢ ∀p L t.
            AND_unavail_FT_gate p L t =
            FTree p (AND (gate_list (union_unavail_event_list p L t)))
   
   [NAND_unavail_FT_gate_def]  Definition
      
      ⊢ ∀p L1 L2 t.
            NAND_unavail_FT_gate p L1 L2 t =
            FTree p
              (AND
                 (gate_list
                    (compl_list p (union_unavail_event_list p L1 t) ⧺
                     union_unavail_event_list p L2 t)))
   
   [NOR_unavail_FT_gate_def]  Definition
      
      ⊢ ∀p L t.
            NOR_unavail_FT_gate p L t =
            p_space p DIFF
            FTree p (OR (gate_list (union_unavail_event_list p L t)))
   
   [OR_unavail_FT_gate_def]  Definition
      
      ⊢ ∀p L t.
            OR_unavail_FT_gate p L t =
            FTree p (OR (gate_list (union_unavail_event_list p L t)))
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [XOR_unavail_FT_gate_def]  Definition
      
      ⊢ ∀p X Y t.
            XOR_unavail_FT_gate p X Y t =
            XOR_FT_gate p (atomic (union_unavail_events p X t))
              (atomic (union_unavail_events p Y t))
   
   [avail_event_def]  Definition
      
      ⊢ ∀L n t.
            avail_event L n t =
            {x |
            SIGMA (λa. FST (EL a L) x + SND (EL a L) x) (count n) ≤ t ∧
            t <
            SIGMA (λa. FST (EL a L) x + SND (EL a L) x) (count n) +
            FST (EL n L) x}
   
   [avail_event_list_def]  Definition
      
      ⊢ ∀L n t. avail_event_list L n t = MAP (λa. avail_event a n t) L
   
   [cdf_def]  Definition
      
      ⊢ ∀p X t. cdf p X t = distribution p X {y | y ≤ t}
   
   [compl_steady_state_avail_def]  Definition
      
      ⊢ (compl_steady_state_avail [] = 1) ∧
        ∀h t.
            compl_steady_state_avail (h::t) =
            (1 − steady_state_avail h) * compl_steady_state_avail t
   
   [expec_avail1_def]  Definition
      
      ⊢ ∀p L n t.
            expec_avail1 p L n t =
            sum (0,n) (prob p ∘ (λa. avail_event L a t))
   
   [expec_avail_def]  Definition
      
      ⊢ ∀p L n t.
            expec_avail p L n t =
            sum (0,n) (λa. prob p (avail_event L a t))
   
   [expec_def]  Definition
      
      ⊢ ∀n f. expec n f = sum (0,n) f
   
   [inst_avail_exp1_def]  Definition
      
      ⊢ ∀p L n m.
            inst_avail_exp1 p L n m ⇔
            ∀t.
                prob p (union_avail_events L n (&t)) =
                SND m / (SND m + FST m) +
                FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)
   
   [inst_avail_exp2_def]  Definition
      
      ⊢ ∀p L m.
            inst_avail_exp2 p L m ⇔
            ∀t.
                prob p (union_avail_events1 L (&t)) =
                SND m / (SND m + FST m) +
                FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)
   
   [inst_avail_exp3_def]  Definition
      
      ⊢ ∀p L m.
            inst_avail_exp3 p L m ⇔
            ∀t.
                prob p (union_avail_events1 L (&t) ∩ p_space p) =
                SND m / (SND m + FST m) +
                FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)
   
   [inst_avail_exp_def]  Definition
      
      ⊢ ∀p L n m.
            inst_avail_exp p L n m ⇔
            ∀t.
                expec n (λa. prob p (avail_event L a (Normal t))) =
                SND m / (SND m + FST m) +
                FST m / (SND m + FST m) * exp (-(SND m + FST m) * t)
   
   [inst_avail_exp_list1_def]  Definition
      
      ⊢ (∀p M. inst_avail_exp_list1 p [] M ⇔ T) ∧
        ∀p h t M.
            inst_avail_exp_list1 p (h::t) M ⇔
            inst_avail_exp2 p h (HD M) ∧ inst_avail_exp_list1 p t (TL M)
   
   [inst_avail_exp_list2_def]  Definition
      
      ⊢ (∀p M. inst_avail_exp_list2 p [] M ⇔ T) ∧
        ∀p h t M.
            inst_avail_exp_list2 p (h::t) M ⇔
            inst_avail_exp3 p h (HD M) ∧ inst_avail_exp_list2 p t (TL M)
   
   [inst_avail_exp_list_def]  Definition
      
      ⊢ (∀p n M. inst_avail_exp_list p [] n M ⇔ T) ∧
        ∀p h t n M.
            inst_avail_exp_list p (h::t) n M ⇔
            inst_avail_exp p h n (HD M) ∧ inst_avail_exp_list p t n (TL M)
   
   [inst_unavail_exp_def]  Definition
      
      ⊢ ∀p L m.
            inst_unavail_exp p L m ⇔
            ∀t.
                prob p (union_unavail_events p L (&t)) =
                FST m / (SND m + FST m) −
                FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)
   
   [inst_unavail_exp_list_def]  Definition
      
      ⊢ (∀p M. inst_unavail_exp_list p [] M ⇔ T) ∧
        ∀p h t M.
            inst_unavail_exp_list p (h::t) M ⇔
            inst_unavail_exp p h (HD M) ∧ inst_unavail_exp_list p t (TL M)
   
   [list_union_avail_event_list_def]  Definition
      
      ⊢ ∀L t.
            list_union_avail_event_list L t =
            MAP (λa. union_avail_event_list1 a t) L
   
   [rel_event1_def]  Definition
      
      ⊢ ∀p X t. rel_event1 p X t = PREIMAGE X {y | t < y} ∩ p_space p
   
   [reliability_def]  Definition
      
      ⊢ ∀p X t. reliability p X t = 1 − cdf p X t
   
   [steady_state_avail_def]  Definition
      
      ⊢ ∀m. steady_state_avail m = SND m / (SND m + FST m)
   
   [steady_state_avail_list_def]  Definition
      
      ⊢ (steady_state_avail_list [] = []) ∧
        ∀h t.
            steady_state_avail_list (h::t) =
            steady_state_avail h::steady_state_avail_list t
   
   [steady_state_avail_prod_def]  Definition
      
      ⊢ (steady_state_avail_prod [] = 1) ∧
        ∀h t.
            steady_state_avail_prod (h::t) =
            steady_state_avail h * steady_state_avail_prod t
   
   [steady_state_unavail_def]  Definition
      
      ⊢ ∀m. steady_state_unavail m = FST m / (SND m + FST m)
   
   [steady_state_unavail_list_def]  Definition
      
      ⊢ ∀M.
            steady_state_unavail_list M =
            MAP (λa. steady_state_unavail a) M
   
   [two_dim_inst_avail_exp_def]  Definition
      
      ⊢ (∀p M. two_dim_inst_avail_exp p [] M ⇔ T) ∧
        ∀p h t M.
            two_dim_inst_avail_exp p (h::t) M ⇔
            inst_avail_exp_list1 p h (HD M) ∧
            two_dim_inst_avail_exp p t (TL M)
   
   [two_dim_inst_unavail_exp_def]  Definition
      
      ⊢ (∀p M. two_dim_inst_unavail_exp p [] M ⇔ T) ∧
        ∀p h t M.
            two_dim_inst_unavail_exp p (h::t) M ⇔
            inst_unavail_exp_list p h (HD M) ∧
            two_dim_inst_unavail_exp p t (TL M)
   
   [two_dim_steady_state_avail_list_def]  Definition
      
      ⊢ (two_dim_steady_state_avail_list [] = []) ∧
        ∀h t.
            two_dim_steady_state_avail_list (h::t) =
            steady_state_avail_list h::two_dim_steady_state_avail_list t
   
   [two_dim_steady_state_avail_prod_def]  Definition
      
      ⊢ (two_dim_steady_state_avail_prod [] = 1) ∧
        ∀h t.
            two_dim_steady_state_avail_prod (h::t) =
            steady_state_avail_prod h * two_dim_steady_state_avail_prod t
   
   [unavail_event_def]  Definition
      
      ⊢ ∀p L n t.
            unavail_event p L n t =
            p_space p DIFF avail_event L n t ∩ p_space p
   
   [union_avail_event_list1_def]  Definition
      
      ⊢ ∀L t.
            union_avail_event_list1 L t =
            MAP (λa. union_avail_events1 a t) L
   
   [union_avail_event_list_def]  Definition
      
      ⊢ ∀L n t.
            union_avail_event_list L n t =
            MAP (λa. union_avail_events a n t) L
   
   [union_avail_events1_def]  Definition
      
      ⊢ ∀L t.
            union_avail_events1 L t =
            BIGUNION
              (IMAGE (λa. avail_event L a (Normal t)) (count (LENGTH L)))
   
   [union_avail_events_def]  Definition
      
      ⊢ ∀L n t.
            union_avail_events L n t =
            BIGUNION (IMAGE (λa. avail_event L a (Normal t)) (count n))
   
   [union_unavail_event_list_def]  Definition
      
      ⊢ ∀p L t.
            union_unavail_event_list p L t =
            MAP (λa. union_unavail_events p a t) L
   
   [union_unavail_events_def]  Definition
      
      ⊢ ∀p L t.
            union_unavail_events p L t =
            p_space p DIFF union_avail_events1 L t ∩ p_space p
   
   [AND_gate_unavail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t'.
                 ¬NULL (union_unavail_event_list p L (&t')) ∧
                 (∀z.
                      MEM z (union_unavail_event_list p L (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p (union_unavail_event_list p L (&t'))) ∧
            inst_unavail_exp_list p L M ⇒
            (lim (λt. prob p (AND_unavail_FT_gate p L (&t))) =
             list_prod (steady_state_unavail_list M))
   
   [AND_inst_avail_prod_tends_steady]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧ inst_unavail_exp_list p L M ⇒
            (λt.
                 list_prod
                   (list_prob p (union_unavail_event_list p L (&t)))) -->
            list_prod (steady_state_unavail_list M)
   
   [EXT_LE_LT]  Theorem
      
      ⊢ ∀x y. x ≤ y ∨ y < x ⇔ (x = y) ∨ x < y ∨ y < x
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [LET_ANTISYM]  Theorem
      
      ⊢ ∀x y. ¬(x < y ∧ y ≤ x)
   
   [NAND_steady_state_avail]  Theorem
      
      ⊢ ∀p L1 L2 M1 M2.
            prob_space p ∧ (∀z. MEM z (M1 ⧺ M2) ⇒ 0 < FST z ∧ 0 < SND z) ∧
            ((LENGTH L1 = LENGTH M1) ∧ (LENGTH L2 = LENGTH M2)) ∧
            (∀t'.
                 1 ≤
                 LENGTH
                   (union_unavail_event_list p L1 (&t') ⧺
                    union_unavail_event_list p L2 (&t')) ∧
                 (∀z.
                      MEM z
                        (union_unavail_event_list p L1 (&t') ⧺
                         union_unavail_event_list p L2 (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p
                   (union_unavail_event_list p L1 (&t') ⧺
                    union_unavail_event_list p L2 (&t'))) ∧
            inst_avail_exp_list2 p L1 M1 ∧ inst_unavail_exp_list p L2 M2 ⇒
            (lim (λt. prob p (NAND_unavail_FT_gate p L1 L2 (&t))) =
             list_prod (steady_state_avail_list M1) *
             list_prod (steady_state_unavail_list M2))
   
   [OR_steady_state_unavail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t'.
                 ¬NULL (union_unavail_event_list p L (&t')) ∧
                 (∀z.
                      MEM z (union_unavail_event_list p L (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p (union_unavail_event_list p L (&t'))) ∧
            inst_unavail_exp_list p L M ⇒
            (lim (λt. prob p (OR_unavail_FT_gate p L (&t))) =
             1 − list_prod (one_minus_list (steady_state_unavail_list M)))
   
   [PERM_refl]  Theorem
      
      ⊢ ∀L. PERM L L
   
   [XOR_steady_unavail]  Theorem
      
      ⊢ ∀p X1 X2 m1 m2 t.
            prob_space p ∧
            (∀t'.
                 union_unavail_events p X1 (&t') ∈ events p ∧
                 union_unavail_events p X2 (&t') ∈ events p ∧
                 indep p (union_unavail_events p X1 (&t'))
                   (union_unavail_events p X2 (&t'))) ∧
            (0 < FST m1 ∧ 0 < SND m1) ∧ (0 < FST m2 ∧ 0 < SND m2) ∧
            inst_unavail_exp p X1 m1 ∧ inst_unavail_exp p X2 m2 ⇒
            (lim
               (λt.
                    prob p
                      (XOR_FT_gate p
                         (atomic (union_unavail_events p X1 (&t)))
                         (atomic (union_unavail_events p X2 (&t))))) =
             steady_state_unavail m1 * (1 − steady_state_unavail m2) +
             steady_state_unavail m2 * (1 − steady_state_unavail m1))
   
   [avail_ge_rel]  Theorem
      
      ⊢ ∀p t L.
            0 ≤ t ∧ ¬NULL L ∧ (∀n. avail_event L n t ∈ events p) ∧
            prob_space p ⇒
            reliability p (FST (HD L)) t ≤ expec_avail p L (LENGTH L) t
   
   [avail_ge_rel1]  Theorem
      
      ⊢ ∀p t L.
            0 ≤ Normal t ∧ ¬NULL L ∧
            (∀a b.
                 a ≠ b ⇒
                 DISJOINT (avail_event L a (Normal t))
                   (avail_event L b (Normal t))) ∧
            (∀n. avail_event L n (Normal t) ∈ events p) ∧ prob_space p ⇒
            reliability p (FST (HD L)) (Normal t) ≤
            prob p (union_avail_events L (LENGTH L) t)
   
   [compl_fail_event_eq_rel_event1]  Theorem
      
      ⊢ ∀X t p.
            p_space p DIFF PREIMAGE X {y | y ≤ t} ∩ p_space p =
            rel_event1 p X t
   
   [compl_rel_event_eq_fail_event1]  Theorem
      
      ⊢ ∀p t s.
            prob_space p ⇒
            (p_space p DIFF PREIMAGE s {y | t < y} ∩ p_space p =
             PREIMAGE s {y | y ≤ t} ∩ p_space p)
   
   [compl_steady_state_avail_equi]  Theorem
      
      ⊢ ∀M.
            compl_steady_state_avail M =
            list_prod (one_minus_list (steady_state_avail_list M))
   
   [in_events_normal_events]  Theorem
      
      ⊢ ∀p A t.
            prob_space p ∧ p_space p DIFF A ∩ p_space p ∈ events p ⇒
            A ∩ p_space p ∈ events p
   
   [inst_XOR_tends_steadty]  Theorem
      
      ⊢ ∀p X1 m1.
            inst_unavail_exp p X1 m1 ∧ 0 < FST m1 ∧ 0 < SND m1 ⇒
            (λt. prob p (union_unavail_events p X1 (&t))) -->
            steady_state_unavail m1
   
   [lim_inst_OR_tend_steady]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t' z.
                 MEM z (union_unavail_event_list p L (&t')) ⇒ z ∈ events p) ∧
            inst_avail_exp_list2 p L M ⇒
            (λt.
                 list_prod
                   (list_prob p
                      (compl_list p (union_unavail_event_list p L (&t))))) -->
            list_prod (steady_state_avail_list M)
   
   [lim_inst_parall_series_tend_steady]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z (FLAT M) ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀n. n < LENGTH L ⇒ (LENGTH (EL n L) = LENGTH (EL n M))) ∧
            two_dim_inst_avail_exp p L M ⇒
            (λt.
                 (list_prod ∘ one_minus_list of
                  (λa. list_prod (list_prob p a)))
                   (list_union_avail_event_list L (&t))) -->
            list_prod
              (one_minus_list (MAP (λa. steady_state_avail_prod a) M))
   
   [lim_inst_parall_tend_steady]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧ inst_avail_exp_list1 p L M ⇒
            (λt.
                 list_prod
                   (one_minus_list
                      (list_prob p (union_avail_event_list1 L (&t))))) -->
            compl_steady_state_avail M
   
   [lim_inst_series_parall_tend_steady]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z (FLAT M) ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀n. n < LENGTH L ⇒ (LENGTH (EL n L) = LENGTH (EL n M))) ∧
            two_dim_inst_avail_exp p L M ⇒
            (λt.
                 (list_prod of
                  (λa. 1 − list_prod (one_minus_list (list_prob p a))))
                   (list_union_avail_event_list L (&t))) -->
            list_prod
              (one_minus_list (MAP (λa. compl_steady_state_avail a) M))
   
   [neg_exp_tend0_new]  Theorem
      
      ⊢ ∀t c. 0 < c ⇒ (λt. exp (&t * -c)) --> 0
   
   [not_null_leng]  Theorem
      
      ⊢ ∀L1. ¬NULL L1 ⇒ 1 ≤ LENGTH L1
   
   [parallel_rbd_avail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t'.
                 ¬NULL (union_avail_event_list1 L (&t')) ∧
                 (∀z.
                      MEM z (union_avail_event_list1 L (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p (union_avail_event_list1 L (&t'))) ∧
            inst_avail_exp_list1 p L M ⇒
            (lim
               (λt.
                    prob p
                      (rbd_struct p
                         (parallel
                            (rbd_list (union_avail_event_list1 L (&t)))))) =
             1 − list_prod (one_minus_list (steady_state_avail_list M)))
   
   [series_expec_tends_prod_avail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧ inst_avail_exp_list1 p L M ⇒
            (λt. list_prod (list_prob p (union_avail_event_list1 L (&t)))) -->
            steady_state_avail_prod M
   
   [series_rbd_avail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t'.
                 ¬NULL (union_avail_event_list1 L (&t')) ∧
                 (∀z.
                      MEM z (union_avail_event_list1 L (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p (union_avail_event_list1 L (&t'))) ∧
            inst_avail_exp_list1 p L M ⇒
            (lim
               (λt.
                    prob p
                      (rbd_struct p
                         (series
                            (rbd_list (union_avail_event_list1 L (&t)))))) =
             steady_state_avail_prod M)
   
   [steady_avail_temp]  Theorem
      
      ⊢ ∀a b. 0 < a ∧ 0 < b ⇒ 0 < a + b
   
   [steady_state_NOR_unavail_FT_gate]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z M ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀t'.
                 ¬NULL (union_unavail_event_list p L (&t')) ∧
                 (∀z.
                      MEM z (union_unavail_event_list p L (&t')) ⇒
                      z ∈ events p) ∧
                 mutual_indep p (union_unavail_event_list p L (&t'))) ∧
            inst_unavail_exp_list p L M ⇒
            (lim (λt. prob p (NOR_unavail_FT_gate p L (&t))) =
             list_prod (one_minus_list (steady_state_unavail_list M)))
   
   [steady_state_avail]  Theorem
      
      ⊢ ∀p L n m t.
            (0 < FST m ∧ 0 < SND m) ∧ inst_avail_exp p L n m ⇒
            (lim (λt. expec_avail p L n (Normal (&t))) =
             SND m / (SND m + FST m))
   
   [steady_state_avail1]  Theorem
      
      ⊢ ∀p L n m.
            prob_space p ∧
            (∀t.
                 (∀a b.
                      a ≠ b ⇒
                      DISJOINT (avail_event L a (Normal t))
                        (avail_event L b (Normal t))) ∧
                 ∀n. avail_event L n (Normal t) ∈ events p) ∧
            (0 < FST m ∧ 0 < SND m) ∧ inst_avail_exp p L n m ⇒
            (lim (λt. prob p (union_avail_events L n (&t))) =
             SND m / (SND m + FST m))
   
   [steady_state_parallel_series_ABD]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z (FLAT M) ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀n. n < LENGTH L ⇒ (LENGTH (EL n L) = LENGTH (EL n M))) ∧
            (∀t'.
                 (∀z. MEM z (list_union_avail_event_list L (&t')) ⇒ ¬NULL z) ∧
                 (∀z.
                      MEM z (FLAT (list_union_avail_event_list L (&t'))) ⇒
                      z ∈ events p) ∧
                 mutual_indep p
                   (FLAT (list_union_avail_event_list L (&t')))) ∧
            two_dim_inst_avail_exp p L M ⇒
            (lim
               (λt.
                    prob p
                      (rbd_struct p
                         ((parallel of (λa. series (rbd_list a)))
                            (list_union_avail_event_list L (&t))))) =
             1 −
             list_prod
               (one_minus_list (MAP (λa. steady_state_avail_prod a) M)))
   
   [steady_state_series_parallel_avail]  Theorem
      
      ⊢ ∀p L M.
            prob_space p ∧ (∀z. MEM z (FLAT M) ⇒ 0 < FST z ∧ 0 < SND z) ∧
            (LENGTH L = LENGTH M) ∧
            (∀n. n < LENGTH L ⇒ (LENGTH (EL n L) = LENGTH (EL n M))) ∧
            (∀t'.
                 (∀z. MEM z (list_union_avail_event_list L (&t')) ⇒ ¬NULL z) ∧
                 (∀z.
                      MEM z (FLAT (list_union_avail_event_list L (&t'))) ⇒
                      z ∈ events p) ∧
                 mutual_indep p
                   (FLAT (list_union_avail_event_list L (&t')))) ∧
            two_dim_inst_avail_exp p L M ⇒
            (lim
               (λt.
                    prob p
                      (rbd_struct p
                         ((series of (λa. parallel (rbd_list a)))
                            (list_union_avail_event_list L (&t))))) =
             list_prod
               (one_minus_list (MAP (λa. compl_steady_state_avail a) M)))
   
   
*)
end
