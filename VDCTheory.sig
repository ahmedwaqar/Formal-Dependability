signature VDCTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val CDF_def : thm
    val Reliability_def : thm
    val UNIONL_def : thm
    val cloud_server_fail_rate_list_def : thm
    val cloud_server_rv_list_def : thm
    val exp_dist_def : thm
    val exp_dist_list_def : thm
    val exp_func_list_def : thm
    val fail_event_def : thm
    val four_dim_exp_dist_list_def : thm
    val four_dim_rel_event_list_def : thm
    val gen_list_def : thm
    val gen_rv_list_def : thm
    val log_base_def : thm
    val rel_event_def : thm
    val rel_event_list_def : thm
    val rel_virt_cloud_server_def : thm
    val three_dim_exp_dist_list_def : thm
    val three_dim_rel_event_list_def : thm
    val two_dim_exp_dist_list_def : thm
    val two_dim_rel_event_list_def : thm
  
  (*  Theorems  *)
    val IN_UNIONL : thm
    val VDC_case_study_thm : thm
    val bound_log_inequal : thm
    val bound_mult_ratr : thm
    val cloud_server_rv_list_not_null : thm
    val cloud_server_rv_list_not_null1 : thm
    val cloud_server_rv_list_not_null2 : thm
    val cloud_server_rv_list_not_null3 : thm
    val comp_rel_event_eq_fail_event : thm
    val compl_fail_event_eq_rel_event : thm
    val compl_rel_event_eq_fail_event : thm
    val compl_rel_pow_n : thm
    val extreal_not_le : thm
    val gen_list_def_compute : thm
    val gen_list_suc : thm
    val in_events_cloud_server_rv_list : thm
    val in_events_cloud_server_rv_list1 : thm
    val len_cloud_server_fail_rate_eq_rv_list : thm
    val len_cloud_server_fail_rate_eq_rv_list1 : thm
    val len_cloud_server_fail_rate_eq_rv_list2 : thm
    val len_cloud_server_fail_rate_eq_rv_list3 : thm
    val len_cloud_server_fail_rate_eq_rv_list4 : thm
    val len_cloud_server_fail_rate_eq_rv_list5 : thm
    val len_cloud_server_fail_rate_eq_rv_list6 : thm
    val len_cloud_server_fail_rate_eq_rv_list7 : thm
    val mem_flat_fun_eq_mem_flat_null_list : thm
    val mem_flat_fun_eq_mem_flat_null_list1 : thm
    val mem_flat_fun_eq_mem_flat_null_list2 : thm
    val mem_flat_fun_eq_mem_flat_null_list3 : thm
    val mem_flat_map_not_null : thm
    val mem_flat_map_not_null1 : thm
    val mem_flat_map_not_null2 : thm
    val mem_flat_map_not_null3 : thm
    val nested_series_parallel_exp_dist : thm
    val nested_series_parallel_rbd_alt_form : thm
    val nlen_gen_list_eq_n : thm
    val nlen_gen_list_eq_n1 : thm
    val not_null_map : thm
    val parallel_series_exp_fail_rate : thm
    val parallel_series_parallel_prod_rel_exp_dist : thm
    val parallel_series_parallel_rbd_alt_form : thm
    val rbd_virtual_cloud_server_alt_form : thm
    val rel_parallel_series_exp_fail_rate : thm
    val rel_prod_series_rbd_exp_dist : thm
    val rel_prod_tend_0 : thm
    val rel_series_parallel_RBD_exp_dist_fail_rate : thm
    val rel_series_parallel_RBD_exp_dist_fail_rate_lemma1 : thm
    val rel_virtual_cloud_server : thm
    val seq_rel_prod_tend_0 : thm
    val virt_config_bounds : thm
  
  val VDC_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [RBD] Parent theory of "VDC"
   
   [CDF_def]  Definition
      
      ⊢ ∀p X t. CDF p X t = distribution p X {y | y ≤ Normal t}
   
   [Reliability_def]  Definition
      
      ⊢ ∀p X t. Reliability p X t = 1 − CDF p X t
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [cloud_server_fail_rate_list_def]  Definition
      
      ⊢ ∀L m n.
            cloud_server_fail_rate_list L m n = gen_list (gen_list L m) n
   
   [cloud_server_rv_list_def]  Definition
      
      ⊢ ∀L m n. cloud_server_rv_list L m n = gen_list (gen_list L m) n
   
   [exp_dist_def]  Definition
      
      ⊢ ∀p X l.
            exp_dist p X l ⇔
            ∀t. CDF p X t = if 0 ≤ t then 1 − exp (-l * t) else 0
   
   [exp_dist_list_def]  Definition
      
      ⊢ (∀p L. exp_dist_list p [] L ⇔ T) ∧
        ∀p h t L.
            exp_dist_list p (h::t) L ⇔
            exp_dist p h (HD L) ∧ exp_dist_list p t (TL L)
   
   [exp_func_list_def]  Definition
      
      ⊢ ∀C t. exp_func_list C t = MAP (λa. exp (-(a * t))) C
   
   [fail_event_def]  Definition
      
      ⊢ ∀p X t.
            fail_event p X t = PREIMAGE X {y | y ≤ Normal t} ∩ p_space p
   
   [four_dim_exp_dist_list_def]  Definition
      
      ⊢ (∀p L. four_dim_exp_dist_list p [] L ⇔ T) ∧
        ∀p h t L.
            four_dim_exp_dist_list p (h::t) L ⇔
            three_dim_exp_dist_list p h (HD L) ∧
            four_dim_exp_dist_list p t (TL L)
   
   [four_dim_rel_event_list_def]  Definition
      
      ⊢ ∀p L t.
            four_dim_rel_event_list p L t =
            MAP (λa. three_dim_rel_event_list p a t) L
   
   [gen_list_def]  Definition
      
      ⊢ (∀L. gen_list L 0 = []) ∧
        ∀L n. gen_list L (SUC n) = SNOC L (gen_list L n)
   
   [gen_rv_list_def]  Definition
      
      ⊢ ∀X n. gen_rv_list X n = gen_list X n
   
   [log_base_def]  Definition
      
      ⊢ ∀b x. log_base b x = ln x / ln b
   
   [rel_event_def]  Definition
      
      ⊢ ∀p X t. rel_event p X t = PREIMAGE X {y | Normal t < y} ∩ p_space p
   
   [rel_event_list_def]  Definition
      
      ⊢ ∀p L t.
            rel_event_list p L t =
            MAP (λa. PREIMAGE a {y | Normal t < y} ∩ p_space p) L
   
   [rel_virt_cloud_server_def]  Definition
      
      ⊢ ∀p L t.
            rel_virt_cloud_server p L t =
            prob p
              (rbd_struct p
                 ((series of
                   (λa. parallel (rbd_list (rel_event_list p a t)))) L))
   
   [three_dim_exp_dist_list_def]  Definition
      
      ⊢ (∀p L. three_dim_exp_dist_list p [] L ⇔ T) ∧
        ∀p h t L.
            three_dim_exp_dist_list p (h::t) L ⇔
            two_dim_exp_dist_list p h (HD L) ∧
            three_dim_exp_dist_list p t (TL L)
   
   [three_dim_rel_event_list_def]  Definition
      
      ⊢ ∀p L t.
            three_dim_rel_event_list p L t =
            MAP (λa. two_dim_rel_event_list p a t) L
   
   [two_dim_exp_dist_list_def]  Definition
      
      ⊢ (∀p L. two_dim_exp_dist_list p [] L ⇔ T) ∧
        ∀p h t L.
            two_dim_exp_dist_list p (h::t) L ⇔
            exp_dist_list p h (HD L) ∧ two_dim_exp_dist_list p t (TL L)
   
   [two_dim_rel_event_list_def]  Definition
      
      ⊢ ∀p L t.
            two_dim_rel_event_list p L t = MAP (λa. rel_event_list p a t) L
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [VDC_case_study_thm]  Theorem
      
      ⊢ ∀X_VM X_VMM X_HW X_C C_VM C_VMM C_HW C m n p t.
            0 ≤ t ∧ prob_space p ∧
            ¬NULL (cloud_server_rv_list [X_VM] m n) ∧
            ¬NULL (cloud_server_fail_rate_list [C_VM] m n) ∧
            (∀z.
                 MEM z (FLAT (FLAT (cloud_server_rv_list [X_VM] m n))) ⇒
                 ¬NULL z) ∧ (LENGTH C = LENGTH X_C) ∧ ¬NULL C_VM ∧
            ¬NULL X_VM ∧ (LENGTH X_VM = LENGTH C_VM) ∧
            exp_dist_list p X_C C ∧ ¬NULL (rel_event_list p X_C t) ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (FLAT
                         (FLAT
                            (four_dim_rel_event_list p
                               (cloud_server_rv_list [X_VM] m n) t)))) ⇒
                 x' ∈ events p) ∧ rel_event p X_VMM t ∈ events p ∧
            rel_event p X_HW t ∈ events p ∧
            (∀z'. MEM z' (rel_event_list p X_C t) ⇒ z' ∈ events p) ∧
            (LENGTH X_VM = LENGTH C_VM) ∧
            four_dim_exp_dist_list p
              (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n)
              (cloud_server_fail_rate_list [C_VMM::C_HW::C_VM] m n) ∧
            mutual_indep p
              (rel_event_list p X_C t ⧺
               FLAT
                 (FLAT
                    (FLAT
                       (four_dim_rel_event_list p
                          (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n) t)))) ⇒
            (prob p
               (rbd_struct p (series (rbd_list (rel_event_list p X_C t))) ∩
                rbd_struct p
                  ((series of parallel of series of
                    (λa. parallel (rbd_list (rel_event_list p a t))))
                     (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n))) =
             list_prod (exp_func_list C t) *
             (list_prod of (λa. 1 − list_prod (one_minus_list a)) of
              (λa. list_prod a) of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t))))
               (cloud_server_fail_rate_list [C_VMM::C_HW::C_VM] m n))
   
   [bound_log_inequal]  Theorem
      
      ⊢ ∀a b c e n.
            0 ≤ e ∧ e < 1 ∧ a < b ∧ 0 < n ∧ 0 < b ∧
            (a = e * b * (1 − (1 − c) pow n)) ∧ 0 < c ∧ c < 1 ⇒
            &n > log_base 10 (1 − a / b) / log_base 10 (1 − c)
   
   [bound_mult_ratr]  Theorem
      
      ⊢ ∀a b c. 0 < c ⇒ (a * (b / c) = a * b / c)
   
   [cloud_server_rv_list_not_null]  Theorem
      
      ⊢ ∀p t a b c n m.
            (∀z.
                 MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ⇒
                 ¬NULL z) ⇒
            ∀z.
                MEM z
                  (FLAT
                     (FLAT
                        (four_dim_rel_event_list p
                           (cloud_server_rv_list [a::b::c] m n) t))) ⇒
                ¬NULL z
   
   [cloud_server_rv_list_not_null1]  Theorem
      
      ⊢ ∀p t a b c n m.
            (∀z.
                 MEM z (FLAT (gen_list [c] m)) ∨
                 MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ⇒
                 ¬NULL z) ⇒
            ∀z.
                MEM z
                  (FLAT
                     (three_dim_rel_event_list p (gen_list [a::b::c] m) t)) ⇒
                ¬NULL z
   
   [cloud_server_rv_list_not_null2]  Theorem
      
      ⊢ ∀a b c n m.
            (∀z.
                 MEM z (FLAT (gen_list [c] m)) ∨
                 MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ⇒
                 ¬NULL z) ⇒
            ∀z. MEM z (FLAT (gen_list [a::b::c] m)) ⇒ ¬NULL z
   
   [cloud_server_rv_list_not_null3]  Theorem
      
      ⊢ ∀a b c n m.
            (∀z.
                 MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ⇒
                 ¬NULL z) ⇒
            ∀z.
                MEM z (FLAT (FLAT (cloud_server_rv_list [a::b::c] m n))) ⇒
                ¬NULL z
   
   [comp_rel_event_eq_fail_event]  Theorem
      
      ⊢ ∀X t p. p_space p DIFF rel_event p X t = fail_event p X t
   
   [compl_fail_event_eq_rel_event]  Theorem
      
      ⊢ ∀X t p. p_space p DIFF fail_event p X t = rel_event p X t
   
   [compl_rel_event_eq_fail_event]  Theorem
      
      ⊢ ∀p t s.
            prob_space p ⇒
            (p_space p DIFF PREIMAGE s {y | Normal t < y} ∩ p_space p =
             PREIMAGE s {y | y ≤ Normal t} ∩ p_space p)
   
   [compl_rel_pow_n]  Theorem
      
      ⊢ ∀X p t n.
            prob_space p ∧ rel_event p X t ∈ events p ⇒
            (list_prod
               (one_minus_list
                  (list_prob p (rel_event_list p (gen_rv_list X n) t))) =
             (1 − Reliability p X t) pow n)
   
   [extreal_not_le]  Theorem
      
      ⊢ ∀x y. ¬(x < y) ⇔ ¬ ¬(y ≤ x)
   
   [gen_list_def_compute]  Theorem
      
      ⊢ (∀L. gen_list L 0 = []) ∧
        (∀L n.
             gen_list L (NUMERAL (BIT1 n)) =
             SNOC L (gen_list L (NUMERAL (BIT1 n) − 1))) ∧
        ∀L n.
            gen_list L (NUMERAL (BIT2 n)) =
            SNOC L (gen_list L (NUMERAL (BIT1 n)))
   
   [gen_list_suc]  Theorem
      
      ⊢ ∀L n. gen_list L (SUC n) = L::gen_list L n
   
   [in_events_cloud_server_rv_list]  Theorem
      
      ⊢ ∀p t a b c n m.
            rel_event p a t ∈ events p ∧ rel_event p b t ∈ events p ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (FLAT
                         (FLAT
                            (four_dim_rel_event_list p
                               (cloud_server_rv_list [c] m n) t)))) ⇒
                 x' ∈ events p) ⇒
            ∀x'.
                MEM x'
                  (FLAT
                     (FLAT
                        (FLAT
                           (four_dim_rel_event_list p
                              (cloud_server_rv_list [a::b::c] m n) t)))) ⇒
                x' ∈ events p
   
   [in_events_cloud_server_rv_list1]  Theorem
      
      ⊢ ∀p t a b c n m.
            rel_event p a t ∈ events p ∧ rel_event p b t ∈ events p ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (FLAT (three_dim_rel_event_list p (gen_list [c] m) t))) ∨
                 MEM x'
                   (FLAT
                      (FLAT
                         (FLAT
                            (MAP (λa. three_dim_rel_event_list p a t)
                               (cloud_server_rv_list [c] m n))))) ⇒
                 x' ∈ events p) ⇒
            ∀x'.
                MEM x'
                  (FLAT
                     (FLAT
                        (three_dim_rel_event_list p (gen_list [a::b::c] m)
                           t))) ⇒
                x' ∈ events p
   
   [len_cloud_server_fail_rate_eq_rv_list]  Theorem
      
      ⊢ ∀a b c d e f n m.
            LENGTH (cloud_server_fail_rate_list [a::b::c] m n) =
            LENGTH (cloud_server_rv_list [d::e::f] m n)
   
   [len_cloud_server_fail_rate_eq_rv_list1]  Theorem
      
      ⊢ ∀a b c d e f m.
            (LENGTH [a::b::c] = LENGTH [d::e::f]) ⇒
            (LENGTH (gen_list [a::b::c] m) = LENGTH (gen_list [d::e::f] m))
   
   [len_cloud_server_fail_rate_eq_rv_list2]  Theorem
      
      ⊢ ∀a b c d e f n m n'.
            (LENGTH [a::b::c] = LENGTH [d::e::f]) ∧
            n' < LENGTH (cloud_server_rv_list [a::b::c] m n) ∧
            n' < LENGTH (cloud_server_fail_rate_list [d::e::f] m n) ∧
            ¬NULL c ∧ ¬NULL f ⇒
            (LENGTH (EL n' (cloud_server_rv_list [a::b::c] m n)) =
             LENGTH (EL n' (cloud_server_fail_rate_list [d::e::f] m n)))
   
   [len_cloud_server_fail_rate_eq_rv_list3]  Theorem
      
      ⊢ ∀a b c d e f m n.
            (LENGTH c = LENGTH f) ∧ ¬NULL f ∧ ¬NULL c ∧
            n < LENGTH (gen_list [a::b::c] m) ∧
            n < LENGTH (gen_list [d::e::f] m) ⇒
            (LENGTH (EL n (gen_list [a::b::c] m)) =
             LENGTH (EL n (gen_list [d::e::f] m)))
   
   [len_cloud_server_fail_rate_eq_rv_list4]  Theorem
      
      ⊢ ∀a b c d e f l m n n'.
            (LENGTH c = LENGTH f) ∧
            n' < LENGTH (cloud_server_rv_list [a::b::c] m l) ∧
            n' < LENGTH (cloud_server_fail_rate_list [d::e::f] m l) ∧
            n < LENGTH (EL n' (cloud_server_rv_list [a::b::c] m l)) ∧
            n < LENGTH (EL n' (cloud_server_fail_rate_list [d::e::f] m l)) ∧
            ¬NULL f ∧ ¬NULL c ∧
            ¬NULL (cloud_server_fail_rate_list [f] m l) ∧
            ¬NULL (cloud_server_rv_list [c] m l) ⇒
            (LENGTH (EL n (EL n' (cloud_server_rv_list [a::b::c] m l))) =
             LENGTH
               (EL n (EL n' (cloud_server_fail_rate_list [d::e::f] m l))))
   
   [len_cloud_server_fail_rate_eq_rv_list5]  Theorem
      
      ⊢ ∀a b c d e f n.
            (LENGTH c = LENGTH f) ∧ ¬NULL f ∧ ¬NULL c ∧
            n < LENGTH [a::b::c] ∧ n < LENGTH [d::e::f] ⇒
            (LENGTH (EL n [a::b::c]) = LENGTH (EL n [d::e::f]))
   
   [len_cloud_server_fail_rate_eq_rv_list6]  Theorem
      
      ⊢ ∀a b c d e f m n n'.
            (LENGTH c = LENGTH f) ∧ ¬NULL f ∧ ¬NULL c ∧
            n' < LENGTH (gen_list [a::b::c] m) ∧
            n' < LENGTH (gen_list [d::e::f] m) ∧
            n < LENGTH (EL n' (gen_list [a::b::c] m)) ∧
            n < LENGTH (EL n' (gen_list [d::e::f] m)) ⇒
            (LENGTH (EL n (EL n' (gen_list [a::b::c] m))) =
             LENGTH (EL n (EL n' (gen_list [d::e::f] m))))
   
   [len_cloud_server_fail_rate_eq_rv_list7]  Theorem
      
      ⊢ ∀a b c d e f l m n n' n''.
            ¬NULL f ∧ ¬NULL c ∧ (LENGTH c = LENGTH f) ∧
            n'' < LENGTH (cloud_server_rv_list [a::b::c] m l) ∧
            n'' < LENGTH (cloud_server_fail_rate_list [d::e::f] m l) ∧
            n' < LENGTH (EL n'' (cloud_server_rv_list [a::b::c] m l)) ∧
            n' <
            LENGTH (EL n'' (cloud_server_fail_rate_list [d::e::f] m l)) ∧
            n <
            LENGTH (EL n' (EL n'' (cloud_server_rv_list [a::b::c] m l))) ∧
            n <
            LENGTH
              (EL n' (EL n'' (cloud_server_fail_rate_list [d::e::f] m l))) ⇒
            (LENGTH
               (EL n (EL n' (EL n'' (cloud_server_rv_list [a::b::c] m l)))) =
             LENGTH
               (EL n
                  (EL n'
                     (EL n'' (cloud_server_fail_rate_list [d::e::f] m l)))))
   
   [mem_flat_fun_eq_mem_flat_null_list]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z (FLAT (FLAT L)) ⇒ ¬NULL z) ⇒
            ∀z.
                MEM z (FLAT (FLAT (four_dim_rel_event_list p L t))) ⇒
                ¬NULL z
   
   [mem_flat_fun_eq_mem_flat_null_list1]  Theorem
      
      ⊢ ∀p t L. ¬NULL L ⇒ ¬NULL (rel_event_list p L t)
   
   [mem_flat_fun_eq_mem_flat_null_list2]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z (FLAT L) ⇒ ¬NULL z) ⇒
            ∀z.
                MEM z
                  (FLAT
                     (MAP
                        (λa.
                             MAP
                               (λa.
                                    MAP
                                      (λa.
                                           PREIMAGE a {y | Normal t < y} ∩
                                           p_space p) a) a) L)) ⇒
                ¬NULL z
   
   [mem_flat_fun_eq_mem_flat_null_list3]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z L ⇒ ¬NULL z) ⇒
            ∀z. MEM z (two_dim_rel_event_list p L t) ⇒ ¬NULL z
   
   [mem_flat_map_not_null]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z (FLAT (FLAT L)) ⇒ ¬NULL z) ⇒
            ∀z.
                MEM z
                  (FLAT (FLAT (MAP (λa. three_dim_rel_event_list p a t) L))) ⇒
                ¬NULL z
   
   [mem_flat_map_not_null1]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z (FLAT L) ⇒ ¬NULL z) ⇒
            ∀z.
                MEM z (FLAT (MAP (λa. two_dim_rel_event_list p a t) L)) ⇒
                ¬NULL z
   
   [mem_flat_map_not_null2]  Theorem
      
      ⊢ ∀f L.
            (∀y. ¬NULL (f y)) ∧ (∀z. MEM z L ⇒ ¬NULL z) ⇒
            ∀z. MEM z (MAP f L) ⇒ ¬NULL z
   
   [mem_flat_map_not_null3]  Theorem
      
      ⊢ ∀p t L.
            (∀z. MEM z L ⇒ ¬NULL z) ⇒
            ∀z. MEM z (MAP (λa. rel_event_list p a t) L) ⇒ ¬NULL z
   
   [nested_series_parallel_exp_dist]  Theorem
      
      ⊢ ∀p t L C.
            0 ≤ t ∧ prob_space p ∧ (∀z. MEM z (FLAT (FLAT L)) ⇒ ¬NULL z) ∧
            (∀x'.
                 MEM x'
                   (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t)))) ⇒
                 x' ∈ events p) ∧ (LENGTH C = LENGTH L) ∧
            (∀n.
                 n < LENGTH L ∧ n < LENGTH C ⇒
                 (LENGTH (EL n L) = LENGTH (EL n C))) ∧
            (∀n' n.
                 n' < LENGTH L ∧ n' < LENGTH C ∧ n < LENGTH (EL n' L) ∧
                 n < LENGTH (EL n' C) ⇒
                 (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C)))) ∧
            (∀n'' n' n.
                 n'' < LENGTH L ∧ n'' < LENGTH C ∧ n' < LENGTH (EL n'' L) ∧
                 n' < LENGTH (EL n'' C) ∧ n < LENGTH (EL n' (EL n'' L)) ∧
                 n < LENGTH (EL n' (EL n'' C)) ⇒
                 (LENGTH (EL n (EL n' (EL n'' L))) =
                  LENGTH (EL n (EL n' (EL n'' C))))) ∧
            four_dim_exp_dist_list p L C ∧
            mutual_indep p
              (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t)))) ⇒
            (prob p
               (rbd_struct p
                  ((series of parallel of series of
                    (λa. parallel (rbd_list (rel_event_list p a t)))) L)) =
             (list_prod of (λa. 1 − list_prod (one_minus_list a)) of
              (λa. list_prod a) of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
   
   [nested_series_parallel_rbd_alt_form]  Theorem
      
      ⊢ ∀p t L.
            prob_space p ⇒
            (rbd_struct p
               ((series of parallel of series of
                 (λa. parallel (rbd_list a)))
                  (four_dim_rel_event_list p L t)) =
             rbd_struct p
               ((series of parallel of series of
                 (λa. parallel (rbd_list (rel_event_list p a t)))) L))
   
   [nlen_gen_list_eq_n]  Theorem
      
      ⊢ ∀L n t p. LENGTH (rel_event_list p (gen_rv_list L n) t) = n
   
   [nlen_gen_list_eq_n1]  Theorem
      
      ⊢ ∀L n. LENGTH (gen_list L n) = n
   
   [not_null_map]  Theorem
      
      ⊢ ∀f l. ¬NULL l ⇒ ¬NULL (MAP f l)
   
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
   
   [parallel_series_parallel_prod_rel_exp_dist]  Theorem
      
      ⊢ ∀p t L C.
            0 ≤ t ∧ prob_space p ∧ (LENGTH C = LENGTH L) ∧
            mutual_indep p (FLAT (FLAT (three_dim_rel_event_list p L t))) ∧
            (∀x'.
                 MEM x' (FLAT (FLAT (three_dim_rel_event_list p L t))) ⇒
                 x' ∈ events p) ∧ (∀z. MEM z (FLAT L) ⇒ ¬NULL z) ∧
            three_dim_exp_dist_list p L C ∧
            (∀n' n.
                 n' < LENGTH L ∧ n' < LENGTH C ∧ n < LENGTH (EL n' L) ∧
                 n < LENGTH (EL n' C) ⇒
                 (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C)))) ∧
            (∀n.
                 n < LENGTH L ∧ n < LENGTH C ⇒
                 (LENGTH (EL n L) = LENGTH (EL n C))) ⇒
            (1 −
             list_prod
               (one_minus_list
                  (MAP
                     ((λa. list_prod a) of
                      (λa. 1 − list_prod (one_minus_list (list_prob p a))))
                     (three_dim_rel_event_list p L t))) =
             1 −
             list_prod
               (one_minus_list
                  (MAP
                     ((λa. list_prod a) of
                      (λa.
                           1 −
                           list_prod (one_minus_list (exp_func_list a t))))
                     C)))
   
   [parallel_series_parallel_rbd_alt_form]  Theorem
      
      ⊢ ∀p t L.
            prob_space p ⇒
            (rbd_struct p
               ((parallel of series of (λa. parallel (rbd_list a)))
                  (three_dim_rel_event_list p L t)) =
             rbd_struct p
               ((parallel of series of
                 (λa. parallel (rbd_list (rel_event_list p a t)))) L))
   
   [rbd_virtual_cloud_server_alt_form]  Theorem
      
      ⊢ ∀p t L.
            prob_space p ⇒
            (rbd_struct p
               ((series of (λa. parallel (rbd_list (rel_event_list p a t))))
                  L) =
             rbd_struct p
               ((series of (λa. parallel (rbd_list a)))
                  (two_dim_rel_event_list p L t)))
   
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
   
   [rel_prod_series_rbd_exp_dist]  Theorem
      
      ⊢ ∀p t L C.
            0 ≤ t ∧ prob_space p ∧ exp_dist_list p L C ∧
            (LENGTH C = LENGTH L) ∧
            (∀x. MEM x (rel_event_list p L t) ⇒ x ∈ events p) ⇒
            (list_prod (list_prob p (rel_event_list p L t)) =
             list_prod (exp_func_list C t))
   
   [rel_prod_tend_0]  Theorem
      
      ⊢ ∀n p X t.
            0 ≤ t ∧ possibly p (rel_event p X t) ∧ prob_space p ⇒
            (lim
               (λn.
                    list_prod
                      (one_minus_list
                         (list_prob p
                            (rel_event_list p (gen_rv_list X n) t)))) =
             0)
   
   [rel_series_parallel_RBD_exp_dist_fail_rate]  Theorem
      
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
                  ((series of (λa. parallel (rbd_list a)))
                     (two_dim_rel_event_list p L t))) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
   
   [rel_series_parallel_RBD_exp_dist_fail_rate_lemma1]  Theorem
      
      ⊢ ∀p t l c.
            0 ≤ t ∧ prob_space p ∧ (LENGTH l = LENGTH c) ∧
            (∀x'. MEM x' (rel_event_list p l t) ⇒ x' ∈ events p) ∧
            exp_dist_list p l c ⇒
            (1 −
             list_prod
               (one_minus_list (list_prob p (rel_event_list p l t))) =
             1 − list_prod (one_minus_list (exp_func_list c t)))
   
   [rel_virtual_cloud_server]  Theorem
      
      ⊢ ∀L_VM L_VMM L_HW C_VM C_VMM C_HW p t.
            ¬NULL L_VM ∧ 0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x' (rel_event_list p (L_VMM::L_HW::L_VM) t) ⇒
                 x' ∈ events p) ∧
            mutual_indep p (rel_event_list p (L_VMM::L_HW::L_VM) t) ∧
            (LENGTH C_VM = LENGTH L_VM) ∧
            exp_dist_list p (L_VMM::L_HW::L_VM) (C_VMM::C_HW::C_VM) ⇒
            (prob p
               (rbd_struct p
                  ((series of
                    (λa. parallel (rbd_list (rel_event_list p a t))))
                     [L_VMM::L_HW::L_VM])) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (exp_func_list a t))))
               [C_VMM::C_HW::C_VM])
   
   [seq_rel_prod_tend_0]  Theorem
      
      ⊢ ∀n p X t.
            0 ≤ t ∧ possibly p (rel_event p X t) ∧ prob_space p ⇒
            (λn.
                 list_prod
                   (one_minus_list
                      (list_prob p (rel_event_list p (gen_rv_list X n) t)))) -->
            0
   
   [virt_config_bounds]  Theorem
      
      ⊢ ∀X_VM X_VMM X_HW p n t.
            prob_space p ∧ 0 ≤ t ∧
            ¬NULL (rel_event_list p (gen_rv_list X_VM n) t) ∧
            rel_event p X_VMM t ∈ events p ∧
            rel_event p X_VM t ∈ events p ∧ rel_event p X_HW t ∈ events p ∧
            (∀x'.
                 MEM x' (rel_event_list p (gen_rv_list X_VM n) t) ⇒
                 x' ∈ events p) ∧
            rel_virt_cloud_server p [[X_VMM]; [X_HW]; gen_rv_list X_VM n] t <
            Reliability p X_VMM t ∧ Reliability p X_HW t < 1 ∧
            0 < Reliability p X_VMM t ∧
            (0 < Reliability p X_VM t ∧ Reliability p X_VM t < 1) ∧
            mutual_indep p
              (rel_event_list p (X_VMM::X_HW::gen_rv_list X_VM n) t) ⇒
            &n >
            log_base 10
              (1 −
               rel_virt_cloud_server p
                 [[X_VMM]; [X_HW]; gen_rv_list X_VM n] t /
               Reliability p X_VMM t) /
            log_base 10 (1 − Reliability p X_VM t)
   
   
*)
end
