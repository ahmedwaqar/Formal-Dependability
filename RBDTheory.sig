signature RBDTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val UNIONL_def : thm
    val big_inter_def : thm
    val compl_list_def : thm
    val compl_pspace_def : thm
    val list_prob_def : thm
    val list_prod_def : thm
    val list_prod_one_minus_rel_def : thm
    val list_prod_rel_def : thm
    val mutual_indep_def : thm
    val of_DEF : thm
    val one_minus_list_def : thm
    val rbd_TY_DEF : thm
    val rbd_case_def : thm
    val rbd_list_def : thm
    val rbd_size_def : thm
  
  (*  Theorems  *)
    val IN_UNIONL : thm
    val MEM_NULL_arrang1 : thm
    val Parallel_Series_struct_thm : thm
    val Prob_Incl_excl : thm
    val datatype_rbd : thm
    val in_events_big_inter : thm
    val in_events_parallel_of_series_parallel : thm
    val in_events_parallel_series : thm
    val in_events_series_parallel : thm
    val in_events_series_parallel_of_series_parallel : thm
    val inter_set_arrang1 : thm
    val mutual_indep_FLAT_append1 : thm
    val mutual_indep_FLAT_front_cons : thm
    val mutual_indep_append1 : thm
    val mutual_indep_append_sym : thm
    val mutual_indep_compl : thm
    val mutual_indep_compl_event_imp_norm_event : thm
    val mutual_indep_cons : thm
    val mutual_indep_cons_append : thm
    val mutual_indep_cons_append1 : thm
    val mutual_indep_cons_append10 : thm
    val mutual_indep_cons_append11 : thm
    val mutual_indep_cons_append12 : thm
    val mutual_indep_cons_append13 : thm
    val mutual_indep_cons_append14 : thm
    val mutual_indep_cons_append15 : thm
    val mutual_indep_cons_append16 : thm
    val mutual_indep_cons_append17 : thm
    val mutual_indep_cons_append18 : thm
    val mutual_indep_cons_append19 : thm
    val mutual_indep_cons_swap : thm
    val mutual_indep_flat_append : thm
    val mutual_indep_flat_append1 : thm
    val mutual_indep_flat_cons1 : thm
    val mutual_indep_flat_cons2 : thm
    val mutual_indep_flat_cons3 : thm
    val mutual_indep_flat_cons4 : thm
    val mutual_indep_flat_cons5 : thm
    val mutual_indep_flat_cons6 : thm
    val mutual_indep_front_append : thm
    val one_minus_eq_lemm : thm
    val parallel_lem1 : thm
    val parallel_lem2 : thm
    val parallel_lem3 : thm
    val parallel_lem4 : thm
    val parallel_lem5 : thm
    val parallel_lem6 : thm
    val parallel_lem7 : thm
    val parallel_lem8 : thm
    val parallel_rbd_indep_series_parallel_rbd : thm
    val parallel_rbd_lem1 : thm
    val parallel_rbd_lem2 : thm
    val parallel_rbd_lem3 : thm
    val parallel_rbd_lem4 : thm
    val parallel_rbd_lem5 : thm
    val parallel_rbd_lem6 : thm
    val parallel_rbd_lem7 : thm
    val parallel_series_lem1 : thm
    val parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd : thm
    val parallel_series_struct_rbd_v2 : thm
    val parallel_struct_thm : thm
    val prob_B : thm
    val prob_big_inter_compl_list : thm
    val prob_compl_subset : thm
    val prob_indep_big_inter1 : thm
    val prob_indep_compl_event_big_inter_list : thm
    val rbd_11 : thm
    val rbd_Axiom : thm
    val rbd_case_cong : thm
    val rbd_case_eq : thm
    val rbd_distinct : thm
    val rbd_induction : thm
    val rbd_nchotomy : thm
    val rbd_struct_def : thm
    val rbd_struct_ind : thm
    val rel_nested_series_parallel_rbd : thm
    val rel_parallel_of_series_parallel_rbd : thm
    val rel_parallel_series_rbd : thm
    val series_parallel_rbd_indep_series_parallel_of_series_parallel : thm
    val series_parallel_struct_thm : thm
    val series_parallel_struct_thm_v2 : thm
    val series_rbd_append : thm
    val series_rbd_append2 : thm
    val series_rbd_eq_big_inter : thm
    val series_rbd_indep_parallel_series_rbd : thm
    val series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel : thm
    val series_rbd_indep_series_parallel_of_series_parallel : thm
    val series_rbd_indep_series_parallel_rbd : thm
    val series_struct_thm : thm
  
  val RBD_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [probability] Parent theory of "RBD"
   
   [sorting] Parent theory of "RBD"
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [big_inter_def]  Definition
      
      ⊢ (∀p. big_inter p [] = p_space p) ∧
        ∀p h t. big_inter p (h::t) = h ∩ big_inter p t
   
   [compl_list_def]  Definition
      
      ⊢ ∀p L. compl_list p L = MAP (λa. p_space p DIFF a) L
   
   [compl_pspace_def]  Definition
      
      ⊢ ∀p s. compl_pspace p s = p_space p DIFF s
   
   [list_prob_def]  Definition
      
      ⊢ (∀p. list_prob p [] = []) ∧
        ∀p h t. list_prob p (h::t) = prob p h::list_prob p t
   
   [list_prod_def]  Definition
      
      ⊢ (list_prod [] = 1) ∧ ∀h t. list_prod (h::t) = h * list_prod t
   
   [list_prod_one_minus_rel_def]  Definition
      
      ⊢ ∀p L.
            list_prod_one_minus_rel p L =
            MAP (λa. list_prod (one_minus_list (list_prob p a))) L
   
   [list_prod_rel_def]  Definition
      
      ⊢ ∀p L. list_prod_rel p L = MAP (λa. list_prod (list_prob p a)) L
   
   [mutual_indep_def]  Definition
      
      ⊢ ∀p L.
            mutual_indep p L ⇔
            ∀L1 n.
                PERM L L1 ∧ 1 ≤ n ∧ n ≤ LENGTH L ⇒
                (prob p (big_inter p (TAKE n L1)) =
                 list_prod (list_prob p (TAKE n L1)))
   
   [of_DEF]  Definition
      
      ⊢ ∀g f. g of f = g ∘ (λa. MAP f a)
   
   [one_minus_list_def]  Definition
      
      ⊢ (one_minus_list [] = []) ∧
        ∀h t. one_minus_list (h::t) = 1 − h::one_minus_list t
   
   [rbd_TY_DEF]  Definition
      
      ⊢ ∃rep.
            TYPE_DEFINITION
              (λa0'.
                   ∀'rbd' '@temp @ind_typeRBD0list' .
                       (∀a0'.
                            (∃a.
                                 (a0' =
                                  (λa.
                                       ind_type$CONSTR 0 ARB
                                         (ind_type$FCONS a
                                            (λn. ind_type$BOTTOM))) a) ∧
                                 '@temp @ind_typeRBD0list' a) ∨
                            (∃a.
                                 (a0' =
                                  (λa.
                                       ind_type$CONSTR (SUC 0) ARB
                                         (ind_type$FCONS a
                                            (λn. ind_type$BOTTOM))) a) ∧
                                 '@temp @ind_typeRBD0list' a) ∨
                            (∃a.
                                 a0' =
                                 (λa.
                                      ind_type$CONSTR (SUC (SUC 0)) a
                                        (λn. ind_type$BOTTOM)) a) ⇒
                            'rbd' a0') ∧
                       (∀a1'.
                            (a1' =
                             ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (∃a0 a1.
                                 (a1' =
                                  (λa0 a1.
                                       ind_type$CONSTR
                                         (SUC (SUC (SUC (SUC 0)))) ARB
                                         (ind_type$FCONS a0
                                            (ind_type$FCONS a1
                                               (λn. ind_type$BOTTOM)))) a0
                                    a1) ∧ 'rbd' a0 ∧
                                 '@temp @ind_typeRBD0list' a1) ⇒
                            '@temp @ind_typeRBD0list' a1') ⇒
                       'rbd' a0') rep
   
   [rbd_case_def]  Definition
      
      ⊢ (∀a f f1 f2. rbd_CASE (series a) f f1 f2 = f a) ∧
        (∀a f f1 f2. rbd_CASE (parallel a) f f1 f2 = f1 a) ∧
        ∀a f f1 f2. rbd_CASE (atomic a) f f1 f2 = f2 a
   
   [rbd_list_def]  Definition
      
      ⊢ (rbd_list [] = []) ∧ ∀h t. rbd_list (h::t) = atomic h::rbd_list t
   
   [rbd_size_def]  Definition
      
      ⊢ (∀f a. rbd_size f (series a) = 1 + rbd1_size f a) ∧
        (∀f a. rbd_size f (parallel a) = 1 + rbd1_size f a) ∧
        (∀f a. rbd_size f (atomic a) = 1) ∧ (∀f. rbd1_size f [] = 0) ∧
        ∀f a0 a1.
            rbd1_size f (a0::a1) = 1 + (rbd_size f a0 + rbd1_size f a1)
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [MEM_NULL_arrang1]  Theorem
      
      ⊢ ∀L1 L2 L.
            (∀x. MEM x (L1::L2::L) ⇒ ¬NULL x) ⇒
            ∀x. MEM x ((L1 ⧺ L2)::L) ⇒ ¬NULL x
   
   [Parallel_Series_struct_thm]  Theorem
      
      ⊢ ∀p L.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT L) ⇒
            (prob p
               (rbd_struct p (parallel (MAP (λa. series (rbd_list a)) L))) =
             1 − list_prod (one_minus_list (list_prod_rel p L)))
   
   [Prob_Incl_excl]  Theorem
      
      ⊢ ∀p a b.
            prob_space p ∧ a ∈ events p ∧ b ∈ events p ⇒
            (prob p (a ∪ b) = prob p a + prob p b − prob p (a ∩ b))
   
   [datatype_rbd]  Theorem
      
      ⊢ DATATYPE (rbd series parallel atomic)
   
   [in_events_big_inter]  Theorem
      
      ⊢ ∀L p.
            (∀x. MEM x L ⇒ x ∈ events p) ∧ prob_space p ⇒
            big_inter p L ∈ events p
   
   [in_events_parallel_of_series_parallel]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x'. MEM x' (FLAT (FLAT L)) ⇒ x' ∈ events p) ⇒
            rbd_struct p
              (parallel (MAP (series of (λa. parallel (rbd_list a))) L)) ∈
            events p
   
   [in_events_parallel_series]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x (FLAT L) ⇒ x ∈ events p) ⇒
            rbd_struct p (parallel (MAP (λa. series (rbd_list a)) L)) ∈
            events p
   
   [in_events_series_parallel]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x (FLAT L) ⇒ x ∈ events p) ⇒
            rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L)) ∈
            events p
   
   [in_events_series_parallel_of_series_parallel]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧
            (∀x'. MEM x' (FLAT (FLAT (FLAT L))) ⇒ x' ∈ events p) ⇒
            rbd_struct p
              (series
                 (MAP (parallel of series of (λa. parallel (rbd_list a))) L)) ∈
            events p
   
   [inter_set_arrang1]  Theorem
      
      ⊢ ∀a b c d. a ∩ b ∩ c ∩ d = a ∩ (b ∩ c) ∩ d
   
   [mutual_indep_FLAT_append1]  Theorem
      
      ⊢ ∀L L1 L2 p.
            mutual_indep p (FLAT (L1::L2::L)) ⇒ mutual_indep p (L1 ⧺ L2)
   
   [mutual_indep_FLAT_front_cons]  Theorem
      
      ⊢ ∀h L p. mutual_indep p (FLAT (h::L)) ⇒ mutual_indep p (FLAT L)
   
   [mutual_indep_append1]  Theorem
      
      ⊢ ∀L1 L2 L p.
            mutual_indep p (L1 ⧺ L2 ⧺ L) ⇒ mutual_indep p (L2 ⧺ L1 ⧺ L)
   
   [mutual_indep_append_sym]  Theorem
      
      ⊢ ∀L1 L p. mutual_indep p (L1 ⧺ L) ⇒ mutual_indep p (L ⧺ L1)
   
   [mutual_indep_compl]  Theorem
      
      ⊢ ∀L1 p.
            prob_space p ∧ mutual_indep p L1 ∧
            (∀x. MEM x L1 ⇒ x ∈ events p) ∧ 1 ≤ LENGTH L1 ⇒
            mutual_indep p (compl_list p L1)
   
   [mutual_indep_compl_event_imp_norm_event]  Theorem
      
      ⊢ ∀L1 p.
            prob_space p ∧ mutual_indep p (compl_list p L1) ∧
            (∀x. MEM x L1 ⇒ x ∈ events p) ∧ 1 ≤ LENGTH L1 ⇒
            mutual_indep p L1
   
   [mutual_indep_cons]  Theorem
      
      ⊢ ∀L h p. mutual_indep p (h::L) ⇒ mutual_indep p L
   
   [mutual_indep_cons_append]  Theorem
      
      ⊢ ∀L1 L2 h p.
            mutual_indep p (h::L1 ⧺ L2) ⇒ mutual_indep p (L1 ⧺ h::L2)
   
   [mutual_indep_cons_append1]  Theorem
      
      ⊢ ∀L1 L2 Q h p.
            mutual_indep p (h::L1 ⧺ Q::L2) ⇒ mutual_indep p (L1 ⧺ Q::h::L2)
   
   [mutual_indep_cons_append10]  Theorem
      
      ⊢ ∀L1 h L p.
            mutual_indep p (FLAT (L1::h::L)) ⇒ mutual_indep p (FLAT (h::L))
   
   [mutual_indep_cons_append11]  Theorem
      
      ⊢ ∀h L1 L2 L p.
            mutual_indep p (L1 ⧺ h::(L2 ⧺ L)) ⇒
            mutual_indep p (h::(L1 ⧺ L))
   
   [mutual_indep_cons_append12]  Theorem
      
      ⊢ ∀h L1 L2 L p.
            mutual_indep p (FLAT (L1::(h::L2)::L)) ⇒
            mutual_indep p (FLAT ((h::L1)::L))
   
   [mutual_indep_cons_append13]  Theorem
      
      ⊢ ∀L L1 L2 p.
            mutual_indep p (FLAT (L1::L2::L)) ⇒ mutual_indep p (L1 ⧺ L2)
   
   [mutual_indep_cons_append14]  Theorem
      
      ⊢ ∀h L1 L p. mutual_indep p (L1 ⧺ h::L) ⇒ mutual_indep p (L1 ⧺ L)
   
   [mutual_indep_cons_append15]  Theorem
      
      ⊢ ∀h L1 L2 L p.
            mutual_indep p (FLAT (L1::(h::L2)::L)) ⇒
            mutual_indep p (FLAT ([h]::L))
   
   [mutual_indep_cons_append16]  Theorem
      
      ⊢ ∀h L1 L2 L p.
            mutual_indep p (FLAT (L1::(h::L2)::L)) ⇒
            mutual_indep p (FLAT ([h]::L2::L))
   
   [mutual_indep_cons_append17]  Theorem
      
      ⊢ ∀h L1 L p.
            mutual_indep p (FLAT ((h::L1)::L)) ⇒
            mutual_indep p (FLAT ([h]::L))
   
   [mutual_indep_cons_append18]  Theorem
      
      ⊢ ∀h L1 L p.
            mutual_indep p (FLAT ((h::L1)::L)) ⇒
            mutual_indep p (FLAT (L1::L))
   
   [mutual_indep_cons_append19]  Theorem
      
      ⊢ ∀h L1 L p.
            mutual_indep p (FLAT ((h::L1)::L)) ⇒
            mutual_indep p (FLAT (L1::[h]::L))
   
   [mutual_indep_cons_swap]  Theorem
      
      ⊢ ∀p L1 h. mutual_indep p (h::L1) ⇒ mutual_indep p (L1 ⧺ [h])
   
   [mutual_indep_flat_append]  Theorem
      
      ⊢ ∀L L1 L2 p.
            mutual_indep p (FLAT (L1::L2::L)) ⇒ mutual_indep p (L1 ⧺ L2)
   
   [mutual_indep_flat_append1]  Theorem
      
      ⊢ ∀L h L1 p.
            mutual_indep p (FLAT (L1::h::L)) ⇒
            mutual_indep p (FLAT ((h ⧺ L1)::L))
   
   [mutual_indep_flat_cons1]  Theorem
      
      ⊢ ∀L1 h L p.
            mutual_indep p (FLAT ((h::L1)::L)) ⇒
            mutual_indep p (FLAT (L1::[h]::L))
   
   [mutual_indep_flat_cons2]  Theorem
      
      ⊢ ∀L1 h L p.
            mutual_indep p (FLAT (L1::h::L)) ⇒ mutual_indep p (FLAT (h::L))
   
   [mutual_indep_flat_cons3]  Theorem
      
      ⊢ ∀L1 h L p.
            mutual_indep p (FLAT (L1::h::L)) ⇒
            mutual_indep p (FLAT (L1::L))
   
   [mutual_indep_flat_cons4]  Theorem
      
      ⊢ ∀L1 h L p.
            mutual_indep p (FLAT (L1::h::L)) ⇒
            mutual_indep p (FLAT (L1::L))
   
   [mutual_indep_flat_cons5]  Theorem
      
      ⊢ ∀L L1 L2 p. mutual_indep p (FLAT (L1::L2::L)) ⇒ mutual_indep p L1
   
   [mutual_indep_flat_cons6]  Theorem
      
      ⊢ ∀h L1 L p.
            mutual_indep p (FLAT ((h::L1)::L)) ⇒
            mutual_indep p (FLAT [L1; [h]])
   
   [mutual_indep_front_append]  Theorem
      
      ⊢ ∀L1 L p. mutual_indep p (L1 ⧺ L) ⇒ mutual_indep p L
   
   [one_minus_eq_lemm]  Theorem
      
      ⊢ ∀p L.
            prob_space p ⇒
            (list_prod
               (one_minus_list
                  (MAP (λa. list_prod (one_minus_list (list_prob p a))) L)) =
             list_prod
               (MAP (λa. 1 − list_prod (one_minus_list (list_prob p a))) L))
   
   [parallel_lem1]  Theorem
      
      ⊢ ∀p s t.
            p_space p DIFF (s ∪ t) =
            (p_space p DIFF s) ∩ (p_space p DIFF t)
   
   [parallel_lem2]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x L ⇒ x ∈ events p) ⇒
            (rbd_struct p (series (rbd_list (compl_list p L))) =
             p_space p DIFF rbd_struct p (parallel (rbd_list L)))
   
   [parallel_lem3]  Theorem
      
      ⊢ ∀L p.
            (∀x. MEM x L ⇒ x ∈ events p) ∧ prob_space p ⇒
            rbd_struct p (parallel (rbd_list L)) ∈ events p
   
   [parallel_lem4]  Theorem
      
      ⊢ ∀p L.
            (∀x. MEM x L ⇒ x ∈ events p) ∧ prob_space p ∧
            rbd_struct p (parallel (rbd_list L)) ∈ events p ⇒
            rbd_struct p (parallel (rbd_list L)) ⊆ p_space p
   
   [parallel_lem5]  Theorem
      
      ⊢ ∀p L. rbd_struct p (series (rbd_list L)) = big_inter p L
   
   [parallel_lem6]  Theorem
      
      ⊢ ∀p x L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (prob p (rbd_struct p (parallel (rbd_list L))) =
             1 − prob p (rbd_struct p (series (rbd_list (compl_list p L)))))
   
   [parallel_lem7]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (one_minus_list (list_prob p L) = list_prob p (compl_list p L))
   
   [parallel_lem8]  Theorem
      
      ⊢ ∀L. one_minus_list L = MAP (λa. 1 − a) L
   
   [parallel_rbd_indep_series_parallel_rbd]  Theorem
      
      ⊢ ∀p L1 L.
            prob_space p ∧ (∀x. MEM x (L1::L) ⇒ ¬NULL x) ∧
            (∀x. MEM x (FLAT (L1::L)) ⇒ x ∈ events p) ∧
            mutual_indep p (FLAT (L1::L)) ⇒
            (prob p
               (rbd_struct p (parallel (rbd_list L1)) ∩
                rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))) =
             prob p (rbd_struct p (parallel (rbd_list L1))) *
             prob p
               (rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))))
   
   [parallel_rbd_lem1]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (one_minus_list (list_prob p L) = list_prob p (compl_list p L))
   
   [parallel_rbd_lem2]  Theorem
      
      ⊢ ∀L1 L2 Q. LENGTH (L1 ⧺ Q::L2) = LENGTH (Q::L1 ⧺ L2)
   
   [parallel_rbd_lem3]  Theorem
      
      ⊢ ∀A B C D. A ∩ B ∩ C ∩ D = B ∩ C ∩ D ∩ A
   
   [parallel_rbd_lem4]  Theorem
      
      ⊢ ∀A C. A ∩ (p_space p DIFF C) = A ∩ p_space p DIFF A ∩ C
   
   [parallel_rbd_lem5]  Theorem
      
      ⊢ ∀m L x. MEM x (TAKE m L) ⇒ MEM x L
   
   [parallel_rbd_lem6]  Theorem
      
      ⊢ ∀A C. A ∩ (p_space p DIFF C) = A ∩ p_space p DIFF A ∩ C
   
   [parallel_rbd_lem7]  Theorem
      
      ⊢ ∀L1 p.
            prob_space p ∧ (∀x. MEM x L1 ⇒ x ∈ events p) ⇒
            (L1 = compl_list p (compl_list p L1))
   
   [parallel_series_lem1]  Theorem
      
      ⊢ ∀l1 l2 l3 l4.
            (PERM l1 = PERM (l2 ⧺ l3)) ⇒
            (PERM (l1 ⧺ l4) = PERM (l2 ⧺ (l4 ⧺ l3)))
   
   [parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd]  Theorem
      
      ⊢ ∀p L1 L.
            prob_space p ∧ (∀z. MEM z (FLAT (FLAT (L1::L))) ⇒ ¬NULL z) ∧
            (∀x'. MEM x' (FLAT (FLAT (FLAT (L1::L)))) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (FLAT (FLAT (L1::L)))) ⇒
            (prob p
               (rbd_struct p
                  (parallel
                     (MAP (series of (λa. parallel (rbd_list a))) L1)) ∩
                rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))) =
             prob p
               (rbd_struct p
                  (parallel
                     (MAP (series of (λa. parallel (rbd_list a))) L1))) *
             prob p
               (rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))))
   
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
   
   [parallel_struct_thm]  Theorem
      
      ⊢ ∀p L.
            ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧ prob_space p ∧
            mutual_indep p L ⇒
            (prob p (rbd_struct p (parallel (rbd_list L))) =
             1 − list_prod (one_minus_list (list_prob p L)))
   
   [prob_B]  Theorem
      
      ⊢ ∀p a b.
            prob_space p ∧ a ∈ events p ∧ b ∈ events p ⇒
            (prob p b = prob p (a ∩ b) + prob p (compl_pspace p a ∩ b))
   
   [prob_big_inter_compl_list]  Theorem
      
      ⊢ ∀L1 n p.
            prob_space p ∧ mutual_indep p L1 ∧
            (∀x. MEM x L1 ⇒ x ∈ events p) ∧ 1 ≤ LENGTH L1 ⇒
            (prob p (big_inter p (TAKE n (compl_list p L1))) =
             list_prod (list_prob p (TAKE n (compl_list p L1))))
   
   [prob_compl_subset]  Theorem
      
      ⊢ ∀p s t.
            prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ t ⊆ s ⇒
            (prob p (s DIFF t) = prob p s − prob p t)
   
   [prob_indep_big_inter1]  Theorem
      
      ⊢ ∀L1 L2 Q n p.
            prob_space p ∧ mutual_indep p (L1 ⧺ Q::L2) ∧
            (∀x. MEM x (L1 ⧺ Q::L2) ⇒ x ∈ events p) ∧
            1 ≤ LENGTH (L1 ⧺ Q::L2) ⇒
            (prob p
               (big_inter p (TAKE n (compl_list p L1)) ∩
                big_inter p (Q::L2)) =
             list_prod (list_prob p (TAKE n (compl_list p L1))) *
             list_prod (list_prob p (Q::L2)))
   
   [prob_indep_compl_event_big_inter_list]  Theorem
      
      ⊢ ∀L1 n h p.
            mutual_indep p (h::L1) ∧ (∀x. MEM x (h::L1) ⇒ x ∈ events p) ∧
            prob_space p ∧ (LENGTH L1 = 1) ⇒
            (prob p
               ((p_space p DIFF h) ∩ big_inter p (TAKE n (compl_list p L1))) =
             prob p (p_space p DIFF h) *
             list_prod (list_prob p (TAKE n (compl_list p L1))))
   
   [rbd_11]  Theorem
      
      ⊢ (∀a a'. (series a = series a') ⇔ (a = a')) ∧
        (∀a a'. (parallel a = parallel a') ⇔ (a = a')) ∧
        ∀a a'. (atomic a = atomic a') ⇔ (a = a')
   
   [rbd_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4.
            ∃fn0 fn1.
                (∀a. fn0 (series a) = f0 a (fn1 a)) ∧
                (∀a. fn0 (parallel a) = f1 a (fn1 a)) ∧
                (∀a. fn0 (atomic a) = f2 a) ∧ (fn1 [] = f3) ∧
                ∀a0 a1. fn1 (a0::a1) = f4 a0 a1 (fn0 a0) (fn1 a1)
   
   [rbd_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 f2.
            (M = M') ∧ (∀a. (M' = series a) ⇒ (f a = f' a)) ∧
            (∀a. (M' = parallel a) ⇒ (f1 a = f1' a)) ∧
            (∀a. (M' = atomic a) ⇒ (f2 a = f2' a)) ⇒
            (rbd_CASE M f f1 f2 = rbd_CASE M' f' f1' f2')
   
   [rbd_case_eq]  Theorem
      
      ⊢ (rbd_CASE x f f1 f2 = v) ⇔
        (∃l. (x = series l) ∧ (f l = v)) ∨
        (∃l. (x = parallel l) ∧ (f1 l = v)) ∨
        ∃f'. (x = atomic f') ∧ (f2 f' = v)
   
   [rbd_distinct]  Theorem
      
      ⊢ (∀a' a. series a ≠ parallel a') ∧ (∀a' a. series a ≠ atomic a') ∧
        ∀a' a. parallel a ≠ atomic a'
   
   [rbd_induction]  Theorem
      
      ⊢ ∀P0 P1.
            (∀l. P1 l ⇒ P0 (series l)) ∧ (∀l. P1 l ⇒ P0 (parallel l)) ∧
            (∀f. P0 (atomic f)) ∧ P1 [] ∧ (∀r l. P0 r ∧ P1 l ⇒ P1 (r::l)) ⇒
            (∀r. P0 r) ∧ ∀l. P1 l
   
   [rbd_nchotomy]  Theorem
      
      ⊢ ∀rr.
            (∃l. rr = series l) ∨ (∃l. rr = parallel l) ∨ ∃f. rr = atomic f
   
   [rbd_struct_def]  Theorem
      
      ⊢ (∀p a. rbd_struct p (atomic a) = a) ∧
        (∀p. rbd_struct p (series []) = p_space p) ∧
        (∀xs x p.
             rbd_struct p (series (x::xs)) =
             rbd_struct p x ∩ rbd_struct p (series xs)) ∧
        (∀p. rbd_struct p (parallel []) = ∅) ∧
        ∀xs x p.
            rbd_struct p (parallel (x::xs)) =
            rbd_struct p x ∪ rbd_struct p (parallel xs)
   
   [rbd_struct_ind]  Theorem
      
      ⊢ ∀P.
            (∀p a. P p (atomic a)) ∧ (∀p. P p (series [])) ∧
            (∀p x xs. P p x ∧ P p (series xs) ⇒ P p (series (x::xs))) ∧
            (∀p. P p (parallel [])) ∧
            (∀p x xs. P p x ∧ P p (parallel xs) ⇒ P p (parallel (x::xs))) ⇒
            ∀v v1. P v v1
   
   [rel_nested_series_parallel_rbd]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀z. MEM z (FLAT (FLAT L)) ⇒ ¬NULL z) ∧
            (∀x'. MEM x' (FLAT (FLAT (FLAT L))) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (FLAT (FLAT L))) ⇒
            (prob p
               (rbd_struct p
                  ((series of parallel of series of
                    (λa. parallel (rbd_list a))) L)) =
             (list_prod of (λa. 1 − list_prod (one_minus_list a)) of
              (λa. list_prod a) of
              (λa. 1 − list_prod (one_minus_list (list_prob p a)))) L)
   
   [rel_parallel_of_series_parallel_rbd]  Theorem
      
      ⊢ ∀p L1 L.
            prob_space p ∧ (∀z. MEM z (FLAT (FLAT (L1::L))) ⇒ ¬NULL z) ∧
            (∀x'. MEM x' (FLAT (FLAT (FLAT (L1::L)))) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (FLAT (FLAT (L1::L)))) ⇒
            (prob p
               (rbd_struct p
                  (parallel
                     (MAP (series of (λa. parallel (rbd_list a))) L1))) =
             1 −
             list_prod
               (one_minus_list
                  (MAP
                     ((λa. list_prod a) of
                      (λa. 1 − list_prod (one_minus_list (list_prob p a))))
                     L1)))
   
   [rel_parallel_series_rbd]  Theorem
      
      ⊢ ∀p L.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT L) ⇒
            (prob p
               (rbd_struct p ((parallel of (λa. series (rbd_list a))) L)) =
             1 − list_prod (one_minus_list (list_prod_rel p L)))
   
   [series_parallel_rbd_indep_series_parallel_of_series_parallel]  Theorem
      
      ⊢ ∀p L1 L.
            prob_space p ∧ (∀z. MEM z (FLAT (FLAT ([L1]::L))) ⇒ ¬NULL z) ∧
            (∀x'. MEM x' (FLAT (FLAT (FLAT ([L1]::L)))) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT (FLAT (FLAT ([L1]::L)))) ⇒
            (prob p
               (rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L1)) ∩
                rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))) =
             prob p
               (rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L1))) *
             prob p
               (rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))))
   
   [series_parallel_struct_thm]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀z. MEM z L ⇒ ¬NULL z) ∧
            (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT L) ⇒
            (prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L)) =
             list_prod (one_minus_list (list_prod_one_minus_rel p L)))
   
   [series_parallel_struct_thm_v2]  Theorem
      
      ⊢ ∀p L.
            (∀z. MEM z L ⇒ ¬NULL z) ∧ prob_space p ∧
            (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧
            mutual_indep p (FLAT L) ⇒
            (prob p
               (rbd_struct p ((series of (λa. parallel (rbd_list a))) L)) =
             (list_prod of
              (λa. 1 − list_prod (one_minus_list (list_prob p a)))) L)
   
   [series_rbd_append]  Theorem
      
      ⊢ ∀p h L1.
            prob_space p ∧ (∀x. MEM x (h ⧺ L1) ⇒ x ∈ events p) ⇒
            (rbd_struct p (series (rbd_list h)) ∩
             rbd_struct p (series (rbd_list L1)) =
             rbd_struct p (series (rbd_list (h ⧺ L1))))
   
   [series_rbd_append2]  Theorem
      
      ⊢ ∀p h L1.
            prob_space p ∧ (∀x. MEM x (h ⧺ L1) ⇒ x ∈ events p) ∧ ¬NULL h ∧
            ¬NULL L1 ∧ mutual_indep p (h ⧺ L1) ⇒
            (prob p (rbd_struct p (series (rbd_list (h ⧺ L1)))) =
             prob p (rbd_struct p (series (rbd_list h))) *
             prob p (rbd_struct p (series (rbd_list L1))))
   
   [series_rbd_eq_big_inter]  Theorem
      
      ⊢ ∀p L. rbd_struct p (series (rbd_list L)) = big_inter p L
   
   [series_rbd_indep_parallel_series_rbd]  Theorem
      
      ⊢ ∀p L L1.
            prob_space p ∧ (∀x. MEM x (L1::L) ⇒ ¬NULL x) ∧
            (∀x. MEM x (FLAT (L1::L)) ⇒ x ∈ events p) ∧
            mutual_indep p (FLAT (L1::L)) ⇒
            (prob p
               (rbd_struct p (series (rbd_list L1)) ∩
                rbd_struct p (parallel (MAP (λa. series (rbd_list a)) L))) =
             prob p (rbd_struct p (series (rbd_list L1))) *
             prob p
               (rbd_struct p (parallel (MAP (λa. series (rbd_list a)) L))))
   
   [series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel]  Theorem
      
      ⊢ ∀p h' L1 L.
            prob_space p ∧
            (∀z. MEM z (FLAT (FLAT ([[[L1]]] ⧺ [h']::L))) ⇒ ¬NULL z) ∧
            (∀x'.
                 MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ⧺ [h']::L)))) ⇒
                 x' ∈ events p) ∧
            mutual_indep p (L1 ⧺ FLAT (FLAT (FLAT ([h']::L)))) ∧
            (∀L1.
                 prob_space p ∧
                 (∀z. MEM z (FLAT (FLAT ([[[L1]]] ⧺ L))) ⇒ ¬NULL z) ∧
                 (∀x'.
                      MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ⧺ L)))) ⇒
                      x' ∈ events p) ∧
                 mutual_indep p (L1 ⧺ FLAT (FLAT (FLAT L))) ⇒
                 (prob p
                    (rbd_struct p (series (rbd_list L1)) ∩
                     rbd_struct p
                       (series
                          (MAP
                             (parallel of series of
                              (λa. parallel (rbd_list a))) L))) =
                  prob p (rbd_struct p (series (rbd_list L1))) *
                  prob p
                    (rbd_struct p
                       (series
                          (MAP
                             (parallel of series of
                              (λa. parallel (rbd_list a))) L))))) ⇒
            (prob p
               (rbd_struct p (series (rbd_list L1)) ∩
                rbd_struct p (series (MAP (λa. parallel (rbd_list a)) h')) ∩
                rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))) =
             prob p (rbd_struct p (series (rbd_list L1))) *
             prob p
               (rbd_struct p (series (MAP (λa. parallel (rbd_list a)) h')) ∩
                rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))))
   
   [series_rbd_indep_series_parallel_of_series_parallel]  Theorem
      
      ⊢ ∀p L L1.
            prob_space p ∧
            (∀z. MEM z (FLAT (FLAT ([[[L1]]] ⧺ L))) ⇒ ¬NULL z) ∧
            (∀x'.
                 MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ⧺ L)))) ⇒ x' ∈ events p) ∧
            mutual_indep p (L1 ⧺ FLAT (FLAT (FLAT L))) ⇒
            (prob p
               (rbd_struct p (series (rbd_list L1)) ∩
                rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))) =
             prob p (rbd_struct p (series (rbd_list L1))) *
             prob p
               (rbd_struct p
                  (series
                     (MAP
                        (parallel of series of (λa. parallel (rbd_list a)))
                        L))))
   
   [series_rbd_indep_series_parallel_rbd]  Theorem
      
      ⊢ ∀p L L1.
            prob_space p ∧ (∀x. MEM x (L1::L) ⇒ ¬NULL x) ∧
            (∀x. MEM x (FLAT (L1::L)) ⇒ x ∈ events p) ∧
            mutual_indep p (FLAT (L1::L)) ⇒
            (prob p
               (rbd_struct p (series (rbd_list L1)) ∩
                rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))) =
             prob p (rbd_struct p (series (rbd_list L1))) *
             prob p
               (rbd_struct p (series (MAP (λa. parallel (rbd_list a)) L))))
   
   [series_struct_thm]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧
            mutual_indep p L ⇒
            (prob p (rbd_struct p (series (rbd_list L))) =
             list_prod (list_prob p L))
   
   
*)
end
