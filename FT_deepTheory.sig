signature FT_deepTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val K_out_N_struct_def : thm
    val NOR_FT_gate_def : thm
    val UNIONL_def : thm
    val XOR_FT_gate_def : thm
    val comp_FT_gate_def : thm
    val gate_TY_DEF : thm
    val gate_case_def : thm
    val gate_list_def : thm
    val gate_size_def : thm
    val has_size_def : thm
    val inhibit_FT_gate_def : thm
    val inter_list_def : thm
    val majority_voting_FT_gate_def : thm
    val sum_set_def : thm
    val union_list_def : thm
  
  (*  Theorems  *)
    val AND_gate_append : thm
    val AND_gate_eq_big_inter : thm
    val AND_gate_thm : thm
    val BIGINTER_SET : thm
    val BIGUNION_EQ_UNION_LIST : thm
    val BINOMIAL_DEF1 : thm
    val BINOMIAL_DEF2 : thm
    val BINOMIAL_DEF3 : thm
    val BINOMIAL_DEF4 : thm
    val BINOMIAL_DEF5 : thm
    val BINOMIAL_DEF6 : thm
    val BINOMIAL_DEF7 : thm
    val BINOMIAL_FACT : thm
    val EXP_PASCAL_REAL : thm
    val EXP_PASCAL_REAL1 : thm
    val FINITE_RESTRICT : thm
    val FINITE_SUBSETS_RESTRICT_NEW : thm
    val FINITE_SUBSETS_RESTRICT_NEW1 : thm
    val FORALL_INSERT : thm
    val FTree_def : thm
    val FTree_ind : thm
    val INCLUSION_EXCLUSION_RESTRICTED : thm
    val INCLUSION_EXCLUSION_RESTRICTED_REAL : thm
    val INTER_BIGUNION : thm
    val IN_UNIONL : thm
    val K_out_N_Parallel_Struct : thm
    val K_out_N_Series_Struct : thm
    val NAND_FT_gate : thm
    val NAND_eq_big_inter_alt_form : thm
    val NOR_gate_thm : thm
    val OR_gate_lem1 : thm
    val OR_gate_lem2 : thm
    val OR_gate_lem3 : thm
    val OR_gate_lem4 : thm
    val OR_gate_lem5 : thm
    val OR_gate_lem6 : thm
    val OR_gate_lem7 : thm
    val OR_gate_thm : thm
    val OR_lem1 : thm
    val OR_lem2 : thm
    val OR_lem3 : thm
    val OR_lem4 : thm
    val OR_lem5 : thm
    val OR_lem6 : thm
    val OR_lem7 : thm
    val OR_lem8 : thm
    val PROB_COMPL_SUBSET : thm
    val PROB_INCLUSION_EXCLUSION : thm
    val PROB_INCLUSION_EXCLUSION_PRINCIPLE : thm
    val PROB_INCLUSION_EXCLUSION_list : thm
    val PROB_XOR_GATE : thm
    val PROB_XOR_GATE1 : thm
    val REAL_SUM_IMAGE_IMAGE1 : thm
    val SUBSET_INSERT_EXISTS_NEW : thm
    val SUM_0_SUM_1 : thm
    val SUM_0_SUM_2 : thm
    val SUM_1_SUM_2 : thm
    val SUM_C_EQ : thm
    val SUM_POS_LT : thm
    val SUM_SHIFT : thm
    val SUM_SHIFT_P : thm
    val SUM_SWITCH_SUM : thm
    val XOR_FT_gate_thm : thm
    val binomial_def : thm
    val binomial_def_compute : thm
    val binomial_ind : thm
    val comp_FT_gate_thm : thm
    val compl_event_nevent_empty : thm
    val datatype_gate : thm
    val disj_thm : thm
    val gate_11 : thm
    val gate_Axiom : thm
    val gate_case_cong : thm
    val gate_case_eq : thm
    val gate_distinct : thm
    val gate_induction : thm
    val gate_nchotomy : thm
    val has_size_clauses : thm
    val has_size_suc : thm
    val incl_excl_temp1 : thm
    val incl_excl_temp2 : thm
    val incl_excl_temp3 : thm
    val incl_excl_temp4 : thm
    val incl_excl_temp5 : thm
    val incl_excl_temp6 : thm
    val incl_excl_temp7 : thm
    val incl_excl_temp8 : thm
    val incl_excl_temp9 : thm
    val indep_compl_event_nevents : thm
    val inhibit_FT_gate_thm : thm
    val k_out_n_RBD : thm
    val k_out_n_RBD_v1 : thm
    val k_out_n_lemma1 : thm
    val k_out_n_lemma2 : thm
    val k_out_n_lemma3 : thm
    val k_out_n_lemma4 : thm
    val k_out_n_lemma5 : thm
    val k_out_n_lemma6 : thm
    val k_out_n_lemma6_new : thm
    val k_out_n_lemma6_new1 : thm
    val k_out_n_temp2 : thm
    val k_out_n_temp5 : thm
    val k_out_ntemp1 : thm
    val lemma_NEW : thm
    val majority_voting_FT_gate_thm : thm
    val mutual_indep_append_sym : thm
    val num_neq : thm
    val prob_compl_A_INTER_B : thm
    val prob_indep_big_inter2 : thm
    val simple_image_gen : thm
    val temp1 : thm
    val temp2 : thm
    val temp3 : thm
    val temp4 : thm
    val temp5 : thm
    val temp6 : thm
    val xor_gate_temp1 : thm
    val xor_gate_temp2 : thm
  
  val FT_deep_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [RBD] Parent theory of "FT_deep"
   
   [K_out_N_struct_def]  Definition
      
      ⊢ ∀p X k n.
            K_out_N_struct p X k n =
            BIGUNION
              (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                 {x | k ≤ x ∧ x < SUC n})
   
   [NOR_FT_gate_def]  Definition
      
      ⊢ ∀p L. NOR_FT_gate p L = p_space p DIFF FTree p (OR (gate_list L))
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [XOR_FT_gate_def]  Definition
      
      ⊢ ∀p A B.
            XOR_FT_gate p A B =
            FTree p (OR [AND [NOT A; B]; AND [A; NOT B]])
   
   [comp_FT_gate_def]  Definition
      
      ⊢ ∀p A B.
            comp_FT_gate p A B = FTree p (OR [AND [A; B]; NOT (OR [A; B])])
   
   [gate_TY_DEF]  Definition
      
      ⊢ ∃rep.
            TYPE_DEFINITION
              (λa0'.
                   ∀'gate' '@temp @ind_typeFT_deep0list' .
                       (∀a0'.
                            (∃a.
                                 (a0' =
                                  (λa.
                                       ind_type$CONSTR 0 ARB
                                         (ind_type$FCONS a
                                            (λn. ind_type$BOTTOM))) a) ∧
                                 '@temp @ind_typeFT_deep0list' a) ∨
                            (∃a.
                                 (a0' =
                                  (λa.
                                       ind_type$CONSTR (SUC 0) ARB
                                         (ind_type$FCONS a
                                            (λn. ind_type$BOTTOM))) a) ∧
                                 '@temp @ind_typeFT_deep0list' a) ∨
                            (∃a.
                                 (a0' =
                                  (λa.
                                       ind_type$CONSTR (SUC (SUC 0)) ARB
                                         (ind_type$FCONS a
                                            (λn. ind_type$BOTTOM))) a) ∧
                                 'gate' a) ∨
                            (∃a.
                                 a0' =
                                 (λa.
                                      ind_type$CONSTR (SUC (SUC (SUC 0))) a
                                        (λn. ind_type$BOTTOM)) a) ⇒
                            'gate' a0') ∧
                       (∀a1'.
                            (a1' =
                             ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                               (λn. ind_type$BOTTOM)) ∨
                            (∃a0 a1.
                                 (a1' =
                                  (λa0 a1.
                                       ind_type$CONSTR
                                         (SUC (SUC (SUC (SUC (SUC 0)))))
                                         ARB
                                         (ind_type$FCONS a0
                                            (ind_type$FCONS a1
                                               (λn. ind_type$BOTTOM)))) a0
                                    a1) ∧ 'gate' a0 ∧
                                 '@temp @ind_typeFT_deep0list' a1) ⇒
                            '@temp @ind_typeFT_deep0list' a1') ⇒
                       'gate' a0') rep
   
   [gate_case_def]  Definition
      
      ⊢ (∀a f f1 f2 f3. gate_CASE (AND a) f f1 f2 f3 = f a) ∧
        (∀a f f1 f2 f3. gate_CASE (OR a) f f1 f2 f3 = f1 a) ∧
        (∀a f f1 f2 f3. gate_CASE (NOT a) f f1 f2 f3 = f2 a) ∧
        ∀a f f1 f2 f3. gate_CASE (atomic a) f f1 f2 f3 = f3 a
   
   [gate_list_def]  Definition
      
      ⊢ (gate_list [] = []) ∧
        ∀h t. gate_list (h::t) = atomic h::gate_list t
   
   [gate_size_def]  Definition
      
      ⊢ (∀f a. gate_size f (AND a) = 1 + gate1_size f a) ∧
        (∀f a. gate_size f (OR a) = 1 + gate1_size f a) ∧
        (∀f a. gate_size f (NOT a) = 1 + gate_size f a) ∧
        (∀f a. gate_size f (atomic a) = 1) ∧ (∀f. gate1_size f [] = 0) ∧
        ∀f a0 a1.
            gate1_size f (a0::a1) = 1 + (gate_size f a0 + gate1_size f a1)
   
   [has_size_def]  Definition
      
      ⊢ ∀s n. has_size s n ⇔ FINITE s ∧ (CARD s = n)
   
   [inhibit_FT_gate_def]  Definition
      
      ⊢ ∀p A B C.
            inhibit_FT_gate p A B C = FTree p (AND [OR [A; B]; NOT C])
   
   [inter_list_def]  Definition
      
      ⊢ (∀p. inter_list p [] = p_space p) ∧
        ∀p h t. inter_list p (h::t) = h ∩ inter_list p t
   
   [majority_voting_FT_gate_def]  Definition
      
      ⊢ ∀p X k n.
            majority_voting_FT_gate p X k n =
            BIGUNION
              (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                 {x | k ≤ x ∧ x < SUC n})
   
   [sum_set_def]  Definition
      
      ⊢ ∀s f. sum_set s f = SIGMA f s
   
   [union_list_def]  Definition
      
      ⊢ (union_list [] = ∅) ∧ ∀h t. union_list (h::t) = h ∪ union_list t
   
   [AND_gate_append]  Theorem
      
      ⊢ ∀p h L1.
            prob_space p ∧ (∀x. MEM x (h ⧺ L1) ⇒ x ∈ events p) ⇒
            (FTree p (AND (gate_list h)) ∩ FTree p (AND (gate_list L1)) =
             FTree p (AND (gate_list (h ⧺ L1))))
   
   [AND_gate_eq_big_inter]  Theorem
      
      ⊢ ∀p L. FTree p (AND (gate_list L)) = big_inter p L
   
   [AND_gate_thm]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧
            mutual_indep p L ⇒
            (prob p (FTree p (AND (gate_list L))) =
             list_prod (list_prob p L))
   
   [BIGINTER_SET]  Theorem
      
      ⊢ ∀s p.
            FINITE s ∧ prob_space p ⇒
            (BIGINTER s ∩ p_space p = inter_list p (SET_TO_LIST s))
   
   [BIGUNION_EQ_UNION_LIST]  Theorem
      
      ⊢ ∀L. BIGUNION (set L) = union_list L
   
   [BINOMIAL_DEF1]  Theorem
      
      ⊢ ∀n. binomial n 0 = 1
   
   [BINOMIAL_DEF2]  Theorem
      
      ⊢ ∀n k. n < k ⇒ (binomial n k = 0)
   
   [BINOMIAL_DEF3]  Theorem
      
      ⊢ ∀n. binomial n n = 1
   
   [BINOMIAL_DEF4]  Theorem
      
      ⊢ ∀n k. binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k
   
   [BINOMIAL_DEF5]  Theorem
      
      ⊢ ∀n k. k ≤ n ⇒ binomial n k ≠ 0
   
   [BINOMIAL_DEF6]  Theorem
      
      ⊢ ∀n. binomial (SUC n) 1 = SUC n
   
   [BINOMIAL_DEF7]  Theorem
      
      ⊢ ∀n k. 0 ≤ binomial n k
   
   [BINOMIAL_FACT]  Theorem
      
      ⊢ ∀a b. binomial (a + b) b * (FACT a * FACT b) = FACT (a + b)
   
   [EXP_PASCAL_REAL]  Theorem
      
      ⊢ ∀a b n.
            (a + b) pow n =
            SIGMA (λx. &binomial n x * a pow (n − x) * b pow x)
              (count (SUC n))
   
   [EXP_PASCAL_REAL1]  Theorem
      
      ⊢ ∀a b n.
            (a + b) pow n =
            sum_set (count (SUC n))
              (λx. &binomial n x * a pow (n − x) * b pow x)
   
   [FINITE_RESTRICT]  Theorem
      
      ⊢ ∀s P. {x | x ∈ s ∧ P x} ⊆ s
   
   [FINITE_SUBSETS_RESTRICT_NEW]  Theorem
      
      ⊢ ∀s p. FINITE s ⇒ FINITE {t | t ⊆ s ∧ p t}
   
   [FINITE_SUBSETS_RESTRICT_NEW1]  Theorem
      
      ⊢ ∀s p. FINITE s ⇒ FINITE {t | t ⊆ s}
   
   [FORALL_INSERT]  Theorem
      
      ⊢ ∀P a s. (∀x. x ∈ a INSERT s ⇒ P x) ⇔ P a ∧ ∀x. x ∈ s ⇒ P x
   
   [FTree_def]  Theorem
      
      ⊢ (∀p a. FTree p (atomic a) = a) ∧
        (∀p a. FTree p (NOT a) = p_space p DIFF FTree p a) ∧
        (∀p. FTree p (AND []) = p_space p) ∧
        (∀xs x p. FTree p (AND (x::xs)) = FTree p x ∩ FTree p (AND xs)) ∧
        (∀p. FTree p (OR []) = ∅) ∧
        ∀xs x p. FTree p (OR (x::xs)) = FTree p x ∪ FTree p (OR xs)
   
   [FTree_ind]  Theorem
      
      ⊢ ∀P.
            (∀p a. P p (atomic a)) ∧ (∀p a. P p a ⇒ P p (NOT a)) ∧
            (∀p. P p (AND [])) ∧
            (∀p x xs. P p x ∧ P p (AND xs) ⇒ P p (AND (x::xs))) ∧
            (∀p. P p (OR [])) ∧
            (∀p x xs. P p x ∧ P p (OR xs) ⇒ P p (OR (x::xs))) ⇒
            ∀v v1. P v v1
   
   [INCLUSION_EXCLUSION_RESTRICTED]  Theorem
      
      ⊢ ∀P f A x.
            (∀s t. P s ∧ P t ∧ DISJOINT s t ⇒ (f (s ∪ t) = f s + f t)) ∧
            P ∅ ∧
            (∀s t. P s ∧ P t ⇒ P (s ∩ t) ∧ P (s ∪ t) ∧ P (s DIFF t)) ∧
            FINITE A ∧ (∀a. a ∈ A ⇒ P (x a)) ⇒
            (f (BIGUNION (IMAGE x A)) =
             sum_set {B | B ⊆ A ∧ B ≠ ∅}
               (λB. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))
   
   [INCLUSION_EXCLUSION_RESTRICTED_REAL]  Theorem
      
      ⊢ ∀P f A.
            (∀s t. P s ∧ P t ∧ DISJOINT s t ⇒ (f (s ∪ t) = f s + f t)) ∧
            P ∅ ∧
            (∀s t. P s ∧ P t ⇒ P (s ∩ t) ∧ P (s ∪ t) ∧ P (s DIFF t)) ∧
            FINITE A ∧ (∀a. a ∈ A ⇒ P a) ⇒
            (f (BIGUNION A) =
             sum_set {B | B ⊆ A ∧ B ≠ ∅}
               (λB. -1 pow (CARD B + 1) * f (BIGINTER B)))
   
   [INTER_BIGUNION]  Theorem
      
      ⊢ (∀s t. BIGUNION s ∩ t = BIGUNION {x ∩ t | x ∈ s}) ∧
        ∀s t. t ∩ BIGUNION s = BIGUNION {t ∩ x | x ∈ s}
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [K_out_N_Parallel_Struct]  Theorem
      
      ⊢ ∀p n X pr.
            prob_space p ∧ 1 < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (prob p
               (BIGUNION
                  (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                     {x | 1 ≤ x ∧ x < SUC n})) =
             1 − (1 − pr) pow n)
   
   [K_out_N_Series_Struct]  Theorem
      
      ⊢ ∀p n X pr.
            prob_space p ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (prob p
               (BIGUNION
                  (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                     {x | n ≤ x ∧ x < SUC n})) =
             pr pow n)
   
   [NAND_FT_gate]  Theorem
      
      ⊢ ∀p L1 L2.
            prob_space p ∧ 1 ≤ LENGTH (L1 ⧺ L2) ∧
            (∀x'. MEM x' (L1 ⧺ L2) ⇒ x' ∈ events p) ∧
            mutual_indep p (L1 ⧺ L2) ⇒
            (prob p (FTree p (AND (gate_list (compl_list p L1 ⧺ L2)))) =
             list_prod (list_prob p (compl_list p L1)) *
             list_prod (list_prob p L2))
   
   [NAND_eq_big_inter_alt_form]  Theorem
      
      ⊢ ∀p L1 L2.
            prob_space p ∧
            (∀x. MEM x (compl_list p L1 ⧺ L2) ⇒ x ∈ events p) ⇒
            (big_inter p (compl_list p L1) ∩ big_inter p L2 =
             FTree p (AND (gate_list (compl_list p L1 ⧺ L2))))
   
   [NOR_gate_thm]  Theorem
      
      ⊢ ∀p L.
            ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧ prob_space p ∧
            mutual_indep p L ⇒
            (prob p (NOR_FT_gate p L) =
             list_prod (one_minus_list (list_prob p L)))
   
   [OR_gate_lem1]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (one_minus_list (list_prob p L) = list_prob p (compl_list p L))
   
   [OR_gate_lem2]  Theorem
      
      ⊢ ∀L1 L2 Q. LENGTH (L1 ⧺ Q::L2) = LENGTH (Q::L1 ⧺ L2)
   
   [OR_gate_lem3]  Theorem
      
      ⊢ ∀A B C D. A ∩ B ∩ C ∩ D = B ∩ C ∩ D ∩ A
   
   [OR_gate_lem4]  Theorem
      
      ⊢ ∀p A C. A ∩ (p_space p DIFF C) = A ∩ p_space p DIFF A ∩ C
   
   [OR_gate_lem5]  Theorem
      
      ⊢ ∀m L x. MEM x (TAKE m L) ⇒ MEM x L
   
   [OR_gate_lem6]  Theorem
      
      ⊢ ∀A C. A ∩ (p_space p DIFF C) = A ∩ p_space p DIFF A ∩ C
   
   [OR_gate_lem7]  Theorem
      
      ⊢ ∀L1 p.
            prob_space p ∧ (∀x. MEM x L1 ⇒ x ∈ events p) ⇒
            (L1 = compl_list p (compl_list p L1))
   
   [OR_gate_thm]  Theorem
      
      ⊢ ∀p L.
            ¬NULL L ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ∧ prob_space p ∧
            mutual_indep p L ⇒
            (prob p (FTree p (OR (gate_list L))) =
             1 − list_prod (one_minus_list (list_prob p L)))
   
   [OR_lem1]  Theorem
      
      ⊢ ∀p s t.
            p_space p DIFF (s ∪ t) =
            (p_space p DIFF s) ∩ (p_space p DIFF t)
   
   [OR_lem2]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x L ⇒ x ∈ events p) ⇒
            (FTree p (AND (gate_list (compl_list p L))) =
             p_space p DIFF FTree p (OR (gate_list L)))
   
   [OR_lem3]  Theorem
      
      ⊢ ∀L p.
            (∀x. MEM x L ⇒ x ∈ events p) ∧ prob_space p ⇒
            FTree p (OR (gate_list L)) ∈ events p
   
   [OR_lem4]  Theorem
      
      ⊢ ∀p L.
            (∀x. MEM x L ⇒ x ∈ events p) ∧ prob_space p ∧
            FTree p (OR (gate_list L)) ∈ events p ⇒
            FTree p (OR (gate_list L)) ⊆ p_space p
   
   [OR_lem5]  Theorem
      
      ⊢ ∀p L. FTree p (AND (gate_list L)) = big_inter p L
   
   [OR_lem6]  Theorem
      
      ⊢ ∀p x L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (prob p (FTree p (OR (gate_list L))) =
             1 − prob p (FTree p (AND (gate_list (compl_list p L)))))
   
   [OR_lem7]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x'. MEM x' L ⇒ x' ∈ events p) ⇒
            (one_minus_list (list_prob p L) = list_prob p (compl_list p L))
   
   [OR_lem8]  Theorem
      
      ⊢ ∀L. one_minus_list L = MAP (λa. 1 − a) L
   
   [PROB_COMPL_SUBSET]  Theorem
      
      ⊢ ∀p s t.
            prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ t ⊆ s ⇒
            (prob p (s DIFF t) = prob p s − prob p t)
   
   [PROB_INCLUSION_EXCLUSION]  Theorem
      
      ⊢ ∀p s.
            prob_space p ∧ (∀a. a ∈ s ⇒ a ∈ events p) ∧ FINITE s ∧
            (∀k. k ∈ s ⇒ FINITE k) ⇒
            (prob p (BIGUNION s) =
             sum_set {t | t ⊆ s ∧ t ≠ ∅}
               (λt. -1 pow (CARD t + 1) * prob p (BIGINTER t)))
   
   [PROB_INCLUSION_EXCLUSION_PRINCIPLE]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x L ⇒ x ∈ events p) ⇒
            (prob p (union_list L) =
             sum_set {t | t ⊆ set L ∧ t ≠ ∅}
               (λt. -1 pow (CARD t + 1) * prob p (BIGINTER t)))
   
   [PROB_INCLUSION_EXCLUSION_list]  Theorem
      
      ⊢ ∀p L.
            prob_space p ∧ (∀x. MEM x L ⇒ x ∈ events p) ⇒
            (prob p (BIGUNION (set L)) =
             sum_set {t | t ⊆ set L ∧ t ≠ ∅}
               (λt. -1 pow (CARD t + 1) * prob p (BIGINTER t)))
   
   [PROB_XOR_GATE]  Theorem
      
      ⊢ ∀A B p.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ⇒
            (prob p (COMPL A ∩ B ∪ COMPL B ∩ A) =
             prob p A + prob p B − 2 * prob p (A ∩ B))
   
   [PROB_XOR_GATE1]  Theorem
      
      ⊢ ∀A B p.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ⇒
            (prob p ((p_space p DIFF A) ∩ B ∪ (p_space p DIFF B) ∩ A) =
             prob p A + prob p B − 2 * prob p (A ∩ B))
   
   [REAL_SUM_IMAGE_IMAGE1]  Theorem
      
      ⊢ ∀P f' f.
            FINITE P ∧ INJ f' P (IMAGE f' P) ⇒
            (SIGMA f (IMAGE f' P) = SIGMA (f ∘ f') P)
   
   [SUBSET_INSERT_EXISTS_NEW]  Theorem
      
      ⊢ ∀s x t. s ⊆ x INSERT t ⇔ s ⊆ t ∨ ∃u. u ⊆ t ∧ (s = x INSERT u)
   
   [SUM_0_SUM_1]  Theorem
      
      ⊢ ∀n f. sum (0,SUC n) f = f 0 + sum (1,n) f
   
   [SUM_0_SUM_2]  Theorem
      
      ⊢ ∀n f. sum (0,SUC (SUC n)) f = f 0 + f 1 + sum (2,n) f
   
   [SUM_1_SUM_2]  Theorem
      
      ⊢ ∀n f. sum (1,SUC n) f = f 1 + sum (2,n) f
   
   [SUM_C_EQ]  Theorem
      
      ⊢ ∀n m c. sum (n,SUC m) (λi. c) = &(m + 1) * c
   
   [SUM_POS_LT]  Theorem
      
      ⊢ ∀f. (∀n. 0 < f n) ⇒ ∀m n. 0 < sum (m,SUC n) f
   
   [SUM_SHIFT]  Theorem
      
      ⊢ ∀n f. sum (0,n) f = sum (1,n) (λi. f (i − 1))
   
   [SUM_SHIFT_P]  Theorem
      
      ⊢ ∀n p f. sum (p,n) (λi. f (i + 1)) = sum (p + 1,n) f
   
   [SUM_SWITCH_SUM]  Theorem
      
      ⊢ ∀f n1 n2 m1 m2.
            sum (n1,m1) (λi. sum (n2,m2) (λj. f i j)) =
            sum (n2,m2) (λj. sum (n1,m1) (λi. f i j))
   
   [XOR_FT_gate_thm]  Theorem
      
      ⊢ ∀a b p.
            prob_space p ∧ a ∈ events p ∧ b ∈ events p ∧ indep p a b ⇒
            (prob p (XOR_FT_gate p (atomic a) (atomic b)) =
             prob p a * (1 − prob p b) + prob p b * (1 − prob p a))
   
   [binomial_def]  Theorem
      
      ⊢ (∀n. binomial n 0 = 1) ∧ (∀k. binomial 0 (SUC k) = 0) ∧
        ∀n k. binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k
   
   [binomial_def_compute]  Theorem
      
      ⊢ (∀n. binomial n 0 = 1) ∧ (∀k. binomial 0 (NUMERAL (BIT1 k)) = 0) ∧
        (∀k. binomial 0 (NUMERAL (BIT2 k)) = 0) ∧
        (∀n k.
             binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT1 k)) =
             binomial (NUMERAL (BIT1 n) − 1) (NUMERAL (BIT1 k)) +
             binomial (NUMERAL (BIT1 n) − 1) (NUMERAL (BIT1 k) − 1)) ∧
        (∀n k.
             binomial (NUMERAL (BIT2 n)) (NUMERAL (BIT1 k)) =
             binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT1 k)) +
             binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT1 k) − 1)) ∧
        (∀n k.
             binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT2 k)) =
             binomial (NUMERAL (BIT1 n) − 1) (NUMERAL (BIT2 k)) +
             binomial (NUMERAL (BIT1 n) − 1) (NUMERAL (BIT1 k))) ∧
        ∀n k.
            binomial (NUMERAL (BIT2 n)) (NUMERAL (BIT2 k)) =
            binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT2 k)) +
            binomial (NUMERAL (BIT1 n)) (NUMERAL (BIT1 k))
   
   [binomial_ind]  Theorem
      
      ⊢ ∀P.
            (∀n. P n 0) ∧ (∀k. P 0 (SUC k)) ∧
            (∀n k. P n k ∧ P n (SUC k) ⇒ P (SUC n) (SUC k)) ⇒
            ∀v v1. P v v1
   
   [comp_FT_gate_thm]  Theorem
      
      ⊢ ∀p A B.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ∧ indep p A B ⇒
            (prob p (comp_FT_gate p (atomic A) (atomic B)) =
             1 − (prob p A + prob p B − 2 * (prob p A * prob p B)))
   
   [compl_event_nevent_empty]  Theorem
      
      ⊢ ∀p A. compl_pspace p A ∩ A = ∅
   
   [datatype_gate]  Theorem
      
      ⊢ DATATYPE (gate AND OR NOT atomic)
   
   [disj_thm]  Theorem
      
      ⊢ ∀X m n.
            m ≠ n ⇒
            DISJOINT (PREIMAGE X {Normal (&m)} ∩ p_space p)
              (PREIMAGE X {Normal (&n)} ∩ p_space p)
   
   [gate_11]  Theorem
      
      ⊢ (∀a a'. (AND a = AND a') ⇔ (a = a')) ∧
        (∀a a'. (OR a = OR a') ⇔ (a = a')) ∧
        (∀a a'. (NOT a = NOT a') ⇔ (a = a')) ∧
        ∀a a'. (atomic a = atomic a') ⇔ (a = a')
   
   [gate_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4 f5.
            ∃fn0 fn1.
                (∀a. fn0 (AND a) = f0 a (fn1 a)) ∧
                (∀a. fn0 (OR a) = f1 a (fn1 a)) ∧
                (∀a. fn0 (NOT a) = f2 a (fn0 a)) ∧
                (∀a. fn0 (atomic a) = f3 a) ∧ (fn1 [] = f4) ∧
                ∀a0 a1. fn1 (a0::a1) = f5 a0 a1 (fn0 a0) (fn1 a1)
   
   [gate_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 f2 f3.
            (M = M') ∧ (∀a. (M' = AND a) ⇒ (f a = f' a)) ∧
            (∀a. (M' = OR a) ⇒ (f1 a = f1' a)) ∧
            (∀a. (M' = NOT a) ⇒ (f2 a = f2' a)) ∧
            (∀a. (M' = atomic a) ⇒ (f3 a = f3' a)) ⇒
            (gate_CASE M f f1 f2 f3 = gate_CASE M' f' f1' f2' f3')
   
   [gate_case_eq]  Theorem
      
      ⊢ (gate_CASE x f f1 f2 f3 = v) ⇔
        (∃l. (x = AND l) ∧ (f l = v)) ∨ (∃l. (x = OR l) ∧ (f1 l = v)) ∨
        (∃g. (x = NOT g) ∧ (f2 g = v)) ∨ ∃f'. (x = atomic f') ∧ (f3 f' = v)
   
   [gate_distinct]  Theorem
      
      ⊢ (∀a' a. AND a ≠ OR a') ∧ (∀a' a. AND a ≠ NOT a') ∧
        (∀a' a. AND a ≠ atomic a') ∧ (∀a' a. OR a ≠ NOT a') ∧
        (∀a' a. OR a ≠ atomic a') ∧ ∀a' a. NOT a ≠ atomic a'
   
   [gate_induction]  Theorem
      
      ⊢ ∀P0 P1.
            (∀l. P1 l ⇒ P0 (AND l)) ∧ (∀l. P1 l ⇒ P0 (OR l)) ∧
            (∀g. P0 g ⇒ P0 (NOT g)) ∧ (∀f. P0 (atomic f)) ∧ P1 [] ∧
            (∀g l. P0 g ∧ P1 l ⇒ P1 (g::l)) ⇒
            (∀g. P0 g) ∧ ∀l. P1 l
   
   [gate_nchotomy]  Theorem
      
      ⊢ ∀gg.
            (∃l. gg = AND l) ∨ (∃l. gg = OR l) ∨ (∃g. gg = NOT g) ∨
            ∃f. gg = atomic f
   
   [has_size_clauses]  Theorem
      
      ⊢ (has_size s 0 ⇔ (s = ∅)) ∧
        (has_size s (SUC n) ⇔ ∃a t. has_size t n ∧ a ∉ t ∧ (s = a INSERT t))
   
   [has_size_suc]  Theorem
      
      ⊢ ∀s n.
            has_size s (SUC n) ⇔
            s ≠ ∅ ∧ ∀a. a ∈ s ⇒ has_size (s DELETE a) n
   
   [incl_excl_temp1]  Theorem
      
      ⊢ ∀fa fas s s'. (fa + s − fas = s + s') ⇔ (fa − fas = s')
   
   [incl_excl_temp2]  Theorem
      
      ⊢ ∀a b x. (x − a = x + b) ⇔ (b = -a)
   
   [incl_excl_temp3]  Theorem
      
      ⊢ ∀f s. BIGINTER (IMAGE f s) = {y | ∀x. x ∈ s ⇒ y ∈ f x}
   
   [incl_excl_temp4]  Theorem
      
      ⊢ ∀P e. {s | P s ∧ s ≠ e} = {s | P s} DELETE e
   
   [incl_excl_temp5]  Theorem
      
      ⊢ ∀x s. x ∈ s ⇒ (x INSERT s = s)
   
   [incl_excl_temp6]  Theorem
      
      ⊢ ∀s. ∅ ∈ {B | B ⊆ s}
   
   [incl_excl_temp7]  Theorem
      
      ⊢ ∀a b c. (a = b − c) ⇔ (b = c + a)
   
   [incl_excl_temp8]  Theorem
      
      ⊢ ∀f e s.
            FINITE s ⇒
            (sum_set (s DELETE e) f = sum_set (e INSERT s) f − f e)
   
   [incl_excl_temp9]  Theorem
      
      ⊢ ∀f e s.
            e ∈ s ∧ FINITE s ⇒ (sum_set (s DELETE e) f = sum_set s f − f e)
   
   [indep_compl_event_nevents]  Theorem
      
      ⊢ ∀p A B C.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ∧ C ∈ events p ∧
            mutual_indep p [A; B; C] ⇒
            (prob p (compl_pspace p C ∩ A ∩ B) =
             prob p A * prob p B − prob p A * prob p B * prob p C)
   
   [inhibit_FT_gate_thm]  Theorem
      
      ⊢ ∀p A B C.
            prob_space p ∧ A ∈ events p ∧ B ∈ events p ∧ C ∈ events p ∧
            mutual_indep p [A; B; C] ⇒
            (prob p (inhibit_FT_gate p (atomic A) (atomic B) (atomic C)) =
             (1 − (1 − prob p A) * (1 − prob p B)) * (1 − prob p C))
   
   [k_out_n_RBD]  Theorem
      
      ⊢ ∀p n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial (SUC n) x * pr pow x * (1 − pr) pow (SUC n − x)) ⇒
            (prob p
               (BIGUNION
                  (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                     {x | k ≤ x ∧ x < SUC n})) =
             sum (k,SUC n − k)
               (λx.
                    &binomial (SUC n) x * pr pow x *
                    (1 − pr) pow (SUC n − x)))
   
   [k_out_n_RBD_v1]  Theorem
      
      ⊢ ∀p n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (prob p (K_out_N_struct p X k n) =
             sum (k,SUC n − k)
               (λx. &binomial n x * pr pow x * (1 − pr) pow (n − x)))
   
   [k_out_n_lemma1]  Theorem
      
      ⊢ ∀p s n k.
            prob_space p ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count n -> events p) ⇒
            IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) (count n) ⊆
            events p
   
   [k_out_n_lemma2]  Theorem
      
      ⊢ ∀k n. {x | k ≤ x ∧ x < n} = {x | k ≤ x} ∩ {x | x < n}
   
   [k_out_n_lemma3]  Theorem
      
      ⊢ ∀k n. FINITE {x | k ≤ x ∧ x < n}
   
   [k_out_n_lemma4]  Theorem
      
      ⊢ ∀k n. k < n ⇒ ({x | k ≤ x ∧ x < n} ∪ count k = count n)
   
   [k_out_n_lemma5]  Theorem
      
      ⊢ ∀p s n k X.
            prob_space p ∧ k < n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count n -> events p) ∧
            (s =
             BIGUNION
               (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                  {x | k ≤ x ∧ x < n})) ⇒
            (sum (k,n − k)
               (prob p ∘ (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)) =
             prob p s)
   
   [k_out_n_lemma6]  Theorem
      
      ⊢ ∀p s n k X pr.
            prob_space p ∧ k < n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count n -> events p) ∧
            (s =
             BIGUNION
               (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                  {x | k ≤ x ∧ x < n})) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (sum (k,n − k)
               (λx. &binomial n x * pr pow x * (1 − pr) pow (n − x)) =
             prob p s)
   
   [k_out_n_lemma6_new]  Theorem
      
      ⊢ ∀p s n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (s =
             BIGUNION
               (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                  {x | k ≤ x ∧ x < SUC n})) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial (SUC n) x * pr pow x * (1 − pr) pow (SUC n − x)) ⇒
            (sum (k,SUC n − k)
               (λx.
                    &binomial (SUC n) x * pr pow x *
                    (1 − pr) pow (SUC n − x)) =
             prob p s)
   
   [k_out_n_lemma6_new1]  Theorem
      
      ⊢ ∀p s n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (s =
             BIGUNION
               (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                  {x | k ≤ x ∧ x < SUC n})) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial n x * pr pow x * (1 − pr) pow (n − x)) ⇒
            (sum (k,SUC n − k)
               (λx. &binomial n x * pr pow x * (1 − pr) pow (n − x)) =
             prob p s)
   
   [k_out_n_temp2]  Theorem
      
      ⊢ ∀k n. {x | x < n ∧ k ≤ x} = {x | x < n} ∩ {x | k ≤ x}
   
   [k_out_n_temp5]  Theorem
      
      ⊢ ∀p n k X.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (s =
             BIGUNION
               (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
                  {x | k ≤ x ∧ x < SUC n})) ⇒
            (sum (k,SUC n − k)
               (prob p ∘ (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)) =
             prob p s)
   
   [k_out_ntemp1]  Theorem
      
      ⊢ ∀k n. n INSERT {x | k ≤ x ∧ x < n} = n INSERT {x | x < n ∧ k ≤ x}
   
   [lemma_NEW]  Theorem
      
      ⊢ {t | t ⊆ a INSERT s ∧ P t} =
        {t | t ⊆ s ∧ P t} ∪ {a INSERT t | t | t ⊆ s ∧ P (a INSERT t)}
   
   [majority_voting_FT_gate_thm]  Theorem
      
      ⊢ ∀p n k X pr.
            prob_space p ∧ k < SUC n ∧
            (λx. PREIMAGE X {Normal (&x)} ∩ p_space p) ∈
            (count (SUC n) -> events p) ∧
            (∀x.
                 distribution p X {Normal (&x)} =
                 &binomial (SUC n) x * pr pow x * (1 − pr) pow (SUC n − x)) ⇒
            (prob p (majority_voting_FT_gate p X k n) =
             sum (k,SUC n − k)
               (λx.
                    &binomial (SUC n) x * pr pow x *
                    (1 − pr) pow (SUC n − x)))
   
   [mutual_indep_append_sym]  Theorem
      
      ⊢ ∀L1 L p. mutual_indep p (L1 ⧺ L) ⇒ mutual_indep p (L ⧺ L1)
   
   [num_neq]  Theorem
      
      ⊢ ∀a b. a ≠ b ⇔ a < b ∨ b < a
   
   [prob_compl_A_INTER_B]  Theorem
      
      ⊢ ∀a b p.
            prob_space p ∧ a ∈ events p ∧ b ∈ events p ⇒
            (prob p (compl_pspace p a ∩ b) = prob p b − prob p (a ∩ b))
   
   [prob_indep_big_inter2]  Theorem
      
      ⊢ ∀L1 L2 n p.
            prob_space p ∧ mutual_indep p (L1 ⧺ L2) ∧
            (∀x. MEM x (L1 ⧺ L2) ⇒ x ∈ events p) ∧ 1 ≤ LENGTH (L1 ⧺ L2) ⇒
            (prob p
               (big_inter p (TAKE n (compl_list p L1)) ∩ big_inter p L2) =
             list_prod (list_prob p (TAKE n (compl_list p L1))) *
             list_prod (list_prob p L2))
   
   [simple_image_gen]  Theorem
      
      ⊢ ∀f P. {f s | P s} = IMAGE f {s | P s}
   
   [temp1]  Theorem
      
      ⊢ ∀P. (∀s n. has_size s n ⇒ P s) ⇒ ∀s. FINITE s ⇒ P s
   
   [temp2]  Theorem
      
      ⊢ (∀P f A x n.
             (∀s t. P s ∧ P t ∧ DISJOINT s t ⇒ (f (s ∪ t) = f s + f t)) ∧
             P ∅ ∧
             (∀s t. P s ∧ P t ⇒ P (s ∩ t) ∧ P (s ∪ t) ∧ P (s DIFF t)) ∧
             has_size A n ∧ (∀a. a ∈ A ⇒ P (x a)) ⇒
             (f (BIGUNION (IMAGE x A)) =
              sum_set {B | B ⊆ A ∧ B ≠ ∅}
                (λB. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))) ⇒
        ∀P f A x.
            (∀s t. P s ∧ P t ∧ DISJOINT s t ⇒ (f (s ∪ t) = f s + f t)) ∧
            P ∅ ∧
            (∀s t. P s ∧ P t ⇒ P (s ∩ t) ∧ P (s ∪ t) ∧ P (s DIFF t)) ∧
            FINITE A ∧ (∀a. a ∈ A ⇒ P (x a)) ⇒
            (f (BIGUNION (IMAGE x A)) =
             sum_set {B | B ⊆ A ∧ B ≠ ∅}
               (λB. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))
   
   [temp3]  Theorem
      
      ⊢ ∀P. (∀n. (∀m. m < n ⇒ P m) ⇒ P n) ⇒ ∀n. P n
   
   [temp4]  Theorem
      
      ⊢ ∀A. has_size s 0 ⇔ (s = ∅)
   
   [temp5]  Theorem
      
      ⊢ ∀s t. s ∪ (t DIFF s) = s ∪ t
   
   [temp6]  Theorem
      
      ⊢ ∀s t. s ∩ t ∪ (t DIFF s) = t
   
   [xor_gate_temp1]  Theorem
      
      ⊢ ∀A B. COMPL A ∩ B ∪ COMPL B ∩ A = A DIFF B ∪ (B DIFF A)
   
   [xor_gate_temp2]  Theorem
      
      ⊢ ∀A B. A DIFF B = A DIFF A ∩ B
   
   
*)
end
