signature railwayTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val UNIONL_def : thm
    val in_events_def : thm
    val one_minus_exp_func_list_def : thm
    val three_dim_fail_event_list_def : thm
    val two_dim_fail_event_list_def : thm
  
  (*  Theorems  *)
    val IN_UNIONL : thm
    val fail_prob_railway_FT : thm
    val railway_FT_equi_RBD : thm
  
  val railway_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [smart_grid] Parent theory of "railway"
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [in_events_def]  Definition
      
      ⊢ ∀p L. in_events p L ⇔ ∀z. MEM z L ⇒ z ∈ events p
   
   [one_minus_exp_func_list_def]  Definition
      
      ⊢ ∀C t. one_minus_exp_func_list C t = MAP (λa. 1 − exp (-(a * t))) C
   
   [three_dim_fail_event_list_def]  Definition
      
      ⊢ ∀p L t.
            three_dim_fail_event_list p L t =
            MAP (λa. two_dim_fail_event_list p a t) L
   
   [two_dim_fail_event_list_def]  Definition
      
      ⊢ ∀p L t.
            two_dim_fail_event_list p L t =
            MAP (λa. fail_event_list p a t) L
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [fail_prob_railway_FT]  Theorem
      
      ⊢ 0 ≤ t ∧ prob_space p ∧
        mutual_indep p
          (FLAT
             (FLAT
                (FLAT
                   [three_dim_fail_event_list p
                      [[[x3; x4; x5; x6; x7; x8; x1; x2]];
                       [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t]))) ∧
        (∀x'.
             MEM x'
               (FLAT
                  (FLAT
                     (FLAT
                        [three_dim_fail_event_list p
                           [[[x3; x4; x5; x6; x7; x8; x1; x2]];
                            [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]]
                           t]))) ⇒
             x' ∈ events p) ∧
        exp_dist_list p
          [x1; x2; x3; x4; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14;
           x15; x16]
          [c1; c2; c3; c4; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14;
           c15; c16] ⇒
        (prob p
           (FTree p
              (OR
                 [OR (gate_list (fail_event_list p [x3; x4] t));
                  OR (gate_list (fail_event_list p [x5; x6] t));
                  AND
                    [OR (gate_list (fail_event_list p [x9; x10] t));
                     OR (gate_list (fail_event_list p [x13; x14] t));
                     OR (gate_list (fail_event_list p [x15; x16] t));
                     OR (gate_list (fail_event_list p [x11; x12] t))];
                  OR (gate_list (fail_event_list p [x7; x8] t));
                  OR (gate_list (fail_event_list p [x1; x2] t))])) =
         1 −
         exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
         exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) *
         exp (-(c1 * t)) * exp (-(c2 * t)) *
         (1 −
          (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
          (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
          (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
          (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))
   
   [railway_FT_equi_RBD]  Theorem
      
      ⊢ prob_space p ∧
        in_events p
          (fail_event_list p
             [x1; x2; x3; x4; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13;
              x14; x15; x16] t) ⇒
        (FTree p
           (OR
              [OR (gate_list (fail_event_list p [x3; x4] t));
               OR (gate_list (fail_event_list p [x5; x6] t));
               AND
                 [OR (gate_list (fail_event_list p [x9; x10] t));
                  OR (gate_list (fail_event_list p [x13; x14] t));
                  OR (gate_list (fail_event_list p [x15; x16] t));
                  OR (gate_list (fail_event_list p [x11; x12] t))];
               OR (gate_list (fail_event_list p [x7; x8] t));
               OR (gate_list (fail_event_list p [x1; x2] t))]) =
         rbd_struct p
           ((parallel of series of (λa. parallel (rbd_list a)))
              (three_dim_fail_event_list p
                 [[[x3; x4; x5; x6; x7; x8; x1; x2]];
                  [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t)))
   
   
*)
end
