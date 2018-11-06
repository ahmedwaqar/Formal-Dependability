signature ASN_gatewayTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ASN_gateway_FT_def : thm
    val A_FT_def : thm
    val B1_FT_def : thm
    val B2_FT_def : thm
    val Internal_FT_def : thm
    val RT_FT_def : thm
    val UNIONL_def : thm
    val exp_dist_def : thm
    val exp_func_def : thm
    val fail_event_list_def : thm
    val list_exp_def : thm
    val list_fail_event_list_def : thm
    val list_sum_def : thm
    val one_minus_exp_def : thm
    val one_minus_exp_prod_def : thm
  
  (*  Theorems  *)
    val ASN_FT_eq_parallel_series_RBD : thm
    val ASN_gateway_lem5 : thm
    val ASN_gateway_lem6 : thm
    val ASN_gateway_lemma1 : thm
    val ASN_gateway_lemma2 : thm
    val ASN_gateway_thm : thm
    val A_FT_lemma1 : thm
    val B1_FT_lemma2 : thm
    val B1_FT_lemma2_new : thm
    val B1_FT_lemma3 : thm
    val B1_FT_lemma3_new : thm
    val B1_FT_lemma4 : thm
    val B1_FT_lemma5 : thm
    val B1_FT_lemma6 : thm
    val IN_UNIONL : thm
    val Internal_FT_lemma1 : thm
    val Internal_FT_lemma2 : thm
    val RT_FT_lemma2 : thm
  
  val ASN_gateway_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [FT_deep] Parent theory of "ASN_gateway"
   
   [VDC] Parent theory of "ASN_gateway"
   
   [ASN_gateway_FT_def]  Definition
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time ED EQ1 EN1 EN2 EN3 EN4 human.
            ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7
              E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6
              C7 C8 notshw AL SL PD Others time ED EQ1 EN1 EN2 EN3 EN4
              human =
            FTree p
              (OR
                 [AND (gate_list (fail_event_list p [ED; EQ1] t));
                  OR
                    [AND
                       (gate_list
                          (fail_event_list p [EN1; EN2; EN3; EN4] t));
                     atomic (fail_event p human t)];
                  Internal_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6
                    E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20
                    E21 C5 C6 C7 C8 notshw AL SL PD Others time])
   
   [A_FT_def]  Definition
      
      ⊢ ∀p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14
            E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8.
            A_FT p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
              E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 =
            OR
              [B1_FT p t D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21;
               B2_FT p t D7 D10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21;
               AND
                 [OR (gate_list (fail_event_list p [C5; C6; C7] t));
                  atomic (fail_event p C8 t)]]
   
   [B1_FT_def]  Definition
      
      ⊢ ∀p t D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21.
            B1_FT p t D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 =
            OR
              [OR
                 [atomic (fail_event p D1 t);
                  AND
                    [OR (gate_list (fail_event_list p [E1; E2] t));
                     atomic (fail_event p E21 t)];
                  OR (gate_list (fail_event_list p [E3; E4; E5] t))];
               OR
                 [atomic (fail_event p D4 t);
                  AND
                    [OR (gate_list (fail_event_list p [E6; E7] t));
                     atomic (fail_event p E21 t)];
                  OR (gate_list (fail_event_list p [E8; E9; E10] t))]]
   
   [B2_FT_def]  Definition
      
      ⊢ ∀p t D7 D10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21.
            B2_FT p t D7 D10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 =
            OR
              [OR
                 [atomic (fail_event p D7 t);
                  AND
                    [OR (gate_list (fail_event_list p [E11; E12] t));
                     atomic (fail_event p E21 t)];
                  OR (gate_list (fail_event_list p [E13; E14; E15] t))];
               OR
                 [atomic (fail_event p D10 t);
                  AND
                    [OR (gate_list (fail_event_list p [E16; E17] t));
                     atomic (fail_event p E21 t)];
                  OR (gate_list (fail_event_list p [E18; E19; E20] t))]]
   
   [Internal_FT_def]  Definition
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time.
            Internal_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8
              E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7
              C8 notshw AL SL PD Others time =
            OR
              [AND
                 [OR (gate_list (fail_event_list p [FD; AP] t));
                  atomic (fail_event p FF1 t)];
               OR
                 [A_FT p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
                    E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8;
                  atomic (fail_event p notshw t);
                  RT_FT p t AL SL PD Others time]]
   
   [RT_FT_def]  Definition
      
      ⊢ ∀p t AL SL PD Others time.
            RT_FT p t AL SL PD Others time =
            AND
              [OR (gate_list (fail_event_list p [AL; SL; PD; Others] t));
               atomic (fail_event p time t)]
   
   [UNIONL_def]  Definition
      
      ⊢ (UNIONL [] = ∅) ∧ ∀s ss. UNIONL (s::ss) = s ∪ UNIONL ss
   
   [exp_dist_def]  Definition
      
      ⊢ ∀p X l.
            exp_dist p X l ⇔
            ∀x. CDF p X x = if 0 ≤ x then 1 − exp (-l * x) else 0
   
   [exp_func_def]  Definition
      
      ⊢ ∀x c. exp_func x c = exp (-(c * x))
   
   [fail_event_list_def]  Definition
      
      ⊢ ∀p L t. fail_event_list p L t = MAP (λa. fail_event p a t) L
   
   [list_exp_def]  Definition
      
      ⊢ (∀p L. list_exp p [] L ⇔ T) ∧
        ∀p h t L.
            list_exp p (h::t) L ⇔ exp_dist p (HD L) h ∧ list_exp p t (TL L)
   
   [list_fail_event_list_def]  Definition
      
      ⊢ ∀p L t.
            list_fail_event_list p L t = MAP (λa. fail_event_list p a t) L
   
   [list_sum_def]  Definition
      
      ⊢ (list_sum [] = 0) ∧ ∀h t. list_sum (h::t) = h + list_sum t
   
   [one_minus_exp_def]  Definition
      
      ⊢ ∀t C. one_minus_exp t C = MAP (λc. 1 − exp (-(t * c))) C
   
   [one_minus_exp_prod_def]  Definition
      
      ⊢ ∀t C.
            one_minus_exp_prod t C =
            MAP (λa. 1 − list_prod (one_minus_list (exp_func_list a t))) C
   
   [ASN_FT_eq_parallel_series_RBD]  Theorem
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time ED EQ1 EN1 EN2 EN3 EN4 human.
            ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7
              E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6
              C7 C8 notshw AL SL PD Others time ED EQ1 EN1 EN2 EN3 EN4
              human =
            rbd_struct p
              ((parallel of (λa. series (rbd_list a)))
                 (list_fail_event_list p
                    [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]; [FD; FF1];
                     [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3];
                     [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10];
                     [D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14];
                     [E15]; [E16; E21]; [E17; E21]; [E18]; [E19]; [E20];
                     [C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                     [SL; time]; [PD; time]; [Others; time]] t))
   
   [ASN_gateway_lem5]  Theorem
      
      ⊢ ∀p t C5 C6 C7 C8 notshw AL time SL PD Others.
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t))) =
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p [[C5; C8]; [C6; C8]; [C7; C8]]
                       t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[notshw]; [AL; time]; [SL; time]; [PD; time];
                        [Others; time]] t)))
   
   [ASN_gateway_lem6]  Theorem
      
      ⊢ ∀p t C5 C6 C7 C8 C_C5 C_C6 C_C7 C_C8.
            0 ≤ t ∧ prob_space p ∧
            list_exp p (FLAT [[C_C5; C_C8]; [C_C6; C_C8]; [C_C7; C_C8]])
              (FLAT [[C5; C8]; [C6; C8]; [C7; C8]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p [[C5; C8]; [C6; C8]; [C7; C8]]
                        t))) =
             list_prod
               (one_minus_exp_prod t
                  [[C_C5; C_C8]; [C_C6; C_C8]; [C_C7; C_C8]]))
   
   [ASN_gateway_lemma1]  Theorem
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time ED EQ1 EN1 EN2 EN3 EN4 human.
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human];
                        [FD; FF1]; [FF1; AP]; [D1]; [D4]; [E1; E21];
                        [E2; E21]; [E3]; [E4]; [E5]; [E6; E21]; [E7; E21];
                        [E8]; [E9]; [E10]; [D7]; [D10]; [E11; E21];
                        [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
                        [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
                        [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t))) =
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]] t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[FD; FF1]; [FF1; AP]; [D1]; [D4]; [E1; E21];
                        [E2; E21]; [E3]; [E4]; [E5]; [E6; E21]; [E7; E21];
                        [E8]; [E9]; [E10]; [D7]; [D10]; [E11; E21];
                        [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
                        [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
                        [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t)))
   
   [ASN_gateway_lemma2]  Theorem
      
      ⊢ ∀p t ED EQ1 EN1 EN2 EN3 EN4 human C_ED C_EQ1 C_EN1 C_EN2 C_EN3
            C_EN4 C_human.
            0 ≤ t ∧ prob_space p ∧
            list_exp p
              (FLAT
                 [[C_ED; C_EQ1]; [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]])
              (FLAT [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p
                        [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]] t))) =
             list_prod
               (one_minus_exp_prod t
                  [[C_ED; C_EQ1]; [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]]))
   
   [ASN_gateway_thm]  Theorem
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time ED EQ1 EN1 EN2 EN3 EN4 human C_ED C_EQ1 C_EN1 C_EN2
            C_EN3 C_EN4 C_human C_FD C_AP C_FF1 C_notshw C_AL C_SL C_PD
            C_Others C_time C_C5 C_C6 C_C7 C_C8 C_E1 C_E2 C_E6 C_E7 C_D1
            C_D4 C_E3 C_E4 C_E5 C_E8 C_E9 C_E10 C_E11 C_E12 C_E16 C_E17
            C_D7 C_D10 C_E13 C_E14 C_E15 C_E18 C_E19 C_E20 C_E21.
            0 ≤ t ∧ prob_space p ∧
            (∀x'.
                 MEM x'
                   (FLAT
                      (list_fail_event_list p
                         [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human];
                          [FD; FF1]; [FF1; AP]; [D1]; [D4]; [E1; E21];
                          [E2; E21]; [E3]; [E4]; [E5]; [E6; E21];
                          [E7; E21]; [E8]; [E9]; [E10]; [D7]; [D10];
                          [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
                          [E16; E21]; [E17; E21]; [E18]; [E19]; [E20];
                          [C5; C8]; [C6; C8]; [C7; C8]; [notshw];
                          [AL; time]; [SL; time]; [PD; time];
                          [Others; time]] t)) ⇒
                 x' ∈ events p) ∧
            mutual_indep p
              (FLAT
                 (list_fail_event_list p
                    [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]; [FD; FF1];
                     [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3];
                     [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10];
                     [D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14];
                     [E15]; [E16; E21]; [E17; E21]; [E18]; [E19]; [E20];
                     [C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                     [SL; time]; [PD; time]; [Others; time]] t)) ∧
            list_exp p
              (FLAT
                 [[C_C5; C_C6; C_C7; C_C8]; [C_D1]; [C_D4]; [C_E1; C_E21];
                  [C_E2; C_E21]; [C_E3]; [C_E4]; [C_E5]; [C_E6; C_E21];
                  [C_E7; C_E21]; [C_E8]; [C_E9]; [C_E10]; [C_D7]; [C_D10];
                  [C_E11; C_E21]; [C_E12; C_E21]; [C_E13]; [C_E14];
                  [C_E15]; [C_E16; C_E21]; [C_E17; C_E21]; [C_E18];
                  [C_E19]; [C_E20]; [C_AL; C_time]; [C_SL; C_time];
                  [C_PD; C_time]; [C_Others; C_time]; [C_FD; C_FF1];
                  [C_AP; C_FF1]; [C_notshw]; [C_ED; C_EQ1];
                  [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]])
              (FLAT
                 [[C5; C6; C7; C8]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3];
                  [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10];
                  [D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
                  [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]; [AL; time];
                  [SL; time]; [PD; time]; [Others; time]; [FD; FF1];
                  [AP; FF1]; [notshw]; [ED; EQ1]; [EN1; EN2; EN3; EN4];
                  [human]]) ⇒
            (prob p
               (ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6
                  E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21
                  C5 C6 C7 C8 notshw AL SL PD Others time ED EQ1 EN1 EN2
                  EN3 EN4 human) =
             1 −
             list_prod
               (one_minus_exp_prod t
                  [[C_ED; C_EQ1]; [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]]) *
             (list_prod
                (one_minus_exp_prod t [[C_FD; C_FF1]; [C_AP; C_FF1]]) *
              (exp
                 (-(t *
                   list_sum
                     [C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10])) *
               list_prod
                 (one_minus_exp_prod t
                    [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21];
                     [C_E7; C_E21]]) *
               (exp
                  (-(t *
                    list_sum
                      [C_D7; C_D10; C_E13; C_E14; C_E15; C_E18; C_E19;
                       C_E20])) *
                list_prod
                  (one_minus_exp_prod t
                     [[C_E11; C_E21]; [C_E12; C_E21]; [C_E16; C_E21];
                      [C_E17; C_E21]])) *
               list_prod
                 (one_minus_exp_prod t
                    [[C_C5; C_C8]; [C_C6; C_C8]; [C_C7; C_C8]])) *
              exp (-(C_notshw * t)) *
              list_prod
                (one_minus_exp_prod t
                   [[C_AL; C_time]; [C_SL; C_time]; [C_PD; C_time];
                    [C_Others; C_time]])))
   
   [A_FT_lemma1]  Theorem
      
      ⊢ ∀p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14
            E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL time SL PD
            Others.
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
                        [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7];
                        [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
                        [E16; E21]; [E17; E21]; [E18]; [E19]; [E20];
                        [C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t))) =
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
                        [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14];
                        [E15]; [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]]
                       t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t)))
   
   [B1_FT_lemma2]  Theorem
      
      ⊢ ∀a b c d e f g h i j k l.
            1 − a * b * c * d * e * f * g * h * i * j * k * l =
            1 − a * b * e * f * g * j * k * l * c * d * h * i
   
   [B1_FT_lemma2_new]  Theorem
      
      ⊢ ∀a b c d e f g h i j k l.
            a * b * c * d * e * f * g * h * i * j * k * l =
            a * b * e * f * g * j * k * l * c * d * h * i
   
   [B1_FT_lemma3]  Theorem
      
      ⊢ ∀p D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 t.
            1 −
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
                        [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t))) =
            1 −
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E3]; [E4]; [E5]; [E8]; [E9]; [E10]] t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]] t)))
   
   [B1_FT_lemma3_new]  Theorem
      
      ⊢ ∀p D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 t.
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
                        [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t))) =
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E3]; [E4]; [E5]; [E8]; [E9]; [E10]] t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]] t)))
   
   [B1_FT_lemma4]  Theorem
      
      ⊢ ∀p t D1 D4 E1 E3 E4 E5 E8 E9 E10 C_D1 C_D4 C_E3 C_E4 C_E5 C_E8 C_E9
            C_E10.
            0 ≤ t ∧ prob_space p ∧
            list_exp p [C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10]
              (FLAT [[D1]; [D4]; [E3]; [E4]; [E5]; [E8]; [E9]; [E10]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p
                        [[D1]; [D4]; [E3]; [E4]; [E5]; [E8]; [E9]; [E10]] t))) =
             exp
               (-(t *
                 list_sum [C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10])))
   
   [B1_FT_lemma5]  Theorem
      
      ⊢ ∀a b c d e f g h i j k l.
            a * b * c * d * e * f * g * h * i * j * k * l =
            a * b * e * f * g * j * k * l * c * d * h * i
   
   [B1_FT_lemma6]  Theorem
      
      ⊢ ∀p t E1 E2 E6 E7 E21 C_E1 C_E2 C_E6 C_E7 C_E21.
            0 ≤ t ∧ prob_space p ∧
            list_exp p
              (FLAT
                 [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21];
                  [C_E7; C_E21]])
              (FLAT [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p
                        [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]] t))) =
             list_prod
               (one_minus_exp_prod t
                  [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21];
                   [C_E7; C_E21]]))
   
   [IN_UNIONL]  Theorem
      
      ⊢ ∀l v. v ∈ UNIONL l ⇔ ∃s. MEM s l ∧ v ∈ s
   
   [Internal_FT_lemma1]  Theorem
      
      ⊢ ∀p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
            E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
            Others time.
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[FD; FF1]; [FF1; AP]; [D1]; [D4]; [E1; E21];
                        [E2; E21]; [E3]; [E4]; [E5]; [E6; E21]; [E7; E21];
                        [E8]; [E9]; [E10]; [D7]; [D10]; [E11; E21];
                        [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
                        [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
                        [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t))) =
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p [[FD; FF1]; [FF1; AP]] t))) *
            list_prod
              (one_minus_list
                 (list_prod_rel p
                    (list_fail_event_list p
                       [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
                        [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7];
                        [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
                        [E16; E21]; [E17; E21]; [E18]; [E19]; [E20];
                        [C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
                        [SL; time]; [PD; time]; [Others; time]] t)))
   
   [Internal_FT_lemma2]  Theorem
      
      ⊢ ∀p t FD AP FF1 C_FD C_AP C_FF1.
            0 ≤ t ∧ prob_space p ∧
            list_exp p (FLAT [[C_FD; C_FF1]; [C_AP; C_FF1]])
              (FLAT [[FD; FF1]; [AP; FF1]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p [[FD; FF1]; [FF1; AP]] t))) =
             list_prod
               (one_minus_exp_prod t [[C_FD; C_FF1]; [C_AP; C_FF1]]))
   
   [RT_FT_lemma2]  Theorem
      
      ⊢ ∀p t AL SL PD Others time C_AL C_SL C_PD C_Others C_time.
            0 ≤ t ∧ prob_space p ∧
            list_exp p
              (FLAT
                 [[C_AL; C_time]; [C_SL; C_time]; [C_PD; C_time];
                  [C_Others; C_time]])
              (FLAT [[AL; time]; [SL; time]; [PD; time]; [Others; time]]) ⇒
            (list_prod
               (one_minus_list
                  (list_prod_rel p
                     (list_fail_event_list p
                        [[AL; time]; [SL; time]; [PD; time];
                         [Others; time]] t))) =
             list_prod
               (one_minus_exp_prod t
                  [[C_AL; C_time]; [C_SL; C_time]; [C_PD; C_time];
                   [C_Others; C_time]]))
   
   
*)
end
