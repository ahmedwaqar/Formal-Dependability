(* ========================================================================= *)
(* File Name: Formal Importance Measure Analysis                             *)
(*---------------------------------------------------------------------------*)
(* Description:                                                              *)
(*                                                                           *)
(*                                                                           *)
(*                HOL4-Kananaskis 12 		 			     *)
(*									     *)
(*		Author :  Waqar Ahmad             		     	     *)
(*                                              			     *)
(* 	    Electrical and Computer Engineering                              *)
(*	    Concordia Univeristy, Montreal, QC, Canada                       *)
(*                                          		               	     *)
(*                                                                           *)
(* ========================================================================= *)



(*app load ["FT_deepTheory","arithmeticTheory","probabilityTheory","listTheory","VDCTheory","RBDTheory","railwayTheory","util_probTheory","transcTheory","ASN_gatewayTheory","pred_setTheory","dep_rewrite","sortingTheory","combinTheory","seqTheory","realTheory","realLib","pred_setTheory","transform_FT_RBDTheory","FTRImpTheory","FTImp_deepTheory"];*)
open FT_deepTheory probabilityTheory listTheory VDCTheory RBDTheory railwayTheory util_probTheory transcTheory ASN_gatewayTheory combinTheory pred_setTheory sortingTheory dep_rewrite seqTheory pred_setTheory arithmeticTheory realTheory realLib transform_FT_RBDTheory FTRImpTheory FTImp_deepTheory;

   
open HolKernel boolLib bossLib Parse;
val _ = new_theory "FTImp_deep";

(*------new tactics for set simplification----*)
(*--------------------*)
infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);


val coherent_struct_def = Define
`coherent_struct phi (L:'a list) = phi L`;

val _ = Unicode.unicode_version {u = UnicodeChars.phi, tmnm = "coherent_struct"};


(*
`coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))))) = s`

`coherent_struct (\b. rbd_struct p ((series of (\a. parallel (rbd_list a))) b)) [[x1;x2]] = t `
*)

val lupdate_def = Define
`lupdate e (n,i) L = LUPDATE e i (EL n L)`;


val coherent_struct_update_def = Define
`coherent_struct_update e i phi L =
 coherent_struct phi (LUPDATE e i L)`;


val _ = Unicode.unicode_version {tmnm = "coherent_struct_update",
                                 u = UnicodeChars.phi^
                                     UnicodeChars.rsquo};
				     
val coherent_struct_update2_def = Define
`coherent_struct_update2 e e' i j phi L =
 coherent_struct phi (LUPDATE e' j (LUPDATE e i L))`;

val _ = Unicode.unicode_version {tmnm = "coherent_struct_update2",
                                 u = UnicodeChars.phi^
                                     UnicodeChars.rdquo};
				     
val _ = Unicode.unicode_version {tmnm = "fail_event",
                                 u = UnicodeChars.omega};



val binary_MCS_def = Define
`(binary_MCS phi (i,x,L:'a event list) =
 phi (LUPDATE x i L))`;

val comp_state_vec_def = Define
`comp_state_vec (f:'a event -> bool) L = FOLDL (\a b. a /\ f b) T L`;

val coherent_state_vec_def = Define
`(coherent_state_vec (f:'a event -> bool) [] = T) /\
(coherent_state_vec (f:'a event -> bool) (h::t) = f h /\ coherent_state_vec f t)`;


val comp_vec_space_1 = store_thm("comp_vec_space_1",
  ``!L p.
  prob_space p /\
  ~NULL L /\
  in_events p L /\
  coherent_state_vec (λa. a = p_space p) L ==>
  (list_prod (list_prob p L) = 1)``,
Induct
>- (rw[])
\\ Cases_on `L`
>- (fs[list_prod_def,list_prob_def,coherent_state_vec_def,PROB_UNIV])
\\ rw[list_prod_def,Once list_prob_def]
\\ fs[coherent_state_vec_def]
\\ rw[PROB_UNIV]
\\ first_x_assum (match_mp_tac)
\\ fs[in_events_def]
\\ metis_tac[]);

val coherent_state_vec1_def = Define
`coherent_state_vec1 f L = (!x. MEM x L ==> (f x))`;

val coherent_state_vec_space = store_thm("coherent_state_vec_space",
  ``!p L.
  prob_space p /\ coherent_state_vec1 (λa. a = p_space p) L ==> in_events p L``,
rw[in_events_def,coherent_state_vec1_def,EVENTS_SPACE]);

val coherent_state_vec_empty = store_thm("coherent_state_vec_empty",
  ``!p L.
  prob_space p /\ coherent_state_vec1 (λa. a = EMPTY) L ==> in_events p L``,
rw[in_events_def,coherent_state_vec1_def,EVENTS_EMPTY]);

val in_events_AND_gate = store_thm("in_events_AND_gate",
  ``!p L.
    prob_space p /\
    in_events p L ==> FTree p (AND (gate_list L)) ∈ events p``,
rw[]
\\ metis_tac[AND_gate_eq_big_inter,in_events_big_inter,in_events_def]);


val coherent_AND_FT_gate1 = store_thm("coherent_AND_FT_gate1",
  ``!L p.
     prob_space p /\
     coherent_state_vec1 (\a. a = (p_space p)) L ==>
     (prob p
     	(coherent_struct (\b. FTree p (AND (gate_list b))) L) =
     1)``,
Induct
>- (rw[coherent_struct_def,FTree_def,gate_list_def,PROB_UNIV])
\\ rw[coherent_struct_def,FTree_def,gate_list_def,coherent_state_vec1_def]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
\\ DEP_REWRITE_TAC[in_events_AND_gate]
>- (DEP_REWRITE_TAC[coherent_state_vec1_def,coherent_state_vec_space]
   \\ rw[])
\\ fs[coherent_struct_def,coherent_state_vec1_def]);


val coherent_AND_FT_gate2 = store_thm("coherent_AND_FT_gate2",
  ``!L p. ~NULL L /\
     prob_space p /\
     coherent_state_vec1 (\a. a = (EMPTY)) L ==>
     (prob p
     	(coherent_struct (\b. FTree p (AND (gate_list b))) L) =
     0)``,
Induct
>- (rw[])
\\ rw[coherent_struct_def,FTree_def,gate_list_def,PROB_EMPTY]
\\ Cases_on `NULL L`
>- (fs[NULL_EQ,coherent_state_vec1_def,PROB_EMPTY])
\\ fs[coherent_state_vec1_def,PROB_EMPTY]);


val AND_gate_empty = store_thm("AND_gate_empty",
  ``!p L. ~NULL L /\
  coherent_state_vec1 (\a. a = EMPTY) L ==>
  ((coherent_struct (\b. FTree p (AND (gate_list b))) L) = EMPTY)``,
Induct_on `L`
>- (rw[])
\\  rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec1_def]);


val OR_AND_FT_EMPTY = store_thm("OR_AND_FT_EMPTY",
  ``!L p. not_null L /\
     coherent_state_vec1 (\a. a = (EMPTY)) (FLAT L) ==>
     ((coherent_struct (λb. FTree p ((OR of (λa. AND (gate_list a))) b)) L) =
     EMPTY)``,
Induct
>- (rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,smart_gridTheory.not_null_def])
\\ rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,smart_gridTheory.not_null_def]
\\ DEP_REWRITE_TAC[SIMP_RULE real_ss[coherent_struct_def,of_DEF]AND_gate_empty]
\\ fs[coherent_state_vec1_def]
\\ fs[smart_gridTheory.not_null_def,coherent_struct_def,of_DEF]
\\ DEP_ASM_REWRITE_TAC[]
\\ fs[coherent_state_vec1_def]);

val prob_OR_AND_FT_EMPTY_0 = store_thm("prob_OR_AND_FT_EMPTY_0",
  ``!L p. not_null L /\ prob_space p /\
     coherent_state_vec1 (\a. a = (EMPTY)) (FLAT L) ==>
     (prob p (coherent_struct (λb. FTree p ((OR of (λa. AND (gate_list a))) b)) L) =
     0)``,
rw[]
\\ DEP_REWRITE_TAC[OR_AND_FT_EMPTY]
\\ metis_tac[PROB_EMPTY]);

(*------*)


val X_vec_def = Define
`X_vec L = MAP (\a. FST a) L`;

val XL_vec_def = Define
`XL_vec L = MAP (\a. X_vec a) L`;


val Y_vec_def = Define
`Y_vec L = MAP (\a. SND a) L`;

val YL_vec_def = Define
`YL_vec L = MAP (\a. Y_vec a) L`;

val mem_subset_def = Define
`mem_subset L = EVERY (\a. (FST a) SUBSET (SND a)) L`;

val mem_subset_vec_def = Define
`mem_subset_vec L = EVERY (\a. mem_subset a) L`;


val coherent_AND_gate_le = store_thm("coherent_AND_gate_le",
  ``!p L.
mem_subset L ==> (FTree p (AND (gate_list (X_vec L))) SUBSET FTree p (AND (gate_list (Y_vec L))))``,
Induct_on `L`
>- (rw[LIST_TO_SET,X_vec_def,Y_vec_def])
\\ rw[gate_list_def,FTree_def,of_DEF,LIST_TO_SET,X_vec_def,Y_vec_def,INTER_SUBSET]
>- (fs[X_vec_def,Y_vec_def,INTER_SUBSET,mem_subset_def]
   \\ metis_tac[SUBSET_TRANS,INTER_SUBSET])
\\ irule SUBSET_TRANS
\\ Q.EXISTS_TAC `FTree p (AND (gate_list (MAP (λa. FST a) L)))`
\\ rw[]
\\ fs[X_vec_def,Y_vec_def,mem_subset_def]);


val coherent_OR_gate_le = store_thm("coherent_OR_gate_le",
  ``!p L.
    mem_subset L ==>
    (FTree p (OR (gate_list (X_vec L))) SUBSET FTree p (OR (gate_list (Y_vec L))))``,
Induct_on `L`
>- (rw[LIST_TO_SET,X_vec_def,Y_vec_def])
\\ rw[gate_list_def,FTree_def,of_DEF,LIST_TO_SET,X_vec_def,Y_vec_def,INTER_SUBSET]
>- (fs[X_vec_def,Y_vec_def,SUBSET_UNION,mem_subset_def]
   \\ metis_tac[SUBSET_TRANS,SUBSET_UNION])
\\ irule SUBSET_TRANS
\\ Q.EXISTS_TAC `FTree p (OR (gate_list (MAP (λa. SND a) L)))`
\\ rw[]
\\ fs[X_vec_def,Y_vec_def,mem_subset_def]);


val coherent_AND_of_OR_subset = store_thm("coherent_AND_of_OR_subset",
  ``!p L.
mem_subset_vec L ==>
(coherent_struct (\b. FTree p ((AND of (\a. OR (gate_list a))) b)) (XL_vec L) SUBSET
(coherent_struct (\b. FTree p ((AND of (\a. OR (gate_list a))) b)) (YL_vec L)))  ``,
gen_tac
\\ Induct
>- (rw[coherent_struct_def,FTree_def,of_DEF,LIST_TO_SET,XL_vec_def,YL_vec_def])
\\ rw[coherent_struct_def,FTree_def,of_DEF,LIST_TO_SET,XL_vec_def,YL_vec_def]
>- (irule SUBSET_TRANS
   \\ Q.EXISTS_TAC `FTree p (OR (gate_list (X_vec h)))`
   \\ rw[INTER_SUBSET]
   \\ irule coherent_OR_gate_le
   \\ fs[mem_subset_vec_def])
\\ irule SUBSET_TRANS
\\ Q.EXISTS_TAC `FTree p (AND (MAP (λa. OR (gate_list a)) (MAP (λa. X_vec a) L)))`
\\ rw[INTER_SUBSET]
\\ fs[coherent_struct_def,of_DEF,XL_vec_def,YL_vec_def,mem_subset_vec_def]);

val coherent_OR_of_AND_subset = store_thm("coherent_OR_of_AND_subset",
  ``!p L.
mem_subset_vec L ==>
(coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) (XL_vec L) SUBSET
(coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) (YL_vec L)))  ``,
gen_tac
\\ Induct
>- (rw[coherent_struct_def,FTree_def,of_DEF,LIST_TO_SET,XL_vec_def,YL_vec_def])
\\ rw[coherent_struct_def,FTree_def,of_DEF,LIST_TO_SET,XL_vec_def,YL_vec_def]
>- (irule SUBSET_TRANS
   \\ Q.EXISTS_TAC `FTree p (AND (gate_list (Y_vec h)))`
   \\ rw[SUBSET_UNION]
   \\ irule coherent_AND_gate_le
   \\ fs[mem_subset_vec_def])
\\ irule SUBSET_TRANS
\\ Q.EXISTS_TAC `FTree p (OR (MAP (λa. AND (gate_list a)) (MAP (λa. Y_vec a) L)))`
\\ rw[SUBSET_UNION]
\\ fs[coherent_struct_def,of_DEF,XL_vec_def,YL_vec_def,mem_subset_vec_def]);


val prob_coherent_AND_of_OR_le = store_thm("prob_coherent_AND_of_OR_le",
  ``!p L.
prob_space p /\
in_events p (FLAT (XL_vec L)) /\
in_events p (FLAT (YL_vec L)) /\
mem_subset_vec L ==>
(prob p (coherent_struct (\b. FTree p ((AND of (\a. OR (gate_list a))) b)) (XL_vec L)) <=
prob p (coherent_struct (\b. FTree p ((AND of (\a. OR (gate_list a))) b)) (YL_vec L)))``,
rw[]
\\ irule PROB_INCREASING
\\ rw[coherent_AND_of_OR_subset]
\\ rw[coherent_struct_def]
\\ rw[AND_OR_to_series_parallel,of_DEF]
\\ match_mp_tac in_events_series_parallel
\\ fs[in_events_def]);


val prob_coherent_OR_of_AND_le = store_thm("prob_coherent_OR_of_AND_le",
  ``!p L.
prob_space p /\
in_events p (FLAT (XL_vec L)) /\
in_events p (FLAT (YL_vec L)) /\
mem_subset_vec L ==>
(prob p (coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) (XL_vec L)) <=
prob p (coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) (YL_vec L)))``,
rw[]
\\ irule PROB_INCREASING
\\ rw[coherent_OR_of_AND_subset]
\\ rw[coherent_struct_def]
\\ rw[OR_AND_to_parallel_series,of_DEF]
\\ match_mp_tac in_events_parallel_series
\\ fs[in_events_def]);
(*-----*)




val coherent_AND_FT_gate = store_thm("coherent_AND_FT_gate",
  ``!L p. ~NULL L /\
     prob_space p /\
     in_events p L /\
     mutual_indep p L /\
     coherent_state_vec (\a. a = (p_space p)) L ==>
     (prob p
     	(coherent_struct (\b. FTree p (AND (gate_list b))) L) =
     1)``,
rw[coherent_struct_def]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ fs[in_events_def]
\\ irule comp_vec_space_1
\\ rw[in_events_def]);

val AND_gate_space = store_thm("AND_gate_space",
  ``!p L.
  ~NULL L /\ coherent_state_vec (\a. a = (p_space p)) L ==>
  ((coherent_struct (\b. FTree p (AND (gate_list b))) L) = p_space p)``,
Induct_on `L`
>- (rw[])
\\  rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec_def]
\\ Cases_on `L`
>- (rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec_def])
\\ fs[coherent_struct_def]);

val coherent_state_vec_append = store_thm("coherent_state_vec_append",
  ``!p h L.
  coherent_state_vec (λa. a = p_space p) (h ⧺ L) ==>  coherent_state_vec (λa. a = p_space p) h ``,
gen_tac
\\ Induct
>- (rw[coherent_state_vec_def])
\\ rw[coherent_state_vec_def]
\\ metis_tac[]);

val coherent_state_vec_append1 = store_thm("coherent_state_vec_append1",
  ``!p h L.
  coherent_state_vec (λa. a = p_space p) (h ⧺ L) ==>  (coherent_state_vec (λa. a = p_space p) h /\  coherent_state_vec (λa. a = p_space p) L)``,
gen_tac
\\ Induct_on `h`
>- (rw[coherent_state_vec_def])
\\ rw[coherent_state_vec_def]
\\ metis_tac[]);



val OR_AND_FT_SPACE = store_thm("OR_AND_FT_SPACE",
  ``!p L.
  ~NULL L /\ coherent_state_vec (\a. a = (p_space p)) (FLAT L) ==>
  (coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) L = p_space p)``,
rw[]
\\ Induct_on `L`
>- (rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF])
\\ rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF]
\\ Cases_on `NULL h`
>- (fs[NULL_EQ]
   \\  rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec_def]
   \\ Cases_on `L`
   >- (rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec_def])
   \\ fs[coherent_struct_def,of_DEF])
\\ DEP_REWRITE_TAC[SIMP_RULE real_ss [coherent_struct_def]AND_gate_space]
\\ rw[]
>- (metis_tac[coherent_state_vec_append])
\\  Cases_on `L`
>- (rw[coherent_struct_def,FTree_def,gate_list_def,of_DEF,coherent_state_vec_def])
\\ full_simp_tac std_ss[coherent_struct_def,of_DEF,NULL,FLAT]
\\ DEP_ASM_REWRITE_TAC[]
\\ metis_tac[UNION_IDEMPOT,coherent_state_vec_append1]);

val prob_OR_AND_FT_SPACE_1 = store_thm("prob_OR_AND_FT_SPACE_1",
  ``!p L. prob_space p /\
  ~NULL L /\ coherent_state_vec (\a. a = (p_space p)) (FLAT L) ==>
  (prob p (coherent_struct (\b. FTree p ((OR of (\a. AND (gate_list a))) b)) L) = 1)  ``,
rw[]
\\ DEP_REWRITE_TAC[OR_AND_FT_SPACE ]
\\ metis_tac[PROB_UNIV]);



val BImp_measure_def = Define
`BImp_measure p i phi L =
prob p (coherent_struct_update (p_space p) i phi L) -
prob p (coherent_struct_update EMPTY i phi L) `;



val BImp_measure'_def = Define
`BImp_measure' p e' i j phi L =
prob p (coherent_struct_update2 (p_space p) e' i j phi L) -
prob p (coherent_struct_update2 EMPTY e' i j phi L)`;


val BImp_measure''_def = Define
`BImp_measure'' p i j phi L =
BImp_measure' p (p_space p) i j phi L -
BImp_measure' p EMPTY i j phi L`;

val B_Imp'_def = Define
`B_Imp' p e i j phi L =
 prob p (coherent_struct_update2 e (p_space p) i j phi L) −
 prob p (coherent_struct_update2 e EMPTY i j phi L)`;

(*
`BImp_measure p j (\a. FTree p (AND (gate_list a))) L <= BImp_measure p i (\a. FTree p (AND (gate_list a))) L`


`x2 IN events p /\ prob_space p ==>
(BImp_measure p 0 (\a. FTree p (AND (gate_list a))) [x1;x2] =
 prob p (EL 1 [x1;x2]) * (BImp_measure'' p 0 1 (\a. FTree p (AND (gate_list a))) [x1;x2]) +
 BImp_measure' p (EMPTY) 0 1 (\a. FTree p (AND (gate_list a))) [x1;x2])`

rw[BImp_measure''_def,BImp_measure'_def,BImp_measure_def]
\\ rw[coherent_struct_update2_def,coherent_struct_update_def,coherent_struct_def]
\\ rw[FTree_def]
\\ once_rewrite_tac[ONE]
\\ rw[LUPDATE_def]
\\ rw[FTree_def,gate_list_def]
\\ DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_SPACE,PROB_UNIV,PROB_EMPTY]
\\ once_rewrite_tac[INTER_COMM]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
*)
val mutual_indep_append_lupdate = store_thm("mutual_indep_append_lupdate",
  ``!p L n l e.
  n <= LENGTH L /\
  mutual_indep p (e::l++L) ==> mutual_indep p (l++ LUPDATE e n L)``,
gen_tac
\\ Induct_on `L`
>- (rw[LUPDATE_def]
   \\ metis_tac[mutual_indep_cons])
\\ rw[]
\\ Cases_on `n`
>- (rw[LUPDATE_def]
   \\ irule mutual_indep_append_sym
   \\ once_rewrite_tac[(prove(``!a b k. b::c = [b]++c``,rw[]))]
   \\ irule mutual_indep_cons
   \\ Q.EXISTS_TAC `h`
   \\ once_rewrite_tac[(prove(``!a b k. b::c = [b]++c``,rw[]))]
   \\ rewrite_tac[APPEND_ASSOC]
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ irule mutual_indep_append1
   \\ rewrite_tac[APPEND_ASSOC]
   \\ irule mutual_indep_append_sym
   \\ rewrite_tac[APPEND_ASSOC]
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ irule mutual_indep_append1
   \\ rw[]
   \\  once_rewrite_tac[GSYM (prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[]))]
   \\ metis_tac[])
\\ first_x_assum (mp_tac o Q.SPECL[`n'`,`l ++ [h]`,`e`])
\\ rw[LUPDATE_def]
\\ once_rewrite_tac[prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[])]
\\ first_x_assum (match_mp_tac)
\\ once_rewrite_tac[GSYM (prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[]))]
\\ metis_tac[]
\\ rw[LUPDATE_def]);


val mutual_indep_append_lupdate1 = store_thm("mutual_indep_append_lupdate1",
  ``!p L n l e.
  mutual_indep p (e::l++L) ==> mutual_indep p (l++ LUPDATE e n L)``,
gen_tac
\\ Induct_on `L`
>- (rw[LUPDATE_def]
   \\ metis_tac[mutual_indep_cons])
\\ rw[]
\\ Cases_on `n`
>- (rw[LUPDATE_def]
   \\ irule mutual_indep_append_sym
   \\ once_rewrite_tac[(prove(``!a b k. b::c = [b]++c``,rw[]))]
   \\ irule mutual_indep_cons
   \\ Q.EXISTS_TAC `h`
   \\ once_rewrite_tac[(prove(``!a b k. b::c = [b]++c``,rw[]))]
   \\ rewrite_tac[APPEND_ASSOC]
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ irule mutual_indep_append1
   \\ rewrite_tac[APPEND_ASSOC]
   \\ irule mutual_indep_append_sym
   \\ rewrite_tac[APPEND_ASSOC]
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ irule mutual_indep_append1
   \\ rw[]
   \\  once_rewrite_tac[GSYM (prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[]))]
   \\ metis_tac[])
\\ first_x_assum (mp_tac o Q.SPECL[`n'`,`l ++ [h]`,`e`])
\\ rw[LUPDATE_def]
\\ once_rewrite_tac[prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[])]
\\ first_x_assum (match_mp_tac)
\\ once_rewrite_tac[GSYM (prove(``!a b c. a ++ b::c = a ++ [b]++c``,rw[]))]
\\ metis_tac[]
\\ rw[LUPDATE_def]);


val mutual_indep_lupdate = store_thm("mutual_indep_lupdate",
  ``!p L n e.
  mutual_indep p (e::L) ==> mutual_indep p (LUPDATE e n L)``,
rw[]
\\ MP_TAC(Q.ISPECL[`(p :α event # α event event # (α event -> real))`,
                   `(L :α event list)`,
		   `(n :num)`,
		   `[]:'a event list`,
		   `(e :α event)`] mutual_indep_append_lupdate1)
\\ rw[]);



val BImp_measure_0 = store_thm("BImp_measure_0",
  ``!p h L.
prob_space p /\
in_events p L ==>
(BImp_measure p 0 (λa. FTree p (AND (gate_list a))) (h::L) =
 prob p (FTree p (AND (gate_list L))))``,
rw[BImp_measure_def,coherent_struct_update_def,coherent_struct_def,LUPDATE_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ metis_tac[ in_events_AND_gate]);

val in_events_MEM_LUPDATE_SPACE = store_thm("in_events_MEM_LUPDATE_SPACE",
  ``!p n L.
    prob_space p /\ (!x. MEM x L ==> x IN events p) ==>
    (!x. MEM x (LUPDATE (p_space p) n L) ==> x IN events p)``,
rw[in_events_def]
\\ metis_tac[MEM_LUPDATE_E,EVENTS_SPACE]);


val in_events_MEM_LUPDATE_EMPTY = store_thm("in_events_MEM_LUPDATE_EMPTY",
  ``!p n L. prob_space p /\ in_events p L ==>
            (!x. MEM x (LUPDATE (EMPTY) n L) ==> x IN events p)``,
rw[in_events_def]
\\ metis_tac[MEM_LUPDATE_E,EVENTS_EMPTY]);

val mutual_indep_lupdate_cons = store_thm("mutual_indep_lupdate_cons",
  ``!p n h h' L. mutual_indep p (h::h'::L) ==> mutual_indep p (h::LUPDATE h' n L)``,
rw[]
\\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
\\ irule mutual_indep_append_lupdate1
\\ once_rewrite_tac[prove(``!a b. [a ;b] = [a]++[b]``,rw[])]
\\ irule mutual_indep_append1
\\ rw[]);

val mutual_indep_lupdate_cons1 = store_thm("mutual_indep_lupdate_cons1",
  ``!p n h h' L. mutual_indep p (h'::h::L) ==> mutual_indep p (h::LUPDATE h' n L)``,
rw[]
\\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
\\ irule mutual_indep_append_lupdate1
\\ rw[]);

val mutual_indep_lupdate_cons2 = store_thm("mutual_indep_lupdate_cons2",
  ``!p n h h' h'' L. mutual_indep p (h'::h''::h::L) ==> mutual_indep p (h::LUPDATE h' n L)``,
rw[]
\\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
\\ irule mutual_indep_append_lupdate1
\\ once_rewrite_tac[prove(``!a b. [a ;b] = [a]++[b]``,rw[])]
\\ irule mutual_indep_front_append
\\ Q.EXISTS_TAC `[h'']`
\\ rewrite_tac[APPEND_ASSOC]
\\ rewrite_tac[Once  (GSYM APPEND_ASSOC)]
\\ irule mutual_indep_append1
\\ rw[]);

val mutual_indep_lupdate_cons3 = store_thm("mutual_indep_lupdate_cons3",
  ``!p n h h' L. mutual_indep p (h'::h::L) ==> mutual_indep p (LUPDATE h' n L)``,
rw[]
\\ irule mutual_indep_lupdate
\\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
\\ irule mutual_indep_front_append
\\ Q.EXISTS_TAC `[h]`
\\ rewrite_tac[APPEND_ASSOC]
\\ irule mutual_indep_append1 \\ rw[]);

val mutual_indep_cons1 = store_thm("mutual_indep_cons1",
  ``!p h h' L. mutual_indep p (h'::h::L) ==>  mutual_indep p (h'::L)``,
rw[]
\\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
\\ irule mutual_indep_front_append
\\ Q.EXISTS_TAC `[h]`
\\ rewrite_tac[APPEND_ASSOC]
\\ irule mutual_indep_append1 \\ rw[]);

val mutual_indep_append2 = store_thm("mutual_indep_append2",
  ``!p l1 l2 L. mutual_indep p (l1++l2++L) ==>  mutual_indep p (l1++L)``,
rw[]
\\ irule mutual_indep_front_append
\\ Q.EXISTS_TAC `l2`
\\ metis_tac[APPEND_ASSOC,mutual_indep_append1]);

val not_null_lupdate = store_thm("not_null_lupdate",
  ``!e n L. ~NULL L ==> ¬NULL (LUPDATE e n L)``,
gen_tac
\\ Cases
\\ Cases
   \\ rw[LUPDATE_def]);

val AND_FT_gate_cons_indep = store_thm("AND_FT_gate_cons_indep",
  ``!p h L.
prob_space p ∧ ¬NULL L ∧ (∀x'. MEM x' (h::L) ⇒ x' ∈ events p) ∧
 mutual_indep p (h::L) ⇒
(prob p (h INTER FTree p (AND (gate_list L))) =
 prob p (h) * prob p (FTree p (AND (gate_list L))))``,
rw[]
\\ rw[prove (``!h p l. h INTER FTree p (AND (gate_list l)) =  FTree p (AND (gate_list (h::l)))``, rw[FTree_def,gate_list_def])]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ rw[list_prob_def,list_prod_def] \\ metis_tac[NULL,list_prob_def,list_prod_def,mutual_indep_cons]);


val BImp_measure_SUC = store_thm("BImp_measure_SUC",
  ``!p n h L.
prob_space p /\ ~NULL L /\
in_events p (h::L) /\
mutual_indep p (EMPTY ::p_space p::h::L) ==>
(BImp_measure p (SUC n) (λa. FTree p (AND (gate_list a))) (h::L) =
 prob p h * BImp_measure p n (λa. FTree p (AND (gate_list a))) (L))``,
rw[BImp_measure_def,coherent_struct_update_def,coherent_struct_def,LUPDATE_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ rw[prove (``!h p l. h INTER FTree p (AND (gate_list l)) =  FTree p (AND (gate_list (h::l)))``, rw[FTree_def,gate_list_def])]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ fs[in_events_def]
\\ dsimp[]
\\ asm_rewrite_tac[]
\\ rw[]
\\ fs[]
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE])
>- (irule mutual_indep_lupdate_cons1
   \\ metis_tac[mutual_indep_cons])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons2
   \\ metis_tac[])
>- (metis_tac[not_null_lupdate])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (metis_tac[mutual_indep_cons,mutual_indep_lupdate_cons3])
>- (metis_tac[not_null_lupdate])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate
   \\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
   \\ irule  mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p;h]`
   \\ rw[APPEND_ASSOC])
\\ rw[list_prob_def,list_prod_def]
\\ REAL_ARITH_TAC);


val BImp_measure'_AND_FT_SUC_0 = store_thm("BImp_measure'_AND_FT_SUC_0",
  ``!p h h' L i.
  prob_space p /\ ~NULL L /\
in_events p (h::L) /\
mutual_indep p (EMPTY ::p_space p::h::L) ==>
  (BImp_measure' p h (SUC i) 0 (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p h * BImp_measure p i (λa. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ rw[prove (``!h p l. h INTER FTree p (AND (gate_list l)) =  FTree p (AND (gate_list (h::l)))``, rw[FTree_def,gate_list_def])]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ fs[in_events_def]
\\ dsimp[]
\\ asm_rewrite_tac[]
\\ rw[]
\\ fs[]
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE])
>- (irule mutual_indep_lupdate_cons1
   \\ metis_tac[mutual_indep_cons])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons2
   \\ metis_tac[])
>- (metis_tac[not_null_lupdate])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (metis_tac[mutual_indep_cons,mutual_indep_lupdate_cons3])
>- (metis_tac[not_null_lupdate])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate
   \\ once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
   \\ irule  mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p;h]`
   \\ rw[APPEND_ASSOC])
\\ rw[list_prob_def,list_prod_def]
\\ REAL_ARITH_TAC);


val B_Imp'_AND_FT_SUC_0 = store_thm("B_Imp'_AND_FT_SUC_0",
  ``!p h h' L i.
  prob_space p /\
in_events p (h::L) ==>
  (B_Imp' p h (SUC i) 0 (\a. FTree p (AND (gate_list a))) (h'::L) =
   prob p (FTree p (AND (gate_list (LUPDATE h i L)))))``,
rw[B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
\\ DEP_REWRITE_TAC[in_events_AND_gate]
\\ rw[]
\\ fs[in_events_def]
\\ rw[]
\\ imp_res_tac MEM_LUPDATE_E
\\ fs[]);

val BImp_measure'_AND_FT_SUC_0_SPACE = store_thm("BImp_measure'_AND_FT_SUC_0_SPACE",
  ``!p h' L i.
  prob_space p /\
in_events p L ==>
  (BImp_measure' p (p_space p) (SUC i) 0 (\a. FTree p (AND (gate_list a))) (h'::L) =
  BImp_measure p i (λa. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
\\ DEP_REWRITE_TAC[in_events_AND_gate]
\\ rw[in_events_def]
\\ imp_res_tac MEM_LUPDATE_E
\\ fs[in_events_def,EVENTS_SPACE,EVENTS_EMPTY]);

val BImp_measure'_AND_FT_SUC_0_EMPTY = store_thm("BImp_measure'_AND_FT_SUC_0_EMPTY",
  ``!p h' L i.
  prob_space p ==>
  (BImp_measure' p EMPTY (SUC i) 0 (\a. FTree p (AND (gate_list a))) (h'::L) =
  0)``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]);


val BImp_measure'_AND_FT_0_SUC = store_thm("BImp_measure'_AND_FT_0_SUC",
  ``!p h h' L j.
  prob_space p /\
in_events p (h::L) ==>
  (BImp_measure' p h 0 (SUC j) (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p (coherent_struct_update h j (\a. FTree p (AND (gate_list a))) L))``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[]
\\ DEP_REWRITE_TAC[in_events_AND_gate]
\\ rw[in_events_def]
\\ imp_res_tac MEM_LUPDATE_E
\\ fs[in_events_def]);


val B_Imp'_AND_FT_0_SUC = store_thm("B_Imp'_AND_FT_0_SUC",
  ``!p h h' L j.
  prob_space p /\
in_events p (h::L) /\
mutual_indep p (EMPTY::p_space p::h::L) ==>
  (B_Imp' p h 0 (SUC j) (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p h * (BImp_measure p j (\a. FTree p (AND (gate_list a))) L ))``,
rw[B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ Cases_on `NULL L`
>- (fs[NULL_EQ]
   \\ rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY])
\\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep]
\\ rw[]
\\ fs[not_null_lupdate,in_events_def,in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def]
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons1
   \\ metis_tac[mutual_indep_cons])
>- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a]++b::c``,rw[])]
   \\ irule mutual_indep_append2
   \\ rw[]
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[])
\\ REAL_ARITH_TAC);


val BImp_measure'_AND_FT_SUC_SUC = store_thm("BImp_measure'_AND_FT_SUC_SUC",
  ``!p h h' L i j.
  prob_space p /\ ~NULL L /\
in_events p (h::h'::L) /\
mutual_indep p (EMPTY ::p_space p::h::h'::L) ==>
  (BImp_measure' p h (SUC i) (SUC j) (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p h' * BImp_measure' p h i j (\a. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ rw[prove (``!h p l. h INTER FTree p (AND (gate_list l)) =  FTree p (AND (gate_list (h::l)))``, rw[FTree_def,gate_list_def])]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ fs[in_events_def]
\\ dsimp[]
\\ asm_rewrite_tac[]
\\ rw[]
\\ fs[]
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[])
   \\ metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[]
   \\ metis_tac[mutual_indep_cons])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[])
   \\ metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[]
   \\  once_rewrite_tac[prove(``!a b c. a ::b::c::d = [a]++b::c::d``,rw[])]
   \\ irule mutual_indep_append2
   \\ rw[]
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[])
>- (metis_tac[not_null_lupdate])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[])
   \\ metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate
   \\ irule mutual_indep_lupdate_cons1
   \\  once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[h']`
   \\ rw[]
   \\ metis_tac[mutual_indep_cons])
>- (metis_tac[not_null_lupdate])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[])
   \\ metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (irule mutual_indep_lupdate
   \\ irule mutual_indep_lupdate_cons1
   \\  once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[h']`
   \\ rw[]
   \\ once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a]++ b::c::d``,rw[])]
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[])
\\ rw[list_prob_def,list_prod_def]
\\ REAL_ARITH_TAC);

val B_Imp'_AND_FT_SUC_SUC = store_thm("B_Imp'_AND_FT_SUC_SUC",
  ``!p h h' L i j.
  prob_space p /\
in_events p (h::h'::L) /\
mutual_indep p (EMPTY ::p_space p::h::h'::L) ==>
  (B_Imp' p h (SUC i) (SUC j) (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p h' * B_Imp' p h i j (\a. FTree p (AND (gate_list a))) L)``,
rw[B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ Cases_on `NULL L`
>- (fs[NULL_EQ]
   \\ rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY])
\\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep]
\\ rw[]
\\ fs[in_events_def]
>- (metis_tac[not_null_lupdate])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[EVENTS_SPACE])
   \\ imp_res_tac MEM_LUPDATE_E
   \\ metis_tac[])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c . a ::b::c = [a;b]++ c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[]
   \\ once_rewrite_tac[prove(``!a b c . a ::b::c::d = [a]++ [b]++c::d``,rw[])]
   \\ irule mutual_indep_append1
   \\ rw[]
   \\ metis_tac[mutual_indep_cons])
>- (metis_tac[not_null_lupdate])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[EVENTS_EMPTY])
   \\ imp_res_tac MEM_LUPDATE_E
   \\ metis_tac[])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c . a ::b::c = [a;b]++ c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[]
   \\ once_rewrite_tac[prove(``!a b c . a ::b::c::d = [a]++ [b]++c::d``,rw[])]
   \\ irule mutual_indep_append1
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[]
   \\ metis_tac[])
\\ REAL_ARITH_TAC);




(*val BImp_measure'_AND_FT_SUC_SUC_SPACE = store_thm("BImp_measure'_AND_FT_SUC_SUC_SPACE",
  ``!p h' L i j.
  prob_space p /\ ~NULL L /\
in_events p (h'::L) /\
mutual_indep p (EMPTY ::p_space p::p_space p::h'::L) ==>
  (BImp_measure' p (p_space p) (SUC i) (SUC j) (\a. FTree p (AND (gate_list a))) (h'::L) =
  prob p h' * BImp_measure' p h i j (\a. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ rw[prove (``!h p l. h INTER FTree p (AND (gate_list l)) =  FTree p (AND (gate_list (h::l)))``, rw[FTree_def,gate_list_def])]
\\ DEP_REWRITE_TAC[AND_gate_thm]
\\ fs[in_events_def]
\\ dsimp[]
\\ asm_rewrite_tac[]
\\ rw[]
\\ fs[]
>- (imp_res_tac MEM_LUPDATE_E
   \\ metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
>- (once_rewrite_tac[prove(``!a b. a ::c = [a]++c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ )

*)


val BImp_measure''_AND_FT_0_SUC = store_thm("BImp_measure''_AND_FT_0_SUC",
  ``!p h L j.
  prob_space p /\
  in_events p L ==>
  (BImp_measure'' p 0 (SUC j) (\a. FTree p (AND (gate_list a))) (h::L) =
     prob p
      (coherent_struct_update (p_space p) j (λa. FTree p (AND (gate_list a)))
         L) −
    prob p (coherent_struct_update ∅ j (λa. FTree p (AND (gate_list a))) L))``,
rw[BImp_measure''_def]
\\ DEP_REWRITE_TAC[BImp_measure'_AND_FT_0_SUC]
\\ fs[in_events_def]
\\ metis_tac[EVENTS_SPACE,EVENTS_EMPTY]);


val BImp_measure''_AND_FT_SUC_0 = store_thm("BImp_measure''_AND_FT_SUC_0",
  ``!p h L i.
  prob_space p /\
  in_events p L ==>
  (BImp_measure'' p (SUC i) 0 (\a. FTree p (AND (gate_list a))) (h::L) =
  BImp_measure p i (λa. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure''_def]
\\ DEP_REWRITE_TAC[BImp_measure'_AND_FT_SUC_0_SPACE,BImp_measure'_AND_FT_SUC_0_EMPTY]
\\ rw[PROB_UNIV,PROB_EMPTY]);


val BImp_measure''_AND_FT_0_SUC = store_thm("BImp_measure''_AND_FT_0_SUC",
  ``!p h L j.
  prob_space p /\
  in_events p L ==>
  (BImp_measure'' p 0 (SUC j) (\a. FTree p (AND (gate_list a))) (h::L) =
  BImp_measure p j (λa. FTree p (AND (gate_list a))) L)``,
rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ rw[FTree_def,gate_list_def,PROB_EMPTY]
\\ rw[]
\\  DEP_REWRITE_TAC[INTER_PSPACE]
\\ rw[EVENTS_EMPTY,EVENTS_SPACE]
\\ DEP_REWRITE_TAC[in_events_AND_gate]
\\ rw[in_events_def,EVENTS_SPACE]
\\ imp_res_tac MEM_LUPDATE_E
\\ fs[in_events_def,EVENTS_EMPTY,EVENTS_SPACE]);


val BImp_measure''_AND_FT_SUC_SUC = store_thm("BImp_measure''_AND_FT_SUC_SUC",
  ``!p h L i j.
  prob_space p /\
  ~NULL L /\
  in_events p (h::L) /\
  mutual_indep p (∅ ::EMPTY::p_space p::p_space p::h::L) ==>
  (BImp_measure'' p (SUC i) (SUC j) (\a. FTree p (AND (gate_list a))) (h::L) =
  prob p h * (BImp_measure' p (p_space p) i j (λa. FTree p (AND (gate_list a))) L -
  BImp_measure' p ∅ i j (λa. FTree p (AND (gate_list a))) L))``,
rw[BImp_measure''_def]
\\ DEP_REWRITE_TAC[BImp_measure'_AND_FT_SUC_SUC]
\\ rw[]
\\ fs[in_events_def,EVENTS_SPACE,EVENTS_EMPTY]
>- (metis_tac[EVENTS_SPACE])
>- (metis_tac[mutual_indep_cons])
>- (metis_tac[EVENTS_EMPTY])
>- (once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[]
   \\ once_rewrite_tac[prove(``!a b c d e f. a ::b::c::d::e::f = [a;b;c]++[d]++e::f``,rw[])]
   \\ irule mutual_indep_append1
   \\ rw[])
\\ REAL_ARITH_TAC);


val BImp_measure_i_lemma = store_thm("BImp_measure_i_lemma",
  ``!p L i j.
~NULL L /\
in_events p L /\
i <> j /\
mutual_indep p (EMPTY::EMPTY::p_space p::p_space p::L) /\
prob_space p ==>
(BImp_measure p i (\a. FTree p (AND (gate_list a))) L =
 prob p (EL j L) * (BImp_measure'' p i j (\a. FTree p (AND (gate_list a))) L) +
 BImp_measure' p (EMPTY) i j (\a. FTree p (AND (gate_list a))) L)``,
gen_tac
\\ Induct
>- (rw[])
\\ rw[]
\\ Cases_on `L`
>- (fs[]
   \\ Cases_on `i`
   >- (Cases_on `j`
      >- (rw[])
      \\ DEP_REWRITE_TAC[BImp_measure_0,BImp_measure''_AND_FT_0_SUC]
      \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ rw[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY]
      \\ rw[])
   \\ Cases_on `j`
   >- (rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   \\ rw[FTree_def,gate_list_def,PROB_EMPTY])
   \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   \\ rw[FTree_def,gate_list_def,PROB_EMPTY])
\\ fs[]
\\ Q.ABBREV_TAC `l' = h'::t`
\\ Cases_on `i`
>- (Cases_on `j`
   >- (rw[])
   \\ sg ` 0 < SUC n` >- (rw[ADD1])
   \\ pop_assum mp_tac
   \\ rewrite_tac[LT_SUC]
   \\ disch_tac
   \\ full_simp_tac std_ss[]
   >- (first_x_assum (mp_tac o Q.SPECL[`0`,`n`])
      \\ fs[prim_recTheory.LESS_NOT_EQ]
      \\ Q.UNABBREV_TAC `l'`
      \\ Cases_on `NULL t`
      >- (fs[NULL_EQ]
      	 \\ Cases_on `n`
	 >- (fs[])
	 \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   	 \\ rw[FTree_def,gate_list_def,PROB_EMPTY]
	 \\ fs[in_events_def,EVENTS_EMPTY]
	 \\ metis_tac[EVENTS_EMPTY])
     \\ Cases_on `n`
     >- (fs[])
     \\ DEP_ASM_REWRITE_TAC[BImp_measure''_AND_FT_0_SUC, BImp_measure'_AND_FT_0_SUC,BImp_measure_0]
     \\ DEP_REWRITE_TAC[ BImp_measure_SUC]
     \\ rw[in_events_def,EVENTS_EMPTY]
     \\ fs[in_events_def]
     >- (once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
      	\\ irule mutual_indep_append2
      	\\ Q.EXISTS_TAC `[p_space p ;h]`
      	\\ rw[]
      	\\ metis_tac[mutual_indep_cons])
     >- (metis_tac[EVENTS_EMPTY])
     >- (metis_tac[EVENTS_EMPTY])
     \\ fs[coherent_struct_update_def,coherent_struct_def,LUPDATE_def]
     \\ rw[FTree_def,gate_list_def,PROB_EMPTY]
     \\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep]
     \\ rw[not_null_lupdate]
     \\ fs[in_events_def]
     >- (metis_tac[mutual_indep_cons])
     >- (metis_tac[in_events_MEM_LUPDATE_EMPTY,in_events_MEM_LUPDATE_SPACE,in_events_def])
     >- (irule mutual_indep_lupdate_cons1
      	\\ once_rewrite_tac[prove(``!a b c d e f. a ::b::c = [a]++b::c``,rw[])]
      	\\ irule mutual_indep_append2
      	\\ Q.EXISTS_TAC `[∅;p_space p;p_space p;h]`
      	\\ rw[]
      	\\ metis_tac[mutual_indep_cons])
    \\ rw[REAL_ARITH ``!a b c e:real. a * (b*c) + b * e = b * ((a * c) + e)``]
    \\ DISJ2_TAC
    \\ first_x_assum (match_mp_tac)
    \\ rw[]
    \\ fs[]
    \\ once_rewrite_tac[prove(``!a b c d e f. a ::b::c::d::e::f = [a;b;c;d]++e::f``,rw[])]
    \\ irule mutual_indep_append2
    \\ Q.EXISTS_TAC `[h]`
    \\ rw[]
    \\ metis_tac[mutual_indep_cons])
  \\ fs[Once EQ_SYM_EQ]
  \\ rewrite_tac[ONE]
  \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
  \\ rewrite_tac[ONE]
  \\ rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY]
  \\ Cases_on `NULL t`
  >- (fs[NULL_EQ]
     \\ rw[FTree_def,gate_list_def,PROB_UNIV]
     \\ DEP_REWRITE_TAC[INTER_PSPACE]
     \\ once_rewrite_tac[INTER_COMM]
     \\ DEP_REWRITE_TAC[INTER_PSPACE]
     \\ fs[in_events_def])
  \\ DEP_REWRITE_TAC[INTER_PSPACE]
  \\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep,EVENTS_INTER,in_events_AND_gate]
  \\ rw[]
  \\ fs[in_events_def]
  \\ metis_tac[mutual_indep_cons])
\\ Cases_on `j`
>- (DEP_REWRITE_TAC[BImp_measure_SUC,BImp_measure''_AND_FT_SUC_0,BImp_measure'_AND_FT_0_SUC ,BImp_measure'_AND_FT_SUC_0_EMPTY]
   \\ rw[]
   >-  (Q.UNABBREV_TAC `l'`
       \\ rw[])
   >- (once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
      \\ irule mutual_indep_append2
      \\ Q.EXISTS_TAC `[p_space p]`
      \\ rw[]
      \\ metis_tac[mutual_indep_cons])
   \\ fs[in_events_def])
\\ DEP_REWRITE_TAC[BImp_measure_SUC,BImp_measure''_AND_FT_SUC_SUC,BImp_measure'_AND_FT_SUC_SUC ,BImp_measure'_AND_FT_SUC_SUC]
\\ rw[]
\\ fs[in_events_def,EVENTS_EMPTY]
>- (once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
      \\ irule mutual_indep_append2
      \\ Q.EXISTS_TAC `[p_space p]`
      \\ rw[]
      \\ metis_tac[mutual_indep_cons])
>-  (Q.UNABBREV_TAC `l'`
     \\ rw[])
>- (metis_tac[EVENTS_EMPTY])
>- (once_rewrite_tac[prove(``!a b c d e. a ::b::c::d::e = [a;b]++[c] ++d::e``,rw[])]
   \\ irule mutual_indep_append1
   \\ irule mutual_indep_append2
   \\ Q.EXISTS_TAC `[p_space p]`
   \\ rw[])
\\ rw[]
\\ rw[REAL_ARITH ``!a b c d e:real. a * (b* (c - d)) + b * e = b * (a * (c-d)+e)``]
\\ DISJ2_TAC
\\ fs[BImp_measure''_def]
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ once_rewrite_tac[prove(``!a b c d e. a ::b::c::d::e = [a;b;c;d]++e``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[h]`
\\ rw[]);






val BImp_measure_j_lemma1 = store_thm("BImp_measure_i_lemma",
  ``!p L i j.
~NULL L /\
in_events p L /\
i < j /\
mutual_indep p (EMPTY::EMPTY::p_space p::p_space p::L) /\
prob_space p ==>
(BImp_measure p j (\a. FTree p (AND (gate_list a))) L =
 prob p (EL i L) * (BImp_measure'' p i j (\a. FTree p (AND (gate_list a))) L))``,
gen_tac
\\ Induct
>- (rw[])
\\ rw[]
\\ Cases_on `L`
>- (fs[]
   \\ Cases_on `i`
   >- (Cases_on `j`
      >- (fs[])
      \\ DEP_REWRITE_TAC[BImp_measure_0,BImp_measure''_AND_FT_0_SUC]
      \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ rw[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY]
      \\ rw[])
   \\ Cases_on `j`
   >- (rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   \\ rw[FTree_def,gate_list_def,PROB_UNIV]
   \\ fs[prim_recTheory.SUC_LESS])
   \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   \\ rw[FTree_def,gate_list_def,PROB_UNIV])
\\ fs[]
\\ Q.ABBREV_TAC `l' = h'::t`
\\ Cases_on `i`
>- (Cases_on `j`
   >- (fs[])
   \\ qpat_x_assum `0 < SUC n` mp_tac
   \\ rewrite_tac[LT_SUC]
   \\ disch_tac
   \\ full_simp_tac std_ss[]
   >- (first_x_assum (mp_tac o Q.SPECL[`0`,`n`])
      \\ fs[prim_recTheory.LESS_NOT_EQ]
      \\ Q.UNABBREV_TAC `l'`
      \\ Cases_on `NULL t`
      >- (fs[NULL_EQ]
      	 \\ Cases_on `n`
	 >- (fs[])
	 \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
   	 \\ rw[FTree_def,gate_list_def,PROB_EMPTY,PROB_UNIV]
	 \\ fs[in_events_def,EVENTS_EMPTY]
	 \\ metis_tac[EVENTS_EMPTY])
     \\ Cases_on `n`
     >- (fs[])
     \\ DEP_ASM_REWRITE_TAC[BImp_measure''_AND_FT_0_SUC, BImp_measure'_AND_FT_0_SUC,BImp_measure_0]
     \\ DEP_REWRITE_TAC[ BImp_measure_SUC]
     \\ rw[in_events_def,EVENTS_EMPTY]
     \\ fs[in_events_def]
     >- (once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
      	\\ irule mutual_indep_append2
      	\\ Q.EXISTS_TAC `[p_space p]`
      	\\ rw[]
      	\\ metis_tac[mutual_indep_cons])
     \\ once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
     \\ irule mutual_indep_append2
     \\ Q.EXISTS_TAC `[p_space p;h]`
     \\ rw[]
     \\ metis_tac[mutual_indep_cons])
  \\ fs[Once EQ_SYM_EQ]
  \\ rewrite_tac[ONE]
  \\ rw[BImp_measure''_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
  \\ rewrite_tac[ONE]
  \\ rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY]
  \\ Cases_on `NULL t`
  >- (fs[NULL_EQ]
     \\ rw[FTree_def,gate_list_def,PROB_UNIV]
     \\ DEP_REWRITE_TAC[INTER_PSPACE]
     \\ once_rewrite_tac[INTER_COMM]
     \\ DEP_REWRITE_TAC[INTER_PSPACE]
     \\ fs[in_events_def])
  \\ DEP_REWRITE_TAC[INTER_PSPACE]
  \\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep,EVENTS_INTER,in_events_AND_gate]
  \\ rw[]
  \\ fs[in_events_def]
  \\  once_rewrite_tac[prove(``!a b. a ::b = [a]++b``,rw[])]
  \\ irule mutual_indep_append2
  \\ Q.EXISTS_TAC `[h']`
  \\ rw[]
  \\ metis_tac[mutual_indep_cons])
\\ Cases_on `j`
>- (DEP_REWRITE_TAC[BImp_measure_SUC,BImp_measure''_AND_FT_SUC_0,BImp_measure'_AND_FT_0_SUC ,BImp_measure'_AND_FT_SUC_0_EMPTY]
   \\ rw[]
   \\ fs[in_events_def])
\\ DEP_REWRITE_TAC[BImp_measure_SUC,BImp_measure''_AND_FT_SUC_SUC,BImp_measure'_AND_FT_SUC_SUC ,BImp_measure'_AND_FT_SUC_SUC]
\\ rw[]
\\ fs[in_events_def,EVENTS_EMPTY]
>- (once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a;b]++c::d``,rw[])]
      \\ irule mutual_indep_append2
      \\ Q.EXISTS_TAC `[p_space p]`
      \\ rw[]
      \\ metis_tac[mutual_indep_cons])
>-  (Q.UNABBREV_TAC `l'`
     \\ rw[])
\\ rw[]
\\ rw[REAL_ARITH ``!a b c d:real. a * (b* (c - d)) = b * (a * (c-d))``]
\\ DISJ2_TAC
\\ fs[BImp_measure''_def]
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ once_rewrite_tac[prove(``!a b c d e. a ::b::c::d::e = [a;b;c;d]++e``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[h]`
\\ rw[]);


val B_Imp'_EMPTY_i_j_0 = store_thm("B_Imp'_EMPTY_i_j_0",
  ``!p L i j.
~NULL L /\
in_events p L /\
i < j /\
mutual_indep p (EMPTY::p_space p::EMPTY::L) /\
prob_space p ==>
(B_Imp' p ∅ i j (λa. FTree p (AND (gate_list a))) L = 0)``,
gen_tac
\\ Induct
>- (rw[])
\\ rw[]
\\ Cases_on `L`
>- (fs[]
   \\ Cases_on `i`
   >- (Cases_on `j`
      >- (fs[])
      \\ rw[BImp_measure''_def,B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ rw[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY])
   \\ Cases_on `j`
   >- (fs[prim_recTheory.SUC_LESS])
   \\ rw[BImp_measure''_def,B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ rw[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY])
\\ fs[]
\\ Cases_on `i`
>- (Cases_on `j`
    >- (fs[])
    \\ rw[BImp_measure''_def,B_Imp'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ rw[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY])
\\  Cases_on `j`
>- (fs[prim_recTheory.SUC_LESS])
\\ DEP_REWRITE_TAC[B_Imp'_AND_FT_SUC_SUC]   
\\ rw[]
\\ fs[in_events_def]
>- (metis_tac[EVENTS_EMPTY])
\\ DISJ2_TAC
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ fs[]
\\ once_rewrite_tac[prove(``!a b c d e. a ::b::c::d::e = [a;b;c]++d::e``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[h]`
\\ rw[]
\\ metis_tac[mutual_indep_cons]);




val BImp_measure_j_lemma = store_thm("BImp_measure_j_lemma",
  ``!p L i j.
~NULL L /\
in_events p L /\
i < j /\
mutual_indep p (EMPTY::EMPTY::p_space p::p_space p::L) /\
prob_space p ==>
(BImp_measure p j (\a. FTree p (AND (gate_list a))) L =
 prob p (EL i L) * (BImp_measure'' p i j (\a. FTree p (AND (gate_list a))) L) +
 B_Imp' p ∅ i j (λa. FTree p (AND (gate_list a))) L)``,
rw[]
\\ DEP_REWRITE_TAC[BImp_measure_j_lemma1]
\\ rw[]
\\ DEP_REWRITE_TAC[B_Imp'_EMPTY_i_j_0]
\\ rw[]
\\ once_rewrite_tac[prove(``!a b c d e. a ::b::c::d = [a;b]++[c] ++ d``,rw[])]
\\ irule mutual_indep_append1
\\ rw[]
\\ once_rewrite_tac[prove(``!a b c d e. a ::b::c::d = [a;b]++c::d``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[p_space p]`
\\ rw[]
\\ metis_tac[]);

val AND_FT_gate_lupdate_empty_0 = store_thm("AND_FT_gate_lupdate_empty_0",
  ``!p L n h.
~NULL L /\ n < LENGTH L /\ prob_space p /\
mutual_indep p (EMPTY::h::L) /\
(!x. MEM x (h::L) ==> x IN events p)
==> (prob p (FTree p (AND (gate_list (LUPDATE ∅ n (h::L))))) = 0)``,
gen_tac
\\ Induct
>- (rw[])
\\ rw[]
\\ Cases_on `n`
>- (rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY])
\\ rw[LUPDATE_def,FTree_def,gate_list_def,PROB_EMPTY]
\\ Cases_on `L`
>- (fs[NULL_EQ])
\\ fs[]
\\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep]
\\ rw[]
\\ fs[]
>- (ho_match_mp_tac not_null_lupdate
   \\ rw[])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[EVENTS_EMPTY])
   \\ fs[])
>- (irule mutual_indep_lupdate_cons1
   \\ rw[])
\\ DISJ2_TAC
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ fs[]
\\ once_rewrite_tac[prove(``!a b c d. a ::b::c::d = [a]++b::c::d``,rw[])]
\\ irule mutual_indep_append2   
\\ Q.EXISTS_TAC `[h']`
\\ rw[]);


val Boland_Imp_measure_cons = store_thm("Boland_Imp_measure_cons",
  ``!p h h' L i j.
in_events p (h::h'::L) /\
j < LENGTH L /\
i < j /\
mutual_indep p (EMPTY::p_space p::h::h'::L) /\
prob_space p ==>
(prob p (coherent_struct_update2 (p_space p) (EMPTY) i j (λa. FTree p (AND (gate_list a))) (h::h'::L)) =
prob p (coherent_struct_update2 EMPTY (p_space p) i j (λa. FTree p (AND (gate_list a))) (h::h'::L)))``,
gen_tac
\\ Induct_on `L`
>- (rw[])
\\ rw[]
\\ Cases_on `i`
>- (Cases_on `j`
    >- (fs[])
    \\ fs[BImp_measure''_def,B_Imp'_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
      \\ fs[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY]
      \\ DEP_REWRITE_TAC[INTER_PSPACE]
      \\ rw[]
      >- (DEP_REWRITE_TAC[in_events_AND_gate]
      	 \\ rw[in_events_def]
	 \\ imp_res_tac MEM_LUPDATE_E
	 >- (metis_tac[EVENTS_EMPTY])
	 \\ fs[])
      \\ DEP_REWRITE_TAC[AND_FT_gate_lupdate_empty_0]
      \\ rw[]
      \\ fs[]
      \\ once_rewrite_tac[prove(``!a b c. a ::b::c::d = [a]++b::c::d``,rw[])]
      \\ irule mutual_indep_append2
      \\ rw[]
      \\ Q.EXISTS_TAC `[p_space p;h']`
      \\ rw[])
\\ Cases_on `j`
>- (fs[])
\\ fs[BImp_measure''_def,B_Imp'_def,BImp_measure'_def,coherent_struct_update2_def,coherent_struct_def,LUPDATE_def,BImp_measure_def,coherent_struct_update_def]
\\ fs[FTree_def,gate_list_def,PROB_EMPTY,in_events_def,EVENTS_EMPTY]
\\ DEP_REWRITE_TAC[AND_FT_gate_cons_indep]
\\ rw[not_null_lupdate]
\\ fs[]
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[EVENTS_EMPTY])
   \\ imp_res_tac MEM_LUPDATE_E
   \\ fs[]
   \\ metis_tac[EVENTS_EMPTY,EVENTS_SPACE])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[]
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c::d::e::f = [a]++[b]++c::d::e::f``,rw[])]
   \\ irule mutual_indep_append1
   \\ rw[])
>- (imp_res_tac MEM_LUPDATE_E
   >- (metis_tac[EVENTS_EMPTY,EVENTS_SPACE])
   \\ imp_res_tac MEM_LUPDATE_E
   \\ fs[]
   \\ metis_tac[EVENTS_EMPTY,EVENTS_SPACE])
>- (irule mutual_indep_lupdate_cons1
   \\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
   \\ irule mutual_indep_append_lupdate1
   \\ rw[])
\\ DISJ2_TAC
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ fs[]
\\ once_rewrite_tac[prove(``!a b c. a ::b::c = [a;b]++c``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[h']`
\\ rw[]);

val Borland_Imp_measure_eq = store_thm("Borland_Imp_measure_eq",
  `` !p L i j.
in_events p L /\
SUC (SUC j) < LENGTH L /\
i < j /\
mutual_indep p (EMPTY::p_space p::L) /\
prob_space p ==>
(prob p (coherent_struct_update2 (p_space p) (EMPTY) i j (λa. FTree p (AND (gate_list a))) L) =
prob p (coherent_struct_update2 EMPTY (p_space p) i j (λa. FTree p (AND (gate_list a))) L)) ``,
rw[]
\\ Cases_on `L`
>- (fs[])
\\ Cases_on `t`
>- (fs[])
\\ irule Boland_Imp_measure_cons
\\ fs[]);


val perm_equi_comps_def = Define
`perm_equi_comps p i j L =
(prob p
  (coherent_struct_update2 (p_space p) ∅ i j
     (λa. FTree p (AND (gate_list a))) L) = 
prob p
  (coherent_struct_update2 ∅ (p_space p) i j
     (λa. FTree p (AND (gate_list a))) L))`;


val BImp_measure_gt = store_thm("BImp_measure_gt",
  ``!p L i j.
~NULL L /\
in_events p L /\
i < j /\
mutual_indep p (EMPTY::EMPTY::p_space p::p_space p::L) /\
prob_space p /\
perm_equi_comps p i j L /\
0 <= BImp_measure'' p i j (λa. FTree p (AND (gate_list a))) L /\
(prob p (EL i L) <= prob p (EL j L)) ==>
(0 <= BImp_measure p i (λa. FTree p (AND (gate_list a))) L -
 BImp_measure p j (λa. FTree p (AND (gate_list a))) L) ``,
rw[]
\\ DEP_REWRITE_TAC[BImp_measure_i_lemma,BImp_measure_j_lemma]
\\ rw[]
\\ rw[REAL_ARITH ``!a b c d e:real. a * b + c - (d * b + e) = (a - d) * b + c - e``]
\\ rw[BImp_measure'_def, B_Imp'_def]
\\ rw[REAL_ARITH ``!a b c i e:real. i * e + (a  - b) - (c - b) = i * e + a - c``]
\\ fs[perm_equi_comps_def]
\\ once_asm_rewrite_tac[]
\\ rw[REAL_ARITH ``!a b c i e:real. i * e + a  - a = i * e + 0``]
\\ DEP_REWRITE_TAC [REAL_LE_MUL]
\\ rw[REAL_SUB_LE]);


val BImp_measure_le = store_thm("BImp_measure_le",
  ``!p L i j.
~NULL L /\
in_events p L /\
SUC (SUC j) < LENGTH L /\
i < j /\
mutual_indep p (EMPTY::EMPTY::p_space p::p_space p::L) /\
prob_space p /\
0 <= BImp_measure'' p i j (λa. FTree p (AND (gate_list a))) L /\
(prob p (EL i L) <= prob p (EL j L)) ==>
(BImp_measure p j (λa. FTree p (AND (gate_list a))) L <=
 BImp_measure p i (λa. FTree p (AND (gate_list a))) L)``,
rw[]
\\ once_rewrite_tac[GSYM REAL_SUB_LE]
\\ irule BImp_measure_gt
\\ rw[]
\\ rw[perm_equi_comps_def]
\\ irule Borland_Imp_measure_eq
\\ rw[]
\\ once_rewrite_tac[prove(``!a b c. a::b::c = [a] ++ b::c``,rw[])]
\\ irule mutual_indep_append2
\\ Q.EXISTS_TAC `[EMPTY;p_space p]`
\\ rw[]);

val _  = export_theory();


