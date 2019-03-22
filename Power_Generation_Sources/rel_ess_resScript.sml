(* ========================================================================= *)
(* File Name: rel_ess_resScript.sml	                                     *)
(*---------------------------------------------------------------------------*)
(* Description:                                                              *)
(*                                                                           *)
(*                                                                           *)
(*                HOL4-Kananaskis 11 		 			     *)
(*									     *)
(*		Author :  Waqar Ahmad             		     	     *)
(*                                              			     *)
(* 	    School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*	    National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                          		               	     *)
(*                                                                           *)
(* ========================================================================= *)

(*loadPath := ["/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal-Dependability-K11/Formal-Dependability"] @ !loadPath;
(*loadPath := "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal-Dependability-K11/Formal-Dependability" :: !loadPath;
loadPath := "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/UAE_project/HOL_script" :: !loadPath; *)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","RBDTheory","FT_deepTheory","VDCTheory","railwayTheory","AvailabilityTheory","smart_grid_inequivalityTheory"];

*)
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory RBDTheory FT_deepTheory VDCTheory railwayTheory AvailabilityTheory smart_grid_inequivalityTheory; 
open HolKernel boolLib bossLib Parse;

val _ = new_theory "rel_ess_res";

(*--------------------------*)
val pop_orw = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*--------------------------*)

val disc_event_list_def = Define
`disc_event_list p r L = MAP (\a. PREIMAGE a {Normal (&r)}) L`;

val binomial_dist_event_def = Define
`binomial_dist_event X p k n =
BIGUNION
       (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
          {x | k <= x /\ x < SUC n})`;

val combined_ESS_RES_event_def = Define
`combined_ESS_RES_event p r k n z X L1 L2 =
 big_inter p (disc_event_list p r L1) INTER
  binomial_dist_event X p k n INTER
  union_pair_disj_events1 p L2 n z`;

val mutual_indep_disj_pair_events_append_list_def = Define 
`mutual_indep_disj_pair_events_append_list p n P1 Q1 L L1 = 
(!x. MEM x (pair_wise_indep_events_list P1 Q1 L) ==>
 pred_disj_pair_events x n L) /\
 mutual_indep p (L1 ++ pair_wise_indep_events_list P1 Q1 L)`;


(* ------------------------------------------------------------------------- *)
(* Definition  Probability Mass Function                                  *)
(* ------------------------------------------------------------------------- *)
val Pmf_def = Define
 `Pmf p X (x) = distribution p X {y | y =  Normal &x}`;

val FOG_avail_def = Define
`FOG_avail p X m = !t. (Pmf p X (t) = steady_state_avail m)`;

val pred_FOG_avail_def = Define
`(pred_FOG_avail p []  = T) /\
 (pred_FOG_avail p (h::t) =
 FOG_avail p (FST h) (SND h) /\ pred_FOG_avail p t)`;

val rv_list_def = Define
`rv_list L = MAP (\a. FST a) L`;

val fail_rep_list_def = Define
`fail_rep_list L = MAP (\a. SND a) L`;


val rv_list1_def = Define
`rv_list1 (l1,l2) =  if ~NULL l1  then l1 else []`;

val fail_rep_list1_def = Define
`fail_rep_list1 (l1,l2) = if ~NULL l2  then l2 else []`;

(*----------------------*)
val rel_ESS_RES_lemma1 = store_thm("rel_ESS_RES_lemma1",
  ``!p L1 L2 (X:'b->extreal) k r n z.
    prob_space p /\ ~NULL L1 /\ ~NULL L2 /\
    in_events p (disc_event_list p r L1 ++
      [binomial_dist_event X p k n; union_pair_disj_events1 p L2 n z]) /\
    mutual_indep p
    (disc_event_list p r L1 ++
    [binomial_dist_event X p k n; union_pair_disj_events1 p L2 n z])  ==>
  (prob p (combined_ESS_RES_event p r k n z X L1 L2) =
    prob p (big_inter p (disc_event_list p r L1)) *
    prob p (binomial_dist_event X p k n) *
    prob p (union_pair_disj_events1 p L2 n z))``,
rw[combined_ESS_RES_event_def]
\\ `(big_inter p (disc_event_list p r L1) INTER binomial_dist_event X p k n INTER
   union_pair_disj_events1 p L2 n z) = (rbd_struct p (series (rbd_list ((disc_event_list p r L1)++ (binomial_dist_event X p k n :: [union_pair_disj_events1 p L2 n z])))))` by RW_TAC std_ss[]
>- (DEP_REWRITE_TAC[GSYM series_rbd_append]
   \\ DEP_REWRITE_TAC[parallel_lem5]
   \\ rw[] \\ fs[in_events_def]
   \\ rw[big_inter_def]
   \\ `(union_pair_disj_events1 p L2 n z INTER p_space p) = union_pair_disj_events1 p L2 n z` by (once_rewrite_tac[INTER_COMM] \\ DEP_REWRITE_TAC[INTER_PSPACE])
   >- (fs[])
   \\ pop_orw
   \\ rw[INTER_ASSOC])
\\ pop_orw
\\  DEP_REWRITE_TAC[series_rbd_append2]
\\ rw[disc_event_list_def]
\\ fs[in_events_def,disc_event_list_def]
>- (match_mp_tac not_null_map
   \\ rw[])
\\ `prob p
  (rbd_struct p
     (series (rbd_list (MAP (\a. PREIMAGE a {Normal (&r)}) L1)))) =
    prob p (big_inter p (MAP (\a. PREIMAGE a {Normal (&r)}) L1))` by rw[series_rbd_eq_big_inter]
\\ pop_orw
\\ rw[GSYM REAL_MUL_ASSOC]
\\ DISJ2_TAC
\\ DEP_REWRITE_TAC[series_struct_thm]
\\ rw[disc_event_list_def,not_null_map]
\\ fs[in_events_def,disc_event_list_def]
>- (match_mp_tac mutual_indep_front_append
   \\ Q.EXISTS_TAC `MAP (\a. PREIMAGE a {Normal (&r)}) L1`
   \\ rw[])
\\ rw[list_prod_def,list_prob_def]);
(*----------------------*)


(*----------------------*)
val rel_ESS_RES_lemma2 = store_thm("rel_ESS_RES_lemma2",
  ``!p L1 L2 (X:'b->extreal) k r n z P Q.
    prob_space p /\ ~NULL L1 /\ ~NULL L2 /\
    in_events p (disc_event_list p r L1 ++
      [binomial_dist_event X p k n; union_pair_disj_events1 p L2 n z]) /\
       ((!z x.
     z < n /\ x < n /\ z < x /\
     (!X.
        MEM X L2 ==> PREIMAGE X {Normal (&z - &x)} IN events p) /\
     !Y. MEM Y L2 ==> PREIMAGE Y {Normal (&x)} IN events p)) /\
     mutual_indep_disj_pair_events_append_list p n P Q L2
         (binomial_dist_event X p k n::
              disc_event_list p r L1)  ==>
  (prob p (combined_ESS_RES_event p r k n z X L1 L2) =
    prob p (big_inter p (disc_event_list p r L1)) *
    prob p (binomial_dist_event X p k n) *
    prob p (union_pair_disj_events1 p L2 n z))``,
rw[combined_ESS_RES_event_def]
\\  `(big_inter p (disc_event_list p r L1) INTER binomial_dist_event X p k n INTER
   union_pair_disj_events1 p L2 n z) =
   big_inter p (binomial_dist_event X p k n::disc_event_list p r L1) INTER
   union_pair_disj_events1 p L2 n z` by rw[big_inter_def]
>- (rw[INTER_COMM])
\\ pop_orw
\\ rw[union_pair_disj_events_alt_symb_form]
\\ Cases_on `L2`
>- (rw[symb_union_pair_disj_def]
   \\ rw[big_inter_def,PROB_UNIV]
   \\ once_rewrite_tac[INTER_COMM] \\ DEP_REWRITE_TAC[INTER_PSPACE]
   \\ DEP_REWRITE_TAC[EVENTS_INTER]
   \\ fs[in_events_def])
\\ DEP_REWRITE_TAC[big_inter_indep_symb_union_pair_disj]
\\ rw[]
>-  (Q.EXISTS_TAC `P`
    \\ Q.EXISTS_TAC `Q`
    \\ rw[]
    \\ fs[in_events_def]
    >- (fs[pred_mutual_indep_pair_events_def,mutual_indep_disj_pair_events_append_list_def]
       \\ rw[]
       \\ DEP_REWRITE_TAC[pred_disj_pair_events_implies_pred_pair1]
       \\ rw[])
    \\ rw[union_disj_pair2_thm])
\\ DISJ2_TAC 
\\ `(big_inter p (binomial_dist_event X p k n ::disc_event_list p r L1)  = (rbd_struct p (series (rbd_list ((disc_event_list p r L1)++ [(binomial_dist_event X p k n)])))))` by RW_TAC std_ss[]
>- (DEP_REWRITE_TAC[GSYM series_rbd_append]
   \\ DEP_REWRITE_TAC[parallel_lem5]
   \\ rw[] \\ fs[in_events_def]
   \\ rw[big_inter_def]
   \\ `(binomial_dist_event X p k n INTER p_space p) = binomial_dist_event X p k n` by (once_rewrite_tac[INTER_COMM] \\ DEP_REWRITE_TAC[INTER_PSPACE])
   >- (fs[])
   \\ pop_orw
   \\ rw[INTER_ASSOC,INTER_COMM])
\\ pop_orw
\\  DEP_REWRITE_TAC[series_rbd_append2]
\\ rw[disc_event_list_def]
\\ fs[in_events_def,disc_event_list_def]
>- (match_mp_tac not_null_map
   \\ rw[])
>- (fs[mutual_indep_disj_pair_events_append_list_def]
   \\ match_mp_tac mutual_indep_front_append
   \\ Q.EXISTS_TAC `pair_wise_indep_events_list P Q (h::t)`
   \\ rw[]
   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
   \\ match_mp_tac mutual_indep_append_sym
   \\ match_mp_tac mutual_indep_append1
   \\ rw[])
\\ rw[rbd_struct_def,rbd_list_def]
\\ `prob p
  (rbd_struct p
     (series (rbd_list (MAP (\a. PREIMAGE a {Normal (&r)}) L1)))) =
    prob p (big_inter p (MAP (\a. PREIMAGE a {Normal (&r)}) L1))` by rw[series_rbd_eq_big_inter]
\\ pop_orw
\\ rw[GSYM REAL_MUL_ASSOC]
\\ DISJ2_TAC
\\ `(binomial_dist_event X p k n INTER p_space p) = binomial_dist_event X p k n` by (once_rewrite_tac[INTER_COMM] \\ DEP_REWRITE_TAC[INTER_PSPACE])
>- (fs[])
\\ pop_orw
\\ rw[]);


(*----------------------*)
val rel_ESS = store_thm("rel_ESS",
  ``!p L r M.
prob_space p /\
~NULL L /\
in_events p (disc_event_list p r (rv_list L)) /\
mutual_indep p (disc_event_list p r (rv_list L)) /\
pred_FOG_avail p (L :((α -> extreal) # real # real) list) ==>
(prob p (big_inter p (disc_event_list p r (rv_list L))) =
list_prod (steady_state_avail_list (fail_rep_list L)))``,
rw[]
\\ Induct_on `L`
>- (rw[])
\\ rw[disc_event_list_def,rv_list_def,fail_rep_list_def,steady_state_avail_list_def]
\\ ` (PREIMAGE (FST h) {Normal (&r)}::
                MAP (\a. PREIMAGE a {Normal (&r)})
                  (MAP (\a. FST a) L)) =  ([PREIMAGE (FST h) {Normal (&r)}]++
                MAP (\a. PREIMAGE a {Normal (&r)})
                  (MAP (\a. FST a) L))` by rw[APPEND]
\\ pop_orw
\\ simp_tac std_ss[GSYM parallel_lem5]
\\ Cases_on `L`
>- (fs[rbd_struct_def,rbd_list_def,list_prod_def,steady_state_avail_def,steady_state_avail_list_def,pred_FOG_avail_def,distribution_def,FOG_avail_def,Pmf_def])
\\ DEP_REWRITE_TAC[series_rbd_append2]
\\ rw[disc_event_list_def,not_null_map]
\\ fs[in_events_def,disc_event_list_def]
\\ rw[list_prod_def]
\\ `prob p
  (rbd_struct p (series (rbd_list [PREIMAGE (FST h) {Normal (&r)}]))) =
  steady_state_avail (SND h)` by fs[rbd_struct_def,rbd_list_def,list_prod_def,steady_state_avail_def,steady_state_avail_list_def,pred_FOG_avail_def,distribution_def,FOG_avail_def,Pmf_def]
\\ pop_orw
\\ rw[]
\\ DISJ2_TAC
\\ fs [GSYM in_events_def]
\\ ` in_events p
        (MAP (\a. PREIMAGE a {Normal (&r)}) (rv_list (h'::t))) /\
      mutual_indep p
        (MAP (\a. PREIMAGE a {Normal (&r)}) (rv_list (h'::t))) /\
      pred_FOG_avail p (h'::t)` by  fs[rbd_struct_def,rbd_list_def,list_prod_def,steady_state_avail_def,steady_state_avail_list_def,pred_FOG_avail_def,distribution_def,FOG_avail_def,Pmf_def,rv_list_def,in_events_def]
>- (rw[] \\ fs[]
   \\ match_mp_tac mutual_indep_cons
   \\ Q.EXISTS_TAC `PREIMAGE (FST h) {Normal (&r)}`
   \\ rw[])
\\ fs[]
\\ rw[parallel_lem5]
\\ fs[rv_list_def,fail_rep_list_def]);
(*----------------------*)

val rel_ESS_bino_dist = store_thm("rel_ESS_bino_dist",
  ``!p p' k n r X_bino X_RES.
prob_space p /\ k < SUC n /\
 (\x. PREIMAGE (X_bino) {Normal (&x)} INTER p_space p) IN
 (count (SUC n) -> events p) /\
 (!x.
    distribution p X_bino {Normal (&x)} =
    &binomial n x * prob p' (PREIMAGE (FST X_RES) {Normal (&r)} INTER p_space p') pow x *
    (1 - prob p' (PREIMAGE (FST X_RES) {Normal (&r)} INTER p_space p')) pow (n - x)) /\
    FOG_avail p' (FST X_RES) (SND X_RES) ==>
(prob p (binomial_dist_event X_bino p k n) =
sum (k,SUC n - k)
        (\x. &binomial n x * (steady_state_avail (SND X_RES)) pow x * (1 - (steady_state_avail (SND (X_RES:('a->extreal)#real#real)))) pow (n - x)))``,
rw[]
\\ MP_TAC (Q.ISPECL[`p :'b event # 'b event event # ('b event -> real)`,`n:num`,`k:num`,`X_bino:'b->extreal`,`prob p' (PREIMAGE (FST (X_RES:('a->extreal)#real#real)) {Normal (&r)} INTER p_space p')`] k_out_n_RBD_v1)
\\ rw[]
\\ fs[binomial_dist_event_def,K_out_N_struct_def]
\\ fs[FOG_avail_def,distribution_def,Pmf_def]);

(*----------------------*)
val n_times_steady_state_avail_prod_def = Define
`(n_times_steady_state_avail_prod [] n = 1) /\
(n_times_steady_state_avail_prod (h::[]) n = steady_state_avail h)  /\
(n_times_steady_state_avail_prod (h::t) n = (real_of_num n * steady_state_avail h) * n_times_steady_state_avail_prod t n)`;


(*----------------------*)
val rel_conven_generators_lemma1 = store_thm("rel_conven_generators_lemma1",
  ``!n p h t P Q.
prob_space p /\
(!z x.
              z < n /\ x < n /\ z < x /\ 0 < n /\
              (!X.
                 MEM X (rv_list (h::t)) ==>
                 PREIMAGE X {Normal (&z - &x)} IN events p) /\
              !Y.
                MEM Y (rv_list (h::t)) ==>
                PREIMAGE Y {Normal (&x)} IN events p) /\
           mutual_indep_disj_pair_events p n P Q (rv_list (h::t)) /\
           pred_FOG_avail p (h::t) ==>
     (sum (0,n) (\x. nsum_pair_disj_events1 p (rv_list (h::t)) n x) =
     &n * n_times_steady_state_avail_prod (fail_rep_list (h::t)) n)``,
 Induct_on `t`
>- (rw[n_times_steady_state_avail_prod_def,nsum_pair_disj_events1_def,steady_state_avail_prod_def,rv_list_def,fail_rep_list_def]
\\ fs[pred_FOG_avail_def,FOG_avail_def,Pmf_def,distribution_def]
\\ `!x. steady_state_avail (SND h) = steady_state_avail (SND h) * (\a. 1 ) x` by rw[]
\\ pop_orw
\\ rw[SUM_CMUL]
\\ Cases_on `n`
>- (rw[sum,n_times_steady_state_avail_prod_def]
   \\ fs[])
\\ rw[SUM_C_EQ,n_times_steady_state_avail_prod_def,ADD1]
\\ REAL_ARITH_TAC)
\\ rw[n_times_steady_state_avail_prod_def,nsum_pair_disj_events1_def,steady_state_avail_prod_def,rv_list_def,fail_rep_list_def]
\\ `!x x'. prob p (PREIMAGE (FST h') {Normal (&x - &x')} INTER p_space p) = steady_state_avail (SND h')` by rw[]
>- (fs[pred_FOG_avail_def,FOG_avail_def,Pmf_def,distribution_def]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(x - x'):num`] MP_TAC)
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(x - x'):num`] MP_TAC)
   \\ rw[]
   \\ `real_of_num x - real_of_num x' = real_of_num (x - x')` by rw[]
     >- (once_rewrite_tac [REAL_SUB]
     	\\ rw[]
	\\ FIRST_X_ASSUM (Q.SPECL_THEN [`x':num`, `x:num`] MP_TAC)
	\\ rw[])
   \\ rw[])
\\ `!x. sum (0,n)
       (\x'.
          prob p (PREIMAGE (FST h') {Normal (&x - &x')} INTER p_space p) *
          nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n x') =
	 sum (0,n)
       (\x'.
          steady_state_avail (SND h') *
          nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n x') ` by rw[]
\\ pop_orw
\\ `!x'. steady_state_avail (SND h') *
          nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n x' =
	  steady_state_avail (SND h') *
          (\a. nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n a) x' ` by rw[]
\\ pop_orw
\\ rw[SUM_CMUL]
\\  Cases_on `n`
>- (rw[sum,n_times_steady_state_avail_prod_def]
   \\ fs[])
\\ rw[SUM_C_EQ,n_times_steady_state_avail_prod_def,ADD1]
\\ rw[GSYM ADD1]
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`(SUC n' :num)`, `(p :α event # α event event # (α event -> real))`,
         `(h :(α -> extreal) # real # real)`,
         `(P :(α -> extreal) -> α event)`, `(Q :(α -> extreal) -> α event)`] MP_TAC)
\\ rw[]
\\ FULL_SIMP_TAC std_ss[GSYM MEM]
\\ `(!z x.
         (!X.
            MEM X (rv_list (h::t)) ==>
            PREIMAGE X {Normal (&z - &x)} IN events p) /\
         !Y.
           MEM Y (rv_list (h::t)) ==>
           PREIMAGE Y {Normal (&x)} IN events p) /\
      mutual_indep_disj_pair_events p (SUC n') P Q (rv_list (h::t)) /\
      pred_FOG_avail p (h::t)` by ALL_TAC
>-(rw[] \\ fs[rv_list_def,mutual_indep_disj_pair_events_def,pred_FOG_avail_def]
\\ rw[]
  \\ fs[mutual_indep_disj_pair_events_def,pair_wise_indep_events_list_def]
  \\ rw[]
  \\ fs[pair_wise_indep_events_list_def,pred_disj_pair_events_def]
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [`x`] MP_TAC)
\\ rw[]
\\ match_mp_tac mutual_indep_cons
  \\ Q.EXISTS_TAC `Q (FST h')`
  \\ metis_tac[])
\\ fs[]
\\ fs[rv_list_def]
\\ rw[fail_rep_list_def]
\\ REAL_ARITH_TAC);
(*-----------------------*)
val rel_conv_generators = store_thm("rel_conv_generators",
  ``!p n L P Q z.
  (!z x.
     z < n /\ x < n /\ z < x /\
     (!X.
        MEM X (rv_list L) ==> PREIMAGE X {Normal (&z - &x)} IN events p) /\
     !Y. MEM Y (rv_list L) ==> PREIMAGE Y {Normal (&x)} IN events p) /\
  mutual_indep_disj_pair_events p n P Q (rv_list L) /\ prob_space p /\
  pred_FOG_avail p (L :((α -> extreal) # real # real) list) ==>
(prob p (union_pair_disj_events1 p (rv_list L)  n z) =
n_times_steady_state_avail_prod (fail_rep_list L) n)``,
rw[]
\\ DEP_REWRITE_TAC[prob_sum_of_indep_rvs_list]
\\ rw[]
>- (Q.EXISTS_TAC `P`
   \\ Q.EXISTS_TAC `Q`
   \\ rw[])
\\ Induct_on `L`
>- (rw[nsum_pair_disj_events1_def,steady_state_avail_prod_def,rv_list_def,fail_rep_list_def,n_times_steady_state_avail_prod_def])
\\ Cases_on `L`
>- (rw[nsum_pair_disj_events1_def,steady_state_avail_prod_def,rv_list_def,fail_rep_list_def,nsum_pair_disj_events1_def,n_times_steady_state_avail_prod_def]
   \\ fs[pred_FOG_avail_def,FOG_avail_def,Pmf_def,distribution_def])
\\ rw[nsum_pair_disj_events1_def,steady_state_avail_prod_def,rv_list_def,fail_rep_list_def,nsum_pair_disj_events1_def,n_times_steady_state_avail_prod_def]
\\ `!x. prob p (PREIMAGE (FST h') {Normal (&z - &x)} INTER p_space p) =
        steady_state_avail (SND h')` by rw[]

>- (fs[pred_FOG_avail_def,FOG_avail_def,Pmf_def,distribution_def]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(z - x):num`] MP_TAC)
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(z - x):num`] MP_TAC)
   \\ rw[]
   \\ `real_of_num z - real_of_num x = real_of_num (z - x)` by rw[]
     >- (once_rewrite_tac [REAL_SUB]
     	\\ rw[]
	\\ FIRST_X_ASSUM (Q.SPECL_THEN [`x:num`, `z:num`] MP_TAC)
	\\ rw[])
   \\ rw[])
\\ rw[]
\\ `!x. nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n x =
       (\a. nsum_pair_disj_events1 p (FST h::MAP (\a. FST a) t) n a) x` by rw[]
\\ pop_orw
\\ rw[SUM_CMUL]
\\ rw[GSYM rv_list_def, GSYM nsum_pair_disj_events1_def]
\\ `(FST h::rv_list t) = (rv_list (h::t))` by rw[rv_list_def]
\\ pop_orw
\\ DEP_REWRITE_TAC[rel_conven_generators_lemma1]
\\ rw[]
>- (Q.EXISTS_TAC `P`
\\ Q.EXISTS_TAC `Q`
\\ rw[]
\\ fs[rv_list_def,mutual_indep_disj_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def]
>-(match_mp_tac mutual_indep_cons
  \\ Q.EXISTS_TAC `Q (FST h')`
  \\ metis_tac[])
\\ fs[pred_FOG_avail_def])
\\ rw[fail_rep_list_def]
\\ REAL_ARITH_TAC);


(*----------------------*)
val Pred_FOR_append = store_thm("Pred_FOR_append",
  ``!L1 L2 p. pred_FOG_avail p (L1 ++ L2) = pred_FOG_avail p L1 /\ pred_FOG_avail p L2  ``,

Induct
>-(rw[pred_FOG_avail_def])
\\ rw[pred_FOG_avail_def]
\\ metis_tac[]);

(*----------------------*)

val pred_disj_pair_eq_pred_pair_events = store_thm(
  "pred_disj_pair_eq_pred_pair_events",
  ``!x n L.
     pred_disj_pair_events x n L =
     pred_pair_events x (\z h. PREIMAGE h {Normal (&z)})
       (\h z x. PREIMAGE h {Normal (&z - &x)}) n L  ``,
Induct_on `L`
>-(rw[pred_disj_pair_events_def, pred_pair_events_def])
\\ Cases_on `L`
>-(rw[pred_disj_pair_events_def, pred_pair_events_def])
\\ rw[pred_disj_pair_events_def, pred_pair_events_def]
\\ metis_tac[]);
(*----------------------*)
val Rel_of_comb_ESS_RES_GEN_power_plant = store_thm(
  "Rel_of_comb_ESS_RES_GEN_power_plant",
  ``!p p' r k n z (X_bino) (L1:(('b->extreal)#real#real) list) L2 X_RES P Q.
prob_space p /\ ~NULL L1 /\ ~NULL L2 /\ in_events p ((binomial_dist_event X_bino p k n::disc_event_list p r (rv_list L1))) /\
 ((!z x.
     z < n /\ x < n /\ z < x /\
     (!X.
        MEM X (rv_list L2) ==> PREIMAGE X {Normal (&z - &x)} IN events p) /\
     !Y. MEM Y (rv_list L2) ==> PREIMAGE Y {Normal (&x)} IN events p)) /\
(k < SUC n /\
        (\x. PREIMAGE X_bino {Normal (&x)} INTER p_space p) IN
        (count (SUC n) -> events p) /\
        (!x.
           distribution p X_bino {Normal (&x)} =
           &binomial n x *
           prob p' (PREIMAGE (FST X_RES) {Normal (&r)} INTER p_space p') pow
           x *
           (1 -
            prob p'
              (PREIMAGE (FST X_RES) {Normal (&r)} INTER p_space p')) pow
           (n - x)) /\ FOG_avail p' (FST X_RES) (SND X_RES) /\ pred_FOG_avail p (L1 ++ L2)) /\
mutual_indep_disj_pair_events_append_list p n P Q (rv_list L2) ((binomial_dist_event X_bino p k n::disc_event_list p r (rv_list L1)))
==>
(prob p (combined_ESS_RES_event p r k n z X_bino (rv_list L1) (rv_list L2)) =
list_prod (steady_state_avail_list (fail_rep_list L1)) *
sum (k,SUC n - k)
        (\x. &binomial n x * (steady_state_avail (SND X_RES)) pow x * (1 - (steady_state_avail (SND (X_RES:('a->extreal)#real#real)))) pow (n - x)) *
n_times_steady_state_avail_prod (fail_rep_list L2) n)``,

rw[]
\\ DEP_REWRITE_TAC[rel_ESS_RES_lemma2]
\\ DEP_REWRITE_TAC[rel_conv_generators]
\\ DEP_REWRITE_TAC[rel_ESS_bino_dist]
\\ DEP_REWRITE_TAC[rel_ESS]
\\ rw[]
\\ fs[in_events_def,Pred_FOR_append,mutual_indep_disj_pair_events_append_list_def]
>- (match_mp_tac mutual_indep_cons
   \\ Q.EXISTS_TAC `binomial_dist_event X_bino p k n`
   \\ match_mp_tac mutual_indep_front_append
   \\ Q.EXISTS_TAC `pair_wise_indep_events_list P Q (rv_list L2)`
   \\ match_mp_tac mutual_indep_append_sym
   \\ rw[])
>- (Q.EXISTS_TAC `p'`
   \\ Q.EXISTS_TAC `r`
   \\ rw[])
>- (Q.EXISTS_TAC `P`
   \\ Q.EXISTS_TAC `Q`
   \\ fs[Pred_FOR_append]
   \\ fs[mutual_indep_disj_pair_events_def,mutual_indep_disj_pair_events_append_list_def]
   \\ match_mp_tac mutual_indep_front_append
   \\ Q.EXISTS_TAC `binomial_dist_event X_bino p k n::
              (disc_event_list p r (rv_list L1))`
   \\ fs[])
\\ Q.EXISTS_TAC `P`
\\ Q.EXISTS_TAC `Q`
\\ rw[]
\\ fs[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,Pred_FOR_append,rv_list_def,not_null_map]
\\ match_mp_tac in_events_union_pair_disj_events
\\ rw[]
\\ fs[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
\\ rw[]
\\ once_rewrite_tac[INTER_COMM] \\ DEP_REWRITE_TAC[INTER_PSPACE]
 \\ rw[]);

val _ = export_theory();
