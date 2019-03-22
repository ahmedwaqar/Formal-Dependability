(* ========================================================================= *)
(* File Name: smart-grid_inequivality.sml                                    *)
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
(*loadPath := "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal-Dependability-K11/Formal-Dependability" :: !loadPath;


app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","RBDTheory","FT_deepTheory","VDCTheory"];*)
	  
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory RBDTheory FT_deepTheory VDCTheory;
open HolKernel boolLib bossLib Parse;

val _ = new_theory "smart_grid_inequivality";

(*--------------------------*)
val pop_orw = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*--------------------*)
val pair_disj_events_def = Define 
`pair_disj_events p X Y k z = (PREIMAGE X {Normal (&k)} INTER 
		      	      (PREIMAGE Y {Normal (z - &k)})) `;

val union_pair_disj_events_def = Define 
`union_pair_disj_events p X Y n z = BIGUNION
        (IMAGE (\x. pair_disj_events p X Y x z  INTER p_space p)
           (count n))`;

val disj_pair_lem1 = store_thm("disj_pair_lem1",
  ``!a b c. a INTER (b INTER c) = a INTER b INTER (a INTER c)  ``,
rw[]\\ SRW_TAC[][INTER_DEF,EXTENSION,GSPECIFICATION]\\ METIS_TAC[]);

val prob_disj_pair_events = store_thm("prob_disj_pair_events",
  ``!X Y z n p. prob_space p /\ 
    (!x. (pair_disj_events p X Y x z IN events p)) /\ 
  	 (!a b. b <> a ==> DISJOINT (pair_disj_events p X Y a z)
	     	       	   	    (pair_disj_events p X Y b z)) ==> 
  (prob p (union_pair_disj_events p X Y n z) =
     sum (0,n) (prob p o (\x. pair_disj_events p X Y x z  INTER p_space p))) ``,
rw[]
\\ MATCH_MP_TAC (GSYM PROB_FINITELY_ADDITIVE)
\\ rw[union_pair_disj_events_def]
>- (rw[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   \\ ONCE_REWRITE_TAC[INTER_COMM] \\ DEP_REWRITE_TAC [INTER_PSPACE] \\ rw[])
\\ rw[DISJOINT_DEF,INTER_ASSOC]
\\ rw [prove (``!a b c. a INTER b INTER c INTER b = a INTER (b INTER c)``,rw[]\\ SRW_TAC[][INTER_DEF,EXTENSION,GSPECIFICATION]\\ METIS_TAC[])]
\\  ONCE_REWRITE_TAC[INTER_COMM] \\ DEP_REWRITE_TAC [INTER_PSPACE] \\ rw[]
\\ rw[GSYM DISJOINT_DEF]);

val prob_disj_pair_events_indep = store_thm("prob_disj_pair_events_indep",
  ``!X Y z n p. prob_space p /\
    (!x. (pair_disj_events p X Y x z IN events p) /\
    	  indep p (PREIMAGE X {Normal (&x)} INTER p_space p)
	  	  (PREIMAGE Y {Normal (z - &x)} INTER p_space p)) /\ 
  	 (!a b. b <> a ==> DISJOINT (pair_disj_events p X Y a z)
	     	       	   	    (pair_disj_events p X Y b z)) ==> 
  (prob p (union_pair_disj_events p X Y n z) =
     sum (0,n) (\x. prob p (PREIMAGE X {Normal (&x)} INTER p_space p) *
     	            prob p (PREIMAGE Y {Normal (z - &x)} INTER p_space p))) ``,
rw[]
\\ DEP_REWRITE_TAC[prob_disj_pair_events]
\\ rw[]
\\ rw[o_DEF]
\\ FULL_SIMP_TAC std_ss[pair_disj_events_def,indep_def,INTER_COMM]
\\ ONCE_REWRITE_TAC[disj_pair_lem1]
\\ rw[]);

(*----------------------------------------------
val nsum_pair_disj_events_def = Define 
`(nsum_pair_disj_events p [] n z x = p_space p) /\
 (nsum_pair_disj_events p (h::t) n z x =  
  (PREIMAGE h {Normal (z - &x)} INTER p_space p) INTER
  (BIGUNION (IMAGE (\x. nsum_pair_disj_events p t n z x)
           (count n))))`;


val nsum_pair_disj_events_def = Define 
`(nsum_pair_disj_events p [] n z x = p_space p) /\
 (nsum_pair_disj_events p (h::[]) n z x = 
  (PREIMAGE h {Normal (&x)} INTER p_space p)) /\
 (nsum_pair_disj_events p (h::t) n z x =  
  (PREIMAGE h {Normal (z - &x)} INTER p_space p) INTER
  (BIGUNION (IMAGE (\x. nsum_pair_disj_events p t n z x)
           (count n))))`; 

---------------------------------------*)


val union_pair_disj_events_def = Define 
`(union_pair_disj_events p [] n z x = p_space p) /\
 (union_pair_disj_events p (h::[]) n z x = 
  (PREIMAGE h {Normal (&x)} INTER p_space p)) /\
 (union_pair_disj_events p (h::t) n z x =  
  (BIGUNION (IMAGE (\x. (PREIMAGE h {Normal (z - &x)} INTER p_space p) INTER
   union_pair_disj_events p t n z x) (count n))))`;

val nsum_pair_disj_events_def = Define 
`(nsum_pair_disj_events p [] n z x = 1) /\
 (nsum_pair_disj_events p (h::[]) n z x = 
  prob p (PREIMAGE h {Normal (&x)} INTER p_space p)) /\
 (nsum_pair_disj_events p (h::t) n z x =  
  sum (0,n) (\x. prob p (PREIMAGE h {Normal (z - &x)} INTER p_space p) *
     	           nsum_pair_disj_events p t n z x ))`;


val nsum_pair_disj_events1_def = Define 
`(nsum_pair_disj_events1 p [] n z = 1) /\
 (nsum_pair_disj_events1 p (h::[]) n z = 
  prob p (PREIMAGE h {Normal (&z)} INTER p_space p)) /\
 (nsum_pair_disj_events1 p (h::t) n z =  
  sum (0,n) (\x. prob p (PREIMAGE h {Normal (&z - &x)} INTER p_space p) *
     	           nsum_pair_disj_events1 p t n x ))`;



val union_pair_disj_events1_def = Define 
`(union_pair_disj_events1 p [] n z = p_space p) /\
 (union_pair_disj_events1 p (h::[]) n z = 
  PREIMAGE h {Normal (&z)} INTER p_space p) /\
 (union_pair_disj_events1 p (h::t) n z =  
  (BIGUNION (IMAGE (\x. (PREIMAGE h {Normal (&z - &x)} INTER p_space p) INTER
   union_pair_disj_events1 p t n (&x)) (count n))))`;


(*---------------------------------------------------
val sum_of_pair_disj_events_def = tDefine "sum_of_pair_disj_events"
`(sum_of_pair_disj_events p [] z n t = p_space p) /\
 (sum_of_pair_disj_events p (h::[]) z n t = 
  (PREIMAGE h {Normal (&t)} INTER p_space p)) /\
 (sum_of_pair_disj_events p L z n t =  
  (BIGUNION (IMAGE (\x. (PREIMAGE (HD L) {Normal (z - &x)} INTER p_space p) INTER
   sum_of_pair_disj_events p (TL L) z n x) (count n))))`
(WF_REL_TAC `measure (\a. LENGTH(FST(SND a)))`\\
simp_tac list_ss[]);
---------------------------------------------------*)

(*---------------------------------------------------
`!p n z L a b X Y h'. (b <> a) /\
    
   (!a b X Y. (b <> a) /\ MEM X (TL L) /\ MEM Y L ==> DISJOINT (pair_disj_events p X Y a z)
	     	       	      (pair_disj_events p X Y b z)) ==>
  (DISJOINT
  (PREIMAGE h' {Normal (z - &a)} INTER p_space p INTER
   union_pair_disj_events p (h::L) n z a)
  (PREIMAGE h' {Normal (z - &b)} INTER p_space p INTER
   union_pair_disj_events p (h::L) n z b))`
rw[]
\\ Induct_on `L`
>- (simp_tac list_ss[union_pair_disj_events_def,nsum_pair_disj_events_def])
\\ simp_tac list_ss[]
\\ rw[]
\\ RW_TAC std_ss[]
\\ Cases_on `L`
>- (simp_tac list_ss[union_pair_disj_events_def,nsum_pair_disj_events_def])
\\ fs []
---------------------------------------------------*)
(*-------------------
``!p n r z h' L. prob_space p /\ (z < n) /\
     (!X Y. MEM X L /\ MEM Y L ==> (!x z. (x < n) /\ (z < n)==>
     	 (indep p (PREIMAGE X {Normal (&z - &x)} INTER p_space p)
	  	  (PREIMAGE Y {Normal (&x)} INTER p_space p))))
==> (prob p
  (PREIMAGE h' {Normal (&z - &r)} INTER p_space p INTER
   union_pair_disj_events1 p L n z) = prob p
  (PREIMAGE h' {Normal (&z - &r)} INTER p_space p) *
   prob p (union_pair_disj_events1 p L n z)) ``,
(*-------------------*)

---------------------------------------------------*)
(*------------------*)
val disj_pair_thm = store_thm("disj_pair_thm",
  ``(!p a b X Y z. b <> a ==> DISJOINT (pair_disj_events p X Y a z)
	     	       	   	    (pair_disj_events p X Y b z))``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [pair_disj_events_def,IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]);

(*------------------*)

val disj_thm = store_thm("disj_thm",
  ``!p X (m:num) (n:num).(m <> n)==>  DISJOINT ((PREIMAGE X {Normal &m} INTER p_space p) ) ((PREIMAGE X {Normal &n} INTER p_space p) )``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [pair_disj_events_def,IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]);
(*------------------*)
val union_disj_pair_thm = store_thm("union_disj_pair_thm",
  ``!p a b h' z n h L.
a <> b ==>
(DISJOINT
  (PREIMAGE h' {Normal (z - &a)} INTER p_space p INTER
   union_pair_disj_events p (h::L) n z a)
  (PREIMAGE h' {Normal (z - &b)} INTER p_space p INTER
   union_pair_disj_events p (h::L) n z b))``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [pair_disj_events_def,IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ DISJ1_TAC
\\ rw[realTheory.real_sub]);
(*------------------
 ``a <> b ==>
DISJOINT
  (big_inter p L1 INTER PREIMAGE h' {Normal (z - &a)} INTER p_space p INTER
   symb_union_pair_disj p P Q (h::t) n a)
  (big_inter p L1 INTER PREIMAGE h' {Normal (z - &b)} INTER p_space p INTER
   symb_union_pair_disj p P Q (h::t) n b)``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [pair_disj_events_def,IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ DISJ1_TAC
\\ rw[realTheory.real_sub]);
----------------------------*)
(*------------------*)
val union_disj_pair1_thm = store_thm("union_disj_pair1_thm",
  ``!p a b h' z n h L.
a <> b ==>
(DISJOINT
  (PREIMAGE h' {Normal (&z - &a)} INTER p_space p INTER
   union_pair_disj_events1 p (h::L) n a)
  (PREIMAGE h' {Normal (&z - &b)} INTER p_space p INTER
   union_pair_disj_events1 p (h::L) n b))``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ DISJ1_TAC
\\ rw[realTheory.real_sub]);
(*------------------*)
val union_disj_pair2_thm = store_thm("union_disj_pair2_thm",
  ``!p a b h' z.
a <> b ==>
(DISJOINT
  (PREIMAGE h' {Normal (&z - &a)})
  (PREIMAGE h' {Normal (&z - &b)}))``,
RW_TAC std_ss [DISJOINT_ALT]
\\ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]
\\ RW_TAC std_ss [DISJOINT_ALT]
\\ rw[realTheory.real_sub]);
(*-------------------*)


(*-------------------*)
val in_events_union_pair_disj_events = store_thm("in_events_union_pair_disj_events",
  ``!p n z L. 
  prob_space p /\ 
  (z < n) /\ 
  (!X. 
     MEM X L ==> 
     (!z. 
     	(z < n) ==> 
       	(\x. PREIMAGE X {Normal(&z - &x)} INTER p_space p) IN 
       	((count n) -> events p))) /\ 
  (!Y. 
     MEM Y L ==> 
     (\x. PREIMAGE Y {Normal (&x)} INTER p_space p) IN 
     (count n -> events p)) ==> 
 (union_pair_disj_events1 p L n &z IN events p)``,
GEN_TAC
\\ GEN_TAC
\\ Induct_on `L`
>- (simp_tac list_ss[union_pair_disj_events1_def]
   \\ rw[EVENTS_SPACE])
\\ GEN_TAC
\\ Cases_on `L`
>- (simp_tac std_ss[union_pair_disj_events1_def]
   \\ rw[]
   \\ fs [IN_IMAGE,IN_FUNSET,IN_COUNT])
\\ rw[]
\\ RW_TAC std_ss[union_pair_disj_events1_def]
\\ DEP_REWRITE_TAC[EVENTS_COUNTABLE_UNION]
\\ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
\\ RW_TAC std_ss[]
\\ RW_TAC std_ss[SUBSET_DEF]
\\ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
\\ DEP_ONCE_REWRITE_TAC[EVENTS_INTER]
\\ rw[EVENTS_SPACE]
>- ((`(!X.
         MEM X (h'::t) ==>
         !z'.
           z' < n ==>
           !x.
             x < n ==>
             PREIMAGE X {Normal (&z' - &x)} INTER p_space p IN events p)` by rw[]
	     >- (rw[])
	     >-(rw[])
	     \\ full_simp_tac std_ss[])

	\\ (`(!Y.
         MEM Y (h'::t) ==>
         !x. x < n ==> PREIMAGE Y {Normal (&x)} INTER p_space p IN events p)` by rw[]
	 >- (rw[])
	 >-(rw[])
	 \\ full_simp_tac std_ss[]))
\\ MATCH_MP_TAC COUNTABLE_IMAGE
\\ MATCH_MP_TAC FINITE_COUNTABLE
\\ RW_TAC std_ss [FINITE_COUNT]);
(*-----------------------*)

(*----------------------------

``{A INTER x |x | x IN {x1;x2}} = IMAGE (\x. A INTER x)({x1;x2})``
------------------------------*)
val test1 = store_thm("test1",
  ``!A f n. {A INTER x |x |(x IN IMAGE (\x. f x) (count n))} = 
  IMAGE (\x. A INTER x) (IMAGE (\x. f x) (count n))``,
srw_tac[][IN_IMAGE,IN_FUNSET,IN_COUNT,EXTENSION,GSPECIFICATION]);

(*----------------------*)
val bigunion_image_lem = store_thm("bigunion_image_lem",
  ``!A f n. A INTER BIGUNION (IMAGE (\x. f x) (count n)) = BIGUNION (IMAGE (\x. A INTER f x) (count n))``,
simp[]
\\ once_rewrite_tac[FT_deepTheory.INTER_BIGUNION]
\\ rw[test1]
\\ rw[GSYM pred_setTheory.IMAGE_COMPOSE]\\
rw[o_DEF]);


(*----------------------*)

val symb_union_pair_disj_def = Define 
`(symb_union_pair_disj p P Q [] n z = p_space p) /\
(symb_union_pair_disj p P Q (h::[]) n z = P z h INTER p_space p)  /\
(symb_union_pair_disj p P Q (h::t) n z = 
 BIGUNION (IMAGE (\x. ((\a. Q h z a) x) INTER p_space p  INTER symb_union_pair_disj p P Q t n x ) (count n)))`;
(*----------------------*)
(*------------
val symb_union_pair_disj1_def = Define 
`(symb_union_pair_disj1 p P Q [] n z = p_space p) /\
(symb_union_pair_disj1 p P Q (h::t) n z = 
 big_inter p (IMAGE (\x. ((\a. Q h z a) x) INTER p_space p  :: symb_union_pair_disj1 p P Q t n x ) (count n)))`;
-------------------*)
(*----------------------*)
val pair_wise_events_def = Define 
`(pair_wise_events p P Q [] z x = p_space p) /\
(pair_wise_events p P Q (h::[]) z x = P z h) /\
(pair_wise_events p P Q (h::t) z x = ((Q h z x) INTER pair_wise_events p P Q (t) z x))`;
(*----------------------*)
(*------------
val pair_wise_events_list1_def = Define 
`(pair_wise_events_list1 p P Q [] n = []) /\
(pair_wise_events_list1 p P Q (h::t) n = 
(if ((z < n) /\ (x < n)) then ((Q h z x) :: pair_wise_events_list1 p P Q (t) n) else []))`;



FT_deepTheory.BIGINTER_SET

val test2_def = Define 
`test2  A f n = {{A ; x} | x IN IMAGE (\x. f x) (count n)}`;

``IMAGE (\y. (IMAGE
        (\x. C x y)
        (count n))) (count n):: L = s``,
srw_tac[][EXTENSION,GSPECIFICATION]\\
EQ_TAC 
rw[IMAGE_DEF]
-------------------*)
val pair_wise_indep_events_list_def = Define 
`(pair_wise_indep_events_list P1 Q1  [] = []) /\
(pair_wise_indep_events_list P1 Q1 (h::[]) = [P1 h]) /\
(pair_wise_indep_events_list P1 Q1 (h::t) = 
 Q1 h::pair_wise_indep_events_list P1 Q1 t)`;

(*----------------------*)

val pred_pair_events_def = Define 
`(pred_pair_events x P Q n [] = T) /\
(pred_pair_events x P Q n (h::[]) = (!z. z < n ==> 
  (x = P (z:num) h))) /\
(pred_pair_events x P Q n (h::t) = 
(!y z. y < n /\ z < n ==> 
  (x = Q h (y:num) (z:num))) /\ 
  pred_pair_events x P Q n t)`;

(*----------------------*)

val pred_mutual_indep_pair_events_def = Define 
`pred_mutual_indep_pair_events p n P1 Q1 P Q L1 L = 
(!x. MEM x (pair_wise_indep_events_list P1 Q1 L) ==>
 pred_pair_events x P Q n L) /\
 mutual_indep p (L1 ++ (pair_wise_indep_events_list P1 Q1 L))`;

(*----------------------*)
(*----------------------*)

val pred_mutual_indep_pair_events1_def = Define 
`pred_mutual_indep_pair_events1 p n P1 Q1 P Q L = 
(!x. MEM x (pair_wise_indep_events_list P1 Q1 L) ==>
 pred_pair_events x P Q n L) /\
 mutual_indep p (pair_wise_indep_events_list P1 Q1 L)`;

(*----------------------*)
(*---------------------------
`(!x y. x < n /\ y < n) /\ (!x. MEM x (pair_wise_indep_events_list P1 (h::t)) ==>
 pred_pair_events x Q n (h::t)) /\
 mutual_indep p (Q h x1 y1::L1 ++ (pair_wise_indep_events_list P1 t)) ==>
mutual_indep p (L1++ (pair_wise_indep_events_list P1 (h::t)))`

rw[ pair_wise_indep_events_list_def,pred_pair_events_def]
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`P1 h`] MP_TAC)\\
rw[]
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`x1`,`y1`] MP_TAC)
\\ rw[]
\\ fs[]
\\ rw [mutual_indep_cons_append])
\\ MATCH_MP_TAC mutual_indep_cons_append11
\\ Q.EXISTS_TAC `[]`
\\ rw[]);

`(!x y. x < n /\ y < n) /\ (!x. MEM x (pair_wise_indep_events_list P1 (h::t)) ==>
 pred_pair_events x Q n (h::t)) /\
mutual_indep p (L1++ (pair_wise_indep_events_list P1 (h::t)))  ==>
mutual_indep p (Q h x1 y1::L1 ++ (pair_wise_indep_events_list P1 t)) `
FIRST_X_ASSUM (Q.SPECL_THEN [`z`,`x`] MP_TAC)


``BIGUNION {s;t} = {s;t}``,
 `(P h IN {C x y| x < n /\ y < n})::L = s`
`{C x y| x < n /\ y < n} IN IMAGE (\y. IMAGE (\x. C x y) (count n)) (count n)`
Q.EXISTS_TAC `y`
\\ rw[]
``symb_union_pair_disj1 p P Q (h::t) n z INTER p_space p = s``,
rw[symb_union_pair_disj1_def]\\
DEP_REWRITE_TAC [FT_deepTheory.BIGINTER_SET]




(*----------------------*)
val pair_wise_events_list_def = Define 
`(pair_wise_events_list p P Q [] z x = []) /\
(pair_wise_events_list p P Q (h::[]) z x = P z h) /\
(pair_wise_events_list p P Q (h::t) z x = 
((Q h z x) :: pair_wise_events_list p P Q (t) z x))`;
(*----------------------*)
val indep_pair_wise_events_def = Define 
`indep_pair_wise_events p P Q L1 L2 n = 
!x z. (x < n) /\ (z < n) ==> mutual_indep p (L1 ++ pair_wise_events_list P Q L2 z x)`;
(*----------------------*)
val indep_pair_wise_events_def = Define 
`indep_pair_wise_events p P Q L1 L2 n = 
!x z. (x < n) /\ (z < n) ==> mutual_indep p (L1 ++ pair_wise_events_list P Q L2 z x)`;
-------------------------*)			
(*-----------------------*)
val in_events_symb_union_pair_disj = store_thm("in_events_symb_union_pair_disj",
  ``!p n P Q t h x. prob_space p /\ (x < n) /\
(!X. 
     MEM X (h::t) ==> 
     (!z. 
     	(z < n) ==> 
       	(\x. Q X z x INTER p_space p) IN 
       	((count n) -> events p))) /\ 
  (!Y. 
     MEM Y (h::t) ==> 
     (\x. P x Y INTER p_space p) IN 
     (count n -> events p)) ==>
(symb_union_pair_disj p P Q (h::t) n x IN events p)``,
GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ Induct
>- (rw[symb_union_pair_disj_def]
   \\ fs[IN_IMAGE,IN_FUNSET,IN_COUNT])
\\ RW_TAC std_ss[]
\\ rw[symb_union_pair_disj_def]
\\ DEP_REWRITE_TAC[EVENTS_COUNTABLE_UNION]
\\ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
\\ RW_TAC std_ss[]
\\ RW_TAC std_ss[SUBSET_DEF]
\\ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
>- (DEP_ONCE_REWRITE_TAC[EVENTS_INTER]
   \\ rw[EVENTS_SPACE])
\\ MATCH_MP_TAC COUNTABLE_IMAGE
\\ MATCH_MP_TAC FINITE_COUNTABLE
\\ RW_TAC std_ss [FINITE_COUNT]);

(*-----------------------*)
(*--------------------------
val indep_test_def = Define 
`(indep_test P Q [] n z = UNIV) /\ 
(indep_test P Q (h::t) n z = IMAGE (\x. Q h z x UNION  indep_test P Q (h::t) n x) (count n)})  `;
(*-----------------------*)
``indep_pair_wise_events p P Q L1 (h'::h::t) n ==>
 indep_pair_wise_events p P Q (Q h' z x::L1) (h::t) n``,
rw[indep_pair_wise_events_def,pair_wise_events_list_def]

-----------------------*)
(*-----------------------*)
val big_inter_indep_symb_union_pair_disj = store_thm(
  "big_inter_indep_symb_union_pair_disj",
  ``!p n P1 Q1 P Q t h z L1. prob_space p /\ 
 pred_mutual_indep_pair_events p n P1 Q1 P Q L1 (h::t) /\
(!z x. (z < n) /\ x < n /\  
(!X a b. (b <> a) ==> (DISJOINT
       (Q X z a )
       (Q X z b)))/\
(!X. 
     MEM X (h::t) ==>  
       	Q X z x IN  events p) /\ 
  (!Y. 
     MEM Y (h::t) ==> P x Y IN events p)) /\
~NULL L1 /\
(!z.  MEM z L1 ==> z IN events p) ==>
(prob p (big_inter p L1 INTER symb_union_pair_disj p P Q (h::t) n z) = 
prob p (big_inter p L1) * prob p (symb_union_pair_disj p P Q (h::t) n z))``,
GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ Induct_on `t`
>- (rw[symb_union_pair_disj_def]
   \\ fs[pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def]
   \\ `(P z h INTER p_space p) =  big_inter p [P z h]` by rw[big_inter_def]
   \\ pop_orw
   \\ rw[GSYM parallel_lem5]
   \\ once_rewrite_tac[INTER_COMM]
   \\ DEP_REWRITE_TAC[series_rbd_append]
   \\ RW_TAC std_ss[]
   >- (fs[])
   \\ DEP_REWRITE_TAC[series_rbd_append2]
   \\ rw[]
   >-(fs[])
   >-(fs[])
   >-(fs[pred_pair_events_def]
   \\ NTAC 3 (POP_ASSUM MP_TAC)
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z:num`] MP_TAC)
     \\ rw[]
     \\ fs[]
     \\ `(P z h::L1) = [P z h]++L1` by rw[]
     \\ pop_orw
     \\ rw[mutual_indep_append_sym])
   \\ REAL_ARITH_TAC)
\\ simp_tac std_ss[]
\\ RW_TAC std_ss[]
\\ rw[symb_union_pair_disj_def]
\\ rw[bigunion_image_lem]
\\ rw[INTER_ASSOC]
\\ (`prob p
    (BIGUNION
     (IMAGE
        (\x.
           big_inter p L1 INTER Q h' z x INTER p_space p INTER
           symb_union_pair_disj p P Q (h::t) n x) (count n))) = 
	   sum (0,n) (prob p ∘(\x.
           big_inter p L1 INTER Q h' z x INTER p_space p INTER
           symb_union_pair_disj p P Q (h::t) n x))` by ALL_TAC)
>- (MATCH_MP_TAC (GSYM PROB_FINITELY_ADDITIVE)
   \\ rw[]
   >- (rw[IN_IMAGE,IN_FUNSET,IN_COUNT]
      \\ rw[]
      \\ DEP_ONCE_REWRITE_TAC[EVENTS_INTER]
      \\ rw[]
      >- (rw[GSYM INTER_ASSOC]
      	 \\ MATCH_MP_TAC EVENTS_INTER
	 \\ rw[]
	 >- (DEP_REWRITE_TAC[in_events_big_inter]
	    \\ rw[])
	 \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE])
      \\ DEP_REWRITE_TAC[in_events_symb_union_pair_disj]
      \\ rw[]
       >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
          \\ rw[]
       	  \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE])
      >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
          \\ rw[]
       	  \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE])
      >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
          \\ rw[]
       	  \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE])
      \\ (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
          \\ rw[]
       	  \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE]))
     \\ fs[DISJOINT_ALT]
     \\ rw[]
     \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z:num`,`x':num`] MP_TAC)
     \\ rw[]
     \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(h':'b)`,`a:num`,`b:num`] MP_TAC)
     \\ rw[])
\\ pop_orw
\\ rw[o_DEF]
\\ (`!x. prob p
       (big_inter p L1 INTER Q h' z x INTER p_space p INTER
        symb_union_pair_disj p P Q (h::t) n x) =
	prob p
       (big_inter p L1 INTER Q h' z x INTER p_space p) *
       prob p (symb_union_pair_disj p P Q (h::t) n x)` by ALL_TAC)
   >- (rw[]
      \\ FIRST_X_ASSUM (Q.SPECL_THEN [`h:'b`,`x:num`,`Q h' z x::L1`] MP_TAC)
      \\  RW_TAC std_ss[]
      \\ full_simp_tac std_ss[]
      \\ `pred_mutual_indep_pair_events p n P1 Q1 P Q (Q h' z x::L1) (h::t)` by rw[]
      >- (full_simp_tac std_ss[pred_mutual_indep_pair_events_def]
      	 \\ fs[pair_wise_indep_events_list_def,pred_pair_events_def]
	 \\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
	 \\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
	 \\ rw[]
	 \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z:num`,`x:num`] MP_TAC)
	 \\ rw[]
	 \\ fs[]
      	 \\ match_mp_tac mutual_indep_cons_append11
	 \\ Q.EXISTS_TAC `[]`
	 \\ rw[])
      \\ FULL_SIMP_TAC std_ss[]
      \\ (`(!z x.
         (!X. MEM X (h::t) ==> Q X z x IN events p) /\
         !Y. MEM Y (h::t) ==> P x Y IN events p) /\ ¬NULL (Q h' z x::L1) /\
      	 (!z'. MEM z' (Q h' z x::L1) ==> z' IN events p)` by rw[])
      	 >- (fs[])
      	 >- (fs[])
      \\ full_simp_tac std_ss[big_inter_def]
      \\ `Q h' z x INTER p_space p = Q h' z x` by once_rewrite_tac[INTER_COMM]
      	 >- (DEP_REWRITE_TAC[INTER_PSPACE]
	    \\ fs[])
      \\ once_rewrite_tac[INTER_COMM]
      \\ once_rewrite_tac[GSYM INTER_ASSOC]
      \\ rw[]
      \\ rw[INTER_ASSOC]
      \\ rw[prove(``!a b c. a INTER b INTER c = c INTER (b INTER a)``, srw_tac[][EXTENSION,GSPECIFICATION] \\ metis_tac[])]
      \\ rewrite_tac[INTER_ASSOC]
      \\ rw[]
      \\ DISJ2_TAC
      \\ rw[prove(``!a b c. a INTER b INTER c = b INTER (a INTER c)``, srw_tac[][EXTENSION,GSPECIFICATION] \\ metis_tac[])]
      \\ rw[INTER_COMM])
\\ pop_orw
\\  `!x. ( Q h' z x INTER p_space p) =  big_inter p [ Q h' z x]` by rw[big_inter_def]
\\ once_rewrite_tac[GSYM INTER_ASSOC]
\\ pop_orw
\\ rw[GSYM parallel_lem5]
\\ once_rewrite_tac[INTER_COMM]
\\ `!x.prob p
       (rbd_struct p (series (rbd_list [Q h' z x])) INTER
        rbd_struct p (series (rbd_list L1))) = prob p
       (rbd_struct p (series (rbd_list [Q h' z x]))) *
       prob p ( rbd_struct p (series (rbd_list L1))) ` by rw[]
   >- (DEP_REWRITE_TAC[series_rbd_append]
      \\ RW_TAC std_ss[]	 
      >- (fs[])
      \\ DEP_REWRITE_TAC[series_rbd_append2]
      \\ rw[]
      >-(fs[])
      >-(fs[])
      \\ fs[pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_pair_events_def]
      \\ NTAC 4 (POP_ASSUM MP_TAC)
      \\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
      \\ rw[]
      \\ fs[]
      \\ NTAC 4 (POP_ASSUM MP_TAC)
      \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z`,`x`] MP_TAC)
      \\ rw[]
      \\ fs[]
      \\ `(Q h' z x::L1) =(Q h' z x::(L1++ [])) ` by rw[]
      \\ pop_orw
      \\ MATCH_MP_TAC mutual_indep_cons_append11
      \\ Q.EXISTS_TAC `pair_wise_indep_events_list P1 Q1 (h::t)`
      \\ rw[])
\\ pop_orw
\\ once_rewrite_tac[REAL_MUL_SYM]
\\ once_rewrite_tac[REAL_MUL_ASSOC]
\\ once_rewrite_tac[REAL_MUL_SYM]
\\ DEP_REWRITE_TAC[SUM_CMUL]
\\ rw[REAL_EQ_MUL_LCANCEL]
\\ DISJ2_TAC
\\ (`prob p
 (BIGUNION
     (IMAGE
        (\x.
           p_space p INTER symb_union_pair_disj p P Q (h::t) n x INTER Q h' z x)
        (count n))) = 
	   sum (0,n) (prob p ∘(\x.
           p_space p INTER symb_union_pair_disj p P Q (h::t) n x INTER Q h' z x))` by ALL_TAC)
>- (MATCH_MP_TAC (GSYM PROB_FINITELY_ADDITIVE)
   \\ rw[]
   >-(rw[IN_IMAGE,IN_FUNSET,IN_COUNT]
      \\ rw[]
      \\ DEP_ONCE_REWRITE_TAC[EVENTS_INTER]
      \\ rw[]
      >- (MATCH_MP_TAC EVENTS_INTER
	 \\ rw[]
	 \\ rw[EVENTS_SPACE]
      	 \\ DEP_REWRITE_TAC[in_events_symb_union_pair_disj]
      	 \\ rw[]
       	 >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
            \\ rw[]
       	    \\ DEP_REWRITE_TAC[EVENTS_INTER]
	    \\ rw[EVENTS_SPACE])
      	 >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
            \\ rw[]
       	    \\ DEP_REWRITE_TAC[EVENTS_INTER]
	    \\ rw[EVENTS_SPACE])
      	 >- (fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
            \\ rw[]
       	    \\ DEP_REWRITE_TAC[EVENTS_INTER]
	    \\ rw[EVENTS_SPACE])
     	 \\ fs[IN_IMAGE,IN_FUNSET,IN_COUNT]
         \\ rw[]
       	 \\ DEP_REWRITE_TAC[EVENTS_INTER]
	 \\ rw[EVENTS_SPACE]))
  \\  fs[DISJOINT_ALT]
  \\ rw[]
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z:num`,`x':num`] MP_TAC)
  \\ rw[]
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(h':'b)`,`a:num`,`b:num`] MP_TAC)
  \\ rw[])
\\ pop_orw
\\ once_rewrite_tac[INTER_COMM]
\\ rw[INTER_ASSOC]
\\ rw[o_DEF]
\\ (`!x. prob p
       (big_inter p [Q h' z x] INTER symb_union_pair_disj p P Q (h::t) n x) = 
      prob p
       (big_inter p [Q h' z x]) * prob p (symb_union_pair_disj p P Q (h::t) n x)` by rw[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`h:'b`,`x:num`,`[Q h' z x]`] MP_TAC)
    \\  RW_TAC std_ss[]
    \\ full_simp_tac std_ss[]
    \\ `pred_mutual_indep_pair_events p n P1 Q1 P Q [Q h' z x] (h::t)` by rw[]
    >- (full_simp_tac std_ss[pred_mutual_indep_pair_events_def]
      	\\ fs[pair_wise_indep_events_list_def,pred_pair_events_def]
	\\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
	\\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
	\\ rw[]
	\\ FIRST_X_ASSUM (Q.SPECL_THEN [`z:num`,`x:num`] MP_TAC)
	\\ rw[]
	\\ fs[]
      	\\ match_mp_tac mutual_indep_front_append 
	\\ Q.EXISTS_TAC `L1`
	\\ rw[])
   \\ full_simp_tac std_ss[]
   \\ `(!z' x.
         (!X. MEM X (h::t) ==> Q X z' x IN events p) /\
         !Y. MEM Y (h::t) ==> P x Y IN events p) /\ ¬NULL [Q h' z x] /\
      (!z'. MEM z' [Q h' z x] ==> z' IN events p)` by rw[]
   \\ full_simp_tac std_ss[])
\\ `!x. ( Q h' z x INTER p_space p) =  big_inter p [ Q h' z x]` by rw[big_inter_def]
\\ pop_orw
\\ pop_orw
\\ rewrite_tac[rbd_struct_def,rbd_list_def,big_inter_def]
\\ rw[REAL_MUL_COMM]);

(*------------------------------------------*)
val indep_event_symb_union_pair_disj = store_thm(
  "indep_event_symb_union_pair_disj",
  ``!p h t n P1 Q1 P Q A z. prob_space p /\
(!z x.
         z < n /\ x < n /\
         (!X a b. b ≠ a ==> DISJOINT (Q X z a) (Q X z b)) /\
         (!X. MEM X (h::t) ==> Q X z x IN events p) /\
         !Y. MEM Y (h::t) ==> P x Y IN events p) /\ A IN events p /\
pred_mutual_indep_pair_events p n P1 Q1 P Q [A] (h::t) ==>
(prob p (A INTER symb_union_pair_disj p P Q (h::t) n z) = 
prob p (A) * prob p (symb_union_pair_disj p P Q (h::t) n z))``,
rpt(gen_tac)
\\ rw_tac std_ss[]
\\ MP_TAC(Q.ISPECL[`p:α event # α event event # (α event -> real)`,
   	            `n:num`,`P1:'b->'a event`,`Q1:'b->'a event`,`(P :num -> β -> α event)`,
		    ` (Q :β -> num -> num -> α event)`,`(t :β list)`,`(h :β)`,
		    `z:num`,`[A:'a event]`] big_inter_indep_symb_union_pair_disj)
\\ full_simp_tac std_ss[]
\\ rw[]
\\ full_simp_tac std_ss[big_inter_def]
\\ `A INTER p_space p = A` by  once_rewrite_tac[INTER_COMM]
>- (DEP_REWRITE_TAC[INTER_PSPACE] \\  rw[])
\\ full_simp_tac std_ss[]);
(*------------------------------------*)
val union_pair_disj_events_alt_symb_form = store_thm(
  "union_pair_disj_events_alt_symb_form",
  ``!L p n z. prob_space p ==>
    (union_pair_disj_events1 p L n z =
    symb_union_pair_disj p (\z h. PREIMAGE h {Normal (&z)}) (\h z x. PREIMAGE h {Normal (&z - &x)}) L n z)``,
Induct    
>- (rw[union_pair_disj_events1_def,symb_union_pair_disj_def])
\\ Cases_on `L`
>- (rw[union_pair_disj_events1_def,symb_union_pair_disj_def])
\\ rw[union_pair_disj_events1_def,symb_union_pair_disj_def]);

(*------------------------------------*)
(*----------------------*)

val pred_disj_pair_events_def = Define 
`(pred_disj_pair_events x n [] = T) /\
(pred_disj_pair_events x n (h::[]) = (!z. z < n ==> 
  (x = PREIMAGE h {Normal &z}))) /\
(pred_disj_pair_events x n (h::t) = 
(!y z. y < n /\ z < n ==> 
  (x = PREIMAGE h {Normal (&z - &y)})) /\ 
  pred_disj_pair_events x n t)`;

(*----------------------*)
val mutual_indep_disj_pair_events_def = Define 
`mutual_indep_disj_pair_events p n P1 Q1 L = 
(!x. MEM x (pair_wise_indep_events_list P1 Q1 L) ==>
 pred_disj_pair_events x n L) /\
 mutual_indep p (pair_wise_indep_events_list P1 Q1 L)`;
(*------------------------------------*)
val pred_disj_pair_events_implies_pred_pair = store_thm(
  "pred_disj_pair_events_implies_pred_pair",
  ``!x n h h' L.
  pred_disj_pair_events x n (h'::L) ==>
  pred_pair_events x (\z h. PREIMAGE h {Normal (&z)})
  (\h z x. PREIMAGE h {Normal (&z - &x)}) n L``,
rw[]
\\ Induct_on `L`
>- (rw[pred_disj_pair_events_def,pred_pair_events_def])
\\ rw[pred_disj_pair_events_def,pred_pair_events_def]
\\ Cases_on `L`
>-(rw[pred_disj_pair_events_def,pred_pair_events_def]
 \\ full_simp_tac list_ss[pred_disj_pair_events_def,pred_pair_events_def])
 \\ full_simp_tac list_ss[pred_disj_pair_events_def,pred_pair_events_def]);
 (*------------------------------------*)
val pred_disj_pair_events_implies_pred_pair1 = store_thm(
  "pred_disj_pair_events_implies_pred_pair1",
  ``!x n h L.
  pred_disj_pair_events x n (L) ==>
  pred_pair_events x (\z h. PREIMAGE h {Normal (&z)})
  (\h z x. PREIMAGE h {Normal (&z - &x)}) n L``,
rw[]
\\ Induct_on `L`
>- (rw[pred_disj_pair_events_def,pred_pair_events_def])
\\ rw[pred_disj_pair_events_def,pred_pair_events_def]
\\ Cases_on `L`
>-(rw[pred_disj_pair_events_def,pred_pair_events_def]
 \\ full_simp_tac list_ss[pred_disj_pair_events_def,pred_pair_events_def])
 \\ full_simp_tac list_ss[pred_disj_pair_events_def,pred_pair_events_def]);
(*------------------------------------*)
val pred_disj_pair_events_imp_pred_pair_events = store_thm(
  "pred_disj_pair_events_imp_pred_pair_events",
  ``!x n L. pred_disj_pair_events x n L ==> pred_pair_events x (\z h. PREIMAGE h {Normal (&z)})
  (\h z x. PREIMAGE h {Normal (&z - &x)}) n L``,
Induct_on `L`
>- (rw[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def,pred_pair_events_def])
\\ Cases_on `L`
>-(rw[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def,pred_pair_events_def])
\\ rw[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def,pred_pair_events_def]);
(*-----------------------------------*)

val mutual_indep_disj_pair_implies_pred_mutual_indep_pair = store_thm(
  "mutual_indep_disj_pair_implies_pred_mutual_indep_pair",
  ``!p n P1 Q1 h h' z r t.
 (r < n) /\ (z < n) /\ mutual_indep_disj_pair_events p n P1 Q1 (h'::(h::t)) ==>
  pred_mutual_indep_pair_events p n P1 Q1 (\z h. PREIMAGE h {Normal (&z)})
  (\h z x. PREIMAGE h {Normal (&z - &x)})
  [PREIMAGE h' {Normal (&z - &r)}] (h::t)``,
Induct_on `t`
>- (rw[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def,pred_pair_events_def]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
   \\ rw[]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`r:num`,`z:num`] MP_TAC)
   \\ rw[]
   \\ fs[])
\\ rw[mutual_indep_disj_pair_events_def,pred_mutual_indep_pair_events_def,pair_wise_indep_events_list_def,pred_disj_pair_events_def,pred_pair_events_def]
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h'`] MP_TAC)
   \\ rw[]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`r:num`,`z:num`] MP_TAC)
   \\ rw[]
   \\ fs[])
>-(MATCH_MP_TAC pred_disj_pair_events_imp_pred_pair_events
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(p :α event # α event event # (α event -> real))`, `(n :num)`,
         `(P1 :(α -> extreal) -> α event)`, `(Q1 :(α -> extreal) -> α event)`,
         `(h :α -> extreal)`, `(h' :α -> extreal)`, `(z :num)`, `(r :num)`] MP_TAC)
 \\ rw[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`(p :α event # α event event # (α event -> real))`, `(n :num)`,
         `(P1 :(α -> extreal) -> α event)`, `(Q1 :(α -> extreal) -> α event)`,
         `(h :α -> extreal)`, `(h' :α -> extreal)`, `(z :num)`, `(r :num)`] MP_TAC)
 \\ rw[])
 >- (MATCH_MP_TAC pred_disj_pair_events_imp_pred_pair_events
  \\ FIRST_X_ASSUM (Q.SPECL_THEN [`(p :α event # α event event # (α event -> real))`, `(n :num)`,
         `(P1 :(α -> extreal) -> α event)`, `(Q1 :(α -> extreal) -> α event)`,
         `(h :α -> extreal)`, `(h' :α -> extreal)`, `(z :num)`, `(r :num)`] MP_TAC)
 \\ rw[])
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`Q1 h''`] MP_TAC)
\\ rw[]
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`r:num`,`z:num`] MP_TAC)
\\ rw[]
\\ fs[]
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`r:num`,`z:num`] MP_TAC)
\\ rw[]
\\ fs[]);

(*------------------------------------*)
val prob_sum_of_indep_rvs_list = store_thm("prob_sum_of_indep_rvs_list",
  ``!p P1 Q1 n z L.
    (!z x.
         z < n /\ x < n /\
         (!X. MEM X L ==> (PREIMAGE X {Normal (&z - &x)}) IN events p) /\
         !Y. MEM Y L ==> (PREIMAGE Y {Normal (&x)}) IN events p) /\
	 mutual_indep_disj_pair_events p n P1 Q1 L /\
prob_space p ==> 
  (prob p (union_pair_disj_events1 p L n z) = nsum_pair_disj_events1 p L n z)``,
Induct_on `L`
>- (simp_tac list_ss[union_pair_disj_events1_def,nsum_pair_disj_events1_def]
   \\ rw[PROB_UNIV])
\\ Cases_on `L`
>- (simp_tac list_ss[union_pair_disj_events1_def,nsum_pair_disj_events1_def])
\\ rw[]
\\ simp_tac std_ss[union_pair_disj_events1_def,nsum_pair_disj_events1_def]
\\ RW_TAC std_ss[]
\\ (`prob p (BIGUNION
       (IMAGE
          (\x.
             PREIMAGE h' {Normal (&z - &x)} INTER p_space p INTER
             union_pair_disj_events1 p (h::t) n x) (count n))) = sum (0,n) (prob p o (\x.
           PREIMAGE h' {Normal (&z - &x)} INTER p_space p INTER
           union_pair_disj_events1 p (h::t) n x))` by MATCH_MP_TAC (GSYM PROB_FINITELY_ADDITIVE))
>- (rw[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >- (DEP_ONCE_REWRITE_TAC[EVENTS_INTER]
      \\ once_rewrite_tac[INTER_COMM]
      \\ DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
      \\ rw[EVENTS_SPACE]
      \\ MATCH_MP_TAC in_events_union_pair_disj_events
      \\ once_rewrite_tac[INTER_COMM]
      	 \\ rw[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
	 \\ DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
	 \\ rw[EVENTS_SPACE]
	 \\ FULL_SIMP_TAC list_ss [IN_IMAGE,IN_FUNSET,IN_COUNT])
     \\ rw[union_disj_pair1_thm])
\\ full_simp_tac list_ss[o_DEF]
\\ MATCH_MP_TAC SUM_EQ
\\ rw[]
\\ rw[union_pair_disj_events_alt_symb_form]
\\ DEP_REWRITE_TAC[indep_event_symb_union_pair_disj]
\\ rpt(strip_tac)
>- (Q.EXISTS_TAC `P1`
   \\ Q.EXISTS_TAC `Q1`
   \\ once_rewrite_tac[INTER_COMM]
    \\ rw[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
    \\ DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
    \\ rw[EVENTS_SPACE]
    \\ rw[union_disj_pair2_thm]
    \\ rw[]
    \\ MATCH_MP_TAC mutual_indep_disj_pair_implies_pred_mutual_indep_pair
    \\ rw[])
\\ rw[]
\\ DISJ2_TAC
\\ FIRST_X_ASSUM (Q.SPECL_THEN [`(p :α event # α event event # (α event -> real))`,
         `(P1 :(α -> extreal) -> α event)`, `(Q1 :(α -> extreal) -> α event)`,
          `(n:num)`, `(r :num)`] MP_TAC)
 \\ rw[]
\\ `(!z' x.
         (!X.
            (X = h) ∨ MEM X t ==>
            PREIMAGE X {Normal (&z' - &x)} IN events p) /\
         !Y. (Y = h) ∨ MEM Y t ==> PREIMAGE Y {Normal (&x)} IN events p)` by ALL_TAC
>- (rw[]
   \\ FIRST_X_ASSUM (Q.SPECL_THEN [`z':num`,`x:num`] MP_TAC)
\\ rw[])
\\ FULL_SIMP_TAC std_ss[GSYM MEM]
\\ `mutual_indep_disj_pair_events p n P1 Q1 (h::t)` by fs[mutual_indep_disj_pair_events_def]
>- (rw[]
   >- (fs[pair_wise_indep_events_list_def]
      \\ FIRST_X_ASSUM (Q.SPECL_THEN [`x:'a event`] MP_TAC)
      \\ rw[]
      \\ fs[pred_disj_pair_events_def])
   \\ fs[pair_wise_indep_events_list_def]
   \\ match_mp_tac mutual_indep_cons
   \\ Q.EXISTS_TAC `Q1 h'`
   \\ rw[])
\\ fs[]
\\ rw[GSYM union_pair_disj_events_alt_symb_form]);


val _ = export_theory();
