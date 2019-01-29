(* ========================================================================= *)
(* File Name: Railway Signaling System Importance Measure Analysis           *)
(*---------------------------------------------------------------------------*)
(* Description:                                                              *)
(*                                                                           *)
(*                                                                           *)
(*                HOL4-Kananaskis 12 		 			     *)
(*									     *)
(*		Authors :  Shahid Murtaza (1)     		     	     *)
(*                         Waqar Ahmad (2)               	             *)
(*		(1) National School of Scinces and Technology	             *)
(*		    Islamabad, Pakistan	       	   			     *)
(* 	        (2) Electrical and Computer Engineering                      *)
(*	            Concordia Univeristy, Montreal, QC, Canada               *)
(*                                          		               	     *)
(*                                                                           *)
(* ========================================================================= *)



(*----For Interactive Use----*)
(*loadPath := "/home/shahid/Downloads/Formal-Dependability-master" :: !loadPath;*)
(*loadPath := "/home/savelab/Downloads/Formal-Dependability" :: !loadPath;

app load ["FT_deepTheory","arithmeticTheory","probabilityTheory","listTheory","VDCTheory","RBDTheory","railwayTheory","util_probTheory","transcTheory","ASN_gatewayTheory","pred_setTheory","dep_rewrite","sortingTheory","combinTheory","seqTheory","realTheory","realLib","pred_setTheory","transform_FT_RBDTheory","FTImp_deepTheory"];*)

open FT_deepTheory probabilityTheory listTheory VDCTheory RBDTheory railwayTheory util_probTheory transcTheory ASN_gatewayTheory combinTheory pred_setTheory sortingTheory dep_rewrite seqTheory pred_setTheory arithmeticTheory realTheory realLib transform_FT_RBDTheory FTImp_deepTheory;

   
open HolKernel boolLib bossLib Parse;
val _ = new_theory "railway_signaling";

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

 
(******************************************************************)
(********* DEFINITIONS:  FAILURE AND SUCCESS EVENTS        ********)
(******************************************************************)
val f_comp_def = Define `f_comp p X t = fail_event p X t`;
val s_comp_def = Define `s_comp p X t = p_space p DIFF fail_event p X t`;
(*********************************************)
(**** DEFINITION:PHI_STRUCT_RW ( EVENTS ) ****)
(*********************************************)
val PHI_STRUCT_RW_def = Define
`PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 =
 FTree p
   (OR
     [OR (gate_list ([e3; e4])); OR (gate_list ([e5; e6]));
      AND
        [OR (gate_list ([e9; e10])); OR (gate_list ([e13; e14]));
         OR (gate_list ([e15; e16])); OR (gate_list ([e11; e12]))];
      OR (gate_list ([e7; e8])); OR (gate_list ([e1; e2]))])`;

(*----------------------------------------------------------------*)

(******************************************************************)
(***** Definition : Birnbaum Importance Measure (Vehicle)  ********)
(******************************************************************)
val birnhaum_IMP_Vehicle_def = Define
`birnhaum_IMP_Vehicle p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e1'=
 prob p (PHI_STRUCT_RW p e1  e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16) - 
 prob p (PHI_STRUCT_RW p e1' e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)`;


(*********************************************************************)
(** Definition : Birnbaum Reliability Importance Measure (Vehicle)  **)
(*********************************************************************)
val birnhaum_Rel_IMP_Vehicle_def = Define
`birnhaum_Rel_IMP_Vehicle p x1 x2 x3 x4  x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t =
 birnhaum_IMP_Vehicle p (f_comp p x1 t) (f_comp p x2 t) (f_comp p x3 t) (f_comp p x4 t)
                        (f_comp p x5 t) (f_comp p x6 t) (f_comp p x7 t) (f_comp p x8 t)
                        (f_comp p x9 t) (f_comp p x10 t) (f_comp p x11 t) (f_comp p x12 t) 
                        (f_comp p x13 t) (f_comp p x14 t) (f_comp p x15 t) (f_comp p x16 t)
                        (s_comp p x1 t)`;


(*----------------------------------------------------------------*)


(******************************************************************)
(************  Definition : Birnbaum Importance Measure (X9)  *****)
(******************************************************************)
val birnhaum_IMP_X9_def = Define
`birnhaum_IMP_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' =
 prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16) - 
 prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9' e10 e11 e12 e13 e14 e15 e16)`;
(****************************************************************)
(** Definition : Birnbaum Reliability Importance Measure (X9)  **)
(****************************************************************)
val birnhaum_Rel_IMP_X9_def = Define
`birnhaum_Rel_IMP_X9 p x1 x2 x3 x4  x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t =
 birnhaum_IMP_X9 p (f_comp p x1 t) (f_comp p x2 t) (f_comp p x3 t) (f_comp p x4 t)
                   (f_comp p x5 t) (f_comp p x6 t) (f_comp p x7 t) (f_comp p x8 t)
                   (f_comp p x9 t) (f_comp p x10 t) (f_comp p x11 t) (f_comp p x12 t) 
                   (f_comp p x13 t) (f_comp p x14 t) (f_comp p x15 t) (f_comp p x16 t)
                   (s_comp p x9 t)`;


(*----------------------------------------------------------------*)


(******************************************************************************)
(*************** THEOREMS :   SIMPLIFICATION LEMMAS           *****************)
(******************************************************************************)
val RBD_0 = store_thm("RBD_0",
``(rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
          (two_dim_fail_event_list p
	     [[x1]; [x2;x8;x7;x3;x4;x5;x6]; [x9;x10]; [x13;x14];
	      [x15;x16]; [x11;x12]] t))) =
(fail_event p x1 t ∩
(fail_event p x2 t ∪ fail_event p x8 t ∪ fail_event p x7 t ∪
 fail_event p x3 t ∪ fail_event p x4 t ∪ fail_event p x5 t ∪
 fail_event p x6 t) ∩
((fail_event p x9 t ∪ fail_event p x10 t) ∩
 (fail_event p x13 t ∪ fail_event p x14 t) ∩
 (fail_event p x15 t ∪ fail_event p x16 t) ∩
 (fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p))``,
RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);

(***************)
val  RBD_1 = store_thm("RBD_1",`` (rbd_struct p
           ((series of (λa. parallel (rbd_list a)))
              (two_dim_fail_event_list p [[x1];[x2;x8;x7;x3;x4;x5;x6]] t))) =
  (fail_event p x1 t ∩
    (fail_event p x2 t ∪ fail_event p x8 t ∪ fail_event p x7 t ∪
     fail_event p x3 t ∪ fail_event p x4 t ∪ fail_event p x5 t ∪
     fail_event p x6 t))``,
RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]++SRW_TAC[][EXTENSION,GSPECIFICATION] ++ metis_tac[]);
(**************)
val RBD_2 = store_thm("RBD_2",
``(rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p
	  [[x1]; [x9;x10]; [x13;x14]; [x15;x16]; [x11;x12]] t))) =
  (fail_event p x1 t ∩
   ((fail_event p x9 t ∪ fail_event p x10 t) ∩
    (fail_event p x13 t ∪ fail_event p x14 t) ∩
    (fail_event p x15 t ∪ fail_event p x16 t) ∩
    (fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p))``,
RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);
(******************)
val EVENT2LIST = store_thm("EVENT2LIST",
``!X Y p t.
[fail_event p X t; fail_event p Y t] = fail_event_list p [X;Y] t``,
rw[fail_event_list_def]);
(************************)
val TO_NOT_EVENT = store_thm("TO_NOT_EVENT",
``!p x1 x2 t.
  gate_list [p_space p DIFF fail_event p x1 t; (fail_event p x2 t)] =
  gate_list [FTree p (NOT (atomic (fail_event p x1 t))); (fail_event p x2 t)]``,
rw[gate_list_def,FTree_def]);
(************************)
val TO_END_EVENTS = store_thm("TO_END_EVENTS",
``!p x1 x2 t.
 FTree p
  (OR (gate_list
        [FTree p (NOT (atomic (fail_event p x1 t)));
	 fail_event p x2 t])) =
 ((FTree p (NOT (atomic (fail_event p x1 t)))) UNION
   (FTree p (OR (gate_list [fail_event p x2 t]))))``,
rw[FTree_def,gate_list_def]);
(**********INTER UNION ****)

val INTER_S = store_thm("INTER_S",
``!A B C. A INTER B INTER (A INTER C) = A INTER B INTER C``,
SRW_TAC[][INTER_ASSOC,INTER_IDEMPOT,EXTENSION,GSPECIFICATION] ++ metis_tac[]);

val INTER_ARRAY = store_thm("INTER_ARRAY",
``a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i  =
  (a /\ d /\ g ) /\ (b /\ e /\ h ) /\ (c /\ f /\ i) ``,
metis_tac[]);

val INTER_lem00= store_thm("INTER_lem00",
``!A B C. B INTER A INTER C INTER A = B INTER C INTER A``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

val INTER_lem01= store_thm("INTER_lem01",
``!A B C.
B INTER A INTER B = A INTER  B``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

val INTER_lem02= store_thm("INTER_lem02",
``!A B C D.
A INTER D INTER B INTER A INTER B INTER C =
A INTER D INTER B INTER C``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

val INTER_lem03 = store_thm("INTER_lem03",
``!A B C.
A INTER B INTER B INTER C =
A INTER B INTER C``,
SRW_TAC[][GSPECIFICATION,EXTENSION]
++ metis_tac[]);

(*
val INTER_UNION_lem4 = store_thm("INTER_UNION_lem4",
``!A B C D E G H.
A INTER B INTER G INTER H INTER (C UNION D UNION E) =
(A INTER B INTER G INTER H INTER C) UNION (A INTER B INTER G INTER H INTER (D UNION E))``,
SRW_TAC[][GSPECIFICATION,EXTENSION]
++ metis_tac[]);
*)
val AND_ARRAY_0 = store_thm("AND_ARRAY_0",
``a /\ b /\ c /\ e /\ f /\ g /\ h /\ i /\ a1 /\ b1 /\ c1 /\ d1 /\ e1 /\ f1 /\ g1 /\ h1 /\ i1 /\ a2 /\ b2 /\ c2 /\ x1 /\ x2 /\ x3 /\ d2 /\ e2 =
 (a /\ b /\ e /\ g /\ h /\ a1 /\ b1 /\ d1 /\ e1 /\ g1 /\ h1 /\ a2 /\ b2 /\ d2 /\ e2 /\ x1 /\ x2) /\ (c /\ f /\ i /\ c1 /\ f1 /\ i1 /\ c2 /\ x3)``,
metis_tac[]);

val INTER_UNION_lem1 = store_thm("INTER_UNION_lem1",
``! A B C D. A UNION (B UNION C) INTER D = A UNION (C INTER D) UNION (B INTER D)``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

val INTER_UNION_lem2 = store_thm("INTER_UNION_lem2",
``!a d  A B C D E. A UNION a UNION (B INTER C) UNION D UNION d UNION E = A UNION D UNION d UNION a UNION (B INTER C) UNION E``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

val INTER_UNION_lem3 = store_thm("INTER_UNION_lem3",
``! A B C. A UNION B UNION C = B UNION (C UNION A)``,
SRW_TAC[][GSPECIFICATION,EXTENSION]++metis_tac[]);

(********LISTS ***)
val LIST_APPEND22TL = store_thm("LIST_APPEND22TL",
``!a b c d t. a::b::c::d::t=[a;b]++[c;d]++t``,rw[]);

val LIST_APPEND44TL = store_thm("LIST_APPEND44TL",
``!a b c d a1 b1 c1 d1 t.
 a::b::c::d::a1::b1::c1::d1::t=[a;b;c;d]++[a1;b1;c1;d1]++t``,rw[]);

val LIST_APPEND8TL = store_thm("LIST_APPEND8TL",
``!a b c d a1 b1 c1 d1 t.
 a::b::c::d::a1::b1::c1::d1::t=[a;b;c;d;a1;b1;c1;d1]++t``,rw[]);

val LIST_APPEND9TL = store_thm("LIST_APPEND9TL",
``! a' a b c d a1 b1 c1 d1 t.
 a'::a::b::c::d::a1::b1::c1::d1::t=[a';a;b;c;d;a1;b1;c1;d1]++t``,rw[]);

val LIST_APPEND_ASSOC = store_thm("LIST_APPEND_ASSOC",
``!l l1 l2. l++l1++l2 =l++(l1++l2)``,rw[]);

val LIST_APPEND_HD = store_thm("LIST_APPEND_HD",
``!h t. (h::t) =[h]++(t)``, rw[]);

val LIST_APPEND_2HD = store_thm("LIST_APPEND_2HD",
`` !h h1 t. (h::h1::t) = [h;h1]++(t) ``, rw[]);

val LIST_APPEND_3HD = store_thm("LIST_APPEND_3HD",
``!h h1 h2 t. (h::h1::h2::t) =[h;h1;h2]++(t)``, rw[]);

val LIST_APPEND_4HD = store_thm("LIST_APPEND_4HD",
``!h h1 h2 h3 t. (h::h1::h2::h3::t) =[h;h1;h2;h3]++(t)``, rw[]);

(************************************************************)
val real_add_sub_lem = store_thm("real_add_sub_lem",
``a:real-a9+a10+b-ab10-a10-ab+ab10+a910+ab9-ab10=a+b+a910+ab9-a9-ab-ab10``,
   REAL_ARITH_TAC);
(*******RBDS INTER UNION ***********************************)
val RBD_90 = store_thm("RBD_90",
``(rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p [[x13;x14];[x15;x16];[x11;x12]] t))) =
  ((fail_event p x13 t ∪ fail_event p x14 t) ∩
   (fail_event p x15 t ∪ fail_event p x16 t) ∩
   (fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p)``,
 RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);

val RBD_900 = store_thm("RBD_900",
``(rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p [[x13;x14];[x15;x16];[x11;x12]] t))) =
  ((fail_event p x13 t ∪ fail_event p x14 t) ∩
   ((fail_event p x15 t ∪ fail_event p x16 t) ∩
   ((fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p)))``,
RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);

val RBD_911 = store_thm("RBD_911",
``(rbd_struct p
     ((λa. parallel (rbd_list a))
        (fail_event_list p [x3; x4; x5; x6; x7; x8; x1; x2] t))) =
   (fail_event p x4 t ∪
    (fail_event p x7 t ∪
     (fail_event p x5 t ∪
      (fail_event p x3 t ∪
       (fail_event p x8 t ∪
        (fail_event p x6 t ∪ (fail_event p x2 t ∪ fail_event p x1 t)))))))``,
RW_TAC list_ss[fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,UNION_EMPTY]
++ SRW_TAC[][GSPECIFICATION,EXTENSION]
++ metis_tac[]);

val RBD_91 = store_thm("RBD_91",
``(rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p
	  [[x9];[x13;x14];[x15;x16];[x11;x12]] t))) =
   (fail_event p x9 t ∩ (fail_event p x13 t ∪ fail_event p x14 t) ∩
   (fail_event p x15 t ∪ fail_event p x16 t) ∩
   (fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p)``,
RW_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);


val RBD_INTER_series = store_thm("RBD_INTER_series",
``!x9 L p t.
(fail_event p x9 t ∩
 rbd_struct p
   ((series of (λa. parallel (rbd_list a)))
      (two_dim_fail_event_list p L t))) =
 rbd_struct p
   ((series of (λa. parallel (rbd_list a)))
      (two_dim_fail_event_list p ([x9]::L) t))``,
RW_TAC list_ss[three_dim_fail_event_list_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);

val RBD_INTER_series1 = store_thm("RBD_INTER_series1",
``!x9 x10 L p t.
 (fail_event p x9 t ∩ fail_event p x10 t ∩
  rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p L t))) =
  rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p ([x9]::[x10]::L) t))``,
RW_TAC list_ss[three_dim_fail_event_list_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]);

val RBD_INTER_series2 = store_thm("RBD_INTER_series2",
``!L L1 p t.
   (rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p L t)) ∩
   rbd_struct p (parallel (rbd_list (fail_event_list p L1 t)))) =
   (rbd_struct p
     ((series of (λa. parallel (rbd_list a)))
        (two_dim_fail_event_list p (L1::L) t)))``,
RW_TAC list_ss[three_dim_fail_event_list_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]
++ SRW_TAC[][GSPECIFICATION,EXTENSION]
++ metis_tac[]);

val RBD_92 = store_thm("RBD_92",
``(rbd_struct p
     ((parallel of (series of (λa. parallel (rbd_list a))))
         (three_dim_fail_event_list p
	     [[[x10];[x13;x14];[x15;x16];[x11;x12]];
	      [[x3;x4;x5;x6;x7;x8;x1;x2]]] t))) =
  (fail_event p x10 t ∩ (fail_event p x13 t ∪ fail_event p x14 t) ∩
   (fail_event p x15 t ∪ fail_event p x16 t) ∩
   (fail_event p x11 t ∪ fail_event p x12 t) ∩ p_space p ∪
   fail_event p x4 t ∪ fail_event p x7 t ∪ fail_event p x5 t ∪
   fail_event p x3 t ∪ fail_event p x8 t ∪ fail_event p x6 t ∪
   fail_event p x2 t ∪ fail_event p x1 t)``,
RW_TAC list_ss[three_dim_fail_event_list_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,fail_event_def,UNION_ASSOC,INTER_ASSOC]
++SRW_TAC[][EXTENSION,GSPECIFICATION]++metis_tac[]);

(*----------------------------------------------------------------------*)
(************************************************************)
(************* THEOREM :  fail_prob_railway_FT *************)
(************************************************************)
val fail_prob_railway_FT = store_thm("fail_prob_railway_FT",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
in_events p
 ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
exp_dist_list p [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16]
                 [c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p (FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		      OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		      AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		           OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			   OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			   OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		     OR (gate_list ([fail_event p x7 t; fail_event p x8 t]));
		     OR (gate_list ([fail_event p x1 t; fail_event p x2 t]))])) =
1 −
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
 exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) *
 exp (-(c2 * t)) *
 (1 − 
  (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
  (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
RW_TAC std_ss[EVENT2LIST]
++ DEP_REWRITE_TAC[railway_FT_equi_RBD]
++ RW_TAC std_ss[in_events_def,fail_event_list_def]
>> (FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC std_ss[of_DEF]
++ DEP_REWRITE_TAC[REWRITE_RULE[of_DEF]rel_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (Q.EXISTS_TAC `[]`
   ++ RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC list_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM,three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ FULL_SIMP_TAC list_ss[exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def,fail_event_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);

(*----------------------------------------------------------------------*)
val rail_signal_FT_def = Define
`rail_signal_FT p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t =
 (FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		      OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		      AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		           OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			   OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			   OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		     OR (gate_list ([fail_event p x7 t; fail_event p x8 t]));
		     OR (gate_list ([fail_event p x1 t; fail_event p x2 t]))])) `;

(*----------------------------------------------------------------------*)
(************************************************************************)
(************* THEOREM : Prob of Railway Signal Fault Tree Model ********)
(************************************************************************)

val fail_prob_rail_signal_FT = store_thm("fail_prob_rail_signal_FT",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
in_events p
 ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
exp_dist_list p [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16]
                 [c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p (rail_signal_FT p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t) =
1 −
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
 exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) *
 exp (-(c2 * t)) *
 (1 − 
  (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
  (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
rw[rail_signal_FT_def,fail_prob_railway_FT]);
(*----------------------------------------------------------------------*)
(*********************************************)
(*** THEOREM : fail_prob_railway_FT1 *********)
(*********************************************)
val fail_prob_railway_FT1 = store_thm("fail_prob_railway_FT1",
``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
     c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (CDF p x1 t = 1) /\
mutual_indep p
   ((fail_event_list p
      [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
       x11; x12] t)) /\
in_events p
   ((fail_event_list p
      [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
       x11; x12] t)) /\
exp_dist_list p
 [x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16]
 [c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p ((FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		       OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		       AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		            OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			    OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			    OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		       OR (gate_list ([ fail_event p x7 t; fail_event p x8 t]));
		       OR (gate_list ([fail_event p x1 t; fail_event p x2 t]))]))) = 1) ``,
RW_TAC std_ss[EVENT2LIST]
++ DEP_REWRITE_TAC[railway_FT_equi_RBD]
++ RW_TAC std_ss[in_events_def,fail_event_list_def]
>> (FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC std_ss[of_DEF]
++ DEP_REWRITE_TAC[REWRITE_RULE[of_DEF]rel_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (Q.EXISTS_TAC `[]`
   ++ RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC list_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM,three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ FULL_SIMP_TAC list_ss[exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def,fail_event_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);

(*-------------------------*)
val CDF_SPACE = store_thm("CDF_SPACE",
  ``!p x t. prob_space p /\ (fail_event p x t = p_space p) ==> (CDF p x t =  1)``,
rw[CDF_def,VDCTheory.exp_dist_def,distribution_def,fail_event_def,PROB_UNIV]);


(*--------------------------

val BImp_measure_rail_alt = store_thm("BImp_measure_rail_alt",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t.
  prob_space p /\ (fail_event p x1 t = p_space p) ==>
(BImp_measure p 0
    (\b. (FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		       OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		       AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		            OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			    OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			    OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		       OR (gate_list ([ fail_event p x7 t; fail_event p x8 t]));
		       OR (gate_list b)])))
    ([fail_event p x1 t; fail_event p x2 t]) =
birnhaum_Rel_IMP_Vehicle p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
   x13 x14 x15 x16 t)``,
rw[BImp_measure_def,birnhaum_Rel_IMP_Vehicle_def,birnhaum_IMP_Vehicle_def,coherent_struct_update_def,s_comp_def,LUPDATE_def,f_comp_def,PHI_STRUCT_RW_def,coherent_struct_def]);





(************************************************************)
(************* THEOREM :  fail_prob_railway_FT0 *************)
(************************************************************)
val fail_prob_railway_FT0 = store_thm("fail_prob_railway_FT0",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
       c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (CDF p x1 t = 1) /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
in_events p
 ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16; x11; x12] t)) /\
exp_dist_list p [x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16]
                 [c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p (FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		      OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		      AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		           OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			   OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			   OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		     OR (gate_list ([fail_event p x7 t; fail_event p x8 t]));
		     OR (gate_list ([p_space p DIFF fail_event p x1 t; fail_event p x2 t]))])) =
1 −
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
 exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) *
 exp (-(c2 * t)) *
 (1 − 
  (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
  (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
rw[FTree_def,UNION_EMPTY,INTER_ASSOC,UNION_ASSOC]
++ rw[TO_NOT_EVENT,TO_END_EVENTS,UNION_COMM]
++ rw[FTree_def,gate_list_def]++rw[GSYM UNION_ASSOC]
++ DEP_ONCE_REWRITE_TAC[Prob_Incl_excl]
++ DEP_ONCE_REWRITE_TAC[PROB_COMPL] 
++ CONJ_TAC
>> (FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def])
++ CONJ_TAC
>> (rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]
    ++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
    ++ FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def,EVENTS_COMPL])
++ rw[GSYM compl_pspace_def]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]
++ CONJ_TAC
>> (rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]
    ++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
    ++ FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def]) 
++ rw[realTheory.real_sub]++rw[REAL_NEG_ADD]++rw[REAL_ADD_ASSOC]
++ RW_TAC real_ss[GSYM real_sub] 
++ rw[UNION_ASSOC]++ ONCE_REWRITE_TAC[UNION_OVER_INTER]
++ DEP_ONCE_REWRITE_TAC[Prob_Incl_excl] 
++ CONJ_TAC 
>> (rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]
    ++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
    ++ FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def]) 
++ rw[INTER_S]++rw[GSYM RBD_0]++rw[GSYM RBD_1,GSYM RBD_2] 
++ DEP_REWRITE_TAC[series_parallel_struct_thm_v2] 
++ CONJ_TAC
>> (FULL_SIMP_TAC list_ss[fail_event_list_def,three_dim_fail_event_list_def,
          two_dim_fail_event_list_def] 
   ++ fs[INTER_ARRAY] 
   ++ CONJ_TAC 
   >> (fs[NULL] ++ metis_tac[NULL]) 
   ++ CONJ_TAC
   >> (fs[in_events_def]++metis_tac[]) 
   ++ rw[]
   >> (ONCE_REWRITE_TAC[LIST_APPEND22TL]++DEP_ONCE_REWRITE_TAC[mutual_indep_append1]
       ++ DEP_ONCE_REWRITE_TAC[mutual_indep_append_sym]
       ++ DEP_REWRITE_TAC[mutual_indep_cons_append13]
       ++ Q.EXISTS_TAC `[[fail_event p x9 t;
         fail_event p x10 t; fail_event p x13 t; fail_event p x14 t;
         fail_event p x15 t; fail_event p x16 t; fail_event p x11 t;
         fail_event p x12 t]]` ++ FULL_SIMP_TAC list_ss[]) 
   >> (ONCE_REWRITE_TAC[LIST_APPEND_HD]++DEP_REWRITE_TAC[mutual_indep_cons_append14]
       ++ Q.EXISTS_TAC `fail_event p x2 t` 
       ++ DEP_REWRITE_TAC[mutual_indep_front_append]
       ++ Q.EXISTS_TAC `[fail_event p x3 t; fail_event p x4 t; fail_event p x5 t;
          fail_event p x6 t; fail_event p x7 t; fail_event p x8 t]` 
       ++ FULL_SIMP_TAC list_ss[]) 
   ++  ONCE_REWRITE_TAC[LIST_APPEND22TL]++DEP_ONCE_REWRITE_TAC[mutual_indep_append1]
   ++ rw[] ++ ONCE_REWRITE_TAC[LIST_APPEND44TL]
   ++ DEP_ONCE_REWRITE_TAC[mutual_indep_append1]
   ++ FULL_SIMP_TAC list_ss[])
++ rw[of_DEF]
++ FULL_SIMP_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,
           fail_event_def,in_events_def,CDF_def, PREIMAGE_def,exp_dist_list_def,
           VDCTheory.exp_dist_def,CDF_def,distribution_def]
++ RW_TAC real_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM]
++ REAL_ARITH_TAC);


(**********************************************************)
(*** THEOREM : birnhaum_Rel_IMP_Vehicle_THM       *********)
(**********************************************************)
val birnhaum_Rel_IMP_Vehicle_THM = store_thm("birnhaum_Rel_IMP_Vehicle_THM",
`` !p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (CDF p x1 t = 1) /\
exp_dist_list p
  [x3; x4; x5; x6; x7; x8; x2; x9; x10; x13; x14; x15; x16; x11; x12]
  [c3; c4; c5; c6; c7; c8; c2; c9; c10; c13; c14; c15; c16; c11; c12] /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
      x11; x12] t)) /\
in_events p
 ((fail_event_list p
    [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
     x11; x12] t)) ==> 
(birnhaum_Rel_IMP_Vehicle p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
   x13 x14 x15 x16 t = 
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
 exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c2 * t)) *
 (1 -
  (1 - exp (-(c9 * t)) * exp (-(c10 * t))) *
  (1 - exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 - exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 - exp (-(c11 * t)) * exp (-(c12 * t)))))``,
RW_TAC std_ss[birnhaum_Rel_IMP_Vehicle_def, birnhaum_IMP_Vehicle_def,PHI_STRUCT_RW_def,f_comp_def,s_comp_def]
++ DEP_REWRITE_TAC[fail_prob_railway_FT1]
++ CONJ_TAC
>> (  Q.EXISTS_TAC `c2`  ++ Q.EXISTS_TAC `c3`  ++ Q.EXISTS_TAC `c4` 
   ++ Q.EXISTS_TAC `c5`  ++ Q.EXISTS_TAC `c6`  ++ Q.EXISTS_TAC `c7` 
   ++ Q.EXISTS_TAC `c8`  ++ Q.EXISTS_TAC `c9`  ++ Q.EXISTS_TAC `c10` 
   ++ Q.EXISTS_TAC `c11`  ++ Q.EXISTS_TAC `c12`  ++ Q.EXISTS_TAC `c13` 
   ++ Q.EXISTS_TAC `c14`  ++ Q.EXISTS_TAC `c15`  ++ Q.EXISTS_TAC `c16`
   ++ fs[exp_dist_list_def,VDCTheory.exp_dist_def,in_events_def,fail_event_list_def,fail_event_def,three_dim_fail_event_list_def,two_dim_fail_event_list_def,FLAT,MEM,in_events_def] ++ metis_tac[])
++ DEP_REWRITE_TAC[fail_prob_railway_FT0]
++ CONJ_TAC
>> (fs[exp_dist_list_def,VDCTheory.exp_dist_def,in_events_def,fail_event_list_def,fail_event_def,three_dim_fail_event_list_def,two_dim_fail_event_list_def,FLAT,MEM,in_events_def, CDF_def]
   ++ metis_tac[])
++ REAL_ARITH_TAC);

(*------------------------------*)
val Birnbaum_imp_rail_vehicle_fail = store_thm("Birnbaum_imp_rail_vehicle_fail",
`` !p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (fail_event p x1 t = p_space p) /\
exp_dist_list p
  [x3; x4; x5; x6; x7; x8; x2; x9; x10; x13; x14; x15; x16; x11; x12]
  [c3; c4; c5; c6; c7; c8; c2; c9; c10; c13; c14; c15; c16; c11; c12] /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
      x11; x12] t)) /\
in_events p
 ((fail_event_list p
    [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
     x11; x12] t)) ==> 
(BImp_measure p 0
            (λb.
                 FTree p
                   (OR
                      [OR (gate_list [ω p x3 t; ω p x4 t]);
                       OR (gate_list [ω p x5 t; ω p x6 t]);
                       AND
                         [OR (gate_list [ω p x9 t; ω p x10 t]);
                          OR (gate_list [ω p x13 t; ω p x14 t]);
                          OR (gate_list [ω p x15 t; ω p x16 t]);
                          OR (gate_list [ω p x11 t; ω p x12 t])];
                       OR (gate_list [ω p x7 t; ω p x8 t]); OR (gate_list b)]))
            [ω p x1 t; ω p x2 t] = 
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
 exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c2 * t)) *
 (1 -
  (1 - exp (-(c9 * t)) * exp (-(c10 * t))) *
  (1 - exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 - exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 - exp (-(c11 * t)) * exp (-(c12 * t)))))``,
rpt gen_tac
\\ rpt disch_tac
\\ DEP_REWRITE_TAC[BImp_measure_rail_alt]
\\ rw[]
\\ DEP_REWRITE_TAC[birnhaum_Rel_IMP_Vehicle_THM]
\\ rw[]
\\ irule CDF_SPACE
\\ rw[]);
(*----------------------------------------------------------------------*)
(***********************************************)
(*** THEOREM : fail_prob_railway_FT9_1 *********)
(***********************************************)
val fail_prob_railway_FT9_1 = store_thm("fail_prob_railway_FT9_1",
``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 c1 c2 c3 c4 c5
     c6 c7 c8 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (CDF p x9 t= 1) /\
mutual_indep p
 ((fail_event_list p
    [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
     x11; x12] t)) /\
in_events p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
      x11; x12] t)) /\
exp_dist_list p
 [x1;x2;x3;x4;x5;x6;x7;x8;x10;x11;x12;x13;x14;x15;x16]
 [c1;c2;c3;c4;c5;c6;c7;c8;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p ((FTree p (OR [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
		       OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
		       AND [OR (gate_list ([fail_event p x9 t; fail_event p x10 t]));
		            OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
			    OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
			    OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
		      OR (gate_list ([fail_event p x7 t; fail_event p x8 t]));
		      OR (gate_list ([fail_event p x1 t; fail_event p x2 t]))]))) = 
 1 −
  exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
  exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) *
  exp (-(c1 * t)) * exp (-(c2 * t)) *
  (1 −
    (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
    (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
    (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
RW_TAC std_ss[EVENT2LIST]
++ DEP_REWRITE_TAC[railway_FT_equi_RBD]
++ RW_TAC std_ss[in_events_def,fail_event_list_def]
>> (FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC std_ss[of_DEF]
++ DEP_REWRITE_TAC[REWRITE_RULE[of_DEF]rel_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (Q.EXISTS_TAC `[]`
   ++ RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC list_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM,three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ FULL_SIMP_TAC list_ss[exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def,fail_event_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);

(************************************************************)
(************* THEOREM :  fail_prob_railway_FT9_0*************)
(************************************************************)
val fail_prob_railway_FT9_0 = store_thm("fail_prob_railway_FT9_0",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 c13 c14 c15 c16 t.
 (0 <= t) /\
 prob_space p /\
 (CDF p x9 t = 1) /\
 mutual_indep p
    (fail_event_list p
       [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
        x11; x12] t ) /\
 in_events p
   (fail_event_list p
      [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
       x11; x12] t ) /\
 exp_dist_list p
    [x1;x2;x3;x4;x5;x6;x7;x8;x10;x11;x12;x13;x14;x15;x16]
    [c1;c2;c3;c4;c5;c6;c7;c8;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p
   (FTree p
     (OR
        [OR (gate_list ([fail_event p x3 t; fail_event p x4 t]));
	 OR (gate_list ([fail_event p x5 t; fail_event p x6 t]));
	 AND[OR
	      (gate_list
	          ([p_space p DIFF fail_event p x9 t; fail_event p x10 t]));
	     OR (gate_list ([fail_event p x13 t; fail_event p x14 t]));
	     OR (gate_list ([fail_event p x15 t; fail_event p x16 t]));
	     OR (gate_list ([fail_event p x11 t; fail_event p x12 t]))];
	 OR (gate_list ([fail_event p x7 t; fail_event p x8 t]));
	 OR (gate_list ([fail_event p x1 t; fail_event p x2 t]))])) =
 1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
    exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) *
    exp (-(c2 * t)) *
    (1 −  
     (1 − exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
rw[FTree_def,gate_list_def,UNION_ASSOC]++rw[INTER_UNION_lem1]
++ rw[UNION_COMM]++rw[UNION_ASSOC]++rw[INTER_ASSOC]
++ rw[UNION_ASSOC]++rw[INTER_UNION_lem2]++rw[INTER_UNION_lem3]
++ DEP_ONCE_REWRITE_TAC[Prob_Incl_excl]++CONJ_TAC 
>> (rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]
   ++DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
   ++FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def,EVENTS_COMPL])
++ rw[GSYM compl_pspace_def]++rw[GSYM INTER_ASSOC]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]++CONJ_TAC 
>> (rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]++
     DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]++
     FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def,EVENTS_COMPL])
++ rw[GSYM RBD_900,GSYM RBD_911] 
++ ONCE_REWRITE_TAC[INTER_COMM] ++ rw[INTER_ASSOC,GSYM RBD_90] 
++ ONCE_REWRITE_TAC[GSYM INTER_COMM] ++ rw[INTER_ASSOC,GSYM RBD_90] 
++ rw[UNION_OVER_INTER] ++ rw[INTER_ASSOC,INTER_lem00,INTER_lem01]    
++ DEP_REWRITE_TAC[Prob_Incl_excl]++ CONJ_TAC 
>> (fs[three_dim_fail_event_list_def,two_dim_fail_event_list_def,fail_event_list_def,
       rbd_struct_def,rbd_list_def,of_DEF,UNION_EMPTY,UNION_ASSOC,INTER_ASSOC] 
    ++ rw[INTER_COMM]++DEP_REWRITE_TAC[INTER_PSPACE]
    ++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
    ++ FULL_SIMP_TAC list_ss[fail_event_list_def,in_events_def,EVENTS_COMPL]) 
++ rw[INTER_ASSOC]++rw[INTER_lem03]++rw[INTER_lem02] 
++ rw[realTheory.real_sub]++rw[REAL_NEG_ADD]++rw[REAL_ADD_ASSOC]
++ RW_TAC real_ss[GSYM real_sub] 
++ rw[RBD_INTER_series,RBD_INTER_series1,RBD_INTER_series2] 
++ DEP_REWRITE_TAC[series_parallel_struct_thm,parallel_struct_thm]
++ CONJ_TAC 
>> (fs[two_dim_fail_event_list_def,fail_event_list_def,MEM,in_events_def]
   ++ fs[AND_ARRAY_0]
   ++ CONJ_TAC
   >> (fs[]++metis_tac[NULL]++rw[])
   ++ rw[]
   >> (DEP_REWRITE_TAC[mutual_indep_front_append]
      ++ Q.EXISTS_TAC `[fail_event p x3 t; fail_event p x4 t; fail_event p x5 t;
         fail_event p x6 t; fail_event p x7 t; fail_event p x8 t;
         fail_event p x1 t; fail_event p x2 t; fail_event p x9 t;
         fail_event p x10 t]`++FULL_SIMP_TAC list_ss[]) 
   >> (DEP_REWRITE_TAC[mutual_indep_front_append] 
      ++ Q.EXISTS_TAC `[fail_event p x9 t;
         fail_event p x10 t; fail_event p x13 t; fail_event p x14 t;
         fail_event p x15 t; fail_event p x16 t; fail_event p x11 t;
         fail_event p x12 t]` 
      ++ DEP_ONCE_REWRITE_TAC[mutual_indep_append_sym]
      ++ FULL_SIMP_TAC list_ss[]) 
   >> (ONCE_REWRITE_TAC[LIST_APPEND_HD]  
      ++ DEP_REWRITE_TAC[mutual_indep_cons_append14] 
      ++ Q.EXISTS_TAC `fail_event p x10 t` 
      ++ DEP_REWRITE_TAC[mutual_indep_front_append]
      ++ Q.EXISTS_TAC `[fail_event p x3 t; fail_event p x4 t; fail_event p x5 t;
         fail_event p x6 t; fail_event p x7 t; fail_event p x8 t;
         fail_event p x1 t; fail_event p x2 t]`
      ++ FULL_SIMP_TAC list_ss[])
   >> (DEP_REWRITE_TAC[mutual_indep_front_append]
      ++ Q.EXISTS_TAC `[fail_event p x3 t; fail_event p x4 t; fail_event p x5 t;
         fail_event p x6 t; fail_event p x7 t; fail_event p x8 t;
         fail_event p x1 t; fail_event p x2 t;fail_event p x9 t]`
      ++ FULL_SIMP_TAC list_ss[])
   >> (ONCE_REWRITE_TAC[LIST_APPEND8TL] 
      ++ DEP_REWRITE_TAC[mutual_indep_cons_append14]
      ++ Q.EXISTS_TAC `fail_event p x9 t` ++FULL_SIMP_TAC list_ss[]) 
   >> (ONCE_REWRITE_TAC[LIST_APPEND8TL]
      ++ DEP_REWRITE_TAC[mutual_indep_cons_append14]
      ++ Q.EXISTS_TAC `fail_event p x10 t`
      ++ DEP_REWRITE_TAC[mutual_indep_cons_append14]
      ++ Q.EXISTS_TAC `fail_event p x9 t` ++ FULL_SIMP_TAC list_ss[]) 

   >> (DEP_REWRITE_TAC[mutual_indep_front_append] 
      ++ Q.EXISTS_TAC `[fail_event p x3 t; fail_event p x4 t; fail_event p x5 t;
         fail_event p x6 t; fail_event p x7 t; fail_event p x8 t;
         fail_event p x1 t; fail_event p x2 t]`
      ++ FULL_SIMP_TAC list_ss[]) 
   ++ ONCE_REWRITE_TAC[LIST_APPEND9TL] 
   ++ DEP_REWRITE_TAC[mutual_indep_cons_append14] 
   ++ Q.EXISTS_TAC `fail_event p x10 t` 
   ++ FULL_SIMP_TAC list_ss[])
++ rw[of_DEF]
++ FULL_SIMP_TAC list_ss[two_dim_fail_event_list_def,fail_event_list_def,
                         fail_event_def,in_events_def,CDF_def, PREIMAGE_def,
         exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def] 
++ RW_TAC list_ss[list_prod_def,list_prod_one_minus_rel_def,one_minus_list_def,
   list_prob_def,o_THM]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ REAL_ARITH_TAC);

(*********************************************************) 
(************** THEOREM: birnhaum_Rel_IMP_X9_THM *********) 
(*********************************************************)
val birnhaum_Rel_IMP_X9_THM = store_thm("birnhaum_Rel_IMP_X9_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
     c2 c3 c4 c5 c6 c7 c8 c1 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (CDF p x9 t = 1) /\
exp_dist_list p
  [x3; x4; x5; x6; x7; x8; x2; x1; x10; x13; x14; x15; x16; x11; x12]
  [c3; c4; c5; c6; c7; c8; c2; c1; c10; c13; c14; c15; c16; c11; c12] /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
      x11; x12] t)) /\
in_events p
 ((fail_event_list p
    [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
     x11; x12] t)) ==> 
(birnhaum_Rel_IMP_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    x14 x15 x16 t = 
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
 exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) *
 exp (-(c1 * t)) * exp (-(c2 * t)) * exp (-(c10 * t)) *
 ((1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
RW_TAC std_ss[birnhaum_Rel_IMP_X9_def, birnhaum_IMP_X9_def,PHI_STRUCT_RW_def,f_comp_def,s_comp_def]
++ DEP_REWRITE_TAC[fail_prob_railway_FT9_1]
++ CONJ_TAC
>>(Q.EXISTS_TAC `c10`
   ++ fs[exp_dist_list_def,VDCTheory.exp_dist_def,in_events_def,fail_event_list_def,
         fail_event_def,three_dim_fail_event_list_def,two_dim_fail_event_list_def,
         FLAT,MEM,in_events_def]
   ++ metis_tac[])
++ DEP_REWRITE_TAC[fail_prob_railway_FT9_0]++CONJ_TAC
>>(fs[exp_dist_list_def,VDCTheory.exp_dist_def,in_events_def,fail_event_list_def,
      fail_event_def,three_dim_fail_event_list_def,two_dim_fail_event_list_def,
      FLAT,MEM,in_events_def, CDF_def]
   ++ metis_tac[])
++ REAL_ARITH_TAC);

(*-----------------------------*)
val BImp_alarm_fail_alt = store_thm("BImp_alarm_fail_alt",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 t.
prob_space p ∧ (ω p x9 t = p_space p) ⇒
 (BImp_measure p 0
            (λb.
                 FTree p
                   (OR
                      [OR (gate_list [ω p x3 t; ω p x4 t]);
                       OR (gate_list [ω p x5 t; ω p x6 t]);
                       AND
                         [OR (gate_list b);
                          OR (gate_list [ω p x13 t; ω p x14 t]);
                          OR (gate_list [ω p x15 t; ω p x16 t]);
                          OR (gate_list [ω p x11 t; ω p x12 t])];
                       OR (gate_list [ω p x7 t; ω p x8 t]);
		       OR (gate_list ([ω p x1 t; ω p x2 t]))]))
	     ([ω p x9 t; ω p x10 t]) =
birnhaum_Rel_IMP_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    x14 x15 x16 t)``,
rw[BImp_measure_def,birnhaum_Rel_IMP_X9_def,birnhaum_IMP_X9_def,coherent_struct_update_def,s_comp_def,LUPDATE_def,f_comp_def,PHI_STRUCT_RW_def,coherent_struct_def]);


(*---------------------------*)
val birnhaum_IMP_alarm_THM = store_thm("birnhaum_IMP_alarm_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
     c2 c3 c4 c5 c6 c7 c8 c1 c10 c11 c12 c13 c14 c15 c16 t.
(0 <= t) /\ prob_space p /\ (ω p x9 t = p_space p) /\
exp_dist_list p
  [x3; x4; x5; x6; x7; x8; x2; x1; x10; x13; x14; x15; x16; x11; x12]
  [c3; c4; c5; c6; c7; c8; c2; c1; c10; c13; c14; c15; c16; c11; c12] /\
mutual_indep p
  ((fail_event_list p
     [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
      x11; x12] t)) /\
in_events p
 ((fail_event_list p
    [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
     x11; x12] t)) ==> 
(BImp_measure p 0
            (λb.
                 FTree p
                   (OR
                      [OR (gate_list [ω p x3 t; ω p x4 t]);
                       OR (gate_list [ω p x5 t; ω p x6 t]);
                       AND
                         [OR (gate_list b);
                          OR (gate_list [ω p x13 t; ω p x14 t]);
                          OR (gate_list [ω p x15 t; ω p x16 t]);
                          OR (gate_list [ω p x11 t; ω p x12 t])];
                       OR (gate_list [ω p x7 t; ω p x8 t]);
                       OR (gate_list [ω p x1 t; ω p x2 t])]))
            [ω p x9 t; ω p x10 t]  = 
 exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) *
 exp (-(c6 * t)) * exp (-(c7 * t)) * exp (-(c8 * t)) *
 exp (-(c1 * t)) * exp (-(c2 * t)) * exp (-(c10 * t)) *
 ((1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
  (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
  (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))``,
rpt gen_tac
\\ rpt disch_tac
\\ DEP_REWRITE_TAC[BImp_alarm_fail_alt,birnhaum_Rel_IMP_X9_THM,CDF_SPACE]
\\ rw[]);

(*************************************************************) 
(************** Definition: Reliability Achievement Worth*****) 
(*************************************************************)


val RAW_X9_def = Define
`RAW_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' =
 prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9' e10 e11 e12 e13 e14 e15 e16) / 
 prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)`;

val RAW_Rel_X9_def = Define
`RAW_Rel_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' t =
RAW_X9 p (f_comp p e1 t) (f_comp p e2 t) (f_comp p e3 t)
         (f_comp p e4 t) (f_comp p e5 t) (f_comp p e6 t) (f_comp p e7 t)
         (f_comp p e8 t) (f_comp p e9 t) (f_comp p e10 t) (f_comp p e11 t)
         (f_comp p e12 t) (f_comp p e13 t) (f_comp p e14 t)
         (f_comp p e15 t) (f_comp p e16 t) (f_comp p e9' t)`;




val RAW_IMP_X9_THM = store_thm("RAW_IMP_X9_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9'
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' c10 c11 c12 c13 c14 c15 c16
        t.
  (CDF p x9' t = 1) /\
  (0 ≤ t ∧ prob_space p ∧
    mutual_indep p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    in_events p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    exp_dist_list p
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x9'; x10; x11; x12; x13; x14; x15;
       x16]
      [c1; c2; c3; c4; c5; c6; c7; c8; c9; c9'; c10; c11; c12; c13; c14; c15; c16]) ==>
  (RAW_Rel_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9' t =
  (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t))))) /
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))) ``,
rw[RAW_Rel_X9_def,RAW_X9_def]
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[f_comp_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT9_1]
\\ rw[]
>- (Q.EXISTS_TAC `c10`
   \\ fs[exp_dist_list_def]
   \\ fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ strip_tac
   >- (sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
        [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
         f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
         f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
         f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
         [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
          f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++
          [f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
           f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]`
      >- (rw[])
      \\ POP_ORW
      \\ irule mutual_indep_append_sym
      \\ sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
      	     [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
            f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t] =
      	    [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++ 
            [f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t]`
      >- (rw[])
      \\ FULL_SIMP_TAC std_ss[]
      \\ WEAKEN_TAC is_eq
      \\ POP_ORW
      \\ imp_res_tac mutual_indep_append_sym
      \\ irule mutual_indep_cons
      \\ Q.EXISTS_TAC `f_comp p x9 t`
      \\ fs[])
  \\ fs[f_comp_def,in_events_def]
  \\ metis_tac[])
\\ rw[PHI_STRUCT_RW_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT]
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t] ++ [f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9' t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
\\ fs[exp_dist_list_def]
\\ metis_tac[]);


val RAW_fail_X9_def = Define
`RAW_fail_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' t =
RAW_X9 p (f_comp p e1 t) (f_comp p e2 t) (f_comp p e3 t)
         (f_comp p e4 t) (f_comp p e5 t) (f_comp p e6 t) (f_comp p e7 t)
         (f_comp p e8 t) (f_comp p e9 t) (f_comp p e10 t) (f_comp p e11 t)
         (f_comp p e12 t) (f_comp p e13 t) (f_comp p e14 t)
         (f_comp p e15 t) (f_comp p e16 t) (s_comp p e9' t)`;


val RAW_fail_IMP_X9_THM = store_thm("RAW_fail_IMP_X9_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9'
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' c10 c11 c12 c13 c14 c15 c16
        t.
  (CDF p x9' t = 1) /\
  (0 ≤ t ∧ prob_space p ∧
    mutual_indep p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    in_events p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    exp_dist_list p
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x9'; x10; x11; x12; x13; x14; x15;
       x16]
      [c1; c2; c3; c4; c5; c6; c7; c8; c9; c9'; c10; c11; c12; c13; c14; c15; c16]) ==>
  (RAW_fail_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9' t =
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c10 * t))) * (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t))))) /
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))) ``,
rw[RAW_fail_X9_def,RAW_X9_def]
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[s_comp_def,f_comp_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT9_0]
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
        [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
         f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
         f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
         f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
         [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
          f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++
          [f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
           f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]`	
    >- (rw[])
    \\ POP_ORW
    \\ irule mutual_indep_append_sym
    \\ sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
      	     [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
            f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t] =
      	    [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++ 
            [f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t]`
    >- (rw[])
    \\ FULL_SIMP_TAC std_ss[]
    \\ WEAKEN_TAC is_eq
    \\ POP_ORW
    \\ imp_res_tac mutual_indep_append_sym
    \\ irule mutual_indep_cons
    \\ Q.EXISTS_TAC `f_comp p x9 t`
    \\ fs[])
>- (fs[f_comp_def,in_events_def,fail_event_list_def]
    \\ metis_tac[])
>- (fs[exp_dist_list_def] \\ metis_tac[])
\\ rw[PHI_STRUCT_RW_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT]
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t] ++ [f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9' t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
\\ fs[exp_dist_list_def]
\\ metis_tac[]);
(***************************************)

(****************************************)



val RRW_fail_X9_def = Define
`RRW_fail_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' t =
RAW_X9 p (f_comp p e1 t) (f_comp p e2 t) (f_comp p e3 t)
         (f_comp p e4 t) (f_comp p e5 t) (f_comp p e6 t) (f_comp p e7 t)
         (f_comp p e8 t) (f_comp p e9 t) (f_comp p e10 t) (f_comp p e11 t)
         (f_comp p e12 t) (f_comp p e13 t) (f_comp p e14 t)
         (f_comp p e15 t) (f_comp p e16 t) (f_comp p e9' t)`;


val RAW_fail_IMP_X9_THM = store_thm("RAW_fail_IMP_X9_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9'
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' c10 c11 c12 c13 c14 c15 c16
        t.
  (CDF p x9 t = 1) /\
  (0 ≤ t ∧ prob_space p ∧
    mutual_indep p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    in_events p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    exp_dist_list p
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x9'; x10; x11; x12; x13; x14; x15;
       x16]
      [c1; c2; c3; c4; c5; c6; c7; c8; c9; c9'; c10; c11; c12; c13; c14; c15; c16]) ==>
  (RRW_fail_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9' t =
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c9' * t)) * exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t))))) /
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))) ``,
rw[RRW_fail_X9_def,RAW_X9_def]
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[s_comp_def,f_comp_def]
\\ mp_tac(Q.ISPECL[`(p :α event # α event event # (α event -> real))`,
                    `(x1 :α -> extreal)`,
         	    `(x2 :α -> extreal)`,
		    `(x3 :α -> extreal)`,
		    `(x4 :α -> extreal)`,
         	    `(x5 :α -> extreal)`,
		    `(x6 :α -> extreal)`,
		    `(x7 :α -> extreal)`,
         	    `(x8 :α -> extreal)`,
		    `(x9' :α -> extreal)`,
		    `(x10 :α -> extreal)`,
         	    `(x11 :α -> extreal)`,
		    `(x12 :α -> extreal)`,
		    `(x13 :α -> extreal)`,
         	    `(x14 :α -> extreal)`,
		    `(x15 :α -> extreal)`,
		    `(x16 :α -> extreal)`,
         	    `(c1 :real)`,`(c2 :real)`,
		    `(c3 :real)`, `(c4 :real)`,
		    `(c5 :real)`, `(c6 :real)`,
         	    `(c7 :real)`, `(c8 :real)`, `(c9' :real)`, `(c10 :real)`, `(c11 :real)`, `(c12 :real)`,
         `(c13 :real)`, `(c14 :real)`, `(c15 :real)`, `(c16 :real)`, `(t :real)`] fail_prob_railway_FT)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ POP_ORW
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++
      [f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9 t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
>- (fs[exp_dist_list_def] \\ metis_tac[])
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[s_comp_def,f_comp_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT9_1]
\\ rw[]
\\ Q.EXISTS_TAC `c10`
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t] ++ [f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9' t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
\\ fs[exp_dist_list_def] \\ metis_tac[]);

(*------------------------------*)


val FV_imp_X9_def = Define
`FV_imp_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' =
(prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16) - prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9' e10 e11 e12 e13 e14 e15 e16)) / 
 prob p (PHI_STRUCT_RW p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)`;

val FV_imp_fail_X9_def = Define
`FV_imp_fail_X9 p e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e9' t =
FV_imp_X9 p (f_comp p e1 t) (f_comp p e2 t) (f_comp p e3 t)
           (f_comp p e4 t) (f_comp p e5 t) (f_comp p e6 t) (f_comp p e7 t)
           (f_comp p e8 t) (f_comp p e9 t) (f_comp p e10 t) (f_comp p e11 t)
           (f_comp p e12 t) (f_comp p e13 t) (f_comp p e14 t)
           (f_comp p e15 t) (f_comp p e16 t) (f_comp p e9' t)`;



val FV_imp_fail_X9_THM = store_thm("FV_imp_fail_X9_THM",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9'
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' c10 c11 c12 c13 c14 c15 c16
        t.
  (CDF p x9' t = 1) /\
  (0 ≤ t ∧ prob_space p ∧
    mutual_indep p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    in_events p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9'; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    exp_dist_list p
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x9'; x10; x11; x12; x13; x14; x15;
       x16]
      [c1; c2; c3; c4; c5; c6; c7; c8; c9; c9'; c10; c11; c12; c13; c14; c15; c16]) ==>
  (FV_imp_fail_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9' t =
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t)))) −
    (1 −
     exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
     exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
     (1 −
      (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
      (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
      (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))) /
   (1 −
    exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
    exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
    (1 −
     (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
     (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
     (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
     (1 − exp (-(c11 * t)) * exp (-(c12 * t))))))``,
rw[FV_imp_fail_X9_def,FV_imp_X9_def]
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[s_comp_def,f_comp_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT]
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t] ++ [f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9' t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
>- (fs[exp_dist_list_def] \\ metis_tac[])
\\ rw[Once PHI_STRUCT_RW_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT9_1]
\\ rw[]
>- (Q.EXISTS_TAC `c10`
   \\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
        [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
         f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
         f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
         f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
         [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
          f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++
          [f_comp p x9' t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
           f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]`	
    >- (rw[])
    \\ POP_ORW
    \\ irule mutual_indep_append_sym
    \\ sg `!x1 x2 x3 x4 x5 x6 x7 x8 x9 x9' x10 x11 x12 x13 x14 x15 x16 x2 t.
      	     [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
            f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t] =
      	    [f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
            f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t] ++ 
            [f_comp p x9 t; f_comp p x9' t; f_comp p x10 t; f_comp p x13 t;
            f_comp p x14 t; f_comp p x15 t; f_comp p x16 t; f_comp p x11 t;
            f_comp p x12 t]`
    >- (rw[])
    \\ FULL_SIMP_TAC std_ss[]
    \\ WEAKEN_TAC is_eq
    \\ POP_ORW
    \\ imp_res_tac mutual_indep_append_sym
    \\ irule mutual_indep_cons
    \\ Q.EXISTS_TAC `f_comp p x9 t`
    \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
\\ fs[exp_dist_list_def] \\ metis_tac[])
\\ rw[Once PHI_STRUCT_RW_def]
\\ once_rewrite_tac[s_comp_def,f_comp_def]
\\ DEP_REWRITE_TAC[fail_prob_railway_FT]
\\ rw[]
>- (fs[fail_event_list_def]
   \\ fs[GSYM f_comp_def]
   \\ once_rewrite_tac[prove (``([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t; f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t] =
       ([f_comp p x3 t; f_comp p x4 t; f_comp p x5 t; f_comp p x6 t;
      f_comp p x7 t; f_comp p x8 t; f_comp p x1 t; f_comp p x2 t;
      f_comp p x9 t] ++ [f_comp p x10 t; f_comp p x13 t; f_comp p x14 t;
      f_comp p x15 t; f_comp p x16 t; f_comp p x11 t; f_comp p x12 t]))``,  rw[])]
   \\  irule mutual_indep_cons
   \\ Q.EXISTS_TAC `f_comp p x9' t`
   \\ irule mutual_indep_cons_append11
   \\  Q.EXISTS_TAC `[]`
   \\ fs[])
>- (fs[fail_event_list_def,in_events_def]
   \\ metis_tac[])
\\ fs[exp_dist_list_def] \\ metis_tac[]);
(*-----------------------------*)
val FV_imp_fail_X9_THM_0 = store_thm("FV_imp_fail_X9_THM_0",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9'
       c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' c10 c11 c12 c13 c14 c15 c16
        t.
  (CDF p x9 t = 1) /\
  (0 ≤ t ∧ prob_space p ∧
    mutual_indep p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    in_events p
      (fail_event_list p
         [x3; x4; x5; x6; x7; x8; x1; x2; x9; x9; x10; x13; x14; x15; x16; x11;
          x12] t) ∧
    exp_dist_list p
      [x1; x2; x3; x4; x5; x6; x7; x8; x9; x9; x10; x11; x12; x13; x14; x15;
       x16]
      [c1; c2; c3; c4; c5; c6; c7; c8; c9; c9; c10; c11; c12; c13; c14; c15; c16]) ==>
  (FV_imp_fail_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x9 t =
   0)``,
rw[]
\\ DEP_REWRITE_TAC[FV_imp_fail_X9_THM]
\\ rw[]
>- (metis_tac[])
\\ fs[exp_dist_list_def,VDCTheory.exp_dist_def]
\\ rw[REAL_NEG_LMUL]
\\ ASSUME_TAC (REAL_ARITH ``(1:real - exp (-c9 * t) = 1) = (exp (-c9 * t) = 0:real)``)
\\ fs[]);

(*----------------------------*)
val fail_rate_pos_def = Define
`fail_rate_pos L = EVERY (\a:real. 0 <= a) L`;



(*-------------------------*)
val birnbaum_imp_measure_le_1_9 = store_thm("birnbaum_imp_measure_le_1_9",
  ``∀p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 c1 c2 c3 c4 c5 c6
         c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 t.
  0 ≤ t ∧ prob_space p ∧ (CDF p x1 t = 1) ∧ (CDF p x9 t = 1) /\ fail_rate_pos [c1;c3; c4; c5; c6; c7; c8; c2; c9; c10; c13; c14; c15; c16; c11;
            c12] /\
         exp_dist_list p
           [x1;x3; x4; x5; x6; x7; x8; x2; x9; x10; x13; x14; x15; x16; x11;
            x12]
           [c1;c3; c4; c5; c6; c7; c8; c2; c9; c10; c13; c14; c15; c16; c11;
            c12] ∧
         mutual_indep p
           (fail_event_list p
              [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
               x11; x12] t) ∧
         in_events p
           (fail_event_list p
              [x3; x4; x5; x6; x7; x8; x1; x2; x9; x10; x13; x14; x15; x16;
               x11; x12] t) /\
	       (c9 <= c1) ==>
(birnhaum_Rel_IMP_X9 p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    x14 x15 x16 t <= birnhaum_Rel_IMP_Vehicle p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 x14 x15 x16 t)``,
rw[]
\\ DEP_REWRITE_TAC[birnhaum_Rel_IMP_Vehicle_THM]
\\ rw[]
>- (fs[exp_dist_list_def])
\\ DEP_REWRITE_TAC[birnhaum_Rel_IMP_X9_THM]
\\ rw[]
>- (fs[exp_dist_list_def])
\\ rewrite_tac[GSYM REAL_MUL_ASSOC]
\\ DEP_REWRITE_TAC[REAL_LE_LMUL_IMP]
\\ rw[EXP_POS_LE]
\\ rw[REAL_MUL_ASSOC]
\\ once_rewrite_tac[REAL_ARITH ``!a b c d e f:real. a * b * c * d * e*f = b*a*c*d*e*f``]
\\ rewrite_tac[GSYM REAL_MUL_ASSOC]
\\ DEP_REWRITE_TAC[REAL_LE_LMUL_IMP]
\\ rw[EXP_POS_LE]
\\ rw[REAL_MUL_ASSOC]
\\ rw[REAL_LE_SUB_LADD]
\\ once_rewrite_tac[REAL_ARITH ``!a b c d e f:real. a * b * c * d * e + f * c * d * e = (a * b + f) * c * d * e``]
\\ DEP_ONCE_REWRITE_TAC[REAL_ARITH ``1:real = 1 * 1``,REAL_LE_MUL2]
\\ DEP_REWRITE_TAC[REAL_SUB_LE,GSYM transcTheory.EXP_ADD,EXP_MONO_LE,GSYM transcTheory.EXP_0,REAL_NEG_LMUL]
\\ DEP_REWRITE_TAC [REAL_LE_MUL,REAL_LE_ADD,EXP_POS_LE,REAL_SUB_LE,EXP_MONO_LE,GSYM REAL_LE_RNEG,REAL_ADD_RID,REAL_NEG_LMUL,REAL_LE_RMUL_IMP]
\\ rw[EXP_0]
>- (irule REAL_LE_TRANS
   \\ Q.EXISTS_TAC `0:real`
   \\ rw[]
   \\ fs[fail_rate_pos_def])
>- (irule REAL_LE_TRANS
   \\ Q.EXISTS_TAC `0:real`
   \\ rw[]
   \\ fs[fail_rate_pos_def])
>- (irule REAL_LE_TRANS
   \\ Q.EXISTS_TAC `0:real`
   \\ rw[]
   \\ fs[fail_rate_pos_def])
>- (irule REAL_LE_TRANS
   \\ Q.EXISTS_TAC `0:real`
   \\ rw[]
   \\ fs[fail_rate_pos_def])
>- (NTAC 2 (DEP_ONCE_REWRITE_TAC[REAL_ARITH ``1:real = 1 * 1``,REAL_LE_MUL2])
   \\ DEP_REWRITE_TAC[REAL_MUL_RID]
   \\ DEP_REWRITE_TAC[REAL_SUB_LE,GSYM transcTheory.EXP_ADD,EXP_MONO_LE,GSYM transcTheory.EXP_0,REAL_NEG_LMUL]
   \\ DEP_REWRITE_TAC [REAL_LE_MUL,REAL_LE_ADD,EXP_POS_LE,REAL_SUB_LE,EXP_MONO_LE,GSYM REAL_LE_RNEG,REAL_ADD_RID,REAL_NEG_LMUL,REAL_LE_RMUL_IMP]
   \\ rw[]
   >- (irule REAL_LE_TRANS
      \\ Q.EXISTS_TAC `0:real`
      \\ rw[]
      \\ fs[fail_rate_pos_def])
   >- (irule REAL_LE_TRANS
      \\ Q.EXISTS_TAC `0:real`
      \\ rw[]
      \\ fs[fail_rate_pos_def])
   >- (irule REAL_LE_TRANS
      \\ Q.EXISTS_TAC `0:real`
      \\ rw[]
      \\ fs[fail_rate_pos_def])
   >- (irule REAL_LE_TRANS
      \\ Q.EXISTS_TAC `0:real`
      \\ rw[]
      \\ fs[fail_rate_pos_def])
   >- (irule REAL_LE_TRANS
      \\ Q.EXISTS_TAC `0:real`
      \\ rw[]
      \\ fs[fail_rate_pos_def])
   >- (rw[EXP_0,transcTheory.EXP_ADD]
      \\ rw[GSYM REAL_LE_SUB_LADD]
      \\ once_rewrite_tac[prove (``(1:real − exp (-c9 * t) * exp (-c10 * t)) = (1 + -(exp (-c9 * t) * exp (-c10 * t)))``,metis_tac[real_sub])]
      \\ rw[REAL_ADD_SUB2]
      \\ ho_match_mp_tac REAL_LE_RMUL_IMP
      \\ rw[]
      \\ rw[EXP_MONO_LE]
      \\ rw[EXP_POS_LE]
      \\ irule REAL_LE_RMUL_IMP
       \\ rw[])
   >- (rw[EXP_0]
      \\ rw[REAL_LE_SUB_RADD]
      \\ once_rewrite_tac[REAL_ADD_COMM]
      \\ rw[GSYM REAL_LE_SUB_RADD]
      \\ rw[EXP_POS_LE])
   \\ rw[EXP_0]
   \\ rw[REAL_LE_SUB_RADD]
   \\ once_rewrite_tac[REAL_ADD_COMM]
   \\ rw[GSYM REAL_LE_SUB_RADD]
   \\ rw[EXP_POS_LE])
\\ rw[EXP_0]
\\ rw[REAL_LE_SUB_RADD]
\\ once_rewrite_tac[REAL_ADD_COMM]
\\ rw[GSYM REAL_LE_SUB_RADD]
\\ rw[EXP_POS_LE])



val _ = export_theory();
