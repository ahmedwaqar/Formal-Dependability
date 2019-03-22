
app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
"util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","RBDTheory","FT_deepTheory","VDCTheory","railwayTheory","AvailabilityTheory","smart_grid_inequivalityTheory","rel_ess_resTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory RBDTheory FT_deepTheory VDCTheory railwayTheory AvailabilityTheory smart_grid_inequivalityTheory rel_ess_resTheory; 



fun power_plant_gen_res_ess_EVAL L thm thms thms1 =
 let
  val specialization = 
    (UNDISCH_ALL o SPEC_ALL o Q.SPECL L)
      thm
  val computation =
    (CONV_RULE (SIMP_CONV real_ss[binomial_def,sum]) o
     REWRITE_RULE thms1 o
     CONV_RULE (SIMP_CONV real_ss[binomial_def,sum]) o
	   REWRITE_RULE thms1 o
	   CONV_RULE (SIMP_CONV real_ss[binomial_def,sum]) o
	   CONV_RULE(SIMP_CONV list_ss thms) o
	   BETA_RULE o
	   REWRITE_RULE thms) specialization
val value = sml_of_hol_real_exp (rhs (concl computation))	
in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp computation)));
      print "\n\n";
      print "Simplified Probability Outage Capacity Expression of Power Plant:\n";
      print (term_to_string (concl computation));
      print "\n\n";
      print "Numerically Computed COPT of Power Plant:\n";
      print (Real.toString (value) ^ "\n\n")
end;





power_plant_gen_res_ess_EVAL [`p:'b event # 'b event event # ('b event -> real)`,
                      `p':α event # α event event # (α event -> real)`,
		      `r:num`, `3:num`, `5:num`,`z:num`,
		      `(X_bino :β -> extreal)`,
		      `[(X_ESS:(β -> extreal),(1000:real,50:real))]`,
		      `[(X_G1:(β -> extreal),(1150:real,100:real));
		      (X_G2:(β -> extreal),(1100:real,150:real));
                      (X_G3:(β -> extreal),(1960:real,40:real));
		      (X_G4:(β -> extreal),(1200:real,50:real));
                      (X_G5:(β -> extreal),(960:real,40:real))]`,
		      `(X_RES:('a -> extreal),(340:real,250:real))`,
		      `(P :(β -> extreal) -> β event)`,
		      `(Q :(β -> extreal) -> β event)`]
    Rel_of_comb_ESS_RES_GEN_power_plant
    [steady_state_avail_def,steady_state_avail_list_def,
     fail_rep_list_def,rv_list_def,n_times_steady_state_avail_prod_def,sum,binomial_def,
     list_prod_def,pow,SUM_1,SUM_2]
   [prove(``5=SUC (SUC (SUC (SUC (SUC 0))))``,REDUCE_TAC),
    prove(``4=SUC (SUC (SUC (SUC 0)))``,REDUCE_TAC),
    prove(``3=SUC (SUC (SUC 0))``,REDUCE_TAC),
    prove(``2=SUC (SUC 0)``,REDUCE_TAC),
    prove(``1=SUC 0``,REDUCE_TAC),sum];

