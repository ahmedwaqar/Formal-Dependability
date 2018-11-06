structure ASN_gatewayTheory :> ASN_gatewayTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading ASN_gatewayTheory ... "
    else ()
  
  open Type Term Thm
  local open FT_deepTheory VDCTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "ASN_gateway"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/ASN_gatewayTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op fail_event_list_def _ = ()
  val op fail_event_list_def = TDB.find "fail_event_list_def"
  fun op list_fail_event_list_def _ = ()
  val op list_fail_event_list_def = TDB.find "list_fail_event_list_def"
  fun op exp_func_def _ = () val op exp_func_def = TDB.find "exp_func_def"
  fun op one_minus_exp_def _ = ()
  val op one_minus_exp_def = TDB.find "one_minus_exp_def"
  fun op one_minus_exp_prod_def _ = ()
  val op one_minus_exp_prod_def = TDB.find "one_minus_exp_prod_def"
  fun op list_sum_def _ = () val op list_sum_def = TDB.find "list_sum_def"
  fun op exp_dist_def _ = () val op exp_dist_def = TDB.find "exp_dist_def"
  fun op list_exp_def _ = () val op list_exp_def = TDB.find "list_exp_def"
  fun op B1_FT_def _ = () val op B1_FT_def = TDB.find "B1_FT_def"
  fun op B2_FT_def _ = () val op B2_FT_def = TDB.find "B2_FT_def"
  fun op A_FT_def _ = () val op A_FT_def = TDB.find "A_FT_def"
  fun op RT_FT_def _ = () val op RT_FT_def = TDB.find "RT_FT_def"
  fun op Internal_FT_def _ = ()
  val op Internal_FT_def = TDB.find "Internal_FT_def"
  fun op ASN_gateway_FT_def _ = ()
  val op ASN_gateway_FT_def = TDB.find "ASN_gateway_FT_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op ASN_FT_eq_parallel_series_RBD _ = ()
  val op ASN_FT_eq_parallel_series_RBD = TDB.find
    "ASN_FT_eq_parallel_series_RBD"
  fun op B1_FT_lemma2 _ = () val op B1_FT_lemma2 = TDB.find "B1_FT_lemma2"
  fun op B1_FT_lemma2_new _ = ()
  val op B1_FT_lemma2_new = TDB.find "B1_FT_lemma2_new"
  fun op B1_FT_lemma5 _ = () val op B1_FT_lemma5 = TDB.find "B1_FT_lemma5"
  fun op B1_FT_lemma3 _ = () val op B1_FT_lemma3 = TDB.find "B1_FT_lemma3"
  fun op B1_FT_lemma3_new _ = ()
  val op B1_FT_lemma3_new = TDB.find "B1_FT_lemma3_new"
  fun op B1_FT_lemma6 _ = () val op B1_FT_lemma6 = TDB.find "B1_FT_lemma6"
  fun op RT_FT_lemma2 _ = () val op RT_FT_lemma2 = TDB.find "RT_FT_lemma2"
  fun op B1_FT_lemma4 _ = () val op B1_FT_lemma4 = TDB.find "B1_FT_lemma4"
  fun op A_FT_lemma1 _ = () val op A_FT_lemma1 = TDB.find "A_FT_lemma1"
  fun op Internal_FT_lemma1 _ = ()
  val op Internal_FT_lemma1 = TDB.find "Internal_FT_lemma1"
  fun op Internal_FT_lemma2 _ = ()
  val op Internal_FT_lemma2 = TDB.find "Internal_FT_lemma2"
  fun op ASN_gateway_lemma1 _ = ()
  val op ASN_gateway_lemma1 = TDB.find "ASN_gateway_lemma1"
  fun op ASN_gateway_lemma2 _ = ()
  val op ASN_gateway_lemma2 = TDB.find "ASN_gateway_lemma2"
  fun op ASN_gateway_lem5 _ = ()
  val op ASN_gateway_lem5 = TDB.find "ASN_gateway_lem5"
  fun op ASN_gateway_lem6 _ = ()
  val op ASN_gateway_lem6 = TDB.find "ASN_gateway_lem6"
  fun op ASN_gateway_thm _ = ()
  val op ASN_gateway_thm = TDB.find "ASN_gateway_thm"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ASN_gateway_grammars = merge_grammars ["VDC", "FT_deep"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ASN_gateway"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ASN_gateway_grammars = 
    Portable.## (addtyUDs,addtmUDs) ASN_gateway_grammars
  val _ = Parse.grammarDB_insert("ASN_gateway",ASN_gateway_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "ASN_gateway"

end
