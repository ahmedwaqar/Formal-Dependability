structure AvailabilityTheory :> AvailabilityTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading AvailabilityTheory ... "
    else ()
  
  open Type Term Thm
  local open FT_deepTheory VDCTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "Availability"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/AvailabilityTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op avail_event_def _ = ()
  val op avail_event_def = TDB.find "avail_event_def"
  fun op union_avail_events_def _ = ()
  val op union_avail_events_def = TDB.find "union_avail_events_def"
  fun op union_avail_events1_def _ = ()
  val op union_avail_events1_def = TDB.find "union_avail_events1_def"
  fun op union_avail_event_list_def _ = ()
  val op union_avail_event_list_def = TDB.find "union_avail_event_list_def"
  fun op union_avail_event_list1_def _ = ()
  val op union_avail_event_list1_def = TDB.find
    "union_avail_event_list1_def"
  fun op list_union_avail_event_list_def _ = ()
  val op list_union_avail_event_list_def = TDB.find
    "list_union_avail_event_list_def"
  fun op avail_event_list_def _ = ()
  val op avail_event_list_def = TDB.find "avail_event_list_def"
  fun op expec_avail_def _ = ()
  val op expec_avail_def = TDB.find "expec_avail_def"
  fun op expec_avail1_def _ = ()
  val op expec_avail1_def = TDB.find "expec_avail1_def"
  fun op cdf_def _ = () val op cdf_def = TDB.find "cdf_def"
  fun op reliability_def _ = ()
  val op reliability_def = TDB.find "reliability_def"
  fun op rel_event1_def _ = ()
  val op rel_event1_def = TDB.find "rel_event1_def"
  fun op expec_def _ = () val op expec_def = TDB.find "expec_def"
  fun op inst_avail_exp_def _ = ()
  val op inst_avail_exp_def = TDB.find "inst_avail_exp_def"
  fun op inst_avail_exp1_def _ = ()
  val op inst_avail_exp1_def = TDB.find "inst_avail_exp1_def"
  fun op inst_avail_exp2_def _ = ()
  val op inst_avail_exp2_def = TDB.find "inst_avail_exp2_def"
  fun op inst_avail_exp3_def _ = ()
  val op inst_avail_exp3_def = TDB.find "inst_avail_exp3_def"
  fun op inst_avail_exp_list_def _ = ()
  val op inst_avail_exp_list_def = TDB.find "inst_avail_exp_list_def"
  fun op inst_avail_exp_list1_def _ = ()
  val op inst_avail_exp_list1_def = TDB.find "inst_avail_exp_list1_def"
  fun op inst_avail_exp_list2_def _ = ()
  val op inst_avail_exp_list2_def = TDB.find "inst_avail_exp_list2_def"
  fun op two_dim_inst_avail_exp_def _ = ()
  val op two_dim_inst_avail_exp_def = TDB.find "two_dim_inst_avail_exp_def"
  fun op steady_state_avail_def _ = ()
  val op steady_state_avail_def = TDB.find "steady_state_avail_def"
  fun op steady_state_avail_list_def _ = ()
  val op steady_state_avail_list_def = TDB.find
    "steady_state_avail_list_def"
  fun op two_dim_steady_state_avail_list_def _ = ()
  val op two_dim_steady_state_avail_list_def = TDB.find
    "two_dim_steady_state_avail_list_def"
  fun op steady_state_avail_prod_def _ = ()
  val op steady_state_avail_prod_def = TDB.find
    "steady_state_avail_prod_def"
  fun op two_dim_steady_state_avail_prod_def _ = ()
  val op two_dim_steady_state_avail_prod_def = TDB.find
    "two_dim_steady_state_avail_prod_def"
  fun op compl_steady_state_avail_def _ = ()
  val op compl_steady_state_avail_def = TDB.find
    "compl_steady_state_avail_def"
  fun op unavail_event_def _ = ()
  val op unavail_event_def = TDB.find "unavail_event_def"
  fun op union_unavail_events_def _ = ()
  val op union_unavail_events_def = TDB.find "union_unavail_events_def"
  fun op union_unavail_event_list_def _ = ()
  val op union_unavail_event_list_def = TDB.find
    "union_unavail_event_list_def"
  fun op steady_state_unavail_def _ = ()
  val op steady_state_unavail_def = TDB.find "steady_state_unavail_def"
  fun op steady_state_unavail_list_def _ = ()
  val op steady_state_unavail_list_def = TDB.find
    "steady_state_unavail_list_def"
  fun op inst_unavail_exp_def _ = ()
  val op inst_unavail_exp_def = TDB.find "inst_unavail_exp_def"
  fun op inst_unavail_exp_list_def _ = ()
  val op inst_unavail_exp_list_def = TDB.find "inst_unavail_exp_list_def"
  fun op two_dim_inst_unavail_exp_def _ = ()
  val op two_dim_inst_unavail_exp_def = TDB.find
    "two_dim_inst_unavail_exp_def"
  fun op AND_unavail_FT_gate_def _ = ()
  val op AND_unavail_FT_gate_def = TDB.find "AND_unavail_FT_gate_def"
  fun op OR_unavail_FT_gate_def _ = ()
  val op OR_unavail_FT_gate_def = TDB.find "OR_unavail_FT_gate_def"
  fun op NOR_unavail_FT_gate_def _ = ()
  val op NOR_unavail_FT_gate_def = TDB.find "NOR_unavail_FT_gate_def"
  fun op NAND_unavail_FT_gate_def _ = ()
  val op NAND_unavail_FT_gate_def = TDB.find "NAND_unavail_FT_gate_def"
  fun op XOR_unavail_FT_gate_def _ = ()
  val op XOR_unavail_FT_gate_def = TDB.find "XOR_unavail_FT_gate_def"
  fun op in_events_normal_events _ = ()
  val op in_events_normal_events = TDB.find "in_events_normal_events"
  fun op steady_state_NOR_unavail_FT_gate _ = ()
  val op steady_state_NOR_unavail_FT_gate = TDB.find
    "steady_state_NOR_unavail_FT_gate"
  fun op OR_steady_state_unavail _ = ()
  val op OR_steady_state_unavail = TDB.find "OR_steady_state_unavail"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op compl_rel_event_eq_fail_event1 _ = ()
  val op compl_rel_event_eq_fail_event1 = TDB.find
    "compl_rel_event_eq_fail_event1"
  fun op compl_fail_event_eq_rel_event1 _ = ()
  val op compl_fail_event_eq_rel_event1 = TDB.find
    "compl_fail_event_eq_rel_event1"
  fun op avail_ge_rel _ = () val op avail_ge_rel = TDB.find "avail_ge_rel"
  fun op avail_ge_rel1 _ = ()
  val op avail_ge_rel1 = TDB.find "avail_ge_rel1"
  fun op neg_exp_tend0_new _ = ()
  val op neg_exp_tend0_new = TDB.find "neg_exp_tend0_new"
  fun op steady_avail_temp _ = ()
  val op steady_avail_temp = TDB.find "steady_avail_temp"
  fun op steady_state_avail _ = ()
  val op steady_state_avail = TDB.find "steady_state_avail"
  fun op steady_state_avail1 _ = ()
  val op steady_state_avail1 = TDB.find "steady_state_avail1"
  fun op EXT_LE_LT _ = () val op EXT_LE_LT = TDB.find "EXT_LE_LT"
  fun op PERM_refl _ = () val op PERM_refl = TDB.find "PERM_refl"
  fun op LET_ANTISYM _ = () val op LET_ANTISYM = TDB.find "LET_ANTISYM"
  fun op not_null_leng _ = ()
  val op not_null_leng = TDB.find "not_null_leng"
  fun op series_expec_tends_prod_avail _ = ()
  val op series_expec_tends_prod_avail = TDB.find
    "series_expec_tends_prod_avail"
  fun op series_rbd_avail _ = ()
  val op series_rbd_avail = TDB.find "series_rbd_avail"
  fun op lim_inst_parall_tend_steady _ = ()
  val op lim_inst_parall_tend_steady = TDB.find
    "lim_inst_parall_tend_steady"
  fun op compl_steady_state_avail_equi _ = ()
  val op compl_steady_state_avail_equi = TDB.find
    "compl_steady_state_avail_equi"
  fun op parallel_rbd_avail _ = ()
  val op parallel_rbd_avail = TDB.find "parallel_rbd_avail"
  fun op lim_inst_parall_series_tend_steady _ = ()
  val op lim_inst_parall_series_tend_steady = TDB.find
    "lim_inst_parall_series_tend_steady"
  fun op steady_state_parallel_series_ABD _ = ()
  val op steady_state_parallel_series_ABD = TDB.find
    "steady_state_parallel_series_ABD"
  fun op lim_inst_series_parall_tend_steady _ = ()
  val op lim_inst_series_parall_tend_steady = TDB.find
    "lim_inst_series_parall_tend_steady"
  fun op steady_state_series_parallel_avail _ = ()
  val op steady_state_series_parallel_avail = TDB.find
    "steady_state_series_parallel_avail"
  fun op AND_inst_avail_prod_tends_steady _ = ()
  val op AND_inst_avail_prod_tends_steady = TDB.find
    "AND_inst_avail_prod_tends_steady"
  fun op AND_gate_unavail _ = ()
  val op AND_gate_unavail = TDB.find "AND_gate_unavail"
  fun op lim_inst_OR_tend_steady _ = ()
  val op lim_inst_OR_tend_steady = TDB.find "lim_inst_OR_tend_steady"
  fun op NAND_steady_state_avail _ = ()
  val op NAND_steady_state_avail = TDB.find "NAND_steady_state_avail"
  fun op inst_XOR_tends_steadty _ = ()
  val op inst_XOR_tends_steadty = TDB.find "inst_XOR_tends_steadty"
  fun op XOR_steady_unavail _ = ()
  val op XOR_steady_unavail = TDB.find "XOR_steady_unavail"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val Availability_grammars = merge_grammars ["VDC", "FT_deep"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="Availability"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val Availability_grammars = 
    Portable.## (addtyUDs,addtmUDs) Availability_grammars
  val _ = Parse.grammarDB_insert("Availability",Availability_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "Availability"

end
