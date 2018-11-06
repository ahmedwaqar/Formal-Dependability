structure WSNTheory :> WSNTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading WSNTheory ... "
    else ()
  
  open Type Term Thm
  local open smart_gridTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "WSN"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/WSNTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op RMST_fail_rate_list_def _ = ()
  val op RMST_fail_rate_list_def = TDB.find "RMST_fail_rate_list_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op E2W_WSN _ = () val op E2W_WSN = TDB.find "E2W_WSN"
  fun op one_minus_exp_equi _ = ()
  val op one_minus_exp_equi = TDB.find "one_minus_exp_equi"
  fun op ESRT_WSN _ = () val op ESRT_WSN = TDB.find "ESRT_WSN"
  fun op parallel_series_struct_rbd_v2 _ = ()
  val op parallel_series_struct_rbd_v2 = TDB.find
    "parallel_series_struct_rbd_v2"
  fun op parallel_series_exp_fail_rate _ = ()
  val op parallel_series_exp_fail_rate = TDB.find
    "parallel_series_exp_fail_rate"
  fun op rel_parallel_series_exp_fail_rate _ = ()
  val op rel_parallel_series_exp_fail_rate = TDB.find
    "rel_parallel_series_exp_fail_rate"
  fun op RMST_fail_rate_list_def_compute _ = ()
  val op RMST_fail_rate_list_def_compute = TDB.find
    "RMST_fail_rate_list_def_compute"
  fun op RMST_WSN _ = () val op RMST_WSN = TDB.find "RMST_WSN"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val WSN_grammars = merge_grammars ["smart_grid"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="WSN"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val WSN_grammars = 
    Portable.## (addtyUDs,addtmUDs) WSN_grammars
  val _ = Parse.grammarDB_insert("WSN",WSN_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "WSN"

end
