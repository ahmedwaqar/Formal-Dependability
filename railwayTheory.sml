structure railwayTheory :> railwayTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading railwayTheory ... "
    else ()
  
  open Type Term Thm
  local open smart_gridTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "railway"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/railwayTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op in_events_def _ = ()
  val op in_events_def = TDB.find "in_events_def"
  fun op two_dim_fail_event_list_def _ = ()
  val op two_dim_fail_event_list_def = TDB.find
    "two_dim_fail_event_list_def"
  fun op three_dim_fail_event_list_def _ = ()
  val op three_dim_fail_event_list_def = TDB.find
    "three_dim_fail_event_list_def"
  fun op one_minus_exp_func_list_def _ = ()
  val op one_minus_exp_func_list_def = TDB.find
    "one_minus_exp_func_list_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op railway_FT_equi_RBD _ = ()
  val op railway_FT_equi_RBD = TDB.find "railway_FT_equi_RBD"
  fun op fail_prob_railway_FT _ = ()
  val op fail_prob_railway_FT = TDB.find "fail_prob_railway_FT"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val railway_grammars = merge_grammars ["smart_grid"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="railway"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val railway_grammars = 
    Portable.## (addtyUDs,addtmUDs) railway_grammars
  val _ = Parse.grammarDB_insert("railway",railway_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "railway"

end
