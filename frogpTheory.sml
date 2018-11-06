structure frogpTheory :> frogpTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading frogpTheory ... "
    else ()
  
  open Type Term Thm
  local open ASN_gatewayTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "frogp"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/frogpTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op pipeline_def _ = () val op pipeline_def = TDB.find "pipeline_def"
  fun op rel_pipeline_z2_def _ = ()
  val op rel_pipeline_z2_def = TDB.find "rel_pipeline_z2_def"
  fun op rel_pipeline_z4_def _ = ()
  val op rel_pipeline_z4_def = TDB.find "rel_pipeline_z4_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op rel_pipeline_z1_ind _ = ()
  val op rel_pipeline_z1_ind = TDB.find "rel_pipeline_z1_ind"
  fun op rel_pipeline_z1_def _ = ()
  val op rel_pipeline_z1_def = TDB.find "rel_pipeline_z1_def"
  fun op series_exp_list_sum _ = ()
  val op series_exp_list_sum = TDB.find "series_exp_list_sum"
  fun op rel_pipeline_series _ = ()
  val op rel_pipeline_series = TDB.find "rel_pipeline_series"
  fun op rel_pipeline_z1_thm _ = ()
  val op rel_pipeline_z1_thm = TDB.find "rel_pipeline_z1_thm"
  fun op len_mem_list_le_ind _ = ()
  val op len_mem_list_le_ind = TDB.find "len_mem_list_le_ind"
  fun op len_mem_list_le_def _ = ()
  val op len_mem_list_le_def = TDB.find "len_mem_list_le_def"
  fun op rel_pipeline_z2_thm _ = ()
  val op rel_pipeline_z2_thm = TDB.find "rel_pipeline_z2_thm"
  fun op rel_pipeline_z3_lemma4 _ = ()
  val op rel_pipeline_z3_lemma4 = TDB.find "rel_pipeline_z3_lemma4"
  fun op rel_pipeline_z3_THM _ = ()
  val op rel_pipeline_z3_THM = TDB.find "rel_pipeline_z3_THM"
  fun op rel_pipeline_z4_lemma2 _ = ()
  val op rel_pipeline_z4_lemma2 = TDB.find "rel_pipeline_z4_lemma2"
  fun op rel_pipeline_z4_THM _ = ()
  val op rel_pipeline_z4_THM = TDB.find "rel_pipeline_z4_THM"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val frogp_grammars = merge_grammars ["ASN_gateway"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="frogp"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val frogp_grammars = 
    Portable.## (addtyUDs,addtmUDs) frogp_grammars
  val _ = Parse.grammarDB_insert("frogp",frogp_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "frogp"

end
