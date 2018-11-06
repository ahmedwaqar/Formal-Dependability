structure transform_FT_RBDTheory :> transform_FT_RBDTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading transform_FT_RBDTheory ... "
    else ()
  
  open Type Term Thm
  local open ASN_gatewayTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "transform_FT_RBD"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/transform_FT_RBDTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op AND_to_series _ = ()
  val op AND_to_series = TDB.find "AND_to_series"
  fun op OR_to_parallel _ = ()
  val op OR_to_parallel = TDB.find "OR_to_parallel"
  fun op AND_OR_to_series_parallel _ = ()
  val op AND_OR_to_series_parallel = TDB.find "AND_OR_to_series_parallel"
  fun op OR_AND_to_parallel_series _ = ()
  val op OR_AND_to_parallel_series = TDB.find "OR_AND_to_parallel_series"
  fun op NAND_gate_transform _ = ()
  val op NAND_gate_transform = TDB.find "NAND_gate_transform"
  fun op NOR_gate_transform _ = ()
  val op NOR_gate_transform = TDB.find "NOR_gate_transform"
  fun op Inhibit_gate_transform _ = ()
  val op Inhibit_gate_transform = TDB.find "Inhibit_gate_transform"
  fun op comp_gate_transform _ = ()
  val op comp_gate_transform = TDB.find "comp_gate_transform"
  fun op k_out_N_to_majority_voting_gate _ = ()
  val op k_out_N_to_majority_voting_gate = TDB.find
    "k_out_N_to_majority_voting_gate"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val transform_FT_RBD_grammars = merge_grammars ["ASN_gateway"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="transform_FT_RBD"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val transform_FT_RBD_grammars = 
    Portable.## (addtyUDs,addtmUDs) transform_FT_RBD_grammars
  val _ = Parse.grammarDB_insert("transform_FT_RBD",transform_FT_RBD_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "transform_FT_RBD"

end
