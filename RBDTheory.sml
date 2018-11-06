structure RBDTheory :> RBDTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading RBDTheory ... "
    else ()
  
  open Type Term Thm
  local open probabilityTheory sortingTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "RBD"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/RBDTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op rbd_TY_DEF _ = () val op rbd_TY_DEF = TDB.find "rbd_TY_DEF"
  fun op rbd_case_def _ = () val op rbd_case_def = TDB.find "rbd_case_def"
  fun op rbd_size_def _ = () val op rbd_size_def = TDB.find "rbd_size_def"
  fun op rbd_list_def _ = () val op rbd_list_def = TDB.find "rbd_list_def"
  fun op of_DEF _ = () val op of_DEF = TDB.find "of_DEF"
  fun op big_inter_def _ = ()
  val op big_inter_def = TDB.find "big_inter_def"
  fun op list_prod_def _ = ()
  val op list_prod_def = TDB.find "list_prod_def"
  fun op list_prob_def _ = ()
  val op list_prob_def = TDB.find "list_prob_def"
  fun op mutual_indep_def _ = ()
  val op mutual_indep_def = TDB.find "mutual_indep_def"
  fun op compl_list_def _ = ()
  val op compl_list_def = TDB.find "compl_list_def"
  fun op one_minus_list_def _ = ()
  val op one_minus_list_def = TDB.find "one_minus_list_def"
  fun op compl_pspace_def _ = ()
  val op compl_pspace_def = TDB.find "compl_pspace_def"
  fun op list_prod_one_minus_rel_def _ = ()
  val op list_prod_one_minus_rel_def = TDB.find
    "list_prod_one_minus_rel_def"
  fun op list_prod_rel_def _ = ()
  val op list_prod_rel_def = TDB.find "list_prod_rel_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op datatype_rbd _ = () val op datatype_rbd = TDB.find "datatype_rbd"
  fun op rbd_11 _ = () val op rbd_11 = TDB.find "rbd_11"
  fun op rbd_distinct _ = () val op rbd_distinct = TDB.find "rbd_distinct"
  fun op rbd_nchotomy _ = () val op rbd_nchotomy = TDB.find "rbd_nchotomy"
  fun op rbd_Axiom _ = () val op rbd_Axiom = TDB.find "rbd_Axiom"
  fun op rbd_induction _ = ()
  val op rbd_induction = TDB.find "rbd_induction"
  fun op rbd_case_cong _ = ()
  val op rbd_case_cong = TDB.find "rbd_case_cong"
  fun op rbd_case_eq _ = () val op rbd_case_eq = TDB.find "rbd_case_eq"
  fun op rbd_struct_ind _ = ()
  val op rbd_struct_ind = TDB.find "rbd_struct_ind"
  fun op rbd_struct_def _ = ()
  val op rbd_struct_def = TDB.find "rbd_struct_def"
  fun op mutual_indep_cons _ = ()
  val op mutual_indep_cons = TDB.find "mutual_indep_cons"
  fun op series_rbd_eq_big_inter _ = ()
  val op series_rbd_eq_big_inter = TDB.find "series_rbd_eq_big_inter"
  fun op series_struct_thm _ = ()
  val op series_struct_thm = TDB.find "series_struct_thm"
  fun op parallel_rbd_lem1 _ = ()
  val op parallel_rbd_lem1 = TDB.find "parallel_rbd_lem1"
  fun op in_events_big_inter _ = ()
  val op in_events_big_inter = TDB.find "in_events_big_inter"
  fun op parallel_rbd_lem2 _ = ()
  val op parallel_rbd_lem2 = TDB.find "parallel_rbd_lem2"
  fun op parallel_rbd_lem3 _ = ()
  val op parallel_rbd_lem3 = TDB.find "parallel_rbd_lem3"
  fun op parallel_rbd_lem4 _ = ()
  val op parallel_rbd_lem4 = TDB.find "parallel_rbd_lem4"
  fun op parallel_rbd_lem5 _ = ()
  val op parallel_rbd_lem5 = TDB.find "parallel_rbd_lem5"
  fun op parallel_rbd_lem6 _ = ()
  val op parallel_rbd_lem6 = TDB.find "parallel_rbd_lem6"
  fun op parallel_rbd_lem7 _ = ()
  val op parallel_rbd_lem7 = TDB.find "parallel_rbd_lem7"
  fun op prob_B _ = () val op prob_B = TDB.find "prob_B"
  fun op Prob_Incl_excl _ = ()
  val op Prob_Incl_excl = TDB.find "Prob_Incl_excl"
  fun op prob_compl_subset _ = ()
  val op prob_compl_subset = TDB.find "prob_compl_subset"
  fun op mutual_indep_cons_append _ = ()
  val op mutual_indep_cons_append = TDB.find "mutual_indep_cons_append"
  fun op mutual_indep_cons_append1 _ = ()
  val op mutual_indep_cons_append1 = TDB.find "mutual_indep_cons_append1"
  fun op mutual_indep_cons_swap _ = ()
  val op mutual_indep_cons_swap = TDB.find "mutual_indep_cons_swap"
  fun op prob_indep_compl_event_big_inter_list _ = ()
  val op prob_indep_compl_event_big_inter_list = TDB.find
    "prob_indep_compl_event_big_inter_list"
  fun op prob_indep_big_inter1 _ = ()
  val op prob_indep_big_inter1 = TDB.find "prob_indep_big_inter1"
  fun op prob_big_inter_compl_list _ = ()
  val op prob_big_inter_compl_list = TDB.find "prob_big_inter_compl_list"
  fun op mutual_indep_compl_event_imp_norm_event _ = ()
  val op mutual_indep_compl_event_imp_norm_event = TDB.find
    "mutual_indep_compl_event_imp_norm_event"
  fun op mutual_indep_compl _ = ()
  val op mutual_indep_compl = TDB.find "mutual_indep_compl"
  fun op parallel_lem1 _ = ()
  val op parallel_lem1 = TDB.find "parallel_lem1"
  fun op parallel_lem2 _ = ()
  val op parallel_lem2 = TDB.find "parallel_lem2"
  fun op parallel_lem3 _ = ()
  val op parallel_lem3 = TDB.find "parallel_lem3"
  fun op parallel_lem4 _ = ()
  val op parallel_lem4 = TDB.find "parallel_lem4"
  fun op parallel_lem5 _ = ()
  val op parallel_lem5 = TDB.find "parallel_lem5"
  fun op parallel_lem6 _ = ()
  val op parallel_lem6 = TDB.find "parallel_lem6"
  fun op parallel_lem7 _ = ()
  val op parallel_lem7 = TDB.find "parallel_lem7"
  fun op parallel_lem8 _ = ()
  val op parallel_lem8 = TDB.find "parallel_lem8"
  fun op parallel_struct_thm _ = ()
  val op parallel_struct_thm = TDB.find "parallel_struct_thm"
  fun op parallel_series_lem1 _ = ()
  val op parallel_series_lem1 = TDB.find "parallel_series_lem1"
  fun op mutual_indep_flat_cons1 _ = ()
  val op mutual_indep_flat_cons1 = TDB.find "mutual_indep_flat_cons1"
  fun op mutual_indep_flat_cons2 _ = ()
  val op mutual_indep_flat_cons2 = TDB.find "mutual_indep_flat_cons2"
  fun op mutual_indep_flat_append _ = ()
  val op mutual_indep_flat_append = TDB.find "mutual_indep_flat_append"
  fun op mutual_indep_flat_cons3 _ = ()
  val op mutual_indep_flat_cons3 = TDB.find "mutual_indep_flat_cons3"
  fun op mutual_indep_flat_append1 _ = ()
  val op mutual_indep_flat_append1 = TDB.find "mutual_indep_flat_append1"
  fun op mutual_indep_front_append _ = ()
  val op mutual_indep_front_append = TDB.find "mutual_indep_front_append"
  fun op mutual_indep_FLAT_front_cons _ = ()
  val op mutual_indep_FLAT_front_cons = TDB.find
    "mutual_indep_FLAT_front_cons"
  fun op mutual_indep_append1 _ = ()
  val op mutual_indep_append1 = TDB.find "mutual_indep_append1"
  fun op mutual_indep_flat_cons4 _ = ()
  val op mutual_indep_flat_cons4 = TDB.find "mutual_indep_flat_cons4"
  fun op mutual_indep_append_sym _ = ()
  val op mutual_indep_append_sym = TDB.find "mutual_indep_append_sym"
  fun op mutual_indep_flat_cons5 _ = ()
  val op mutual_indep_flat_cons5 = TDB.find "mutual_indep_flat_cons5"
  fun op mutual_indep_FLAT_append1 _ = ()
  val op mutual_indep_FLAT_append1 = TDB.find "mutual_indep_FLAT_append1"
  fun op mutual_indep_cons_append10 _ = ()
  val op mutual_indep_cons_append10 = TDB.find "mutual_indep_cons_append10"
  fun op mutual_indep_cons_append11 _ = ()
  val op mutual_indep_cons_append11 = TDB.find "mutual_indep_cons_append11"
  fun op mutual_indep_cons_append12 _ = ()
  val op mutual_indep_cons_append12 = TDB.find "mutual_indep_cons_append12"
  fun op mutual_indep_cons_append13 _ = ()
  val op mutual_indep_cons_append13 = TDB.find "mutual_indep_cons_append13"
  fun op mutual_indep_cons_append14 _ = ()
  val op mutual_indep_cons_append14 = TDB.find "mutual_indep_cons_append14"
  fun op mutual_indep_cons_append15 _ = ()
  val op mutual_indep_cons_append15 = TDB.find "mutual_indep_cons_append15"
  fun op mutual_indep_cons_append16 _ = ()
  val op mutual_indep_cons_append16 = TDB.find "mutual_indep_cons_append16"
  fun op mutual_indep_cons_append17 _ = ()
  val op mutual_indep_cons_append17 = TDB.find "mutual_indep_cons_append17"
  fun op mutual_indep_cons_append18 _ = ()
  val op mutual_indep_cons_append18 = TDB.find "mutual_indep_cons_append18"
  fun op mutual_indep_cons_append19 _ = ()
  val op mutual_indep_cons_append19 = TDB.find "mutual_indep_cons_append19"
  fun op mutual_indep_flat_cons6 _ = ()
  val op mutual_indep_flat_cons6 = TDB.find "mutual_indep_flat_cons6"
  fun op in_events_parallel_series _ = ()
  val op in_events_parallel_series = TDB.find "in_events_parallel_series"
  fun op series_rbd_append _ = ()
  val op series_rbd_append = TDB.find "series_rbd_append"
  fun op inter_set_arrang1 _ = ()
  val op inter_set_arrang1 = TDB.find "inter_set_arrang1"
  fun op MEM_NULL_arrang1 _ = ()
  val op MEM_NULL_arrang1 = TDB.find "MEM_NULL_arrang1"
  fun op series_rbd_append2 _ = ()
  val op series_rbd_append2 = TDB.find "series_rbd_append2"
  fun op series_rbd_indep_parallel_series_rbd _ = ()
  val op series_rbd_indep_parallel_series_rbd = TDB.find
    "series_rbd_indep_parallel_series_rbd"
  fun op Parallel_Series_struct_thm _ = ()
  val op Parallel_Series_struct_thm = TDB.find "Parallel_Series_struct_thm"
  fun op rel_parallel_series_rbd _ = ()
  val op rel_parallel_series_rbd = TDB.find "rel_parallel_series_rbd"
  fun op one_minus_eq_lemm _ = ()
  val op one_minus_eq_lemm = TDB.find "one_minus_eq_lemm"
  fun op parallel_series_struct_rbd_v2 _ = ()
  val op parallel_series_struct_rbd_v2 = TDB.find
    "parallel_series_struct_rbd_v2"
  fun op in_events_series_parallel _ = ()
  val op in_events_series_parallel = TDB.find "in_events_series_parallel"
  fun op series_rbd_indep_series_parallel_rbd _ = ()
  val op series_rbd_indep_series_parallel_rbd = TDB.find
    "series_rbd_indep_series_parallel_rbd"
  fun op parallel_rbd_indep_series_parallel_rbd _ = ()
  val op parallel_rbd_indep_series_parallel_rbd = TDB.find
    "parallel_rbd_indep_series_parallel_rbd"
  fun op series_parallel_struct_thm _ = ()
  val op series_parallel_struct_thm = TDB.find "series_parallel_struct_thm"
  fun op series_parallel_struct_thm_v2 _ = ()
  val op series_parallel_struct_thm_v2 = TDB.find
    "series_parallel_struct_thm_v2"
  fun op in_events_parallel_of_series_parallel _ = ()
  val op in_events_parallel_of_series_parallel = TDB.find
    "in_events_parallel_of_series_parallel"
  fun op in_events_series_parallel_of_series_parallel _ = ()
  val op in_events_series_parallel_of_series_parallel = TDB.find
    "in_events_series_parallel_of_series_parallel"
  fun op
    series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel
    _ = ()
  val op
    series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel
    = TDB.find
    "series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel"
  fun op series_rbd_indep_series_parallel_of_series_parallel _ = ()
  val op series_rbd_indep_series_parallel_of_series_parallel = TDB.find
    "series_rbd_indep_series_parallel_of_series_parallel"
  fun op series_parallel_rbd_indep_series_parallel_of_series_parallel _ =
    ()
  val op series_parallel_rbd_indep_series_parallel_of_series_parallel =
    TDB.find "series_parallel_rbd_indep_series_parallel_of_series_parallel"
  fun op
    parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd
    _ = ()
  val op
    parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd
    = TDB.find
    "parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd"
  fun op rel_parallel_of_series_parallel_rbd _ = ()
  val op rel_parallel_of_series_parallel_rbd = TDB.find
    "rel_parallel_of_series_parallel_rbd"
  fun op rel_nested_series_parallel_rbd _ = ()
  val op rel_nested_series_parallel_rbd = TDB.find
    "rel_nested_series_parallel_rbd"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val RBD_grammars = merge_grammars ["sorting", "probability"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="RBD"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val RBD_grammars = 
    Portable.## (addtyUDs,addtmUDs) RBD_grammars
  val _ = Parse.grammarDB_insert("RBD",RBD_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "RBD"

end
