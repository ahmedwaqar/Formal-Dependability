structure smart_gridTheory :> smart_gridTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading smart_gridTheory ... "
    else ()
  
  open Type Term Thm
  local open ASN_gatewayTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "smart_grid"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/smart_gridTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op in_events_def _ = ()
  val op in_events_def = TDB.find "in_events_def"
  fun op not_null_def _ = () val op not_null_def = TDB.find "not_null_def"
  fun op in_events_k_out_n_def _ = ()
  val op in_events_k_out_n_def = TDB.find "in_events_k_out_n_def"
  fun op k_out_n_event_def _ = ()
  val op k_out_n_event_def = TDB.find "k_out_n_event_def"
  fun op binomial_distr_def _ = ()
  val op binomial_distr_def = TDB.find "binomial_distr_def"
  fun op casc_series_RBD_def _ = ()
  val op casc_series_RBD_def = TDB.find "casc_series_RBD_def"
  fun op redund_star_ring_RBD_def _ = ()
  val op redund_star_ring_RBD_def = TDB.find "redund_star_ring_RBD_def"
  fun op G1_FT_def _ = () val op G1_FT_def = TDB.find "G1_FT_def"
  fun op G2_FT_def _ = () val op G2_FT_def = TDB.find "G2_FT_def"
  fun op G3_FT_def _ = () val op G3_FT_def = TDB.find "G3_FT_def"
  fun op G4_FT_def _ = () val op G4_FT_def = TDB.find "G4_FT_def"
  fun op SABP_FT_def _ = () val op SABP_FT_def = TDB.find "SABP_FT_def"
  fun op binomial_event_def _ = ()
  val op binomial_event_def = TDB.find "binomial_event_def"
  fun op binomial_event_list_def _ = ()
  val op binomial_event_list_def = TDB.find "binomial_event_list_def"
  fun op binomial_conds_def _ = ()
  val op binomial_conds_def = TDB.find "binomial_conds_def"
  fun op K_out_N_struct_list_def _ = ()
  val op K_out_N_struct_list_def = TDB.find "K_out_N_struct_list_def"
  fun op rbd_conds_def _ = ()
  val op rbd_conds_def = TDB.find "rbd_conds_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op rel_casc_seriesRBD _ = ()
  val op rel_casc_seriesRBD = TDB.find "rel_casc_seriesRBD"
  fun op len_EL_lem1 _ = () val op len_EL_lem1 = TDB.find "len_EL_lem1"
  fun op rel_redund_star_ringRBD _ = ()
  val op rel_redund_star_ringRBD = TDB.find "rel_redund_star_ringRBD"
  fun op SABP_FT_alt_form _ = ()
  val op SABP_FT_alt_form = TDB.find "SABP_FT_alt_form"
  fun op SABP_FT_alt_form1 _ = ()
  val op SABP_FT_alt_form1 = TDB.find "SABP_FT_alt_form1"
  fun op fail_prob_SABP_FT_lem1 _ = ()
  val op fail_prob_SABP_FT_lem1 = TDB.find "fail_prob_SABP_FT_lem1"
  fun op fail_prob_SABP_FT _ = ()
  val op fail_prob_SABP_FT = TDB.find "fail_prob_SABP_FT"
  fun op k_out_n_alt _ = () val op k_out_n_alt = TDB.find "k_out_n_alt"
  fun op k_out_n_RBD_v2 _ = ()
  val op k_out_n_RBD_v2 = TDB.find "k_out_n_RBD_v2"
  fun op bigunion_in_events _ = ()
  val op bigunion_in_events = TDB.find "bigunion_in_events"
  fun op series_rbd_indep_k_out_n_rbd _ = ()
  val op series_rbd_indep_k_out_n_rbd = TDB.find
    "series_rbd_indep_k_out_n_rbd"
  fun op parallel_rbd_indep_k_out_n_rbd _ = ()
  val op parallel_rbd_indep_k_out_n_rbd = TDB.find
    "parallel_rbd_indep_k_out_n_rbd"
  fun op parallel_rbd_indep_k_out_n_rbd_v1 _ = ()
  val op parallel_rbd_indep_k_out_n_rbd_v1 = TDB.find
    "parallel_rbd_indep_k_out_n_rbd_v1"
  fun op series_parallel_rbd_indep_k_out_n_rbd_exp_dist _ = ()
  val op series_parallel_rbd_indep_k_out_n_rbd_exp_dist = TDB.find
    "series_parallel_rbd_indep_k_out_n_rbd_exp_dist"
  fun op series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval _ = ()
  val op series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval = TDB.find
    "series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val smart_grid_grammars = merge_grammars ["ASN_gateway"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="smart_grid"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val smart_grid_grammars = 
    Portable.## (addtyUDs,addtmUDs) smart_grid_grammars
  val _ = Parse.grammarDB_insert("smart_grid",smart_grid_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "smart_grid"

end
