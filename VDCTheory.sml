structure VDCTheory :> VDCTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading VDCTheory ... "
    else ()
  
  open Type Term Thm
  local open RBDTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "VDC"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/VDCTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op fail_event_def _ = ()
  val op fail_event_def = TDB.find "fail_event_def"
  fun op rel_event_def _ = ()
  val op rel_event_def = TDB.find "rel_event_def"
  fun op rel_event_list_def _ = ()
  val op rel_event_list_def = TDB.find "rel_event_list_def"
  fun op two_dim_rel_event_list_def _ = ()
  val op two_dim_rel_event_list_def = TDB.find "two_dim_rel_event_list_def"
  fun op three_dim_rel_event_list_def _ = ()
  val op three_dim_rel_event_list_def = TDB.find
    "three_dim_rel_event_list_def"
  fun op four_dim_rel_event_list_def _ = ()
  val op four_dim_rel_event_list_def = TDB.find
    "four_dim_rel_event_list_def"
  fun op log_base_def _ = () val op log_base_def = TDB.find "log_base_def"
  fun op gen_list_def _ = () val op gen_list_def = TDB.find "gen_list_def"
  fun op cloud_server_fail_rate_list_def _ = ()
  val op cloud_server_fail_rate_list_def = TDB.find
    "cloud_server_fail_rate_list_def"
  fun op cloud_server_rv_list_def _ = ()
  val op cloud_server_rv_list_def = TDB.find "cloud_server_rv_list_def"
  fun op CDF_def _ = () val op CDF_def = TDB.find "CDF_def"
  fun op Reliability_def _ = ()
  val op Reliability_def = TDB.find "Reliability_def"
  fun op rel_virt_cloud_server_def _ = ()
  val op rel_virt_cloud_server_def = TDB.find "rel_virt_cloud_server_def"
  fun op exp_func_list_def _ = ()
  val op exp_func_list_def = TDB.find "exp_func_list_def"
  fun op exp_dist_def _ = () val op exp_dist_def = TDB.find "exp_dist_def"
  fun op exp_dist_list_def _ = ()
  val op exp_dist_list_def = TDB.find "exp_dist_list_def"
  fun op two_dim_exp_dist_list_def _ = ()
  val op two_dim_exp_dist_list_def = TDB.find "two_dim_exp_dist_list_def"
  fun op three_dim_exp_dist_list_def _ = ()
  val op three_dim_exp_dist_list_def = TDB.find
    "three_dim_exp_dist_list_def"
  fun op four_dim_exp_dist_list_def _ = ()
  val op four_dim_exp_dist_list_def = TDB.find "four_dim_exp_dist_list_def"
  fun op gen_rv_list_def _ = ()
  val op gen_rv_list_def = TDB.find "gen_rv_list_def"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op gen_list_def_compute _ = ()
  val op gen_list_def_compute = TDB.find "gen_list_def_compute"
  fun op not_null_map _ = () val op not_null_map = TDB.find "not_null_map"
  fun op extreal_not_le _ = ()
  val op extreal_not_le = TDB.find "extreal_not_le"
  fun op compl_rel_event_eq_fail_event _ = ()
  val op compl_rel_event_eq_fail_event = TDB.find
    "compl_rel_event_eq_fail_event"
  fun op gen_list_suc _ = () val op gen_list_suc = TDB.find "gen_list_suc"
  fun op compl_fail_event_eq_rel_event _ = ()
  val op compl_fail_event_eq_rel_event = TDB.find
    "compl_fail_event_eq_rel_event"
  fun op comp_rel_event_eq_fail_event _ = ()
  val op comp_rel_event_eq_fail_event = TDB.find
    "comp_rel_event_eq_fail_event"
  fun op rel_series_parallel_RBD_exp_dist_fail_rate_lemma1 _ = ()
  val op rel_series_parallel_RBD_exp_dist_fail_rate_lemma1 = TDB.find
    "rel_series_parallel_RBD_exp_dist_fail_rate_lemma1"
  fun op rel_series_parallel_RBD_exp_dist_fail_rate _ = ()
  val op rel_series_parallel_RBD_exp_dist_fail_rate = TDB.find
    "rel_series_parallel_RBD_exp_dist_fail_rate"
  fun op rbd_virtual_cloud_server_alt_form _ = ()
  val op rbd_virtual_cloud_server_alt_form = TDB.find
    "rbd_virtual_cloud_server_alt_form"
  fun op rel_virtual_cloud_server _ = ()
  val op rel_virtual_cloud_server = TDB.find "rel_virtual_cloud_server"
  fun op seq_rel_prod_tend_0 _ = ()
  val op seq_rel_prod_tend_0 = TDB.find "seq_rel_prod_tend_0"
  fun op rel_prod_tend_0 _ = ()
  val op rel_prod_tend_0 = TDB.find "rel_prod_tend_0"
  fun op bound_mult_ratr _ = ()
  val op bound_mult_ratr = TDB.find "bound_mult_ratr"
  fun op bound_log_inequal _ = ()
  val op bound_log_inequal = TDB.find "bound_log_inequal"
  fun op nlen_gen_list_eq_n1 _ = ()
  val op nlen_gen_list_eq_n1 = TDB.find "nlen_gen_list_eq_n1"
  fun op nlen_gen_list_eq_n _ = ()
  val op nlen_gen_list_eq_n = TDB.find "nlen_gen_list_eq_n"
  fun op compl_rel_pow_n _ = ()
  val op compl_rel_pow_n = TDB.find "compl_rel_pow_n"
  fun op virt_config_bounds _ = ()
  val op virt_config_bounds = TDB.find "virt_config_bounds"
  fun op mem_flat_map_not_null2 _ = ()
  val op mem_flat_map_not_null2 = TDB.find "mem_flat_map_not_null2"
  fun op mem_flat_map_not_null3 _ = ()
  val op mem_flat_map_not_null3 = TDB.find "mem_flat_map_not_null3"
  fun op mem_flat_map_not_null1 _ = ()
  val op mem_flat_map_not_null1 = TDB.find "mem_flat_map_not_null1"
  fun op mem_flat_map_not_null _ = ()
  val op mem_flat_map_not_null = TDB.find "mem_flat_map_not_null"
  fun op parallel_series_parallel_rbd_alt_form _ = ()
  val op parallel_series_parallel_rbd_alt_form = TDB.find
    "parallel_series_parallel_rbd_alt_form"
  fun op nested_series_parallel_rbd_alt_form _ = ()
  val op nested_series_parallel_rbd_alt_form = TDB.find
    "nested_series_parallel_rbd_alt_form"
  fun op mem_flat_fun_eq_mem_flat_null_list1 _ = ()
  val op mem_flat_fun_eq_mem_flat_null_list1 = TDB.find
    "mem_flat_fun_eq_mem_flat_null_list1"
  fun op mem_flat_fun_eq_mem_flat_null_list2 _ = ()
  val op mem_flat_fun_eq_mem_flat_null_list2 = TDB.find
    "mem_flat_fun_eq_mem_flat_null_list2"
  fun op mem_flat_fun_eq_mem_flat_null_list3 _ = ()
  val op mem_flat_fun_eq_mem_flat_null_list3 = TDB.find
    "mem_flat_fun_eq_mem_flat_null_list3"
  fun op mem_flat_fun_eq_mem_flat_null_list _ = ()
  val op mem_flat_fun_eq_mem_flat_null_list = TDB.find
    "mem_flat_fun_eq_mem_flat_null_list"
  fun op parallel_series_parallel_prod_rel_exp_dist _ = ()
  val op parallel_series_parallel_prod_rel_exp_dist = TDB.find
    "parallel_series_parallel_prod_rel_exp_dist"
  fun op nested_series_parallel_exp_dist _ = ()
  val op nested_series_parallel_exp_dist = TDB.find
    "nested_series_parallel_exp_dist"
  fun op cloud_server_rv_list_not_null1 _ = ()
  val op cloud_server_rv_list_not_null1 = TDB.find
    "cloud_server_rv_list_not_null1"
  fun op cloud_server_rv_list_not_null2 _ = ()
  val op cloud_server_rv_list_not_null2 = TDB.find
    "cloud_server_rv_list_not_null2"
  fun op cloud_server_rv_list_not_null3 _ = ()
  val op cloud_server_rv_list_not_null3 = TDB.find
    "cloud_server_rv_list_not_null3"
  fun op cloud_server_rv_list_not_null _ = ()
  val op cloud_server_rv_list_not_null = TDB.find
    "cloud_server_rv_list_not_null"
  fun op in_events_cloud_server_rv_list1 _ = ()
  val op in_events_cloud_server_rv_list1 = TDB.find
    "in_events_cloud_server_rv_list1"
  fun op in_events_cloud_server_rv_list _ = ()
  val op in_events_cloud_server_rv_list = TDB.find
    "in_events_cloud_server_rv_list"
  fun op rel_prod_series_rbd_exp_dist _ = ()
  val op rel_prod_series_rbd_exp_dist = TDB.find
    "rel_prod_series_rbd_exp_dist"
  fun op len_cloud_server_fail_rate_eq_rv_list _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list"
  fun op len_cloud_server_fail_rate_eq_rv_list1 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list1 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list1"
  fun op len_cloud_server_fail_rate_eq_rv_list2 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list2 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list2"
  fun op len_cloud_server_fail_rate_eq_rv_list3 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list3 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list3"
  fun op len_cloud_server_fail_rate_eq_rv_list4 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list4 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list4"
  fun op len_cloud_server_fail_rate_eq_rv_list5 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list5 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list5"
  fun op len_cloud_server_fail_rate_eq_rv_list6 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list6 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list6"
  fun op len_cloud_server_fail_rate_eq_rv_list7 _ = ()
  val op len_cloud_server_fail_rate_eq_rv_list7 = TDB.find
    "len_cloud_server_fail_rate_eq_rv_list7"
  fun op VDC_case_study_thm _ = ()
  val op VDC_case_study_thm = TDB.find "VDC_case_study_thm"
  fun op parallel_series_exp_fail_rate _ = ()
  val op parallel_series_exp_fail_rate = TDB.find
    "parallel_series_exp_fail_rate"
  fun op rel_parallel_series_exp_fail_rate _ = ()
  val op rel_parallel_series_exp_fail_rate = TDB.find
    "rel_parallel_series_exp_fail_rate"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val VDC_grammars = merge_grammars ["RBD"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="VDC"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val VDC_grammars = 
    Portable.## (addtyUDs,addtmUDs) VDC_grammars
  val _ = Parse.grammarDB_insert("VDC",VDC_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "VDC"

end
