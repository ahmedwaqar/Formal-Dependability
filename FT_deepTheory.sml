structure FT_deepTheory :> FT_deepTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading FT_deepTheory ... "
    else ()
  
  open Type Term Thm
  local open RBDTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "FT_deep"
        (holpathdb.subst_pathvars "/home/waqar/12phdwahmad@seecs.edu.pk/Dropbox/WaqarP_data/Docs_for_Thesis_Compilation/HOL-Code-thesis/Formal_Depend_k12/Formal-Dependability/FT_deepTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op K_out_N_struct_def _ = ()
  val op K_out_N_struct_def = TDB.find "K_out_N_struct_def"
  fun op sum_set_def _ = () val op sum_set_def = TDB.find "sum_set_def"
  fun op comp_FT_gate_def _ = ()
  val op comp_FT_gate_def = TDB.find "comp_FT_gate_def"
  fun op inhibit_FT_gate_def _ = ()
  val op inhibit_FT_gate_def = TDB.find "inhibit_FT_gate_def"
  fun op XOR_FT_gate_def _ = ()
  val op XOR_FT_gate_def = TDB.find "XOR_FT_gate_def"
  fun op NOR_FT_gate_def _ = ()
  val op NOR_FT_gate_def = TDB.find "NOR_FT_gate_def"
  fun op gate_list_def _ = ()
  val op gate_list_def = TDB.find "gate_list_def"
  fun op gate_size_def _ = ()
  val op gate_size_def = TDB.find "gate_size_def"
  fun op gate_case_def _ = ()
  val op gate_case_def = TDB.find "gate_case_def"
  fun op gate_TY_DEF _ = () val op gate_TY_DEF = TDB.find "gate_TY_DEF"
  fun op UNIONL_def _ = () val op UNIONL_def = TDB.find "UNIONL_def"
  fun op majority_voting_FT_gate_def _ = ()
  val op majority_voting_FT_gate_def = TDB.find
    "majority_voting_FT_gate_def"
  fun op has_size_def _ = () val op has_size_def = TDB.find "has_size_def"
  fun op inter_list_def _ = ()
  val op inter_list_def = TDB.find "inter_list_def"
  fun op union_list_def _ = ()
  val op union_list_def = TDB.find "union_list_def"
  fun op BINOMIAL_DEF4 _ = ()
  val op BINOMIAL_DEF4 = TDB.find "BINOMIAL_DEF4"
  fun op BINOMIAL_DEF5 _ = ()
  val op BINOMIAL_DEF5 = TDB.find "BINOMIAL_DEF5"
  fun op BINOMIAL_FACT _ = ()
  val op BINOMIAL_FACT = TDB.find "BINOMIAL_FACT"
  fun op BINOMIAL_DEF7 _ = ()
  val op BINOMIAL_DEF7 = TDB.find "BINOMIAL_DEF7"
  fun op BINOMIAL_DEF3 _ = ()
  val op BINOMIAL_DEF3 = TDB.find "BINOMIAL_DEF3"
  fun op BINOMIAL_DEF2 _ = ()
  val op BINOMIAL_DEF2 = TDB.find "BINOMIAL_DEF2"
  fun op BINOMIAL_DEF1 _ = ()
  val op BINOMIAL_DEF1 = TDB.find "BINOMIAL_DEF1"
  fun op SUM_POS_LT _ = () val op SUM_POS_LT = TDB.find "SUM_POS_LT"
  fun op SUM_SWITCH_SUM _ = ()
  val op SUM_SWITCH_SUM = TDB.find "SUM_SWITCH_SUM"
  fun op SUM_C_EQ _ = () val op SUM_C_EQ = TDB.find "SUM_C_EQ"
  fun op SUM_SHIFT_P _ = () val op SUM_SHIFT_P = TDB.find "SUM_SHIFT_P"
  fun op SUM_SHIFT _ = () val op SUM_SHIFT = TDB.find "SUM_SHIFT"
  fun op SUM_1_SUM_2 _ = () val op SUM_1_SUM_2 = TDB.find "SUM_1_SUM_2"
  fun op SUM_0_SUM_2 _ = () val op SUM_0_SUM_2 = TDB.find "SUM_0_SUM_2"
  fun op SUM_0_SUM_1 _ = () val op SUM_0_SUM_1 = TDB.find "SUM_0_SUM_1"
  fun op binomial_def_compute _ = ()
  val op binomial_def_compute = TDB.find "binomial_def_compute"
  fun op binomial_def _ = () val op binomial_def = TDB.find "binomial_def"
  fun op binomial_ind _ = () val op binomial_ind = TDB.find "binomial_ind"
  fun op comp_FT_gate_thm _ = ()
  val op comp_FT_gate_thm = TDB.find "comp_FT_gate_thm"
  fun op inhibit_FT_gate_thm _ = ()
  val op inhibit_FT_gate_thm = TDB.find "inhibit_FT_gate_thm"
  fun op indep_compl_event_nevents _ = ()
  val op indep_compl_event_nevents = TDB.find "indep_compl_event_nevents"
  fun op mutual_indep_append_sym _ = ()
  val op mutual_indep_append_sym = TDB.find "mutual_indep_append_sym"
  fun op XOR_FT_gate_thm _ = ()
  val op XOR_FT_gate_thm = TDB.find "XOR_FT_gate_thm"
  fun op PROB_XOR_GATE1 _ = ()
  val op PROB_XOR_GATE1 = TDB.find "PROB_XOR_GATE1"
  fun op compl_event_nevent_empty _ = ()
  val op compl_event_nevent_empty = TDB.find "compl_event_nevent_empty"
  fun op prob_compl_A_INTER_B _ = ()
  val op prob_compl_A_INTER_B = TDB.find "prob_compl_A_INTER_B"
  fun op PROB_XOR_GATE _ = ()
  val op PROB_XOR_GATE = TDB.find "PROB_XOR_GATE"
  fun op PROB_COMPL_SUBSET _ = ()
  val op PROB_COMPL_SUBSET = TDB.find "PROB_COMPL_SUBSET"
  fun op xor_gate_temp2 _ = ()
  val op xor_gate_temp2 = TDB.find "xor_gate_temp2"
  fun op xor_gate_temp1 _ = ()
  val op xor_gate_temp1 = TDB.find "xor_gate_temp1"
  fun op NOR_gate_thm _ = () val op NOR_gate_thm = TDB.find "NOR_gate_thm"
  fun op NAND_FT_gate _ = () val op NAND_FT_gate = TDB.find "NAND_FT_gate"
  fun op NAND_eq_big_inter_alt_form _ = ()
  val op NAND_eq_big_inter_alt_form = TDB.find "NAND_eq_big_inter_alt_form"
  fun op AND_gate_append _ = ()
  val op AND_gate_append = TDB.find "AND_gate_append"
  fun op OR_gate_thm _ = () val op OR_gate_thm = TDB.find "OR_gate_thm"
  fun op OR_lem8 _ = () val op OR_lem8 = TDB.find "OR_lem8"
  fun op OR_lem7 _ = () val op OR_lem7 = TDB.find "OR_lem7"
  fun op OR_lem6 _ = () val op OR_lem6 = TDB.find "OR_lem6"
  fun op OR_lem5 _ = () val op OR_lem5 = TDB.find "OR_lem5"
  fun op OR_lem4 _ = () val op OR_lem4 = TDB.find "OR_lem4"
  fun op OR_lem3 _ = () val op OR_lem3 = TDB.find "OR_lem3"
  fun op OR_lem2 _ = () val op OR_lem2 = TDB.find "OR_lem2"
  fun op OR_lem1 _ = () val op OR_lem1 = TDB.find "OR_lem1"
  fun op prob_indep_big_inter2 _ = ()
  val op prob_indep_big_inter2 = TDB.find "prob_indep_big_inter2"
  fun op OR_gate_lem7 _ = () val op OR_gate_lem7 = TDB.find "OR_gate_lem7"
  fun op OR_gate_lem6 _ = () val op OR_gate_lem6 = TDB.find "OR_gate_lem6"
  fun op OR_gate_lem5 _ = () val op OR_gate_lem5 = TDB.find "OR_gate_lem5"
  fun op OR_gate_lem4 _ = () val op OR_gate_lem4 = TDB.find "OR_gate_lem4"
  fun op OR_gate_lem3 _ = () val op OR_gate_lem3 = TDB.find "OR_gate_lem3"
  fun op OR_gate_lem2 _ = () val op OR_gate_lem2 = TDB.find "OR_gate_lem2"
  fun op OR_gate_lem1 _ = () val op OR_gate_lem1 = TDB.find "OR_gate_lem1"
  fun op AND_gate_thm _ = () val op AND_gate_thm = TDB.find "AND_gate_thm"
  fun op AND_gate_eq_big_inter _ = ()
  val op AND_gate_eq_big_inter = TDB.find "AND_gate_eq_big_inter"
  fun op FTree_def _ = () val op FTree_def = TDB.find "FTree_def"
  fun op FTree_ind _ = () val op FTree_ind = TDB.find "FTree_ind"
  fun op gate_case_eq _ = () val op gate_case_eq = TDB.find "gate_case_eq"
  fun op gate_case_cong _ = ()
  val op gate_case_cong = TDB.find "gate_case_cong"
  fun op gate_induction _ = ()
  val op gate_induction = TDB.find "gate_induction"
  fun op gate_Axiom _ = () val op gate_Axiom = TDB.find "gate_Axiom"
  fun op gate_nchotomy _ = ()
  val op gate_nchotomy = TDB.find "gate_nchotomy"
  fun op gate_distinct _ = ()
  val op gate_distinct = TDB.find "gate_distinct"
  fun op gate_11 _ = () val op gate_11 = TDB.find "gate_11"
  fun op datatype_gate _ = ()
  val op datatype_gate = TDB.find "datatype_gate"
  fun op IN_UNIONL _ = () val op IN_UNIONL = TDB.find "IN_UNIONL"
  fun op BINOMIAL_DEF6 _ = ()
  val op BINOMIAL_DEF6 = TDB.find "BINOMIAL_DEF6"
  fun op EXP_PASCAL_REAL _ = ()
  val op EXP_PASCAL_REAL = TDB.find "EXP_PASCAL_REAL"
  fun op EXP_PASCAL_REAL1 _ = ()
  val op EXP_PASCAL_REAL1 = TDB.find "EXP_PASCAL_REAL1"
  fun op num_neq _ = () val op num_neq = TDB.find "num_neq"
  fun op disj_thm _ = () val op disj_thm = TDB.find "disj_thm"
  fun op k_out_n_lemma1 _ = ()
  val op k_out_n_lemma1 = TDB.find "k_out_n_lemma1"
  fun op k_out_n_lemma2 _ = ()
  val op k_out_n_lemma2 = TDB.find "k_out_n_lemma2"
  fun op k_out_ntemp1 _ = () val op k_out_ntemp1 = TDB.find "k_out_ntemp1"
  fun op k_out_n_temp2 _ = ()
  val op k_out_n_temp2 = TDB.find "k_out_n_temp2"
  fun op k_out_n_lemma3 _ = ()
  val op k_out_n_lemma3 = TDB.find "k_out_n_lemma3"
  fun op k_out_n_lemma4 _ = ()
  val op k_out_n_lemma4 = TDB.find "k_out_n_lemma4"
  fun op k_out_n_temp5 _ = ()
  val op k_out_n_temp5 = TDB.find "k_out_n_temp5"
  fun op k_out_n_lemma5 _ = ()
  val op k_out_n_lemma5 = TDB.find "k_out_n_lemma5"
  fun op k_out_n_lemma6_new _ = ()
  val op k_out_n_lemma6_new = TDB.find "k_out_n_lemma6_new"
  fun op k_out_n_lemma6_new1 _ = ()
  val op k_out_n_lemma6_new1 = TDB.find "k_out_n_lemma6_new1"
  fun op k_out_n_lemma6 _ = ()
  val op k_out_n_lemma6 = TDB.find "k_out_n_lemma6"
  fun op k_out_n_RBD _ = () val op k_out_n_RBD = TDB.find "k_out_n_RBD"
  fun op k_out_n_RBD_v1 _ = ()
  val op k_out_n_RBD_v1 = TDB.find "k_out_n_RBD_v1"
  fun op K_out_N_Parallel_Struct _ = ()
  val op K_out_N_Parallel_Struct = TDB.find "K_out_N_Parallel_Struct"
  fun op K_out_N_Series_Struct _ = ()
  val op K_out_N_Series_Struct = TDB.find "K_out_N_Series_Struct"
  fun op majority_voting_FT_gate_thm _ = ()
  val op majority_voting_FT_gate_thm = TDB.find
    "majority_voting_FT_gate_thm"
  fun op SUBSET_INSERT_EXISTS_NEW _ = ()
  val op SUBSET_INSERT_EXISTS_NEW = TDB.find "SUBSET_INSERT_EXISTS_NEW"
  fun op FINITE_SUBSETS_RESTRICT_NEW _ = ()
  val op FINITE_SUBSETS_RESTRICT_NEW = TDB.find
    "FINITE_SUBSETS_RESTRICT_NEW"
  fun op FINITE_SUBSETS_RESTRICT_NEW1 _ = ()
  val op FINITE_SUBSETS_RESTRICT_NEW1 = TDB.find
    "FINITE_SUBSETS_RESTRICT_NEW1"
  fun op lemma_NEW _ = () val op lemma_NEW = TDB.find "lemma_NEW"
  fun op temp1 _ = () val op temp1 = TDB.find "temp1"
  fun op temp3 _ = () val op temp3 = TDB.find "temp3"
  fun op temp2 _ = () val op temp2 = TDB.find "temp2"
  fun op temp4 _ = () val op temp4 = TDB.find "temp4"
  fun op has_size_suc _ = () val op has_size_suc = TDB.find "has_size_suc"
  fun op FORALL_INSERT _ = ()
  val op FORALL_INSERT = TDB.find "FORALL_INSERT"
  fun op INTER_BIGUNION _ = ()
  val op INTER_BIGUNION = TDB.find "INTER_BIGUNION"
  fun op has_size_clauses _ = ()
  val op has_size_clauses = TDB.find "has_size_clauses"
  fun op temp5 _ = () val op temp5 = TDB.find "temp5"
  fun op incl_excl_temp1 _ = ()
  val op incl_excl_temp1 = TDB.find "incl_excl_temp1"
  fun op temp6 _ = () val op temp6 = TDB.find "temp6"
  fun op simple_image_gen _ = ()
  val op simple_image_gen = TDB.find "simple_image_gen"
  fun op FINITE_RESTRICT _ = ()
  val op FINITE_RESTRICT = TDB.find "FINITE_RESTRICT"
  fun op incl_excl_temp2 _ = ()
  val op incl_excl_temp2 = TDB.find "incl_excl_temp2"
  fun op incl_excl_temp3 _ = ()
  val op incl_excl_temp3 = TDB.find "incl_excl_temp3"
  fun op incl_excl_temp4 _ = ()
  val op incl_excl_temp4 = TDB.find "incl_excl_temp4"
  fun op incl_excl_temp5 _ = ()
  val op incl_excl_temp5 = TDB.find "incl_excl_temp5"
  fun op incl_excl_temp6 _ = ()
  val op incl_excl_temp6 = TDB.find "incl_excl_temp6"
  fun op incl_excl_temp7 _ = ()
  val op incl_excl_temp7 = TDB.find "incl_excl_temp7"
  fun op incl_excl_temp8 _ = ()
  val op incl_excl_temp8 = TDB.find "incl_excl_temp8"
  fun op incl_excl_temp9 _ = ()
  val op incl_excl_temp9 = TDB.find "incl_excl_temp9"
  fun op BIGINTER_SET _ = () val op BIGINTER_SET = TDB.find "BIGINTER_SET"
  fun op REAL_SUM_IMAGE_IMAGE1 _ = ()
  val op REAL_SUM_IMAGE_IMAGE1 = TDB.find "REAL_SUM_IMAGE_IMAGE1"
  fun op INCLUSION_EXCLUSION_RESTRICTED _ = ()
  val op INCLUSION_EXCLUSION_RESTRICTED = TDB.find
    "INCLUSION_EXCLUSION_RESTRICTED"
  fun op INCLUSION_EXCLUSION_RESTRICTED_REAL _ = ()
  val op INCLUSION_EXCLUSION_RESTRICTED_REAL = TDB.find
    "INCLUSION_EXCLUSION_RESTRICTED_REAL"
  fun op PROB_INCLUSION_EXCLUSION _ = ()
  val op PROB_INCLUSION_EXCLUSION = TDB.find "PROB_INCLUSION_EXCLUSION"
  fun op PROB_INCLUSION_EXCLUSION_list _ = ()
  val op PROB_INCLUSION_EXCLUSION_list = TDB.find
    "PROB_INCLUSION_EXCLUSION_list"
  fun op BIGUNION_EQ_UNION_LIST _ = ()
  val op BIGUNION_EQ_UNION_LIST = TDB.find "BIGUNION_EQ_UNION_LIST"
  fun op PROB_INCLUSION_EXCLUSION_PRINCIPLE _ = ()
  val op PROB_INCLUSION_EXCLUSION_PRINCIPLE = TDB.find
    "PROB_INCLUSION_EXCLUSION_PRINCIPLE"
  
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val FT_deep_grammars = merge_grammars ["RBD"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="FT_deep"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val FT_deep_grammars = 
    Portable.## (addtyUDs,addtmUDs) FT_deep_grammars
  val _ = Parse.grammarDB_insert("FT_deep",FT_deep_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "FT_deep"

end
