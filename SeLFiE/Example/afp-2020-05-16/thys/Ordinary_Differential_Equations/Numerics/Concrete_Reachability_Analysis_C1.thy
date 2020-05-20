theory Concrete_Reachability_Analysis_C1
imports
  Concrete_Reachability_Analysis
  Abstract_Reachability_Analysis_C1
begin

definition "op_card_vec TYPE('a) = CARD('a)"
lemma op_card_vec_pat_def[autoref_op_pat_def]: "CARD('a) \<equiv> OP (op_card_vec TYPE('a))"
  by (auto simp: op_card_vec_def)
lemma op_card_vec_impl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) E"
  shows "(E, op_card_vec TYPE('a)) \<in> nat_rel"
  using assms by (auto simp: op_card_vec_def)


context approximate_sets
begin

sublocale approximate_sets_ode' where ode_ops = ode_ops for ode_ops ..\<comment> \<open>parametrized by \<open>ode_ops\<close>\<close>

end

context approximate_sets
begin

lemma nonneg_reals_autoref[autoref_rules]: "(None, nonneg_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  and pos_reals_autoref[autoref_rules]: "(None, pos_reals) \<in> \<langle>Id\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

lemma appr1_relI:
  assumes "c1_info_invar DIM('n::executable_euclidean_space) X0i"
  shows "(X0i, (c1_info_of_appr X0i::'n c1_info set)) \<in> appr1_rel"
    using assms
  apply (cases "snd X0i")
  subgoal
    apply (simp add: c1_info_of_appr_def c1_info_invar_def)
    unfolding appr1_rel_internal
    apply (rule UnI1)
    apply auto
    apply (rule exI[where x="fst X0i"])
    apply safe
    subgoal by (auto simp: prod_eq_iff)
    subgoal
      apply (rule exI[where x="eucl_of_list ` set_of_appr (fst X0i)"])
      apply (auto simp: appr_rel_def)
      by (auto simp: appr_rell_internal lv_rel_def set_rel_br br_chain length_set_of_appr
          intro!: brI)
    done
  subgoal for D
    apply (simp add: c1_info_of_appr_def c1_info_invar_def)
    unfolding appr1_rel_internal
    apply (rule UnI2)
    apply (auto simp: set_rel_br)
    apply (rule exI[where x="fst X0i"])
    apply (rule exI[where x=D])
    apply safe
    subgoal by (auto simp: prod_eq_iff)
    subgoal
      by (auto simp: appr_rell_internal lv_rel_def set_rel_br br_chain length_set_of_appr
          intro!: brI) (auto simp:  power2_eq_square)
    done
  done

lemma appr1_rel_br: "appr1_rel = br (c1_info_of_appr::_\<Rightarrow>('n c1_info)set) (c1_info_invar DIM('n::executable_euclidean_space))"
  apply (auto simp: dest!: brD intro!: appr1_relI)
  apply (rule brI)
  subgoal by (auto simp: appr1_rel_internal c1_info_of_appr_def appr_rel_br set_rel_br dest!: brD)
  subgoal by (auto simp: c1_info_invar_def appr1_rel_internal appr_rel_br power2_eq_square dest!: brD)
  done

lemma appr1_rel_aux:
  "{((xs, Some ys), X) |xs ys X. (xs @ ys, X) \<in> appr_rel \<and> length ys = (length xs)\<^sup>2} O
    \<langle>br flow1_of_vec1 top\<rangle>set_rel =
  {((xs, Some ys), X::'n eucl1 set) |xs ys X.
     X = (\<lambda>xs. flow1_of_vec1 (eucl_of_list xs)) ` set_of_appr (xs @ ys) \<and>
     length xs = DIM((real, 'n::enum) vec) \<and> length ys = DIM((real, 'n) vec) * DIM((real, 'n) vec)}"
  apply (auto simp: set_rel_br appr_rel_br power2_eq_square dest!: brD)
  apply (rule relcompI)
   apply simp
   apply (rule brI) apply (rule refl) apply simp
  apply (rule brI) defer apply simp
  apply auto
  done

lemma flow1_of_list_def':
  shows "flow1_of_list xs = flow1_of_vec1 (eucl_of_list xs)"
  by (auto simp: flow1_of_list_def flow1_of_vec1_def eucl_of_list_prod
      blinfun_of_list_eq_blinfun_of_vmatrix)

lemma appr1_rel_def:
  "appr1_rel =
    {((xs, None   ), X \<times> UNIV)| xs X. (xs, X) \<in> appr_rel} \<union>
    {((xs, Some ys), X)| xs ys X. (xs @ ys, X) \<in> appr_rel \<and> length ys = (length xs)\<^sup>2} O \<langle>br flow1_of_vec1 top\<rangle>set_rel"
  unfolding appr1_rel_internal flow1_of_list_def'[abs_def] appr1_rel_aux ..

lemmas [autoref_rel_intf] = REL_INTFI[of appr1_rel i_appr1]
lemma [autoref_op_pat]: "(`) flow1_of_vec1 \<equiv> OP op_image_flow1_of_vec1"
  by auto

lemma op_image_flow1_of_vec1[autoref_rules]:
  assumes "DIM_precond TYPE('a rvec) E"
  shows "(\<lambda>xs. (take E xs, Some (drop E xs)),
    op_image_flow1_of_vec1::('a::enum) vec1 set\<Rightarrow>_) \<in> appr_rel \<rightarrow> appr1_rel"
  using assms
  apply (auto simp: appr1_rel_def set_rel_br flow1_of_vec1_def[abs_def] intro!: brI elim!: notE
      split: option.splits list.splits)
  apply (rule relcompI[OF _ brI[OF refl]])
   apply (auto simp: power2_eq_square min_def appr_rel_br br_def)
  done

lemma index_autoref[autoref_rules]:
  "(index, index) \<in> \<langle>lv_rel\<rangle>list_rel \<rightarrow> lv_rel \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def
  apply parametricity
  apply (auto simp: lv_rel_def br_def list_rel_def)
  using list_of_eucl_eucl_of_list by force

lemma [autoref_op_pat]: "(`) fst \<equiv> OP op_image_fst"
  by auto

lemma op_image_fst_flow1[autoref_rules]:
  shows "(\<lambda>x. fst x, op_image_fst::_\<Rightarrow>'n::executable_euclidean_space set) \<in> appr1_rel \<rightarrow> appr_rel"
  apply (auto simp: appr1_rel_internal flow1_of_list_def set_rel_br image_image power2_eq_square dest!: brD)
  apply (auto simp: br_def appr_rel_br length_set_of_appr image_image eucl_of_list_prod
      dest!: set_of_appr_takeD)
  subgoal for xs ys a
    apply (rule image_eqI[where x="take DIM('n) a"])
    by (auto intro!: take_set_of_apprI dest: length_set_of_appr)
  subgoal for xs ys a
    apply (frule set_of_appr_ex_append2[where b=ys])
    apply auto
    subgoal for r
      apply (rule image_eqI[where x="a @ r"])
       apply (auto simp: length_set_of_appr )
      apply (rule eucl_of_list_eqI)
      by (auto dest!: length_set_of_appr)
    done
  done

lemma op_image_fste_impl[autoref_rules]:
  "((\<lambda>(_, x, _). x), op_image_fste) \<in> appr1e_rel \<rightarrow> appr_rel"
  by (auto simp: image_image split_beta' scaleR2_rel_def
      dest!: op_image_fst_flow1[param_fo] brD)

lemma DIM_precond_vec1I[autoref_rules_raw]:
  assumes "DIM_precond TYPE('n::enum rvec) E"
  shows "DIM_precond TYPE('n::enum vec1) (E + E*E)"
  using assms
  by (auto simp: )

lemma vec1rep_impl[autoref_rules]:
  "(\<lambda>(a, bs). RETURN (map_option ((@) a) bs), vec1rep) \<in> appr1_rel \<rightarrow> \<langle>\<langle>appr_rel\<rangle>option_rel\<rangle>nres_rel"
  apply (auto simp: vec1rep_def appr1_rel_def set_rel_br appr_rel_def power2_eq_square nres_rel_def
      dest!: brD
      intro!: RETURN_SPEC_refine)
  subgoal for xs ys a b
    apply (rule exI[where x="Some (eucl_of_list ` set_of_appr (xs @ ys))"])
    apply (auto simp: appr_rell_internal image_image lv_rel_def set_rel_br length_set_of_appr
        intro!: brI dest!: brD)
    done
  done

lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV $ X" by simp

lemma op_times_UNIV_impl[autoref_rules]: "(\<lambda>x. (x, None), op_times_UNIV) \<in> appr_rel \<rightarrow> appr1_rel"
  by (auto simp: appr1_rel_internal)

schematic_goal solve_poincare_plane_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(ni, n) \<in> lv_rel" and CX[autoref_rules]: "(CXi, CX) \<in> appr1_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of (?R), solve_poincare_plane odo n (CX::'n eucl1 set)) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding solve_poincare_plane_def
  including art
  by autoref_monadic
concrete_definition solve_poincare_plane_impl for ni CXi uses solve_poincare_plane_impl
lemmas solve_poincare_plane_impl_refine[autoref_rules] = solve_poincare_plane_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def solve_poincare_plane .

lemma [autoref_rules_raw]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) K"
  shows "DIM_precond TYPE(((real, 'n) vec, 'n) vec) (K * K)"
  using assms by auto

lemma embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) E"
  shows "((\<lambda>x. x @ replicate (E * E) 0), embed1::'n rvec\<Rightarrow>_) \<in> lv_rel \<rightarrow> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def eucl_of_list_prod)

definition "var_ode_ops_impl = (\<lambda>(ode_ops, _, _, vode_slps).
    (var_ode_ops ode_ops, (case vode_slps of None =>
      let _ = print_msg_impl ''ODE solver not properly initialized: vode_slps missing!'' in
      ode_slps_of (approximate_sets_ode'.var_ode_ops ode_ops)
    | Some (vode_slps) => vode_slps), None, None))"

lemma var_ode_ops[autoref_rules]: "(var_ode_ops_impl, var_ode_ops) \<in> ode_ops_rel \<rightarrow> ode_ops_rel"
  by (auto simp: var_ode_ops_impl_def ode_ops_rel_def init_ode_ops_def split: option.splits)

schematic_goal choose_step1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
    "ncc_precond TYPE('n vec1)"
    "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel" "(hi, h) \<in> rnv_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  notes [autoref_post_simps] = fst_conv
  shows "(nres_of ?f, choose_step1 odo X h) \<in> \<langle>rnv_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding choose_step1_def
  including art
  by autoref_monadic
concrete_definition choose_step1_impl for Xi hi uses choose_step1_impl
lemmas [autoref_rules] = choose_step1_impl.refine[autoref_higher_order_rule (1 2 3)]
sublocale autoref_op_pat_def choose_step1 .

lemma op_image_zerofst_impl[autoref_rules]:
  "(\<lambda>(_, x). (appr_of_ivl ops (replicate E 0) (replicate E 0), x), op_image_zerofst::'n c1_info set \<Rightarrow> _)
    \<in> appr1_rel \<rightarrow> appr1_rel"
  if "DIM_precond (TYPE('n::executable_euclidean_space)) E"
  using that
  apply (auto simp: appr1_rel_br dest!: brD intro!: brI)
  subgoal by (force simp: c1_info_of_appr_def image_image flow1_of_list_def
        set_of_appr_of_ivl_point_append eucl_of_list_prod c1_info_invar_def length_set_of_appr
        split: option.splits elim!: mem_set_of_appr_appendE cong del: image_cong_simp)
  subgoal for a b c d
    apply (auto simp: c1_info_of_appr_def
        split: option.splits)
    subgoal using set_of_appr_nonempty[of a]
      by (force  simp del: set_of_appr_nonempty)
    subgoal
      supply [simp del] = eucl_of_list_take_DIM
      apply (auto simp: image_image set_of_appr_of_ivl_point_append
          flow1_of_list_def)
      apply (frule set_of_appr_ex_append1[where b=a])
      apply auto
      apply (rule image_eqI) prefer 2 apply assumption
      by (auto simp: eucl_of_list_prod c1_info_invar_def
          dest!: length_set_of_appr)
    done
  subgoal
    by (auto simp: c1_info_of_appr_def flow1_of_vec1_def image_image
        set_of_appr_of_ivl_point_append eucl_of_list_prod c1_info_invar_def length_set_of_appr
        split: option.splits elim!: mem_set_of_appr_appendE)
  done
sublocale autoref_op_pat_def op_image_zerofst .

lemma op_image_zerofst_vec_impl[autoref_rules]:
  "(\<lambda>x. (appr_of_ivl ops (replicate E 0) (replicate E 0) @ drop E x), op_image_zerofst_vec::'n vec1 set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  if "DIM_precond (TYPE('n::enum rvec)) E"
  using that
  apply (auto simp: appr_rel_br set_of_appr_of_ivl_point_append image_image eucl_of_list_prod
      dest!: brD intro!: brI
      dest: drop_set_of_apprD[where n="CARD('n)"] cong del: image_cong_simp)
  subgoal for a b
    apply (drule set_of_appr_dropD)
    apply safe
    apply (rule image_eqI) defer apply assumption
    apply (auto simp: eucl_of_list_prod)
    apply (rule eucl_of_list_eq_takeI)
    apply simp
    done
  done
sublocale autoref_op_pat_def op_image_zerofst_vec .

lemma [autoref_op_pat_def]: "embed1 ` X \<equiv> OP op_image_embed1 $ X"
  by auto

lemma op_image_embed1_impl[autoref_rules]:
  assumes "DIM_precond TYPE((real, 'n::enum) vec) E"
  shows "(\<lambda>x. x@appr_of_ivl ops (replicate (E*E) 0) (replicate (E*E) 0), op_image_embed1::'n rvec set \<Rightarrow> _)
    \<in> appr_rel \<rightarrow> appr_rel"
  using assms
  by (force simp: appr_rel_br br_def set_of_appr_of_ivl_point_append set_of_appr_of_ivl_append_point
      image_image eucl_of_list_prod length_set_of_appr)
sublocale autoref_op_pat_def op_image_embed1 .

lemma sv_appr1_rel[relator_props]: "single_valued appr1_rel"
  apply (auto simp:  appr1_rel_internal appr_rel_def intro!: relator_props single_valued_union)
   apply (auto simp: single_valued_def)
   apply (auto simp: lv_rel_def set_rel_br)
   apply (auto simp: br_def)
   apply (rule imageI)
  apply (metis single_valued_def sv_appr_rell)
  by (metis imageI single_valued_def sv_appr_rell)

schematic_goal inter_sctn1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E" "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(Xi, (X::'n eucl1 set)) \<in> appr1_rel" "(hi, h) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?f, inter_sctn1_spec X h) \<in> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding inter_sctn1_spec_def
  including art
  by autoref_monadic
concrete_definition inter_sctn1_impl for Xi hi uses inter_sctn1_impl
lemmas [autoref_rules] = inter_sctn1_impl.refine[autoref_higher_order_rule (1 2)]
sublocale autoref_op_pat_def inter_sctn1_spec .

schematic_goal op_image_fst_coll_nres_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::executable_euclidean_space) E"
  assumes [autoref_rules]: "(XSi, (XS::'n c1_info set)) \<in> clw_rel appr1_rel"
  shows "(RETURN ?r, op_image_fst_coll_nres XS) \<in> \<langle>clw_rel appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding op_image_fst_coll_nres_def
  including art
  by (autoref_monadic (plain))
concrete_definition op_image_fst_coll_nres_impl for XSi uses op_image_fst_coll_nres_impl
lemmas [autoref_rules] = op_image_fst_coll_nres_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def op_image_fst_coll_nres .

lemma [autoref_op_pat]: "(`) fst \<equiv> OP op_image_fst_coll"
  by auto
lemma op_image_fst_coll_impl[autoref_rules]:
  assumes "DIM_precond TYPE('n::executable_euclidean_space) E"
  shows "(op_image_fst_coll_nres_impl, op_image_fst_coll::_\<Rightarrow>'n set) \<in> clw_rel appr1_rel \<rightarrow> clw_rel appr_rel"
  apply rule
  subgoal premises prems for x
    using nres_rel_trans2[OF op_image_fst_coll_nres_spec[OF order_refl]
      op_image_fst_coll_nres_impl.refine[OF assms, simplified, OF prems]]
    by (auto simp: nres_rel_def RETURN_RES_refine_iff)
  done

schematic_goal fst_safe_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::executable_euclidean_space) E"
  assumes [autoref_rules]: "(XSi, (XS::'n c1_info set)) \<in> clw_rel appr1_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of ?r, fst_safe_coll odo XS) \<in> \<langle>clw_rel appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding fst_safe_coll_def
  including art
  by autoref_monadic
concrete_definition fst_safe_coll_impl for XSi uses fst_safe_coll_impl
lemmas [autoref_rules] = fst_safe_coll_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def fst_safe_coll_impl .

lemma [autoref_op_pat]: "(`) flow1_of_vec1 \<equiv> OP op_image_flow1_of_vec1_coll"
  by auto

lemma op_image_flow1_of_vec1_coll[autoref_rules]:
  "(map (\<lambda>x. (take E x, Some (drop E x))), op_image_flow1_of_vec1_coll::_\<Rightarrow>'n eucl1 set) \<in> clw_rel appr_rel \<rightarrow> clw_rel appr1_rel"
  if "DIM_precond TYPE('n::enum rvec) E"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
  apply (rule relator_props)
  unfolding op_image_flow1_of_vec1_coll_def op_image_flow1_of_vec1_def[symmetric]
  apply (rule op_image_flow1_of_vec1)
  using that
  by auto
sublocale autoref_op_pat_def op_image_flow1_of_vec1_coll .

schematic_goal vec1reps_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr1_rel"
  shows "(RETURN ?r, vec1reps X) \<in> \<langle>\<langle>clw_rel appr_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding vec1reps_def
  including art
  by (autoref_monadic (plain))
concrete_definition vec1reps_impl for Xi uses vec1reps_impl
lemma vec1reps_impl_refine[autoref_rules]:
  "(\<lambda>x. RETURN (vec1reps_impl x), vec1reps) \<in> clw_rel appr1_rel \<rightarrow> \<langle>\<langle>clw_rel appr_rel\<rangle>option_rel\<rangle>nres_rel"
  using vec1reps_impl.refine by force
sublocale autoref_op_pat_def vec1reps .

abbreviation "intersection_STATE_rel \<equiv>
  (appr1_rel \<times>\<^sub>r \<langle>Id\<rangle>phantom_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
    clw_rel (\<langle>appr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r bool_rel \<times>\<^sub>r bool_rel)"

lemma print_set_impl1[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1 s), print_set1) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto
sublocale autoref_op_pat_def print_set1 .

lemma trace_set1_impl1[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option list_of_appr1 a), trace_set1) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto
sublocale autoref_op_pat_def trace_set1 .

lemma print_set_impl1e[autoref_rules]:
  shows "(\<lambda>a s. printing_fun optns a (list_of_appr1e s), print_set1e) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto
sublocale autoref_op_pat_def print_set1e .
lemma trace_set1_impl1e[autoref_rules]:
  shows "(\<lambda>s a. tracing_fun optns s (map_option (list_of_appr1e) a), trace_set1e) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto
sublocale autoref_op_pat_def trace_set1e .

schematic_goal split_spec_param1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) E"
  assumes [autoref_rules]: "(Xi, X) \<in> appr1_rel"
  notes [autoref_post_simps] = case_prod_eta
  shows "(nres_of (?f), split_spec_param1 (X::'a eucl1 set)) \<in> \<langle>appr1_rel \<times>\<^sub>r appr1_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_spec_param1_def
  including art
  by autoref_monadic
concrete_definition split_spec_param1_impl for Xi uses split_spec_param1_impl
lemmas split_spec_param1_refine[autoref_rules] =
  split_spec_param1_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def split_spec_param1 .

lemma [autoref_op_pat del]: "{} \<equiv> OP op_empty_default" "{} \<equiv> OP op_empty_coll"
  and [autoref_op_pat_def del]: "get_inter p \<equiv> OP (get_inter p)"
  by simp_all

lemma fst_image_c1_info_of_appr:
  "c1_info_invar (DIM('a)) X \<Longrightarrow>
    (fst ` c1_info_of_appr X::'a::executable_euclidean_space set) = eucl_of_list ` (set_of_appr (fst X))"
  apply (auto simp: c1_info_invar_def power2_eq_square image_image flow1_of_list_def
      c1_info_of_appr_def flow1_of_vec1_def eucl_of_list_prod split: option.splits)
  subgoal for a b
    by (rule image_eqI[where x="take DIM('a) b"]) (auto intro!: take_set_of_apprI simp: length_set_of_appr)
  subgoal for a b
    apply (frule set_of_appr_ex_append2[where b=a])
    apply auto
    subgoal for r
      by (rule image_eqI[where x="b@r"])
         (auto intro!: eucl_of_list_eqI dest!: length_set_of_appr)
    done
  done

lemma op_image_fst_colle_impl[autoref_rules]:
  "(map (\<lambda>(_, x, _). x), op_image_fst_colle) \<in> clw_rel appr1e_rel \<rightarrow> clw_rel appr_rel"
  apply (rule fun_relI)
  unfolding appr_rel_br
  apply (rule map_mem_clw_rel_br)
  unfolding appr1_rel_br
  unfolding scaleR2_rel_br
  unfolding clw_rel_br
   apply (auto dest!: brD simp: image_Union split_beta')
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply (auto simp: fst_image_c1_info_of_appr)
   apply (rule bexI) prefer 2 apply assumption
   apply (auto simp: scaleR2_rel_br scaleR2_def image_def c1_info_of_appr_def
      split: option.splits)
  subgoal for a b c d e f g h i
    apply (rule bexI[where x="take DIM('a) i"])
    by (auto intro!: take_set_of_apprI simp: flow1_of_list_def eucl_of_list_prod c1_info_invar_def
        length_set_of_appr)
  subgoal
    by (auto intro!: take_set_of_apprI simp: flow1_of_vec1_def eucl_of_list_prod
        length_set_of_appr c1_info_invar_def)
  done
sublocale autoref_op_pat_def op_image_fst_colle .

lemma is_empty_appr1_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr1_rel \<rightarrow> bool_rel"
  by (auto simp: appr1_rel_internal set_rel_br) (auto simp: appr_rel_br br_def)
sublocale autoref_op_pat_def is_empty .

schematic_goal split_spec_param1e_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::enum rvec) E"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>appr1_rel\<rangle>scaleR2_rel"
  notes [autoref_post_simps] = case_prod_eta
  shows "(nres_of (?f), split_spec_param1e (X::'a eucl1 set)) \<in>
    \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r \<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_spec_param1e_def
  including art
  by autoref_monadic
concrete_definition split_spec_param1e_impl for Xi uses split_spec_param1e_impl
lemmas split_spec_param1e_refine[autoref_rules] =
  split_spec_param1e_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def split_spec_param1e .

schematic_goal reduce_spec1_impl:
  "(nres_of ?r, reduce_spec1 C X) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  if [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
    and [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel" "(Ci, C) \<in> reduce_argument_rel TYPE('b)"
  unfolding reduce_spec1_def
  including art
  by autoref_monadic
concrete_definition reduce_spec1_impl for Ci Xi uses reduce_spec1_impl
lemmas reduce_spec1_impl_refine[autoref_rules] = reduce_spec1_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def reduce_spec1 .

schematic_goal reduce_spec1e_impl:
  "(nres_of ?r, reduce_spec1e C X) \<in> \<langle>\<langle>appr1_rel\<rangle>scaleR2_rel\<rangle>nres_rel"
  if [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
  and [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> \<langle>appr1_rel\<rangle>scaleR2_rel" "(Ci, C) \<in> reduce_argument_rel TYPE('b)"
  unfolding reduce_spec1e_def
  including art
  by autoref_monadic
concrete_definition reduce_spec1e_impl for Ci Xi uses reduce_spec1e_impl
lemmas reduce_spec1e_impl_refine[autoref_rules] =
  reduce_spec1e_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def reduce_spec1e .

lemma eq_spec_impl[autoref_rules]:
  "(\<lambda>a b. RETURN (a = b), eq_spec) \<in> A \<rightarrow> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  if "PREFER single_valued A"
  using that by (auto simp: nres_rel_def single_valued_def)

schematic_goal select_with_inter_impl:
  assumes [relator_props]: "single_valued A" "single_valued P"
  assumes [autoref_rules]: "(ci, c) \<in> clw_rel (\<langle>A, P\<rangle>inter_rel)" "(ai, a) \<in> clw_rel A"
  shows "(RETURN ?r, select_with_inter $ c $ a) \<in> \<langle>clw_rel (\<langle>A, P\<rangle>inter_rel)\<rangle>nres_rel"
  unfolding select_with_inter_def
  including art
  by (autoref_monadic (plain))
concrete_definition select_with_inter_impl for ci ai uses select_with_inter_impl
lemmas [autoref_rules] = select_with_inter_impl.refine[OF PREFER_sv_D PREFER_sv_D]
sublocale autoref_op_pat_def select_with_inter .

schematic_goal choose_step1e_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
    "ncc_precond TYPE('n vec1)"
    "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1e_rel" "(hi, h) \<in> rnv_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of ?r, choose_step1e odo X h) \<in> \<langle>rnv_rel \<times>\<^sub>r appr1_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr1e_rel\<rangle>nres_rel"
  unfolding choose_step1e_def
  including art
  by autoref_monadic
concrete_definition choose_step1e_impl for Xi hi uses choose_step1e_impl
lemmas [autoref_rules] = choose_step1e_impl.refine[autoref_higher_order_rule (1 2 3)]
sublocale autoref_op_pat_def choose_step1e .

lemma pre_split_reduce_impl[autoref_rules]:
  "(\<lambda>ro. RETURN (pre_split_reduce ro), pre_split_reduce_spec) \<in> reach_optns_rel \<rightarrow> \<langle>reduce_argument_rel TYPE('b)\<rangle>nres_rel"
  by (auto simp: pre_split_reduce_spec_def nres_rel_def reduce_argument_rel_def RETURN_RES_refine)

schematic_goal step_split_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1e_rel"
    and [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), step_split odo ro X)\<in>\<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  using assms
  unfolding step_split_def[abs_def]
  including art
  by autoref_monadic
concrete_definition step_split_impl for odoi Xi uses step_split_impl
lemmas [autoref_rules] = step_split_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def step_split .

schematic_goal width_spec_appr1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> appr1_rel"
  shows "(?r, width_spec_appr1 X) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding width_spec_appr1_def
  by autoref_monadic
concrete_definition width_spec_appr1_impl for Xi uses width_spec_appr1_impl
lemmas width_spec_appr1_impl_refine[autoref_rules] =
  width_spec_appr1_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def width_spec_appr1 .

schematic_goal split_under_threshold_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
  assumes [autoref_rules]: "(thi, th) \<in> rnv_rel" "(Xi, X) \<in> clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of ?x, split_under_threshold ro th (X::'n eucl1 set)) \<in> \<langle>clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_under_threshold_def
  by autoref_monadic
concrete_definition split_under_threshold_impl for thi Xi uses split_under_threshold_impl
lemmas [autoref_rules] = split_under_threshold_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def split_under_threshold .

schematic_goal pre_intersection_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]:
    "(Xi, X::'n eucl1 set) \<in> appr1e_rel"
    "(hi, (h::real)) \<in> rnv_rel"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
    "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of ?r, pre_intersection_step odo roptns X h) \<in>
    \<langle>clw_rel (iinfo_rel appr1e_rel) \<times>\<^sub>r clw_rel appr_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>nres_rel"
  unfolding pre_intersection_step_def
  including art
  by autoref_monadic
concrete_definition pre_intersection_step_impl for roptnsi Xi hi uses pre_intersection_step_impl
lemmas [autoref_rules] = pre_intersection_step_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def pre_intersection_step .

schematic_goal subset_spec_plane_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a) E"
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?R, subset_spec_plane X sctn) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_plane_def
  by autoref_monadic
concrete_definition subset_spec_plane_impl for Xi sctni uses subset_spec_plane_impl
lemmas [autoref_rules] = subset_spec_plane_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def subset_spec_plane .

schematic_goal op_eventually_within_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(Si, S) \<in> lvivl_rel"
  shows "(nres_of ?R, op_eventually_within_sctn X sctn S) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding op_eventually_within_sctn_def
  including art
  by autoref_monadic
concrete_definition op_eventually_within_sctn_impl for Xi sctni Si uses op_eventually_within_sctn_impl
lemmas [autoref_rules] = op_eventually_within_sctn_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def op_eventually_within_sctn .

schematic_goal nonzero_component_within_impl:
  "(nres_of ?r, nonzero_component_within odo ivl sctn (PDP::'n eucl1 set)) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
  and [autoref_rules]:
    "(ivli, ivl) \<in> lvivl_rel"
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(PDPi, PDP) \<in> appr1_rel"
    "(odoi, odo) \<in> ode_ops_rel"
  unfolding nonzero_component_within_def
  including art
  by autoref_monadic
concrete_definition nonzero_component_within_impl uses nonzero_component_within_impl
lemmas [autoref_rules] = nonzero_component_within_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def nonzero_component_within .

schematic_goal disjoints_spec_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(Xi, (X::'n::enum rvec set)) \<in> clw_rel appr_rel" "(Yi, (Y::'n rvec set)) \<in> clw_rel lvivl_rel"
  shows "(nres_of ?f, disjoints_spec X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding disjoints_spec_def op_coll_is_empty_def[symmetric]
  including art
  by autoref_monadic
concrete_definition disjoints_spec_impl for Xi Yi uses disjoints_spec_impl
lemmas [autoref_rules] = disjoints_spec_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def disjoints_spec .

schematic_goal do_intersection_body_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(hi, h) \<in> rnv_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel lvivl_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  and [autoref_rules]: "(STATEi, STATE) \<in> intersection_STATE_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl]
  shows "(nres_of ?f, do_intersection_body odo guards ivl sctn h STATE) \<in> \<langle>intersection_STATE_rel\<rangle>nres_rel"
  unfolding do_intersection_body_def
  by autoref_monadic
concrete_definition do_intersection_body_impl for odoi guardsi ivli sctni hi STATEi uses do_intersection_body_impl
lemmas do_intersection_body_impl_refine[autoref_rules] =
  do_intersection_body_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def do_intersection_body .

schematic_goal do_intersection_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(Xi, X) \<in> appr1_rel" "(hi, h) \<in> rnv_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (\<langle>lvivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel)"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl]
  shows "(nres_of ?f, do_intersection odo guards ivl sctn (X::'n eucl1 set) h)\<in>
    \<langle>bool_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r clw_rel appr1_rel \<times>\<^sub>r
      clw_rel (\<langle>appr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding do_intersection_def
  including art
  by autoref_monadic
concrete_definition do_intersection_impl for odoi guardsi ivli sctni Xi hi uses do_intersection_impl
lemmas do_intersection_impl_refine[autoref_rules] =
  do_intersection_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def do_intersection .

schematic_goal tolerate_error1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) dd"
  assumes [autoref_rules]: "(Yi, Y::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(Ei, E) \<in> appr1_rel"
  shows "(nres_of ?r, tolerate_error1 Y E) \<in> \<langle>bool_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding tolerate_error1_def
  including art
  by autoref_monadic
concrete_definition tolerate_error1_impl for dd Yi Ei uses tolerate_error1_impl
lemmas tolerate_error1_refine[autoref_rules] = tolerate_error1_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def tolerate_error1 .

lemma lower_impl[autoref_rules]: "(lower, lower) \<in> Id \<rightarrow> Id"
  and upper_impl[autoref_rules]: "(lower, lower) \<in> Id \<rightarrow> Id"
  by auto

schematic_goal step_adapt_time_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(hi, h) \<in> rnv_rel"
    "(Xi, X::'n eucl1 set) \<in> (appr1e_rel)"
  shows "(nres_of ?f, step_adapt_time odo X h)\<in>\<langle>rnv_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr1e_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding step_adapt_time_def[abs_def]
  including art
  by autoref_monadic
concrete_definition step_adapt_time_impl for Xi hi uses step_adapt_time_impl
lemmas [autoref_rules] = step_adapt_time_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def step_adapt_time .


schematic_goal resolve_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(hi, h) \<in> rnv_rel"
    "(Xi, X::'n eucl1 set) \<in> (appr1e_rel)"
    "(roptnsi, roptns) \<in> reach_optns_rel"
  shows "(nres_of ?f, resolve_step odo roptns X h)\<in>\<langle>rnv_rel \<times>\<^sub>r clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding resolve_step_def[abs_def]
  including art
  by autoref_monadic
concrete_definition resolve_step_impl for roptnsi Xi hi uses resolve_step_impl
lemmas [autoref_rules] = resolve_step_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def resolve_step .

sublocale autoref_op_pat_def fst_safe_coll .

schematic_goal reach_cont_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
  notes [relator_props, autoref_rules_raw] = sv_appr1_rel
  shows "(nres_of (?f::?'f dres), reach_cont odo roptns guards XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_cont_def
  including art
  by autoref_monadic
concrete_definition reach_cont_impl for guardsi XSi uses reach_cont_impl
lemmas reach_cont_ho[autoref_rules] = reach_cont_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def reach_cont .

schematic_goal reach_cont_par_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
  shows "(nres_of (?f::?'f dres), reach_cont_par odo roptns guards XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_cont_par_def
  including art
  by autoref_monadic
concrete_definition reach_cont_par_impl for roptnsi guardsi XSi uses reach_cont_par_impl
lemmas reach_cont_par_impl_refine[autoref_rules] = reach_cont_par_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def reach_cont_par .

schematic_goal subset_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(xi, x::'a set) \<in> iplane_rel lvivl_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subset_iplane_coll x ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_iplane_coll_def
  including art
  by autoref_monadic
concrete_definition subset_iplane_coll_impl uses subset_iplane_coll_impl
lemmas subset_iplane_coll_impl_refine[autoref_rules] = subset_iplane_coll_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def subset_iplane_coll .


schematic_goal subsets_iplane_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(xi, x::'a set set) \<in> \<langle>iplane_rel lvivl_rel\<rangle>list_wset_rel"
  assumes [autoref_rules]: "(icsi, ics) \<in> clw_rel (iplane_rel lvivl_rel)"
  shows "(nres_of ?r, subsets_iplane_coll x ics) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subsets_iplane_coll_def
  including art
  by autoref_monadic
concrete_definition subsets_iplane_coll_impl uses subsets_iplane_coll_impl
lemmas [autoref_rules] = subsets_iplane_coll_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def subsets_iplane_coll .


schematic_goal symstart_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of ?r, symstart_coll $ odo $ symstart $ XS) \<in> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding symstart_coll_def
  including art
  by autoref_monadic
concrete_definition symstart_coll_impl for symstartd XSi uses symstart_coll_impl
lemmas [autoref_rules] = symstart_coll_impl.refine
sublocale autoref_op_pat_def symstart_coll .

schematic_goal reach_cont_symstart_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    "(roptnsi, roptns) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of (?r), reach_cont_symstart $ odo $ roptns $ symstart $ guards $ XS) \<in>
  \<langle>clw_rel appr_rel \<times>\<^sub>r
    clw_rel (\<langle>iplane_rel lvivl_rel::(_ \<times> 'n rvec set)set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reach_cont_symstart_def Let_def
  including art
  by autoref_monadic
concrete_definition reach_cont_symstart_impl for roptnsi symstartd XSi uses reach_cont_symstart_impl
lemmas [autoref_rules] = reach_cont_symstart_impl.refine
sublocale autoref_op_pat_def reach_cont_symstart .

lemma sv_reach_conts_impl_aux:
  "single_valued (clw_rel (iinfo_rel appr1e_rel))" by (auto intro!: relator_props)

schematic_goal reach_conts_impl:
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(XSi, XS) \<in> clw_rel appr1e_rel"
    "(guardsi, guards::'n rvec set) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roptnsi, roptns) \<in> reach_optns_rel"
  notes [simp] = list_wset_rel_finite[OF sv_reach_conts_impl_aux]
    assumes "(trapi, trap) \<in> ghost_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  shows "(nres_of (?f::?'f dres), reach_conts $ odo $ roptns $ symstart $ trap $ guards $ XS)\<in>?R"
  unfolding autoref_tag_defs
  unfolding reach_conts_def
  including art
  by autoref_monadic
concrete_definition reach_conts_impl for odoi guardsi XSi uses reach_conts_impl
lemmas [autoref_rules] = reach_conts_impl.refine
sublocale autoref_op_pat_def reach_conts .

lemma get_sctns_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_sctns) \<in> \<langle>R\<rangle>halfspaces_rel \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel\<rangle>nres_rel"
  by (auto simp: get_sctns_def nres_rel_def halfspaces_rel_def br_def intro!: RETURN_SPEC_refine)
sublocale autoref_op_pat_def get_sctns .

schematic_goal leaves_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes nccp[autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  notes [simp] = ncc_precondD[OF nccp]
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
  assumes [autoref_rules]: "(Xi, X::'n rvec set) \<in> clw_rel appr_rel"
  shows "(nres_of ?r, leaves_halfspace $ odo $ S $ X) \<in> \<langle>\<langle>\<langle>lv_rel\<rangle>sctn_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding leaves_halfspace_def
  including art
  by autoref_monadic
concrete_definition leaves_halfspace_impl for Si Xi uses leaves_halfspace_impl
lemmas [autoref_rules] = leaves_halfspace_impl.refine
sublocale autoref_op_pat_def leaves_halfspace .

schematic_goal poincare_start_on_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes ncc2[autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes ncc2[autoref_rules_raw]: "ncc_precond TYPE('n::enum vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]:
    "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(guardsi, guards) \<in> clw_rel lvivl_rel"
    "(X0i, X0::'n eucl1 set) \<in> clw_rel (appr1e_rel)"
  shows "(nres_of (?f), poincare_start_on $ odo $ guards $ sctn $ X0) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_start_on_def
  including art
  by autoref_monadic
concrete_definition poincare_start_on_impl for guardsi sctni X0i uses poincare_start_on_impl
lemmas [autoref_rules] = poincare_start_on_impl.refine
sublocale autoref_op_pat_def poincare_start_on .

lemma isets_of_iivls[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) ((lv_rel::(_ \<times> 'a::executable_euclidean_space)set) \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. map (\<lambda>((i, s), x). (appr_of_ivl ops i s, x)) [((i,s), x) \<leftarrow> xs. le i s], isets_of_iivls::_\<Rightarrow>'a set)
    \<in> clw_rel (\<langle>lvivl_rel, A\<rangle>inter_rel) \<rightarrow> clw_rel (\<langle>appr_rel, A\<rangle>inter_rel)"
  apply (rule fun_relI)
  using assms
  apply (auto elim!: single_valued_as_brE)
  unfolding appr_rel_br ivl_rel_br clw_rel_br lvivl_rel_br inter_rel_br
  apply (auto simp: br_def set_of_ivl_def)
  subgoal for a b c d e f g
    apply (rule exI[where x=e])
    apply (rule exI[where x=f])
    apply (rule exI[where x=g])
    apply (rule conjI)
    apply (assumption)
    apply (rule conjI)
    subgoal
      using transfer_operations1[where 'a='a, of "eucl_of_list e" "eucl_of_list f" e f]
        le[of e _ f _, OF lv_relI lv_relI]
      by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
    subgoal
      apply (drule bspec, assumption)
      using transfer_operations1[where 'a='a, of "eucl_of_list e" "eucl_of_list f" e f]
        le[of e _ f _, OF lv_relI lv_relI]
      apply (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
      using atLeastAtMost_iff apply blast
      apply (drule order_trans)
       apply assumption apply simp
      done
    done
  subgoal for a b c d e f g
    apply (drule bspec, assumption)
    using transfer_operations1[where 'a='a, of "eucl_of_list d" "eucl_of_list e" d e]
      le[of d _ e _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  subgoal for a b c d e f
    apply (drule bspec, assumption)
    using transfer_operations1[where 'a='a, of "eucl_of_list d" "eucl_of_list e" d e]
      le[of d _ e _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  done
sublocale autoref_op_pat_def isets_of_iivls .

lemma [autoref_op_pat]: "X \<times> UNIV \<equiv> OP op_times_UNIV_coll $ X" by simp

lemma op_times_UNIV_coll_impl[autoref_rules]: "(map (\<lambda>x. (x, None)), op_times_UNIV_coll) \<in> clw_rel appr_rel \<rightarrow> clw_rel appr1_rel"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
    apply (rule relator_props)
  unfolding op_times_UNIV_coll_def op_times_UNIV_def[symmetric]
   apply (rule op_times_UNIV_impl)
  by auto
sublocale autoref_op_pat_def op_times_UNIV_coll .

schematic_goal do_intersection_core_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> iinfo_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and csctns[autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and csctns[autoref_rules]: "(ivli, ivl) \<in> lvivl_rel"
  notes [simp] = list_set_rel_finiteD
  shows "(nres_of ?f, do_intersection_core odo guards ivl sctn X) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding do_intersection_core_def[abs_def]
  including art
  by autoref_monadic
concrete_definition do_intersection_core_impl for guardsi ivli sctni Xi uses do_intersection_core_impl
sublocale autoref_op_pat_def do_intersection_core .

lemmas do_intersection_core_impl_refine[autoref_rules] =
  do_intersection_core_impl.refine[autoref_higher_order_rule(1 2 3)]

lemma finite_ra1eicacacslsbicae1lw: "(xc, x'c) \<in> \<langle>\<langle>rnv_rel, appr1e_rel\<rangle>info_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel
           (\<langle>appr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r
          clw_rel appr1e_rel\<rangle>list_wset_rel \<Longrightarrow> finite x'c"
  for x'c::"('n::enum eucl1 set * 'n eucl1 set * 'n eucl1 set * 'n rvec set * 'n eucl1 set) set"
  apply (rule list_wset_rel_finite)
  by (auto intro!: relator_props)

schematic_goal do_intersection_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE((real, 'n::enum) vec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(Xi, X::'n eucl1 set) \<in> clw_rel (iinfo_rel appr1e_rel)"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and csctns[autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and csctns[autoref_rules]: "(ivli, ivl) \<in> lvivl_rel"
  notes [simp] = finite_ra1eicacacslsbicae1lw[where 'n='n]
  shows "(nres_of ?f, do_intersection_coll odo guards ivl sctn X) \<in>
      \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding do_intersection_coll_def[abs_def]
  including art
  by autoref_monadic
concrete_definition do_intersection_coll_impl for guardsi ivli sctni Xi uses do_intersection_coll_impl
lemmas [autoref_rules] = do_intersection_coll_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def do_intersection_coll .

schematic_goal op_enlarge_ivl_sctn_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(ivli, ivl::'a set) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel" "(di, d) \<in> rnv_rel"
  shows "(nres_of ?R, op_enlarge_ivl_sctn $ ivl $ sctn $ d) \<in> \<langle>lvivl_rel\<rangle>nres_rel"
  unfolding op_enlarge_ivl_sctn_def
  including art
  by autoref_monadic
concrete_definition op_enlarge_ivl_sctn_impl for ivli sctni di uses op_enlarge_ivl_sctn_impl
lemmas [autoref_rules] = op_enlarge_ivl_sctn_impl.refine
sublocale autoref_op_pat_def op_enlarge_ivl_sctn .

schematic_goal resolve_ivlplanes_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS::('n rvec set \<times> 'n eucl1 set) set) \<in> \<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of ?r, resolve_ivlplanes odo guards ivlplanes XS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r clw_rel (isbelows_rel appr_rel)\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding resolve_ivlplanes_def
  including art
  by autoref_monadic
concrete_definition resolve_ivlplanes_impl for guardsi ivlplanesi XSi uses resolve_ivlplanes_impl
lemmas [autoref_rules] = resolve_ivlplanes_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def resolve_ivlplanes .

schematic_goal poincare_onto_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(CXSi, CXS::'n rvec set) \<in> clw_rel appr_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "((), trap) \<in> ghost_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of ?r, poincare_onto $ odo $ ro $ symstart $ trap $ guards $ ivlplanes $ XS $ CXS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
      \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_def
  including art
  by autoref_monadic
concrete_definition poincare_onto_impl for odoi roi symstarti guardsi ivlplanesi XSi uses poincare_onto_impl
lemmas [autoref_rules] = poincare_onto_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def poincare_onto .

schematic_goal empty_remainders_impl:
  assumes [autoref_rules]:
    "(PSi, PS) \<in> \<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
            \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel"
  shows "(nres_of ?r, empty_remainders PS) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding empty_remainders_def
  including art
  by autoref_monadic
concrete_definition empty_remainders_impl uses empty_remainders_impl

lemmas empty_remainders_impl_refine[autoref_rules] = empty_remainders_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def empty_remainders .

lemma empty_trap_impl[autoref_rules]: "((), empty_trap) \<in> ghost_rel"
  by (auto intro!: ghost_relI)
sublocale autoref_op_pat_def empty_trap .

lemma empty_symstart_impl:\<comment> \<open>why this? \<close>
  "((\<lambda>x. nres_of (dRETURN ([], [x]))), empty_symstart) \<in>
    appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding empty_symstart_def
  using mk_coll[unfolded autoref_tag_defs, OF sv_appr1e_rel[OF sv_appr1_rel], param_fo]
  by (auto intro!: nres_relI simp:)
lemma empty_symstart_nres_rel[autoref_rules]:
  "((\<lambda>x. RETURN ([], [x])), empty_symstart::'n::enum eucl1 set\<Rightarrow>_) \<in>
    appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  using mk_coll[OF PREFER_I[of single_valued, OF sv_appr1e_rel[OF sv_appr1_rel]], param_fo, of x y for x and y::"'n eucl1 set"]
  by (auto simp: mk_coll_def[abs_def] nres_rel_def)
sublocale autoref_op_pat_def empty_symstart .
lemma empty_symstart_dres_nres_rel:
  "((\<lambda>x. dRETURN ([], [x])), empty_symstart::'n::enum eucl1 set\<Rightarrow>_) \<in>
    (appr1e_rel) \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
  using mk_coll[OF PREFER_I[of single_valued, OF sv_appr1e_rel[OF sv_appr1_rel]], param_fo, of x y for x and y::"'n eucl1 set"]
  by (auto simp: mk_coll_def[abs_def] dres_nres_rel_def)


schematic_goal poincare_onto_empty_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
  assumes [autoref_rules]: "(CXSi, CXS::'n rvec set) \<in> clw_rel appr_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  notes [intro, simp] = list_set_rel_finiteD
  shows "(nres_of (?r), poincare_onto_empty odo ro guards ivlplanes XS CXS) \<in>
    \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
      \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_empty_def
  including art
  apply (rule autoref_monadicI)
   apply (autoref phases: id_op rel_inf fix_rel)\<comment> \<open>TODO: what is going wrong here?\<close>
  apply (simp only: autoref_tag_defs)
   apply (rule poincare_onto_impl.refine[unfolded autoref_tag_defs])
            apply fact+
     apply (rule ghost_relI)
    apply (rule empty_symstart_impl)
   apply refine_transfer
  apply refine_transfer
  done

concrete_definition poincare_onto_empty_impl for guardsi XSi CXSi uses poincare_onto_empty_impl
lemmas [autoref_rules] = poincare_onto_empty_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def poincare_onto_empty .

lemma sv_thingy: "single_valued (clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
          clw_rel
           (\<langle>appr_rel,
            \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r
          clw_rel appr_rel)"
  by (intro relator_props)

schematic_goal poincare_onto2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> clw_rel (iplane_rel lvivl_rel)"
    and osctns[autoref_rules]: "(ivlplanesi, ivlplanes) \<in> clw_rel (iplane_rel lvivl_rel)"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD list_wset_rel_finite[OF sv_thingy]
  shows "(nres_of (?r), poincare_onto2 $ odo $ ro $ symstart $ trap $ guards $ ivlplanes $ XS) \<in>
    \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto2_def
    including art
  by autoref_monadic
concrete_definition poincare_onto2_impl for odoi guardsi XSi uses poincare_onto2_impl
lemmas [autoref_rules] = poincare_onto2_impl.refine
sublocale autoref_op_pat_def poincare_onto2 .

schematic_goal width_spec_ivl_impl:
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel" "(xi, x) \<in> lvivl_rel"
  shows "(RETURN ?r, width_spec_ivl M x) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding width_spec_ivl_def
  including art
  by (autoref_monadic (plain))
concrete_definition width_spec_ivl_impl for Mi xi uses width_spec_ivl_impl

lemmas width_spec_ivl_impl_refine[autoref_rules]
  = width_spec_ivl_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def width_spec_ivl .

schematic_goal partition_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(xsi, xs::'a set)\<in> clw_rel lvivl_rel" "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), partition_ivl ro xs)\<in>\<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding partition_ivl_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_ivl_impl for roi xsi uses partition_ivl_impl
lemmas [autoref_rules] = partition_ivl_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def partition_ivl .

schematic_goal vec1repse_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr1e_rel"
  shows "(nres_of ?r, vec1repse X) \<in> \<langle>\<langle>clw_rel appre_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding vec1repse_def
  including art
  by autoref_monadic
concrete_definition vec1repse_impl for Xi uses vec1repse_impl
lemmas vec1repse_impl_refine[autoref_rules] = vec1repse_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def vec1repse .

schematic_goal scaleR2_rep1_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(Yi, Y::'n vec1 set) \<in> appre_rel"
  shows "(nres_of ?r, scaleR2_rep1 Y) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding scaleR2_rep1_def
  including art
  by autoref_monadic
concrete_definition scaleR2_rep1_impl uses scaleR2_rep1_impl
lemmas [autoref_rules] = scaleR2_rep1_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def scaleR2_rep1 .

schematic_goal ivlse_of_setse_impl:
  "(nres_of ?r, ivlse_of_setse X) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  if [autoref_rules_raw]:"DIM_precond TYPE('n::enum rvec) E"
    and [autoref_rules]: "(Xi, X::'n vec1 set) \<in> clw_rel (appre_rel)"
  unfolding ivlse_of_setse_def
  including art
  by autoref_monadic
concrete_definition ivlse_of_setse_impl uses ivlse_of_setse_impl
lemmas [autoref_rules] = ivlse_of_setse_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def ivlse_of_setse .

schematic_goal setse_of_ivlse_impl:
  "(nres_of ?r, setse_of_ivlse X) \<in> \<langle>clw_rel (appre_rel)\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X) \<in> clw_rel elvivl_rel"
  unfolding setse_of_ivlse_def
  including art
  by autoref_monadic
concrete_definition setse_of_ivlse_impl uses setse_of_ivlse_impl
lemmas setse_of_ivlse_impl_refine[autoref_rules] =
  setse_of_ivlse_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def setse_of_ivlse .

lemma op_image_flow1_of_vec1_colle[autoref_rules]:
  "(map (\<lambda>(lu, x). (lu, (take E x, Some (drop E x)))), op_image_flow1_of_vec1_colle::_\<Rightarrow>'n eucl1 set) \<in> clw_rel appre_rel \<rightarrow> clw_rel appr1e_rel"
  if "DIM_precond TYPE('n::enum rvec) E"
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)
     apply (rule relator_props)
    apply (rule relator_props)
    apply (rule relator_props)
    apply (rule lift_scaleR2)
  unfolding op_image_flow1_of_vec1_colle_def op_image_flow1_of_vec1_coll_def op_image_flow1_of_vec1_def[symmetric]
    apply (rule op_image_flow1_of_vec1)
  using that
  subgoal by force
  subgoal for l u x
    unfolding op_image_flow1_of_vec1_def flow1_of_vec1_def scaleR2_def
    apply (auto simp: image_def vimage_def)
    subgoal for a b c d e
      apply (rule exI[where x="c *\<^sub>R e"])
      apply (auto simp: blinfun_of_vmatrix_scaleR)
      apply (rule exI[where x="c"])
      apply auto
      apply (rule bexI) prefer 2 apply assumption
      apply auto
      done
    subgoal for a b c d e
      apply (rule exI[where x="c"])
      apply (auto simp: blinfun_of_vmatrix_scaleR)
      apply (rule exI[where x="blinfun_of_vmatrix e"])
      apply auto
      apply (rule bexI) prefer 2 apply assumption
      apply auto
      done
    done
  subgoal by auto
  done
sublocale autoref_op_pat_def op_image_flow1_of_vec1_colle .

schematic_goal okay_granularity_impl:
  assumes [autoref_rules]: "(ivli,ivl::'n::enum vec1 set)\<in> lvivl_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of ?f, okay_granularity ro ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding okay_granularity_def[abs_def]
  including art
  by autoref_monadic
concrete_definition okay_granularity_impl for roi ivli uses okay_granularity_impl
lemmas [autoref_rules] = okay_granularity_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def okay_granularity .

lemma le_post_inter_granularity_op[autoref_rules]:
  "(\<lambda>roi (ls, us). RETURN (width_appr ops optns (appr_of_ivl ops ls us) \<le> post_inter_granularity roi),
    (le_post_inter_granularity_op::_\<Rightarrow>'a::executable_euclidean_space set\<Rightarrow>_)) \<in>
    (reach_optns_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel)"
  by (auto simp: nres_rel_def le_post_inter_granularity_op_def)
sublocale autoref_op_pat_def le_post_inter_granularity_op .

schematic_goal partition_set_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(xsi,xs::'n eucl1 set)\<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), partition_set ro xs) \<in> \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding partition_set_def
  including art
  by autoref_monadic

concrete_definition partition_set_impl for roi xsi uses partition_set_impl
lemmas [autoref_rules] = partition_set_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def partition_set .

schematic_goal partition_sets_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(xsi,xs::(bool \<times> 'n eucl1 set \<times> _)set)\<in>
    \<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel
              \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  shows "(nres_of (?f), partition_sets ro xs)\<in>\<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding partition_sets_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_sets_impl for roi xsi uses partition_sets_impl
lemmas [autoref_rules] = partition_sets_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def partition_sets .

lemma [autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [x] \<Rightarrow> RETURN x | _ \<Rightarrow> SUCCEED, singleton_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  using assms
  by (auto simp: nres_rel_def singleton_spec_def list_wset_rel_def set_rel_br
      split: list.splits elim!: single_valued_as_brE dest!: brD
      intro!: RETURN_SPEC_refine brI)
sublocale autoref_op_pat_def singleton_spec .

lemma closed_ivl_prod8_list_rel:
  assumes "(xl, x'l)
       \<in> \<langle>bool_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          clw_rel appr1e_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>ivl_rel \<times>\<^sub>r
          \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r clw_rel (\<langle>appr_rel, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel"
  shows "(\<forall>(b, X, PS1, PS2, R, ivl, sctn, CX, CXS)\<in>x'l. closed ivl)"
  using assms
  unfolding list_wset_rel_def set_rel_sv[OF single_valued_Id_arbitrary_interface]
  apply (subst (asm) set_rel_sv)
  subgoal
    by (auto simp: Id_arbitrary_interface_def intro!: relator_props intro: single_valuedI)
  by (auto simp: Id_arbitrary_interface_def)

lemma
  poincare_onto_series_rec_list_eq:\<comment> \<open>TODO: here is a problem if interrupt gets uncurried, too\<close>
  "poincare_onto_series odo interrupt trap guards XS ivl sctn ro = rec_list
      (\<lambda>(((((trap), XS0), ivl), sctn), ro).
          let guard0 = mk_coll (mk_inter ivl (plane_of sctn))
          in ASSUME (closed guard0) \<bind>
             (\<lambda>_. (poincare_onto2 odo (ro ::: reach_optns_rel) (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap
                    (op_empty_coll ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel)) guard0 XS0 :::
                   \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel) \<bind>
                  (\<lambda>(XS1).
                      singleton_spec XS1 \<bind>
                      (\<lambda>(b, X, PS1, PS2, R, ivl', sctn', CX, CXS). CHECKs ''poincare_onto_series: last return!'' (ivl' = ivl \<and> sctn' = sctn) \<bind> (\<lambda>_. RETURN PS2)))))
      (\<lambda>x xs rr (((((trap), XS0), ivl), sctn), ro0).
          case x of
          (guard, ro) \<Rightarrow>
            ASSUME (closed ivl) \<bind> 
            (\<lambda>_. let guard0 = mk_coll (mk_inter ivl (plane_of sctn))
                 in ASSUME (closed guard0) \<bind>
                 (\<lambda>_. ASSUME (\<forall>(guard, ro)\<in>set (x # xs). closed guard) \<bind>
                      (\<lambda>_. let guardset = \<Union>(guard, ro)\<in>set ((guard0, ro0) # xs). guard
                           in (poincare_onto2 odo ro (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (guardset ::: clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel))
                                guard XS0 :::
                               \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel) \<bind>
                              (\<lambda>(XS1).
                                  ASSUME (\<forall>(b, X, PS, PS2, R, ivl, sctn, CX, CXS)\<in>XS1. closed ivl) \<bind>
                                  (\<lambda>_.
                                    partition_sets ro XS1 \<bind>
                                    (\<lambda>XS2. fst_safe_colle odo XS2 \<bind> (\<lambda>_. rr (((((trap), XS2), ivl), sctn), ro0 ::: reach_optns_rel) \<bind> RETURN))))))))
      guards (((((trap), XS), ivl), sctn), ro)"
  by (induction guards arbitrary: XS ivl sctn ro) (auto simp: split_beta' split: prod.splits)

schematic_goal poincare_onto_series_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS::'n eucl1 set) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel" "(ivli, ivl) \<in> lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_prod3_list_rel closed_clw_rel_iplane_rel
    closed_ivl_prod8_list_rel
  notes [autoref_rules_raw] = ghost_relI[of x for x::"'n eucl1 set"]
  shows "(nres_of ?r, poincare_onto_series $ odo $ symstart $ trap $ guards $ XS $ ivl $ sctn $ ro) \<in> \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_series_rec_list_eq
  including art
  apply autoref_monadic
  apply (rule ghost_relI)
  apply (autoref phases: trans)
  apply (autoref phases: trans)
  apply (rule ghost_relI)
  apply (autoref phases: trans)
  apply (autoref phases: trans)
  apply simp
  apply (autoref phases: trans)
    apply (autoref phases: trans)
   apply simp
  apply (refine_transfer)
  done

concrete_definition poincare_onto_series_impl for symstartd guardsi XSi ivli sctni roi uses poincare_onto_series_impl
lemmas [autoref_rules] = poincare_onto_series_impl.refine
sublocale autoref_op_pat_def poincare_onto_series .

schematic_goal poincare_onto_from_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r, poincare_onto_from $ odo $ symstart $ trap $ S $ guards $ ivl $ sctn $ ro $ XS) \<in>
    \<langle>clw_rel appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_from_def
  including art
  by autoref_monadic

concrete_definition poincare_onto_from_impl for symstartd Si guardsi ivli sctni roi XSi uses poincare_onto_from_impl
lemmas [autoref_rules] = poincare_onto_from_impl.refine
sublocale autoref_op_pat_def poincare_onto_from .

schematic_goal subset_spec1_impl:
  "(nres_of ?r, subset_spec1 R P dP) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(Ri, R) \<in> appr1_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  unfolding subset_spec1_def
  including art
  by autoref_monadic
lemmas [autoref_rules] = subset_spec1_impl[autoref_higher_order_rule]
sublocale autoref_op_pat_def subset_spec1 .

schematic_goal subset_spec1_collc:
  "(nres_of (?f), subset_spec1_coll R P dP) \<in> \<langle>bool_rel\<rangle>nres_rel"
  if [autoref_rules]:
    "(Ri, R) \<in> clw_rel appr1_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  unfolding subset_spec1_coll_def
  including art
  by autoref_monadic
concrete_definition subset_spec1_collc for Ri Pimpl dPi uses subset_spec1_collc
lemmas subset_spec1_collc_refine[autoref_rules] = subset_spec1_collc.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def subset_spec1_coll .

schematic_goal one_step_until_time_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(phi, ph) \<in> bool_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  notes [autoref_tyrel] = ty_REL[where 'a="real" and R="Id"]
  shows "(nres_of ?f, one_step_until_time odo X0 ph t1)\<in>\<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding one_step_until_time_def[abs_def]
  including art
  by autoref_monadic
concrete_definition one_step_until_time_impl for odoi X0i phi t1i uses one_step_until_time_impl
lemmas one_step_until_time_impl_refine[autoref_rules] = one_step_until_time_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def one_step_until_time .

schematic_goal ivl_of_appr1_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules]: "(Xi, X::'n::enum rvec set) \<in> clw_rel appr_rel"
  shows "(nres_of ?r, ivl_of_eucl_coll X) \<in> \<langle>appr1_rel\<rangle>nres_rel"
  unfolding ivl_of_eucl_coll_def
  by autoref_monadic
concrete_definition ivl_of_appr1_coll_impl uses ivl_of_appr1_coll_impl
sublocale autoref_op_pat_def ivl_of_eucl_coll .
lemmas ivl_of_appr1_coll_impl_refine[autoref_rules] =
  ivl_of_appr1_coll_impl.refine[autoref_higher_order_rule(1)]

schematic_goal one_step_until_time_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(phi, ph) \<in> bool_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  assumes [autoref_rules]: "(t2i, t2) \<in> rnv_rel"
  shows "(nres_of ?r, one_step_until_time_ivl odo X0 ph t1 t2) \<in> \<langle>appr1e_rel \<times>\<^sub>r \<langle>clw_rel appr_rel\<rangle>phantom_rel\<rangle>nres_rel"
  unfolding one_step_until_time_ivl_def
  including art
  by autoref_monadic
concrete_definition one_step_until_time_ivl_impl for X0i phi t1i t2i uses one_step_until_time_ivl_impl
lemmas [autoref_rules] = one_step_until_time_ivl_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def one_step_until_time_ivl .


schematic_goal poincare_onto_from_in_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and [autoref_rules]: "(Si, S) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
  assumes [autoref_rules]: "(symstarti, symstart::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres)
    \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
  assumes [unfolded autoref_tag_defs, refine_transfer]: "\<And>X. TRANSFER (nres_of (symstartd X) \<le> symstarti X)"
    and [autoref_rules]: "((), trap) \<in> ghost_rel"
    "(Pimpl, P) \<in> lvivl_rel"
    "(dPi, dP) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r, poincare_onto_from_in_ivl
      $ odo $ symstart $ trap $ S $ guards $ ivl $ sctn $ ro $ XS $ P $ dP) \<in>
    \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_from_in_ivl_def
  including art
  by autoref_monadic

concrete_definition poincare_onto_from_in_ivl_impl for E odoi symstartd Si guardsi ivli sctni roi XSi Pimpl dPi uses poincare_onto_from_in_ivl_impl
lemmas [autoref_rules] = poincare_onto_from_in_ivl_impl.refine
sublocale autoref_op_pat_def poincare_onto_from_in_ivl .

lemma TRANSFER_I: "x \<Longrightarrow> TRANSFER x"
  by simp

lemma dres_nres_rel_nres_relD: "(symstartd, symstart) \<in> A \<rightarrow> \<langle>B\<rangle>dres_nres_rel \<Longrightarrow> (\<lambda>x. nres_of (symstartd x), symstart) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
  by (auto simp: dres_nres_rel_def nres_rel_def dest!: fun_relD)

lemma c1_info_of_apprsI:
  assumes "(b, a) \<in> clw_rel appr1_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_apprs b"
  using assms
  by (auto simp: appr1_rel_br clw_rel_br c1_info_of_apprs_def dest!: brD)

lemma clw_rel_appr1_relI:
  assumes "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invar CARD('n::enum) X"
  shows "(XS, c1_info_of_apprs XS::('n rvec\<times>_)set) \<in> clw_rel appr1_rel"
  by (auto simp: appr1_rel_br clw_rel_br c1_info_of_apprs_def intro!: brI assms)

lemma c1_info_of_appr'I:
  assumes "(b, a) \<in> \<langle>clw_rel appr1_rel\<rangle>phantom_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appr' b"
  using assms
  by (auto simp add: c1_info_of_appr'_def intro!: c1_info_of_apprsI split: option.splits)

lemma appr1e_relI:
  assumes "c1_info_invare CARD('n::enum) X0i"
  shows "(X0i, c1_info_of_appre X0i::'n eucl1 set) \<in> appr1e_rel"
  using assms
  apply (cases X0i)
  apply (auto simp: scaleR2_rel_def c1_info_of_appre_def c1_info_invare_def)
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (rule appr1_relI)
    apply (auto simp: vimage_def intro!: brI)
   apply (metis ereal_dense2 less_imp_le)
    apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (rule appr1_relI)
   apply (auto simp: vimage_def intro!: brI)
  by (metis basic_trans_rules(23) ereal_cases ereal_less_eq(1) ereal_top order_eq_refl)

lemma c1_info_of_apprI:
  assumes "(b, a) \<in> appr1_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appr b"
  using assms
  apply (auto simp add: c1_info_of_appr_def c1_info_invar_def appr1_rel_internal appr_rel_def lv_rel_def
      set_rel_br
      dest!: brD
      split: option.splits)
   apply (auto simp add:  appr_rell_internal dest!: brD)
  done

lemma c1_info_of_appreI:
  assumes "(lub, a) \<in> appr1e_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_appre lub"
  using assms
  apply (auto simp add: scaleR2_def c1_info_of_appre_def image_def vimage_def scaleR2_rel_def
      dest!: brD
      intro!: c1_info_of_apprsI split: option.splits)
  subgoal for a b c d e f g h i
    apply (rule exI[where x=g])
    apply (rule conjI, assumption)+
    apply (rule bexI)
     prefer 2
     apply (rule c1_info_of_apprI) apply assumption
     apply assumption apply simp
    done
  done

lemma c1_info_of_apprseI:
  assumes "(b, a) \<in> clw_rel appr1e_rel"
  assumes "x \<in> a"
  shows "x \<in> c1_info_of_apprse b"
  using assms
  by (force simp: appr1_rel_br scaleR2_rel_br clw_rel_br c1_info_of_appre_def c1_info_of_apprse_def
      dest!: brD)

lemma clw_rel_appr1e_relI:
  assumes "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n::enum) X"
  shows "(XS, c1_info_of_apprse XS::('n rvec\<times>_)set) \<in> clw_rel appr1e_rel"
  using assms
  apply (auto simp: c1_info_of_apprse_def c1_info_of_appre_def c1_info_invare_def)
  unfolding appr1_rel_br scaleR2_rel_br clw_rel_br
  apply (rule brI)
   apply (auto simp: c1_info_invar_def vimage_def)
  subgoal premises prems for a b c d
    using prems(1)[OF prems(2)]
    by (cases a; cases b) auto
  done

schematic_goal one_step_until_time_ivl_in_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(X0i, X0::'n eucl1 set) \<in> appr1e_rel"
  assumes [autoref_rules]: "(t1i, t1) \<in> rnv_rel"
  assumes [autoref_rules]: "(t2i, t2) \<in> rnv_rel"
      "(Ri, R) \<in> lvivl_rel"
      "(dRi, dR) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  shows "(nres_of ?r, one_step_until_time_ivl_in_ivl odo X0 t1 t2 R dR) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding one_step_until_time_ivl_in_ivl_def
  including art
  by autoref_monadic
concrete_definition one_step_until_time_ivl_in_ivl_impl for odoi X0i t1i t2i Ri dRi
  uses one_step_until_time_ivl_in_ivl_impl
lemmas one_step_until_time_ivl_in_ivl_impl_refine[autoref_rules] =
  one_step_until_time_ivl_in_ivl_impl.refine[autoref_higher_order_rule(1 2 3)]
sublocale autoref_op_pat_def one_step_until_time_ivl_in_ivl .

schematic_goal poincare_onto_in_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('n::enum rvec) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n::enum rvec)"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('n vec1)"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel appr1e_rel"
    and osctns[autoref_rules]: "(guardsi, guards) \<in> \<langle>clw_rel (iplane_rel lvivl_rel)\<times>\<^sub>rreach_optns_rel\<rangle>list_rel"
    and civl[autoref_rules]: "(ivli, ivl::'n rvec set) \<in> lvivl_rel"
    and csctns[autoref_rules]: "(sctni, sctn::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    and [autoref_rules]: "(roi, ro) \<in> reach_optns_rel"
      "(Pimpl, P::'n rvec set) \<in> lvivl_rel"
      "(dPi, dP:: ((real, 'n) vec, 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>(default_rel UNIV)"
  notes [intro, simp] = list_set_rel_finiteD closed_ivl_rel[OF civl] closed_ivl_prod3_list_rel
  shows "(nres_of ?r,
    poincare_onto_in_ivl odo guards ivl sctn ro XS P dP) \<in>
    \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding poincare_onto_in_ivl_def
  including art
  apply (rule autoref_monadicI)
   apply (autoref phases: id_op rel_inf fix_rel)
   apply (autoref_trans_step)
    apply (autoref_trans_step)
     apply (autoref_trans_step)
    apply (simp only: autoref_tag_defs)
    apply (rule poincare_onto_series_impl.refine[unfolded autoref_tag_defs])\<comment> \<open>TODO: why?\<close>
               apply fact+
      apply (rule empty_symstart_impl)
     apply refine_transfer
    apply (rule ghost_relI)
   apply (autoref phases: trans)
  unfolding autoref_tag_defs
  by refine_transfer

concrete_definition poincare_onto_in_ivl_impl for E odoi guardsi ivli sctni roi XSi Pimpl dPi
  uses poincare_onto_in_ivl_impl
lemmas [autoref_rules] = poincare_onto_in_ivl_impl.refine[autoref_higher_order_rule(1 2 3)]


subsection \<open>Main (executable) interfaces to the ODE solver, with initialization\<close>

definition "carries_c1 = Not o Option.is_none o (snd o snd)"

definition "solves_poincare_map odo symstart S guards ivli sctni roi XS P dP \<longleftrightarrow>
  poincare_onto_from_in_ivl_impl (D odo) (init_ode_ops True (carries_c1 (hd XS)) odo) symstart S guards ivli sctni
    roi XS P dP = dRETURN True"

definition "solves_poincare_map' odo S = solves_poincare_map odo (\<lambda>x. dRETURN ([], [x])) [S]"

definition "one_step_until_time_ivl_in_ivl_check odo X t0 t1 Ri dRi \<longleftrightarrow>
  one_step_until_time_ivl_in_ivl_impl (D odo) (init_ode_ops True (carries_c1 X) odo) X t0 t1 Ri dRi = dRETURN True"

definition "solves_poincare_map_onto odo guards ivli sctni roi XS P dP \<longleftrightarrow>
  poincare_onto_in_ivl_impl (D odo) (init_ode_ops True (carries_c1 (hd XS)) odo) guards ivli sctni roi XS P dP = dRETURN True"

end

context approximate_sets begin

lemma c1_info_of_appre_c0_I:
  "(x, d) \<in> c1_info_of_appre ((1, 1), X0, None)"
  if "list_of_eucl x \<in> set_of_appr X0"
  using that
  by (force simp: c1_info_of_appre_def c1_info_of_appr_def)

lemma lvivl'_invar_None[simp]: "lvivl'_invar n None"
  by (auto simp: lvivl'_invar_def)

lemma c1_info_invar_None: "c1_info_invar n (u, None) \<longleftrightarrow> length u = n"
  by (auto simp: c1_info_invar_def)

lemma c1_info_invare_None: "c1_info_invare n ((l, u), x, None) \<longleftrightarrow>((l < u \<or> -\<infinity> < l \<and> l \<le> u \<and> u < \<infinity>) \<and> length x = n)"
  by (auto simp: c1_info_invare_def Let_def c1_info_invar_None)

end

end