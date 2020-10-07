theory Concrete_Rigorous_Numerics
  imports
    Abstract_Rigorous_Numerics
begin

context includes autoref_syntax begin

lemma [autoref_rules]:
  "(slp_of_fas, slp_of_fas) \<in> fas_rel \<rightarrow> slp_rel"
  "(Norm, Norm) \<in> fas_rel \<rightarrow> Id"
  by auto

lemma [autoref_rules]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> Id"
  by auto

lemma [autoref_rules]:
  "(floatarith.Var, floatarith.Var) \<in> nat_rel \<rightarrow> Id"
  "(slp_of_fas, slp_of_fas) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  "(fold_const_fa, fold_const_fa) \<in> Id \<rightarrow> Id"
  "(open_form, open_form) \<in> Id \<rightarrow> bool_rel"
  "(max_Var_floatariths, max_Var_floatariths) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel"
  "(max_Var_form, max_Var_form) \<in> Id \<rightarrow> nat_rel"
  "(length, length) \<in> \<langle>A\<rangle>list_rel \<rightarrow> nat_rel"
  by (auto simp: list_rel_imp_same_length)

end

context approximate_sets begin

lemma prod_rel_relcomp_distr: "(R \<times>\<^sub>r S) O (T \<times>\<^sub>r U) = (R O T) \<times>\<^sub>r (S O U)"
  by (auto simp: prod_rel_def)

lemma appr_relp_comp: "appr_rell O \<langle>lv_rel\<rangle>set_rel \<subseteq> appr_rel"
  "appr_rel \<subseteq> appr_rell O \<langle>lv_rel\<rangle>set_rel"
  by (auto simp: appr_rel_def)

lemma rnv_rel_comp2:
  "rnv_rel \<subseteq> rnv_rel O rnv_rel"
  "rnv_rel O rnv_rel \<subseteq> rnv_rel"
  by auto

lemma rl_comp_lv: "rl_rel O lv_rel \<subseteq> lv_rel"
  "lv_rel \<subseteq> rl_rel O lv_rel"
  by auto

lemmas rel_lemmas =
  fun_rel_comp_dist[THEN order_trans]
  fun_rel_mono nres_rel_comp[THEN eq_refl, THEN order_trans]
  nres_rel_mono prod_rel_mono prod_rel_relcomp_distr[THEN eq_refl, THEN order_trans]
  appr_relp_comp
  rnv_rel_comp2
  rl_comp_lv
  sctn_rel

lemma width_spec_width_spec: "(width_spec, width_spec) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: width_spec_def nres_relI)

lemma [autoref_itype]:
  "width_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Inf_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "Sup_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_nres"
  "inter_sctn_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>B\<rangle>\<^sub>ii_sctn \<rightarrow>\<^sub>i \<langle>C\<rangle>\<^sub>ii_nres"
  "split_spec ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "split_spec_param ::\<^sub>i i_nat \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i \<langle>\<langle>B, B\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "Inf_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  "Sup_inner ::\<^sub>i A \<rightarrow>\<^sub>i B \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_nres"
  by auto

lemma transfer_operations[unfolded comps, autoref_rules]:
  "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
    (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
    (appr_of_ivl ops xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
  "(product_appr ops, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
  "(msum_appr ops, (+)) \<in> appr_rel \<rightarrow> appr_rel \<rightarrow> appr_rel"
  "(RETURN o inf_of_appr ops optns, Inf_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o sup_of_appr ops optns, Sup_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  "(RETURN o2 split_appr ops, split_spec_param) \<in> nat_rel \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel \<times>\<^sub>r appr_rel\<rangle>nres_rel"
  "(RETURN o2 appr_inf_inner ops optns, Inf_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN o2 appr_sup_inner ops optns, Sup_inner) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o2 inter_appr_plane ops optns, inter_sctn_spec) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o2 reduce_appr ops optns, reduce_spec) \<in> reduce_argument_rel TYPE('b) \<rightarrow> appr_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  "(RETURN o width_appr ops optns, width_spec) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  "(nres_of o3 approx_slp_dres ops optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
  subgoal premises prems using transfer_operations_rl(1)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(2)[OF prems] by simp
  subgoal premises prems using transfer_operations_rl(3)[OF prems]
    unfolding appr_rel_def set_plus_def
    apply auto
    apply (drule fun_relD, assumption, drule fun_relD, assumption, rule relcompI, assumption)
    apply (auto simp: set_rel_sv[OF lv_rel_sv])
      apply (rule ImageI)
       apply (rule lv_rel_add[param_fo], assumption, assumption)
      apply force
    subgoal for a b c d e f g
      apply (rule bexI[where x="eucl_of_list f"])
       apply (rule bexI[where x="eucl_of_list g"])
      using lv_rel_add[param_fo, of f "eucl_of_list f", of g "eucl_of_list g::'a"]
      by (auto simp: lv_rel_def br_def subset_iff)
    subgoal
      by (auto simp: lv_rel_def br_def subset_iff)
    done
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(4)[OF 1(1) refl]
    have Is: "(RETURN (inf_of_appr ops optns x), Inf_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('c)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Inf_specs_Inf_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (inf_of_appr ops optns x), Inf_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 x y z)
    from transfer_operations_rl(5)[OF 1(1) refl]
    have Is: "(RETURN (sup_of_appr ops optns x), Sup_specs (length x) y) \<in> \<langle>rl_rel\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('d)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ Sup_specs_Sup_spec[param_fo], OF Is \<open>length x = _\<close> 1(2)]
    have "(RETURN (sup_of_appr ops optns x), Sup_spec z) \<in> \<langle>rl_rel\<rangle>nres_rel O \<langle>lv_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 n x y z)
    from transfer_operations_rl(6)[OF _ 1(1) refl]
    have Is: "(RETURN (split_appr ops n x), split_spec_params (length x) n y) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('e)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ split_spec_params_split_spec_param[param_fo], OF Is \<open>length x = _\<close> IdI 1(2)]
    have "(RETURN (split_appr ops n x), split_spec_param n z) \<in>
        \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(7) Inf_inners_Inf_inner, THEN rev_subsetD] rel_lemmas)
  subgoal
    by (intro relcompI[OF transfer_operations_rl(8) Sup_inners_Sup_inner, THEN rev_subsetD] rel_lemmas)
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 r s x y z)
    from 1 have lens: "length (normal r) = length x"
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    have poslen: "0 < length x"
      using 1
      apply (cases r; cases s)
      apply (auto simp: sctn_rel_def)
      by (auto simp: lv_rel_def set_rel_def br_def appr_rell_internal)
    have rr: "(r, r) \<in> \<langle>rl_rel\<rangle>sctn_rel"
      by (cases r) (auto simp: sctn_rel_def)
    from transfer_operations_rl(9)[OF 1(2) refl lens poslen rr]
    have Is: "(nres_of (inter_appr_plane ops optns x r), inter_sctn_specs (length x) y r) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by (auto dest!: fun_relD)
    from 1 have "length x = DIM('h)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ inter_sctn_specs_inter_sctn_spec[param_fo], OF Is, OF \<open>length x = _\<close> 1(3) 1(1)]
    have "(nres_of (inter_appr_plane ops optns x r), inter_sctn_spec z s) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal apply (auto simp: appr_rel_def)
  proof goal_cases
    case (1 ro x y z)
    from transfer_operations_rl(10)[OF 1(2) refl 1(1)]
    have Is: "(RETURN (reduce_appr ops optns ro x), reduce_specs (length x) () y) \<in> \<langle>appr_rell\<rangle>nres_rel"
      by auto
    from 1 have "length x = DIM('i)"
      unfolding set_rel_sv[OF lv_rel_sv]
      by (auto simp: lv_rel_def br_def appr_rell_internal length_set_of_appr subset_iff)
    from relcompI[OF _ reduce_specs_reduce_spec[param_fo], OF Is \<open>length x = _\<close> IdI 1(3)]
    have "(RETURN (reduce_appr ops optns ro x), reduce_spec () z) \<in> \<langle>appr_rell\<rangle>nres_rel O \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
      by simp
    then show ?case
      by (simp add: nres_rel_comp prod_rel_relcomp_distr comps)
  qed
  subgoal
    by (intro relcompI[OF transfer_operations_rl(11) width_spec_width_spec, THEN rev_subsetD] rel_lemmas)
  subgoal using transfer_operations_rl(12) by auto
  done

lemma approx_slp_spec[autoref_op_pat_def]: "approx_slp_spec fas \<equiv> OP (approx_slp_spec fas)"
  by auto

lemma
  concat_appr:
  assumes "(xsi, xs) \<in> \<langle>appr_rell\<rangle>list_rel"
  shows "(concat_appr ops xsi, concat ` listset xs) \<in> appr_rell"
  using assms
  apply (auto simp: appr_rell_internal br_def)
  subgoal premises prems for xi
  proof -
    have "length xi = length xs" "length xs = length xsi"
      using prems
       by (auto simp: list_rel_def list_all2_iff length_listset)
    then show ?thesis using prems
    proof (induction rule: list_induct3)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs y ys z zs)
      have "(z, set_of_appr z) \<in> appr_rell"
        "(concat_appr ops zs, set_of_appr (concat_appr ops zs)) \<in> appr_rell"
        by (auto simp: appr_rell_internal br_def)
      from transfer_operations(2)[param_fo, OF this]
      have *: "set_of_appr (product_appr ops z (concat_appr ops zs)) =
        (\<lambda>(x, y). x @ y) ` (set_of_appr z \<times> set_of_appr (concat_appr ops zs))"
        by (simp add: appr_rell_internal br_def product_listset_def)
      show ?case
        using Cons
        apply (auto simp: appr_rell_internal *)
        apply (rule image_eqI[where x="(x, concat xs)"])
         by (auto simp: set_Cons_def)
     qed
   qed
   subgoal premises prems for z
   proof -
     have "length xsi = length xs"
       using prems
       by (auto simp: list_rel_def list_all2_iff)
     then show ?thesis
       using prems
     proof (induction arbitrary: z rule: list_induct2 )
       case Nil
       then show ?case by simp
     next
       case (Cons x xs y ys)
       have "(x, set_of_appr x) \<in> appr_rell" "(concat_appr ops xs, set_of_appr (concat_appr ops xs)) \<in> appr_rell"
         by (auto simp: appr_rell_internal br_def)
       from transfer_operations(2)[param_fo, OF this]
       have *: "set_of_appr (product_appr ops x (concat_appr ops xs)) =
          product_listset (set_of_appr x) (set_of_appr (concat_appr ops xs))"
         by (auto simp: appr_rell_internal br_def)
       show ?case using Cons
         apply (auto simp: * product_listset_def list_rel_def set_Cons_def)
         subgoal premises prems for a b
           using prems(2)[OF prems(7)] prems(6)
           apply (auto )
           subgoal for ya
           apply (rule image_eqI[where x="a#ya"])
             by (auto simp: set_Cons_def)
           done
         done
     qed
   qed
   done

lemma op_concat_listset_autoref[autoref_rules]:
  "(concat_appr ops, op_concat_listset) \<in> \<langle>appr_rell\<rangle>list_rel \<rightarrow> appr_rell"
  using concat_appr by force

lemma transfer_operations1[autoref_rules]:
  assumes "SIDE_PRECOND (x \<le> y)" "(xi, x) \<in> lv_rel" "(yi, y) \<in> lv_rel"
  shows "(appr_of_ivl ops xi yi, op_atLeastAtMost_appr $ x $ y) \<in> appr_rel"
proof -
  have "(appr_of_ivl ops xi yi, lv_ivl (list_of_eucl x) (list_of_eucl y)) \<in> appr_rell"
    apply (rule transfer_operations_rl[unfolded autoref_tag_defs])
    using assms lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: lv_rel_def br_def)
  then have "(appr_of_ivl ops xi yi, eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y)::'a set) \<in> appr_rel"
    unfolding appr_rel_br
    using assms[unfolded lv_rel_def]
    using lv_rel_le[param_fo, of xi x yi y]
    by (auto simp: appr_rell_internal br_def appr_rel_br)
       (auto simp: lv_rel_def br_def)
  also have "eucl_of_list ` lv_ivl (list_of_eucl x) (list_of_eucl y) = {x .. y}"
    by (subst eucl_of_list_image_lv_ivl) auto
  finally show ?thesis by simp
qed

lemma appr_of_ivl_point_appr_rel:
  "(appr_of_ivl ops x x, {eucl_of_list x::'a::executable_euclidean_space}) \<in> appr_rel"
  if "length x = DIM('a)"
  using transfer_operations1[OF _ lv_relI lv_relI, OF _ that that]
  by auto

lemmas [autoref_post_simps] = concat.simps append_Nil2 append.simps

lemma is_empty_appr_rel[autoref_rules]:
  "(\<lambda>_. False, is_empty) \<in> appr_rel \<rightarrow> bool_rel"
  by (auto simp: appr_rel_br br_def)

lemma appr_rel_nonempty: "(x, X) \<in> appr_rel \<Longrightarrow> X \<noteq> {}"
  by (auto simp: appr_rel_br br_def)

lemma [autoref_rules]: "(ops, ops) \<in> Id"
  by simp

lemma single_valued_appr_rel[relator_props]:
  "single_valued (appr_rel)"
  by (auto simp: appr_rel_br)

schematic_goal ivl_rep_of_set_impl:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules]: "(ai, X) \<in> appr_rel"
  shows "(RETURN (?f::?'r), op_ivl_rep_of_set X) \<in> ?R"
  unfolding op_ivl_rep_of_set_def including art by (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_impl for  ai uses ivl_rep_of_set_impl
lemma ivl_rep_of_set_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN (ivl_rep_of_set_impl x), op_ivl_rep_of_set) \<in> appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_impl.refine
  by auto

schematic_goal ivl_rep_of_sets_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>appr_rel\<rangle>list_wset_rel"
  notes [refine_transfer] = FORWEAK_LIST_plain.refine
  shows "(RETURN (?f), op_ivl_rep_of_sets a::('a \<times> 'a)nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  unfolding op_ivl_rep_of_sets_def
  by (autoref_monadic(plain))
concrete_definition ivl_rep_of_sets_impl for n ai uses ivl_rep_of_sets_impl
lemma ivl_rep_of_sets_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_sets_impl n ai), op_ivl_rep_of_sets::_\<Rightarrow>('a \<times> 'a)nres) \<in> \<langle>appr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_sets_impl.refine by force

schematic_goal ivl_rep_of_set_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  shows "(RETURN (?f), ivl_rep_of_set_coll a::('a\<times>'a) nres) \<in> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  unfolding ivl_rep_of_set_coll_def
  by (autoref_monadic (plain))
concrete_definition ivl_rep_of_set_coll_impl for n ai uses ivl_rep_of_set_coll_impl
lemma ivl_rep_of_set_coll_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
  (\<lambda>ai. RETURN (ivl_rep_of_set_coll_impl n ai), ivl_rep_of_set_coll::_\<Rightarrow>('a\<times>'a) nres) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel \<times>\<^sub>r lv_rel\<rangle>nres_rel"
  using ivl_rep_of_set_coll_impl.refine by force

schematic_goal ivls_of_sets_impl:
  assumes [autoref_rules]: "(xsi, xs) \<in> clw_rel appr_rel"
  shows "(nres_of (?f), ivls_of_sets $ xs) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding ivls_of_sets_def
  by autoref_monadic
concrete_definition ivls_of_sets_impl for xsi uses ivls_of_sets_impl
lemma ivls_of_set_impl_refine[autoref_rules]:
  "(\<lambda>ai. nres_of (ivls_of_sets_impl ai), ivls_of_sets) \<in> clw_rel appr_rel \<rightarrow> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  using ivls_of_sets_impl.refine by force

lemma card_info[autoref_rules]:
  "((\<lambda>x. RETURN (length x)), card_info) \<in> clw_rel R \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  by (auto simp: card_info_def nres_rel_def)

lemma ivl_to_set[autoref_rules]:
  "(\<lambda>(i, s). if list_all2 (\<le>) i s then [appr_of_ivl ops i s] else [], ivl_to_set::_\<Rightarrow>'a::executable_euclidean_space set) \<in> lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  supply le = lv_rel_le[param_fo]
  apply (clarsimp simp add: ivl_rel_def)
  subgoal premises prems for ls us l u X
    using le[OF \<open>(_, l) \<in> _\<close> \<open>(_, u) \<in> _\<close>] prems transfer_operations1[of l u ls us]
    apply (auto simp: Cons_mem_clw_rel_iff single_valued_appr_rel ivl_rel_def[symmetric] intro!: exI[where x=X])
    subgoal by (auto simp: set_of_ivl_def br_def)
    subgoal using Union_rel_empty by (auto simp: set_of_ivl_def br_def )
    done
  done

lemma sets_of_ivls[autoref_rules]:
  shows "(\<lambda>xs. map (\<lambda>(i, s). appr_of_ivl ops i s) [(i,s) \<leftarrow> xs. list_all2 (\<le>) i s], sets_of_ivls::_\<Rightarrow>'a::executable_euclidean_space set) \<in> clw_rel lvivl_rel \<rightarrow> clw_rel (appr_rel)"
  supply le = lv_rel_le[param_fo]
  apply (rule fun_relI)
  unfolding appr_rel_br ivl_rel_br clw_rel_br lvivl_rel_br
  apply (auto simp: br_def set_of_ivl_def)
  subgoal for a b c d
    apply (rule exI conjI le le[param_fo,THEN IdD, THEN iffD2] lv_relI| assumption | force)+
    using transfer_operations1[where 'a='a, of "eucl_of_list c" "eucl_of_list d" c d]
    apply (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def)
    by (metis (mono_tags, lifting) atLeastAtMost_iff atLeastatMost_empty_iff case_prodD empty_iff)
  subgoal for a b c d
    using transfer_operations1[where 'a='a, of "eucl_of_list b" "eucl_of_list c" b c]
      le[of b _ c _, OF lv_relI lv_relI]
    by (auto simp: appr_rel_br br_def lvivl_rel_br set_of_ivl_def lv_rel_def intro!: bexI)
  done

schematic_goal above_sctn_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, above_sctn $ X $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule above_sctn_nres[THEN nres_rel_trans2]) autoref_monadic
concrete_definition above_sctn_impl for Xi sctni uses above_sctn_impl
lemma above_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (above_sctn_impl ai sctni), above_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using above_sctn_impl.refine by force

schematic_goal below_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition below_sctn_impl for ai sctni uses below_sctn_impl
lemma below_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (below_sctn_impl ai sctni), below_sctn) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_impl.refine by force

schematic_goal sbelow_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, sbelow_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule sbelow_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition sbelow_sctn_impl for ai sctni uses sbelow_sctn_impl
lemma sbelow_sctn_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctn_impl ai sctni), sbelow_sctn) \<in>
    appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctn_impl.refine by force

schematic_goal sbelow_sctns_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns $ a $ sctns) \<in> ?R"
  unfolding autoref_tag_defs
  apply (rule sbelow_sctns_nres[THEN nres_rel_trans2])
  subgoal using list_set_rel_finiteD[of sctnsi sctns "\<langle>lv_rel\<rangle>sctn_rel"] \<open>(sctnsi, sctns) \<in> _\<close> by (simp add: relAPP_def)
  by (autoref_monadic (plain))
concrete_definition sbelow_sctns_impl for ai sctnsi uses sbelow_sctns_impl
lemma sbelow_sctns_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (sbelow_sctns_impl ai sctni), sbelow_sctns) \<in>
    appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_impl.refine by force

schematic_goal intersects_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, op_intersects $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs op_intersects_def
  by (autoref_monadic (plain))
concrete_definition intersects_impl for ai sctni uses intersects_impl
lemma intersects_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_impl ai sctni), op_intersects) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_impl.refine by force

schematic_goal sbelow_sctns_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  shows "(?f::?'r, sbelow_sctns_coll $ a $ sctns) \<in> ?R"
  unfolding sbelow_sctns_coll_def
  by autoref
concrete_definition sbelow_sctns_coll_impl for ai sctnsi uses sbelow_sctns_coll_impl
lemma sbelow_sctns_coll_impl_refine[autoref_rules]:
  "(sbelow_sctns_coll_impl, sbelow_sctns_coll) \<in> clw_rel appr_rel \<rightarrow> sctns_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using sbelow_sctns_coll_impl.refine by force

schematic_goal sbelow_sctns_coll_dres:
  "nres_of ?r \<le> sbelow_sctns_coll_impl a sctns"
  unfolding sbelow_sctns_coll_impl_def
  by refine_transfer
concrete_definition sbelow_sctns_coll_dres for a sctns uses sbelow_sctns_coll_dres
lemmas [refine_transfer] = sbelow_sctns_coll_dres.refine

schematic_goal below_sctn_coll_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, below_sctn_coll $ a $ sctn) \<in> ?R"
  unfolding below_sctn_coll_def by autoref
concrete_definition below_sctn_coll_impl for ai sctni uses below_sctn_coll_impl
lemma below_sctn_coll_impl_refine[autoref_rules]:
  "(below_sctn_coll_impl, below_sctn_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using below_sctn_coll_impl.refine by force
schematic_goal below_sctn_coll_dres:
  "nres_of ?r \<le> below_sctn_coll_impl a sctn"
  unfolding below_sctn_coll_impl_def
  by refine_transfer
concrete_definition below_sctn_coll_dres for a sctn uses below_sctn_coll_dres
lemmas [refine_transfer] = below_sctn_coll_dres.refine

schematic_goal intersects_clw_impl:
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f::?'r, intersects_clw $ a $ sctn) \<in> ?R"
  unfolding intersects_clw_def autoref_tag_defs
  including art
  by (autoref_monadic (plain))
concrete_definition intersects_clw_impl for ai sctni uses intersects_clw_impl
lemma intersects_clw_impl_refine[autoref_rules]:
  "(\<lambda>ai sctni. RETURN (intersects_clw_impl ai sctni), intersects_clw) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using intersects_clw_impl.refine by force

schematic_goal subset_spec_ivlc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> appr_rel"
      "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), op_subset $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding op_subset_def
  by autoref_monadic
concrete_definition subset_spec_ivlc for Xi ivli uses subset_spec_ivlc

lemma subset_spec_ivl_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivlc Xi Yi), op_subset) \<in> appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  for A::"(_ \<times> 'a::executable_euclidean_space set) set"
  using subset_spec_ivlc.refine
  by auto

schematic_goal subset_spec_ivl_collc:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> clw_rel appr_rel"
    "(ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  notes [autoref_post_simps] = Let_def
  shows "(RETURN (?f), subset_spec_coll $ X $ ivl) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_coll_def
  by (autoref_monadic (plain))
concrete_definition subset_spec_ivl_collc for Xi ivli uses subset_spec_ivl_collc
lemma subset_spec_ivl_collc_refine[autoref_rules]:
  "(\<lambda>Xi Yi. RETURN (subset_spec_ivl_collc Xi Yi), subset_spec_coll) \<in> clw_rel appr_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivl_collc.refine by force

schematic_goal project_set_appr:
  fixes b::"'a::executable_euclidean_space" and y
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), op_project_set X b y) \<in> ?R"
  unfolding op_project_set_def
  by autoref_monadic
concrete_definition project_set_appr for Xi bi yi uses project_set_appr
lemma project_set_appr_refine[autoref_rules]:
  "(\<lambda>Xi bi yi. nres_of (project_set_appr Xi bi yi), op_project_set) \<in> appr_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using project_set_appr.refine by force

schematic_goal project_set_clw_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), project_set_clw X b y) \<in> ?R"
  unfolding project_set_clw_def
  including art
  by autoref_monadic
concrete_definition project_set_clw_impl for Xi bi yi uses project_set_clw_impl
lemma project_set_clw_refine[autoref_rules]:
  "(\<lambda>Xi bi yi. nres_of (project_set_clw_impl Xi bi yi), project_set_clw) \<in>
    clw_rel appr_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel \<rightarrow> \<langle>clw_rel appr_rel\<rangle>nres_rel"
  using project_set_clw_impl.refine by force

schematic_goal subset_spec_ivls_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
  shows "(RETURN ?f, subset_spec_ivls X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_def
  by (autoref_monadic (plain))
concrete_definition subset_spec_ivls_impl for Xi Yi uses subset_spec_ivls_impl
lemmas [autoref_rules] = subset_spec_ivls_impl.refine[autoref_higher_order_rule]

schematic_goal subset_spec_ivls_clw_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(Yi, Y) \<in> clw_rel lvivl_rel"
    "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, subset_spec_ivls_clw M X Y) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding subset_spec_ivls_clw_def
  including art
  by (autoref_monadic)
concrete_definition subset_spec_ivls_clw_impl for Mi Xi Yi uses subset_spec_ivls_clw_impl
lemma [autoref_rules]:
"DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Mi Xi Yi. nres_of (subset_spec_ivls_clw_impl D Mi Xi Yi),
   subset_spec_ivls_clw::nat \<Rightarrow> 'a set \<Rightarrow> _)
  \<in> nat_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using subset_spec_ivls_clw_impl.refine by force

lemma REMDUPS_impl[autoref_rules]: "(remdups, REMDUPS) \<in> clw_rel A \<rightarrow> clw_rel A"
  if "PREFER single_valued A"
  using that
  by (force simp: clw_rel_br dest!: brD intro!: brI elim!: single_valued_as_brE)

schematic_goal split_along_ivls2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(ISi, IS) \<in> clw_rel lvivl_rel"
      "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?f, split_along_ivls2 $ M $ X $ IS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_along_ivls2_def
  by autoref_monadic
concrete_definition split_along_ivls2_impl uses split_along_ivls2_impl
lemmas [autoref_rules] = split_along_ivls2_impl.refine

lemma op_list_of_eucl_image_autoref[autoref_rules]:
  shows "(\<lambda>xs. xs, op_list_of_eucl_image) \<in> appr_rel \<rightarrow> appr_rell"
  by (auto simp: length_set_of_appr appr_rel_def lv_rel_def image_image set_rel_br
      cong: image_cong
      dest!: brD)

lemma op_eucl_of_list_image_autoref[autoref_rules]:
  includes autoref_syntax
  assumes "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes "(xsi, xs) \<in> appr_rell"
  assumes "SIDE_PRECOND (env_len xs D)"
  shows "(xsi, op_eucl_of_list_image $ (xs)::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  by (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)

lemma take_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> take n xs \<in> set_of_appr (take n XS)"
  apply (cases "n < length xs")
   apply (subst take_eq_map_nth)
    apply simp
   apply (subst take_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma set_of_appr_ex_append1:
  "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r @ xrs \<in> set_of_appr (b @ xs)"
proof (induction b)
  case Nil
  then show ?case by (auto intro!: exI[where x=Nil])
next
  case (Cons a b)
  then show ?case
    apply (auto)
    subgoal for r
      apply (drule set_of_apprs_ex_Cons[where b=a and xs="b@xs"])
      apply auto
      by (metis Cons_eq_appendI)
    done
qed

lemma set_of_appr_ex_append2:
  assumes "xrs \<in> set_of_appr xs" shows "\<exists>r. xrs @ r \<in> set_of_appr (xs @ b)"
proof -
  from set_of_appr_ex_append1[OF assms, of b]
  obtain r where r: "r @ xrs \<in> set_of_appr (b @ xs)" by auto
  have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b])
    \<in> set_of_appr (map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]))"
    by (rule set_of_appr_project[OF r, of "[length b..<length b + length xs] @ [0..<length b]"])
      auto
  also have "map ((!) (b @ xs)) ([length b..<length b + length xs] @ [0..<length b]) = xs @ b"
    by (auto intro!: nth_equalityI simp: nth_append)
  also have "map ((!) (r @ xrs)) ([length b..<length b + length xs] @ [0..<length b]) = xrs @ r"
    using length_set_of_appr[OF r] assms length_set_of_appr
    by (auto intro!: nth_equalityI simp: nth_append)
  finally show ?thesis by rule
qed

lemma drop_all_conc: "drop (length a) (a@b) = b"
  by (simp)

lemma set_of_appr_takeD: "xs \<in> set_of_appr (take n XS) \<Longrightarrow> xs \<in> take n ` set_of_appr XS"
  apply (frule set_of_appr_ex_append2[where b="map ((!) XS) [n..<length XS]"])
  apply (auto simp: take_append_take_minus_idem)
  apply (rule image_eqI)
   prefer 2 apply assumption
  by (metis append_eq_append_conv append_take_drop_id drop_all_conc length_drop length_set_of_appr)

lemma op_take_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. take ni xs, op_take_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule take_set_of_apprD)
  subgoal by (rule set_of_appr_takeD)
  done

lemma drop_eq_map_nth: "drop n xs = map ((!) xs) [n..<length xs]"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma drop_set_of_apprD: "xs \<in> set_of_appr XS \<Longrightarrow> drop n xs \<in> set_of_appr (drop n XS)"
   apply (subst drop_eq_map_nth)
   apply (subst drop_eq_map_nth)
    apply (simp add: length_set_of_appr)
   apply (rule set_of_appr_project)
  by (auto simp: length_set_of_appr)

lemma drop_append_drop_minus_idem: "n < length XS \<Longrightarrow> map ((!) XS) [0..<n] @ drop n XS = XS"
  by (auto intro!: nth_equalityI simp: nth_append)

lemma set_of_appr_dropD: "xs \<in> set_of_appr (drop n XS) \<Longrightarrow> xs \<in> drop n ` set_of_appr XS"
  apply (cases "n < length XS")
  subgoal
    apply (frule set_of_appr_ex_append1[where b="map ((!) XS) [0..<n]"])
    apply (auto simp: drop_append_drop_minus_idem)
    apply (rule image_eqI)
    prefer 2 apply assumption
    by (metis (mono_tags, lifting) diff_add_inverse2 diff_diff_cancel drop_all_conc length_append
        length_drop length_set_of_appr less_imp_le)
  subgoal
    using set_of_appr_nonempty[of XS]
    by (auto simp: length_set_of_appr image_iff simp del: set_of_appr_nonempty)
  done

lemma op_drop_image_autoref[autoref_rules]:
  shows "(\<lambda>ni xs. drop ni xs, op_drop_image) \<in> nat_rel \<rightarrow> appr_rell \<rightarrow> appr_rell"
  apply (auto simp: appr_rell_internal br_def )
  subgoal by (rule drop_set_of_apprD)
  subgoal by (rule set_of_appr_dropD)
  done

lemma mem_set_of_appr_appendE:
  assumes "zs \<in> set_of_appr (XS @ YS)"
  obtains xs ys where "zs = xs @ ys" "xs \<in> set_of_appr XS" "ys \<in> set_of_appr YS"
proof -
  have "zs = map ((!) zs) [0..<length XS] @ map ((!) zs) [length XS..<length XS + length YS]"
    using assms
    by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
  moreover
  from
    set_of_appr_project[OF assms, of "[0..<length XS]"]
    set_of_appr_project[OF assms, of "[length XS..<length XS + length YS]"]
  have "map ((!) zs) [0..<length XS] \<in> set_of_appr XS"
    "map ((!) zs) [length XS..<length XS + length YS] \<in> set_of_appr YS"
    by (auto simp : map_nth_append2 map_nth_append1)
  ultimately show ?thesis ..
qed

lemma lv_ivl_self[simp]: "lv_ivl xs xs = {xs}" for xs::"'a::order list"
  by (force simp: lv_ivl_def list_all2_conv_all_nth
      intro!: nth_equalityI)

lemma set_of_appr_of_ivl_point'[simp]:
  "set_of_appr (appr_of_ivl ops (replicate E 0) (replicate E 0)) = {replicate E (0::real)}"
  using transfer_operations_rl(1)[of "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E (0::real))" "(replicate E 0)"]
  by (auto simp: appr_rell_internal br_def)

lemma set_of_appr_of_ivl_point:
  "set_of_appr (appr_of_ivl ops xs xs) = {xs}"
  using transfer_operations_rl(1)[of xs xs xs xs]
  by (auto simp: appr_rell_internal br_def)

lemma set_of_appr_of_ivl_append_point:
  "set_of_appr (xs @ appr_of_ivl ops p p) = (\<lambda>x. x @ p) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="take (length xs) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[length xs..<length xs + length p]"])
       apply simp
      apply (auto simp: map_nth_append2 set_of_appr_of_ivl_point)
      subgoal premises prems
      proof -
        from prems
        have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) =
          p ! (i - length xs)"
          by simp
        also have "map ((!) x) [length xs..<length xs + length p] ! (i - length xs) = x ! i"
          using prems
          apply (auto simp: map_nth)
          by (metis add_diff_cancel_left' add_diff_inverse_nat add_less_cancel_left nth_map_upt)
        finally show ?thesis
          using prems by (simp add: min_def)
      qed
      done
    subgoal
      apply (frule set_of_appr_project[where ?is="[0..<length xs]"])
       apply (auto simp: map_nth_append1 take_eq_map_nth
          elim!: mem_set_of_appr_appendE
          dest: length_set_of_appr)
      done
    done
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append2[where b="appr_of_ivl ops p p", OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "x @ r \<in> set_of_appr (xs @ appr_of_ivl ops p p)"
      by auto
    have "map ((!) (x @ r)) [length xs..<length xs + (length p)]
        \<in> set_of_appr
            (map ((!) (xs @ appr_of_ivl ops p p))
              [length xs..<length xs + (length p)])"
      by (rule set_of_appr_project[OF r, of "[length xs..<length xs+(length p)]"])
         auto
    also have "map ((!) (x @ r)) [length xs..<length xs + (length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (xs @ appr_of_ivl ops p p))
        [length xs..<length xs + (length p)] = appr_of_ivl ops p p"
      by (auto intro!: nth_equalityI)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma nth_append_cond:
  "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (auto simp: nth_append)

lemma set_of_appr_of_ivl_point_append:
  "set_of_appr (appr_of_ivl ops p p @ xs) = (\<lambda>x. p @ x) ` set_of_appr xs"
  apply auto
   apply (frule length_set_of_appr)
  subgoal for x
    apply (rule image_eqI[where x="drop (length p) x"])
     apply (auto intro!: nth_equalityI simp: min_def)
     apply (simp add: nth_append)
    subgoal for i
      apply (frule set_of_appr_project[where ?is="[0..<(length p)]"])
       apply simp
      apply (auto simp: map_nth_append1 dest: length_set_of_appr)
      by (metis insertE mem_set_of_appr_appendE memb_imp_not_empty nth_append_cond(1) set_of_appr_of_ivl_point)
    by (metis add_right_imp_eq drop_all_conc drop_set_of_apprD length_append length_set_of_appr)
  subgoal premises prems for x
  proof -
    from set_of_appr_ex_append1[where b="appr_of_ivl ops p p",
        OF \<open>x \<in> set_of_appr xs\<close>]
    obtain r where r: "r @ x \<in> set_of_appr (appr_of_ivl ops p p @ xs)"
      by auto
    have "map ((!) (r @ x)) [0..<(length p)]
        \<in> set_of_appr
            (map ((!) (appr_of_ivl ops p p @ xs))
              [0..<(length p)])"
      by (rule set_of_appr_project[OF r, of "[0..<(length p)]"])
         (auto simp: )
    also have "map ((!) (r @ x)) [0..<(length p)] = r"
      using length_set_of_appr prems r
      by (auto intro!: nth_equalityI simp: nth_append dest!: length_set_of_appr)
    also have "map ((!) (appr_of_ivl ops p p @ xs))
        [0..<(length p)] = appr_of_ivl ops p p"
      by (auto intro!: nth_equalityI simp: nth_append)
    finally have "r = p"
      by (auto simp: set_of_appr_of_ivl_point)
    with r show ?thesis by simp
  qed
  done

lemma op_eucl_of_list_image_pad:
  includes autoref_syntax
  assumes "(xsi, xs) \<in> appr_rell" "DIM_precond TYPE('a::executable_euclidean_space) E"
  shows "(take E xsi @ (let z = replicate (E - length xsi) 0 in appr_of_ivl ops z z),
    op_eucl_of_list_image $ xs::'a set) \<in> appr_rel"
  using assms
  unfolding appr_rel_br
  apply (auto simp: length_set_of_appr appr_rel_br br_def image_image env_len_def appr_rell_internal)
    apply (auto simp: Let_def set_of_appr_of_ivl_append_point length_set_of_appr)
   apply (rule image_eqI)
    prefer 2
    apply (rule image_eqI)
     apply (rule refl)
    apply (rule take_set_of_apprD)
    apply assumption
   apply auto
  apply (drule set_of_appr_takeD)
  apply auto
  done
concrete_definition op_eucl_of_list_image_pad for E xsi uses op_eucl_of_list_image_pad
lemma op_eucl_of_list_image_pad_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
  (op_eucl_of_list_image_pad E, op_eucl_of_list_image::_\<Rightarrow>'a set) \<in> appr_rell \<rightarrow> appr_rel"
  using op_eucl_of_list_image_pad.refine
  by force

lemma [autoref_op_pat_def]: "approx_slp_appr fas \<equiv> OP (approx_slp_appr fas)"
  by auto
schematic_goal approx_slp_appr_impl:
  includes autoref_syntax
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(slpi, slp) \<in> slp_rel" "(Xi, X) \<in> appr_rell"
    notes [autoref_rules] = IdI[of E]
  shows "(nres_of ?r, approx_slp_appr fas $ slp $ X::'a set nres) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding approx_slp_appr_def assms(1)[unfolded DIM_eq_def]
  including art
  by autoref_monadic

concrete_definition approx_slp_appr_impl for E slpi Xi uses approx_slp_appr_impl
lemma approx_slp_appr_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) E \<Longrightarrow>
(\<lambda>slpi Xi. nres_of (approx_slp_appr_impl E slpi Xi), approx_slp_appr fas::_\<Rightarrow>_\<Rightarrow>'a set nres) \<in>
    slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>appr_rel\<rangle>nres_rel"
  using approx_slp_appr_impl.refine[where 'a='a, of E]
  by force

lemma DIM_precond_real[autoref_rules_raw]: "DIM_precond TYPE(real) 1" by simp

schematic_goal mig_set_impl: "(nres_of ?r, mig_set $ D $ X) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  if [autoref_rules]: "(Xi, X::'a set) \<in> appr_rel"  "(Di, D) \<in> nat_rel"
  and [autoref_rules_raw, simplified, simp]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  unfolding autoref_tag_defs
  unfolding mig_set_def
  including art
  by autoref_monadic
concrete_definition mig_set_impl for Di Xi uses mig_set_impl
lemma mig_set_impl_refine[autoref_rules]:
  includes autoref_syntax
  assumes "DIM_precond TYPE('a::executable_euclidean_space) D" "(Di, D) \<in> nat_rel"
  shows "(\<lambda>x. nres_of (mig_set_impl D x), mig_set $ D::'a set\<Rightarrow>_) \<in> appr_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  using mig_set_impl.refine assms by force

lemma ncc_precondD:
  assumes "ncc_precond TYPE('a::executable_euclidean_space)"
  shows"(Xi, X::'a set) \<in> appr_rel \<Longrightarrow> ncc X"
  using assms
  by (auto simp: ncc_precond_def split_beta' br_def appr_rel_br
      dest!: bspec[where x="(Xi, X)"])

end

end