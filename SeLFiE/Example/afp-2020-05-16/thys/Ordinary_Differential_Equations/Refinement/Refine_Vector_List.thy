theory Refine_Vector_List
  imports
  Ordinary_Differential_Equations.ODE_Auxiliarities
  "../Refinement/Autoref_Misc" (* TODO: what is still needed there? *)
  "../Refinement/Weak_Set"
  "Enclosure_Operations"
begin

subsection \<open>Id on euclidean space, real etc\<close>

consts i_rnv::interface
abbreviation "rnv_rel \<equiv> (Id::('a::real_normed_vector\<times>_) set)"
lemmas [autoref_rel_intf] = REL_INTFI[of rnv_rel i_rnv]

context includes autoref_syntax begin

lemma [autoref_rules]:
  "((=), (=)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "((\<le>), (\<le>)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "((<), (<)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> bool_rel"
  "(min, min) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(max, max) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((+), (+)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((-), (-)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((/), (/)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((*), (*)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((^), (^)) \<in> rnv_rel \<rightarrow> nat_rel \<rightarrow> rnv_rel"
  "(int, int) \<in> nat_rel \<rightarrow> int_rel"
  "(Float, Float) \<in> int_rel \<rightarrow> int_rel \<rightarrow> Id"
  "(real_of_float, real_of_float) \<in> Id \<rightarrow> rnv_rel"
  "(upto, upto) \<in> int_rel \<rightarrow> int_rel \<rightarrow> \<langle>int_rel\<rangle>list_rel"
  "(upt, upt) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel"
  "(product_lists, product_lists) \<in> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel"
  "(floor, floor) \<in> rnv_rel \<rightarrow> int_rel"
  by auto
end

subsection \<open>list vector relation\<close>

definition lv_rel::"(real list \<times> 'a::executable_euclidean_space) set"
  where "lv_rel = br eucl_of_list (\<lambda>xs. length xs = DIM('a))"

lemmas [autoref_rel_intf] = REL_INTFI[of lv_rel i_rnv]

lemma lv_rel_sv[relator_props]: "single_valued lv_rel"
  by (auto simp: lv_rel_def)

context includes autoref_syntax begin

lemma lv_rel_le[autoref_rules]: "(list_all2 (\<lambda>x y. x \<le> y), (\<le>)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def eucl_le[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

lemma lv_rel_inf[autoref_rules]: "(List.map2 min, inf) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_inf[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id inf_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_sup[autoref_rules]: "(List.map2 max, sup) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_add[autoref_rules]: "(List.map2 (+), (+)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def algebra_simps
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_minus[autoref_rules]: "(List.map2 (-), (-)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def algebra_simps
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_scaleR[autoref_rules]: "(\<lambda>r. map (scaleR r), scaleR) \<in> rnv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_uminus[autoref_rules]: "(map uminus, uminus) \<in> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_abs[autoref_rules]: "(map abs, abs) \<in> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_abs[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_inner[autoref_rules]: "(inner_lv_rel, (\<bullet>)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel"
  by (subst euclidean_inner[abs_def], subst sum_list_Basis_list[symmetric])
    (auto simp: lv_rel_def br_def eucl_of_list_inner sum_list_sum_nth index_nth_id inner_lv_rel_def)

definition "mig_real a b = (if a \<le> 0 \<and> 0 \<le> b \<or> b \<le> 0 \<and> 0 \<le> a then 0 else min (abs a) (abs b))"
definition "mig_componentwise a b = (\<Sum>i\<in>Basis. mig_real (a \<bullet> i) (b \<bullet> i) *\<^sub>R i)"
definition "mig_lv a b = (List.map2 mig_real a b)"
lemma length_mig_lv[simp]: "length (mig_lv a b) = min (length a) (length b)"
  by (auto simp: mig_lv_def)
lemma mig_lv_nth: "mig_real (a ! i) (b ! i) = mig_lv a b ! i" if "i < length a" "i < length b"
  by (auto simp: mig_lv_def that)

lemma mig_real_abs_le: "\<bar>mig_real a b\<bar> \<le> \<bar>x\<bar>" if "x \<in> {a .. b}" for x::real
  using that
  by (auto simp: mig_real_def abs_real_def)

lemma norm_eucl_L2: "norm x = sqrt (\<Sum>i\<in>Basis. (x \<bullet> i)\<^sup>2)"
  unfolding norm_conv_dist by (subst euclidean_dist_l2)  (simp add: L2_set_def)

lemma mig_componentwise_inner_Basis: "mig_componentwise a b \<bullet> i = mig_real (a \<bullet> i) (b \<bullet> i)"
  if "i \<in> Basis"
  using that
  by (auto simp: mig_componentwise_def)

lemma norm_mig_componentwise_le: "norm (mig_componentwise a b) \<le> norm x" if "x \<in> {a .. b}" for
  a::"'a::ordered_euclidean_space"
  apply (rule norm_le_in_cubeI)
  apply (simp add: mig_componentwise_inner_Basis)
  apply (rule mig_real_abs_le)
  using that
  by (auto simp: eucl_le[where 'a='a])

lemma mig_componentwise_autoref[autoref_rules]:
  "(mig_lv, mig_componentwise) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  unfolding lv_rel_def
  by (auto simp: mig_componentwise_def euclidean_eq_iff[where 'a='a] eucl_of_list_inner mig_lv_nth
      br_def)

primrec vecsumlist' where
  "vecsumlist' 0 xs       = []"
| "vecsumlist' (Suc i) xs = sum_list (map hd xs)#vecsumlist' i (map tl xs)"

lemma vecsumlist':
  assumes "\<And>xs. xs \<in> set xss \<Longrightarrow> i \<le> length xs"
  shows "vecsumlist' i xss = map (\<lambda>i. sum_list (map (\<lambda>xs. xs ! i) xss)) [0..<i]"
  using assms
proof (induction i arbitrary: xss)
  case 0
  then show ?case by simp
next
  case (Suc i)
  from Suc.prems have xss_ne: "x \<in> set xss \<Longrightarrow> x \<noteq> []" for x
    by force
  show ?case
    apply simp
    apply (subst Suc.IH)
    subgoal using Suc.prems by force
    apply (auto intro!: nth_equalityI)
    using xss_ne
    apply (auto simp: nth_Cons nth_append o_def split: nat.splits)
    apply (meson hd_conv_nth arg_cong[OF map_cong, where f = sum_list])
    apply (meson hd_conv_nth arg_cong[OF map_cong, where f = sum_list])
    apply (meson Misc.nth_tl arg_cong[OF map_cong, where f = sum_list])
    by (metis (no_types, lifting) Misc.nth_tl Suc_leI le_neq_implies_less map_cong)
qed

lemma inner_sum_list_left: "sum_list xs \<bullet> b = (\<Sum>x\<leftarrow>xs. x \<bullet> b)"
  by (auto simp: sum_list_sum_nth inner_sum_left)

definition [simp]: "DIM_eq (TYPE('a::executable_euclidean_space)) n \<longleftrightarrow> DIM('a) = n"
abbreviation "DIM_precond TYPE('a) n \<equiv> DIM_eq TYPE('a::executable_euclidean_space) n"

lemma DIM_precond_times[autoref_rules_raw]:
  "DIM_precond TYPE('a::executable_euclidean_space\<times>'b::executable_euclidean_space) (D + E)"
  if "DIM_precond TYPE('a::executable_euclidean_space) D"
     "DIM_precond TYPE('b::executable_euclidean_space) E"
  using that by (auto simp: )

lemma [autoref_rules]: "(sum_list, sum_list) \<in> \<langle>rnv_rel\<rangle>list_rel \<rightarrow> rnv_rel"
  by auto

lemma lv_rel_sum_list[autoref_rules]:
  assumes "DIM_precond TYPE('a::executable_euclidean_space) n"
  shows "(vecsumlist' n, sum_list) \<in> \<langle>lv_rel::(real list \<times> 'a) set\<rangle>list_rel \<rightarrow> lv_rel"
proof
  fix xss and XS::"'a list"
  assume xss: "(xss, XS) \<in> \<langle>lv_rel\<rangle>list_rel"
  then have "\<And>xs. xs \<in> set xss \<Longrightarrow> DIM('a) \<le> length xs"
    by (auto simp: lv_rel_def list_rel_def in_set_conv_nth br_def dest!: list_all2_nthD )
  from vecsumlist'[OF this, of xss] assms xss
  show "(vecsumlist' n xss, sum_list XS) \<in> lv_rel"
    apply (auto simp: lv_rel_def br_def)
    apply (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner inner_sum_list_left)
    apply (rule sum_list_nth_eqI)
     apply (auto simp: list_all2_iff list_rel_def in_set_zip Ball_def)
    apply (drule_tac x = "xss ! na" in spec)
    apply (drule_tac x = "XS ! na" in spec)
    apply (auto simp: eucl_of_list_inner)
    done
qed

lemma lv_rel_eq[autoref_rules]: "((=), (=)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def euclidean_eq_iff[where 'a='a] eucl_of_list_inner
      intro!: nth_equalityI)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

lemma lv_rel_zero[autoref_rules]:
  assumes "DIM_precond TYPE('a::executable_euclidean_space) n"
  shows "(replicate n 0, 0::'a) \<in> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def eucl_of_list_inner intro!: euclidean_eqI[where 'a='a])

definition "Basis_list_impl n = (let zs = replicate n 0 in map (\<lambda>i. zs[i:=1]) [0..<n])"
lemma lv_rel_Basis_list[autoref_rules]:
  assumes "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  shows "(Basis_list_impl n, Basis_list::'a list) \<in> \<langle>lv_rel\<rangle>list_rel"
  using assms
  by (auto simp: list_rel_def lv_rel_def eucl_of_list_inner inner_Basis nth_eq_iff_index
      Basis_list_impl_def
      intro!: brI list_all2_all_nthI euclidean_eqI[where 'a='a])

definition "lv_ivl xrs yrs = {zrs. list_all2 (\<le>) xrs zrs \<and> list_all2 (\<le>) zrs yrs}"

lemma lv_relI:
  "length x = DIM('a) \<Longrightarrow> (x, eucl_of_list x::'a::executable_euclidean_space) \<in> lv_rel"
  by (auto simp: lv_rel_def br_def)

lemma eucl_of_list_image_lv_ivl:
  assumes [simp]: "length xrs = DIM('a)" "length yrs = DIM('a)"
  shows "eucl_of_list ` (lv_ivl xrs yrs) =
    {eucl_of_list xrs .. eucl_of_list yrs::'a::executable_euclidean_space}"
  apply (auto simp: list_all2_iff lv_ivl_def eucl_le[where 'a='a] eucl_of_list_inner Ball_def
      in_set_zip)
  apply (metis Basis_list index_less_size_conv length_Basis_list)
   apply (metis Basis_list index_less_size_conv length_Basis_list)
  apply (rule image_eqI)
   apply (rule eucl_of_list_list_of_eucl[symmetric])
  using nth_Basis_list_in_Basis apply fastforce
  done

end

subsection \<open>Specs for Vectors\<close>

context includes autoref_syntax begin

lemma Inf_specs_Inf_spec:
  "(Inf_specs d, Inf_spec::_\<Rightarrow>'a::executable_euclidean_space nres) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  if "d = DIM('a)"
  apply (auto intro!: nres_relI RES_refine simp: Inf_specs_def Inf_spec_def set_rel_def that)
  subgoal for x y s
    apply (rule exI[where x="eucl_of_list s"])
    apply (auto simp: lv_rel_def br_def subset_iff)
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    subgoal for c
      using lv_rel_le[where 'a ='a, param_fo, OF lv_relI lv_relI, of s c]
      by auto
    done
  done

lemma Sup_specs_Sup_spec:
  "(Sup_specs d, Sup_spec::_\<Rightarrow>'a::executable_euclidean_space nres) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>nres_rel"
  if "d = DIM('a)"
 apply (auto intro!: nres_relI RES_refine simp: Sup_specs_def Sup_spec_def set_rel_def that)
  subgoal for x y s
    apply (rule exI[where x="eucl_of_list s"])
    apply (auto simp: lv_rel_def br_def subset_iff)
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    apply auto
    apply (drule bspec, assumption)
    subgoal for c
      using lv_rel_le[where 'a ='a, param_fo, OF lv_relI lv_relI, of c s]
      by auto
    done
  done

lemma Sup_inners_Sup_inner: "(Sup_inners, Sup_inner) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine
      simp: Sup_inners_def Sup_inner_def  plane_ofs_def plane_of_def lv_rel_def br_def)
  subgoal for a b c d
    using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of d b]
    by auto
  done

lemma Inf_inners_Inf_inner: "(Inf_inners, Inf_inner) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine
      simp: Inf_inners_def Inf_inner_def plane_ofs_def plane_of_def lv_rel_def br_def)
  subgoal for a b c d
    using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of d b]
    by auto
  done

lemma split_spec_params_split_spec_param:
  "(split_spec_params d, split_spec_param::nat\<Rightarrow>'a::executable_euclidean_space set\<Rightarrow>_) \<in> nat_rel \<rightarrow> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<times>\<^sub>r\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a::executable_euclidean_space)"
  apply (auto intro!: nres_relI RES_refine simp: split_spec_param_def split_spec_params_def env_len_def that)
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine simp: plane_ofs_def plane_of_def lv_rel_def br_def subset_iff)
  done

lemma reduce_specs_reduce_spec:
  "(reduce_specs d, reduce_spec::_\<Rightarrow>'a::executable_euclidean_space set\<Rightarrow>_) \<in> Id \<rightarrow> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a::executable_euclidean_space)"
  apply (auto intro!: nres_relI RES_refine simp: reduce_spec_def reduce_specs_def env_len_def that)
  unfolding set_rel_sv[OF lv_rel_sv]
  apply (auto intro!: nres_relI RES_refine simp: plane_ofs_def plane_of_def lv_rel_def br_def subset_iff)
  done

definition [simp]: "rnv_of_lv x = x"

lemma rnv_of_lv_impl[autoref_rules]: "(hd, rnv_of_lv) \<in> lv_rel \<rightarrow> rnv_rel"
  by (auto simp: lv_rel_def br_def length_Suc_conv)

lemma
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows snd_lv_rel[autoref_rules(overloaded)]: "(drop D, snd::('a \<times> _) \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel"
    and fst_lv_rel[autoref_rules(overloaded)]: "(take D, fst::('a \<times> _) \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel"
  using assms by (auto simp: lv_rel_def br_def eucl_of_list_prod)

definition [simp]: "Pair_lv_rel = Pair"

lemma Pair_lv_rel[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows "((@), Pair_lv_rel::'a \<Rightarrow> _) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def intro!: eucl_of_list_eqI)

definition [simp]: "split_lv_rel X = (fst X, snd X)"

schematic_goal split_lv_rel_impl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  shows "(?r, split_lv_rel::'a\<times>_\<Rightarrow>_) \<in> lv_rel \<rightarrow> lv_rel \<times>\<^sub>r lv_rel"
  unfolding split_lv_rel_def
  by autoref

lemma lv_rel_less[autoref_rules]: "(list_all2 (\<lambda>x y. x < y), eucl_less) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def eucl_less_def[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

lemma list_of_eucl_autoref[autoref_rules]: "(\<lambda>x. x, list_of_eucl) \<in> lv_rel \<rightarrow> \<langle>rnv_rel\<rangle>list_rel"
  by (auto simp: lv_rel_def br_def)

definition [simp]: "op_DIM TYPE('a) = DIM('a::executable_euclidean_space)"
lemma [autoref_op_pat_def]: "DIM('a) \<equiv> OP (op_DIM TYPE('a::executable_euclidean_space))" by simp
lemma op_DIM[autoref_rules]:
  assumes [simplified, symmetric, simp]: "DIM_precond TYPE('a) E"
  shows "(E, (op_DIM TYPE('a::executable_euclidean_space))) \<in> nat_rel"
  using assms
  by auto

end

end