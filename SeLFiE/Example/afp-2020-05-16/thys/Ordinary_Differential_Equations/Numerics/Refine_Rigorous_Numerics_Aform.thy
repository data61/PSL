theory Refine_Rigorous_Numerics_Aform
  imports
    Refine_Rigorous_Numerics
    "HOL-Types_To_Sets.Types_To_Sets"
begin

lemma Joints_ne_empty[simp]: "Joints xs \<noteq> {}" "{} \<noteq> Joints xs"
  by (auto simp: Joints_def valuate_def)

lemma Inf_aform_le_Affine: "x \<in> Affine X \<Longrightarrow> Inf_aform X \<le> x"
  by (auto simp: Affine_def valuate_def intro!: Inf_aform)
lemma Sup_aform_ge_Affine: "x \<in> Affine X \<Longrightarrow> x \<le> Sup_aform X"
  by (auto simp: Affine_def valuate_def intro!: Sup_aform)

lemmas Inf_aform'_Affine_le = order_trans[OF Inf_aform' Inf_aform_le_Affine]
lemmas Sup_aform'_Affine_ge = order_trans[OF Sup_aform_ge_Affine Sup_aform']

fun approx_form_aform :: "nat \<Rightarrow> form \<Rightarrow> real aform list \<Rightarrow> bool" where
"approx_form_aform prec (Less a b) bs =
   (case (approx_floatariths prec [a - b] bs)
   of Some [r] \<Rightarrow> Sup_aform' prec r < 0
    | _ \<Rightarrow> False)"
| "approx_form_aform prec (LessEqual a b) bs =
   (case (approx_floatariths prec [a - b] bs)
   of Some [r] \<Rightarrow> Sup_aform' prec r \<le> 0
    | _ \<Rightarrow> False)"
| "approx_form_aform prec (AtLeastAtMost a b c) bs =
   (case (approx_floatariths prec [a - b, a - c] bs)
   of Some [r, s] \<Rightarrow> 0 \<le> Inf_aform' prec r \<and>  Sup_aform' prec s \<le> 0
    | _ \<Rightarrow> False)"
| "approx_form_aform prec (Bound a b c d) bs = False"
| "approx_form_aform prec (Assign a b c) bs = False"
| "approx_form_aform prec (Conj a b) bs \<longleftrightarrow>
    approx_form_aform prec a bs \<and> approx_form_aform prec b bs"
| "approx_form_aform prec (Disj a b) bs \<longleftrightarrow>
    approx_form_aform prec a bs \<or> approx_form_aform prec b bs"

lemma in_Joints_intervalD:
  "x \<in> {Inf_aform' p X .. Sup_aform' p X} \<and> xs \<in> Joints XS"
  if "x#xs \<in> Joints (X#XS)"
  using that
  by (auto simp: Joints_def valuate_def Affine_def
      intro!: Inf_aform'_Affine_le Sup_aform'_Affine_ge)

lemma approx_form_aform:
  "interpret_form f vs"
  if "approx_form_aform p f VS" "vs \<in> Joints VS"
  using that
  by (induction f)
    (auto split: option.splits list.splits simp: algebra_simps
      dest!: approx_floatariths_outer
      dest!: in_Joints_intervalD[where p=p])

fun msum_aforms::"nat \<Rightarrow> real aform list \<Rightarrow> real aform list \<Rightarrow> real aform list"  where
  "msum_aforms d (x#xs) (y#ys) = msum_aform d x y#msum_aforms d xs ys"
| "msum_aforms d _ _ = []"

definition [simp]: "degree_aforms_real = (degree_aforms::real aform list \<Rightarrow> nat)"

abbreviation "msum_aforms' \<equiv> \<lambda>X Y. msum_aforms (degree_aforms_real (X @ Y)) X Y"

lemma aform_val_msum_aforms:
  assumes "degree_aforms xs \<le> d"
  shows "aform_vals e (msum_aforms d xs ys) = List.map2 (+) (aform_vals e xs) (aform_vals (\<lambda>i. e (i + d)) ys)"
  using assms
proof (induction xs ys rule: msum_aforms.induct)
  case (1 d x xs y ys)
  from 1 have "degree_aforms xs \<le> d"
    by (auto simp: degrees_def)
  from 1(1)[OF this] 1
  have "aform_vals e (msum_aforms d xs ys) = List.map2 (+) (aform_vals e xs) (aform_vals (\<lambda>i. e (i + d)) ys)"
    by simp
  then show ?case
    using 1
    by (simp add: aform_vals_def aform_val_msum_aform degrees_def)
qed (auto simp: aform_vals_def)

lemma Joints_msum_aforms:
  assumes "degree_aforms xs \<le> d"
  assumes "degree_aforms ys \<le> d"
  shows "Joints (msum_aforms d xs ys) = {List.map2 (+) a b |a b. a \<in> Joints xs \<and> b \<in> Joints ys}"
  apply (auto simp: Joints_def valuate_def aform_vals_def[symmetric]
      aform_val_msum_aforms assms)
   apply force
  subgoal for e e'
    apply (rule image_eqI[where x="\<lambda>i. if i < d then e i else e' (i - d)"])
     apply (auto simp: Pi_iff)
  proof goal_cases
    case 1
    have "(aform_vals e xs) = aform_vals (\<lambda>i. if i < d then e i else e' (i - d)) xs"
      using assms
      by (auto intro!: simp: aform_vals_def aform_val_def degrees_def intro!: pdevs_val_degree_cong)
    then show ?case
      by simp
  qed
  done

definition "split_aforms_largest_uncond_take n X =
  (let (i, x) = max_pdev (abssum_of_pdevs_list (map snd (take n X))) in split_aforms X i)"

text \<open>intersection with plane\<close>

definition
  "project_coord x b n = (\<Sum>i\<leftarrow>Basis_list. (if i = b then n else if i = -b then -n else x \<bullet> i) *\<^sub>R i)"

lemma inner_eq_abs_times_sgn:
  "u \<bullet> b = abs u \<bullet> b * sgn (u \<bullet> b)" if "b \<in> Basis" for b::"'a::ordered_euclidean_space"
  by (subst sgn_mult_abs[symmetric]) (auto simp: that abs_inner )

lemma inner_Basis_eq_zero_absI: "x \<in> Basis \<Longrightarrow> abs u \<in> Basis \<Longrightarrow> x \<noteq> \<bar>u\<bar> \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> u \<bullet> x = 0"
  for x::"'a::ordered_euclidean_space"
  apply (subst euclidean_inner)
  apply (auto simp: inner_Basis if_distribR if_distrib cong: if_cong)
  apply (subst inner_eq_abs_times_sgn)
  by (auto simp: inner_Basis)

lemma abs_in_BasisE:
  fixes u::"'a::ordered_euclidean_space"
  assumes "abs u \<in> Basis"
  obtains "abs u = u" | "abs u = - u"
proof (cases "u \<bullet> abs u = 1")
  case True
  have "abs u = (\<Sum>i\<in>Basis. (if i = abs u then (abs u \<bullet> i) *\<^sub>R i else 0))"
    using assms
    by (auto simp: )
  also have "\<dots> = (\<Sum>i\<in>Basis. (if i = abs u then (u \<bullet> i) *\<^sub>R i else 0))"
    by (rule sum.cong) (auto simp: True)
  also have "\<dots> = (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R i)"
    by (rule sum.cong) (auto simp: inner_Basis_eq_zero_absI assms)
  also have "\<dots> = u" by (simp add: euclidean_representation)
  finally show ?thesis ..
next
  case False
  then have F: "u \<bullet> \<bar>u\<bar> = -1"
    apply (subst inner_eq_abs_times_sgn[OF assms]) 
    apply (subst (asm) inner_eq_abs_times_sgn[OF assms]) 
    using assms
    apply (auto simp: inner_Basis sgn_if)
    by (metis (full_types) abs_0_eq euclidean_all_zero_iff inner_Basis_eq_zero_absI nonzero_Basis)
  have "abs u = (\<Sum>i\<in>Basis. (if i = abs u then (abs u \<bullet> i) *\<^sub>R i else 0))"
    using assms
    by (auto simp: )
  also have "\<dots> = (\<Sum>i\<in>Basis. (if i = abs u then (- u \<bullet> i) *\<^sub>R i else 0))"
    by (rule sum.cong) (auto simp: F)
  also have "\<dots> = (\<Sum>i\<in>Basis. (- u \<bullet> i) *\<^sub>R i)"
    by (rule sum.cong) (auto simp: inner_Basis_eq_zero_absI assms)
  also have "\<dots> = - u" by (subst euclidean_representation) simp
  finally show ?thesis ..
qed
  
lemma abs_in_Basis_iff:
  fixes u::"'a::ordered_euclidean_space"
  shows "abs u \<in> Basis \<longleftrightarrow> u \<in> Basis \<or> - u \<in> Basis"
proof -
  have u: "u = (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R i)"
    by (simp add: euclidean_representation)
  have u': "- u = (\<Sum>i\<in>Basis. (- (u \<bullet> i)) *\<^sub>R i)"
    by (subst u) (simp add: sum_negf)
  have au: "abs u = (\<Sum>i\<in>Basis. \<bar>u \<bullet> i\<bar> *\<^sub>R i)"
    by (simp add: eucl_abs[where 'a='a])
  have "(u \<in> Basis \<or> - u \<in> Basis)" if "(\<bar>u\<bar> \<in> Basis)"
    apply (rule abs_in_BasisE[OF that])
    using that
    by auto
  show ?thesis
    apply safe
    subgoal premises prems
      using prems(1)
      apply (rule abs_in_BasisE)
      using prems
      by simp_all
    subgoal
      apply (subst au)
      apply (subst (asm) u)
      apply (subst sum.cong[OF refl])
       apply (subst abs_inner[symmetric]) apply auto
      using u apply auto[1]
      done
    subgoal
      apply (subst au)
      apply (subst (asm) u')
      apply (subst sum.cong[OF refl])
      apply (subst abs_inner[symmetric]) apply auto
      using u' apply auto
      by (metis Basis_nonneg abs_of_nonpos inner_minus_left neg_0_le_iff_le scaleR_left.minus)
    done
qed

lemma abs_inner_Basis:
  fixes u v::"'a::ordered_euclidean_space"
  assumes "abs u \<in> Basis" "abs v \<in> Basis"
  shows "inner u v = (if u = v then 1 else if u = -v then -1 else 0)"
proof -
  define i where "i \<equiv> if u \<in> Basis then u else -u"
  define j where "j \<equiv> if v \<in> Basis then v else -v"
  have u: "u = (if u \<in> Basis then i else - i)"
    and v: "v = (if v \<in> Basis then j else - j)"
    by (auto simp: i_def j_def)
  have "i \<in> Basis" "j \<in> Basis"
    using assms
     by (auto simp: i_def j_def abs_in_Basis_iff)
   then show ?thesis
     apply (subst u)
     apply (subst v)
     apply (auto simp: inner_Basis)
     apply (auto simp: j_def i_def split: if_splits)
     using Basis_nonneg abs_of_nonpos by fastforce
 qed

lemma
  project_coord_inner_Basis:
  assumes "i \<in> Basis"
  shows "(project_coord x b n) \<bullet> i = (if i = b then n else if i = -b then -n else x \<bullet> i)"
proof -
  have "project_coord x b n \<bullet> i =
    (\<Sum>j\<in>Basis. (if j = b then n else if j = -b then -n else x \<bullet> j) * (if j = i then 1 else 0))"
    using assms
    by (auto simp: project_coord_def inner_sum_left inner_Basis)
  also have "\<dots> = (\<Sum>j\<in>Basis. (if j = i then (if j = b then n else if j = -b then -n else x \<bullet> j) else 0))"
    by (rule sum.cong) auto
  also have "\<dots> = (if i = b then n else if i = -b then -n else x \<bullet> i)"
    using assms
    by (subst sum.delta) auto
  finally show ?thesis by simp
qed

lemma
  project_coord_inner:
  assumes "abs i \<in> Basis"
  shows "(project_coord x b n) \<bullet> i = (if i = b then n else if i = -b then -n else x \<bullet> i)"
proof -
  consider "i \<in> Basis" | "- i \<in> Basis"
    using assms
    by (auto simp: abs_in_Basis_iff)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: project_coord_inner_Basis)
  next
    case 2
    have "project_coord x b n \<bullet> i = - (project_coord x b n \<bullet> - i)"
      by simp
    also have "\<dots> = - (if - i = b then n else if - i = -b then -n else x \<bullet> - i)"
      using 2
      by (subst project_coord_inner_Basis) simp_all
    also have "\<dots> = (if i = b then n else if i = -b then -n else x \<bullet> i)"
      using 2 by auto (metis Basis_nonneg abs_le_zero_iff abs_of_nonneg neg_le_0_iff_le nonzero_Basis)
    finally show ?thesis .
  qed
qed

lift_definition project_coord_pdevs::"'a::executable_euclidean_space sctn \<Rightarrow> 'a pdevs \<Rightarrow> 'a pdevs" is
  "\<lambda>sctn xs i. project_coord (xs i) (normal sctn) 0"
  by (rule finite_subset) (auto simp: project_coord_def cong: if_cong)

definition "project_coord_aform sctn cxs =
  (project_coord (fst cxs) (normal sctn) (pstn sctn), project_coord_pdevs sctn (snd cxs))"

definition project_coord_aform_lv :: "real aform list \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real aform list"
  where "project_coord_aform_lv xs b n = xs[b:=(n, zero_pdevs)]"

definition "project_ncoord_aform x b n = project_coord_aform (Sctn (Basis_list ! b) n) x"

lemma
  finite_sum_subset_aux_lemma:
  assumes "finite s"
  shows " {i. (\<Sum>x\<in>s. f x i) \<noteq> 0} \<subseteq> {i. \<exists>x\<in>s. f x i \<noteq> 0}"
proof -
  have "{i. (\<Sum>x\<in>s. f x i) \<noteq> 0} = - {i. (\<Sum>x\<in>s. f x i) = 0}"
    by auto
  also have "\<dots> \<subseteq> - {i. \<forall>x \<in> s. f x i = 0}"
    by auto
  also have "\<dots> = {i. \<exists>x \<in> s. f x i \<noteq> 0}"
    by auto
  finally show ?thesis by simp
qed

lift_definition sum_pdevs::"('i \<Rightarrow> 'a::comm_monoid_add pdevs) \<Rightarrow> 'i set \<Rightarrow>  'a pdevs"
  is "\<lambda>f X. if finite X then (\<lambda>i. \<Sum>x\<in>X. f x i) else (\<lambda>_. 0)"
  apply auto
  apply (rule finite_subset)
   apply (rule finite_sum_subset_aux_lemma)
   apply auto
  done

lemma pdevs_apply_sum_pdevs[simp]:
  "pdevs_apply (sum_pdevs f X) i = (\<Sum>x\<in>X. pdevs_apply (f x) i)"
  by transfer auto

lemma sum_pdevs_empty[simp]: "sum_pdevs f {} = zero_pdevs"
  by transfer auto

lemma sum_pdevs_insert[simp]:
  "finite xs \<Longrightarrow> sum_pdevs f (insert a xs) =
    (if a \<in> xs then sum_pdevs f xs else add_pdevs (f a) (sum_pdevs f xs))"
  by (auto simp: insert_absorb intro!: pdevs_eqI)

lemma sum_pdevs_infinite[simp]: "infinite X \<Longrightarrow> sum_pdevs f X = zero_pdevs"
  by transfer auto

lemma compute_sum_pdevs[code]:
  "sum_pdevs f (set XS) = foldr (\<lambda>a b. add_pdevs (f a) b) (remdups XS) zero_pdevs"
  by (induction XS) (auto simp: )

lemma degree_sum_pdevs_le:
  "degree (sum_pdevs f X) \<le> Max (degree ` f ` X)"
  apply (rule degree_le)
  apply auto
  apply (cases "X = {}")
  subgoal by (simp add: )
  subgoal by (cases "finite X") simp_all
  done

lemma pdevs_val_sum_pdevs:
  "pdevs_val e (sum_pdevs f X) = (\<Sum>x\<in>X. pdevs_val e (f x))"
  apply (cases "finite X")
  subgoal
    apply (subst pdevs_val_sum_le)
     apply (rule degree_sum_pdevs_le)
    apply (auto simp: scaleR_sum_right)
    apply (subst sum.swap)
    apply (rule sum.cong[OF refl])
    apply (subst pdevs_val_sum_le[where d="Max (degree ` f ` X)"])
     apply (auto simp: Max_ge_iff)
    done
  subgoal by simp
  done

definition eucl_of_list_aform :: "(real \<times> real pdevs) list \<Rightarrow> 'a::executable_euclidean_space aform"
where "eucl_of_list_aform xs =
  (eucl_of_list (map fst xs), sum_pdevs (\<lambda>i. pdevs_scaleR (snd (xs ! index Basis_list i)) i) Basis)"

definition lv_aforms_rel::"(((real \<times> real pdevs) list) \<times> ('a::executable_euclidean_space aform)) set"
  where "lv_aforms_rel = br eucl_of_list_aform (\<lambda>xs. length xs = DIM('a))"


definition "inner_aforms' p X Y =
  (let fas = [inner_floatariths (map floatarith.Var [0..<length X])
    (map floatarith.Var[length X..<length X + length Y])]
  in
    approx_slp_outer p (length fas) fas (X@Y)
    )"

lemma
  affine_extension_AffineD:
  assumes "affine_extension2 (\<lambda>d x y. Some (F d x y)) f"
  assumes "[x, y] \<in> Joints [X, Y]"
  assumes "d \<ge> degree_aform X"
  assumes "d \<ge> degree_aform Y"
  shows "f x y \<in> Affine (F d X Y)"
proof -
  from assms(2) obtain e where e:
    "e \<in> funcset UNIV {-1 .. 1}"
    "x = aform_val e X"
    "y = aform_val e Y"
    by (auto simp: Joints_def valuate_def)
  from affine_extension2E[OF assms(1) refl e(1) assms(3) assms(4)]
  obtain e' where "e' \<in> funcset UNIV {- 1..1}" "f (aform_val e X) (aform_val e Y) = aform_val e' (F d X Y)"
    "\<And>n. n < d \<Longrightarrow> e' n = e n" "aform_val e X = aform_val e' X" "aform_val e Y = aform_val e' Y"
    by auto
  then show ?thesis by (auto simp: Affine_def valuate_def e)
qed

lemma aform_val_zero_pdevs[simp]: "aform_val e (x, zero_pdevs) = x"
  by (auto simp: aform_val_def)

lemma neg_equal_zero_eucl[simp]: "-a = a \<longleftrightarrow> a = 0" for a::"'a::euclidean_space"
  by (auto simp: algebra_simps euclidean_eq_iff[where 'a='a])

context includes autoref_syntax begin

lemma Option_bind_param[param, autoref_rules]:
  "((\<bind>), (\<bind>)) \<in> \<langle>S\<rangle>option_rel \<rightarrow> (S \<rightarrow> \<langle>R\<rangle>option_rel) \<rightarrow> \<langle>R\<rangle>option_rel"
  unfolding Option.bind_def
  by parametricity

lemma zip_Basis_list_pat[autoref_op_pat_def]: "\<Sum>(b, m)\<leftarrow>zip Basis_list ms. m *\<^sub>R b \<equiv> OP eucl_of_list $ ms"
proof (rule eq_reflection)
  have z: "zip ms (Basis_list::'a list) = map (\<lambda>(x, y). (y, x)) (zip Basis_list ms)"
    by (subst zip_commute) simp
  show "(\<Sum>(b, m)\<leftarrow>zip (Basis_list::'a list) ms. m *\<^sub>R b) = OP eucl_of_list $ ms"
    unfolding eucl_of_list_def autoref_tag_defs
    apply (subst z)
    apply (subst map_map)
    apply (auto cong: map_cong simp: split_beta')
    done
qed

lemma length_aforms_of_ivls: "length (aforms_of_ivls a b) = min (length a) (length b)"
  by (auto simp: aforms_of_ivls_def)

lemma length_lv_rel:
  "(ys, y::'a) \<in> lv_rel \<Longrightarrow> length ys = DIM('a::executable_euclidean_space)"
  by (auto simp: lv_rel_def br_def)

lemma lv_rel_nth[simp]: "(xs, x::'a::executable_euclidean_space) \<in> lv_rel \<Longrightarrow> b \<in> Basis \<Longrightarrow>
  xs ! index (Basis_list) b = x \<bullet> b"
  unfolding lv_rel_def
  by (auto simp: br_def eucl_of_list_inner)

lemma aform_of_ivl_autoref[autoref_rules]:
  "(aforms_of_ivls, aform_of_ivl) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_aforms_rel"
  apply (auto simp: lv_aforms_rel_def br_def eucl_of_list_aform_def length_aforms_of_ivls length_lv_rel)
  subgoal for xs x ys y
    apply (auto simp: aform_of_ivl_def aforms_of_ivls_def o_def eucl_of_list_inner inner_simps
        pdevs_apply_pdevs_of_ivl length_lv_rel
        intro!: euclidean_eqI[where 'a='a] pdevs_eqI)
    by (metis index_Basis_list_nth inner_not_same_Basis length_Basis_list nth_Basis_list_in_Basis)
  done

lemma bound_intersect_2d_ud[autoref_rules]:
  shows "(bound_intersect_2d_ud, bound_intersect_2d_ud) \<in> nat_rel \<rightarrow> ((rnv_rel \<times>\<^sub>r rnv_rel) \<times>\<^sub>r Id) \<rightarrow> rnv_rel \<rightarrow> \<langle>rnv_rel \<times>\<^sub>r rnv_rel\<rangle>option_rel"
  by auto

lemma eucl_of_list_autoref[autoref_rules]:
  includes autoref_syntax
  assumes "SIDE_PRECOND (length xs = DIM('a::executable_euclidean_space))"
  assumes "(xsi, xs) \<in> \<langle>rnv_rel\<rangle>list_rel"
  shows "(xsi, eucl_of_list $ xs::'a) \<in> lv_rel"
  using assms
  unfolding lv_rel_def
  by (auto simp: br_def)

definition "inner2s x b c = (inner_lv_rel x b, inner_lv_rel x c)"

lemma inner_lv_rel_autoref[autoref_rules]:
  "(inner_lv_rel, (\<bullet>)) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel"
  using lv_rel_inner[unfolded inner_lv_rel_def[symmetric]]
  by auto

lemma inner_lv_rel_eq:
  "\<lbrakk>length xs = DIM('a::executable_euclidean_space); (xa, x'a) \<in> lv_rel\<rbrakk> \<Longrightarrow>
  inner_lv_rel xs xa = eucl_of_list xs \<bullet> (x'a::'a)"
  using inner_lv_rel_autoref[param_fo, of "xs" "eucl_of_list xs" xa x'a]
  unfolding lv_rel_def
  by (auto simp: br_def)

definition "inner_pdevs xs ys = sum_pdevs (\<lambda>i. scaleR_pdevs (ys ! i) (xs ! i)) {..<length xs}"

definition "pdevs_inner2s xs a b = prod_of_pdevs (inner_pdevs xs a) (inner_pdevs xs b)"

lemma inner2_aform_autoref[autoref_rules]:
  shows "((\<lambda>xs a b. (inner2s (map fst xs) a b, pdevs_inner2s (map snd xs) a b)), inner2_aform) \<in> lv_aforms_rel \<rightarrow> lv_rel \<rightarrow> lv_rel \<rightarrow> ((rnv_rel \<times>\<^sub>r rnv_rel)\<times>\<^sub>rId)"
  unfolding inner2_aform_def
  apply (auto simp: lv_aforms_rel_def br_def eucl_of_list_aform_def inner2_aform_def )
   apply (auto simp: inner2s_def inner2_def inner_lv_rel_eq pdevs_inner2s_def inner_pdevs_def
      sum_Basis_sum_nth_Basis_list inner_sum_left inner_Basis mult.commute
      intro!: pdevs_eqI)
  subgoal for a b c d e f
    apply (rule sum.cong)
     apply force
    subgoal for n by (auto dest!: lv_rel_nth[where b="Basis_list ! n"] simp: inner_commute)
    done
  subgoal for a b c d e f
    apply (rule sum.cong)
     apply force
    subgoal for n by (auto dest!: lv_rel_nth[where b="Basis_list ! n"] simp: inner_commute)
    done
  done

lemma RETURN_inter_aform_plane_ortho_annot:
  "RETURN (inter_aform_plane_ortho p (Z::'a aform) n g) =
    (case those (map (\<lambda>b. bound_intersect_2d_ud p (inner2_aform Z n b) g) Basis_list) of
      Some mMs \<Rightarrow>
      do {
        ASSERT (length mMs = DIM('a::executable_euclidean_space));
        let l = (\<Sum>(b, m)\<leftarrow>zip Basis_list (map fst mMs). m *\<^sub>R b);
        let u = (\<Sum>(b, M)\<leftarrow>zip Basis_list (map snd mMs). M *\<^sub>R b);
        RETURN (Some (aform_of_ivl l u))
      }
  | None \<Rightarrow> RETURN None)"
  apply (auto simp: inter_aform_plane_ortho_def split: option.splits)
  subgoal premises prems for x2
  proof -
    have "length x2 = DIM('a)" using prems
      using map_eq_imp_length_eq by (force simp: those_eq_Some_map_Some_iff)
    then show ?thesis using prems by auto
  qed
  done

definition "inter_aform_plane_ortho_nres p Z n g = RETURN (inter_aform_plane_ortho p Z n g)"

schematic_goal inter_aform_plane_ortho_lv:
  fixes Z::"'a::executable_euclidean_space aform"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a) D"
  assumes [autoref_rules]: "(pp, p) \<in> nat_rel" "(Zi, Z) \<in> lv_aforms_rel"
    "(ni, n) \<in> lv_rel" "(gi, g) \<in> rnv_rel"
  notes [autoref_rules] = those_param param_map
  shows "(nres_of (?f::?'a dres), inter_aform_plane_ortho_nres $ p $ Z $ n $ g) \<in> ?R"
  unfolding autoref_tag_defs
  unfolding RETURN_inter_aform_plane_ortho_annot inter_aform_plane_ortho_nres_def
  including art
  by autoref_monadic
concrete_definition inter_aform_plane_ortho_lv for pp Zi ni gi uses inter_aform_plane_ortho_lv
lemmas [autoref_rules] = inter_aform_plane_ortho_lv.refine

lemma project_coord_lv[autoref_rules]:
  assumes "(xs, x::'a::executable_euclidean_space aform) \<in> lv_aforms_rel" "(ni, n) \<in> nat_rel"
  assumes "SIDE_PRECOND (n < DIM('a))"
  shows "(project_coord_aform_lv xs ni, project_ncoord_aform $ x $ n) \<in> rnv_rel \<rightarrow> lv_aforms_rel"
  using assms
  apply (auto simp: project_coord_aform_lv_def project_ncoord_aform_def lv_rel_def
      project_coord_aform_def eucl_of_list_aform_def
      lv_aforms_rel_def br_def)
  subgoal
    apply (auto intro!: euclidean_eqI[where 'a='a])
    apply (subst project_coord_inner_Basis)
     apply (auto simp: eucl_of_list_inner )
     apply (subst nth_list_update)
      apply (auto simp: )
    using in_Basis_index_Basis_list apply force
    using inner_not_same_Basis nth_Basis_list_in_Basis apply fastforce
    apply (auto simp: nth_list_update)
    done
  subgoal for i
    apply (auto intro!: pdevs_eqI simp: project_coord_pdevs.rep_eq)
    apply (auto intro!: euclidean_eqI[where 'a='a])
    apply (subst project_coord_inner_Basis)
     apply (auto simp: eucl_of_list_inner )
     apply (subst nth_list_update)
      apply (auto simp: )
    using inner_not_same_Basis nth_Basis_list_in_Basis apply fastforce
    apply (auto simp: nth_list_update)
    done
  done

definition inter_aform_plane
  where "inter_aform_plane prec Xs (sctn::'a sctn) =
    do {
      cxs \<leftarrow> inter_aform_plane_ortho_nres (prec) (Xs) (normal sctn) (pstn sctn);
      case cxs of
        Some cxs \<Rightarrow>
          (if normal sctn \<in> set Basis_list
            then do {
              ASSERT (index Basis_list (normal sctn) < DIM('a::executable_euclidean_space));
              RETURN ((project_ncoord_aform cxs (index Basis_list (normal sctn)) (pstn sctn)))
            }
          else if - normal sctn \<in> set Basis_list
            then do {
              ASSERT (index Basis_list (-normal sctn) < DIM('a));
              RETURN ((project_ncoord_aform cxs (index Basis_list (-normal sctn)) (- pstn sctn)))
            }
          else SUCCEED)
      | None \<Rightarrow> SUCCEED
    }"

lemma [autoref_rules]:
  assumes [THEN GEN_OP_D, param]: "GEN_OP (=) (=) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(index, index) \<in> \<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel"
  unfolding index_def find_index_def
  by parametricity

schematic_goal inter_aform_plane_lv:
  fixes Z::"'a::executable_euclidean_space aform"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a) D"
  assumes [autoref_rules]: "(preci, prec) \<in> nat_rel" "(Zi, Z) \<in> lv_aforms_rel"
      "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  notes [autoref_rules] = those_param param_map
  shows "(nres_of (?f::?'a dres), inter_aform_plane prec Z sctn) \<in> ?R"
  unfolding autoref_tag_defs
  unfolding inter_aform_plane_def
  including art
  by (autoref_monadic )

concrete_definition inter_aform_plane_lv for preci Zi sctni uses inter_aform_plane_lv
lemmas [autoref_rules] = inter_aform_plane_lv.refine[autoref_higher_order_rule(1)]

end


lemma Basis_not_uminus:
  fixes i::"'a::euclidean_space"
  shows "i \<in> Basis \<Longrightarrow> - i \<notin> Basis"
  by (metis inner_Basis inner_minus_left one_neq_neg_one zero_neq_neg_one)

lemma
  pdevs_apply_project_coord_pdevs:
  assumes "normal sctn \<in> Basis \<or> - normal sctn \<in> Basis"
  assumes "i \<in> Basis"
  shows "pdevs_apply (project_coord_pdevs sctn cxs) x \<bullet> i =
    (if i = abs (normal sctn) then 0 else pdevs_apply cxs x \<bullet> i)"
  using assms[unfolded abs_in_Basis_iff[symmetric]]
  apply (transfer fixing: sctn)
  apply (auto simp: project_coord_inner Basis_not_uminus)
  using Basis_nonneg apply force
  using Basis_nonneg assms(1) by force

lemma pdevs_domain_project_coord_pdevs_subset:
  "pdevs_domain (project_coord_pdevs sctn X) \<subseteq> pdevs_domain X"
  apply (auto simp: )
  apply (auto simp: euclidean_eq_iff[where 'a='a] )
  by (metis add.inverse_neutral project_coord_inner_Basis project_coord_pdevs.rep_eq)

lemma pdevs_val_project_coord_pdevs_inner_Basis:
  assumes "b \<in> Basis"
  shows "pdevs_val e (project_coord_pdevs sctn X) \<bullet> b =
    (if b = abs (normal sctn) then 0 else pdevs_val e X \<bullet> b)"
  using assms
  apply (auto simp: )
   apply (simp add: pdevs_val_pdevs_domain inner_sum_left )
   apply (subst sum.cong[OF refl])
    apply (subst pdevs_apply_project_coord_pdevs)
      apply (simp add: abs_in_Basis_iff)
     apply simp
    apply (rule refl)
   apply auto
  unfolding pdevs_val_pdevs_domain inner_sum_left
  apply (rule sum.mono_neutral_cong_left)
     apply simp
    apply (rule pdevs_domain_project_coord_pdevs_subset)
     apply auto
   apply (metis Basis_nonneg abs_minus_cancel abs_of_nonneg euclidean_all_zero_iff
      project_coord_inner_Basis project_coord_pdevs.rep_eq)
   apply (metis Basis_nonneg abs_minus_cancel abs_of_nonneg
      project_coord_inner_Basis project_coord_pdevs.rep_eq)
  done

lemma inner_in_Sum: "b \<in> Basis \<Longrightarrow> x \<bullet> b = (\<Sum>i\<in>Basis. x \<bullet> i * (i \<bullet> b))"
  apply (subst euclidean_representation[of x, symmetric])
  unfolding inner_sum_left
  by (auto simp: intro!: )

lemma aform_val_project_coord_aform:
  "aform_val e (project_coord_aform sctn X) = project_coord (aform_val e X) (normal sctn) (pstn sctn)"
  apply (auto simp: aform_val_def project_coord_def project_coord_aform_def)
  apply (rule euclidean_eqI)
  unfolding inner_add_left inner_sum_left
  apply (subst pdevs_val_project_coord_pdevs_inner_Basis)
   apply (auto simp: )
   apply (rule sum.cong)
  apply auto
   apply (metis abs_in_Basis_iff abs_inner abs_inner_Basis abs_zero inner_commute)
  apply (subst inner_in_Sum[where x="pdevs_val e (snd X)"], force)
  unfolding sum.distrib[symmetric]
  apply (rule sum.cong)
  apply auto
  apply (metis Basis_nonneg abs_inner_Basis abs_of_nonneg abs_of_nonpos inner_commute neg_0_le_iff_le)
   apply (metis Basis_nonneg abs_inner_Basis abs_of_nonneg abs_of_nonpos neg_0_le_iff_le)
  apply (auto simp: inner_Basis)
  done

lemma project_coord_on_plane:
  assumes "x \<in> plane_of (Sctn n c)"
  shows "project_coord x n c = x"
  using assms
  by (auto simp: project_coord_def plane_of_def intro!: euclidean_eqI[where 'a='a])

lemma
  mem_Affine_project_coord_aformI:
  assumes "x \<in> Affine X"
  assumes "x \<in> plane_of sctn"
  shows "x \<in> Affine (project_coord_aform sctn X)"
proof -
  have "x = project_coord x (normal sctn) (pstn sctn)"
    using assms by (intro project_coord_on_plane[symmetric]) auto
  also
  from assms obtain e where "e \<in> funcset UNIV {-1 .. 1}" "x = aform_val e X"
    by (auto simp: Affine_def valuate_def)
  note this(2)
  also have "project_coord (aform_val e X) (normal sctn) (pstn sctn) =
    aform_val e (project_coord_aform sctn X)"
    by (simp add: aform_val_project_coord_aform)
  finally have "x = aform_val e (project_coord_aform sctn X)" unfolding \<open>x = aform_val e X\<close> .
  then show ?thesis using \<open>e \<in> _\<close>
    by (auto simp: Affine_def valuate_def)
qed

lemma
  mem_Affine_project_coord_aformD:
  assumes "x \<in> Affine (project_coord_aform sctn X)"
  assumes "abs (normal sctn) \<in> Basis"
  shows "x \<in> plane_of sctn"
  using assms
  by (auto simp: Affine_def valuate_def aform_val_project_coord_aform plane_of_def
      project_coord_inner)

definition "reduce_aform prec t X =
    summarize_aforms (prec) (collect_threshold (prec) 0 t) (degree_aforms X) X"

definition "correct_girard p m N (X::real aform list) =
  (let
    Xs = map snd X;
    M = pdevs_mapping Xs;
    D = domain_pdevs Xs;
    diff = m - card D
  in if 0 < diff then (\<lambda>_ _. True) else
    let
      Ds = sorted_list_of_set D;
      ortho_indices = map fst (take (diff + N) (sort_key (\<lambda>(i, r). r) (map (\<lambda>i. let xs = M i in (i, sum_list' p (map abs xs) - fold max (map abs xs) 0)) Ds)));
      _ = ()
    in (\<lambda>i (xs::real list). i \<notin> set ortho_indices))"

definition "reduce_aforms prec C X = summarize_aforms (prec) C (degree_aforms X) X"

definition "pdevs_of_real x = (x, zero_pdevs)"

definition aform_inf_inner where "aform_inf_inner prec X n =
  (case inner_aforms' (prec) X (map pdevs_of_real n) of
    Some Xn \<Rightarrow> Inf_aform' (prec) (hd Xn))"
definition aform_sup_inner where "aform_sup_inner prec X n =
  (case inner_aforms' (prec) X (map pdevs_of_real n) of
    Some Xn \<Rightarrow> Sup_aform' (prec) (hd Xn))"

text \<open>cannot fail\<close>

lemma approx_un_ne_None: "approx_un p (\<lambda>ivl. Some (f ivl)) (Some r) \<noteq> None"
  by (auto simp: approx_un_def split_beta')

lemma approx_un_eq_Some:
  "approx_un p (\<lambda>ivl. Some (f ivl)) (Some r) = Some s \<longleftrightarrow>
  s = ivl_err (real_interval (f (ivl_of_aform_err p r)))"
  using approx_un_ne_None
  by (auto simp: approx_un_def split_beta')

lemma is_float_uminus:
  "is_float aa \<Longrightarrow> is_float (- aa)"
  by (auto simp: is_float_def)

lemma is_float_uminus_iff[simp]:
  "is_float (- aa) = is_float aa"
  using is_float_uminus[of aa] is_float_uminus[of "-aa"]
  by (auto simp: is_float_def)

lemma is_float_simps[simp]:
  "is_float 0"
  "is_float 1"
  "is_float (real_of_float x)"
  "is_float (truncate_down p X)"
  "is_float (truncate_up p X)"
  "is_float (eucl_truncate_down p X)"
  "is_float (eucl_truncate_up p X)"
  by (auto simp: is_float_def eucl_truncate_down_def eucl_truncate_up_def truncate_down_def truncate_up_def)

lemma is_float_sum_list'[simp]:
  "is_float (sum_list' p xs)"
  by (induction xs) (auto simp: is_float_def)

lemma is_float_inverse_aform': "is_float (fst (fst (inverse_aform' p X)))"
  unfolding inverse_aform'_def
  by (simp add: Let_def trunc_bound_eucl_def)

lemma is_float_min_range:
  "min_range_antimono p F D E X Y = Some ((a, b), c) \<Longrightarrow> is_float a"
  "min_range_antimono p F D E X Y = Some ((a, b), c) \<Longrightarrow> is_float c"
  "min_range_mono p F D E X Y = Some ((a, b), c) \<Longrightarrow> is_float a"
  "min_range_mono p F D E X Y = Some ((a, b), c) \<Longrightarrow> is_float c"
  by (auto simp: min_range_antimono_def min_range_mono_def Let_def bind_eq_Some_conv
      prod_eq_iff trunc_bound_eucl_def
      mid_err_def affine_unop_def split: prod.splits)

lemma is_float_ivl_err:
  assumes "ivl_err x = ((a, b), c)" "is_float (lower x)" "is_float (upper x)"
  shows "is_float a" "is_float c"
proof -
  define x1 where "x1 = lower x"
  define x2 where "x2 = upper x"
  have "a = (x1 + x2) / 2" "c = (x2 - x1) / 2"
    using assms by (auto simp: ivl_err_def x1_def x2_def)
  moreover have "(x1 + x2) / 2 \<in> float" "(x2 - x1) / 2 \<in> float"
    using assms
    by (auto simp: is_float_def x1_def x2_def)
  ultimately show "is_float a" "is_float c"
    unfolding is_float_def by blast+
qed

lemma is_float_trunc_bound_eucl[simp]:
  "is_float (fst (trunc_bound_eucl p X))"
  by (auto simp: trunc_bound_eucl_def Let_def)

lemma add_eq_times_2_in_float: "a + b = c * 2 \<Longrightarrow> is_float a \<Longrightarrow> is_float b \<Longrightarrow> is_float c"
proof goal_cases
  case 1
  then have "c = (a + b) / 2"
    by simp
  also have "\<dots> \<in> float" using 1(3,2) by (simp add: is_float_def)
  finally show ?case by (simp add: is_float_def)
qed


lemma approx_floatarith_Some_is_float:
  "approx_floatarith p fa XS = Some ((a, b), ba) \<Longrightarrow>
  list_all (\<lambda>((a, b), c). is_float a \<and> is_float c) XS \<Longrightarrow>
  is_float a \<and> is_float ba"
  apply (induction fa arbitrary: a b ba)
  subgoal by (auto simp: bind_eq_Some_conv add_aform'_def Let_def )
  subgoal by (auto simp: bind_eq_Some_conv uminus_aform_def Let_def)
  subgoal by (auto simp: bind_eq_Some_conv mult_aform'_def Let_def )
  subgoal by (auto simp: bind_eq_Some_conv inverse_aform_err_def map_aform_err_def
        prod_eq_iff is_float_inverse_aform'
        acc_err_def aform_to_aform_err_def aform_err_to_aform_def inverse_aform_def
        Let_def split: if_splits)
  subgoal by (auto simp: bind_eq_Some_conv cos_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv arctan_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal apply (auto simp: bind_eq_Some_conv uminus_aform_def Let_def is_float_min_range
        is_float_ivl_err set_of_eq real_interval_abs
        split: if_splits prod.splits)
    apply (metis is_float_ivl_err(1) is_float_simps(3) lower_real_interval real_interval_abs upper_real_interval)
    by (metis is_float_ivl_err(2) is_float_simps(3) lower_real_interval real_interval_abs upper_real_interval)
  subgoal by (auto simp: bind_eq_Some_conv max_aform_err_def Let_def is_float_min_range
        is_float_ivl_err max_def
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv min_aform_err_def Let_def is_float_min_range
        is_float_ivl_err min_def
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv arctan_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv sqrt_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv exp_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv powr_aform_err_def approx_bin_def
        exp_aform_err_def Let_def is_float_min_range
        is_float_ivl_err mult_aform'_def
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv ln_aform_err_def Let_def is_float_min_range
        is_float_ivl_err
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv power_aform_err_def Let_def is_float_min_range
        is_float_ivl_err mid_err_def dest!: add_eq_times_2_in_float
        split: if_splits prod.splits)
  subgoal by (auto simp: bind_eq_Some_conv cos_aform_err_def Let_def is_float_min_range
        approx_un_def is_float_ivl_err
        split: if_splits)
  subgoal by (auto simp: bind_eq_Some_conv cos_aform_err_def Let_def is_float_min_range
        list_all_length
        split: if_splits)
  subgoal by (auto simp: bind_eq_Some_conv num_aform_def Let_def)
  done

lemma plain_floatarith_not_None:
  assumes "plain_floatarith N fa" "N \<le> length XS"
    "list_all (\<lambda>((a, b), c). is_float a \<and> is_float c) XS"
  shows "approx_floatarith p fa XS \<noteq> None"
  using assms
  by (induction fa)
    (auto simp: Let_def split_beta' approx_un_eq_Some prod_eq_iff
      approx_floatarith_Some_is_float)

lemma plain_floatarith_slp_not_None:
  assumes "\<And>fa. fa \<in> set fas \<Longrightarrow> plain_floatarith N fa" "N \<le> length XS"
    "list_all (\<lambda>((a, b), c). is_float a \<and> is_float c) XS"
  shows "approx_slp p fas XS \<noteq> None"
  using assms 
  apply (induction fas arbitrary: XS)
  subgoal by simp
  subgoal for fa fas XS
    using plain_floatarith_not_None[of N fa XS p]
    by (auto simp: Let_def split_beta' approx_un_eq_Some prod_eq_iff
      bind_eq_Some_conv approx_floatarith_Some_is_float)
  done

lemma plain_floatarithE:
  assumes "plain_floatarith N fa" "N \<le> length XS"
    "list_all (\<lambda>((a, b), c). is_float a \<and> is_float c) XS"
  obtains R where "approx_floatarith p fa XS = Some R"
  using plain_floatarith_not_None[OF assms]
  by force

lemma approx_slp_outer_eq_None_iff:
  "approx_slp_outer p a b XS = None \<longleftrightarrow>
    approx_slp p b ((map (\<lambda>x. (x, 0)) XS)) = None"
  by (auto simp: approx_slp_outer_def Let_def bind_eq_None_conv)

lemma approx_slp_sing_eq_None_iff:
  "approx_slp p [b] xs = None \<longleftrightarrow> approx_floatarith p b xs = None"
  by (auto simp: approx_slp_outer_def Let_def bind_eq_None_conv)

lemma plain_inner_floatariths:
  "plain_floatarith N (inner_floatariths xs ys)"
  if "list_all (plain_floatarith N) xs"  "list_all (plain_floatarith N) ys"
  using that
  by (induction xs ys rule: inner_floatariths.induct) auto

lemma aiN: "approx_floatarith p (inner_floatariths xs ys) zs \<noteq> None"
  if "\<And>x. x \<in> set xs \<Longrightarrow> approx_floatarith p x zs \<noteq> None"
  and "\<And>x. x \<in> set ys \<Longrightarrow> approx_floatarith p x zs \<noteq> None"
  using that
  apply (induction xs ys rule: inner_floatariths.induct)
  apply (auto simp: Let_def bind_eq_Some_conv)
  by (metis old.prod.exhaust)

lemma aiVN: "approx_floatarith p
        (inner_floatariths (map floatarith.Var [0..<length a])
          (map floatarith.Var [length a..<length a + length b]))
        (map (\<lambda>x. (x, 0)) a @ map (\<lambda>x. (x, 0)) b) \<noteq> None"
  by (rule aiN) (auto simp: nth_append)

lemma iaN: "inner_aforms' p a b \<noteq> None"
  unfolding inner_aforms'_def Let_def approx_slp_outer_def
  using aiVN[of p a b]
  by (auto simp: Let_def bind_eq_Some_conv)

definition "support_aform prec b X = (let ia = inner_aform X b in fst X \<bullet> b + tdev' (prec) (snd ia))"

definition "width_aforms prec X =
  (let t = tdev' (prec) ((abssum_of_pdevs_list (map snd X))) in t)"

definition "inf_aforms prec xs = map (Inf_aform' (prec)) xs"
definition "sup_aforms prec xs = map (Sup_aform' (prec)) xs"

definition "fresh_index_aforms xs = Max (insert 0 (degree_aform ` set xs))"

definition "independent_aforms x env = (msum_aform (fresh_index_aforms env) (0, zero_pdevs) x#env)"

definition "aform_form_ivl prec form xs =
  dRETURN (approx_form prec form (ivls_of_aforms prec xs) [])"
definition "aform_form prec form xs =
  dRETURN (approx_form_aform prec form xs)"
definition "aform_slp prec n slp xs =
  dRETURN (approx_slp_outer prec n slp xs)"
definition
  "aform_isFDERIV prec n ns fas xs =
    dRETURN (isFDERIV_approx prec n ns fas (ivls_of_aforms prec xs))"

definition aform_rel_internal: "aform_rel R = br Affine top O \<langle>R\<rangle>set_rel"
lemma aform_rel_def: "\<langle>rnv_rel\<rangle>aform_rel = br Affine top"
  unfolding relAPP_def
  by (auto simp: aform_rel_internal)
definition "aforms_rel = br Joints top"

definition aform_rell :: "((real \<times> real pdevs) list \<times> real list set) set"
where "aform_rell = aforms_rel"

definition aforms_relp_internal: "aforms_relp R = aforms_rel O \<langle>R\<rangle>set_rel"
lemma aforms_relp_def: "\<langle>R\<rangle>aforms_relp = aforms_rel O \<langle>R\<rangle>set_rel"
  by (auto simp: aforms_relp_internal relAPP_def)

definition "product_aforms x y = x @ msum_aforms (degree_aforms (x)) (replicate (length y) (0, zero_pdevs)) y"

lemma
  eucl_of_list_mem_eucl_of_list_aform:
  assumes "x \<in> Joints a"
  assumes "length a = DIM('a::executable_euclidean_space)"
  shows "eucl_of_list x \<in> Affine (eucl_of_list_aform a::'a aform)"
  using assms
  by (auto simp: Joints_def Affine_def valuate_def eucl_of_list_aform_def
      aform_val_def pdevs_val_sum_pdevs inner_simps eucl_of_list_inner
      intro!: euclidean_eqI[where 'a='a])

lemma
  in_image_eucl_of_list_eucl_of_list_aform:
  assumes "length x = DIM('a::executable_euclidean_space)" "xa \<in> Affine (eucl_of_list_aform x::'a aform)"
  shows "xa \<in> eucl_of_list ` Joints x"
  using assms
  by (auto intro!: nth_equalityI image_eqI[where x="list_of_eucl xa"]
      simp: aform_val_def eucl_of_list_aform_def Affine_def valuate_def Joints_def
      inner_simps pdevs_val_sum_pdevs eucl_of_list_inner)

lemma
  eucl_of_list_image_Joints:
  assumes "length x = DIM('a::executable_euclidean_space)"
  shows "eucl_of_list ` Joints x = Affine (eucl_of_list_aform x::'a aform)"
  using assms
  by (auto intro!: eucl_of_list_mem_eucl_of_list_aform
      in_image_eucl_of_list_eucl_of_list_aform)

definition "aform_ops =
\<lparr>
  appr_of_ivl = aforms_of_ivls,
  product_appr = product_aforms,
  msum_appr = msum_aforms',
  inf_of_appr = \<lambda>optns. inf_aforms (precision optns),
  sup_of_appr = \<lambda>optns. sup_aforms (precision optns),
  split_appr = split_aforms_largest_uncond_take,
  appr_inf_inner = \<lambda>optns. aform_inf_inner (precision optns),
  appr_sup_inner = \<lambda>optns. aform_sup_inner (precision optns),
  inter_appr_plane = \<lambda>optns xs sctn. inter_aform_plane_lv (length xs) (precision optns) xs sctn,
  reduce_appr = \<lambda>optns. reduce_aforms (precision optns),
  width_appr = \<lambda>optns. width_aforms (precision optns),
  approx_slp_dres = \<lambda>optns. aform_slp (precision optns),
  approx_euclarithform = \<lambda>optns. aform_form (precision optns),
  approx_isFDERIV = \<lambda>optns. aform_isFDERIV  (precision optns)
\<rparr>"

lemma Affine_eq_permI:
  assumes "fst X = fst Y"
  assumes "map snd (list_of_pdevs (snd X)) <~~> map snd (list_of_pdevs (snd Y))" (is "?perm X Y")
  shows "Affine X = Affine Y"
proof -
  {
    fix X Y and e::"nat \<Rightarrow> real"
    assume perm: "?perm X Y" and e: "e \<in> funcset UNIV {- 1..1}"
    from pdevs_val_of_list_of_pdevs2[OF e, of "snd X"]
    obtain e' where e':
      "pdevs_val e (snd X) = pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs (snd X))))"
      "e' \<in> funcset UNIV {- 1..1}"
      by auto
    note e'(1)
    also from pdevs_val_perm[OF perm e'(2)]
    obtain e'' where e'':
      "e'' \<in> funcset UNIV {- 1..1}"
      "pdevs_val e' (pdevs_of_list (map snd (list_of_pdevs (snd X)))) =
      pdevs_val e'' (pdevs_of_list (map snd (list_of_pdevs (snd Y))))"
      by auto
    note e''(2)
    also from pdevs_val_of_list_of_pdevs[OF e''(1), of "snd Y", simplified]
    obtain e''' where e''':
      "pdevs_val e'' (pdevs_of_list (map snd (list_of_pdevs (snd Y)))) = pdevs_val e''' (snd Y)"
      "e''' \<in> funcset UNIV {- 1..1}"
      by auto
    note e'''(1)
    finally have "\<exists>e' \<in> funcset UNIV {-1 .. 1}. pdevs_val e (snd X) = pdevs_val e' (snd Y)"
      using e'''(2) by auto
  } note E = this
  note e1 = E[OF assms(2)]
    and e2 = E[OF perm_sym[OF assms(2)]]
  show ?thesis
    by (auto simp: Affine_def valuate_def aform_val_def assms dest: e1 e2)
qed

context includes autoref_syntax begin

lemma aform_of_ivl_refine: "x \<le> y \<Longrightarrow> (aform_of_ivl x y, atLeastAtMost x y) \<in> \<langle>rnv_rel\<rangle>aform_rel"
  by (auto simp: aform_rel_def br_def Affine_aform_of_ivl)

lemma aforms_of_ivl_leI1:
  fixes en::real
  assumes "-1 \<le> en" "xsn \<le> ysn"
  shows "xsn \<le> (xsn + ysn) / 2 + (ysn - xsn) * en / 2"
proof -
  have "xsn * (1 + en) \<le> ysn * (1 + en)"
    using assms mult_right_mono by force
  then show ?thesis
    by (auto simp: algebra_simps divide_simps)
qed

lemma aforms_of_ivl_leI2:
  fixes en::real
  assumes "1 \<ge> en" "xsn \<le> ysn"
  shows "(xsn + ysn) / 2 + (ysn - xsn) * en / 2 \<le> ysn"
proof -
  have "xsn * (1 - en) \<le> ysn * (1 - en)"
    using assms mult_right_mono by force
  then show ?thesis
    by (auto simp: algebra_simps divide_simps)
qed

lemma Joints_aforms_of_ivlsD1:
  "zs \<in> Joints (aforms_of_ivls xs ys) \<Longrightarrow> list_all2 (\<le>) xs ys \<Longrightarrow> list_all2 (\<le>) xs zs"
  by (auto simp: Joints_def valuate_def aforms_of_ivls_def aform_val_def Pi_iff
      list_all2_conv_all_nth intro!: list_all2_all_nthI aforms_of_ivl_leI1)

lemma Joints_aforms_of_ivlsD2:
  "zs \<in> Joints (aforms_of_ivls xs ys) \<Longrightarrow> list_all2 (\<le>) xs ys \<Longrightarrow> list_all2 (\<le>) zs ys"
  by (auto simp: Joints_def valuate_def aforms_of_ivls_def aform_val_def Pi_iff
      list_all2_conv_all_nth intro!: list_all2_all_nthI aforms_of_ivl_leI2)

lemma aforms_of_ivls_refine:
  "list_all2 (\<le>) xrs yrs \<Longrightarrow>
       (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
       (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow> (aforms_of_ivls xri yri, lv_ivl xrs yrs) \<in> aforms_rel"
  apply (auto simp: aforms_rel_def br_def list_all2_lengthD lv_ivl_def
      Joints_aforms_of_ivlsD1 Joints_aforms_of_ivlsD2 intro!: aforms_of_ivls)
  subgoal by (simp add: list_all2_conv_all_nth)
  subgoal by (simp add: list_all2_conv_all_nth)
  done

lemma degrees_zero_pdevs[simp]: "degrees (replicate n zero_pdevs) = 0"
  by (auto simp: degrees_def intro!: Max_eqI)

lemma Joints_product_aforms:
  "Joints (product_aforms a b) = product_listset (Joints a) (Joints b)"
  apply (auto simp: Joints_def valuate_def product_listset_def product_aforms_def
      aform_vals_def[symmetric] aform_val_msum_aforms)
  subgoal for e
    apply (rule image_eqI[where
          x="(aform_vals e a,
              List.map2 (+) (aform_vals e (replicate (length b) (0, zero_pdevs))) (aform_vals (\<lambda>i. e (i + degree_aforms a)) b))"])
     apply (auto simp: split_beta')
    apply (auto simp: aform_vals_def intro!: nth_equalityI image_eqI[where x="\<lambda>i. e (i + degree_aforms a)"])
    done
  subgoal for e1 e2
    apply (rule image_eqI[where x="\<lambda>i. if i < degree_aforms a then e1 i else e2 (i - degree_aforms a)"])
     apply (auto simp: aform_vals_def aform_val_def Pi_iff
        intro!: nth_equalityI pdevs_val_degree_cong)
    subgoal premises prems for x xs k
    proof -
      from prems
      have "degree xs \<le> degree_aforms a"
        by (auto simp: degrees_def Max_gr_iff)
      then show ?thesis using prems by auto
    qed
    done
  done

lemma product_aforms_refine:
  "(product_aforms, product_listset) \<in> aforms_rel \<rightarrow> aforms_rel \<rightarrow> aforms_rel"
  by (auto simp: aforms_rel_def br_def Joints_product_aforms)

lemma mem_lv_rel_set_rel_iff:
  fixes z::"'a::executable_euclidean_space set"
  shows "(y, z) \<in> \<langle>lv_rel\<rangle>set_rel \<longleftrightarrow> (z = eucl_of_list ` y \<and> (\<forall>x \<in> y. length x = DIM('a)))"
  unfolding lv_rel_def
  by (auto simp: set_rel_def br_def)

lemma eucl_of_list_mem_lv_rel: "length x = DIM('a::executable_euclidean_space) \<Longrightarrow>
    (x, eucl_of_list x::'a) \<in> lv_rel"
  unfolding lv_rel_def
  by (auto simp:  br_def)

lemma
  mem_Joints_msum_aforms'I:
  "a \<in> Joints x \<Longrightarrow> b \<in> Joints y \<Longrightarrow> List.map2 (+) a b \<in> Joints (msum_aforms' x y)"
  by (auto simp: Joints_msum_aforms degrees_def)

lemma
  mem_Joints_msum_aforms'E:
  assumes "xa \<in> Joints (msum_aforms' x y)" 
  obtains a b where "xa = List.map2 (+) a b" "a \<in> Joints x" "b \<in> Joints y"
  using assms
  by (auto simp: Joints_msum_aforms degrees_def)

lemma msum_aforms'_refine_raw:
  shows "(msum_aforms' x y, {List.map2 (+) a b|a b. a \<in> Joints x \<and> b \<in> Joints y}) \<in> aforms_rel"
  unfolding aforms_rel_def br_def
  by (safe elim!: mem_Joints_msum_aforms'E intro!: mem_Joints_msum_aforms'I) (auto simp: Joints_imp_length_eq)

lemma aforms_relD: "(a, b) \<in> aforms_rel \<Longrightarrow> b = Joints a"
  by (auto simp: aforms_rel_def br_def)

lemma msum_aforms'_refine:
  "(msum_aforms', \<lambda>xs ys. {List.map2 (+) x y |x y. x \<in> xs \<and> y \<in> ys}) \<in> aforms_rel \<rightarrow> aforms_rel \<rightarrow> aforms_rel"
  by (safe dest!: aforms_relD intro!: msum_aforms'_refine_raw)

lemma length_inf_aforms[simp]: "length (inf_aforms optns x) = length x"
  and length_sup_aforms[simp]: "length (sup_aforms optns x) = length x"
  by (auto simp: inf_aforms_def sup_aforms_def)

lemma inf_aforms_refine:
  "(xi, x) \<in> aforms_rel \<Longrightarrow> length xi = d \<Longrightarrow> (RETURN (inf_aforms optns xi), Inf_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
  unfolding o_def
  apply (auto simp: br_def aforms_rel_def mem_lv_rel_set_rel_iff nres_rel_def Inf_specs_def
      intro!: RETURN_SPEC_refine)
  unfolding lv_rel_def
  by (auto simp: aforms_rel_def br_def Joints_imp_length_eq
      eucl_of_list_inner inf_aforms_def nth_in_AffineI
      intro!: Inf_aform'_Affine_le list_all2_all_nthI)

lemma sup_aforms_refine:
  "(xi, x) \<in> aforms_rel \<Longrightarrow> length xi = d \<Longrightarrow> (RETURN (sup_aforms optns xi), Sup_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
  unfolding o_def
  apply (auto simp: aforms_relp_def mem_lv_rel_set_rel_iff nres_rel_def Sup_specs_def
      intro!: RETURN_SPEC_refine)
  unfolding lv_rel_def
  by (auto simp: aforms_rel_def br_def Joints_imp_length_eq
      eucl_of_list_inner sup_aforms_def nth_in_AffineI
      intro!: Sup_aform'_Affine_ge list_all2_all_nthI)

lemma nres_of_THE_DRES_le:
  assumes "\<And>v. x = Some v \<Longrightarrow> RETURN v \<le> y"
  shows "nres_of (THE_DRES x) \<le> y"
  using assms by (auto simp: THE_DRES_def split: option.split)

lemma degree_le_fresh_index: "a \<in> set A \<Longrightarrow> degree_aform a \<le> fresh_index_aforms A"
  by (auto simp: fresh_index_aforms_def intro!: Max_ge)

lemma zero_in_JointsI: "xs \<in> Joints XS \<Longrightarrow> z = (0, zero_pdevs) \<Longrightarrow> 0 # xs \<in> Joints (z # XS)"
  by (auto simp: Joints_def valuate_def)

lemma cancel_nonneg_pos_add_multI: "0 \<le> c + c * x"
  if "c \<ge> 0" "1 + x \<ge> 0"
  for c x::real
proof -
  have "0 \<le> c + c * x \<longleftrightarrow> 0 \<le> c * (1 + x)" by (auto simp: algebra_simps)
  also have "\<dots> \<longleftrightarrow> 0 \<le> 1 + x"
    using that
    by (auto simp: zero_le_mult_iff)
  finally show ?thesis 
    using that by simp
qed
   
lemma Joints_map_split_aform:
  fixes x::"real aform list"
  shows "Joints x \<subseteq> Joints (map (\<lambda>a. fst (split_aform a i)) x) \<union> Joints (map (\<lambda>b. snd (split_aform b i)) x)"
  unfolding subset_iff
  apply (intro allI impI)
proof goal_cases
  case (1 xs)
  then obtain e where e: "e \<in> funcset UNIV {-1 .. 1}" "xs = map (aform_val e) x"
    by (auto simp: Joints_def valuate_def)
  consider "e i \<ge> 0" | "e i \<le> 0" by arith
  then show ?case
  proof cases
    case 1
    let ?e = "e(i:= 2 * e i - 1)"
    note e(2)
    also
    have "map (aform_val e) x = map (aform_val ?e) (map (\<lambda>b. snd (split_aform b i)) x)"
      by (auto simp: aform_val_def split_aform_def Let_def divide_simps algebra_simps)
    also have "\<dots> \<in> Joints (map (\<lambda>b. snd (split_aform b i)) x)"
      using e \<open>0 \<le> e i\<close>
      by (auto simp: Joints_def valuate_def Pi_iff intro!: image_eqI[where x = ?e])
    finally show ?thesis by simp
  next
    case 2
    let ?e = "e(i:= 2 * e i + 1)"
    note e(2)
    also
    have "map (aform_val e) x = map (aform_val ?e) (map (\<lambda>b. fst (split_aform b i)) x)"
      by (auto simp: aform_val_def split_aform_def Let_def divide_simps algebra_simps)
    also have "\<dots> \<in> Joints (map (\<lambda>b. fst (split_aform b i)) x)"
      using e \<open>0 \<ge> e i\<close>
      by (auto simp: Joints_def valuate_def Pi_iff real_0_le_add_iff
          intro!: image_eqI[where x = ?e] cancel_nonneg_pos_add_multI)
    finally show ?thesis by simp
  qed
qed


lemma split_aforms_lemma:
  fixes x::"real aform list"
  assumes "(x, y) \<in> aforms_rel"
  assumes "z \<subseteq> y"
  assumes "l = (length x)"
  shows "\<exists>a b. (split_aforms x i, a, b)
     \<in> aforms_rel \<times>\<^sub>r aforms_rel \<and> env_len a l \<and> env_len b l \<and> z \<subseteq> a \<union> b"
  using assms
  apply (auto simp: split_aforms_def o_def)
  apply (rule exI[where x="Joints (map (\<lambda>x. fst (split_aform x i)) x)"])
  apply auto
  subgoal by (auto intro!: brI simp: aforms_rel_def)
  apply (rule exI[where x="Joints (map (\<lambda>x. snd (split_aform x i)) x)"])
  apply (rule conjI)
  subgoal by (auto intro!: brI simp: aforms_rel_def)
  subgoal
    using Joints_map_split_aform[of x i]
    by (auto simp: br_def aforms_rel_def env_len_def Joints_imp_length_eq)
  done

lemma length_summarize_pdevs_list[simp]:
  "length (summarize_pdevs_list a b c d) = length d"
  by (auto simp: summarize_pdevs_list_def)

lemma length_summarize_aforms[simp]:
  "length (summarize_aforms a b e d) = length d"
  by (auto simp: summarize_aforms_def Let_def)

lemma
  split_aform_largest_take_refine:
  "(ni, n) \<in> nat_rel \<Longrightarrow>
       (xi::real aform list, x) \<in> aforms_rel \<Longrightarrow>
       length xi = d \<Longrightarrow> (RETURN (split_aforms_largest_uncond_take ni xi), split_spec_params d n x) \<in> \<langle>aforms_rel \<times>\<^sub>r aforms_rel\<rangle>nres_rel"
  apply (auto simp: split_spec_params_def nres_rel_def aforms_relp_def mem_lv_rel_set_rel_iff
      split_aforms_largest_uncond_take_def Let_def comps
      split: prod.splits
      intro!: RETURN_SPEC_refine)
  apply (rule split_aforms_lemma)
  by (auto simp add: aforms_rel_def)

lemma aform_val_pdevs_of_real[simp]: "aform_val e (pdevs_of_real x) = x"
  by (auto simp: pdevs_of_real_def)

lemma degree_aform_pdevs_of_real[simp]: "degree_aform (pdevs_of_real x) = 0"
  by (auto simp: pdevs_of_real_def)

lemma interpret_floatarith_inner_eq:
  shows "interpret_floatarith (inner_floatariths xs ys) vs =
    (\<Sum>(x, y) \<leftarrow> (zip xs ys). (interpret_floatarith x vs) * (interpret_floatarith y vs))"
  by (induction xs ys rule: inner_floatariths.induct) auto

lemma approx_slp_outer_sing:
  "approx_slp_outer p (Suc 0) [fa] XS = Some R \<longleftrightarrow> (\<exists>Y.
  approx_floatarith p fa (map (\<lambda>x. (x, 0)) XS) = Some Y \<and>
       [aform_err_to_aform Y (max (degree_aforms XS) (degree_aform_err Y))] = R)"
  by (auto simp: approx_slp_outer_def bind_eq_Some_conv degrees_def)

lemma aforms_err_aform_valsI:
  assumes "vs = aform_vals e XS"
  shows "vs \<in> aforms_err e (map (\<lambda>x. (x, 0)) (XS))"
    by (auto simp: assms aforms_err_def o_def aform_err_def aform_vals_def)


lemma aform_val_degree_cong:
  "b = d \<Longrightarrow> (\<And>i. i < degree_aform d \<Longrightarrow> a i = c i) \<Longrightarrow> aform_val a b = aform_val c d"
  by (auto simp: aform_val_def intro!: pdevs_val_degree_cong)

lemma mem_degree_aformD: "x \<in> set XS \<Longrightarrow> degree_aform x \<le> degree_aforms XS"
  by (auto simp: degrees_def)
lemma degrees_append_leD1: "(degrees xs) \<le> degrees (xs @ ys)"
  unfolding degrees_def
  by (rule Max_mono) (auto simp: degrees_def min_def max_def Max_ge_iff image_Un Max_gr_iff)

lemma inner_aforms':
  assumes "xs \<in> Joints XS"
  assumes "inner_aforms' p XS (map pdevs_of_real rs) = Some R"
  shows "(\<Sum>(x, y) \<leftarrow> (zip xs rs). x * y) \<in> Affine (hd R)" (is ?th1) "length R = 1" (is ?th2)
proof -
  from assms obtain e where "e \<in> funcset UNIV {-1 .. 1}" "xs = aform_vals e XS"
    by (auto simp: Joints_def valuate_def aform_vals_def)
  then have e: "xs @ rs = aform_vals e (XS @ map pdevs_of_real rs)"
    "xs @ rs \<in> Joints (XS @ map pdevs_of_real rs)"
    "length xs = length XS"
    "e \<in> funcset UNIV {- 1..1}"
    by (auto simp: aform_vals_def o_def degrees_def Joints_def valuate_def)
  have "approx_slp_outer p (Suc 0)
     ([inner_floatariths (map floatarith.Var [0..<length XS])
         (map floatarith.Var [length XS..<length XS + length rs])])
     (XS @ map pdevs_of_real rs) =
    Some R"
    using assms(2)
    by (auto simp: inner_aforms'_def)
  then obtain Y where Y:
    "approx_floatarith p
       (inner_floatariths (map floatarith.Var [0..<length XS])
         (map floatarith.Var [length XS..<length XS + length rs]))
       (map (\<lambda>x. (x, 0)) (XS @ map pdevs_of_real rs)) =
      Some Y"
    "R = [aform_err_to_aform Y (max (degree_aforms (XS @ map pdevs_of_real rs)) (degree_aform_err Y))]"
    unfolding approx_slp_outer_sing by auto
  let ?m = "(max (degree_aforms (XS @ map pdevs_of_real rs)) (degree_aform_err Y))"
  from approx_floatarith_Elem[OF Y(1) e(4) aforms_err_aform_valsI[OF e(1)]]
  have "interpret_floatarith
     (inner_floatariths (map floatarith.Var [0..<length XS]) (map floatarith.Var [length XS..<length XS + length rs]))
     (xs @ rs)
    \<in> aform_err e Y" "degree_aform_err Y \<le> max (degree_aforms (XS @ map pdevs_of_real rs)) (degree_aform_err Y)"
    by auto
  from aform_err_to_aformE[OF this] obtain err where err:
    "interpret_floatarith
           (inner_floatariths (map floatarith.Var [0..<length XS])
             (map floatarith.Var [length XS..<length XS + length rs]))
           (xs @ rs) =
          aform_val (e(max (degree_aforms (XS @ map pdevs_of_real rs)) (degree_aform_err Y) := err))
           (aform_err_to_aform Y (max (degree_aforms (XS @ map pdevs_of_real rs)) (degree_aform_err Y)))"
    "- 1 \<le> err" "err \<le> 1"
    by auto
  let ?e' = "(e(max (degrees (map snd XS @ map (snd \<circ> pdevs_of_real) rs)) (degree_aform_err Y) := err))"
  from e(1) have e': "xs @ rs = aform_vals ?e' (XS @ map pdevs_of_real rs)"
    apply (auto simp: aform_vals_def intro!: aform_val_degree_cong)
     apply (frule mem_degree_aformD)
     apply (frule le_less_trans[OF degrees_append_leD1])
     apply (auto simp: o_def)
    done
  from err have "interpret_floatarith
           (inner_floatariths (map floatarith.Var [0..<length XS])
             (map floatarith.Var [length XS..<length XS + length rs]))
           (xs @ rs)#xs@rs \<in> Joints (R @ XS @ map pdevs_of_real rs)"
    using e(1,3,4) e'
    apply (auto simp: valuate_def Joints_def
      intro!: nth_equalityI
        image_eqI[where x="?e'"])
     apply (simp add: Y aform_vals_def; fail)
    apply (simp add: Y o_def)
    apply (simp add: nth_append nth_Cons)
    apply (auto split: nat.splits simp: nth_append nth_Cons aform_vals_def)
    done
  then have "(\<Sum>(x, y)\<leftarrow>zip (map floatarith.Var [0..<length XS])
                (map floatarith.Var
                  [length XS..<
                   length XS + length rs]). interpret_floatarith x (xs @ rs) * interpret_floatarith y (xs @ rs)) #
    xs @ rs
    \<in> Joints (R @ XS @ map pdevs_of_real rs)"
    apply (subst (asm)interpret_floatarith_inner_eq )
    apply (auto simp:  )
    done
  also have "(\<Sum>(x, y)\<leftarrow>zip (map floatarith.Var [0..<length XS])
                (map floatarith.Var
                  [length XS..<
                   length XS + length rs]). interpret_floatarith x (xs @ rs) * interpret_floatarith y (xs @ rs)) =
    (\<Sum>(x, y)\<leftarrow>zip xs rs. x * y)"
    by (auto simp: sum_list_sum_nth assms e(3) nth_append intro!: sum.cong)
  finally show ?th1 ?th2
    by (auto simp: Affine_def valuate_def Joints_def Y)
qed

lemma inner_aforms'_inner_lv_rel:
  "(a, a') \<in> aforms_rel \<Longrightarrow>
       inner_aforms' prec a (map pdevs_of_real a'a) = Some R \<Longrightarrow>
       x \<in> a' \<Longrightarrow> inner_lv_rel x a'a \<in> Affine (hd R)"
  unfolding mem_lv_rel_set_rel_iff
  unfolding lv_rel_def aforms_rel_def
  apply (auto simp: br_def)
  apply (subst arg_cong2[where f="(\<in>)", OF _ refl])
  defer
   apply (rule inner_aforms')
     apply (auto simp: br_def Joints_imp_length_eq inner_lv_rel_def)
  done

lemma aform_inf_inner_refine:
  "(RETURN o2 aform_inf_inner optns, Inf_inners) \<in> aforms_rel \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: aforms_relp_def nres_rel_def Inf_inners_def aform_inf_inner_def[abs_def] comp2_def
      iaN
      intro!: Inf_aform'_Affine_le inner_aforms'_inner_lv_rel
      split: option.splits list.splits)

lemma aform_sup_inner_refine:
  "(RETURN o2 aform_sup_inner optns, Sup_inners) \<in> aforms_rel \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: aforms_relp_def nres_rel_def Sup_inners_def aform_sup_inner_def[abs_def] comp2_def
      iaN
      intro!: Sup_aform'_Affine_ge inner_aforms'_inner_lv_rel
      split: option.splits list.splits)

lemma lv_aforms_rel_comp_br_Affine_le: "lv_aforms_rel O br Affine top \<subseteq> \<langle>lv_rel\<rangle>aforms_relp"
  apply (auto simp: lv_aforms_rel_def aforms_relp_def br_def)
  apply (rule relcompI)
   apply (auto simp: aforms_rel_def intro!: brI )
  by (auto simp: mem_lv_rel_set_rel_iff Joints_imp_length_eq
      intro!: eucl_of_list_mem_eucl_of_list_aform intro!: in_image_eucl_of_list_eucl_of_list_aform)

lemma bijective_lv_rel[relator_props]: "bijective lv_rel"
  unfolding lv_rel_def bijective_def
  apply (auto simp: br_def)
  by (metis eucl_of_list_inj)

lemma sv_lv_rel_inverse[relator_props]: "single_valued (lv_rel\<inverse>)"
  using bijective_lv_rel
  by (rule bijective_imp_sv)

lemma list_of_eucl_image_lv_rel_inverse:
  "(x, list_of_eucl ` x) \<in> \<langle>lv_rel\<inverse>\<rangle>set_rel"
  unfolding set_rel_sv[OF sv_lv_rel_inverse]
  apply (auto simp: )
    apply (rule ImageI)
     apply (rule converseI)
     apply (rule lv_relI)
     apply auto
   apply (rule image_eqI)
    prefer 2 apply assumption
  unfolding lv_rel_def
   apply (auto simp: br_def)
  subgoal for y
    apply (rule exI[where x="list_of_eucl y"])
    apply auto
    done
  done

lemma lv_rel_comp_lv_rel_inverse:
  "((lv_rel::(_\<times>'a::executable_euclidean_space) set) O lv_rel\<inverse>) = {(x, y). x = y \<and> length x = DIM('a)}"
  apply (auto simp: intro!: lv_relI)
  unfolding lv_rel_def
  by (auto simp: br_def intro!: eucl_of_list_inj)

lemma inter_aform_plane_refine_aux:
  "d = CARD('n::enum) \<Longrightarrow>
  (xi, x) \<in> aforms_rel \<Longrightarrow> (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
  length xi = d \<Longrightarrow>
  length (normal si) = d \<Longrightarrow>
  (nres_of (inter_aform_plane_lv (length xi) optns xi si), inter_sctn_specs d x s)
  \<in> \<langle>aforms_rel\<rangle>nres_rel"
proof (goal_cases)
  case 1
  from 1 have sis: "si = s"
    by (cases si; cases s) (auto simp: sctn_rel_def)
  have Dp: "DIM_precond TYPE('n rvec) CARD('n)"
    by auto
  have a: "(xi, eucl_of_list_aform xi::'n rvec aform) \<in> lv_aforms_rel"
    by (auto simp: lv_aforms_rel_def br_def aforms_relp_def aforms_rel_def mem_lv_rel_set_rel_iff 1
        Joints_imp_length_eq)
  have b: "(si, (Sctn (eucl_of_list (normal si)) (pstn si))::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    using 1
    by (cases si)
      (auto simp: lv_aforms_rel_def br_def aforms_relp_def aforms_rel_def mem_lv_rel_set_rel_iff
        Joints_imp_length_eq sctn_rel_def intro!: lv_relI)
  have a: "(nres_of (inter_aform_plane_lv CARD('n) optns xi si),
    inter_aform_plane optns (eucl_of_list_aform xi::'n rvec aform) (Sctn (eucl_of_list (normal si)) (pstn si)))
    \<in> \<langle>lv_aforms_rel\<rangle>nres_rel"
    (is "(_, inter_aform_plane _ ?ea ?se) \<in> _")
    using inter_aform_plane_lv.refine[OF Dp IdI a b, of optns]
    by simp
  have b: "(inter_aform_plane optns ?ea ?se, inter_sctn_spec (Affine ?ea) ?se) \<in> \<langle>br Affine top\<rangle>nres_rel"
    using 1
    apply (auto simp: inter_sctn_spec_def nres_rel_def inter_aform_plane_def project_ncoord_aform_def
        inter_aform_plane_ortho_nres_def
        split: option.splits
        intro!: RETURN_SPEC_refine
        dest!: inter_inter_aform_plane_ortho)
     apply (auto simp: aform_rel_def br_def nres_rel_def comps bind_eq_Some_conv
        inter_sctn_spec_def inter_aform_plane_def plane_of_def aforms_relp_def aforms_rel_def
        mem_lv_rel_set_rel_iff
        intro!: RETURN_SPEC_refine nres_of_THE_DRES_le mem_Affine_project_coord_aformI
        dest!: inter_inter_aform_plane_ortho
        split: if_splits)
     apply (auto dest!: mem_Affine_project_coord_aformD simp: abs_in_Basis_iff plane_of_def)
    done
  from relcompI[OF a b]
  have "(nres_of (inter_aform_plane_lv CARD('n) optns xi si), inter_sctn_spec (Affine ?ea) ?se) \<in>
      \<langle>lv_aforms_rel\<rangle>nres_rel O \<langle>br Affine top\<rangle>nres_rel"
    by auto
  also have "\<langle>lv_aforms_rel\<rangle>nres_rel O \<langle>br Affine top\<rangle>nres_rel \<subseteq> \<langle>\<langle>lv_rel\<rangle>aforms_relp\<rangle>nres_rel"
    unfolding nres_rel_comp
    apply (rule nres_rel_mono)
    apply (rule lv_aforms_rel_comp_br_Affine_le)
    done
  finally
  have step1: "(nres_of (inter_aform_plane_lv CARD('n) optns xi si),
      inter_sctn_spec (Affine (eucl_of_list_aform xi)::'n rvec set) (Sctn (eucl_of_list (normal si)) (pstn si)))
      \<in> \<langle>\<langle>lv_rel\<rangle>aforms_relp\<rangle>nres_rel"
    by simp
  have step2: "(inter_sctn_spec (Affine (eucl_of_list_aform xi)::'n rvec set) (Sctn (eucl_of_list (normal si)) (pstn si)),
    inter_sctn_specs CARD('n) (Joints xi) si) \<in> \<langle>\<langle>lv_rel\<inverse>\<rangle>set_rel\<rangle>nres_rel"
    apply (auto simp: inter_sctn_specs_def inter_sctn_spec_def simp: nres_rel_def intro!: SPEC_refine)
    subgoal for x
      apply (rule exI[where x="list_of_eucl ` x"])
      apply (auto simp: env_len_def plane_ofs_def intro: list_of_eucl_image_lv_rel_inverse)
      subgoal for y
        apply (rule image_eqI[where x="eucl_of_list y"])
          apply (subst list_of_eucl_eucl_of_list)
          apply (auto simp: 1 Joints_imp_length_eq)
        apply (rule subsetD, assumption)
        apply (auto simp: intro!: eucl_of_list_mem_eucl_of_list_aform 1)
        using inner_lv_rel_autoref[where 'a="'n rvec", param_fo, OF lv_relI lv_relI, of y "normal si"]
        by (auto simp: plane_of_def 1 Joints_imp_length_eq)
      subgoal for y
        apply (drule subsetD, assumption)
        using inner_lv_rel_autoref[where 'a="'n rvec", param_fo, OF lv_relI lv_relI, of "list_of_eucl y" "normal si"]
        by (auto simp: plane_of_def 1 Joints_imp_length_eq)
      done
    done
  from relcompI[OF step1 step2]
  have "(nres_of (inter_aform_plane_lv CARD('n) optns xi si), inter_sctn_specs CARD('n) (Joints xi) si)
    \<in> \<langle>\<langle>lv_rel::(real list \<times> 'n rvec)set\<rangle>aforms_relp\<rangle>nres_rel O \<langle>\<langle>lv_rel\<inverse>\<rangle>set_rel\<rangle>nres_rel" by simp
  also have "\<langle>\<langle>lv_rel::(real list \<times> 'n rvec)set\<rangle>aforms_relp\<rangle>nres_rel O \<langle>\<langle>lv_rel\<inverse>\<rangle>set_rel\<rangle>nres_rel \<subseteq>
    \<langle>aforms_rel O Id\<rangle>nres_rel"
    unfolding nres_rel_comp O_assoc aforms_relp_def
    apply (rule nres_rel_mono)
    apply (rule relcomp_mono[OF order_refl])
    unfolding set_rel_sv[OF sv_lv_rel_inverse] set_rel_sv[OF lv_rel_sv]
    apply (auto simp: length_lv_rel)
    unfolding relcomp_Image[symmetric] lv_rel_comp_lv_rel_inverse
     apply (auto simp: Basis_not_uminus length_lv_rel)
    unfolding lv_rel_def
    subgoal for a b c d
      apply (auto dest!: brD simp: length_lv_rel)
      using eucl_of_list_inj[where 'a="'n rvec", of d b]
      by auto
    done
  finally show ?case using 1 by (simp add: aforms_rel_def br_def sis)
qed

end

setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum"}, SOME @{typ "'a list"})\<close>
setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum_all"}, SOME @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"})\<close>
setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum_ex"}, SOME @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"})\<close>

lemmas inter_aform_plane_refine_unoverloaded0 =
  inter_aform_plane_refine_aux[internalize_sort "'n::enum",
    unoverload enum_class.enum,
    unoverload enum_class.enum_all,
    unoverload enum_class.enum_ex]

theorem
  inter_aform_plane_refine_unoverloaded:
    "class.enum (enum::'a list) enum_all enum_ex \<and> d = CARD('a) \<Longrightarrow>
    (xi, x) \<in> aforms_rel \<Longrightarrow>
    (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
    length xi = d \<Longrightarrow>
    length (normal si) = d \<Longrightarrow>
    (nres_of (inter_aform_plane_lv (length xi) optns xi si), inter_sctn_specs d x s)
    \<in> \<langle>aforms_rel\<rangle>nres_rel"
  by (rule inter_aform_plane_refine_unoverloaded0) auto

setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum"}, SOME @{typ "'a::enum list"})\<close>
setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum_all"}, SOME @{typ "('a::enum \<Rightarrow> bool) \<Rightarrow> bool"})\<close>
setup \<open>Sign.add_const_constraint (@{const_name "enum_class.enum_ex"}, SOME @{typ "('a::enum \<Rightarrow> bool) \<Rightarrow> bool"})\<close>

context includes autoref_syntax begin

text \<open>TODO: this is a special case of \<open>Cancel_Card_Constraint\<close> from \<open>AFP/Perron_Frobenius\<close>!\<close>
lemma type_impl_card_n_enum:
  assumes "\<exists>(Rep :: 'a \<Rightarrow> nat) Abs. type_definition Rep Abs {0 ..< n :: nat}"
  obtains enum enum_all enum_ex
  where "class.enum (enum::'a list) enum_all enum_ex \<and> n = CARD('a)"
proof -
  from assms obtain rep :: "'a \<Rightarrow> nat" and abs :: "nat \<Rightarrow> 'a" where t: "type_definition rep abs {0 ..< n}" by auto
  have "card (UNIV :: 'a set) = card {0 ..< n}" using t by (rule type_definition.card)
  also have "\<dots> = n" by auto
  finally have bn: "CARD ('a) = n" .

  let ?enum = "(map abs [0..<n])"
  have "class.enum ?enum (Ball (set ?enum)) (Bex (set ?enum))"
    apply standard
    using t
    apply (auto simp: distinct_map type_definition_def)
    using t type_definition.univ apply fastforce
    using t type_definition.Abs_inj_on apply blast
    apply (meson t type_definition.Abs_induct)
    by (metis t tdD1)
  with bn have "class.enum ?enum (Ball (set ?enum)) (Bex (set ?enum)) \<and> n = CARD('a)"
    by simp
  then show ?thesis ..
qed


lemma inter_aform_plane_refine_ex_typedef:
  "(xi, x) \<in> aforms_rel \<Longrightarrow>
  (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
  length xi = d \<Longrightarrow>
  length (normal si) = d \<Longrightarrow>
  (nres_of (inter_aform_plane_lv (length xi) optns xi si), inter_sctn_specs d x s)
  \<in> \<langle>aforms_rel\<rangle>nres_rel"
  if "\<exists>(Rep :: 'a \<Rightarrow> nat) Abs. type_definition Rep Abs {0 ..< d :: nat}"
  by (rule type_impl_card_n_enum[OF that]) (rule inter_aform_plane_refine_unoverloaded; assumption)

lemma inter_aform_plane_refine:
  "0 < d \<Longrightarrow>
  (xi, x) \<in> aforms_rel \<Longrightarrow>
  (si, s) \<in> \<langle>Id\<rangle>sctn_rel \<Longrightarrow>
  length xi = d \<Longrightarrow>
  length (normal si) = d \<Longrightarrow>
  (nres_of (inter_aform_plane_lv (length xi) optns xi si), inter_sctn_specs d x s)
  \<in> \<langle>aforms_rel\<rangle>nres_rel"
  by (rule inter_aform_plane_refine_ex_typedef[cancel_type_definition, simplified])

lemma Joints_reduce_aforms: "x \<in> Joints X \<Longrightarrow> x \<in> Joints (reduce_aforms prec t X)"
proof (auto simp: reduce_aforms_def summarize_threshold_def[abs_def] Joints_def valuate_def aform_val_def, goal_cases)
  case (1 e)
  from summarize_aformsE[OF \<open>e \<in> _\<close> order_refl, of "X" "prec" t]
  guess e' .
  thus ?case
    by (auto intro!: image_eqI[where x=e'] simp: aform_vals_def)
qed

lemma length_reduce_aform[simp]: "length (reduce_aforms optns a x) = length x"
  by (auto simp: reduce_aforms_def)

lemma reduce_aform_refine:
  "(xi, x) \<in> aforms_rel \<Longrightarrow> length xi = d \<Longrightarrow>
    (RETURN (reduce_aforms prec C xi), reduce_specs d r x) \<in> \<langle>aforms_rel\<rangle>nres_rel"
  apply (auto simp: reduce_specs_def nres_rel_def comps aforms_relp_def mem_lv_rel_set_rel_iff
      aforms_rel_def env_len_def
      intro!: RETURN_SPEC_refine)
  apply (auto simp: br_def env_len_def)
  by (auto simp: mem_lv_rel_set_rel_iff Joints_imp_length_eq
      intro!: in_image_eucl_of_list_eucl_of_list_aform Joints_reduce_aforms
      eucl_of_list_mem_eucl_of_list_aform)

lemma aform_euclarithform_refine:
  "(nres_of o2 aform_form optns, approx_form_spec) \<in> Id \<rightarrow> aforms_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: approx_form_spec_def nres_rel_def comps aform_form_def
      aforms_rel_def br_def approx_form_aform
      dest!: approx_form_aux
      intro!: ivls_of_aforms)

lemma aform_isFDERIV:
  "(\<lambda>N xs fas vs. nres_of (aform_isFDERIV optns N xs fas vs), isFDERIV_spec)
    \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> aforms_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: isFDERIV_spec_def nres_rel_def comps aform_isFDERIV_def
      aforms_rel_def br_def
      dest!: approx_form_aux
      intro!: ivls_of_aforms isFDERIV_approx)

lemma approx_slp_lengthD: "approx_slp p slp a = Some xs \<Longrightarrow>
  length xs = length slp + length a"
  by (induction slp arbitrary: xs a) (auto simp: bind_eq_Some_conv)

lemma approx_slp_outer_lengthD: "approx_slp_outer p d slp a = Some xs \<Longrightarrow>
  length xs = min d (length slp + length a)"
  by (auto simp: approx_slp_outer_def Let_def bind_eq_Some_conv o_def
      aforms_err_to_aforms_def aform_err_to_aform_def dest!: approx_slp_lengthD)

lemma approx_slp_refine:
  "(nres_of o3 aform_slp prec, approx_slp_spec fas) \<in> 
    nat_rel \<rightarrow> fas_rel \<rightarrow> aforms_rel \<rightarrow> \<langle>\<langle>aforms_rel\<rangle>option_rel\<rangle>nres_rel"
  apply (auto simp: approx_slp_spec_def comps aform_slp_def nres_rel_def
      intro!: RETURN_SPEC_refine ASSERT_refine_right)
  subgoal for a b
    apply (rule exI[where x = "map_option Joints (approx_slp_outer prec (length fas) (slp_of_fas fas) a)"])
    apply (auto simp: option.splits aforms_rel_def br_def env_len_def Joints_imp_length_eq)
    apply (auto dest!: approx_slp_outer_lengthD)[]
    using length_slp_of_fas_le trans_le_add1 approx_slp_outer_lengthD apply blast
    using approx_slp_outer_plain by blast
  done

lemma fresh_index_aforms_Nil[simp]: "fresh_index_aforms [] = 0"
  by (auto simp: fresh_index_aforms_def)

lemma independent_aforms_Nil[simp]:
  "independent_aforms x [] = [x]"
  by (auto simp: independent_aforms_def)

lemma mem_Joints_zero_iff[simp]: "x # xs \<in> Joints ((0, zero_pdevs) # XS) \<longleftrightarrow> (x = 0 \<and> xs \<in> Joints XS)"
  by (auto simp: Joints_def valuate_def)

lemma Joints_independent_aforms_eq: "Joints (independent_aforms x xs) = set_Cons (Affine x) (Joints xs)"
  by (simp add: independent_aforms_def Joints_msum_aform degree_le_fresh_index set_Cons_def)

lemma independent_aforms_refine: "(independent_aforms, set_Cons) \<in> \<langle>rnv_rel\<rangle>aform_rel \<rightarrow> aforms_rel \<rightarrow> aforms_rel"
  by (auto simp: aforms_rel_def br_def aform_rel_def Joints_independent_aforms_eq)

end


locale aform_approximate_sets = approximate_sets
  aform_ops
  Joints
  aforms_rel
begin

lemma Joints_in_lv_rel_set_relD:
  "(Joints xs, X) \<in> \<langle>lv_rel\<rangle>set_rel \<Longrightarrow> X = Affine (eucl_of_list_aform xs)"
  unfolding lv_rel_def set_rel_br
  by (auto simp: br_def Joints_imp_length_eq eucl_of_list_image_Joints[symmetric])

lemma ncc_precond: "ncc_precond TYPE('a::executable_euclidean_space)"
  unfolding ncc_precond_def ncc_def appr_rel_def
  by (auto simp: aforms_rel_def compact_Affine convex_Affine dest!: Joints_in_lv_rel_set_relD brD)

lemma fst_eucl_of_list_aform_map: "fst (eucl_of_list_aform (map (\<lambda>x. (fst x, asdf x)) x)) =
  fst (eucl_of_list_aform x)"
  by (auto simp: eucl_of_list_aform_def o_def)

lemma
  Affine_pdevs_of_list:\<comment> \<open>TODO: move!\<close>
  "Affine (fst x, pdevs_of_list (map snd (list_of_pdevs (snd x)))) = Affine x"
  by (auto simp: Affine_def valuate_def aform_val_def
      elim: pdevs_val_of_list_of_pdevs2[where X = "snd x"]
        pdevs_val_of_list_of_pdevs[where X = "snd x"])

end

lemma aform_approximate_sets: "aform_approximate_sets prec"
  apply (unfold_locales)
  unfolding aform_ops_def approximate_set_ops.simps
  subgoal unfolding relAPP_def aforms_rel_def .
  subgoal by (force simp: aforms_of_ivls_refine)
  subgoal by (rule product_aforms_refine)
  subgoal by (rule msum_aforms'_refine)
  subgoal by (rule inf_aforms_refine)
  subgoal by (rule sup_aforms_refine)
  subgoal by (rule split_aform_largest_take_refine)
  subgoal by (rule aform_inf_inner_refine)
  subgoal by (rule aform_sup_inner_refine)
  subgoal by (rule inter_aform_plane_refine) simp_all
  subgoal by (auto split: option.splits intro!: reduce_aform_refine)
  subgoal by (force simp: width_spec_def nres_rel_def)
  subgoal by (rule approx_slp_refine)
  subgoal by (rule aform_euclarithform_refine)
  subgoal by (rule aform_isFDERIV)
  subgoal by simp
  subgoal by (auto simp: Joints_imp_length_eq)
  subgoal by (force simp: Affine_def Joints_def valuate_def intro!:)
  subgoal by (force simp: Affine_def Joints_def valuate_def intro!:)
  subgoal by (auto simp: Joints_imp_length_eq)
  done

end
