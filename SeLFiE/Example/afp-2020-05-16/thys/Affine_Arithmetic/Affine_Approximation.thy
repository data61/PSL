 section \<open>Approximation with Affine Forms\<close>
theory Affine_Approximation
imports
  "HOL-Decision_Procs.Approximation"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.Mapping"
  Executable_Euclidean_Space
  Affine_Form
  Straight_Line_Program
begin
text \<open>\label{sec:approxaffine}\<close>

lemma convex_on_imp_above_tangent:\<comment> \<open>TODO: generalizes @{thm convex_on_imp_above_tangent}\<close>
  assumes convex: "convex_on A f" and connected: "connected A"
  assumes c: "c \<in> A" and x : "x \<in> A"
  assumes deriv: "(f has_field_derivative f') (at c within A)"
  shows   "f x - f c \<ge> f' * (x - c)"
proof (cases x c rule: linorder_cases)
  assume xc: "x > c"
  let ?A' = "{c<..<x}"
  have subs: "?A' \<subseteq> A" using xc x c
    by (simp add: connected connected_contains_Ioo)
  have "at c within ?A' \<noteq> bot"
    using xc
    by (simp add: at_within_eq_bot_iff)
  moreover from deriv have "((\<lambda>y. (f y - f c) / (y - c)) \<longlongrightarrow> f') (at c within ?A')"
    unfolding has_field_derivative_iff using subs
    by (blast intro: tendsto_mono at_le)
  moreover from eventually_at_right_real[OF xc]
    have "eventually (\<lambda>y. (f y - f c) / (y - c) \<le> (f x - f c) / (x - c)) (at_right c)"
  proof eventually_elim
    fix y assume y: "y \<in> {c<..<x}"
    with convex connected x c have "f y \<le> (f x - f c) / (x - c) * (y - c) + f c"
      using interior_subset[of A]
      by (intro convex_onD_Icc' convex_on_subset[OF convex] connected_contains_Icc) auto
    hence "f y - f c \<le> (f x - f c) / (x - c) * (y - c)" by simp
    thus "(f y - f c) / (y - c) \<le> (f x - f c) / (x - c)" using y xc by (simp add: divide_simps)
  qed
  hence "eventually (\<lambda>y. (f y - f c) / (y - c) \<le> (f x - f c) / (x - c)) (at c within ?A')"
    by (simp add: eventually_at_filter eventually_mono)
  ultimately have "f' \<le> (f x - f c) / (x - c)" by (simp add: tendsto_upperbound)
  thus ?thesis using xc by (simp add: field_simps)
next
  assume xc: "x < c"
  let ?A' = "{x<..<c}"
  have subs: "?A' \<subseteq> A" using xc x c
    by (simp add: connected connected_contains_Ioo)
  have "at c within ?A' \<noteq> bot"
    using xc
    by (simp add: at_within_eq_bot_iff)
  moreover from deriv have "((\<lambda>y. (f y - f c) / (y - c)) \<longlongrightarrow> f') (at c within ?A')"
    unfolding has_field_derivative_iff using subs
    by (blast intro: tendsto_mono at_le)
  moreover from eventually_at_left_real[OF xc]
    have "eventually (\<lambda>y. (f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)) (at_left c)"
  proof eventually_elim
    fix y assume y: "y \<in> {x<..<c}"
    with convex connected x c have "f y \<le> (f x - f c) / (c - x) * (c - y) + f c"
      using interior_subset[of A]
      by (intro convex_onD_Icc'' convex_on_subset[OF convex] connected_contains_Icc) auto
    hence "f y - f c \<le> (f x - f c) * ((c - y) / (c - x))" by simp
    also have "(c - y) / (c - x) = (y - c) / (x - c)" using y xc by (simp add: field_simps)
    finally show "(f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)" using y xc
      by (simp add: divide_simps)
  qed
  hence "eventually (\<lambda>y. (f y - f c) / (y - c) \<ge> (f x - f c) / (x - c)) (at c within ?A')"
    by (simp add: eventually_at_filter eventually_mono)
  ultimately have "f' \<ge> (f x - f c) / (x - c)" by (simp add: tendsto_lowerbound)
  thus ?thesis using xc by (simp add: field_simps)
qed simp_all


text \<open>Approximate operations on affine forms.\<close>

lemma Affine_notempty[intro, simp]: "Affine X \<noteq> {}"
  by (auto simp: Affine_def valuate_def)

lemma truncate_up_lt: "x < y \<Longrightarrow> x < truncate_up prec y"
  by (rule less_le_trans[OF _ truncate_up])

lemma truncate_up_pos_eq[simp]: "0 < truncate_up p x \<longleftrightarrow> 0 < x"
  by (auto simp: truncate_up_lt) (metis (poly_guards_query) not_le truncate_up_nonpos)

lemma inner_scaleR_pdevs_0: "inner_scaleR_pdevs 0 One_pdevs = zero_pdevs"
  unfolding inner_scaleR_pdevs_def
  by transfer (auto simp: unop_pdevs_raw_def)

lemma Affine_aform_of_point_eq[simp]: "Affine (aform_of_point p) = {p}"
  by (simp add: Affine_aform_of_ivl aform_of_point_def)

lemma mem_Affine_aform_of_point: "x \<in> Affine (aform_of_point x)"
  by simp

lemma
  aform_val_aform_of_ivl_innerE:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "a \<le> b" "c \<in> Basis"
  obtains f where "aform_val e (aform_of_ivl a b) \<bullet> c = aform_val f (aform_of_ivl (a \<bullet> c) (b \<bullet> c))"
    "f \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  have [simp]: "a \<bullet> c \<le> b \<bullet> c"
    using assms by (auto simp: eucl_le[where 'a='a])
  have "(\<lambda>x. x \<bullet> c) ` Affine (aform_of_ivl a b) = Affine (aform_of_ivl (a \<bullet> c) (b \<bullet> c))"
    using assms
    by (auto simp: Affine_aform_of_ivl eucl_le[where 'a='a]
      image_eqI[where x="\<Sum>i\<in>Basis. (if i = c then x else a \<bullet> i) *\<^sub>R i" for x])
  then obtain f where
      "aform_val e (aform_of_ivl a b) \<bullet> c = aform_val f (aform_of_ivl (a \<bullet> c) (b \<bullet> c))"
      "f \<in> UNIV \<rightarrow> {-1 .. 1}"
    using assms
    by (force simp: Affine_def valuate_def)
  thus ?thesis ..
qed

lift_definition coord_pdevs::"nat \<Rightarrow> real pdevs" is "\<lambda>n i. if i = n then 1 else 0" by auto

lemma pdevs_apply_coord_pdevs [simp]: "pdevs_apply (coord_pdevs i) x = (if x = i then 1 else 0)"
  by transfer simp

lemma degree_coord_pdevs[simp]: "degree (coord_pdevs i) = Suc i"
  by (auto intro!: degree_eqI)

lemma pdevs_val_coord_pdevs[simp]: "pdevs_val e (coord_pdevs i) = e i"
  by (auto simp: pdevs_val_sum if_distrib sum.delta cong: if_cong)

definition "aforms_of_ivls ls us = map
    (\<lambda>(i, (l, u)). ((l + u)/2, scaleR_pdevs ((u - l)/2) (coord_pdevs i)))
    (zip [0..<length ls] (zip ls us))"

lemma
  aforms_of_ivls:
  assumes "length ls = length us" "length xs = length ls"
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i \<in> {ls ! i .. us ! i}"
  shows "xs \<in> Joints (aforms_of_ivls ls us)"
proof -
  {
    fix i assume "i < length xs"
    then have "\<exists>e. e \<in> {-1 .. 1} \<and> xs ! i = (ls ! i + us ! i) / 2 + e * (us ! i - ls ! i) / 2"
      using assms
      by (force intro!: exI[where x="(xs ! i - (ls ! i + us ! i) / 2) / (us ! i - ls ! i) * 2"]
          simp: divide_simps algebra_simps)
  } then obtain e where e: "e i \<in> {-1 .. 1}"
    "xs ! i = (ls ! i + us ! i) / 2 + e i * (us ! i - ls ! i) / 2" 
    if "i < length xs" for i
    using that by metis
  define e' where "e' i = (if i < length xs then e i else 0)" for i
  show ?thesis
    using e assms
    by (auto simp: aforms_of_ivls_def Joints_def valuate_def e'_def aform_val_def
        intro!: image_eqI[where x=e'] nth_equalityI)
qed


subsection \<open>Approximate Operations\<close>

definition "max_pdev x = fold (\<lambda>x y. if infnorm (snd x) \<ge> infnorm (snd y) then x else y) (list_of_pdevs x) (0, 0)"


subsubsection \<open>set of generated endpoints\<close>

fun points_of_list where
  "points_of_list x0 [] = [x0]"
| "points_of_list x0 ((i, x)#xs) = (points_of_list (x0 + x) xs @ points_of_list (x0 - x) xs)"

primrec points_of_aform where
  "points_of_aform (x, xs) = points_of_list x (list_of_pdevs xs)"


subsubsection \<open>Approximate total deviation\<close>

definition sum_list'::"nat \<Rightarrow> 'a list \<Rightarrow> 'a::executable_euclidean_space"
  where "sum_list' p xs = fold (\<lambda>a b. eucl_truncate_up p (a + b)) xs 0"

definition "tdev' p x = sum_list' p (map (abs o snd) (list_of_pdevs x))"

lemma
  eucl_fold_mono:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'a\<Rightarrow>'a"
  assumes mono: "\<And>w x y z. w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> f w y \<le> f x z"
  shows "x \<le> y \<Longrightarrow> fold f xs x \<le> fold f xs y"
  by (induct xs arbitrary: x y) (auto simp: mono)

lemma sum_list_add_le_fold_eucl_truncate_up:
  fixes z::"'a::executable_euclidean_space"
  shows "sum_list xs + z \<le> fold (\<lambda>x y. eucl_truncate_up p (x + y)) xs z"
proof (induct xs arbitrary: z)
  case (Cons x xs)
  have "sum_list (x # xs) + z = sum_list xs + (z + x)"
    by simp
  also have "\<dots> \<le> fold (\<lambda>x y. eucl_truncate_up p (x + y)) xs (z + x)"
    using Cons by simp
  also have "\<dots> \<le> fold (\<lambda>x y. eucl_truncate_up p (x + y)) xs (eucl_truncate_up p (x + z))"
    by (auto intro!: add_mono eucl_fold_mono eucl_truncate_up eucl_truncate_up_mono simp: ac_simps)
  finally show ?case by simp
qed simp

lemma sum_list_le_sum_list':
  "sum_list xs \<le> sum_list' p xs"
  unfolding sum_list'_def
  using sum_list_add_le_fold_eucl_truncate_up[of xs 0] by simp

lemma sum_list'_sum_list_le:
  "y \<le> sum_list xs \<Longrightarrow> y \<le> sum_list' p xs"
  by (metis sum_list_le_sum_list' order.trans)

lemma tdev': "tdev x \<le> tdev' p x"
  unfolding tdev'_def
proof -
  have "tdev x = (\<Sum>i = 0 ..< degree x. \<bar>pdevs_apply x i\<bar>)"
    by (auto intro!: sum.mono_neutral_cong_left simp: tdev_def)
  also have "\<dots> = (\<Sum>i \<leftarrow> rev [0 ..< degree x]. \<bar>pdevs_apply x i\<bar>)"
    by (metis atLeastLessThan_upt sum_list_rev rev_map sum_set_upt_conv_sum_list_nat)
  also have
    "\<dots> = sum_list (map (\<lambda>xa. \<bar>pdevs_apply x xa\<bar>) [xa\<leftarrow>rev [0..<degree x] . pdevs_apply x xa \<noteq> 0])"
    unfolding filter_map map_map o_def
    by (subst sum_list_map_filter) auto
  also note sum_list_le_sum_list'[of _ p]
  also have "[xa\<leftarrow>rev [0..<degree x] . pdevs_apply x xa \<noteq> 0] =
      rev (sorted_list_of_set (pdevs_domain x))"
    by (subst rev_is_rev_conv[symmetric])
      (auto simp: filter_map rev_filter intro!: sorted_distinct_set_unique
        sorted_filter[of "\<lambda>x. x", simplified] degree_gt)
  finally
  show "tdev x \<le> sum_list' p (map (abs \<circ> snd) (list_of_pdevs x))"
    by (auto simp: list_of_pdevs_def o_def rev_map filter_map rev_filter)
qed

lemma tdev'_le: "x \<le> tdev y \<Longrightarrow> x \<le> tdev' p y"
  by (metis order.trans tdev')

lemmas abs_pdevs_val_le_tdev' = tdev'_le[OF abs_pdevs_val_le_tdev]

lemma tdev'_uminus_pdevs[simp]: "tdev' p (uminus_pdevs x) = tdev' p x"
  by (auto simp: tdev'_def o_def rev_map filter_map rev_filter list_of_pdevs_def pdevs_domain_def)

abbreviation Radius::"'a::ordered_euclidean_space aform \<Rightarrow> 'a"
  where "Radius X \<equiv> tdev (snd X)"

abbreviation Radius'::"nat\<Rightarrow>'a::executable_euclidean_space aform \<Rightarrow> 'a"
  where "Radius' p X \<equiv> tdev' p (snd X)"

lemma Radius'_uminus_aform[simp]: "Radius' p (uminus_aform X) = Radius' p X"
  by (auto simp: uminus_aform_def)


subsubsection \<open>truncate partial deviations\<close>

definition trunc_pdevs_raw::"nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a::executable_euclidean_space"
  where "trunc_pdevs_raw p x i = eucl_truncate_down p (x i)"

lemma nonzeros_trunc_pdevs_raw:
  "{i. trunc_pdevs_raw r x i \<noteq> 0} \<subseteq> {i. x i \<noteq> 0}"
  by (auto simp: trunc_pdevs_raw_def[abs_def])

lift_definition trunc_pdevs::"nat \<Rightarrow> 'a::executable_euclidean_space pdevs \<Rightarrow> 'a pdevs"
  is trunc_pdevs_raw
  by (auto intro!: finite_subset[OF nonzeros_trunc_pdevs_raw])

definition trunc_err_pdevs_raw::"nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a::executable_euclidean_space"
  where "trunc_err_pdevs_raw p x i = trunc_pdevs_raw p x i - x i"

lemma nonzeros_trunc_err_pdevs_raw:
  "{i. trunc_err_pdevs_raw r x i \<noteq> 0} \<subseteq> {i. x i \<noteq> 0}"
  by (auto simp: trunc_pdevs_raw_def trunc_err_pdevs_raw_def[abs_def])

lift_definition trunc_err_pdevs::"nat \<Rightarrow> 'a::executable_euclidean_space pdevs \<Rightarrow> 'a pdevs"
  is trunc_err_pdevs_raw
  by (auto intro!: finite_subset[OF nonzeros_trunc_err_pdevs_raw])

term float_plus_down

lemma pdevs_apply_trunc_pdevs[simp]:
  fixes x y::"'a::euclidean_space"
  shows "pdevs_apply (trunc_pdevs p X) n = eucl_truncate_down p (pdevs_apply X n)"
  by transfer (simp add: trunc_pdevs_raw_def)

lemma pdevs_apply_trunc_err_pdevs[simp]:
  fixes x y::"'a::euclidean_space"
  shows "pdevs_apply (trunc_err_pdevs p X) n =
    eucl_truncate_down p (pdevs_apply X n) - (pdevs_apply X n)"
  by transfer (auto simp: trunc_err_pdevs_raw_def trunc_pdevs_raw_def)

lemma pdevs_val_trunc_pdevs:
  fixes x y::"'a::euclidean_space"
  shows "pdevs_val e (trunc_pdevs p X) = pdevs_val e X + pdevs_val e (trunc_err_pdevs p X)"
proof -
  have "pdevs_val e X + pdevs_val e (trunc_err_pdevs p X) =
      pdevs_val e (add_pdevs X (trunc_err_pdevs p X))"
    by simp
  also have "\<dots> = pdevs_val e (trunc_pdevs p X)"
    by (auto simp: pdevs_val_def trunc_pdevs_raw_def trunc_err_pdevs_raw_def)
  finally show ?thesis by simp
qed

lemma pdevs_val_trunc_err_pdevs:
  fixes x y::"'a::euclidean_space"
  shows "pdevs_val e (trunc_err_pdevs p X) = pdevs_val e (trunc_pdevs p X) - pdevs_val e X"
  by (simp add: pdevs_val_trunc_pdevs)

definition truncate_aform::"nat \<Rightarrow> 'a aform \<Rightarrow> 'a::executable_euclidean_space aform"
  where "truncate_aform p x = (eucl_truncate_down p (fst x), trunc_pdevs p (snd x))"

definition truncate_error_aform::"nat \<Rightarrow> 'a aform \<Rightarrow> 'a::executable_euclidean_space aform"
  where "truncate_error_aform p x =
    (eucl_truncate_down p (fst x) - fst x, trunc_err_pdevs p (snd x))"

lemma
  abs_aform_val_le:
  assumes "e \<in> UNIV \<rightarrow> {- 1..1}"
  shows "abs (aform_val e X) \<le> eucl_truncate_up p (\<bar>fst X\<bar> + tdev' p (snd X))"
proof -
  have "abs (aform_val e X) \<le> \<bar>fst X\<bar> + \<bar>pdevs_val e (snd X)\<bar>"
    by (auto simp: aform_val_def intro!: abs_triangle_ineq)
  also have "\<bar>pdevs_val e (snd X)\<bar> \<le> tdev (snd X)"
    using assms by (rule abs_pdevs_val_le_tdev)
  also note tdev'
  also note eucl_truncate_up
  finally show ?thesis by simp
qed


subsubsection \<open>truncation with error bound\<close>

definition "trunc_bound_eucl p s =
  (let
    d = eucl_truncate_down p s;
    ed = abs (d - s) in
  (d, eucl_truncate_up p ed))"

lemma trunc_bound_euclE:
  obtains err where
  "\<bar>err\<bar> \<le> snd (trunc_bound_eucl p x)"
  "fst (trunc_bound_eucl p x) = x + err"
proof atomize_elim
  have "fst (trunc_bound_eucl p x) = x + (eucl_truncate_down p x - x)"
    (is "_ = _ + ?err")
    by (simp_all add: trunc_bound_eucl_def Let_def)
  moreover have "abs ?err \<le> snd (trunc_bound_eucl p x)"
    by (simp add: trunc_bound_eucl_def Let_def eucl_truncate_up)
  ultimately show "\<exists>err. \<bar>err\<bar> \<le> snd (trunc_bound_eucl p x) \<and> fst (trunc_bound_eucl p x) = x + err"
    by auto
qed

definition "trunc_bound_pdevs p x = (trunc_pdevs p x, tdev' p (trunc_err_pdevs p x))"

lemma pdevs_apply_fst_trunc_bound_pdevs[simp]: "pdevs_apply (fst (trunc_bound_pdevs p x)) =
  pdevs_apply (trunc_pdevs p x)"
  by (simp add: trunc_bound_pdevs_def)

lemma trunc_bound_pdevsE:
  assumes "e \<in> UNIV \<rightarrow> {- 1..1}"
  obtains err where
  "\<bar>err\<bar> \<le> snd (trunc_bound_pdevs p x)"
  "pdevs_val e (fst ((trunc_bound_pdevs p x))) = pdevs_val e x + err"
proof atomize_elim
  have "pdevs_val e (fst (trunc_bound_pdevs p x)) = pdevs_val e x +
    pdevs_val e (add_pdevs (trunc_pdevs p x) (uminus_pdevs x))"
    (is "_ = _ + ?err")
    by (simp_all add: trunc_bound_pdevs_def Let_def)
  moreover have "abs ?err \<le> snd (trunc_bound_pdevs p x)"
    using assms
    by (auto simp add: pdevs_val_trunc_pdevs trunc_bound_pdevs_def Let_def eucl_truncate_up
      intro!: order_trans[OF abs_pdevs_val_le_tdev tdev'])
  ultimately show "\<exists>err. \<bar>err\<bar> \<le> snd (trunc_bound_pdevs p x) \<and>
      pdevs_val e (fst ((trunc_bound_pdevs p x))) = pdevs_val e x + err"
    by auto
qed

lemma
  degree_add_pdevs_le:
  assumes "degree X \<le> n"
  assumes "degree Y \<le> n"
  shows "degree (add_pdevs X Y) \<le> n"
  using assms
  by (auto intro!: degree_le)


lemma truncate_aform_error_aform_cancel:
  "aform_val e (truncate_aform p z) = aform_val e z + aform_val e (truncate_error_aform p z) "
  by (simp add: truncate_aform_def aform_val_def truncate_error_aform_def pdevs_val_trunc_pdevs)

lemma error_absE:
  assumes "abs err \<le> k"
  obtains e::real where "err = e * k" "e \<in> {-1 .. 1}"
  using assms
  by atomize_elim
    (safe intro!: exI[where x="err / abs k"] divide_atLeastAtMost_1_absI, auto)

lemma eucl_truncate_up_nonneg_eq_zero_iff:
  "x \<ge> 0 \<Longrightarrow> eucl_truncate_up p x = 0 \<longleftrightarrow> x = 0"
  by (metis (poly_guards_query) eq_iff eucl_truncate_up eucl_truncate_up_zero)

lemma
  aform_val_consume_error:
  assumes "abs err \<le> abs (pdevs_apply (snd X) n)"
  shows "aform_val (e(n := 0)) X + err = aform_val (e(n := err/pdevs_apply (snd X) n)) X"
  using assms
  by (auto simp add: aform_val_def)

lemma
  aform_val_consume_errorE:
  fixes X::"real aform"
  assumes "abs err \<le> abs (pdevs_apply (snd X) n)"
  obtains err' where "aform_val (e(n := 0)) X + err = aform_val (e(n := err')) X" "err' \<in> {-1 .. 1}"
  by atomize_elim
    (rule aform_val_consume_error assms aform_val_consume_error exI conjI
      divide_atLeastAtMost_1_absI)+

lemma
  degree_trunc_pdevs_le:
  assumes "degree X \<le> n"
  shows "degree (trunc_pdevs p X) \<le> n"
  using assms
  by (auto intro!: degree_le)

lemma pdevs_val_sum_less_degree:
  "pdevs_val e X = (\<Sum>i<d. e i *\<^sub>R pdevs_apply X i)" if "degree X \<le> d"
  unfolding pdevs_val_pdevs_domain
  apply (rule sum.mono_neutral_cong_left)
  using that
  by force+


subsubsection \<open>general affine operation\<close>

definition "affine_binop (X::real aform) Y a b c d k =
  (a * fst X + b * fst Y + c,
    pdev_upd (add_pdevs (scaleR_pdevs a (snd X)) (scaleR_pdevs b (snd Y))) k d)"

lemma pdevs_domain_One_pdevs[simp]: "pdevs_domain (One_pdevs::'a::executable_euclidean_space pdevs) =
  {0..<DIM('a)}"
  apply (auto simp: length_Basis_list split: if_splits)
  subgoal for i
    using nth_Basis_list_in_Basis[of i, where 'a='a]
    by (auto simp: length_Basis_list)
  done

lemma pdevs_val_One_pdevs:
  "pdevs_val e (One_pdevs::'a::executable_euclidean_space pdevs) = (\<Sum>i<DIM('a). e i *\<^sub>R Basis_list ! i)"
  by (auto simp: pdevs_val_pdevs_domain length_Basis_list intro!:sum.cong)

lemma affine_binop:
  assumes "degree_aforms [X, Y] \<le> k"
  shows "aform_val e (affine_binop X Y a b c d k) =
    a * aform_val e X + b * aform_val e Y + c + e k * d"
  using assms
  by (auto simp: aform_val_def affine_binop_def degrees_def
      pdevs_val_msum_pdevs degree_add_pdevs_le pdevs_val_One_pdevs Basis_list_real_def
      algebra_simps)

definition "affine_binop' p (X::real aform) Y a b c d k =
  (let
    \<comment> \<open>TODO: more round-off operations here?\<close>
    (r, e1) = trunc_bound_eucl p (a * fst X + b * fst Y + c);
    (Z, e2) = trunc_bound_pdevs p (add_pdevs (scaleR_pdevs a (snd X)) (scaleR_pdevs b (snd Y)))
  in
    (r, pdev_upd Z k (sum_list' p [e1, e2, d]))
  )"

lemma sum_list'_noneg_eq_zero_iff: "sum_list' p xs = 0 \<longleftrightarrow> (\<forall>x\<in>set xs. x = 0)" if "\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0"
proof safe
  fix x assume x: "sum_list' p xs = 0" "x \<in> set xs"
  from that have "0 \<le> sum_list xs" by (auto intro!: sum_list_nonneg)
  with that x have "sum_list xs = 0"
    by (metis antisym sum_list_le_sum_list')
  then have "(\<Sum>i<length xs.  xs ! i) = 0"
    by (auto simp: sum_list_sum_nth atLeast0LessThan)
  then show "x = 0" using x(2) that
    by (subst (asm) sum_nonneg_eq_0_iff) (auto simp: in_set_conv_nth)
next
  show "\<forall>x\<in>set xs. x = 0 \<Longrightarrow> sum_list' p xs = 0"
    by (induction xs) (auto simp: sum_list'_def)
qed

lemma affine_binop'E:
  assumes deg: "degree_aforms [X, Y] \<le> k"
  assumes e: "e \<in> UNIV \<rightarrow> {- 1..1}"
  assumes d: "abs u \<le> d"
  obtains ek where
    "a * aform_val e X + b * aform_val e Y + c + u = aform_val (e(k:=ek)) (affine_binop' p X Y a b c d k)"
    "ek \<in> {-1 .. 1}"
proof -
  have "a * aform_val e X + b * aform_val e Y + c + u =
    (a * fst X + b * fst Y + c) + pdevs_val e (add_pdevs (scaleR_pdevs a (snd X)) (scaleR_pdevs b (snd Y))) + u"
    (is "_ = ?c + pdevs_val _ ?ps + _")
    by (auto simp: aform_val_def algebra_simps)

  from trunc_bound_euclE[of p ?c] obtain ec where ec: "abs ec \<le> snd (trunc_bound_eucl p ?c)"
    "fst (trunc_bound_eucl p ?c) - ec = ?c"
    by (auto simp: algebra_simps)

  moreover

  from trunc_bound_pdevsE[OF e, of p ?ps]
  obtain eps where eps: "\<bar>eps\<bar> \<le> snd (trunc_bound_pdevs p ?ps)"
    "pdevs_val e (fst (trunc_bound_pdevs p ?ps)) - eps = pdevs_val e ?ps"
    by (auto simp: algebra_simps)

  moreover
  define ek where "ek = (u - ec - eps)/
        sum_list' p [snd (trunc_bound_eucl p ?c), snd (trunc_bound_pdevs p ?ps), d]"
  have "degree (fst (trunc_bound_pdevs p ?ps)) \<le>
      degree_aforms [X, Y]"
    by (auto simp: trunc_bound_pdevs_def degrees_def intro!: degree_trunc_pdevs_le degree_add_pdevs_le)
  moreover
  from this have "pdevs_apply (fst (trunc_bound_pdevs p ?ps)) k = 0"
    using deg order_trans by blast
  ultimately have "a * aform_val e X + b * aform_val e Y + c + u =
    aform_val (e(k:=ek)) (affine_binop' p X Y a b c d k)"
    apply (auto simp: affine_binop'_def algebra_simps aform_val_def split: prod.splits)
    subgoal for x y z
      apply (cases "sum_list' p [x, z, d] = 0")
      subgoal
        apply simp
        apply (subst (asm) sum_list'_noneg_eq_zero_iff)
        using d deg
        by auto
      subgoal
        apply (simp add: divide_simps algebra_simps ek_def)
        using \<open>pdevs_apply (fst (trunc_bound_pdevs p (add_pdevs (scaleR_pdevs a (snd X)) (scaleR_pdevs b (snd Y))))) k = 0\<close> by auto
      done
    done
  moreover have "ek \<in> {-1 .. 1}"
    unfolding ek_def
    apply (rule divide_atLeastAtMost_1_absI)
    apply (rule abs_triangle_ineq4[THEN order_trans])
    apply (rule order_trans)
     apply (rule add_right_mono)
     apply (rule abs_triangle_ineq4)
    using ec(1) eps(1)
    by (auto simp: sum_list'_def eucl_truncate_up_real_def add.assoc
        intro!: order_trans[OF _ abs_ge_self] order_trans[OF _ truncate_up_le] add_mono d )
  ultimately show ?thesis ..
qed

subsubsection \<open>Inf/Sup\<close>

definition "Inf_aform' p X = eucl_truncate_down p (fst X - tdev' p (snd X))"

definition "Sup_aform' p X = eucl_truncate_up p (fst X + tdev' p (snd X))"

lemma Inf_aform':
  shows "Inf_aform' p X \<le> Inf_aform X"
  unfolding Inf_aform_def Inf_aform'_def
  by (auto intro!: eucl_truncate_down_le add_left_mono tdev')

lemma Sup_aform':
  shows "Sup_aform X \<le> Sup_aform' p X"
  unfolding Sup_aform_def Sup_aform'_def
  by (rule eucl_truncate_up_le add_left_mono tdev')+

lemma Inf_aform_le_Sup_aform[intro]:
  "Inf_aform X \<le> Sup_aform X"
  by (simp add: Inf_aform_def Sup_aform_def algebra_simps)

lemma Inf_aform'_le_Sup_aform'[intro]:
  "Inf_aform' p X \<le> Sup_aform' p X"
  by (metis Inf_aform' Inf_aform_le_Sup_aform Sup_aform' order.trans)

definition
  "ivls_of_aforms prec = map (\<lambda>a. Interval' (float_of (Inf_aform' prec a)) (float_of(Sup_aform' prec a)))"

lemma
  assumes "\<And>i. e'' i \<le> 1"
  assumes "\<And>i. -1 \<le> e'' i"
  shows Inf_aform'_le: "Inf_aform' p r \<le> aform_val e'' r"
    and Sup_aform'_le: "aform_val e'' r \<le> Sup_aform' p r"
  by (auto intro!: order_trans[OF Inf_aform'] order_trans[OF _ Sup_aform'] Inf_aform Sup_aform
    simp: Affine_def valuate_def intro!: image_eqI[where x=e''] assms)


lemma InfSup_aform'_in_float[intro, simp]:
  "Inf_aform' p X \<in> float" "Sup_aform' p X \<in> float"
  by (auto simp: Inf_aform'_def eucl_truncate_down_real_def
      Sup_aform'_def eucl_truncate_up_real_def)

theorem ivls_of_aforms: "xs \<in> Joints XS \<Longrightarrow> bounded_by xs (ivls_of_aforms prec XS)"
  by (auto simp: bounded_by_def ivls_of_aforms_def Affine_def valuate_def Pi_iff set_of_eq
      intro!: Inf_aform'_le Sup_aform'_le
      dest!: nth_in_AffineI split: Interval'_splits)

definition "isFDERIV_aform prec N xs fas AS = isFDERIV_approx prec N xs fas (ivls_of_aforms prec AS)"

theorem isFDERIV_aform:
  assumes "isFDERIV_aform prec N xs fas AS"
  assumes "vs \<in> Joints AS"
  shows "isFDERIV N xs fas vs"
  apply (rule isFDERIV_approx)
  apply (rule ivls_of_aforms)
  apply (rule assms)
  apply (rule assms[unfolded isFDERIV_aform_def])
  done

definition "env_len env l = (\<forall>xs \<in> env. length xs = l)"

lemma env_len_takeI: "env_len xs d1 \<Longrightarrow> d1 \<ge> d \<Longrightarrow> env_len (take d ` xs) d"
  by (auto simp: env_len_def)

subsection \<open>Min Range approximation\<close>

lemma
  linear_lower:
  fixes x::real
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_field_derivative f' x) (at x within {a .. b})"
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> f' x \<le> u"
  assumes "x \<in> {a .. b}"
  shows "f b + u * (x - b) \<le> f x"
proof -
  from assms(2-)
    mvt_very_simple[of x b f "\<lambda>x. (*) (f' x)",
      rule_format,
      OF _ has_derivative_subset[OF assms(1)[simplified has_field_derivative_def]]]
  obtain y where "y \<in> {x .. b}"  "f b - f x = (b - x) * f' y"
    by (auto simp: Bex_def ac_simps)
  moreover hence "f' y \<le> u" using assms by auto
  ultimately have "f b - f x \<le> (b - x) * u"
    by (auto intro!: mult_left_mono)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma
  linear_lower2:
  fixes x::real
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_field_derivative f' x) (at x within {a .. b})"
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> l \<le> f' x"
  assumes "x \<in> {a .. b}"
  shows "f x \<ge> f a + l * (x - a)"
proof -
  from assms(2-)
    mvt_very_simple[of a x f "\<lambda>x. (*) (f' x)",
      rule_format,
      OF _ has_derivative_subset[OF assms(1)[simplified has_field_derivative_def]]]
  obtain y where "y \<in> {a .. x}"  "f x - f a = (x - a) * f' y"
    by (auto simp: Bex_def ac_simps)
  moreover hence "l \<le> f' y" using assms by auto
  ultimately have "(x - a) * l \<le> f x - f a"
    by (auto intro!: mult_left_mono)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma
  linear_upper:
  fixes x::real
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_field_derivative f' x) (at x within {a .. b})"
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> f' x \<le> u"
  assumes "x \<in> {a .. b}"
  shows "f x \<le> f a + u * (x - a)"
proof -
  from assms(2-)
    mvt_very_simple[of a x f "\<lambda>x. (*) (f' x)",
      rule_format,
      OF _ has_derivative_subset[OF assms(1)[simplified has_field_derivative_def]]]
  obtain y where "y \<in> {a .. x}"  "f x - f a = (x - a) * f' y"
    by (auto simp: Bex_def ac_simps)
  moreover hence "f' y \<le> u" using assms by auto
  ultimately have "(x - a) * u \<ge> f x - f a"
    by (auto intro!: mult_left_mono)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma
  linear_upper2:
  fixes x::real
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_field_derivative f' x) (at x within {a .. b})"
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> l \<le> f' x"
  assumes "x \<in> {a .. b}"
  shows "f x \<le> f b + l * (x - b)"
proof -
  from assms(2-)
    mvt_very_simple[of x b f "\<lambda>x. (*) (f' x)",
      rule_format,
      OF _ has_derivative_subset[OF assms(1)[simplified has_field_derivative_def]]]
  obtain y where "y \<in> {x .. b}"  "f b - f x = (b - x) * f' y"
    by (auto simp: Bex_def ac_simps)
  moreover hence "l \<le> f' y" using assms by auto
  ultimately have "f b - f x \<ge> (b - x) * l"
    by (auto intro!: mult_left_mono)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma linear_enclosure:
  fixes x::real
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_field_derivative f' x) (at x within {a .. b})"
  assumes "\<And>x. x \<in> {a .. b} \<Longrightarrow> f' x \<le> u"
  assumes "x \<in> {a .. b}"
  shows "f x \<in> {f b + u * (x - b) .. f a + u * (x - a)}"
  using linear_lower[OF assms] linear_upper[OF assms]
  by auto

definition "mid_err ivl = ((lower ivl + upper ivl::float)/2, (upper ivl - lower ivl)/2)"

lemma degree_aform_uminus_aform[simp]: "degree_aform (uminus_aform X) = degree_aform X"
  by (auto simp: uminus_aform_def)


subsubsection \<open>Addition\<close>

definition add_aform::"'a::real_vector aform \<Rightarrow> 'a aform \<Rightarrow> 'a aform"
  where "add_aform x y = (fst x + fst y, add_pdevs (snd x) (snd y))"

lemma aform_val_add_aform:
  shows "aform_val e (add_aform X Y) = aform_val e X + aform_val e Y"
  by (auto simp: add_aform_def aform_val_def)

type_synonym aform_err = "real aform \<times> real"

definition add_aform'::"nat \<Rightarrow> aform_err \<Rightarrow> aform_err \<Rightarrow> aform_err"
  where "add_aform' p x y =
    (let
      z0 = trunc_bound_eucl p (fst (fst x) + fst (fst y));
      z = trunc_bound_pdevs p (add_pdevs (snd (fst x)) (snd (fst y)))
      in ((fst z0, fst z), (sum_list' p [snd z0, snd z, abs (snd x), abs (snd y)])))"

abbreviation degree_aform_err::"aform_err \<Rightarrow> nat"
  where "degree_aform_err X \<equiv> degree_aform (fst X)"

lemma degree_aform_err_add_aform':
  assumes "degree_aform_err x \<le> n"
  assumes "degree_aform_err y \<le> n"
  shows "degree_aform_err (add_aform' p x y) \<le> n"
  using assms
  by (auto simp: add_aform'_def Let_def trunc_bound_pdevs_def
      intro!: degree_pdev_upd_le degree_trunc_pdevs_le degree_add_pdevs_le)

definition "aform_err e Xe = {aform_val e (fst Xe) - snd Xe .. aform_val e (fst Xe) + snd Xe::real}"

lemma aform_errI: "x \<in> aform_err e Xe"
  if "abs (x - aform_val e (fst Xe)) \<le> snd Xe"
  using that by (auto simp: aform_err_def abs_real_def algebra_simps split: if_splits)

lemma add_aform':
  assumes e: "e \<in> UNIV \<rightarrow> {- 1..1}"
  assumes x: "x \<in> aform_err e X"
  assumes y: "y \<in> aform_err e Y"
  shows "x + y \<in> aform_err e (add_aform' p X Y)"
proof -
  let ?t1 = "trunc_bound_eucl p (fst (fst X) + fst (fst Y))"
  from trunc_bound_euclE
  obtain e1 where abs_e1: "\<bar>e1\<bar> \<le> snd ?t1" and e1: "fst ?t1 = fst (fst X) + fst (fst Y) + e1"
    by blast
  let ?t2 = "trunc_bound_pdevs p (add_pdevs (snd (fst X)) (snd (fst Y)))"
  from trunc_bound_pdevsE[OF e, of p "add_pdevs (snd (fst X)) (snd (fst Y))"]
  obtain e2 where abs_e2: "\<bar>e2\<bar> \<le> snd (?t2)"
    and e2: "pdevs_val e (fst ?t2) = pdevs_val e (add_pdevs (snd (fst X)) (snd (fst Y))) + e2"
    by blast

  have e_le: "\<bar>e1 + e2 + snd X + snd Y\<bar> \<le> snd (add_aform' p (X) Y)"
    apply (auto simp: add_aform'_def Let_def )
    apply (rule sum_list'_sum_list_le)
    apply (simp add: add.assoc)
    by (intro order.trans[OF abs_triangle_ineq] add_mono abs_e1 abs_e2 order_refl)
  then show ?thesis
    apply (intro aform_errI)
    using x y abs_e1 abs_e2
    apply (simp add: aform_val_def aform_err_def add_aform_def add_aform'_def Let_def e1 e2 assms)
    by (auto intro!: order_trans[OF _ sum_list_le_sum_list'] )
qed


subsubsection \<open>Scaling\<close>

definition aform_scaleR::"real aform \<Rightarrow> 'a::real_vector \<Rightarrow> 'a aform"
  where "aform_scaleR x y = (fst x *\<^sub>R y, pdevs_scaleR (snd x) y)"

lemma aform_val_scaleR_aform[simp]:
  shows "aform_val e (aform_scaleR X y) = aform_val e X *\<^sub>R y"
  by (auto simp: aform_scaleR_def aform_val_def scaleR_left_distrib)


subsubsection \<open>Multiplication\<close>

lemma aform_val_mult_exact:
  "aform_val e x * aform_val e y =
    fst x * fst y +
    pdevs_val e (add_pdevs (scaleR_pdevs (fst y) (snd x)) (scaleR_pdevs (fst x) (snd y))) +
    (\<Sum>i<d. e i *\<^sub>R pdevs_apply (snd x) i)*(\<Sum>i<d. e i *\<^sub>R pdevs_apply (snd y) i)"
   if "degree (snd x) \<le> d" "degree (snd y) \<le> d"
   using that
  by (auto simp: pdevs_val_sum_less_degree[where d=d] aform_val_def algebra_simps)

lemma sum_times_bound:\<comment> \<open>TODO: this gives better bounds for the remainder of multiplication\<close>
  "(\<Sum>i<d. e i * f i::real) * (\<Sum>i<d. e i * g i) =
   (\<Sum>i<d. (e i)\<^sup>2 * (f i * g i)) +
   (\<Sum>(i, j) | i < j \<and> j < d. (e i * e j) * (f j * g i + f i * g j))" for d::nat
proof -
  have "(\<Sum>i<d. e i * f i)*(\<Sum>i<d. e i * g i) = (\<Sum>(i, j)\<in>{..<d} \<times> {..<d}. e i * f i * (e j * g j))"
    unfolding sum_product sum.cartesian_product ..
  also have "\<dots> = (\<Sum>(i, j)\<in>{..<d} \<times> {..<d} \<inter> {(i, j). i = j}. e i * f i * (e j * g j)) +
    ((\<Sum>(i, j)\<in>{..<d} \<times> {..<d} \<inter> {(i, j). i < j}. e i * f i * (e j * g j)) +
    (\<Sum>(i, j)\<in>{..<d} \<times> {..<d} \<inter> {(i, j). j < i}. e i * f i * (e j * g j)))"
    (is "_ = ?a + (?b + ?c)")
    by (subst sum.union_disjoint[symmetric], force, force, force)+ (auto intro!: sum.cong)
  also have "?c = (\<Sum>(i, j)\<in>{..<d} \<times> {..<d} \<inter> {(i, j). i < j}. e i * f j * (e j * g i))"
    by (rule sum.reindex_cong[of "\<lambda>(x, y). (y, x)"]) (auto intro!: inj_onI)
  also have "?b + \<dots> = (\<Sum>(i, j)\<in>{..<d} \<times> {..<d} \<inter> {(i, j). i < j}. (e i * e j) * (f j * g i + f i * g j))"
    by (auto simp: algebra_simps sum.distrib split_beta')
  also have "\<dots> = (\<Sum>(i, j) | i < j \<and> j < d. (e i * e j) * (f j * g i + f i * g j))"
    by (rule sum.cong) auto
  also have "?a = (\<Sum>i<d. (e i)\<^sup>2 * (f i * g i))"
    by (rule sum.reindex_cong[of "\<lambda>i. (i, i)"]) (auto simp: power2_eq_square intro!: inj_onI)
  finally show ?thesis by simp
qed

definition mult_aform::"aform_err \<Rightarrow> aform_err \<Rightarrow> aform_err"
  where "mult_aform x y = ((fst (fst x) * fst (fst y),
    (add_pdevs (scaleR_pdevs (fst (fst y)) (snd (fst x))) (scaleR_pdevs (fst (fst x)) (snd (fst y))))),
     (tdev (snd (fst x)) * tdev (snd (fst y)) +
      abs (snd x) * (abs (fst (fst y)) + Radius (fst y)) +
      abs (snd y) * (abs (fst (fst x)) + Radius (fst x)) + abs (snd x) * abs (snd y)
     ))"

lemma mult_aformE:
  fixes X Y::"aform_err"
  assumes e: "e \<in> UNIV \<rightarrow> {- 1..1}"
  assumes x: "x \<in> aform_err e X"
  assumes y: "y \<in> aform_err e Y"
  shows "x * y \<in> aform_err e (mult_aform X Y)"
proof -
  define ex where "ex \<equiv> x - aform_val e (fst X)"
  define ey where "ey \<equiv> y - aform_val e (fst Y)"

  have [intro, simp]: "\<bar>ex\<bar> \<le> \<bar>snd X\<bar>" "\<bar>ey\<bar> \<le> \<bar>snd Y\<bar>"
    using x y
    by (auto simp: ex_def ey_def aform_err_def)
  have "x * y =
    fst (fst X) * fst (fst Y) +
    fst (fst Y) * pdevs_val e (snd (fst X)) +
    fst (fst X) * pdevs_val e (snd (fst Y)) +

    (pdevs_val e (snd (fst X)) * pdevs_val e (snd (fst Y)) +
    ex * (fst (fst Y) + pdevs_val e (snd (fst Y))) +
    ey * (fst (fst X) + pdevs_val e (snd (fst X))) +
    ex * ey)"
    (is "_ = ?c + ?d + ?e + ?err")
    by (auto simp: ex_def ey_def algebra_simps aform_val_def)

  have abs_err: "abs ?err \<le> snd (mult_aform X Y)"
    by (auto simp: mult_aform_def abs_mult
        intro!: abs_triangle_ineq[THEN order_trans] add_mono mult_mono
          abs_pdevs_val_le_tdev e)
  show ?thesis
    apply (auto simp: intro!: aform_errI order_trans[OF _ abs_err])
    apply (subst mult_aform_def)
    apply (auto simp: aform_val_def ex_def ey_def algebra_simps)
    done
qed

definition mult_aform'::"nat \<Rightarrow> aform_err \<Rightarrow> aform_err \<Rightarrow> aform_err"
  where "mult_aform' p x y = (
    let
      (fx, sx) = x;
      (fy, sy) = y;
      ex = abs sx;
      ey = abs sy;
      z0 = trunc_bound_eucl p (fst fx * fst fy);
      u = trunc_bound_pdevs p (scaleR_pdevs (fst fy) (snd fx));
      v = trunc_bound_pdevs p (scaleR_pdevs (fst fx) (snd fy));
      w = trunc_bound_pdevs p (add_pdevs (fst u) (fst v));
      tx = tdev' p (snd fx);
      ty = tdev' p (snd fy);
      l = truncate_up p (tx * ty);
      ee = truncate_up p (ex * ey);
      e1 = truncate_up p (ex * truncate_up p (abs (fst fy) + ty));
      e2 = truncate_up p (ey * truncate_up p (abs (fst fx) + tx))
    in
      ((fst z0, (fst w)), (sum_list' p [ee, e1, e2, l, snd z0, snd u, snd v, snd w])))"

lemma aform_errE:
  "abs (x - aform_val e (fst X)) \<le> snd X"
  if "x \<in> aform_err e X"
  using that by (auto simp: aform_err_def)

lemma mult_aform'E:
  fixes X Y::"aform_err"
  assumes e: "e \<in> UNIV \<rightarrow> {- 1..1}"
  assumes x: "x \<in> aform_err e X"
  assumes y: "y \<in> aform_err e Y"
  shows "x * y \<in> aform_err e (mult_aform' p X Y)"
proof -
  let ?z0 = "trunc_bound_eucl p (fst (fst X) * fst (fst Y))"
  from trunc_bound_euclE
  obtain e1 where abs_e1: "\<bar>e1\<bar> \<le> snd ?z0" and e1: "fst ?z0 = fst (fst X) * fst (fst Y) + e1"
    by blast
  let ?u = "trunc_bound_pdevs p (scaleR_pdevs (fst (fst Y)) (snd (fst X)))"
  from trunc_bound_pdevsE[OF e]
  obtain e2 where abs_e2: "\<bar>e2\<bar> \<le> snd (?u)"
    and e2: "pdevs_val e (fst ?u) = pdevs_val e (scaleR_pdevs (fst (fst Y)) (snd (fst X))) + e2"
    by blast
  let ?v = "trunc_bound_pdevs p (scaleR_pdevs (fst (fst X)) (snd (fst Y)))"
  from trunc_bound_pdevsE[OF e]
  obtain e3 where abs_e3: "\<bar>e3\<bar> \<le> snd (?v)"
    and e3: "pdevs_val e (fst ?v) = pdevs_val e (scaleR_pdevs (fst (fst X)) (snd (fst Y))) + e3"
    by blast
  let ?w = "trunc_bound_pdevs p (add_pdevs (fst ?u) (fst ?v))"
  from trunc_bound_pdevsE[OF e]
  obtain e4 where abs_e4: "\<bar>e4\<bar> \<le> snd (?w)"
    and e4: "pdevs_val e (fst ?w) = pdevs_val e (add_pdevs (fst ?u) (fst ?v)) + e4"
    by blast
  let ?tx = "tdev' p (snd (fst X))" and ?ty = "tdev' p (snd (fst Y))"
  let ?l = "truncate_up p (?tx * ?ty)"
  let ?ee = "truncate_up p (abs (snd X) * abs (snd Y))"
  let ?e1 = "truncate_up p (abs (snd X) * truncate_up p (\<bar>fst (fst Y)\<bar> + ?ty))"
  let ?e2 = "truncate_up p (abs (snd Y) * truncate_up p (\<bar>fst (fst X)\<bar> + ?tx))"

  let ?e0 = "x * y - fst (fst X) * fst (fst Y) -
      fst (fst X) * pdevs_val e (snd (fst Y)) -
      fst (fst Y) * pdevs_val e (snd (fst X))"
  let ?err = "?e0 - (e1 + e2  + e3 + e4)"
  have "abs ?err \<le> abs ?e0 + abs e1 + abs e2 + abs e3 + abs e4"
    by arith
  also have "\<dots> \<le> abs ?e0 + snd ?z0 + snd ?u + snd ?v + snd ?w"
    unfolding abs_mult
    by (auto intro!: add_mono mult_mono e abs_pdevs_val_le_tdev' abs_ge_zero abs_e1 abs_e2 abs_e3
      abs_e4 intro: tdev'_le)
  also
  have asdf: "snd (mult_aform X Y) \<le> tdev' p (snd (fst X)) * tdev' p (snd (fst Y)) + ?e1 + ?e2 + ?ee"
    by (auto simp: mult_aform_def intro!: add_mono mult_mono order_trans[OF _ tdev'] truncate_up_le)
  have "abs ?e0 \<le> ?ee + ?e1 + ?e2 + tdev' p (snd (fst X)) * tdev' p (snd (fst Y))"
    using mult_aformE[OF e x y, THEN aform_errE, THEN order_trans, OF asdf]
    by (simp add: aform_val_def mult_aform_def) arith
  also have "tdev' p (snd (fst X)) * tdev' p (snd (fst Y)) \<le> ?l"
    by (auto intro!: truncate_up_le)
  also have "?ee + ?e1 + ?e2 + ?l + snd ?z0 + snd ?u + snd ?v + snd ?w \<le>
      sum_list' p [?ee, ?e1, ?e2, ?l, snd ?z0, snd ?u, snd ?v, snd ?w]"
    by (rule order_trans[OF _ sum_list_le_sum_list']) simp
  also have "\<dots> \<le> (snd (mult_aform' p X Y))"
    by (auto simp: mult_aform'_def Let_def assms split: prod.splits)
  finally have err_le: "abs ?err \<le> (snd (mult_aform' p X Y))" by arith

  show ?thesis
    apply (rule aform_errI[OF order_trans[OF _ err_le]])
    apply (subst mult_aform'_def)
    using e1 e2 e3 e4
    apply (auto simp: aform_val_def Let_def assms split: prod.splits)
    done
qed

lemma degree_aform_mult_aform':
  assumes "degree_aform_err x \<le> n"
  assumes "degree_aform_err y \<le> n"
  shows "degree_aform_err (mult_aform' p x y) \<le> n"
  using assms
  by (auto simp: mult_aform'_def Let_def trunc_bound_pdevs_def split: prod.splits
      intro!: degree_pdev_upd_le degree_trunc_pdevs_le degree_add_pdevs_le)

lemma
  fixes x a b::real
  assumes "a > 0"
  assumes "x \<in> {a ..b}"
  assumes "- inverse (b*b) \<le> alpha"
  shows inverse_linear_lower: "inverse b + alpha * (x - b) \<le> inverse x" (is ?lower)
    and inverse_linear_upper: "inverse x \<le> inverse a + alpha * (x - a)" (is ?upper)
proof -
  have deriv_inv:
    "\<And>x. x \<in> {a .. b} \<Longrightarrow> (inverse has_field_derivative - inverse (x*x)) (at x within {a .. b})"
    using assms
    by (auto intro!: derivative_eq_intros)
  show ?lower
    using assms
    by (intro linear_lower[OF deriv_inv])
        (auto simp: mult_mono intro!:  order_trans[OF _ assms(3)])
  show ?upper
    using assms
    by (intro linear_upper[OF deriv_inv])
        (auto simp: mult_mono intro!:  order_trans[OF _ assms(3)])
qed


subsubsection \<open>Inverse\<close>

definition inverse_aform'::"nat \<Rightarrow> real aform \<Rightarrow> real aform \<times> real" where
  "inverse_aform' p X = (
    let l = Inf_aform' p X in
    let u = Sup_aform' p X in
    let a = min (abs l) (abs u) in
    let b = max (abs l) (abs u) in
    let sq = truncate_up p (b * b) in
    let alpha = - real_divl p 1 sq in
    let dmax = truncate_up p (real_divr p 1 a - alpha * a) in
    let dmin = truncate_down p (real_divl p 1 b - alpha * b) in
    let zeta' = truncate_up p ((dmin + dmax) / 2) in
    let zeta = if l < 0 then - zeta' else zeta' in
    let delta = truncate_up p (zeta - dmin) in
    let res1 = trunc_bound_eucl p (alpha * fst X) in
    let res2 = trunc_bound_eucl p (fst res1 + zeta) in
    let zs = trunc_bound_pdevs p (scaleR_pdevs alpha (snd X)) in
    ((fst res2, fst zs), (sum_list' p [delta, snd res1, snd res2, snd zs])))"

lemma inverse_aform'E:
  fixes X::"real aform"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes Inf_pos: "Inf_aform' p X > 0"
  assumes "x = aform_val e X"
  shows "inverse x \<in> aform_err e (inverse_aform' p X)"
proof -
  define l where "l = Inf_aform' p X"
  define u where "u = Sup_aform' p X"
  define a where "a = min (abs l) (abs u)"
  define b where "b = max (abs l) (abs u)"
  define sq where "sq = truncate_up p (b * b)"
  define alpha where "alpha = - (real_divl p 1 sq)"
  define d_max' where "d_max' = truncate_up p (real_divr p 1 a - alpha * a)"
  define d_min' where "d_min' = truncate_down p (real_divl p 1 b - alpha * b)"
  define zeta where "zeta = truncate_up p ((d_min' + d_max') / 2)"
  define delta where "delta = truncate_up p (zeta - d_min')"
  note vars = l_def u_def a_def b_def sq_def alpha_def d_max'_def d_min'_def zeta_def delta_def
  let ?x = "aform_val e X"

  have "0 < l" using assms by (auto simp add: l_def Inf_aform_def)
  have "l \<le> u" by (auto simp: l_def u_def)

  hence a_def': "a = l" and b_def': "b = u" and "0 < a" "0 < b"
    using \<open>0 < l\<close> by (simp_all add: a_def b_def)
  have "0 < ?x"
    by (rule less_le_trans[OF Inf_pos order.trans[OF Inf_aform' Inf_aform], OF e])
  have "a \<le> ?x"
    by (metis order.trans Inf_aform e Inf_aform' a_def' l_def)
  have "?x \<le> b"
    by (metis order.trans Sup_aform e Sup_aform' b_def' u_def)
  hence "?x \<in> {?x .. b}"
    by simp

  have "- inverse (b * b) \<le> alpha"
    by (auto simp add: alpha_def inverse_mult_distrib[symmetric] inverse_eq_divide sq_def
      intro!: order_trans[OF real_divl] divide_left_mono truncate_up mult_pos_pos \<open>0 < b\<close>)

  {
    note \<open>0 < a\<close>
    moreover
    have "?x \<in> {a .. b}" using \<open>a \<le> ?x\<close> \<open>?x \<le> b\<close> by simp
    moreover
    note \<open>- inverse (b * b) \<le> alpha\<close>
    ultimately have "inverse ?x \<le> inverse a + alpha * (?x - a)"
      by (rule inverse_linear_upper)
    also have "\<dots> = alpha * ?x + (inverse a - alpha * a)"
      by (simp add: algebra_simps)
    also have "inverse a - (alpha * a) \<le> (real_divr p 1 a - alpha * a)"
      by (auto simp: inverse_eq_divide real_divr)
    also have "\<dots> \<le> (truncate_down p (real_divl p 1 b - alpha * b) +
          (real_divr p 1 a - alpha * a)) / 2 +
        (truncate_up p (real_divr p 1 a - alpha * a) -
          truncate_down p (real_divl p 1 b - alpha * b)) / 2"
      (is "_ \<le> (truncate_down p ?lb + ?ra) / 2 + (truncate_up p ?ra - truncate_down p ?lb) / 2")
      by (auto simp add: field_simps
        intro!: order_trans[OF _ add_left_mono[OF mult_left_mono[OF truncate_up]]])
    also have "(truncate_down p ?lb + ?ra) / 2 \<le>
        truncate_up p ((truncate_down p ?lb + truncate_up p ?ra) / 2)"
      by (intro truncate_up_le divide_right_mono add_left_mono truncate_up) auto
    also
    have "(truncate_up p ?ra - truncate_down p ?lb) / 2 + truncate_down p ?lb \<le>
        (truncate_up p ((truncate_down p ?lb + truncate_up p ?ra) / 2))"
      by (rule truncate_up_le) (simp add: field_simps)
    hence "(truncate_up p ?ra - truncate_down p ?lb) / 2 \<le> truncate_up p
        (truncate_up p ((truncate_down p ?lb + truncate_up p ?ra) / 2) - truncate_down p ?lb)"
      by (intro truncate_up_le) (simp add: field_simps)
    finally have "inverse ?x \<le> alpha * ?x + zeta + delta"
      by (auto simp: zeta_def delta_def d_min'_def d_max'_def right_diff_distrib ac_simps)
  } note upper = this

  {
    have "alpha * b + truncate_down p (real_divl p 1 b - alpha * b) \<le> inverse b"
      by (rule order_trans[OF add_left_mono[OF truncate_down]])
        (auto simp: inverse_eq_divide real_divl)
    hence "zeta + alpha * b \<le> delta + inverse b"
      by (auto simp: zeta_def delta_def d_min'_def d_max'_def right_diff_distrib
        intro!: order_trans[OF _ add_right_mono[OF truncate_up]])
    hence "alpha * ?x + zeta - delta \<le> inverse b + alpha * (?x - b)"
      by (simp add: algebra_simps)
    also
    {
      note \<open>0 < aform_val e X\<close>
      moreover
      note \<open>aform_val e X \<in> {aform_val e X .. b}\<close>
      moreover

      note \<open>- inverse (b * b) \<le> alpha\<close>
      ultimately
      have "inverse b + alpha * (aform_val e X - b) \<le> inverse (aform_val e X)"
        by (rule inverse_linear_lower)
    }
    finally have "alpha * (aform_val e X) + zeta - delta \<le> inverse (aform_val e X)" .
  } note lower = this


  have "inverse (aform_val e X) = alpha * (aform_val e X) + zeta +
      (inverse (aform_val e X) - alpha * (aform_val e X) - zeta)"
    (is "_ = _ + ?linerr")
    by simp
  also
  have "?linerr \<in> {- delta .. delta}"
    using lower upper by simp
  hence linerr_le: "abs ?linerr \<le> delta"
    by auto

  let ?z0 = "trunc_bound_eucl p (alpha * fst X)"
  from trunc_bound_euclE
  obtain e1 where abs_e1: "\<bar>e1\<bar> \<le> snd ?z0" and e1: "fst ?z0 = alpha * fst X + e1"
    by blast
  let ?z1 = "trunc_bound_eucl p (fst ?z0 + zeta)"
  from trunc_bound_euclE
  obtain e1' where abs_e1': "\<bar>e1'\<bar> \<le> snd ?z1" and e1': "fst ?z1 = fst ?z0 + zeta + e1'"
    by blast

  let ?zs = "trunc_bound_pdevs p (scaleR_pdevs alpha (snd X))"
  from trunc_bound_pdevsE[OF e]
  obtain e2 where abs_e2: "\<bar>e2\<bar> \<le> snd (?zs)"
    and e2: "pdevs_val e (fst ?zs) = pdevs_val e (scaleR_pdevs alpha (snd X)) + e2"
    by blast

  have "alpha * (aform_val e X) + zeta =
      aform_val e (fst (inverse_aform' p X)) + (- e1 - e1' - e2)"
    unfolding inverse_aform'_def Let_def vars[symmetric]
    using \<open>0 < l\<close>
    by (simp add: aform_val_def assms e1') (simp add: e1 e2 algebra_simps)
  also
  let ?err = "(- e1 - e1' - e2 + inverse (aform_val e X) - alpha * aform_val e X - zeta)"
  {
    have "abs ?err \<le> abs ?linerr + abs e1 + abs e1' + abs e2"
      by simp
    also have "\<dots> \<le> delta + snd ?z0 + snd ?z1 + snd ?zs"
      by (blast intro: add_mono linerr_le abs_e1 abs_e1' abs_e2)
    also have "\<dots> \<le> (snd (inverse_aform' p X))"
      unfolding inverse_aform'_def Let_def vars[symmetric]
      using \<open>0 < l\<close>
      by (auto simp add: inverse_aform'_def pdevs_apply_trunc_pdevs assms vars[symmetric]
        intro!: order.trans[OF _ sum_list'_sum_list_le])
    finally have "abs ?err \<le> snd (inverse_aform' p X)" by simp
  } note err_le = this
  have "aform_val (e) (fst (inverse_aform' p X)) + (- e1 - e1' - e2) +
    (inverse (aform_val e X) - alpha * aform_val e X - zeta) =
    aform_val e (fst (inverse_aform' p X)) + ?err"
    by simp
  finally
  show ?thesis
    apply (intro aform_errI)
    using err_le
    by (auto simp: assms)
qed

definition "inverse_aform p a =
  do {
    let l = Inf_aform' p a;
    let u = Sup_aform' p a;
    if (l \<le> 0 \<and> 0 \<le> u) then None
    else if (l \<le> 0) then (Some (apfst uminus_aform (inverse_aform' p (uminus_aform a))))
    else Some (inverse_aform' p a)
  }"

lemma eucl_truncate_up_eq_eucl_truncate_down:
  "eucl_truncate_up p x = - (eucl_truncate_down p (- x))"
  by (auto simp: eucl_truncate_up_def eucl_truncate_down_def truncate_up_eq_truncate_down sum_negf)

lemma inverse_aformE:
  fixes X::"real aform"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
    and disj: "Inf_aform' p X > 0 \<or> Sup_aform' p X < 0"
  obtains Y where
    "inverse_aform p X = Some Y"
    "inverse (aform_val e X) \<in> aform_err e Y"
proof -
  {
    assume neg: "Sup_aform' p X < 0"
    from neg have [simp]: "Inf_aform' p X \<le> 0"
      by (metis Inf_aform'_le_Sup_aform' dual_order.strict_trans1 less_asym not_less)
    from neg disj have "0 < Inf_aform' p (uminus_aform X)"
      by (auto simp: Inf_aform'_def Sup_aform'_def eucl_truncate_up_eq_eucl_truncate_down ac_simps)
    from inverse_aform'E[OF e(1) this]
    have iin: "inverse (aform_val e (uminus_aform X)) \<in> aform_err e (inverse_aform' p (uminus_aform X))"
      by simp
    let ?Y = "apfst uminus_aform (inverse_aform' p (uminus_aform X))"
    have "inverse_aform p X = Some ?Y"
      "inverse (aform_val e X) \<in> aform_err e ?Y"
      using neg iin by (auto simp: inverse_aform_def aform_err_def)
    then have ?thesis ..
  } moreover {
    assume pos: "Inf_aform' p X > 0"
    from pos have eq: "inverse_aform p X = Some (inverse_aform' p X)"
      by (auto simp: inverse_aform_def)
    moreover
    from inverse_aform'E[OF e(1) pos refl]
    have "inverse (aform_val e X) \<in> aform_err e (inverse_aform' p X)" .
    ultimately have ?thesis ..
  } ultimately show ?thesis
    using assms by auto
qed

definition aform_err_to_aform::"aform_err \<Rightarrow> nat \<Rightarrow> real aform"
  where "aform_err_to_aform X n = (fst (fst X),  pdev_upd (snd (fst X)) n (snd X))"

lemma aform_err_to_aformE:
  assumes "x \<in> aform_err e X"
  assumes deg: "degree_aform_err X \<le> n"
  obtains err where "x = aform_val (e(n:=err)) (aform_err_to_aform X n)"
    "-1 \<le> err" "err \<le> 1"
proof -
  from aform_errE[OF assms(1)] have "\<bar>x - aform_val e (fst X)\<bar> \<le> snd X" by auto
  from error_absE[OF this] obtain err where err:
    "x - aform_val e (fst X) = err * snd X" "err \<in> {- 1..1}"
    by auto
  have "x = aform_val (e(n:=err)) (aform_err_to_aform X n)"
    "-1 \<le> err" "err \<le> 1"
    using err deg
    by (auto simp: aform_val_def aform_err_to_aform_def)
  then show ?thesis ..
qed

definition aform_to_aform_err::"real aform \<Rightarrow> nat \<Rightarrow> aform_err"
  where "aform_to_aform_err X n = ((fst X,  pdev_upd (snd X) n 0), abs (pdevs_apply (snd X) n))"

lemma aform_to_aform_err: "aform_val e X \<in> aform_err e (aform_to_aform_err X n)"
  if "e \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  from that have abs_e[simp]: "\<And>i. \<bar>e i\<bar> \<le> 1" by (auto simp: abs_real_def)
  have "- e n * pdevs_apply (snd X) n \<le> \<bar>pdevs_apply (snd X) n\<bar>"
  proof -
    have "- e n * pdevs_apply (snd X) n \<le> \<bar>- e n * pdevs_apply (snd X) n\<bar>"
      by auto
    also have "\<dots> \<le> abs (pdevs_apply (snd X) n)"
      using that
      by (auto simp: abs_mult intro!: mult_left_le_one_le)
    finally show ?thesis .
  qed
  moreover have "e n * pdevs_apply (snd X) n \<le> \<bar>pdevs_apply (snd X) n\<bar>"
  proof -
    have "e n * pdevs_apply (snd X) n \<le> \<bar>e n * pdevs_apply (snd X) n\<bar>"
      by auto
    also have "\<dots> \<le> abs (pdevs_apply (snd X) n)"
      using that
      by (auto simp: abs_mult intro!: mult_left_le_one_le)
    finally show ?thesis .
  qed
  ultimately
  show ?thesis
    by (auto simp: aform_to_aform_err_def aform_err_def aform_val_def)
qed

definition "acc_err p x e \<equiv> (fst x, truncate_up p (snd x + e))"

definition ivl_err :: "real interval \<Rightarrow> (real \<times> real pdevs) \<times> real"
  where "ivl_err ivl \<equiv> (((upper ivl + lower ivl)/2, zero_pdevs::real pdevs), (upper ivl - lower ivl) / 2)"

lemma inverse_aform:
  fixes X::"real aform"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "inverse_aform p X = Some Y"
  shows "inverse (aform_val e X) \<in> aform_err e Y"
proof -
  from assms have "Inf_aform' p X > 0 \<or> 0 > Sup_aform' p X"
    by (auto simp: inverse_aform_def Let_def bind_eq_Some_conv split: if_splits)
  from inverse_aformE[OF e this] obtain Y where
    "inverse_aform p X = Some Y" "inverse (aform_val e X) \<in> aform_err e Y"
    by auto
  with assms show ?thesis by auto
qed

lemma aform_err_acc_err_leI:
  "fx \<in> aform_err e (acc_err p X err)"
  if "aform_val e (fst X) - (snd X + err) \<le> fx" "fx \<le> aform_val e (fst X) + (snd X + err)"
  using truncate_up[of "(snd X + err)" p] truncate_down[of p "(snd X + err)"] that
  by (auto simp: aform_err_def acc_err_def)

lemma aform_err_acc_errI:
  "fx \<in> aform_err e (acc_err p X err)"
  if "fx \<in> aform_err e (fst X, snd X + err)"
  using truncate_up[of "(snd X + err)" p] truncate_down[of p "(snd X + err)"] that
  by (auto simp: aform_err_def acc_err_def)

lemma minus_times_le_abs: "- (err * B) \<le> \<bar>B\<bar>" if "-1 \<le> err" "err \<le> 1" for err::real
proof -
  have [simp]: "abs err \<le> 1" using that by (auto simp: )
  have "- (err * B) \<le> abs (- err * B)" by auto
  also have "\<dots> \<le> abs B"
    by (auto simp: abs_mult intro!: mult_left_le_one_le)
  finally show ?thesis by simp
qed

lemma times_le_abs: "err * B \<le> \<bar>B\<bar>" if "-1 \<le> err" "err \<le> 1" for err::real
proof -
  have [simp]: "abs err \<le> 1" using that by (auto simp: )
  have "err * B \<le> abs (err * B)" by auto
  also have "\<dots> \<le> abs B"
    by (auto simp: abs_mult intro!: mult_left_le_one_le)
  finally show ?thesis by simp
qed

lemma aform_err_lemma1: "- 1 \<le> err \<Longrightarrow> err \<le> 1 \<Longrightarrow>
  X1 + (A - e d * B + err * B) - e1 \<le> x \<Longrightarrow>
  X1 + (A - e d * B) - truncate_up p (\<bar>B\<bar> + e1) \<le> x"
  apply (rule order_trans)
   apply (rule diff_mono)
    apply (rule order_refl)
   apply (rule truncate_up_le[where x="e1 - err * B"])
  by (auto simp: minus_times_le_abs)
  
lemma aform_err_lemma2: "- 1 \<le> err \<Longrightarrow> err \<le> 1 \<Longrightarrow>
    x \<le> X1 + (A - e d * B + err * B) + e1 \<Longrightarrow>
    x \<le> X1 + (A - e d * B) + truncate_up p (\<bar>B\<bar> + e1)"
  apply (rule order_trans[rotated])
   apply (rule add_mono)
    apply (rule order_refl)
   apply (rule truncate_up_le[where x="e1 + err * B"])
  by (auto simp: times_le_abs)

lemma aform_err_acc_err_aform_to_aform_errI:
  "x \<in> aform_err e (acc_err p (aform_to_aform_err X1 d) e1)"
  if "-1 \<le> err" "err \<le> 1" "x \<in> aform_err (e(d := err)) (X1, e1)"
  using that
  by (auto simp: acc_err_def aform_err_def aform_val_def aform_to_aform_err_def
      aform_err_to_aform_def aform_err_lemma1 aform_err_lemma2)

definition "map_aform_err I p X =
  (do {
    let X0 = aform_err_to_aform X (degree_aform_err X);
    (X1, e1) \<leftarrow> I X0;
    Some (acc_err p (aform_to_aform_err X1 (degree_aform_err X)) e1)
  })"

lemma map_aform_err:
  "i x \<in> aform_err e Y"
  if I: "\<And>e X Y. e \<in> UNIV \<rightarrow> {-1 .. 1} \<Longrightarrow> I X = Some Y \<Longrightarrow> i (aform_val e X) \<in> aform_err e Y"
  and e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  and Y: "map_aform_err I p X = Some Y"
  and x: "x \<in> aform_err e X"
proof -
  obtain X1 e1 where
    X1: "(I (aform_err_to_aform X (degree_aform_err X))) = Some (X1, e1)"
    and Y: "Y = acc_err p (aform_to_aform_err X1 (degree_aform (fst X))) e1"
    using Y by (auto simp: map_aform_err_def bind_eq_Some_conv Let_def)
  from aform_err_to_aformE[OF x] obtain err where
    err: "x = aform_val (e(degree_aform_err X := err)) (aform_err_to_aform X  (degree_aform_err X)) "
    (is "_ = aform_val ?e _")
    and "- 1 \<le> err" "err \<le> 1"
    by auto
  then have e': "?e \<in> UNIV \<rightarrow> {-1 .. 1}" using e by auto
  from err have "i x =
      i (aform_val (e(degree_aform_err X := err)) (aform_err_to_aform X  (degree_aform_err X)))"
    by simp
  also note I[OF e' X1]
  also have "aform_err (e(degree_aform_err X := err)) (X1, e1) \<subseteq> aform_err e Y"
    apply rule
    unfolding Y using \<open>-1 \<le> err\<close> \<open>err \<le> 1\<close>
    by (rule aform_err_acc_err_aform_to_aform_errI)
  finally show ?thesis .
qed

definition "inverse_aform_err p X = map_aform_err (inverse_aform p) p X"

lemma inverse_aform_err:
  "inverse x \<in> aform_err e Y"
  if  e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  and Y: "inverse_aform_err p X = Some Y"
  and x: "x \<in> aform_err e X"
  using map_aform_err[OF inverse_aform[where p=p] e Y[unfolded inverse_aform_err_def] x]
  by auto

subsection \<open>Reduction (Summarization of Coefficients)\<close>
text \<open>\label{sec:affinesummarize}\<close>

definition "pdevs_of_centered_ivl r = (inner_scaleR_pdevs r One_pdevs)"

lemma pdevs_of_centered_ivl_eq_pdevs_of_ivl[simp]: "pdevs_of_centered_ivl r = pdevs_of_ivl (-r) r"
  by (auto simp: pdevs_of_centered_ivl_def pdevs_of_ivl_def algebra_simps intro!: pdevs_eqI)

lemma filter_pdevs_raw_nonzeros: "{i. filter_pdevs_raw s f i \<noteq> 0} = {i. f i \<noteq> 0} \<inter> {x. s x (f x)}"
  by (auto simp: filter_pdevs_raw_def)

definition summarize_pdevs::
  "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a::executable_euclidean_space pdevs \<Rightarrow> 'a pdevs"
  where "summarize_pdevs p I d x =
    (let t = tdev' p (filter_pdevs (-I) x)
     in msum_pdevs d (filter_pdevs I x) (pdevs_of_centered_ivl t))"

definition summarize_threshold
  where "summarize_threshold p t x y \<longleftrightarrow> infnorm y \<ge> t * infnorm (eucl_truncate_up p (tdev' p x))"

lemma error_abs_euclE:
  fixes err::"'a::ordered_euclidean_space"
  assumes "abs err \<le> k"
  obtains e::"'a \<Rightarrow> real" where "err = (\<Sum>i\<in>Basis. (e i * (k \<bullet> i)) *\<^sub>R i)" "e \<in> UNIV \<rightarrow> {-1 .. 1}"
proof atomize_elim
  {
    fix i::'a
    assume "i \<in> Basis"
    hence "abs (err \<bullet> i) \<le> (k \<bullet> i)" using assms by (auto simp add: eucl_le[where 'a='a] abs_inner)
    hence "\<exists>e. (err  \<bullet> i = e * (k \<bullet> i)) \<and> e \<in> {-1..1}"
      by (rule error_absE) auto
  }
  then obtain e where e:
    "\<And>i. i \<in> Basis \<Longrightarrow> err \<bullet> i = e i * (k \<bullet> i)"
    "\<And>i. i \<in> Basis \<Longrightarrow> e i \<in> {-1 .. 1}"
    by metis
  have singleton: "\<And>b. b \<in> Basis \<Longrightarrow> (\<Sum>i\<in>Basis. e i * (k \<bullet> i) * (if i = b then 1 else 0)) =
    (\<Sum>i\<in>{b}. e i * (k \<bullet> i) * (if i = b then 1 else 0))"
    by (rule sum.mono_neutral_cong_right) auto
  show "\<exists>e::'a\<Rightarrow>real. err = (\<Sum>i\<in>Basis. (e i * (k \<bullet> i)) *\<^sub>R i) \<and> (e \<in> UNIV \<rightarrow> {-1..1})"
    using e
    by (auto intro!: exI[where x="\<lambda>i. if i \<in> Basis then e i else 0"] euclidean_eqI[where 'a='a]
      simp: inner_sum_left inner_Basis singleton)
qed

lemma summarize_pdevsE:
  fixes x::"'a::executable_euclidean_space pdevs"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes d: "degree x \<le> d"
  obtains e' where "pdevs_val e x = pdevs_val e' (summarize_pdevs p I d x)"
    "\<And>i. i < d \<Longrightarrow> e i = e' i"
    "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
proof atomize_elim
  have "pdevs_val e x = (\<Sum>i<degree x. e i *\<^sub>R pdevs_apply x i)"
    by (auto simp add: pdevs_val_sum intro!: sum.cong)
  also have "\<dots> = (\<Sum>i \<in> {..<degree x} \<inter> {i. I i (pdevs_apply x i)}. e i *\<^sub>R pdevs_apply x i) +
    (\<Sum>i\<in> {..<degree x} - {i. I i (pdevs_apply x i)}. e i *\<^sub>R pdevs_apply x i)"
    (is "_ = ?large + ?small")
    by (subst sum.union_disjoint[symmetric]) (auto simp: ac_simps intro!: sum.cong)
  also have "?large = pdevs_val e (filter_pdevs I x)"
    by (simp add: pdevs_val_filter_pdevs)
  also have "?small = pdevs_val e (filter_pdevs (-I) x)"
    by (simp add: pdevs_val_filter_pdevs Collect_neg_eq Diff_eq)
  also
  have "abs \<dots> \<le> tdev' p (filter_pdevs (-I) x)" (is "abs ?r \<le> ?t")
    using e by (rule abs_pdevs_val_le_tdev')
  hence "?r \<in> {-?t .. ?t}"
    by (metis abs_le_D1 abs_le_D2 atLeastAtMost_iff minus_le_iff)
  from in_ivl_affine_of_ivlE[OF this] obtain e2
    where "?r = aform_val e2 (aform_of_ivl (- ?t) ?t)"
      and e2: "e2 \<in> UNIV \<rightarrow> {- 1..1}"
    by metis
  note this(1)
  also
  define e' where "e' i = (if i < d then e i else e2 (i - d))" for i
  hence "aform_val e2 (aform_of_ivl (- ?t) ?t) =
      pdevs_val (\<lambda>i. e' (i + d)) (pdevs_of_ivl (- ?t) ?t)"
    by (auto simp: aform_of_ivl_def aform_val_def)
  also
  have "pdevs_val e (filter_pdevs I x) = pdevs_val e' (filter_pdevs I x)"
    using assms by (auto simp: e'_def pdevs_val_sum intro!: sum.cong)
  finally have "pdevs_val e x =
      pdevs_val e' (filter_pdevs I x) + pdevs_val (\<lambda>i. e' (i + d)) (pdevs_of_ivl (- ?t) ?t)"
    .
  also note pdevs_val_msum_pdevs[symmetric, OF order_trans[OF degree_filter_pdevs_le d]]
  finally have "pdevs_val e x = pdevs_val e' (summarize_pdevs p I d x)"
    by (auto simp: summarize_pdevs_def Let_def)
  moreover have "e' \<in> UNIV \<rightarrow> {-1 .. 1}" using e e2 by (auto simp: e'_def Pi_iff)
  moreover have "\<forall>i < d. e' i = e i"
    by (auto simp: e'_def)
  ultimately show "\<exists>e'. pdevs_val e x = pdevs_val e' (summarize_pdevs p I d x) \<and>
      (\<forall>i<d. e i = e' i) \<and> e' \<in> UNIV \<rightarrow> {- 1..1}"
    by auto
qed

definition "summarize_pdevs_list p I d xs =
  map (\<lambda>(d, x). summarize_pdevs p (\<lambda>i _. I i (pdevs_applys xs i)) d x) (zip [d..<d + length xs] xs)"

lemma filter_pdevs_cong[cong]:
  assumes "x = y"
  assumes "\<And>i. i \<in> pdevs_domain y \<Longrightarrow> P i (pdevs_apply x i) = Q i (pdevs_apply y i)"
  shows "filter_pdevs P x = filter_pdevs Q y"
  using assms
  by (force intro!: pdevs_eqI)

lemma summarize_pdevs_cong[cong]:
  assumes "p = q" "a = c" "b = d"
  assumes PQ: "\<And>i. i \<in> pdevs_domain d \<Longrightarrow> P i (pdevs_apply b i) = Q i (pdevs_apply d i)"
  shows "summarize_pdevs p P a b = summarize_pdevs q Q c d"
proof -
  have "(filter_pdevs P b) = filter_pdevs Q d"
    "(filter_pdevs (\<lambda>a b. \<not> P a b) b) = filter_pdevs (\<lambda>a b. \<not> Q a b) d"
    using assms
    by (auto intro!: filter_pdevs_cong)
  then show ?thesis by (auto simp add: assms summarize_pdevs_def Let_def)
qed

lemma lookup_eq_None_iff: "(Mapping.lookup M x = None) = (x \<notin> Mapping.keys M)"
  by (transfer) auto

lemma lookup_eq_SomeD:
  "(Mapping.lookup M x = Some y) \<Longrightarrow> (x \<in> Mapping.keys M)"
  by transfer auto

definition "domain_pdevs xs = (\<Union>(pdevs_domain ` (set xs)))"

definition "pdevs_mapping xs =
  (let
    D = sorted_list_of_set (domain_pdevs xs);
    M = Mapping.tabulate D (pdevs_applys xs);
    zeroes = replicate (length xs) 0
  in Mapping.lookup_default zeroes M)"

lemma pdevs_mapping_eq[simp]: "pdevs_mapping xs = pdevs_applys xs"
  unfolding pdevs_mapping_def pdevs_applys_def
  apply (auto simp: Mapping.lookup_default_def lookup_eq_None_iff domain_pdevs_def
      split: option.splits intro!: ext)
  subgoal by (auto intro!: nth_equalityI)
  subgoal apply (auto intro!: nth_equalityI dest: )
    subgoal
      apply (frule lookup_eq_SomeD)
      apply auto
      by (metis distinct_sorted_list_of_set keys_tabulate length_map lookup_eq_SomeD lookup_tabulate option.inject)
    subgoal
      apply (frule lookup_eq_SomeD)
      apply (auto simp: map_nth)
      by (metis (mono_tags, lifting) keys_tabulate
          lookup_eq_SomeD lookup_tabulate option.inject distinct_sorted_list_of_set)
    done
  done

lemma compute_summarize_pdevs_list[code]:
  "summarize_pdevs_list p I d xs =
    (let M = pdevs_mapping xs
    in map (\<lambda>(x, y). summarize_pdevs p (\<lambda>i _. I i (M i)) x y) (zip [d..<d + length xs] xs))"
  unfolding summarize_pdevs_list_def pdevs_mapping_eq
  by auto

lemma
  in_centered_ivlE:
  fixes r t::real
  assumes "r \<in> {-t .. t}"
  obtains e where "e \<in> {-1 .. 1}" "r = e * t"
  using assms
  by (atomize_elim) (auto intro!: exI[where x="r / t"] simp: divide_simps)

lift_definition singleton_pdevs::"'a \<Rightarrow> 'a::real_normed_vector pdevs" is "\<lambda>x i. if i = 0 then x else 0"
  by auto
lemmas [simp] = singleton_pdevs.rep_eq

lemma singleton_0[simp]: "singleton_pdevs 0 = zero_pdevs"
  by (auto intro!: pdevs_eqI)

lemma degree_singleton_pdevs[simp]: "degree (singleton_pdevs x) = (if x = 0 then 0 else Suc 0)"
  by (auto simp: intro!: degree_eqI)

lemma pdevs_val_singleton_pdevs[simp]: "pdevs_val e (singleton_pdevs x) = e 0 *\<^sub>R x"
  by (auto simp: pdevs_val_sum if_distrib sum.delta cong: if_cong)

lemma pdevs_of_ivl_real:
  fixes a b::real
  shows "pdevs_of_ivl a b = singleton_pdevs ((b - a) / 2)"
  by (auto simp: pdevs_of_ivl_def Basis_list_real_def intro!: pdevs_eqI)

lemma summarize_pdevs_listE:
  fixes X::"real pdevs list"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes d: "degrees X \<le> d"
  obtains e' where "pdevs_vals e X = pdevs_vals e' (summarize_pdevs_list p I d X)"
    "\<And>i. i < d \<Longrightarrow> e i = e' i"
    "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  let ?I = "{i. I i (pdevs_applys X i)}"
  let ?J = "\<lambda>i x. I i (pdevs_applys X i)"

  have "pdevs_vals e X = map (\<lambda>x. \<Sum>i<degree x. e i *\<^sub>R pdevs_apply x i) X"
    using d
    by (auto simp: pdevs_vals_def
        simp del: real_scaleR_def
        intro!: pdevs_val_sum_le
        dest!: degrees_leD)
  also have "\<dots> = map (\<lambda>x.
      (\<Sum>i\<in>{..<degree x} \<inter> ?I. e i * pdevs_apply x i) +
      (\<Sum>i\<in>{..<degree x} - ?I. e i * pdevs_apply x i)) X"
    by (rule map_cong[OF refl], subst sum.union_disjoint[symmetric]) (auto intro!: sum.cong)
  also
  have "\<dots> = map (\<lambda>x. pdevs_val e (filter_pdevs ?J x) + pdevs_val e (filter_pdevs (-?J) x)) X"
    (is "_ = map (\<lambda>x. ?large x + ?small x) _")
    by (auto simp: pdevs_val_filter_pdevs Diff_eq Compl_eq)
  also have "\<dots> = map snd (zip [d..<d + length X] \<dots>)" by simp
  also have "\<dots> = map (\<lambda>(d, x). ?large x + ?small x) (zip [d..<d + length X] X)"
    (is "_ = map _ ?z")
    unfolding map_zip_map2
    by simp
  also have "\<dots> = map (\<lambda>(d', x). ?large x + ?small (snd (?z ! (d' - d)))) ?z"
    by (auto simp: in_set_zip)
  also
  let ?t = "\<lambda>x. tdev' p (filter_pdevs (-?J) x)"
  let ?x = "\<lambda>d'. snd (?z ! (d' - d))"
  {
    fix d' assume "d \<le> d'" "d' < d + length X"
    have "abs (?small (?x d')) \<le> ?t (?x d')"
      using \<open>e \<in> _\<close> by (rule abs_pdevs_val_le_tdev')
    then have "?small (?x d') \<in> {-?t (?x d') .. ?t (?x d')}"
      by auto
    from in_centered_ivlE[OF this] have "\<exists>e\<in>{-1 .. 1}. ?small (?x d') = e * ?t (?x d')" by blast
  } then obtain e'' where e'':
    "e'' d' \<in> {-1 .. 1}"
    "?small (?x d') = e'' d' * ?t (?x d')"
    if "d' \<in> {d ..< d + length X}" for d'
    apply atomize_elim
    unfolding all_conj_distrib[symmetric] imp_conjR[symmetric]
    unfolding Ball_def[symmetric] atLeastAtMost_iff[symmetric]
    apply (rule bchoice)
    apply (auto simp: Bex_def )
    done
  define e' where "e' \<equiv> \<lambda>i. if i < d then e i else if i < d + length X then e'' i else 0"
  have e': "e' d' \<in> {-1 .. 1}"
    "?small (?x d') = e' d' * ?t (?x d')"
    if "d' \<in> {d ..< d + length X}" for d'
    using e'' that
    by (auto simp: e'_def split: if_splits)
  then have *: "pdevs_val e (filter_pdevs (\<lambda>a b. \<not> I a (pdevs_applys X a)) (?x d')) =
    e' d' * ?t (?x d')" if "d' \<in> {d ..< d + length X}" for d'
    using that
    by auto
  have "map (\<lambda>(d', x). ?large x + ?small (?x d')) ?z =
      map (\<lambda>(d', x). ?large x + e' d' * ?t (?x d')) ?z"
    apply (auto simp: in_set_zip)
    subgoal for n
      using e'(2)[of "d + n"]
      by auto
    done
  also have "\<dots> = map (\<lambda>(d', x). pdevs_val e' (summarize_pdevs p ?J d' x)) (zip [d..<d + length X] X)"
    apply (auto simp: summarize_pdevs_def pdevs_val_msum_pdevs Let_def in_set_zip)
    apply (subst pdevs_val_msum_pdevs)
    using d
     apply (auto intro!: degree_filter_pdevs_le[THEN order_trans])
    subgoal by (auto dest!: degrees_leD nth_mem)
    apply (auto simp: pdevs_of_ivl_real intro!: )
    subgoal premises prems
    proof -
      have "degree (filter_pdevs (\<lambda>i x. I i (pdevs_applys X i)) (X ! n)) \<le> d" if "n < length X" for n
        using d that
        by (intro degree_filter_pdevs_le[THEN order_trans]) (simp add: degrees_leD)
      then show ?thesis
        using prems e''
        apply (intro pdevs_val_degree_cong)
         apply (auto dest!: )
        apply (auto simp: e'_def)
        apply (meson \<open>\<And>n. \<lbrakk>n < length X; degrees X \<le> d\<rbrakk> \<Longrightarrow> degree (X ! n) \<le> d + n\<close> degree_filter_pdevs_le less_le_trans)
        by (meson less_le_trans trans_less_add1)
    qed
    done
  also have "\<dots> = pdevs_vals e' (summarize_pdevs_list p I d X)"
    by (auto simp: summarize_pdevs_list_def pdevs_vals_def)
  finally have "pdevs_vals e X = pdevs_vals e' (summarize_pdevs_list p I d X)" .
  moreover have "(\<And>i. i < d \<Longrightarrow> e i = e' i)" "e' \<in> UNIV \<rightarrow> {- 1..1}"
    using \<open>e \<in> _\<close> e''
    by (auto simp: e'_def)
  ultimately show ?thesis ..
qed

fun list_ex2 where
  "list_ex2 P [] xs = False"
| "list_ex2 P xs [] = False"
| "list_ex2 P (x#xs) (y#ys) = (P x y \<or> list_ex2 P xs ys)"

lemma list_ex2_iff:
  "list_ex2 P xs ys \<longleftrightarrow> (\<not>list_all2 (-P) (take (length ys) xs) (take (length xs) ys))"
  by (induction P xs ys rule: list_ex2.induct) auto

definition "summarize_aforms p C d (X::real aform list) =
  (zip (map fst X) (summarize_pdevs_list p (C X) d (map snd X)))"

lemma aform_vals_pdevs_vals:
  "aform_vals e X = map (\<lambda>(x, y). x + y) (zip (map fst X) (pdevs_vals e (map snd X)))"
  by (auto simp: pdevs_vals_def aform_vals_def aform_val_def[abs_def]
      map_zip_map map_zip_map2 split_beta' zip_same_conv_map)

lemma summarize_aformsE:
  fixes X::"real aform list"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes d: "degree_aforms X \<le> d"
  obtains e' where "aform_vals e X = aform_vals e' (summarize_aforms p C d X)"
    "\<And>i. i < d \<Longrightarrow> e i = e' i"
    "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  define Xs where "Xs = map snd X"
  have "aform_vals e X = map (\<lambda>(x, y). x + y) (zip (map fst X) (pdevs_vals e Xs))"
    by (auto simp: aform_vals_pdevs_vals Xs_def)
  also obtain e' where e': "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
    "\<And>i. i < d \<Longrightarrow> e i = e' i"
    "pdevs_vals e Xs = pdevs_vals e' (summarize_pdevs_list p (C X) d Xs)"
    using summarize_pdevs_listE[OF e d, of p "C X"]
    by (metis Xs_def)
  note this(3)
  also have "map (\<lambda>(x, y). x + y) (zip (map fst X) \<dots>) = aform_vals e' (summarize_aforms p C d X)"
    unfolding aform_vals_pdevs_vals
    by (simp add: summarize_aforms_def Let_def Xs_def summarize_pdevs_list_def
        split_beta')
  finally have "aform_vals e X = aform_vals e' (summarize_aforms p C d X)"
    "\<And>i. i < d \<Longrightarrow> e i = e' i"
    "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
    using e' d
    by (auto simp: Xs_def)
  then show ?thesis ..
qed

text \<open>Different reduction strategies:\<close>

definition "collect_threshold p ta t (X::real aform list) =
  (let
    Xs = map snd X;
    as = map (\<lambda>X. max ta (t * tdev' p X)) Xs
  in (\<lambda>(i::nat) xs. list_ex2 (\<le>) as (map abs xs)))"

definition "collect_girard p m (X::real aform list) =
  (let
    Xs = map snd X;
    M = pdevs_mapping Xs;
    D = domain_pdevs Xs;
    N = length X
  in if card D \<le> m then (\<lambda>_ _. True) else
    let
      Ds = sorted_list_of_set D;
      ortho_indices = map fst (take (2 * N) (sort_key (\<lambda>(i, r). r) (map (\<lambda>i. let xs = M i in (i, sum_list' p xs - fold max xs 0)) Ds)));
      _ = ()
    in (\<lambda>i (xs::real list). i \<in> set ortho_indices))"



subsection \<open>Splitting with heuristics\<close>

definition "abs_pdevs = unop_pdevs abs"

definition "abssum_of_pdevs_list X = fold (\<lambda>a b. (add_pdevs (abs_pdevs a) b)) X zero_pdevs"

definition "split_aforms xs i = (let splits = map (\<lambda>x. split_aform x i) xs in (map fst splits, map snd splits))"

definition "split_aforms_largest_uncond X =
  (let (i, x) = max_pdev (abssum_of_pdevs_list (map snd X)) in split_aforms X i)"

definition "Inf_aform_err p Rd = (float_of (truncate_down p (Inf_aform' p (fst Rd) - abs(snd Rd))))"
definition "Sup_aform_err p Rd = (float_of (truncate_up p (Sup_aform' p (fst Rd) + abs(snd Rd))))"

context includes interval.lifting begin
lift_definition ivl_of_aform_err::"nat \<Rightarrow> aform_err \<Rightarrow> float interval"
  is "\<lambda>p Rd. (Inf_aform_err p Rd, Sup_aform_err p Rd)"
  by (auto simp: aform_err_def  Inf_aform_err_def Sup_aform_err_def
      intro!: truncate_down_le truncate_up_le add_increasing[OF _ Inf_aform'_le_Sup_aform'])
lemma lower_ivl_of_aform_err: "lower (ivl_of_aform_err p Rd) = Inf_aform_err p Rd"
  and upper_ivl_of_aform_err: "upper (ivl_of_aform_err p Rd) = Sup_aform_err p Rd"
  by (transfer, simp)+
end

definition approx_un::"nat
     \<Rightarrow> (float interval \<Rightarrow> float interval option)
        \<Rightarrow> ((real \<times> real pdevs) \<times> real) option
           \<Rightarrow> ((real \<times> real pdevs) \<times> real) option"
  where "approx_un p f a = do {
  rd \<leftarrow> a;
  ivl \<leftarrow> f (ivl_of_aform_err p rd);
  Some (ivl_err (real_interval ivl))
}"

definition interval_extension1::"(float interval \<Rightarrow> (float interval) option) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
  where "interval_extension1 F f \<longleftrightarrow> (\<forall>ivl ivl'. F ivl = Some ivl' \<longrightarrow> (\<forall>x. x \<in>\<^sub>r ivl \<longrightarrow> f x \<in>\<^sub>r ivl'))"

lemma interval_extension1D:
  assumes "interval_extension1 F f"
  assumes "F ivl = Some ivl'"
  assumes "x \<in>\<^sub>r ivl"
  shows "f x \<in>\<^sub>r ivl'"
  using assms by (auto simp: interval_extension1_def)

lemma approx_un_argE:
  assumes au: "approx_un p F X = Some Y"
  obtains X' where "X = Some X'"
  using assms
  by (auto simp: approx_un_def bind_eq_Some_conv)

lemma degree_aform_independent_from:
  "degree_aform (independent_from d1 X) \<le> d1 + degree_aform X"
  by (auto simp: independent_from_def degree_msum_pdevs_le)

lemma degree_aform_of_ivl:
  fixes a b::"'a::executable_euclidean_space"
  shows "degree_aform (aform_of_ivl a b) \<le> length (Basis_list::'a list)"
  by (auto simp: aform_of_ivl_def degree_pdevs_of_ivl_le)

lemma aform_err_ivl_err[simp]: "aform_err e (ivl_err ivl') = set_of ivl'"
  by (auto simp: aform_err_def ivl_err_def aform_val_def divide_simps set_of_eq)

lemma Inf_Sup_aform_err:
  fixes X
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  defines "X' \<equiv> fst X"
  shows "aform_err e X \<subseteq> {Inf_aform_err p X .. Sup_aform_err p X}"
  using Inf_aform[OF e, of X'] Sup_aform[OF e, of X'] Inf_aform'[of p X'] Sup_aform'[of X' p]
  by (auto simp: aform_err_def X'_def Inf_aform_err_def Sup_aform_err_def
      intro!: truncate_down_le truncate_up_le)

lemma ivl_of_aform_err:
  fixes X
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "x \<in> aform_err e X \<Longrightarrow> x \<in>\<^sub>r ivl_of_aform_err p X"
  using Inf_Sup_aform_err[OF e, of X p]
  by (auto simp: set_of_eq lower_ivl_of_aform_err upper_ivl_of_aform_err)

lemma approx_unE:
  assumes ie: "interval_extension1 F f"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes au: "approx_un p F X'err = Some Ye"
  assumes x: "case X'err of None \<Rightarrow> True | Some X'err \<Rightarrow> x \<in> aform_err e X'err"
  shows "f x \<in> aform_err e Ye"
proof -
  from au obtain ivl' X' err
    where F: "F (ivl_of_aform_err p (X', err)) = Some (ivl')"
      and Y: "Ye = ivl_err (real_interval ivl')"
     and X'err: "X'err = Some (X', err)"
    by (auto simp: approx_un_def bind_eq_Some_conv)

  from x
  have "x \<in> aform_err e (X', err)" by (auto simp: X'err)
  from ivl_of_aform_err[OF e this]
  have "x \<in>\<^sub>r ivl_of_aform_err p (X', err)" .
  from interval_extension1D[OF ie F this]
  have "f x \<in>\<^sub>r ivl'" .
  also have "\<dots> = aform_err e Ye"
    unfolding Y aform_err_ivl_err ..
  finally show ?thesis .
qed

definition "approx_bin p f rd sd = do {
  ivl \<leftarrow> f (ivl_of_aform_err p rd)
             (ivl_of_aform_err p sd);
  Some (ivl_err (real_interval ivl))
}"

definition interval_extension2::"(float interval \<Rightarrow> float interval \<Rightarrow> float interval option) \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> bool"
  where "interval_extension2 F f \<longleftrightarrow> (\<forall>ivl1 ivl2 ivl. F ivl1 ivl2 = Some ivl \<longrightarrow>
    (\<forall>x y. x \<in>\<^sub>r ivl1 \<longrightarrow> y \<in>\<^sub>r ivl2 \<longrightarrow> f x y \<in>\<^sub>r ivl))"

lemma interval_extension2D:
  assumes "interval_extension2 F f"
  assumes "F ivl1 ivl2 = Some ivl"
  shows "x \<in>\<^sub>r ivl1 \<Longrightarrow> y \<in>\<^sub>r ivl2 \<Longrightarrow> f x y \<in>\<^sub>r ivl"
  using assms by (auto simp: interval_extension2_def)

lemma approx_binE:
  assumes ie: "interval_extension2 F f"
  assumes w: "w \<in> aform_err e (W', errw)"
  assumes x: "x \<in> aform_err e (X', errx)"
  assumes ab: "approx_bin p F ((W', errw)) ((X', errx)) = Some Ye"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "f w x \<in> aform_err e Ye"
proof -
  from ab obtain ivl'
    where F: "F (ivl_of_aform_err p (W', errw)) (ivl_of_aform_err p (X', errx)) = Some ivl'"
      and Y: "Ye = ivl_err (real_interval ivl')"
    by (auto simp: approx_bin_def bind_eq_Some_conv max_def)
  from interval_extension2D[OF ie F
        ivl_of_aform_err[OF e, where p=p, OF w]
        ivl_of_aform_err[OF e, where p=p, OF x]]
  have "f w x \<in>\<^sub>r ivl'" .
  also have "\<dots> = aform_err e Ye" unfolding Y aform_err_ivl_err ..
  finally show ?thesis .
qed

definition "min_aform_err p a1 (a2::aform_err) =
  (let
    ivl1 = ivl_of_aform_err p a1;
    ivl2 = ivl_of_aform_err p a2
  in if upper ivl1 < lower ivl2 then a1
      else if upper ivl2 < lower ivl1 then a2
      else ivl_err (real_interval (min_interval ivl1 ivl2)))"

definition "max_aform_err p a1 (a2::aform_err) =
  (let
    ivl1 = ivl_of_aform_err p a1;
    ivl2 = ivl_of_aform_err p a2
  in if upper ivl1 < lower ivl2 then a2
      else if upper ivl2 < lower ivl1 then a1
      else ivl_err (real_interval (max_interval ivl1 ivl2)))"


subsection \<open>Approximate Min Range - Kind Of Trigonometric Functions\<close>

definition affine_unop :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> aform_err \<Rightarrow> aform_err" where
"affine_unop p a b d X = (let
    ((x, xs), xe) = X;
    (ax, axe) = trunc_bound_eucl p (a * x);
    (y, ye) = trunc_bound_eucl p (ax + b);
    (ys, yse) = trunc_bound_pdevs p (scaleR_pdevs a xs)
    in ((y, ys), sum_list' p [truncate_up p (\<bar>a\<bar> * xe), axe, ye, yse, d]))"
  \<comment> \<open>TODO: also do binop\<close>

lemma aform_err_leI:
  "y \<in> aform_err e (c, d)"
  if "y \<in> aform_err e (c, d')" "d' \<le> d"
  using that by (auto simp: aform_err_def)

lemma aform_err_eqI:
  "y \<in> aform_err e (c, d)"
  if "y \<in> aform_err e (c, d')" "d' = d"
  using that by (auto simp: aform_err_def)

lemma sum_list'_append[simp]: "sum_list' p (ds@[d]) = truncate_up p (d + sum_list' p ds)"
  unfolding sum_list'_def
  by (simp add: eucl_truncate_up_real_def)

lemma aform_err_sum_list':
  "y \<in> aform_err e (c, sum_list' p ds)"
  if "y \<in> aform_err e (c, sum_list ds)"
  using that(1)
  apply (rule aform_err_leI)
  by (rule sum_list_le_sum_list')

lemma aform_err_trunc_bound_eucl:
  "y \<in> aform_err e ((fst (trunc_bound_eucl p X), xs), snd (trunc_bound_eucl p X) + d)"
  if y: "y \<in> aform_err e ((X, xs), d)"
  using that
proof -
  from aform_errE[OF y]
  have "\<bar>y - aform_val e (X, xs)\<bar> \<le> d" by auto
  then show ?thesis
    apply (intro aform_errI)
    apply (rule trunc_bound_euclE[of p X])
    by (auto simp: aform_val_def)
qed

lemma trunc_err_pdevsE:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  obtains err where
  "\<bar>err\<bar> \<le> tdev' p (trunc_err_pdevs p xs)"
  "pdevs_val e (trunc_pdevs p xs) = pdevs_val e xs + err"
  using trunc_bound_pdevsE[of e p xs]
  by (auto simp: trunc_bound_pdevs_def assms)

lemma aform_err_trunc_bound_pdevsI:
  "y \<in> aform_err e ((c, fst (trunc_bound_pdevs p xs)), snd (trunc_bound_pdevs p xs) + d)"
  if y: "y \<in> aform_err e ((c, xs), d)"
  and e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  using that
proof -
  define exs where "exs = trunc_err_pdevs p xs"
  from aform_errE[OF y]
  have "\<bar>y - aform_val e (c, xs)\<bar> \<le> d" by auto
  then show ?thesis
    apply (intro aform_errI)
    apply (rule trunc_err_pdevsE[OF e, of p xs])
    by (auto simp: aform_val_def trunc_bound_pdevs_def)
qed

lemma aform_err_addI:
  "y \<in> aform_err e ((a + b, xs), d)"
  if "y - b \<in> aform_err e ((a, xs), d)"
  using that
  by (auto simp: aform_err_def aform_val_def)

theorem affine_unop:
  assumes x: "x \<in> aform_err e X"
  assumes f: "\<bar>f x - (a * x + b)\<bar> \<le> d"
    and e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "f x \<in> aform_err e (affine_unop p a b d X)"
proof -
  show ?thesis
    unfolding affine_unop_def Let_def
    apply (auto simp: split_beta')
    apply (rule aform_err_sum_list')
    apply simp
    apply (rule aform_err_eqI)
     apply (rule aform_err_trunc_bound_eucl)
     apply (rule aform_err_addI)
     apply (rule aform_err_trunc_bound_eucl)
     apply (rule aform_err_trunc_bound_pdevsI)
    using e
      apply auto
    apply (rule aform_errI)
    apply (auto simp: aform_val_def)
  proof -
    define x' where "x' = (fst (fst X) + pdevs_val e (snd (fst X)))"
    have x_x': "\<bar>x - x'\<bar> \<le> snd X"
      using aform_errE[OF x]
      by (auto simp: x'_def aform_val_def)
    have "\<bar>f x - b - (a * fst (fst X) + a * pdevs_val e (snd (fst X)))\<bar> =
      \<bar>f x - (a * x + b) + a * (x - x')\<bar>"
      by (simp add: algebra_simps x'_def)
    also have "\<dots> \<le> \<bar>f x - (a * x + b)\<bar> + \<bar>a * (x - x')\<bar>"
      by (rule abs_triangle_ineq)
    also note f
    also have "\<bar>a * (x - x')\<bar> \<le> truncate_up p (\<bar>a\<bar> * snd X)"
      by (rule truncate_up_le)
        (auto simp: abs_mult intro!: mult_left_mono x_x')
    finally show "\<bar>f x - b - (a * fst (fst X) + a * pdevs_val e (snd (fst X)))\<bar> \<le>
        truncate_up p (\<bar>a\<bar> * snd X) + d"
      by auto
  qed
qed

lemma min_range_coeffs_ge:
  "\<bar>f x - (a * x + b)\<bar> \<le> d"
  if l: "l \<le> x" and u: "x \<le> u"
    and f': "\<And>y. y \<in> {l .. u} \<Longrightarrow> (f has_real_derivative f' y) (at y)"
    and a: "\<And>y. y \<in> {l..u} \<Longrightarrow> a \<le> f' y"
    and d: "d \<ge> (f u - f l - a * (u - l)) / 2 + \<bar>(f l + f u - a * (l + u)) / 2 - b\<bar>"
  for a b d::real
proof (rule order_trans[OF _ d])
  note f'_at = has_field_derivative_at_within[OF f']
  from l u have lu: "x \<in> {l .. u}" and llu: "l \<in> {l .. u}" by simp_all

  define m where "m = (f l + f u - a * (l + u)) / 2"
  have "\<bar>f x - (a * x + b)\<bar> = \<bar>f x - (a * x + m) + (m - b)\<bar>" by (simp add: algebra_simps)
  also have "\<dots> \<le> \<bar>f x - (a * x + m)\<bar> + \<bar>m - b\<bar>" by (rule abs_triangle_ineq)
  also have "\<bar>f x - (a * x + m)\<bar> \<le> (f u - f l - a * (u - l)) / 2"
  proof (rule abs_leI)
    have "f x \<ge> f l + a * (x - l)" (is "?l \<ge> ?r")
      apply (rule order_trans) prefer 2
       apply (rule linear_lower2[OF f'_at, of l u a])
      subgoal by assumption
      subgoal by (rule a)
      subgoal
        using lu
        by (auto intro!: mult_right_mono)
      subgoal using lu by auto
      done
    also have "a * x + m - (f u - f l - a * (u - l)) / 2 \<le> ?r"
      by (simp add: algebra_simps m_def field_simps)
    finally (xtrans) show "- (f x - (a * x + m)) \<le> (f u - f l - a * (u - l)) / 2"
      by (simp add: algebra_simps m_def divide_simps)
  next
    have "f x \<le> f u + a * (x - u)"
      apply (rule order_trans)
       apply (rule linear_upper2[OF f'_at, of l u a])
      subgoal by assumption
      subgoal by (rule a)
      subgoal
        using lu
        by (auto intro!: mult_right_mono)
      subgoal using lu by auto
      done
    also have "\<dots> \<le> a * x + m + (f u - f l - a * (u - l)) / 2"
      by (simp add: m_def divide_simps algebra_simps)
    finally show "f x - (a * x + m) \<le> (f u - f l - a * (u - l)) / 2"
      by (simp add: algebra_simps m_def divide_simps)
  qed
  also have "\<bar>m - b\<bar> = abs ((f l + f u - a * (l + u)) / 2 - b)"
    unfolding m_def ..
  finally show "\<bar>f x - (a * x + b)\<bar> \<le> (f u - f l - a * (u - l)) / 2 + \<bar>(f l + f u - a * (l + u)) / 2 - b\<bar>"
    by (simp)
qed

lemma min_range_coeffs_le:
  "\<bar>f x - (a * x + b)\<bar> \<le> d"
  if l: "l \<le> x" and u: "x \<le> u"
    and f': "\<And>y. y \<in> {l .. u} \<Longrightarrow> (f has_real_derivative f' y) (at y)"
    and a: "\<And>y. y \<in> {l .. u} \<Longrightarrow> f' y \<le> a"
    and d: "d \<ge> (f l - f u + a * (u - l)) / 2 + \<bar>(f l + f u - a * (l + u)) / 2 - b\<bar>"
  for a b d::real
proof (rule order_trans[OF _ d])
  note f'_at = has_field_derivative_at_within[OF f']
  from l u have lu: "x \<in> {l .. u}" and llu: "l \<in> {l .. u}" by simp_all

  define m where "m = (f l + f u - a * (l + u)) / 2"
  have "\<bar>f x - (a * x + b)\<bar> = \<bar>f x - (a * x + m) + (m - b)\<bar>" by (simp add: algebra_simps)
  also have "\<dots> \<le> \<bar>f x - (a * x + m)\<bar> + \<bar>m - b\<bar>" by (rule abs_triangle_ineq)
  also have "\<bar>f x - (a * x + m)\<bar> \<le> (f l - f u + a * (u - l)) / 2"
  proof (rule abs_leI)
    have "f x \<ge> f u + a * (x - u)" (is "?l \<ge> ?r")
      apply (rule order_trans) prefer 2
       apply (rule linear_lower[OF f'_at, of l u a])
      subgoal by assumption
      subgoal by (rule a)
      subgoal
        using lu
        by (auto intro!: mult_right_mono)
      subgoal using lu by auto
      done
    also have "a * x + m - (f l - f u + a * (u - l)) / 2 \<le> ?r"
      using lu
      by (auto simp add: algebra_simps m_def field_simps intro!: mult_left_mono_neg)
    finally (xtrans) show "- (f x - (a * x + m)) \<le> (f l - f u + a * (u - l)) / 2"
      by (simp add: algebra_simps m_def divide_simps)
  next
    have "f x \<le> f l + a * (x - l)"
      apply (rule order_trans)
       apply (rule linear_upper[OF f'_at, of l u a])
      subgoal by assumption
      subgoal by (rule a)
      subgoal
        using lu
        by (auto intro!: mult_right_mono)
      subgoal using lu by auto
      done
    also have "\<dots> \<le> a * x + m + (f l - f u + a * (u - l)) / 2"
      using lu
      by (auto simp add: algebra_simps m_def field_simps intro!: mult_left_mono_neg)
    finally show "f x - (a * x + m) \<le> (f l - f u + a * (u - l)) / 2"
      by (simp add: algebra_simps m_def divide_simps)
  qed
  also have "\<bar>m - b\<bar> = abs ((f l + f u - a * (l + u)) / 2 - b)"
    unfolding m_def ..
  finally show "\<bar>f x - (a * x + b)\<bar> \<le> (f l - f u + a * (u - l)) / 2 + \<bar>(f l + f u - a * (l + u)) / 2 - b\<bar>"
    by (simp)
qed

context includes floatarith_notation begin

definition "range_reducer p l =
  (if l < 0 \<or> l > 2 * lb_pi p
  then approx p (Pi * (Num (-2)) * (Floor (Num (l * Float 1 (-1)) / Pi))) []
  else Some 0)"

lemmas approx_emptyD = approx[OF bounded_by_None[of Nil], simplified]

lemma range_reducerE:
  assumes "range_reducer p l = Some ivl"
  obtains n::int where "n * (2 * pi) \<in>\<^sub>r ivl"
proof (cases "l \<ge> 0 \<and> l \<le> 2 * lb_pi p")
  case False
  with assms have "- \<lfloor>l / (2 * pi)\<rfloor> * (2 * pi) \<in>\<^sub>r ivl"
    by (auto simp: range_reducer_def bind_eq_Some_conv inverse_eq_divide
        algebra_simps dest!: approx_emptyD)
  then show ?thesis ..
next
  case True then have "real_of_int 0 * (2 * pi) \<in>\<^sub>r ivl" using assms
    by (auto simp: range_reducer_def zero_in_float_intervalI)
  then show ?thesis ..
qed

definition "range_reduce_aform_err p X = do {
  r \<leftarrow> range_reducer p (lower (ivl_of_aform_err p X));
  Some (add_aform' p X (ivl_err (real_interval r)))
}"

lemma range_reduce_aform_errE:
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes x: "x \<in> aform_err e X"
  assumes "range_reduce_aform_err p X = Some Y"
  obtains n::int where "x + n * (2 * pi) \<in> aform_err e Y"
proof -
  from assms obtain r
    where x: "x \<in> aform_err e X"
     and r: "range_reducer p (lower (ivl_of_aform_err p X)) = Some r"
     and Y:  "Y = add_aform' p X (ivl_err (real_interval r))"
    by (auto simp: range_reduce_aform_err_def bind_eq_Some_conv mid_err_def split: prod.splits)
  from range_reducerE[OF r]
  obtain n::int where "n * (2 * pi) \<in>\<^sub>r r"
    by auto
  then have "n * (2 * pi) \<in> aform_err e (ivl_err (real_interval r))"
    by (auto simp: aform_val_def ac_simps divide_simps abs_real_def set_of_eq intro!: aform_errI)
  from add_aform'[OF e x this, of p]
  have "x + n * (2 * pi) \<in> aform_err e Y"
    by (auto simp: Y)
  then show ?thesis ..
qed

definition "min_range_mono p F DF l u X = do {
  let L = Num l;
  let U = Num u;
  aivl \<leftarrow> approx p (Min (DF L) (DF U)) [];
  let a = lower aivl;
  let A = Num a;
  bivl \<leftarrow> approx p (Half (F L + F U - A * (L + U))) [];
  let (b, be) = mid_err bivl;
  let (B, Be) = (Num (float_of b), Num (float_of be));
  divl \<leftarrow> approx p ((Half (F U - F L - A * (U - L))) + Be) [];
  Some (affine_unop p a b (real_of_float (upper divl)) X)
}"

lemma min_range_mono:
  assumes x: "x \<in> aform_err e X"
  assumes "l \<le> x" "x \<le> u"
  assumes "min_range_mono p F DF l u X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes F: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> interpret_floatarith (F (Num x)) [] = f x"
  assumes DF: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> interpret_floatarith (DF (Num x)) [] = f' x"
  assumes f': "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  assumes f'_le: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> min (f' l) (f' u) \<le> f' x"
  shows "f x \<in> aform_err e Y"
proof -
  from assms obtain a b be bivl divl
    where bivl: "(f l + f u - a * (l + u))/2 \<in>\<^sub>r bivl"
      and Y: "Y = affine_unop p a b (upper divl) X"
      and du: "(f u - f l - a * (u - l)) / 2 + be \<in>\<^sub>r divl"
      and a: "a \<le> f' l" "a \<le> f' u"
      and b_def: "b = (lower bivl + upper bivl) / 2"
      and be_def: "be = (upper bivl - lower bivl) / 2"
    by (auto simp: min_range_mono_def Let_def bind_eq_Some_conv mid_err_def set_of_eq
        simp del: eq_divide_eq_numeral1
        split: prod.splits if_splits dest!: approx_emptyD)
  have diff_le: "real_of_float a \<le> f' y" if "real_of_float l \<le> y" "y \<le> u" for y
    using f'_le[of y] that a
    by auto
  have le_be: "\<bar>(f (l) + f (u) - a * (real_of_float l + u)) / 2 - b\<bar> \<le> be"
    using bivl
    unfolding b_def be_def
    by (auto simp: abs_real_def divide_simps set_of_eq)
  have "\<bar>f x - (a * x + b)\<bar> \<le> upper divl"
    apply (rule min_range_coeffs_ge)
        apply (rule \<open>l \<le> x\<close>)
       apply (rule \<open>x \<le> u\<close>)
      apply (rule f') apply assumption
    using diff_le apply force
    apply (rule order_trans[OF add_mono[OF order_refl]])
     apply (rule le_be)
    using bivl du
    unfolding b_def[symmetric] be_def[symmetric]
    by (auto simp: set_of_eq)
  from affine_unop[where f=f and p = p, OF \<open>x \<in> _\<close> this e]
  have "f x \<in> aform_err e (affine_unop p (real_of_float a) b (upper divl) X)"
    by (auto simp: Y)
  then show ?thesis
    by (simp add: Y b_def)
qed

definition "min_range_antimono p F DF l u X = do {
  let L = Num l;
  let U = Num u;
  aivl \<leftarrow> approx p (Max (DF L) (DF U)) [];
  let a = upper aivl;
  let A = Num a;
  bivl \<leftarrow> approx p (Half (F L + F U - A * (L + U))) [];
  let (b, be) = mid_err bivl;
  let (B, Be) = (Num (float_of b), Num (float_of be));
  divl \<leftarrow> approx p (Add (Half (F L - F U + A * (U - L))) Be) [];
  Some (affine_unop p a b (real_of_float (upper divl)) X)
}"

lemma min_range_antimono:
  assumes x: "x \<in> aform_err e X"
  assumes "l \<le> x" "x \<le> u"
  assumes "min_range_antimono p F DF l u X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes F: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> interpret_floatarith (F (Num x)) [] = f x"
  assumes DF: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> interpret_floatarith (DF (Num x)) [] = f' x"
  assumes f': "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  assumes f'_le: "\<And>x. x \<in> {real_of_float l .. u} \<Longrightarrow> f' x \<le> max (f' l) (f' u)"
  shows "f x \<in> aform_err e Y"
proof -
  from assms obtain a b be aivl bivl divl
    where bivl: "(f l + f u - real_of_float a * (l + u)) / 2 \<in>\<^sub>r bivl"
    and Y: "Y = affine_unop p a b (real_of_float (upper divl)) X"
    and du: "(f l - f u + a * (u - l)) / 2 + be \<in>\<^sub>r divl"
    and a: "f' l \<le> a" "f' u \<le> a"
    and a_def: "a = upper aivl"
    and b_def: "b = (lower bivl + upper bivl) / 2"
    and be_def: "be = (upper bivl - lower bivl) / 2"
    by (auto simp: min_range_antimono_def Let_def bind_eq_Some_conv mid_err_def set_of_eq
        simp del: eq_divide_eq_numeral1
        split: prod.splits if_splits dest!: approx_emptyD)
  have diff_le: "f' y \<le> real_of_float a" if "real_of_float l \<le> y" "y \<le> u" for y
    using f'_le[of y] that a
    by auto
  have le_be: "\<bar>(f (l) + f (u) - a * (real_of_float l + u)) / 2 - b\<bar> \<le> be"
    using bivl
    unfolding b_def be_def
    by (auto simp: abs_real_def divide_simps set_of_eq)
  have "\<bar>f x - (a * x + b)\<bar> \<le> upper divl"
    apply (rule min_range_coeffs_le)
        apply (rule \<open>l \<le> x\<close>)
       apply (rule \<open>x \<le> u\<close>)
      apply (rule f') apply assumption
    using diff_le apply force
    apply (rule order_trans[OF add_mono[OF order_refl]])
     apply (rule le_be)
    using du bivl
    unfolding b_def[symmetric] be_def[symmetric]
    by (auto simp: set_of_eq)
  from affine_unop[where f=f and p = p, OF \<open>x \<in> _\<close> this e]
  have "f x \<in> aform_err e (affine_unop p (real_of_float a) b (upper divl) X)"
    by (auto simp: Y)
  then show ?thesis
    by (simp add: Y b_def)
qed

definition "cos_aform_err p X = do {
  X \<leftarrow> range_reduce_aform_err p X;
  let ivl = ivl_of_aform_err p X;
  let l = lower ivl;
  let u = upper ivl;
  let L = Num l;
  let U = Num u;
  if l \<ge> 0 \<and> u \<le> lb_pi p then
   min_range_antimono p Cos (\<lambda>x. (Minus (Sin x))) l u X
  else if l \<ge> ub_pi p \<and> u \<le> 2 * lb_pi p then
   min_range_mono p Cos (\<lambda>x. (Minus (Sin x))) l u X
  else do {
    Some (ivl_err (real_interval (cos_float_interval p ivl)))
  }
}"

lemma abs_half_enclosure:
  fixes r::real
  assumes "bl \<le> r" "r \<le> bu"
  shows "\<bar>r - (bl + bu) / 2\<bar> \<le> (bu - bl) / 2"
  using assms
  by (auto simp: abs_real_def divide_simps)

lemma cos_aform_err:
  assumes x: "x \<in> aform_err e X0"
  assumes "cos_aform_err p X0 = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "cos x \<in> aform_err e Y"
proof -
  from assms obtain X ivl l u where
    X: "range_reduce_aform_err p X0 = Some X"
    and ivl_def: "ivl = ivl_of_aform_err p X"
    and l_def: "l = lower ivl"
    and u_def: "u = upper ivl"
    by (auto simp: cos_aform_err_def bind_eq_Some_conv)
  from range_reduce_aform_errE[OF e x X]
  obtain n where xn: "x + real_of_int n * (2 * pi) \<in> aform_err e X"
    by auto
  define xn where "xn = x + n * (2 * pi)"
  with xn have xn: "xn \<in> aform_err e X" by auto
  from ivl_of_aform_err[OF e xn, of p, folded ivl_def]
  have "xn \<in>\<^sub>r ivl" .
  then have lxn: "l \<le> xn" and uxn: "xn \<le> u"
    by (auto simp: l_def u_def set_of_eq)
  consider "l \<ge> 0" "u \<le> lb_pi p"
    | "l < 0 \<or> u > lb_pi p" "l \<ge> ub_pi p" "u \<le> 2 * lb_pi p"
    | "l < 0 \<or> u > lb_pi p" "l < ub_pi p \<or> u > 2 * lb_pi p"
    by arith
  then show ?thesis
  proof cases
    case 1
    then have min_eq_Some: "min_range_antimono p Cos (\<lambda>x. Minus (Sin x)) l u X = Some Y"
      and bounds: "0 \<le> l" "u \<le> (lb_pi p)"
      using assms(2)
      unfolding cos_aform_err_def X l_def u_def
      by (auto simp: X Let_def simp flip: l_def u_def ivl_def  split: prod.splits)
    have bounds: "0 \<le> l" "u \<le> pi" using bounds pi_boundaries[of p] by auto
    have diff_le: "- sin y \<le> max (- sin (real_of_float l)) (- sin (real_of_float u))"
      if "real_of_float l \<le> y" "y \<le> real_of_float u" for y
    proof -
      consider "y \<le> pi / 2" | "y \<ge> pi / 2" by arith
      then show ?thesis
      proof cases
        case 1
        then have "- sin y \<le> - sin l"
          using that bounds
          by (auto intro!: sin_monotone_2pi_le)
        then show ?thesis by auto
      next
        case 2
        then have "- sin y \<le> - sin u"
          using that bounds
          unfolding sin_minus_pi[symmetric]
          apply (intro sin_monotone_2pi_le)
          by (auto intro!: )
        then show ?thesis by auto
      qed
    qed
    have "cos xn \<in> aform_err e Y"
      apply (rule min_range_antimono[OF xn lxn uxn min_eq_Some e, where f'="\<lambda>x. - sin x"])
      subgoal by simp
      subgoal by simp
      subgoal by (auto intro!: derivative_eq_intros)
      subgoal by (rule diff_le) auto
      done
    then show ?thesis
      unfolding xn_def
      by (simp add: )
  next
    case 2
    then have min_eq_Some: "min_range_mono p Cos (\<lambda>x. Minus (Sin x)) l u X = Some Y"
      and bounds: "ub_pi p \<le> l" "u \<le> 2 * lb_pi p"
      using assms(2)
      unfolding cos_aform_err_def X
      by (auto simp: X Let_def simp flip: l_def u_def ivl_def split: prod.splits)
    have bounds: "pi \<le> l" "u \<le> 2 * pi" using bounds pi_boundaries[of p] by auto
    have diff_le: "min (- sin (real_of_float l)) (- sin (real_of_float u)) \<le> - sin y"
      if "real_of_float l \<le> y" "y \<le> real_of_float u" for y
    proof -
      consider "y \<le> 3 * pi / 2" | "y \<ge> 3 * pi / 2" by arith
      then show ?thesis
      proof cases
        case 1
        then have "- sin l \<le> - sin y"
          unfolding sin_minus_pi[symmetric]
          apply (intro sin_monotone_2pi_le)
          using that bounds
          by (auto)
        then show ?thesis by auto
      next
        case 2
        then have "- sin u \<le> - sin y"
          unfolding sin_2pi_minus[symmetric]
          using that bounds
          apply (intro sin_monotone_2pi_le)
          by (auto intro!: )
        then show ?thesis by auto
      qed
    qed
    have "cos xn \<in> aform_err e Y"
      apply (rule min_range_mono[OF xn lxn uxn min_eq_Some e, where f'="\<lambda>x. - sin x"])
      subgoal by simp
      subgoal by simp
      subgoal by (auto intro!: derivative_eq_intros)
      subgoal by (rule diff_le) auto
      done
    then show ?thesis
      unfolding xn_def
      by (simp add: )
  next
    case 3
    then obtain ivl' where
      "cos_float_interval p ivl = ivl'"
      "Y = ivl_err (real_interval ivl')"
      using assms(2)
      unfolding cos_aform_err_def X l_def u_def
      by (auto simp: X simp flip: l_def u_def ivl_def split: prod.splits)
    with cos_float_intervalI[OF \<open>xn \<in>\<^sub>r ivl\<close>, of p]
    show ?thesis
      by (auto simp: xn_def)
  qed
qed

definition "sqrt_aform_err p X = do {
  let ivl = ivl_of_aform_err p X;
  let l = lower ivl;
  let u = upper ivl;
  if 0 < l then min_range_mono p Sqrt (\<lambda>x. Half (Inverse (Sqrt x))) l u X
  else Some (ivl_err (real_interval (sqrt_float_interval p ivl)))
}"

lemma sqrt_aform_err:
  assumes x: "x \<in> aform_err e X"
  assumes "sqrt_aform_err p X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "sqrt x \<in> aform_err e Y"
proof -
  obtain l u ivl
    where ivl_def: "ivl = ivl_of_aform_err p X"
    and l_def: "l = lower ivl"
    and u_def: "u = upper ivl"
    by auto
  from ivl_of_aform_err[OF e x, of p, folded ivl_def]
  have ivl: "x \<in>\<^sub>r ivl" .
  then have lx: "l \<le> x" and ux: "x \<le> u"
    by (auto simp flip: ivl_def simp: l_def u_def set_of_eq)
  consider "l > 0" | "l \<le> 0"
    by arith
  then show ?thesis
  proof cases
    case 1
    then have min_eq_Some: "min_range_mono p Sqrt (\<lambda>x. Half (Inverse (Sqrt x))) l u X = Some Y"
      and bounds: "0 < l"
      using assms(2)
      unfolding sqrt_aform_err_def
      by (auto simp: Let_def simp flip: l_def u_def ivl_def split: prod.splits)
    have "sqrt x \<in> aform_err e Y"
      apply (rule min_range_mono[OF x lx ux min_eq_Some e, where f'="\<lambda>x. 1 / (2 * sqrt x)"])
      subgoal by simp
      subgoal by (simp add: divide_simps)
      subgoal using bounds by (auto intro!: derivative_eq_intros simp: inverse_eq_divide)
      subgoal using \<open>l > 0\<close> by (auto simp: inverse_eq_divide min_def divide_simps)
      done
    then show ?thesis
      by (simp add: )
  next
    case 2
    then have "Y = ivl_err (real_interval (sqrt_float_interval p ivl))"
      using assms(2)
      unfolding sqrt_aform_err_def
      by (auto simp: Let_def simp flip: ivl_def l_def u_def split: prod.splits)
    with sqrt_float_intervalI[OF ivl]
    show ?thesis
      by (auto simp: set_of_eq)
  qed
qed

definition "ln_aform_err p X = do {
  let ivl = ivl_of_aform_err p X;
  let l = lower ivl;
  if 0 < l then min_range_mono p Ln inverse l (upper ivl) X
  else None
}"

lemma ln_aform_err:
  assumes x: "x \<in> aform_err e X"
  assumes "ln_aform_err p X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "ln x \<in> aform_err e Y"
proof -
  obtain ivl l u
    where l_def: "l = lower ivl"
      and u_def: "u = upper ivl"
      and ivl_def: "ivl = ivl_of_aform_err p X"
    by auto
  from ivl_of_aform_err[OF e x, of p, folded ivl_def]
  have "x \<in>\<^sub>r ivl" .
  then have lx: "l \<le> x" and ux: "x \<le> u"
    by (auto simp: set_of_eq l_def u_def)
  consider "l > 0" | "l \<le> 0"
    by arith
  then show ?thesis
  proof cases
    case 1
    then have min_eq_Some: "min_range_mono p Ln inverse l u X = Some Y"
      and bounds: "0 < l"
      using assms(2)
      unfolding ln_aform_err_def
      by (auto simp: Let_def simp flip: ivl_def l_def u_def split: prod.splits if_splits)
    have "ln x \<in> aform_err e Y"
      apply (rule min_range_mono[OF x lx ux min_eq_Some e, where f'=inverse])
      subgoal by simp
      subgoal by (simp add: divide_simps)
      subgoal using bounds by (auto intro!: derivative_eq_intros simp: inverse_eq_divide)
      subgoal using \<open>l > 0\<close> by (auto simp: inverse_eq_divide min_def divide_simps)
      done
    then show ?thesis
      by (simp add: )
  next
    case 2
    then show ?thesis using assms
      by (auto simp: ln_aform_err_def Let_def l_def ivl_def)
  qed
qed

definition "exp_aform_err p X = do {
  let ivl = ivl_of_aform_err p X;
  min_range_mono p Exp Exp (lower ivl) (upper ivl) X
}"

lemma exp_aform_err:
  assumes x: "x \<in> aform_err e X"
  assumes "exp_aform_err p X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "exp x \<in> aform_err e Y"
proof -
  obtain l u ivl
    where l_def: "l = lower ivl"
      and u_def: "u = upper ivl"
      and ivl_def: "ivl = ivl_of_aform_err p X"
    by auto
  from ivl_of_aform_err[OF e x, of p, folded ivl_def]
  have "x \<in>\<^sub>r ivl" .
  then have lx: "l \<le> x" and ux: "x \<le> u"
    by (auto simp: ivl_def l_def u_def set_of_eq)
  have min_eq_Some: "min_range_mono p Exp Exp l u X = Some Y"
    using assms(2)
    unfolding exp_aform_err_def
    by (auto simp: Let_def simp flip: ivl_def u_def l_def split: prod.splits if_splits)
  have "exp x \<in> aform_err e Y"
    apply (rule min_range_mono[OF x lx ux min_eq_Some e, where f'=exp])
    subgoal by simp
    subgoal by (simp add: divide_simps)
    subgoal by (auto intro!: derivative_eq_intros simp: inverse_eq_divide)
    subgoal by (auto simp: inverse_eq_divide min_def divide_simps)
    done
  then show ?thesis
    by (simp add: )
qed

definition "arctan_aform_err p X = do {
  let l = Inf_aform_err p X;
  let u = Sup_aform_err p X;
  min_range_mono p Arctan (\<lambda>x. 1 / (Num 1 + x * x)) l u X
}"

lemma pos_add_nonneg_ne_zero: "a > 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a + b \<noteq> 0"
  for a b::real
  by arith

lemma arctan_aform_err:
  assumes x: "x \<in> aform_err e X"
  assumes "arctan_aform_err p X = Some Y"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "arctan x \<in> aform_err e Y"
proof -
  obtain l u where l: "l = Inf_aform_err p X"
    and u: "u = Sup_aform_err p X"
    by auto
  from x l u have lx: "l \<le> x" and ux: "x \<le> u"
    using Inf_Sup_aform_err[OF e, of X p]
    by auto
  have min_eq_Some: "min_range_mono p Arctan (\<lambda>x. 1 / (Num 1 + x * x))  l u X = Some Y"
    using assms(2)
    unfolding arctan_aform_err_def l u
    by (auto simp: l[symmetric] u[symmetric] split: prod.splits if_splits)
  have "arctan x \<in> aform_err e Y"
    apply (rule min_range_mono[OF x lx ux min_eq_Some e, where f'="\<lambda>x. inverse (1 + x\<^sup>2)"])
    subgoal by simp
    subgoal by (simp add: power2_eq_square inverse_eq_divide)
    subgoal by (auto intro!: derivative_eq_intros simp: inverse_eq_divide)
    subgoal for x
      apply (cases "x \<le> 0")
      subgoal
        apply (rule min.coboundedI1)
        apply (rule deriv_nonneg_imp_mono[of "real_of_float l" x])
        by (auto intro!: derivative_eq_intros simp: mult_le_0_iff pos_add_nonneg_ne_zero)
      subgoal
        apply (rule min.coboundedI2)
        apply (rule le_imp_inverse_le)
        by (auto intro!: power_mono add_pos_nonneg)
      done
    done
  then show ?thesis
    by (simp add: )
qed

subsection \<open>Power, TODO: compare with Min-range approximation?!\<close>

definition "power_aform_err p (X::aform_err) n =
  (if n = 0 then ((1, zero_pdevs), 0)
  else if n = 1 then X
  else
    let x0 = float_of (fst (fst X));
      xs = snd (fst X);
      xe = float_of (snd X);
      C = the (approx p (Num x0 ^\<^sub>e n) []);
      (c, ce) = mid_err C;
      NX = the (approx p (Num (of_nat n) * (Num x0 ^\<^sub>e (n - 1))) []);
      (nx, nxe) = mid_err NX;
      Y = scaleR_pdevs nx xs;
      (Y', Y_err) = trunc_bound_pdevs p Y;
      t = tdev' p xs;
      Ye = truncate_up p (nxe * t);
      err = the (approx p
        (Num (of_nat n) * Num xe * Abs (Num x0) ^\<^sub>e (n - 1) + 
        (Sum\<^sub>e (\<lambda>k. Num (of_nat (n choose k)) * Abs (Num x0) ^\<^sub>e (n - k) * (Num xe + Num (float_of t)) ^\<^sub>e k)
          [2..<Suc n])) []);
      ERR = upper err
    in ((c, Y'), sum_list' p [ce, Y_err, Ye, real_of_float ERR]))"

lemma bounded_by_Nil: "bounded_by [] []"
  by (auto simp: bounded_by_def)

lemma plain_floatarith_approx:
  assumes "plain_floatarith 0 f"
  shows "interpret_floatarith f [] \<in>\<^sub>r (the (approx p f []))"
proof -
  from plain_floatarith_approx_not_None[OF assms(1), of Nil p]
  obtain ivl where "approx p f [] = Some ivl"
    by auto
  from this approx[OF bounded_by_Nil this]
  show ?thesis
    by auto
qed

lemma plain_floatarith_Sum\<^sub>e:
  "plain_floatarith n (Sum\<^sub>e f xs) \<longleftrightarrow> list_all (\<lambda>i. plain_floatarith n (f i)) xs"
  by (induction xs) (auto simp: zero_floatarith_def plus_floatarith_def)

lemma sum_list'_float[simp]: "sum_list' p xs \<in> float"
  by (induction xs rule: rev_induct) (auto simp: sum_list'_def eucl_truncate_up_real_def)

lemma tdev'_float[simp]: "tdev' p xs \<in> float"
  by (auto simp: tdev'_def)

lemma
  fixes x y::real
  assumes "abs (x - y) \<le> e"
  obtains err where "x = y + err" "abs err \<le> e"
  using assms
  apply atomize_elim
  apply (rule exI[where x="x - y"])
  by (auto simp: abs_real_def)

theorem power_aform_err:
  assumes "x \<in> aform_err e X"
  assumes floats[simp]: "fst (fst X) \<in> float" "snd X \<in> float"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "x ^ n \<in> aform_err e (power_aform_err p X n)"
proof -
  consider "n = 0" | "n = 1" | "n \<ge> 2"
    by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (auto simp: aform_err_def power_aform_err_def aform_val_def)
  next
    case 2
    then show ?thesis
      using assms
      by (auto simp: aform_err_def power_aform_err_def aform_val_def)
  next
    case n: 3
    define x0 where "x0 = (fst (fst X))"
    define xs where "xs = snd (fst X)"
    define xe where "xe = (snd X)"
    have [simp]: "x0 \<in> float" "xe \<in> float" using assms by (auto simp: x0_def xe_def)
  
    define xe' where "xe' = x - aform_val e (x0, xs)"
    from aform_errE[OF assms(1)]
    have xe': "\<bar>xe'\<bar> \<le> xe"
      by (auto simp: x0_def xs_def xe_def xe'_def)
    then have xe_nonneg: "0 \<le> xe"
      by (auto simp: )

    define t where "t = tdev' p xs"
    have t: "tdev xs \<le> t" "t \<in> float" by (auto simp add: t_def tdev'_le)
    then have t_nonneg: "0 \<le> t" using tdev_nonneg[of xs] by arith
    note t_pdevs = abs_pdevs_val_le_tdev[OF e, THEN order_trans, OF t(1)]

    have rewr1: "{..n} = (insert 0 (insert 1 {2..n}))" using n by auto
    have "x = (pdevs_val e xs + xe') + x0"
      by (simp add: xe'_def aform_val_def)
    also have "\<dots> ^ n = x0 ^ n + n * x0 ^ (n - Suc 0) * pdevs_val e xs +
      (n * xe' * x0 ^ (n - Suc 0) +
        (\<Sum>k = 2..n. real (n choose k) * (pdevs_val e xs + xe') ^ k * x0 ^ (n - k)))"
      (is "_ = _ + ?err")
      apply (subst binomial_ring)
      unfolding rewr1
      using n
      apply (simp add: algebra_simps)
      done
    also

    let ?ERR = "(Num (of_nat n) * Num (float_of xe) * Abs (Num (float_of x0)) ^\<^sub>e (n - 1) +
          (Sum\<^sub>e (\<lambda>k. Num (of_nat (n choose k)) * Abs (Num (float_of x0)) ^\<^sub>e (n - k) *
            (Num (float_of xe) + Num (float_of t)) ^\<^sub>e k)
            [2..<Suc n]))"
    define err where "err = the (approx p ?ERR [])"
    define ERR where "ERR = upper err"
    have ERR: "abs ?err \<le> ERR"
    proof -
      have err_aerr: "abs (?err) \<le> n * xe * abs x0 ^ (n - Suc 0) +
          (\<Sum>k = 2..n. real (n choose k) * (t + xe) ^ k * abs x0 ^ (n - k))"
        (is "_ \<le> ?aerr")
        by (auto simp: abs_mult power_abs intro!: sum_mono mult_mono power_mono xe'
            mult_nonneg_nonneg zero_le_power t_nonneg xe_nonneg add_nonneg_nonneg
            sum_abs[THEN order_trans] abs_triangle_ineq[THEN order_trans] add_mono t_pdevs)
      also
      have rewr: "{2 .. n} = {2 ..<Suc n}"
        using n
        by (auto simp: )
      have "plain_floatarith 0 ?ERR"
        by (auto simp add: zero_floatarith_def plain_floatarith_Sum\<^sub>e times_floatarith_def
            plus_floatarith_def intro!: list_allI)
      from plain_floatarith_approx[OF this, of p]
      have "ERR \<ge> ?aerr"
        using n
        by (auto simp: set_of_eq err_def ERR_def sum_list_distinct_conv_sum_set rewr t x0_def
            algebra_simps)
      finally show ?thesis .
    qed

    let ?x0n = "Num (float_of x0) ^\<^sub>e n"
    define C where "C = the (approx p ?x0n [])"
    have "plain_floatarith 0 ?x0n" by simp
    from plain_floatarith_approx[OF this, of p]
    have C: "x0 ^ n \<in> {lower C .. upper C}"
      by (auto simp: C_def x0_def set_of_eq)

    define c where "c = fst (mid_err C)"
    define ce where "ce = snd (mid_err C)"
    define ce' where "ce' = x0 ^ n - c"
    have ce': "abs (ce') \<le> ce"
      using C
      by (auto simp: ce'_def c_def ce_def abs_diff_le_iff mid_err_def divide_simps)
    have "x0 ^ n = c + ce'" by (simp add: ce'_def)
    also

    let ?NX = "(Num (of_nat n) * (Num (float_of x0) ^\<^sub>e (n - 1)))"
    define NX where "NX = the (approx p ?NX [])"
    have "plain_floatarith 0 ?NX" by (simp add: times_floatarith_def)
    from plain_floatarith_approx[OF this, of p]
    have NX: "n * x0 ^ (n - 1) \<in> {lower NX .. upper NX}"
      by (auto simp: NX_def x0_def set_of_eq)

    define nx where "nx = fst (mid_err NX)"
    define nxe where "nxe = snd (mid_err NX)"
    define nx' where "nx' = n * x0 ^ (n - 1) - nx"
    define Ye where "Ye = truncate_up p (nxe * t)"
    have Ye: "Ye \<ge> nxe * t" by (auto simp: Ye_def truncate_up_le)
    have nx: "abs (nx') \<le> nxe" "0 \<le> nxe"
      using NX
      by (auto simp: nx_def nxe_def abs_diff_le_iff mid_err_def divide_simps nx'_def)
    have Ye: "abs (nx' * pdevs_val e xs) \<le> Ye"
      by (auto simp: Ye_def abs_mult intro!: truncate_up_le mult_mono nx t_pdevs)
    have "n * x0 ^ (n - Suc 0) = nx + nx'" by (simp add: nx'_def)
    also

    define Y where "Y = scaleR_pdevs nx xs"
    have Y: "pdevs_val e Y = nx * pdevs_val e xs"
      by (simp add: Y_def)
    have "(nx + nx') * pdevs_val e xs = pdevs_val e Y + nx' * pdevs_val e xs"
      unfolding Y by (simp add: algebra_simps)
    also

    define Y' where "Y' = fst (trunc_bound_pdevs p Y)"
    define Y_err where "Y_err = snd (trunc_bound_pdevs p Y)"
    have Y_err: "abs (- pdevs_val e (trunc_err_pdevs p Y)) \<le> Y_err"
      by (auto simp: Y_err_def trunc_bound_pdevs_def abs_pdevs_val_le_tdev' e)
    have "pdevs_val e Y = pdevs_val e Y' + - pdevs_val e (trunc_err_pdevs p Y)"
      by (simp add: Y'_def trunc_bound_pdevs_def pdevs_val_trunc_err_pdevs)
    finally
    have "\<bar>x ^ n - aform_val e (c, Y') \<bar> =
      \<bar>ce' + - pdevs_val e (trunc_err_pdevs p Y) + nx' * pdevs_val e xs + ?err\<bar>"
      by (simp add: algebra_simps aform_val_def)
    also have "\<dots> \<le> ce + Y_err + Ye + ERR"
      by (intro ERR abs_triangle_ineq[THEN order_trans] add_mono ce' Ye Y_err)
    also have "\<dots> \<le> sum_list' p [ce, Y_err, Ye, real_of_float ERR]"
      by (auto intro!: sum_list'_sum_list_le)
    finally show ?thesis
      using n
      by (intro aform_errI)
        (auto simp: power_aform_err_def c_def Y'_def C_def Y_def ERR_def x0_def nx_def xs_def NX_def
          ce_def Y_err_def Ye_def xe_def nxe_def t_def Let_def split_beta' set_of_eq err_def)
  qed
qed

definition [code_abbrev]: "is_float r \<longleftrightarrow> r \<in> float"
lemma [code]: "is_float (real_of_float f) = True"
  by (auto simp: is_float_def)

definition "powr_aform_err p X A = (
    if Inf_aform_err p X > 0 then do {
      L \<leftarrow> ln_aform_err p X;
      exp_aform_err p (mult_aform' p A L)
    }
    else approx_bin p (powr_float_interval p) X A)"

lemma interval_extension_powr: "interval_extension2 (powr_float_interval p) (powr)"
  using powr_float_interval_eqI[of p]
  by (auto simp: interval_extension2_def)

theorem powr_aform_err:
  assumes x: "x \<in> aform_err e X"
  assumes a: "a \<in> aform_err e A"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes Y: "powr_aform_err p X A = Some Y"
  shows "x powr a \<in> aform_err e Y"
proof cases
  assume pos: "Inf_aform_err p X > 0"
  with Inf_Sup_aform_err[OF e, of X p] x
  have "x > 0" by auto
  then have "x powr a = exp (a * ln x)"
    by (simp add: powr_def)
  also
  from pos obtain L where L: "ln_aform_err p X = Some L"
    and E: "exp_aform_err p (mult_aform' p A L) = Some Y"
    using Y
    by (auto simp: bind_eq_Some_conv powr_aform_err_def)
  from ln_aform_err[OF x L e] have "ln x \<in> aform_err e L" .
  from mult_aform'E[OF e a this] have "a * ln x \<in> aform_err e (mult_aform' p A L)" .
  from exp_aform_err[OF this E e]
  have "exp (a * ln x) \<in> aform_err e Y" .
  finally show ?thesis .
next
  from x a have xa: "x \<in> aform_err e (fst X, snd X)" "a \<in> aform_err e (fst A, snd A)" by simp_all
  assume "\<not> Inf_aform_err p X > 0"
  then have "approx_bin p (powr_float_interval p) (fst X, snd X) (fst A, snd A) = Some Y"
    using Y by (auto simp: powr_aform_err_def)
  from approx_binE[OF interval_extension_powr xa this e]
  show "x powr a \<in> aform_err e Y" .
qed

fun
  approx_floatarith :: "nat \<Rightarrow> floatarith \<Rightarrow> aform_err list \<Rightarrow> (aform_err) option"
where
  "approx_floatarith p (Add a b) vs =
    do {
      a1 \<leftarrow> approx_floatarith p a vs;
      a2 \<leftarrow> approx_floatarith p b vs;
      Some (add_aform' p a1 a2)
    }"
| "approx_floatarith p (Mult a b) vs =
    do {
      a1 \<leftarrow> approx_floatarith p a vs;
      a2 \<leftarrow> approx_floatarith p b vs;
      Some (mult_aform' p a1 a2)
    }"
| "approx_floatarith p (Inverse a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      inverse_aform_err p a
    }"
| "approx_floatarith p (Minus a) vs =
    map_option (apfst uminus_aform) (approx_floatarith p a vs)"
| "approx_floatarith p (Num f) vs =
    Some (num_aform (real_of_float f), 0)"
| "approx_floatarith p (Var i) vs =
  (if i < length vs then Some (vs ! i) else None)"
| "approx_floatarith p (Abs a) vs =
    do {
      r \<leftarrow> approx_floatarith p a vs;
      let ivl = ivl_of_aform_err p r;
      let i = lower ivl;
      let s = upper ivl;
      if i > 0 then Some r
      else if s < 0 then Some (apfst uminus_aform r)
      else do {
        Some (ivl_err (real_interval (abs_interval ivl)))
      }
    }"
| "approx_floatarith p (Min a b) vs =
    do {
      a1 \<leftarrow> approx_floatarith p a vs;
      a2 \<leftarrow> approx_floatarith p b vs;
      Some (min_aform_err p a1 a2)
    }"
| "approx_floatarith p (Max a b) vs =
    do {
      a1 \<leftarrow> approx_floatarith p a vs;
      a2 \<leftarrow> approx_floatarith p b vs;
      Some (max_aform_err p a1 a2)
    }"
| "approx_floatarith p (Floor a) vs =
    approx_un p (\<lambda>ivl. Some (floor_float_interval ivl)) (approx_floatarith p a vs)"
| "approx_floatarith p (Cos a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      cos_aform_err p a
    }"
| "approx_floatarith p Pi vs = Some (ivl_err (real_interval (pi_float_interval p)))"
| "approx_floatarith p (Sqrt a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      sqrt_aform_err p a
    }"
| "approx_floatarith p (Ln a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      ln_aform_err p a
    }"
| "approx_floatarith p (Arctan a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      arctan_aform_err p a
    }"
| "approx_floatarith p (Exp a) vs =
    do {
      a \<leftarrow> approx_floatarith p a vs;
      exp_aform_err p a
    }"
| "approx_floatarith p (Power a n) vs =
    do {
      ((a, as), e) \<leftarrow> approx_floatarith p a vs;
      if is_float a \<and> is_float e then Some (power_aform_err p ((a, as), e) n)
      else None
    }"
| "approx_floatarith p (Powr a b) vs =
    do {
      ae1 \<leftarrow> approx_floatarith p a vs;
      ae2 \<leftarrow> approx_floatarith p b vs;
      powr_aform_err p ae1 ae2
    }"

lemma uminus_aform_uminus_aform[simp]: "uminus_aform (uminus_aform z) = (z::'a::real_vector aform)"
  by (auto intro!: prod_eqI pdevs_eqI simp: uminus_aform_def)

lemma degree_aform_inverse_aform':
  "degree_aform X \<le> n \<Longrightarrow> degree_aform (fst (inverse_aform' p X)) \<le> n"
  unfolding inverse_aform'_def
  by (auto simp: Let_def trunc_bound_pdevs_def intro!: degree_pdev_upd_le degree_trunc_pdevs_le)

lemma degree_aform_inverse_aform:
  assumes "inverse_aform p X = Some Y"
  assumes "degree_aform X \<le> n"
  shows "degree_aform (fst Y) \<le> n"
  using assms
  by (auto simp: inverse_aform_def Let_def degree_aform_inverse_aform' split: if_splits)

lemma degree_aform_ivl_err[simp]: "degree_aform (fst (ivl_err a)) = 0"
  by (auto simp: ivl_err_def)

lemma degree_aform_approx_bin:
  assumes "approx_bin p ivl X Y = Some Z"
  assumes "degree_aform (fst X) \<le> m"
  assumes "degree_aform (fst Y) \<le> m"
  shows "degree_aform (fst Z) \<le> m"
  using assms
  by (auto simp: approx_bin_def bind_eq_Some_conv Basis_list_real_def
      intro!: order_trans[OF degree_aform_independent_from]
      order_trans[OF degree_aform_of_ivl])

lemma degree_aform_approx_un:
  assumes "approx_un p ivl X = Some Y"
  assumes "case X of None \<Rightarrow> True | Some X \<Rightarrow> degree_aform (fst X) \<le> d1"
  shows "degree_aform (fst Y) \<le> d1"
  using assms
  by (auto simp: approx_un_def bind_eq_Some_conv Basis_list_real_def
      intro!: order_trans[OF degree_aform_independent_from]
      order_trans[OF degree_aform_of_ivl])

lemma degree_aform_num_aform[simp]: "degree_aform (num_aform x) = 0"
  by (auto simp: num_aform_def)

lemma degree_max_aform:
  assumes "degree_aform_err x \<le> d"
  assumes "degree_aform_err y \<le> d"
  shows "degree_aform_err (max_aform_err p x y) \<le> d"
  using assms
  by (auto simp: max_aform_err_def Let_def Basis_list_real_def split: prod.splits
      intro!: order_trans[OF degree_aform_independent_from] order_trans[OF degree_aform_of_ivl])

lemma degree_min_aform:
  assumes "degree_aform_err x \<le> d"
  assumes "degree_aform_err y \<le> d"
  shows "degree_aform_err ((min_aform_err p x y)) \<le> d"
  using assms
  by (auto simp: min_aform_err_def Let_def Basis_list_real_def split: prod.splits
      intro!: order_trans[OF degree_aform_independent_from] order_trans[OF degree_aform_of_ivl])

lemma degree_aform_acc_err:
  "degree_aform (fst (acc_err p X e)) \<le> d"
  if "degree_aform (fst X) \<le> d"
  using that by (auto simp: acc_err_def)

lemma degree_pdev_upd_degree:
  assumes "degree b \<le> Suc n"
  assumes "degree b \<le> Suc (degree_aform_err X)"
  assumes "degree_aform_err X \<le> n"
  shows "degree (pdev_upd b (degree_aform_err X) 0) \<le> n"
  using assms
  by (auto intro!: degree_le)

lemma degree_aform_err_inverse_aform_err:
  assumes "inverse_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: inverse_aform_err_def bind_eq_Some_conv aform_to_aform_err_def
      acc_err_def map_aform_err_def
      aform_err_to_aform_def
      intro!: degree_aform_acc_err)
  apply (rule degree_pdev_upd_degree)
    apply (auto dest!: degree_aform_inverse_aform)
  apply (meson degree_pdev_upd_le nat_le_linear not_less_eq_eq order_trans)
  apply (meson degree_pdev_upd_le nat_le_linear not_less_eq_eq order_trans)
  done

lemma degree_aform_err_affine_unop:
  "degree_aform_err (affine_unop p a b d X) \<le> n"
  if "degree_aform_err X \<le> n"
  using that
  by (auto simp: affine_unop_def trunc_bound_pdevs_def degree_trunc_pdevs_le split: prod.splits)


lemma degree_aform_err_min_range_mono:
  assumes "min_range_mono p F D l u X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  by (auto simp: min_range_mono_def bind_eq_Some_conv aform_to_aform_err_def
      acc_err_def map_aform_err_def mid_err_def range_reduce_aform_err_def
      aform_err_to_aform_def Let_def split: if_splits prod.splits
      intro!: degree_aform_err_affine_unop)

lemma degree_aform_err_min_range_antimono:
  assumes "min_range_antimono p F D l u X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  by (auto simp: min_range_antimono_def bind_eq_Some_conv aform_to_aform_err_def
      acc_err_def map_aform_err_def mid_err_def range_reduce_aform_err_def
      aform_err_to_aform_def Let_def split: if_splits prod.splits
      intro!: degree_aform_err_affine_unop)

lemma degree_aform_err_cos_aform_err:
  assumes "cos_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: cos_aform_err_def bind_eq_Some_conv aform_to_aform_err_def
      acc_err_def map_aform_err_def mid_err_def range_reduce_aform_err_def
      aform_err_to_aform_def Let_def split: if_splits prod.splits
      intro!: degree_aform_err_affine_unop)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_antimono degree_aform_ivl_err zero_le)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_mono degree_aform_ivl_err zero_le)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_mono degree_aform_ivl_err zero_le)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_antimono degree_aform_ivl_err zero_le)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_antimono degree_aform_ivl_err zero_le)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_antimono degree_aform_ivl_err zero_le)
  done

lemma degree_aform_err_sqrt_aform_err:
  assumes "sqrt_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: sqrt_aform_err_def Let_def split: if_splits)
  apply (metis degree_aform_err_min_range_mono)
  done

lemma degree_aform_err_arctan_aform_err:
  assumes "arctan_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: arctan_aform_err_def bind_eq_Some_conv)
  apply (metis degree_aform_err_min_range_mono)
  done

lemma degree_aform_err_exp_aform_err:
  assumes "exp_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: exp_aform_err_def bind_eq_Some_conv)
  apply (metis degree_aform_err_min_range_mono)
  done

lemma degree_aform_err_ln_aform_err:
  assumes "ln_aform_err p X = Some Y"
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: ln_aform_err_def Let_def split: if_splits)
  apply (metis degree_aform_err_add_aform' degree_aform_err_min_range_mono degree_aform_ivl_err zero_le)
  done

lemma degree_aform_err_power_aform_err:
  assumes "degree_aform_err X \<le> n"
  shows "degree_aform_err (power_aform_err p X m) \<le> n"
  using assms
  by (auto simp: power_aform_err_def Let_def trunc_bound_pdevs_def degree_trunc_pdevs_le
      split: if_splits prod.splits)

lemma degree_aform_err_powr_aform_err:
  assumes "powr_aform_err p X Z = Some Y"
  assumes "degree_aform_err X \<le> n"
  assumes "degree_aform_err Z \<le> n"
  shows "degree_aform_err Y \<le> n"
  using assms
  apply (auto simp: powr_aform_err_def bind_eq_Some_conv degree_aform_mult_aform'
      dest!: degree_aform_err_ln_aform_err degree_aform_err_exp_aform_err
      split: if_splits)
  apply (metis degree_aform_mult_aform' fst_conv order_trans snd_conv)
  apply (rule degree_aform_approx_bin, assumption)
  apply auto
  done

lemma approx_floatarith_degree:
  assumes "approx_floatarith p ra VS = Some X"
  assumes "\<And>V. V \<in> set VS \<Longrightarrow> degree_aform_err V \<le> d"
  shows "degree_aform_err X \<le> d"
  using assms
proof (induction ra arbitrary: X)
  case (Add ra1 ra2)
  then show ?case 
    by (auto simp: bind_eq_Some_conv intro!: degree_aform_err_add_aform' degree_aform_acc_err)
next
  case (Minus ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv)
next
  case (Mult ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: degree_aform_mult_aform' degree_aform_acc_err)
next
  case (Inverse ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_inverse_aform_err)
next
  case (Cos ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_cos_aform_err)
next
  case (Arctan ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_arctan_aform_err)
next
  case (Abs ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv Let_def Basis_list_real_def
        intro!: order_trans[OF degree_aform_independent_from] order_trans[OF degree_aform_of_ivl]
          degree_aform_acc_err
        split: if_splits) 
next
  case (Max ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: degree_max_aform degree_aform_acc_err)
next
  case (Min ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: degree_min_aform degree_aform_acc_err)
next
  case Pi
  then show ?case
    by (auto simp: bind_eq_Some_conv Let_def Basis_list_real_def
        intro!: order_trans[OF degree_aform_independent_from] order_trans[OF degree_aform_of_ivl]
          degree_aform_acc_err
        split: if_splits)
next
  case (Sqrt ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_sqrt_aform_err)
next
  case (Exp ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_exp_aform_err)
next
  case (Powr ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_powr_aform_err)
next
  case (Ln ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro: degree_aform_err_ln_aform_err)
next
  case (Power ra x2a)
  then show ?case
    by (auto intro!: degree_aform_err_power_aform_err simp: bind_eq_Some_conv split: if_splits)
next
  case (Floor ra)
  then show ?case
    apply -
    by (rule degree_aform_approx_un) (auto split: option.splits)
next
  case (Var x)
  then show ?case
    by (auto simp: max_def split: if_splits)
      (use Var.prems(2) nat_le_linear nth_mem order_trans in blast)+
next
  case (Num x)
  then show ?case by auto
qed

definition affine_extension2 where
  "affine_extension2 fnctn_aff fnctn \<longleftrightarrow> (
    \<forall>d a1 a2 X e2.
      fnctn_aff d a1 a2 = Some X \<longrightarrow>
      e2 \<in> UNIV \<rightarrow> {- 1..1} \<longrightarrow>
      d \<ge> degree_aform a1 \<longrightarrow>
      d \<ge> degree_aform a2 \<longrightarrow>
      (\<exists>e3 \<in> UNIV \<rightarrow> {- 1..1}.
        (fnctn (aform_val e2 a1) (aform_val e2 a2) = aform_val e3 X \<and>
          (\<forall>n. n < d \<longrightarrow> e3 n = e2 n) \<and>
          aform_val e2 a1 = aform_val e3 a1 \<and> aform_val e2 a2 = aform_val e3 a2)))"

lemma affine_extension2E:
  assumes "affine_extension2 fnctn_aff fnctn"
  assumes "fnctn_aff d a1 a2 = Some X"
    "e \<in> UNIV \<rightarrow> {- 1..1}"
    "d \<ge> degree_aform a1"
    "d \<ge> degree_aform a2"
  obtains e' where "e' \<in> UNIV \<rightarrow> {- 1..1}"
    "fnctn (aform_val e a1) (aform_val e a2) = aform_val e' X"
    "\<And>n. n < d \<Longrightarrow> e' n = e n"
    "aform_val e a1 = aform_val e' a1"
    "aform_val e a2 = aform_val e' a2"
  using assms
  unfolding affine_extension2_def
  by metis

lemma aform_err_uminus_aform:
  "- x \<in> aform_err e (uminus_aform X, ba)"
  if "e \<in> UNIV \<rightarrow> {-1 .. 1}" "x \<in> aform_err e (X, ba)"
  using that by (auto simp: aform_err_def)

definition "aforms_err e (xs::aform_err list) = listset (map (aform_err e) xs)"

lemma aforms_err_Nil[simp]: "aforms_err e [] = {[]}"
  and aforms_err_Cons: "aforms_err e (x#xs) = set_Cons (aform_err e x) (aforms_err e xs)"
  by (auto simp: aforms_err_def)

lemma in_set_ConsI: "a#b \<in> set_Cons A B"
  if "a \<in> A" and "b \<in> B"
  using that
  by (auto simp: set_Cons_def)

lemma mem_aforms_err_Cons_iff[simp]: "x#xs \<in> aforms_err e (X#XS) \<longleftrightarrow> x \<in> aform_err e X \<and> xs \<in> aforms_err e XS"
  by (auto simp: aforms_err_Cons set_Cons_def)

lemma mem_aforms_err_Cons_iff_Ex_conv: "x \<in> aforms_err e (X#XS) \<longleftrightarrow> (\<exists>y ys. x = y#ys \<and> y \<in> aform_err e X \<and> ys \<in> aforms_err e XS)"
  by (auto simp: aforms_err_Cons set_Cons_def)

lemma listset_Cons_mem_conv:
  "a # vs \<in> listset AVS \<longleftrightarrow> (\<exists>A VS. AVS = A # VS \<and> a \<in> A \<and> vs \<in> listset VS)"
  by (induction AVS) (auto simp: set_Cons_def)

lemma listset_Nil_mem_conv[simp]:
  "[] \<in> listset AVS \<longleftrightarrow> AVS = []"
  by (induction AVS) (auto simp: set_Cons_def)

lemma listset_nthD: "vs \<in> listset VS \<Longrightarrow> i < length vs \<Longrightarrow> vs ! i \<in> VS ! i"
  by (induction vs arbitrary: VS i)
     (auto simp: nth_Cons listset_Cons_mem_conv split: nat.splits)

lemma length_listsetD:
  "vs \<in> listset VS \<Longrightarrow> length vs = length VS"
  by (induction vs arbitrary: VS) (auto simp: listset_Cons_mem_conv)

lemma length_aforms_errD:
  "vs \<in> aforms_err e VS \<Longrightarrow> length vs = length VS"
  by (auto simp: aforms_err_def length_listsetD)

lemma nth_aforms_errI:
  "vs ! i \<in> aform_err e (VS ! i)"
  if "vs \<in> aforms_err e VS" "i < length vs"
  using that
  unfolding aforms_err_def
  apply -
  apply (frule listset_nthD, assumption)
  by (auto simp: aforms_err_def length_listsetD )

lemma eucl_truncate_down_float[simp]: "eucl_truncate_down p x \<in> float"
  by (auto simp: eucl_truncate_down_def)

lemma eucl_truncate_up_float[simp]: "eucl_truncate_up p x \<in> float"
  by (auto simp: eucl_truncate_up_def)

lemma trunc_bound_eucl_float[simp]: "fst (trunc_bound_eucl p x) \<in> float"
  "snd (trunc_bound_eucl p x) \<in> float"
  by (auto simp: trunc_bound_eucl_def Let_def)

lemma add_aform'_float:
  "add_aform' p x y = ((a, b), ba) \<Longrightarrow> a \<in> float"
  "add_aform' p x y = ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: add_aform'_def Let_def)

lemma uminus_aform_float: "uminus_aform (aa, bb) = (a, b) \<Longrightarrow> aa \<in> float \<Longrightarrow> a \<in> float"
  by (auto simp: uminus_aform_def)

lemma mult_aform'_float: "mult_aform' p x y = ((a, b), ba) \<Longrightarrow> a \<in> float"
   "mult_aform' p x y = ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: mult_aform'_def Let_def split_beta')

lemma inverse_aform'_float: "inverse_aform' p x = ((a, bb), baa) \<Longrightarrow> a \<in> float"
  using [[linarith_split_limit=256]]
  by (auto simp: inverse_aform'_def Let_def)

lemma inverse_aform_float:
  "inverse_aform p x = Some ((a, bb), baa) \<Longrightarrow> a \<in> float"
  by (auto simp: inverse_aform_def Let_def apfst_def map_prod_def uminus_aform_def
      inverse_aform'_float
      split: if_splits prod.splits)

lemma inverse_aform_err_float: "inverse_aform_err p x = Some ((a, b), ba) \<Longrightarrow> a \<in> float"
   "inverse_aform_err p x = Some ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: inverse_aform_err_def map_aform_err_def acc_err_def bind_eq_Some_conv
      aform_err_to_aform_def aform_to_aform_err_def inverse_aform_float)

lemma affine_unop_float:
  "affine_unop p asdf aaa bba h = ((a, b), ba) \<Longrightarrow> a \<in> float"
  "affine_unop p asdf aaa bba h = ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: affine_unop_def trunc_bound_eucl_def Let_def split: prod.splits)

lemma min_range_antimono_float:
  "min_range_antimono p f f' i g h = Some ((a, b), ba) \<Longrightarrow> a \<in> float"
  "min_range_antimono p f f' i g h = Some ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: min_range_antimono_def Let_def bind_eq_Some_conv mid_err_def
      affine_unop_float split: prod.splits)

lemma min_range_mono_float:
  "min_range_mono p f f' i g h = Some ((a, b), ba) \<Longrightarrow> a \<in> float"
  "min_range_mono p f f' i g h = Some ((a, b), ba) \<Longrightarrow> ba \<in> float"
  by (auto simp: min_range_mono_def Let_def bind_eq_Some_conv mid_err_def
      affine_unop_float split: prod.splits)

lemma in_float_timesI: "a \<in> float" if "b = a * 2" "b \<in> float"
proof -
  from that have "a = b / 2" by simp
  also have "\<dots> \<in> float" using that(2) by auto
  finally show ?thesis .
qed

lemma interval_extension_floor: "interval_extension1 (\<lambda>ivl. Some (floor_float_interval ivl)) floor"
  by (auto simp: interval_extension1_def floor_float_intervalI)

lemma approx_floatarith_Elem:
  assumes "approx_floatarith p ra VS = Some X"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "vs \<in> aforms_err e VS"
  shows "interpret_floatarith ra vs \<in> aform_err e X"
  using assms(1)
proof (induction ra arbitrary: X)
  case (Add ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: add_aform'[OF e])
next
  case (Minus ra)
  then show ?case
    by (auto intro!: aform_err_uminus_aform[OF e])
next
  case (Mult ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: mult_aform'E[OF e])
next
  case (Inverse ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: inverse_aform_err[OF e])
next
  case (Cos ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: cos_aform_err[OF _ _ e])
next
  case (Arctan ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: arctan_aform_err[OF _ _ e])
next
  case (Abs fa)
  from Abs.prems
  obtain a where a: "approx_floatarith p fa VS = Some a"
    by (auto simp add: Let_def bind_eq_Some_conv)
  from Abs.IH[OF a]
  have mem: "interpret_floatarith fa vs \<in> aform_err e a"
    by auto
  then have mem': "-interpret_floatarith fa vs \<in> aform_err e (apfst uminus_aform a)"
    by (auto simp: aform_err_def)

  let ?i = "lower (ivl_of_aform_err p a)"
  let ?s = "upper (ivl_of_aform_err p a)"
  consider "?i > 0" | "?i \<le> 0" "?s < 0" | "?i \<le> 0" "?s \<ge> 0"
    by arith
  then show ?case
  proof cases
    case hyps: 1
    then show ?thesis
      using Abs.prems mem ivl_of_aform_err[OF e mem, of p]
      by (auto simp: a set_of_eq)
  next
    case hyps: 2
    then show ?thesis
      using Abs.prems mem ivl_of_aform_err[OF e mem, of p]
          ivl_of_aform_err[OF e mem', of p]
      by (cases a) (auto simp: a abs_real_def set_of_eq intro!: aform_err_uminus_aform[OF e])
  next
    case hyps: 3
    then show ?thesis
      using Abs.prems mem ivl_of_aform_err[OF e mem, of p]
      by (auto simp: a abs_real_def max_def Let_def set_of_eq)
  qed
next
  case (Max ra1 ra2)
  from Max.prems
  obtain a b where a: "approx_floatarith p ra1 VS = Some a"
    and b: "approx_floatarith p ra2 VS = Some b"
    by (auto simp add: Let_def bind_eq_Some_conv)
  from Max.IH(1)[OF a] Max.IH(2)[OF b]
  have mem: "interpret_floatarith ra1 vs \<in> aform_err e a"
    "interpret_floatarith ra2 vs \<in> aform_err e b"
    by auto
  let ?ia = "lower (ivl_of_aform_err p a)"
  let ?sa = "upper (ivl_of_aform_err p a)"
  let ?ib = "lower (ivl_of_aform_err p b)"
  let ?sb = "upper (ivl_of_aform_err p b)"
  consider "?sa < ?ib" | "?sa \<ge> ?ib" "?sb < ?ia" | "?sa \<ge> ?ib" "?sb \<ge> ?ia"
    by arith
  then show ?case
    using Max.prems mem ivl_of_aform_err[OF e mem(1), of p] ivl_of_aform_err[OF e mem(2), of p]
    by cases (auto simp: a b max_def max_aform_err_def set_of_eq)
next
  case (Min ra1 ra2)
  from Min.prems
  obtain a b where a: "approx_floatarith p ra1 VS = Some a"
    and b: "approx_floatarith p ra2 VS = Some b"
    by (auto simp add: Let_def bind_eq_Some_conv)
  from Min.IH(1)[OF a] Min.IH(2)[OF b]
  have mem: "interpret_floatarith ra1 vs \<in> aform_err e a"
    "interpret_floatarith ra2 vs \<in> aform_err e b"
    by auto
  let ?ia = "lower (ivl_of_aform_err p a)"
  let ?sa = "upper (ivl_of_aform_err p a)"
  let ?ib = "lower (ivl_of_aform_err p b)"
  let ?sb = "upper (ivl_of_aform_err p b)"
  consider "?sa < ?ib" | "?sa \<ge> ?ib" "?sb < ?ia" | "?sa \<ge> ?ib" "?sb \<ge> ?ia"
    by arith
  then show ?case
    using Min.prems mem ivl_of_aform_err[OF e mem(1), of p] ivl_of_aform_err[OF e mem(2), of p]
    by cases (auto simp: a b min_def min_aform_err_def set_of_eq)
next
  case Pi
  then show ?case using pi_float_interval
    by (auto simp: )
next
  case (Sqrt ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: sqrt_aform_err[OF _ _ e])
next
  case (Exp ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: exp_aform_err[OF _ _ e])
next
  case (Powr ra1 ra2)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: powr_aform_err[OF _ _ e])
next
  case (Ln ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: ln_aform_err[OF _ _ e])
next
  case (Power ra x2a)
  then show ?case
    by (auto simp: bind_eq_Some_conv is_float_def
        intro!: power_aform_err[OF _ _ _ e] split: if_splits)
next
  case (Floor ra)
  then show ?case
    by (auto simp: bind_eq_Some_conv intro!: approx_unE[OF interval_extension_floor e]
        split: option.splits)
next
  case (Var x)
  then show ?case
    using assms(3)
    apply -
    apply (frule length_aforms_errD)
    by (auto split: if_splits simp: aform_err_def dest!: nth_aforms_errI[where i=x])
next
  case (Num x)
  then show ?case
    by (auto split: if_splits simp: aform_err_def num_aform_def aform_val_def)
qed

primrec approx_floatariths_aformerr ::
  "nat \<Rightarrow> floatarith list \<Rightarrow> aform_err list \<Rightarrow> aform_err list option"
  where
    "approx_floatariths_aformerr _ [] _ = Some []"
  | "approx_floatariths_aformerr p (a#bs) vs =
      do {
        a \<leftarrow> approx_floatarith p a vs;
        r \<leftarrow> approx_floatariths_aformerr p bs vs;
        Some (a#r)
      }"


lemma approx_floatariths_Elem:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "approx_floatariths_aformerr p ra VS = Some X"
  assumes "vs \<in> aforms_err e VS"
  shows "interpret_floatariths ra vs \<in> aforms_err e X"
  using assms(2)
proof (induction ra arbitrary: X)
  case Nil then show ?case by simp
next
  case (Cons ra ras)
  from Cons.prems
  obtain a r where a: "approx_floatarith p ra VS = Some a"
    and r: "approx_floatariths_aformerr p ras VS = Some r"
    and X: "X = a # r"
    by (auto simp: bind_eq_Some_conv)
  then show ?case
    using assms(1)
    by (auto simp: X Cons.IH intro!: approx_floatarith_Elem assms)
qed

lemma fold_max_mono:
  fixes x::"'a::linorder"
  shows "x \<le> y \<Longrightarrow> fold max zs x \<le> fold max zs y"
  by (induct zs arbitrary: x y) (auto intro!: Cons simp: max_def)

lemma fold_max_le_self:
  fixes y::"'a::linorder"
  shows "y \<le> fold max ys y"
  by (induct ys) (auto intro: order_trans[OF _ fold_max_mono])

lemma fold_max_le:
  fixes x::"'a::linorder"
  shows "x \<in> set xs \<Longrightarrow> x \<le> fold max xs z"
  by (induct xs arbitrary: x z) (auto intro: order_trans[OF _ fold_max_le_self])

abbreviation "degree_aforms_err \<equiv> degrees o map (snd o fst)"

definition "aforms_err_to_aforms d xs =
  (map (\<lambda>(d, x). aform_err_to_aform x d) (zip [d..<d + length xs] xs))"

lemma aform_vals_empty[simp]: "aform_vals e' [] = []"
  by (auto simp: aform_vals_def)
lemma aforms_err_to_aforms_Nil[simp]: "(aforms_err_to_aforms n []) = []"
  by (auto simp: aforms_err_to_aforms_def)

lemma aforms_err_to_aforms_Cons[simp]:
  "aforms_err_to_aforms n (X # XS) = aform_err_to_aform X n # aforms_err_to_aforms (Suc n) XS"
  by (auto simp: aforms_err_to_aforms_def not_le nth_append nth_Cons 
      intro!: nth_equalityI split: nat.splits)

lemma degree_aform_err_to_aform_le:
  "degree_aform (aform_err_to_aform X n) \<le> max (degree_aform_err X) (Suc n)"
  by (auto simp: aform_err_to_aform_def intro!: degree_le)

lemma less_degree_aform_aform_err_to_aformD: "i < degree_aform (aform_err_to_aform X n) \<Longrightarrow> i < max (Suc n) (degree_aform_err X)"
  using degree_aform_err_to_aform_le[of X n] by auto

lemma pdevs_domain_aform_err_to_aform:
  "pdevs_domain (snd (aform_err_to_aform X n)) = pdevs_domain (snd (fst X)) \<union> (if snd X = 0 then {} else {n})"
  if "n \<ge> degree_aform_err X"
  using that
  by (auto simp: aform_err_to_aform_def split: if_splits)

lemma length_aforms_err_to_aforms[simp]: "length (aforms_err_to_aforms i XS) = length XS"
  by (auto simp: aforms_err_to_aforms_def)

lemma aforms_err_to_aforms_ex:
  assumes X: "x \<in> aforms_err e X"
  assumes deg: "degree_aforms_err X \<le> n"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "\<exists>e'\<in> UNIV \<rightarrow> {-1 .. 1}. x = aform_vals e' (aforms_err_to_aforms n X) \<and>
    (\<forall>i < n. e' i = e i)"
  using X deg
proof (induction X arbitrary: x n)
  case Nil then show ?case using e
    by (auto simp: o_def degrees_def intro!: bexI[where x="\<lambda>i. e i"])
next
  case (Cons X XS)
  from Cons.prems obtain y ys where ys:
    "degree_aform_err X \<le> n"
    "degree_aforms_err XS \<le> n"
    "x = y # ys" "y \<in> aform_err e X" "ys \<in> aforms_err e XS"
    by (auto simp: mem_aforms_err_Cons_iff_Ex_conv degrees_def)
  then have "degree_aforms_err XS \<le> Suc n" by auto
  from Cons.IH[OF ys(5) this]
  obtain e' where e': "e'\<in>UNIV \<rightarrow> {- 1..1}" "ys = aform_vals e' (aforms_err_to_aforms (Suc n) XS)"
    "(\<forall>i<n. e' i = e i)"
    by auto
  from aform_err_to_aformE[OF ys(4,1)] obtain err where err:
    "y = aform_val (e(n := err)) (aform_err_to_aform X n)" "- 1 \<le> err" "err \<le> 1"
    by auto
  show ?case
  proof (safe intro!: bexI[where x="e'(n:=err)"], goal_cases)
    case 1
    then show ?case
      unfolding ys e' err
      apply (auto simp: aform_vals_def  aform_val_def simp del:  pdevs_val_upd)
       apply (rule pdevs_val_degree_cong)
        apply simp
      subgoal
        using ys e'
        by (auto dest!: less_degree_aform_aform_err_to_aformD simp: max_def split: if_splits)
      subgoal premises prems for a b
      proof -
        have "pdevs_val (\<lambda>a. if a = n then err else e' a) b = pdevs_val (e'(n:=err)) b"
          unfolding fun_upd_def by simp
        also have "\<dots> = pdevs_val e' b - e' n * pdevs_apply b n + err * pdevs_apply b n"
          by simp
        also
        from prems
        obtain i where i: "aforms_err_to_aforms (Suc n) XS ! i = (a, b)"
          "i < length (aforms_err_to_aforms (Suc n) XS)"
          by (auto simp: in_set_conv_nth )
        { note i(1)[symmetric]
          also have "aforms_err_to_aforms (Suc n) XS ! i = aform_err_to_aform (XS ! i) (Suc n + i) "
            unfolding aforms_err_to_aforms_def
            using i
            by (simp del: upt_Suc)
          finally have "b = snd (aform_err_to_aform (XS ! i) (Suc n + i))" by (auto simp: prod_eq_iff)
        } note b = this
        have "degree_aform_err (XS ! i) \<le> n"
          using ys(2) i by (auto simp:  degrees_def)
        then have "n \<notin> pdevs_domain b" unfolding b
          apply (subst pdevs_domain_aform_err_to_aform)
          by (auto intro!: degree)
        then have "pdevs_apply b n = 0" by simp
        finally
        show ?thesis by simp
      qed
      done
  next
    case (2 i)
    then show ?case
      using e' by auto
  next
    case (3 i)
    then show ?case
      using e' err
      by auto
  qed
qed

lemma aforms_err_to_aformsE:
  assumes X: "x \<in> aforms_err e X"
  assumes deg: "degree_aforms_err X \<le> n"
    assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  obtains e' where "x = aform_vals e' (aforms_err_to_aforms n X)" "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
    "\<And>i. i < n \<Longrightarrow> e' i = e i"
  using aforms_err_to_aforms_ex[OF X deg e]
  by blast

definition "approx_floatariths p ea as =
  do {
    let da = (degree_aforms as);
    let aes = (map (\<lambda>x. (x, 0)) as);
    rs \<leftarrow> approx_floatariths_aformerr p ea aes;
    let d = max da (degree_aforms_err (rs));
    Some (aforms_err_to_aforms d rs)
  }"

lemma listset_sings[simp]:
  "listset (map (\<lambda>x. {f x}) as) = {map f as}"
  by (induction as) (auto simp: set_Cons_def)

lemma approx_floatariths_outer:
  assumes "approx_floatariths p ea as = Some XS"
  assumes "vs \<in> Joints as"
  shows "(interpret_floatariths ea vs @ vs) \<in> Joints (XS @ as)"
proof -
  from assms obtain da aes rs d where
     da: "da = degree_aforms as"
    and aes: "aes = (map (\<lambda>x. (x, 0)) as)"
    and rs: "approx_floatariths_aformerr p ea aes = Some rs"
    and d: "d = max da (degree_aforms_err (rs))"
    and XS: "aforms_err_to_aforms d rs = XS"
    by (auto simp: approx_floatariths_def Let_def bind_eq_Some_conv)
  have abbd: "(a, b) \<in> set as \<Longrightarrow> degree b \<le> degree_aforms as" for a b
    apply (rule degrees_leD[OF order_refl]) by force
  from da d have i_less: "(a, b) \<in> set as \<Longrightarrow> i < degree b \<Longrightarrow> i < min d da" for i a b
    by (auto dest!: abbd)

  have abbd: "(a, b) \<in> set as \<Longrightarrow> degree b \<le> degree_aforms as" for a b
    apply (rule degrees_leD[OF order_refl]) by force
  from assms obtain e' where vs: "vs = (map (aform_val e') as)" and e': "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
    by (auto simp: Joints_def valuate_def)
  note vs
  also
  have vs_aes: "vs \<in> aforms_err e' aes"
    unfolding aes
    by (auto simp: vs aforms_err_def o_def aform_err_def)
  from approx_floatariths_Elem[OF e' rs this]
  have iars: "interpret_floatariths ea (map (aform_val e') as) \<in> aforms_err e' rs"
    by (auto simp: vs)
  have "degree_aforms_err rs \<le> d"
    by (auto simp: d da)
  from aforms_err_to_aformsE[OF iars this e'] obtain e where
    "interpret_floatariths ea (map (aform_val e') as) = aform_vals e XS"
    and e: "e \<in> UNIV \<rightarrow> {- 1..1}" "\<And>i. i < d \<Longrightarrow> e i = e' i"
    by (auto simp: XS)
  note this (1)
  finally have "interpret_floatariths ea vs = aform_vals e XS" .

  moreover

  from e have e'_eq: "e' i = e i" if "i < min d da" for i
    using that
    by (auto simp: min_def split: if_splits)
  then have "vs = aform_vals e as"
    by (auto simp: vs aform_vals_def aform_val_def intro!: pdevs_val_degree_cong e'_eq i_less)

  ultimately show ?thesis
    using e(1)
    by (auto simp: Joints_def valuate_def aform_vals_def intro!: image_eqI[where x=e])
qed

lemma length_eq_NilI: "length [] = length []"
  and length_eq_ConsI: "length xs = length ys \<Longrightarrow> length (x#xs) = length (y#ys)"
  by auto


subsection \<open>Generic operations on Affine Forms in Euclidean Space\<close>

lemma pdevs_val_domain_cong:
  assumes "b = d"
  assumes "\<And>i. i \<in> pdevs_domain b \<Longrightarrow> a i = c i"
  shows "pdevs_val a b = pdevs_val c d"
  using assms
  by (auto simp: pdevs_val_pdevs_domain)

lemma fresh_JointsI:
  assumes "xs \<in> Joints XS"
  assumes "list_all (\<lambda>Y. pdevs_domain (snd X) \<inter> pdevs_domain (snd Y) = {}) XS"
  assumes "x \<in> Affine X"
  shows "x#xs \<in> Joints (X#XS)"
  using assms
  unfolding Joints_def Affine_def valuate_def
proof safe
  fix e e'::"nat \<Rightarrow> real"
  assume H: "list_all (\<lambda>Y. pdevs_domain (snd X) \<inter> pdevs_domain (snd Y) = {}) XS"
    "e \<in> UNIV \<rightarrow> {- 1..1}"
    "e' \<in> UNIV \<rightarrow> {- 1..1}"
  have "\<And>a b i. \<forall>Y\<in>set XS. pdevs_domain (snd X) \<inter> pdevs_domain (snd Y) = {} \<Longrightarrow>
       pdevs_apply b i \<noteq> 0 \<Longrightarrow>
       pdevs_apply (snd X) i \<noteq> 0 \<Longrightarrow>
       (a, b) \<notin> set XS"
    by (metis (poly_guards_query) IntI all_not_in_conv in_pdevs_domain snd_eqD)
  with H show
    "aform_val e' X # map (aform_val e) XS \<in> (\<lambda>e. map (aform_val e) (X # XS)) ` (UNIV \<rightarrow> {- 1..1})"
    by (intro image_eqI[where x = "\<lambda>i. if i \<in> pdevs_domain (snd X) then e' i else e i"])
      (auto simp: aform_val_def list_all_iff Pi_iff intro!: pdevs_val_domain_cong)
qed


primrec approx_slp::"nat \<Rightarrow> slp \<Rightarrow> aform_err list \<Rightarrow> aform_err list option"
where
  "approx_slp p [] xs = Some xs"
| "approx_slp p (ea # eas) xs =
    do {
      r \<leftarrow> approx_floatarith p ea xs;
      approx_slp p eas (r#xs)
    }"

lemma Nil_mem_Joints[intro, simp]: "[] \<in> Joints []"
  by (force simp: Joints_def valuate_def)

lemma map_nth_Joints: "xs \<in> Joints XS \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length XS) \<Longrightarrow> map (nth xs) is @ xs \<in> Joints (map (nth XS) is @ XS)"
  by (auto simp: Joints_def valuate_def)

lemma map_nth_Joints': "xs \<in> Joints XS \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length XS) \<Longrightarrow> map (nth xs) is \<in> Joints (map (nth XS) is)"
  by (rule Joints_appendD2[OF map_nth_Joints]) auto

lemma approx_slp_Elem:
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "vs \<in> aforms_err e VS"
  assumes "approx_slp p ra VS = Some X"
  shows "interpret_slp ra vs \<in> aforms_err e X"
  using assms(2-)
proof (induction ra arbitrary: X vs VS)
  case (Cons ra ras)
  from Cons.prems
  obtain a where a: "approx_floatarith p ra VS = Some a"
    and r: "approx_slp p ras (a # VS) = Some X"
    by (auto simp: bind_eq_Some_conv)
  from approx_floatarith_Elem[OF a e Cons.prems(1)]
  have "interpret_floatarith ra vs \<in> aform_err e a"
    by auto
  then have 1: "interpret_floatarith ra vs#vs \<in> aforms_err e (a#VS)"
    unfolding mem_aforms_err_Cons_iff
    using Cons.prems(1)
    by auto
  show ?case
    by (auto intro!: Cons.IH 1 r)
qed auto

definition "approx_slp_outer p n slp XS =
  do {
    let d = degree_aforms XS;
    let XSe = (map (\<lambda>x. (x, 0)) XS);
    rs \<leftarrow> approx_slp p slp XSe;
    let rs' = take n rs;
    let d' = max d (degree_aforms_err rs');
    Some (aforms_err_to_aforms d' rs')
  }"

lemma take_in_listsetI: "xs \<in> listset XS \<Longrightarrow> take n xs \<in> listset (take n XS)"
  by (induction XS arbitrary: xs n) (auto simp: take_Cons listset_Cons_mem_conv set_Cons_def split: nat.splits)

lemma take_in_aforms_errI: "take n xs \<in> aforms_err e (take n XS)"
  if "xs \<in> aforms_err e XS"
  using that
  by (auto simp: aforms_err_def take_map[symmetric] intro!: take_in_listsetI)

theorem approx_slp_outer:
  assumes "approx_slp_outer p n slp XS = Some RS"
  assumes slp: "slp = slp_of_fas fas" "n = length fas"
  assumes "xs \<in> Joints XS"
  shows "interpret_floatariths fas xs @ xs \<in> Joints (RS @ XS)"
proof -
  from assms obtain d XSe rs rs' d' where
    d: "d = degree_aforms XS"
    and XSe: "XSe = (map (\<lambda>x. (x, 0)) XS)"
    and rs: "approx_slp p (slp_of_fas fas) XSe = Some rs"
    and rs': "rs' = take (length fas) rs"
    and d': "d' = max d (degree_aforms_err rs')"
    and RS: "aforms_err_to_aforms d' rs' = RS"
    by (auto simp: approx_slp_outer_def Let_def bind_eq_Some_conv)
  have abbd: "(a, b) \<in> set XS \<Longrightarrow> degree b \<le> degree_aforms XS" for a b
    apply (rule degrees_leD[OF order_refl]) by force
  from d' d have i_less: "(a, b) \<in> set XS \<Longrightarrow> i < degree b \<Longrightarrow> i < min d d'" for i a b
    by (auto dest!: abbd)
  from assms obtain e' where vs: "xs = (map (aform_val e') XS)" and e': "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
    by (auto simp: Joints_def valuate_def)
  from d have d: "V \<in> set XS \<Longrightarrow> degree_aform V \<le> d" for V
    by (auto intro!: degrees_leD)
  have xs_XSe: "xs \<in> aforms_err e' XSe"
    by (auto simp: vs aforms_err_def XSe o_def aform_err_def)
  from approx_slp_Elem[OF e' xs_XSe rs]
  have aforms_err: "interpret_slp (slp_of_fas fas) xs \<in> aforms_err e' rs" .
  have "interpret_floatariths fas xs = take (length fas) (interpret_slp (slp_of_fas fas) xs)"
    using assms by (simp add: slp_of_fas)
  also
  from aforms_err
  have "take (length fas) (interpret_slp (slp_of_fas fas) xs) \<in> aforms_err e' rs'"
    unfolding rs'
    by (auto simp: take_map intro!: take_in_aforms_errI)
  finally have ier: "interpret_floatariths fas xs \<in> aforms_err e' rs'" .
  have "degree_aforms_err rs' \<le> d'" using d' by auto
  from aforms_err_to_aformsE[OF ier this e'] obtain e where
    "interpret_floatariths fas xs = aform_vals e RS"
    and e: "e \<in> UNIV \<rightarrow> {- 1..1}" "\<And>i. i < d' \<Longrightarrow> e i = e' i"
    unfolding RS
    by (auto simp: )
  moreover

  from e have e'_eq: "e' i = e i" if "i < min d d'" for i
    using that
    by (auto simp: min_def split: if_splits)
  then have "xs = aform_vals e XS"
    by (auto simp: vs aform_vals_def aform_val_def intro!: pdevs_val_degree_cong e'_eq i_less)

  ultimately show ?thesis
    using e(1)
    by (auto simp: Joints_def valuate_def aform_vals_def intro!: image_eqI[where x=e])

qed

theorem approx_slp_outer_plain:
  assumes "approx_slp_outer p n slp XS = Some RS"
  assumes slp: "slp = slp_of_fas fas" "n = length fas"
  assumes "xs \<in> Joints XS"
  shows "interpret_floatariths fas xs \<in> Joints RS"
proof -
  have "length fas = length RS"
  proof -
    have f1: "length xs = length XS"
      using Joints_imp_length_eq assms(4) by blast
    have "interpret_floatariths fas xs @ xs \<in> Joints (RS @ XS)"
      using approx_slp_outer assms(1) assms(2) assms(3) assms(4) by blast
    then show ?thesis
      using f1 Joints_imp_length_eq by fastforce
  qed
  with Joints_appendD2[OF approx_slp_outer[OF assms]] show ?thesis by simp
qed

end

end
