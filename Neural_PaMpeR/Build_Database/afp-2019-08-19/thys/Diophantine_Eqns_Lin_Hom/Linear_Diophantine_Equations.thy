(*
Author:  Florian Messner <florian.g.messner@uibk.ac.at>
Author:  Julian Parsert <julian.parsert@gmail.com>
Author:  Jonas Schöpf <jonas.schoepf@uibk.ac.at>
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Homogeneous Linear Diophantine Equations\<close>

theory Linear_Diophantine_Equations
  imports List_Vector
begin

(*TODO: move*)
lemma lcm_div_le:
  fixes a :: nat
  shows "lcm a b div b \<le> a"
  by (metis div_by_0 div_le_dividend div_le_mono div_mult_self_is_m lcm_nat_def neq0_conv)

(*TODO: move*)
lemma lcm_div_le':
  fixes a :: nat
  shows "lcm a b div a \<le> b"
  by (metis lcm.commute lcm_div_le)

(*TODO: move*)
lemma lcm_div_gt_0:
  fixes a :: nat
  assumes "a > 0" and "b > 0"
  shows "lcm a b div a > 0"
proof -
  have "lcm a b = (a * b) div (gcd a b)"
    using lcm_nat_def by blast
  moreover have "\<dots> > 0"
    using  assms
    by (metis assms calculation lcm_pos_nat)
  ultimately show ?thesis
    using assms
    by (metis div_by_0 div_mult2_eq div_positive gcd_le2_nat nat_mult_div_cancel_disj neq0_conv
              semiring_normalization_rules(7))
qed

(*TODO: move*)
lemma sum_list_list_update_Suc:
  assumes "i < length u"
  shows "sum_list (u[i := Suc (u ! i)]) = Suc (sum_list u)"
  using assms
proof (induct u arbitrary: i)
  case (Cons x xs)
  then show ?case by (simp_all split: nat.splits)
qed (simp)

(*TODO: move*)
lemma lessThan_conv:
  assumes "card A = n" and "\<forall>x\<in>A. x < n"
  shows "A = {..<n}"
  using assms by (simp add: card_subset_eq subsetI)

text \<open>
  Given a non-empty list \<open>xs\<close> of \<open>n\<close> natural numbers,
  either there is a value in \<open>xs\<close> that is \<open>0\<close> modulo \<open>n\<close>,
  or there are two values whose moduli coincide.
\<close>
lemma list_mod_cases:
  assumes "length xs = n" and "n > 0"
  shows "(\<exists>x\<in>set xs. x mod n = 0) \<or>
    (\<exists>i<length xs. \<exists>j<length xs. i \<noteq> j \<and> (xs ! i) mod n = (xs ! j) mod n)"
proof -
  let ?f = "\<lambda>x. x mod n" and ?X = "set xs"
  have *: "\<forall>x \<in> ?f ` ?X. x < n" using \<open>n > 0\<close> by auto
  consider (eq) "card (?f ` ?X) = card ?X" | (less) "card (?f ` ?X) < card ?X"
    using antisym_conv2 and card_image_le by blast
  then show ?thesis
  proof (cases)
    case eq
    show ?thesis
    proof (cases "distinct xs")
      assume "distinct xs"
      with eq have "card (?f ` ?X) = n"
        using \<open>distinct xs\<close> by (simp add: assms card_distinct distinct_card)
      from lessThan_conv [OF this *] and \<open>n > 0\<close>
      have "\<exists>x\<in>set xs. x mod n = 0" by (metis imageE lessThan_iff)
      then show ?thesis ..
    next
      assume "\<not> distinct xs"
      then show ?thesis by (auto) (metis distinct_conv_nth)
    qed
  next
    case less
    from pigeonhole [OF this]
    show ?thesis by (auto simp: inj_on_def iff: in_set_conv_nth)
  qed
qed

text \<open>
  Homogeneous linear Diophantine equations:
  \<open>a\<^sub>1x\<^sub>1 + \<cdots> + a\<^sub>mx\<^sub>m = b\<^sub>1y\<^sub>1 + \<cdots> + b\<^sub>ny\<^sub>n\<close>
\<close>
locale hlde_ops =
  fixes a b :: "nat list"
begin

abbreviation "m \<equiv> length a"
abbreviation "n \<equiv> length b"

\<comment> \<open>The set of all solutions.\<close>
definition Solutions :: "(nat list \<times> nat list) set"
  where
    "Solutions = {(x, y). a \<bullet> x = b \<bullet> y \<and> length x = m \<and> length y = n}"

lemma in_Solutions_iff:
  "(x, y) \<in> Solutions \<longleftrightarrow> length x = m \<and> length y = n \<and> a \<bullet> x = b \<bullet> y"
  by (auto simp: Solutions_def)

\<comment> \<open>The set of pointwise minimal solutions.\<close>
definition Minimal_Solutions :: "(nat list \<times> nat list) set"
  where
    "Minimal_Solutions = {(x, y) \<in> Solutions. nonzero x \<and>
      \<not> (\<exists>(u, v) \<in> Solutions. nonzero u \<and> u @ v <\<^sub>v x @ y)}"

definition dij :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "dij i j = lcm (a ! i) (b ! j) div (a ! i)"

definition eij :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "eij i j = lcm (a ! i) (b ! j) div (b ! j)"

definition sij :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat list)"
  where
    "sij i j = ((zeroes m)[i := dij i j], (zeroes n)[j := eij i j])"


subsection \<open>Further Constraints on Minimal Solutions\<close>

definition Ej :: "nat \<Rightarrow> nat list \<Rightarrow> nat set"
  where
    "Ej j x = { eij i j - 1 | i. i < length x \<and> x ! i \<ge> dij i j }"

definition Di :: "nat \<Rightarrow> nat list \<Rightarrow> nat set"
  where
    "Di i y = { dij i j - 1 | j. j < length y \<and> y ! j \<ge> eij i j }"

definition Di' :: "nat \<Rightarrow> nat list \<Rightarrow> nat set"
  where
    "Di' i y = { dij i (j + length b - length y) - 1 | j. j < length y \<and> y ! j \<ge> eij i (j + length b - length y) }"

lemma Ej_take_subset:
  "Ej j (take k x) \<subseteq> Ej j x"
  by (auto simp: Ej_def)

lemma Di_take_subset:
  "Di i (take l y) \<subseteq> Di i y"
  by (auto simp: Di_def)

lemma Di'_drop_subset:
  "Di' i (drop l y) \<subseteq> Di' i y"
  by (auto simp: Di'_def) (metis add.assoc add.commute less_diff_conv)

lemma finite_Ej:
  "finite (Ej j x)"
  by (rule finite_subset [of _ "(\<lambda>i. eij i j - 1) ` {0 ..< length x}"]) (auto simp: Ej_def)

lemma finite_Di:
  "finite (Di i y)"
  by (rule finite_subset [of _ "(\<lambda>j. dij i j - 1) ` {0 ..< length y}"]) (auto simp: Di_def)

lemma finite_Di':
  "finite (Di' i y)"
  by (rule finite_subset [of _ "(\<lambda>j. dij i (j + length b - length y) - 1) ` {0 ..< length y}"])
    (auto simp: Di'_def)

definition max_y :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "max_y x j = (if j < n \<and> Ej j x \<noteq> {} then Min (Ej j x) else Max (set a))"

definition max_x :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "max_x y i = (if i < m \<and> Di i y \<noteq> {} then Min (Di i y) else Max (set b))"

definition max_x' :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "max_x' y i = (if i < m \<and> Di' i y \<noteq> {} then Min (Di' i y) else Max (set b))"

lemma Min_Ej_le:
  assumes "j < n"
    and "e \<in> Ej j x"
    and "length x \<le> m"
  shows "Min (Ej j x) \<le> Max (set a)" (is "?m \<le> _")
proof -
  have "?m \<in> Ej j x"
    using assms and finite_Ej and Min_in by blast
  then obtain i where
    i: "?m = eij i j - 1" "i < length x" "x ! i \<ge> dij i j"
    by (auto simp: Ej_def)
  have "lcm (a ! i) (b ! j) div b ! j \<le> a ! i" by (rule lcm_div_le)
  then show ?thesis
    using i and assms
    by (auto simp: eij_def)
      (meson List.finite_set Max_ge diff_le_self le_trans less_le_trans nth_mem)
qed

lemma Min_Di_le:
  assumes "i < m"
    and "e \<in> Di i y"
    and "length y \<le> n"
  shows "Min (Di i y) \<le> Max (set b)" (is "?m \<le> _")
proof -
  have "?m \<in> Di i y"
    using assms and finite_Di and Min_in by blast
  then obtain j where
    j: "?m = dij i j - 1" "j < length y" "y ! j \<ge> eij i j"
    by (auto simp: Di_def)
  have "lcm (a ! i) (b ! j) div a ! i \<le> b ! j" by (rule lcm_div_le')
  then show ?thesis
    using j and assms
    by (auto simp: dij_def)
      (meson List.finite_set Max_ge diff_le_self le_trans less_le_trans nth_mem)
qed

lemma Min_Di'_le:
  assumes "i < m"
    and "e \<in> Di' i y"
    and "length y \<le> n"
  shows "Min (Di' i y) \<le> Max (set b)" (is "?m \<le> _")
proof -
  have "?m \<in> Di' i y"
    using assms and finite_Di' and Min_in by blast
  then obtain j where
    j: "?m = dij i (j + length b - length y) - 1" "j < length y" "y ! j \<ge> eij i (j + length b - length y)"
    by (auto simp: Di'_def)
  then have "j + length b - length y < length b" using assms by auto
  moreover
  have "lcm (a ! i) (b ! (j + length b - length y)) div a ! i \<le> b ! (j + length b - length y)" by (rule lcm_div_le')
  ultimately show ?thesis
    using j and assms
    by (auto simp: dij_def)
      (meson List.finite_set Max_ge diff_le_self le_trans less_le_trans nth_mem)
qed

lemma max_y_le_take:
  assumes "length x \<le> m"
  shows "max_y x j \<le> max_y (take k x) j"
  using assms and Min_Ej_le and Ej_take_subset and Min.subset_imp [OF _ _ finite_Ej]
  by (auto simp: max_y_def) blast

lemma max_x_le_take:
  assumes "length y \<le> n"
  shows "max_x y i \<le> max_x (take l y) i"
  using assms and Min_Di_le and Di_take_subset and Min.subset_imp [OF _ _ finite_Di]
  by (auto simp: max_x_def) blast

lemma max_x'_le_drop:
  assumes "length y \<le> n"
  shows "max_x' y i \<le> max_x' (drop l y) i"
  using assms and Min_Di'_le and Di'_drop_subset and Min.subset_imp [OF _ _ finite_Di']
  by (auto simp: max_x'_def) blast

end

abbreviation "Solutions \<equiv> hlde_ops.Solutions"
abbreviation "Minimal_Solutions \<equiv> hlde_ops.Minimal_Solutions"

abbreviation "dij \<equiv> hlde_ops.dij"
abbreviation "eij \<equiv> hlde_ops.eij"
abbreviation "sij \<equiv> hlde_ops.sij"

declare hlde_ops.dij_def [code]
declare hlde_ops.eij_def [code]
declare hlde_ops.sij_def [code]

lemma Solutions_sym: "(x, y) \<in> Solutions a b \<longleftrightarrow> (y, x) \<in> Solutions b a"
  by (auto simp: hlde_ops.in_Solutions_iff)

lemma Minimal_Solutions_imp_Solutions: "(x, y) \<in> Minimal_Solutions a b \<Longrightarrow> (x, y) \<in> Solutions a b"
  by (auto simp: hlde_ops.Minimal_Solutions_def)

lemma Minimal_SolutionsI:
  assumes "(x, y) \<in> Solutions a b"
    and "nonzero x"
    and "\<not> (\<exists>(u, v) \<in> Solutions a b. nonzero u \<and> u @ v <\<^sub>v x @ y)"
  shows "(x, y) \<in> Minimal_Solutions a b"
  using assms by (auto simp: hlde_ops.Minimal_Solutions_def)

lemma minimize_nonzero_solution:
  assumes "(x, y) \<in> Solutions a b" and "nonzero x"
  obtains u and v where "u @ v \<le>\<^sub>v x @ y" and "(u, v) \<in> Minimal_Solutions a b"
  using assms
proof (induct "x @ y" arbitrary: x y thesis rule: wf_induct [OF wf_less])
  case 1
  then show ?case
  proof (cases "(x, y) \<in> Minimal_Solutions a b")
    case False
    then obtain u and v where "nonzero u" and "(u, v) \<in> Solutions a b" and uv: "u @ v <\<^sub>v x @ y"
      using 1(3,4) by (auto simp: hlde_ops.Minimal_Solutions_def)
    with 1(1) [rule_format, of "u @ v" u v] obtain u' and v' where uv': "u' @ v' \<le>\<^sub>v u @ v"
      and "(u', v') \<in> Minimal_Solutions a b" by blast
    moreover have "u' @ v' \<le>\<^sub>v x @ y" using uv and uv' by auto
    ultimately show ?thesis by (intro 1(2))
  qed blast
qed

lemma Minimal_SolutionsI':
  assumes "(x, y) \<in> Solutions a b"
    and "nonzero x"
    and "\<not> (\<exists>(u, v) \<in> Minimal_Solutions a b. u @ v <\<^sub>v x @ y)"
  shows "(x, y) \<in> Minimal_Solutions a b"
proof (rule Minimal_SolutionsI [OF assms(1,2)])
  show "\<not> (\<exists>(u, v) \<in> Solutions a b. nonzero u \<and> u @ v <\<^sub>v x @ y)"
  proof
    assume "\<exists>(u, v) \<in> Solutions a b. nonzero u \<and> u @ v <\<^sub>v x @ y"
    then obtain u and v where "(u, v) \<in> Solutions a b" and "nonzero u"
      and uv: "u @ v <\<^sub>v x @ y" by blast
    then obtain u' and v' where "(u', v') \<in> Minimal_Solutions a b"
      and uv': "u' @ v' \<le>\<^sub>v u @ v" by (blast elim: minimize_nonzero_solution)
    moreover have "u' @ v' <\<^sub>v x @ y" using uv and uv' by auto
    ultimately show False using assms by blast
  qed
qed

lemma Minimal_Solutions_length:
  "(x, y) \<in> Minimal_Solutions a b \<Longrightarrow> length x = length a \<and> length y = length b"
  by (auto simp: hlde_ops.Minimal_Solutions_def hlde_ops.in_Solutions_iff)

lemma Minimal_Solutions_gt0:
  "(x, y) \<in> Minimal_Solutions a b \<Longrightarrow> zeroes (length x) <\<^sub>v x"
  using zero_less by (auto simp: hlde_ops.Minimal_Solutions_def)

lemma Minimal_Solutions_sym:
  assumes "0 \<notin> set a" and "0 \<notin> set b"
  shows "(xs, ys) \<in> Minimal_Solutions a b \<longrightarrow> (ys, xs) \<in> Minimal_Solutions b a"
  using assms
  by (auto simp: hlde_ops.Minimal_Solutions_def hlde_ops.Solutions_def
           dest: dotprod_eq_nonzero_iff dest!: less_append_swap [of _ _ ys xs])

locale hlde = hlde_ops +
  assumes no0: "0 \<notin> set a" "0 \<notin> set b"
begin

lemma nonzero_Solutions_iff:
  assumes "(x, y) \<in> Solutions"
  shows "nonzero x \<longleftrightarrow> nonzero y"
  using assms and no0 by (auto simp: in_Solutions_iff dest: dotprod_eq_nonzero_iff)

lemma Minimal_Solutions_min:
  assumes "(x, y) \<in> Minimal_Solutions"
    and "u @ v <\<^sub>v x @ y"
    and "a \<bullet> u = b \<bullet> v"
    and [simp]: "length u = m"
    and non0: "nonzero (u @ v)"
  shows False
proof -
  have [simp]: "length v = n" using assms by (force dest: less_appendD Minimal_Solutions_length)
  have "(u, v) \<in> Solutions" using \<open>a \<bullet> u = b \<bullet> v\<close> by (simp add: in_Solutions_iff)
  moreover from nonzero_Solutions_iff [OF this] have "nonzero u" using non0 by auto
  ultimately show False using assms by (auto simp: hlde_ops.Minimal_Solutions_def)
qed

lemma Solutions_snd_not_0:
  assumes "(x, y) \<in> Solutions"
    and "nonzero x"
  shows "nonzero y"
  using assms by (metis nonzero_Solutions_iff)

end

subsection \<open>Pointwise Restricting Solutions\<close>

text \<open>
  Constructing the list of \<open>u\<close> vectors from Huet's proof @{cite "Huet1978"}, satisfying
  \<^item> \<open>\<forall>i<length u. u ! i \<le> y ! i\<close> and
  \<^item> \<open>0 < sum_list u \<le> a\<^sub>k\<close>.
\<close>

text \<open>
  Given \<open>y\<close>, increment a "previous" \<open>u\<close> vector at first position
  starting from \<open>i\<close> where \<open>u\<close> is strictly smaller than \<open>y\<close>. If this
  is not possible, return \<open>u\<close> unchanged.
\<close>
function inc :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where
    "inc y i u =
      (if i < length y then
        if u ! i < y ! i then u[i := u ! i + 1]
        else inc y (Suc i) u
      else u)"
  by (pat_completeness) auto
termination inc
  by (relation "measure (\<lambda>(y, i, u). max (length y) (length u) - i)") auto
(*inc.simps may cause simplification to loop*)
declare inc.simps [simp del]

text \<open>
  Starting from the 0-vector produce \<open>u\<close>s by iteratively
  incrementing with respect to \<open>y\<close>.
\<close>
definition huets_us :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" ("\<^bold>u" 1000)
  where
    "\<^bold>u y i = ((inc y 0) ^^ Suc i) (zeroes (length y))"

lemma huets_us_simps [simp]:
  "\<^bold>u y 0 = inc y 0 (zeroes (length y))"
  "\<^bold>u y (Suc i) = inc y 0 (\<^bold>u y i)"
  by (auto simp: huets_us_def)

lemma length_inc [simp]: "length (inc y i u) = length u"
  by (induct y i u rule: inc.induct) (simp add: inc.simps)

lemma length_us [simp]:
  "length (\<^bold>u y i) = length y"
  by (induct i) (simp_all)

text \<open>
  \<open>inc\<close> produces vectors that are pointwise smaller than \<open>y\<close>
\<close>
lemma inc_le:
  assumes "length u = length y" and "i < length y" and "u \<le>\<^sub>v y"
  shows "inc y i u \<le>\<^sub>v y"
  using assms by (induct y i u rule: inc.induct)
    (auto simp: inc.simps nth_list_update less_eq_def)

lemma us_le:
  assumes "length y > 0"
  shows "\<^bold>u y i \<le>\<^sub>v y"
  using assms by (induct i) (auto simp: inc_le le_length)

lemma sum_list_inc_le:
  "u \<le>\<^sub>v y \<Longrightarrow> sum_list (inc y i u) \<le> sum_list y"
  by (induct y i u rule: inc.induct)
    (auto simp: inc.simps intro: le_sum_list_mono)

lemma sum_list_inc_gt0:
  assumes "sum_list u > 0" and "length y = length u"
  shows "sum_list (inc y i u) > 0"
  using assms
proof (induct y i u rule: inc.induct)
  case (1 y i u)
  then show ?case
    by (auto simp add: inc.simps)
      (meson Suc_neq_Zero gr_zeroI set_update_memI sum_list_eq_0_iff)
qed

lemma sum_list_inc_gt0':
  assumes "length u = length y" and "i < length y" and "y ! i > 0" and "j \<le> i"
  shows "sum_list (inc y j u) > 0"
  using assms
proof (induct y j u rule: inc.induct)
  case (1 y i u)
  then show ?case
    by (auto simp: inc.simps [of y i] sum_list_update)
      (metis elem_le_sum_list le_antisym le_zero_eq neq0_conv not_less_eq_eq sum_list_inc_gt0)
qed

lemma sum_list_us_gt0:
  assumes "sum_list y \<noteq> 0"
  shows "0 < sum_list (\<^bold>u y i)"
  using assms by (induct i) (auto simp: in_set_conv_nth sum_list_inc_gt0' sum_list_inc_gt0)

lemma sum_list_inc_le':
  assumes "length u = length y"
  shows "sum_list (inc y i u) \<le> sum_list u + 1"
  using assms
  by (induct y i u rule: inc.induct) (auto simp: inc.simps sum_list_update)

lemma sum_list_us_le:
  "sum_list (\<^bold>u y i) \<le> i + 1"
proof (induct i)
  case 0
  then show ?case
    by (auto simp: sum_list_update)
      (metis Suc_eq_plus1 in_set_replicate length_replicate sum_list_eq_0_iff sum_list_inc_le')
next
  case (Suc i)
  then show ?case
    by auto (metis Suc_le_mono add.commute le_trans length_us plus_1_eq_Suc sum_list_inc_le')
qed

lemma sum_list_us_bounded:
  assumes "i < k"
  shows "sum_list (\<^bold>u y i) \<le> k"
  using assms and sum_list_us_le [of y i] by force

lemma sum_list_inc_eq_sum_list_Suc:
  assumes "length u = length y" and "i < length y"
    and "\<exists>j\<ge>i. j < length y \<and> u ! j < y ! j"
  shows "sum_list (inc y i u) = Suc (sum_list u)"
  using assms
  by (induct y i u rule: inc.induct)
    (metis  inc.simps Suc_eq_plus1 Suc_leI antisym_conv2 leD sum_list_list_update_Suc)

lemma sum_list_us_eq:
  assumes "i < sum_list y"
  shows "sum_list (\<^bold>u y i) = i + 1"
  using assms
proof (induct i)
  case (Suc i)
  then show ?case
    by (auto)
      (metis (no_types, lifting) Suc_eq_plus1 gr_implies_not0 length_pos_if_in_set
       length_us less_Suc_eq_le less_imp_le_nat linorder_antisym_conv2 not_less_eq_eq
       sum_list_eq_0_iff sum_list_inc_eq_sum_list_Suc sum_list_less_diff_Ex us_le)
qed (metis Suc_eq_plus1 Suc_leI antisym_conv gr_implies_not0 sum_list_us_gt0 sum_list_us_le)

lemma inc_ge: "length u = length y \<Longrightarrow> u \<le>\<^sub>v inc y i u"
  by (induct y i u rule: inc.induct) (auto simp: inc.simps nth_list_update less_eq_def)

lemma us_le_mono:
  assumes "i < j"
  shows "\<^bold>u y i \<le>\<^sub>v \<^bold>u y j"
  using assms
proof (induct "j - i" arbitrary: j i)
  case (Suc n)
  then show ?case
    by (simp add: Suc.prems inc_ge order.strict_implies_order order_vec.lift_Suc_mono_le)
qed simp

lemma us_mono:
  assumes "i < j" and "j < sum_list y"
  shows "\<^bold>u y i <\<^sub>v \<^bold>u y j"
proof -
  let ?u = "\<^bold>u y i" and ?v = "\<^bold>u y j"
  have "?u \<le>\<^sub>v ?v"
    using us_le_mono [OF \<open>i < j\<close>] by simp
  moreover have "sum_list ?u < sum_list ?v"
    using assms by (auto simp: sum_list_us_eq)
  ultimately show ?thesis by (intro le_sum_list_less) (auto simp: less_eq_def)
qed

context hlde
begin

lemma max_coeff_bound_right:
  assumes "(xs, ys) \<in> Minimal_Solutions"
  shows "\<forall>x \<in> set xs. x \<le> maxne0 ys b" (is "\<forall>x\<in>set xs. x \<le> ?m")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain k
    where k_def: "k < length xs \<and> \<not> (xs ! k \<le> ?m)"
    by (metis in_set_conv_nth)
  have sol: "(xs, ys) \<in> Solutions"
    using assms Minimal_Solutions_def by auto
  then have len: "m = length xs" by (simp add: in_Solutions_iff)
  have max_suml: "?m * sum_list ys \<ge> b \<bullet> ys"
    using maxne0_times_sum_list_gt_dotprod sol by (auto simp: in_Solutions_iff)
  then have is_sol: "b \<bullet> ys = a \<bullet> xs"
    using sol by (auto simp: in_Solutions_iff)
  then have a_ge_ak: "a \<bullet> xs \<ge> a ! k * xs ! k"
    using dotprod_pointwise_le k_def len by auto
  then have ak_gt_max: "a ! k * xs ! k > a ! k * ?m"
    using no0 in_set_conv_nth k_def len by fastforce
  then have sl_ys_g_ak: "sum_list ys > a ! k"
    by (metis a_ge_ak is_sol less_le_trans max_suml
        mult.commute mult_le_mono1 not_le)
  define Seq where
    Seq_def: "Seq = map (\<^bold>u ys) [0 ..< a ! k]"
  have ak_n0: "a ! k \<noteq> 0"
    using \<open>a ! k * ?m < a ! k * xs ! k\<close> by auto
  have "zeroes (length ys) <\<^sub>v ys"
    by (intro zero_less) (metis gr_implies_not0 nonzero_iff sl_ys_g_ak sum_list_eq_0_iff)
  then have "length Seq > 0"
    using ak_n0 Seq_def by auto
  have u_in_nton: "\<forall>u \<in> set Seq. length u = length ys"
    by (simp add: Seq_def)
  have prop_3: "\<forall>u \<in> set Seq. u \<le>\<^sub>v ys"
  proof -
    have "length ys > 0"
      using sl_ys_g_ak by auto
    then show ?thesis
      using us_le [of ys ] less_eq_def Seq_def by (simp)
  qed
  have prop_4_1: "\<forall>u \<in> set Seq. sum_list u > 0"
    by (metis Seq_def sl_ys_g_ak gr_implies_not_zero imageE
        set_map sum_list_us_gt0)
  have prop_4_2: "\<forall>u \<in> set Seq. sum_list u \<le> a ! k"
    by (simp add: Seq_def sum_list_us_bounded)
  have prop_5: "\<exists>u. length u = length ys \<and> u \<le>\<^sub>v ys \<and> sum_list u > 0 \<and> sum_list u \<le> a ! k"
    using \<open>0 < length Seq\<close> nth_mem prop_3 prop_4_1 prop_4_2 u_in_nton by blast
  define Us where
    "Us = {u. length u = length ys \<and> u \<le>\<^sub>v ys \<and> sum_list u > 0 \<and> sum_list u \<le> a ! k}"
  have "\<exists>u \<in> Us. b \<bullet> u mod a ! k = 0"
  proof (rule ccontr)
    assume neg_th: "\<not> ?thesis"
    define Seq_p where
      "Seq_p = map (dotprod b) Seq"
    have "length Seq = a ! k"
      by (simp add: Seq_def)
    then consider (eq_0)  "(\<exists>x\<in>set Seq_p. x mod (a ! k) = 0)" |
      (not_0) "(\<exists>i<length Seq_p. \<exists>j<length Seq_p. i \<noteq> j \<and>
               (Seq_p ! i) mod (a!k) = (Seq_p ! j) mod (a!k))"
      using list_mod_cases[of Seq_p] Seq_p_def ak_n0 by auto
    then show False
    proof (cases)
      case eq_0
      have "\<exists>u \<in> set Seq. b \<bullet> u mod a ! k = 0"
        using Seq_p_def eq_0 by auto
      then show False
        by (metis (mono_tags, lifting) Us_def mem_Collect_eq
            neg_th prop_3 prop_4_1 prop_4_2 u_in_nton)
    next
      case not_0
      obtain i and j where
        i_j: "i<length Seq_p" "j<length Seq_p" " i \<noteq> j"
        " Seq_p ! i mod a ! k = Seq_p ! j mod a ! k"
        using not_0 by blast
      define v where
        v_def: "v = Seq!i"
      define w where
        w_def: "w = Seq!j"
      have mod_eq: "b \<bullet> v mod a!k = b \<bullet> w mod a!k"
        using Seq_p_def i_j w_def v_def i_j  by auto
      have "v <\<^sub>v w \<or> w <\<^sub>v v"
        using \<open>i \<noteq> j\<close> and i_j
      proof (cases "i < j")
        case True
        then show ?thesis
          using Seq_p_def sl_ys_g_ak i_j(2) local.Seq_def us_mono v_def w_def by auto
      next
        case False
        then show ?thesis
          using Seq_p_def sl_ys_g_ak \<open>i \<noteq> j\<close> i_j(1) local.Seq_def us_mono v_def w_def by auto
      qed
      then show False
      proof
        assume ass: "v <\<^sub>v w"
        define u where
          u_def: "u = w -\<^sub>v v"
        have "w \<le>\<^sub>v ys"
          using Seq_p_def w_def i_j(2) prop_3 by force
        then have prop_3: "less_eq u ys"
          using vdiff_le ass less_eq_def order_vec.less_imp_le u_def by auto
        have prop_4_1: "sum_list u > 0"
          using le_sum_list_mono [of v w] ass u_def sum_list_vdiff_distr [of v w]
          by (simp add: less_vec_sum_list_less)
        have prop_4_2: "sum_list u \<le> a ! k"
        proof -
          have "u \<le>\<^sub>v w" using u_def
            using ass less_eq_def order_vec.less_imp_le vdiff_le by auto
          then show ?thesis
            by (metis Seq_p_def i_j(2) length_map le_sum_list_mono
                less_le_trans not_le nth_mem prop_4_2 w_def)
        qed
        have "b \<bullet> u mod a ! k = 0"
          by (metis (mono_tags, lifting) in_Solutions_iff \<open>w \<le>\<^sub>v ys\<close> u_def ass no0(2)
              less_eq_def mem_Collect_eq mod_eq mods_with_vec_2 prod.simps(2) sol)
        then show False using neg_th
          by (metis (mono_tags, lifting) Us_def less_eq_def mem_Collect_eq
              prop_3 prop_4_1 prop_4_2)
      next
        assume ass: "w <\<^sub>v v"
        define u where
          u_def: "u = v -\<^sub>v w"
        have "v \<le>\<^sub>v ys"
          using Seq_p_def v_def i_j(1) prop_3 by force
        then have prop_3: "u \<le>\<^sub>v ys"
          using vdiff_le ass less_eq_def order_vec.less_imp_le u_def by auto
        have prop_4_1: "sum_list u > 0"
          using le_sum_list_mono [of w v] sum_list_vdiff_distr [of w v]
            \<open>u \<equiv> v -\<^sub>v w\<close> ass less_vec_sum_list_less by auto
        have prop_4_2: "sum_list u \<le> a!k"
        proof -
          have "u \<le>\<^sub>v v" using u_def
            using ass less_eq_def order_vec.less_imp_le vdiff_le by auto
          then show ?thesis
            by (metis Seq_p_def i_j(1) le_neq_implies_less length_map less_imp_le_nat
                less_le_trans nth_mem prop_4_2 le_sum_list_mono v_def)
        qed
        have "b \<bullet> u mod a ! k = 0"
          by (metis (mono_tags, lifting) in_Solutions_iff \<open>v \<le>\<^sub>v ys\<close> u_def ass no0(2)
              less_eq_def mem_Collect_eq mod_eq mods_with_vec_2 prod.simps(2) sol)
        then show False
          by (metis (mono_tags, lifting) neg_th Us_def less_eq_def mem_Collect_eq prop_3 prop_4_1 prop_4_2)
      qed
    qed
  qed
  then obtain u where
    u3_4: "u \<le>\<^sub>v ys" "sum_list u > 0" "sum_list u \<le> a ! k" " b \<bullet> u mod (a ! k) = 0"
    "length u = length ys"
    unfolding Us_def by auto
  have u_b_len: "length u = n"
    using  less_eq_def u3_4 in_Solutions_iff sol by simp
  have "b \<bullet> u \<le> maxne0 u b * sum_list u"
    by (simp add: maxne0_times_sum_list_gt_dotprod u_b_len)
  also have "... \<le> ?m * a ! k"
    by (intro mult_le_mono) (simp_all add: u3_4 maxne0_mono)
  also have "... < a ! k * xs ! k"
    using ak_gt_max by auto
  then obtain zk where
    zk: "b \<bullet> u = zk * a ! k"
    using u3_4(4) by auto
  have "length xs > k"
    by (simp add: k_def)
  have "zk \<noteq> 0"
  proof -
    have "\<exists>e \<in> set u. e \<noteq> 0"
      using u3_4
      by (metis neq0_conv sum_list_eq_0_iff)
    then have "b \<bullet> u > 0"
      using assms no0 u3_4
      unfolding dotprod_gt0_iff[OF u_b_len [symmetric]]
      by (fastforce simp add: in_set_conv_nth u_b_len)
    then have "a ! k > 0"
      using \<open>a ! k \<noteq> 0\<close> by blast
    then show ?thesis
      using \<open>0 < b \<bullet> u\<close> zk by auto
  qed
  define z where
    z_def: "z = (zeroes (length xs))[k := zk]"
  then have zk_zk: "z ! k = zk"
    by (auto simp add: \<open>k < length xs\<close>)
  have "length z = length xs"
    using assms z_def \<open>k < length xs\<close> by auto
  then have bu_eq_akzk: "b \<bullet> u = a ! k * z ! k"
    by (simp add: \<open>b \<bullet> u = zk * a ! k\<close> zk_zk)
  then have "z!k < xs!k"
    using ak_gt_max  calculation by auto
  then have z_less_xs: "z <\<^sub>v xs"
    by (auto simp add: z_def) (metis \<open>k < length xs\<close> le0 le_list_update less_def
        less_imp_le order_vec.dual_order.antisym nat_neq_iff z_def zk_zk)
  then have "z @ u <\<^sub>v xs @ ys"
    by (intro less_append) (auto simp add: u3_4(1) z_less_xs)
  moreover have "(z, u) \<in> Solutions"
    by (auto simp add: bu_eq_akzk in_Solutions_iff z_def u_b_len \<open>k < length xs\<close> len)
  moreover have "nonzero z"
    using \<open>length z = length xs\<close> and \<open>zk \<noteq> 0\<close> and k_def and zk_zk by (auto simp: nonzero_iff)
  ultimately show False using assms by (auto simp: Minimal_Solutions_def)
qed

text \<open>Proof of Lemma 1 of Huet's paper.\<close>
lemma max_coeff_bound:
  assumes "(xs, ys) \<in> Minimal_Solutions"
  shows "(\<forall>x \<in> set xs. x \<le> maxne0 ys b) \<and> (\<forall>y \<in> set ys. y \<le> maxne0 xs a)"
proof -
  interpret ba: hlde b a by (standard) (auto simp: no0)
  show ?thesis
    using assms and Minimal_Solutions_sym [OF no0, of xs ys]
    by (auto simp: max_coeff_bound_right ba.max_coeff_bound_right)
qed

lemma max_coeff_bound':
  assumes "(x, y) \<in> Minimal_Solutions"
  shows "\<forall>i<length x. x ! i \<le> Max (set b)" and "\<forall>j<length y. y ! j \<le> Max (set a)"
  using max_coeff_bound [OF assms] and maxne0_le_Max
  by auto (metis le_eq_less_or_eq less_le_trans nth_mem)+

lemma Minimal_Solutions_alt_def:
  "Minimal_Solutions = {(x, y)\<in>Solutions.
    (x, y) \<noteq> (zeroes m, zeroes n) \<and>
    x \<le>\<^sub>v replicate m (Max (set b)) \<and>
    y \<le>\<^sub>v replicate n (Max (set a)) \<and>
    \<not> (\<exists>(u, v)\<in>Solutions. nonzero u \<and> u @ v <\<^sub>v x @ y)}"
  by (auto simp: not_nonzero_iff Minimal_Solutions_imp_Solutions less_eq_def Minimal_Solutions_length max_coeff_bound'
    intro!: Minimal_SolutionsI' dest: Minimal_Solutions_gt0)
    (auto simp: Minimal_Solutions_def nonzero_Solutions_iff not_nonzero_iff)


subsection \<open>Special Solutions\<close>

definition Special_Solutions :: "(nat list \<times> nat list) set"
  where
    "Special_Solutions = {sij i j | i j. i < m \<and> j < n}"

lemma dij_neq_0:
  assumes "i < m"
    and "j < n"
  shows "dij i j \<noteq> 0"
proof -
  have "a ! i > 0" and "b ! j > 0"
    using assms and no0 by (simp_all add: in_set_conv_nth)
  then have "dij i j > 0"
    using lcm_div_gt_0 [of "a ! i" "b ! j"] by (simp add: dij_def)
  then show ?thesis by simp
qed

lemma eij_neq_0:
  assumes "i < m"
    and "j < n"
  shows "eij i j \<noteq> 0"
proof -
  have "a ! i > 0" and "b ! j > 0"
    using assms and no0  by (simp_all add: in_set_conv_nth)
  then have "eij i j > 0"
    using lcm_div_gt_0[of "b ! j"  "a ! i"] by (simp add: eij_def lcm.commute)
  then show ?thesis
    by simp
qed

lemma Special_Solutions_in_Solutions:
  "x \<in> Special_Solutions \<Longrightarrow> x \<in> Solutions"
  by (auto simp: in_Solutions_iff Special_Solutions_def sij_def dij_def eij_def)

lemma Special_Solutions_in_Minimal_Solutions:
  assumes "(x, y) \<in> Special_Solutions"
  shows "(x, y) \<in> Minimal_Solutions"
proof (intro Minimal_SolutionsI')
  show "(x, y) \<in> Solutions" by (fact Special_Solutions_in_Solutions [OF assms])
  then have [simp]: "length x = m" "length y = n" by (auto simp: in_Solutions_iff)
  show "nonzero x" using assms and dij_neq_0
    by (auto simp: Special_Solutions_def sij_def nonzero_iff)
     (metis length_replicate set_update_memI)
  show "\<not> (\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y)"
  proof
    assume "\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y"
    then obtain u and v where uv: "(u, v) \<in> Minimal_Solutions" and "u @ v <\<^sub>v x @ y"
      and [simp]: "length u = m" "length v = n"
      and "nonzero u" by (auto simp: Minimal_Solutions_def in_Solutions_iff)
    then consider "u <\<^sub>v x" and "v \<le>\<^sub>v y" | "v <\<^sub>v y" and "u \<le>\<^sub>v x" by (auto elim: less_append_cases)
    then show False
    proof (cases)
      case 1
      then obtain i and j where ij: "i < m" "j < n"
        and less_dij: "u ! i < dij i j"
        and "u \<le>\<^sub>v (zeroes m)[i := dij i j]"
        and "v \<le>\<^sub>v (zeroes n)[j := eij i j]"
        using assms by (auto simp: Special_Solutions_def sij_def unit_less)
      then have u: "u = (zeroes m)[i := u ! i]" and v: "v = (zeroes n)[j := v ! j]"
        by (auto simp: less_eq_def list_eq_iff_nth_eq)
          (metis le_zero_eq length_list_update length_replicate rep_upd_unit)+
      then have "u ! i > 0" using \<open>nonzero u\<close> and ij
        by (metis gr_implies_not0 neq0_conv unit_less zero_less)

      define c where "c = a ! i * u ! i"
      then have ac: "a ! i dvd c" by simp

      have "a \<bullet> u = b \<bullet> v" using uv by (auto simp: Minimal_Solutions_def in_Solutions_iff)
      then have "c = b ! j * v ! j"
        using ij unfolding c_def by (subst (asm) u, subst (asm)v, subst u, subst v) auto
      then have bc: "b ! j dvd c" by simp

      have "a ! i * u ! i < a ! i * dij i j"
        using less_dij and no0 and ij by (auto simp: in_set_conv_nth)
      then have "c < lcm (a ! i) (b ! j)" by (auto simp: dij_def c_def)
      moreover have "lcm (a ! i) (b ! j) dvd c" by (simp add: ac bc)
      moreover have "c > 0" using \<open>u ! i > 0\<close> and no0 and ij by (auto simp: c_def in_set_conv_nth)
      ultimately show False using ac and bc by (auto dest: nat_dvd_not_less)
    next
      case 2
      then obtain i and j where ij: "i < m" "j < n"
        and less_dij: "v ! j < eij i j"
        and "u \<le>\<^sub>v (zeroes m)[i := dij i j]"
        and "v \<le>\<^sub>v (zeroes n)[j := eij i j]"
        using assms by (auto simp: Special_Solutions_def sij_def unit_less)
      then have u: "u = (zeroes m)[i := u ! i]" and v: "v = (zeroes n)[j := v ! j]"
        by (auto simp: less_eq_def list_eq_iff_nth_eq)
          (metis le_zero_eq length_list_update length_replicate rep_upd_unit)+
      moreover have "nonzero v"
        using \<open>nonzero u\<close> and \<open>(u, v) \<in> Minimal_Solutions\<close>
          and Minimal_Solutions_imp_Solutions Solutions_snd_not_0 by blast
      ultimately have "v ! j > 0" using ij
        by (metis gr_implies_not0 neq0_conv unit_less zero_less)

      define c where "c = b ! j * v ! j"
      then have bc: "b ! j dvd c" by simp

      have "a \<bullet> u = b \<bullet> v" using uv by (auto simp: Minimal_Solutions_def in_Solutions_iff)
      then have "c = a ! i * u ! i"
        using ij unfolding c_def by (subst (asm) u, subst (asm)v, subst u, subst v) auto
      then have ac: "a ! i dvd c" by simp

      have "b ! j * v ! j < b ! j * eij i j"
        using less_dij and no0 and ij by (auto simp: in_set_conv_nth)
      then have "c < lcm (a ! i) (b ! j)" by (auto simp: eij_def c_def)
      moreover have "lcm (a ! i) (b ! j) dvd c" by (simp add: ac bc)
      moreover have "c > 0" using \<open>v ! j > 0\<close> and no0 and ij by (auto simp: c_def in_set_conv_nth)
      ultimately show False using ac and bc by (auto dest: nat_dvd_not_less)
    qed
  qed
qed

(*Lemma 2 of Huet*)
lemma non_special_solution_non_minimal:
  assumes "(x, y) \<in> Solutions - Special_Solutions"
    and ij: "i < m" "j < n"
    and "x ! i \<ge> dij i j" and "y ! j \<ge> eij i j"
  shows "(x, y) \<notin> Minimal_Solutions"
proof
  assume min: "(x, y) \<in> Minimal_Solutions"
  moreover have "sij i j \<in> Solutions"
    using ij by (intro Special_Solutions_in_Solutions) (auto simp: Special_Solutions_def)
  moreover have "(case sij i j of (u, v) \<Rightarrow> u @ v) <\<^sub>v x @ y"
    using assms and min
    apply (cases "sij i j")
    apply (auto simp: sij_def Special_Solutions_def)
    by (metis List_Vector.le0 Minimal_Solutions_length le_append le_list_update less_append order_vec.dual_order.strict_iff_order same_append_eq)
  moreover have "(case sij i j of (u, v) \<Rightarrow> nonzero u)"
    apply (auto simp: sij_def)
    by (metis dij_neq_0 ij length_replicate nonzero_iff set_update_memI)
  ultimately show False
    by (auto simp: Minimal_Solutions_def)
qed


subsection \<open>Huet's conditions\<close>

(*A*)
definition "cond_A xs ys \<longleftrightarrow> (\<forall>x\<in>set xs. x \<le> maxne0 ys b)"

(*B*)
definition "cond_B x \<longleftrightarrow>
  (\<forall>k\<le>m. take k a \<bullet> take k x \<le> b \<bullet> map (max_y (take k x)) [0 ..< n])"

(*C*)
definition "boundr x y \<longleftrightarrow> (\<forall>j<n. y ! j \<le> max_y x j)"

(*D*)
definition "cond_D x y \<longleftrightarrow> (\<forall>l\<le>n. take l b \<bullet> take l y \<le> a \<bullet> x)"


subsection \<open>New conditions: facilitating generation of candidates from right to left\<close>

(*condition on right sub-dotproduct*)
definition "subdprodr y \<longleftrightarrow>
  (\<forall>l\<le>n. take l b \<bullet> take l y \<le> a \<bullet> map (max_x (take l y)) [0 ..< m])"

(*condition on left sub-dotproduct*)
definition "subdprodl x y \<longleftrightarrow> (\<forall>k\<le>m. take k a \<bullet> take k x \<le> b \<bullet> y)"

(*bound on elements of left vector*)
definition "boundl x y \<longleftrightarrow> (\<forall>i<m. x ! i \<le> max_x y i)"

lemma boundr:
  assumes min: "(x, y) \<in> Minimal_Solutions"
    and "(x, y) \<notin> Special_Solutions"
  shows "boundr x y"
proof (unfold boundr_def, intro allI impI)
  fix j
  assume ass: "j < n"
  have ln: "m = length x \<and> n = length y"
    using assms Minimal_Solutions_def in_Solutions_iff min by auto
  have is_sol: "(x, y) \<in> Solutions"
    using assms Minimal_Solutions_def min by auto
  have j_less_l: "j < n"
    using assms ass le_less_trans by linarith
  consider (notemp) "Ej j x \<noteq> {}"  | (empty) " Ej j x = {}"
    by blast
  then show "y ! j \<le> max_y x j"
  proof (cases)
    case notemp
    have max_y_def: "max_y x j =  Min (Ej j x)"
      using j_less_l max_y_def notemp by auto
    have fin_e: "finite (Ej j x)"
      using finite_Ej [of j x] by auto
    have e_def': "\<forall>e \<in> Ej j x. (\<exists>i<length x. x ! i \<ge> dij i j \<and> eij i j - 1 = e)"
      using Ej_def [of j x] by auto
    then have "\<exists>i<length x. x ! i \<ge> dij i j \<and> eij i j - 1 = Min (Ej j x)"
      using notemp Min_in e_def' fin_e by blast
    then obtain i where
      i: "i < length x" "x ! i \<ge> dij i j" "eij i j - 1 = Min (Ej j x)"
      by blast
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with non_special_solution_non_minimal [of x y i j]
        and i and ln and assms and is_sol and j_less_l
      have "case sij i j of (u, v) \<Rightarrow> u @ v \<le>\<^sub>v x @ y"
        by (force simp: max_y_def)
      then have cs:"case sij i j of (u, v) \<Rightarrow> u @ v <\<^sub>v x @ y"
        using assms by(auto simp: Special_Solutions_def) (metis append_eq_append_conv
            i(1) j_less_l length_list_update length_replicate sij_def
            order_vec.le_neq_trans ln prod.sel(1))
      then obtain u v where
        u_v: "sij i j = (u, v)" "u @ v <\<^sub>v x @ y"
        by blast
      have dij_gt0: "dij i j > 0"
        using assms(1) assms(2) dij_neq_0 i(1) j_less_l ln by auto
      then have not_0_u: "nonzero u"
      proof (unfold nonzero_iff)
        have "i < length (zeroes m)" by (simp add: i(1) ln)
        then show "\<exists>i\<in>set u. i \<noteq> 0"
          by (metis (no_types) Pair_inject dij_gt0 set_update_memI sij_def u_v(1) neq0_conv)
      qed
      then have "sij i j \<in> Solutions"
        by (metis (mono_tags, lifting) Special_Solutions_def i(1)
            Special_Solutions_in_Solutions j_less_l ln mem_Collect_eq u_v(1))
      then show False
        using assms cs u_v not_0_u Minimal_Solutions_def min by auto
    qed
  next
    case empty
    have "\<forall>y\<in>set y. y \<le> Max (set a)"
      using assms and max_coeff_bound and maxne0_le_Max
      using le_trans by blast
    then  show ?thesis
      using empty j_less_l ln max_y_def by auto
  qed
qed

lemma boundl:
  assumes min: "(x, y) \<in> Minimal_Solutions"
    and "(x, y) \<notin> Special_Solutions"
  shows "boundl x y"
proof (unfold boundl_def, intro allI impI)
  fix i
  assume ass: "i < m"
  have ln: "n = length y \<and> m = length x"
    using assms Minimal_Solutions_def in_Solutions_iff min by auto
  have is_sol: "(x, y) \<in> Solutions"
    using assms Minimal_Solutions_def min by auto
  have i_less_l: "i < m"
    using assms ass le_less_trans by linarith
  consider (notemp) "Di i y \<noteq> {}"  | (empty) " Di i y = {}"
    by blast
  then show "x ! i \<le> max_x y i"
  proof (cases)
    case notemp
    have max_x_def: "max_x y i =  Min (Di i y)"
      using i_less_l max_x_def notemp by auto
    have fin_e: "finite (Di i y)"
      using finite_Di [of i y] by auto
    have e_def': "\<forall>e \<in> Di i y. (\<exists>j<length y. y ! j \<ge> eij i j \<and> dij i j - 1 = e)"
      using Di_def [of i y] by auto
    then have "\<exists>j<length y. y ! j \<ge> eij i j \<and> dij i j - 1 = Min (Di i y)"
      using notemp Min_in e_def' fin_e by blast
    then obtain j where
      j: "j < length y" "y ! j \<ge> eij i j" "dij i j - 1 = Min (Di i y)"
      by blast
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with non_special_solution_non_minimal [of x y i j]
        and j and ln and assms and is_sol and i_less_l
      have "case sij i j of (u, v) \<Rightarrow> u @ v \<le>\<^sub>v x @ y"
        by (force simp: max_x_def)
      then have cs: "case sij i j of (u, v) \<Rightarrow> u @ v <\<^sub>v x @ y"
        using assms by(auto simp: Special_Solutions_def) (metis append_eq_append_conv
            j(1) i_less_l length_list_update length_replicate sij_def
            order_vec.le_neq_trans ln prod.sel(1))
      then obtain u v where
        u_v: "sij i j = (u, v)" "u @ v <\<^sub>v x @ y"
        by blast
      have dij_gt0: "dij i j > 0"
        using assms(1) assms(2) dij_neq_0 j(1) i_less_l ln by auto
      then have not_0_u: "nonzero u"
      proof (unfold nonzero_iff)
        have "i < length (zeroes m)"
          using ass by simp
        then show "\<exists>i\<in>set u. i \<noteq> 0"
          by (metis (no_types) Pair_inject dij_gt0 set_update_memI sij_def u_v(1) neq0_conv)
      qed
      then have "sij i j \<in> Solutions"
        by (metis (mono_tags, lifting) Special_Solutions_def j(1)
            Special_Solutions_in_Solutions i_less_l ln mem_Collect_eq u_v(1))
      then show False
        using assms cs u_v not_0_u Minimal_Solutions_def min by auto
    qed
  next
    case empty
    have "\<forall>x\<in>set x. x \<le> Max (set b)"
      using assms and max_coeff_bound and maxne0_le_Max
      using le_trans by blast
    then  show ?thesis
      using empty i_less_l ln max_x_def by auto
  qed
qed

lemma Solution_imp_cond_D:
  assumes "(x, y) \<in> Solutions"
  shows "cond_D x y"
  using assms and dotprod_le_take by (auto simp: cond_D_def in_Solutions_iff)

lemma Solution_imp_subdprodl:
  assumes "(x, y) \<in> Solutions"
  shows "subdprodl x y"
  using assms and dotprod_le_take
  by (auto simp: subdprodl_def in_Solutions_iff) metis

theorem conds:
  assumes min: "(x, y) \<in> Minimal_Solutions"
  shows cond_A: "cond_A x y"
    and cond_B: "(x, y) \<notin> Special_Solutions \<Longrightarrow> cond_B x"
    and "(x, y) \<notin> Special_Solutions \<Longrightarrow> boundr x y"
    and cond_D: "cond_D x y"
    and subdprodr: "(x, y) \<notin> Special_Solutions \<Longrightarrow> subdprodr y"
    and subdprodl: "subdprodl x y"
proof -
  have sol: "a \<bullet> x = b \<bullet> y" and ln: "m = length x \<and> n = length y"
    using min by (auto simp: Minimal_Solutions_def in_Solutions_iff)
  then have "\<forall>i<m. x ! i \<le> maxne0 y b"
    by (metis min max_coeff_bound_right nth_mem)
  then show "cond_A x y"
    using min and le_less_trans by (auto simp: cond_A_def max_coeff_bound)
  show "(x, y) \<notin> Special_Solutions \<Longrightarrow> cond_B x"
  proof (unfold cond_B_def, intro allI impI)
    fix k assume non_spec: "(x, y) \<notin> Special_Solutions" and k: "k \<le> m"
    from k have "take k a \<bullet> take k x \<le> a \<bullet> x"
      using dotprod_le_take ln by blast
    also have "... = b \<bullet> y" by fact
    also have map_b_dot_p: "... \<le> b \<bullet> map (max_y x) [0..<n]" (is "_ \<le> _ b \<bullet> ?nt")
      using non_spec and less_eq_def and ln and boundr and min
      by (fastforce intro!: dotprod_le_right simp: boundr_def)
    also have "... \<le> b \<bullet> map (max_y (take k x)) [0..<n]" (is "_ \<le> _ \<bullet> ?t")
    proof -
      have "\<forall>j<n. ?nt!j \<le> ?t!j"
        using min and ln and max_y_le_take and k by auto
      then have "?nt \<le>\<^sub>v ?t"
        using less_eq_def by auto
      then show ?thesis
        by (simp add:  dotprod_le_right)
    qed
    finally show "take k a \<bullet> take k x \<le> b \<bullet> map (max_y (take k x)) [0..<n]"
      by (auto simp: cond_B_def)
  qed

  show "(x, y) \<notin> Special_Solutions \<Longrightarrow> subdprodr y"
  proof (unfold subdprodr_def, intro allI impI)
    fix l assume non_spec: "(x, y) \<notin> Special_Solutions" and l: "l \<le> n"
    from l have "take l b \<bullet> take l y \<le> b \<bullet> y"
      using dotprod_le_take ln by blast
    also have "... = a \<bullet> x" by (simp add: sol)
    also have map_b_dot_p: "... \<le> a \<bullet> map (max_x y) [0..<m]" (is "_ \<le> _ a \<bullet> ?nt")
      using non_spec and less_eq_def and ln and boundl and min
      by (fastforce intro!: dotprod_le_right simp: boundl_def)
    also have "... \<le> a \<bullet> map (max_x (take l y)) [0..<m]" (is "_ \<le> _ \<bullet> ?t")
    proof -
      have "\<forall>i<m. ?nt ! i \<le> ?t ! i"
        using min and ln and max_x_le_take and l by auto
      then have "?nt \<le>\<^sub>v ?t"
        using less_eq_def by auto
      then show ?thesis
        by (simp add:  dotprod_le_right)
    qed
    finally show "take l b \<bullet> take l y \<le> a \<bullet> map (max_x (take l y)) [0..<m]"
      by (auto simp: cond_B_def)
  qed

  show "(x, y) \<notin> Special_Solutions \<Longrightarrow> boundr x y"
    using boundr [of x y] and min by blast

  show "cond_D x y"
    using ln and dotprod_le_take and sol by (auto simp: cond_D_def)

  show "subdprodl x y"
    using ln and dotprod_le_take and sol by (force simp: subdprodl_def)
qed

lemma le_imp_Ej_subset:
  assumes "u \<le>\<^sub>v x"
  shows "Ej j u \<subseteq> Ej j x"
  using assms and le_trans by (force simp: Ej_def less_eq_def dij_def eij_def)

lemma le_imp_max_y_ge:
  assumes "u \<le>\<^sub>v x"
    and "length x \<le> m"
  shows "max_y u j \<ge> max_y x j"
  using assms and le_imp_Ej_subset and Min_Ej_le [of j, OF _ _ assms(2)]
  by (metis Min.subset_imp Min_in emptyE finite_Ej max_y_def order_refl subsetCE)

lemma le_imp_Di_subset:
  assumes "v \<le>\<^sub>v y"
  shows "Di i v \<subseteq> Di i y"
  using assms and le_trans by (force simp: Di_def less_eq_def dij_def eij_def)

lemma le_imp_max_x_ge:
  assumes "v \<le>\<^sub>v y"
    and "length y \<le> n"
  shows "max_x v i \<ge> max_x y i"
  using assms and le_imp_Di_subset and Min_Di_le [of i, OF _ _ assms(2)]
  by (metis Min.subset_imp Min_in emptyE finite_Di max_x_def order_refl subsetCE)

end

end
