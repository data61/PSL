(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Type-Class-Multivariate Polynomials in Ordered Terms\<close>

theory MPoly_Type_Class_Ordered
  imports MPoly_Type_Class
begin

class the_min = linorder +
  fixes the_min::'a
  assumes the_min_min: "the_min \<le> x"

text \<open>Type class @{class the_min} guarantees that a least element exists. Instances of @{class the_min}
  should provide @{emph \<open>computable\<close>} definitions of that element.\<close>

instantiation nat :: the_min
begin
  definition "the_min_nat = (0::nat)"
  instance by (standard, simp add: the_min_nat_def)
end

instantiation unit :: the_min
begin
  definition "the_min_unit = ()"
  instance by (standard, simp add: the_min_unit_def)
end

locale ordered_term =
    term_powerprod pair_of_term term_of_pair +
    ordered_powerprod ord ord_strict +
    ord_term_lin: linorder ord_term ord_term_strict
      for pair_of_term::"'t \<Rightarrow> ('a::comm_powerprod \<times> 'k::{the_min,wellorder})"
      and term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
      and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
      and ord_strict (infixl "\<prec>" 50)
      and ord_term::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<preceq>\<^sub>t" 50)
      and ord_term_strict::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<prec>\<^sub>t" 50) +
		assumes splus_mono: "v \<preceq>\<^sub>t w \<Longrightarrow> t \<oplus> v \<preceq>\<^sub>t t \<oplus> w"
    assumes ord_termI: "pp_of_term v \<preceq> pp_of_term w \<Longrightarrow> component_of_term v \<le> component_of_term w \<Longrightarrow> v \<preceq>\<^sub>t w"
begin

abbreviation ord_term_conv (infixl "\<succeq>\<^sub>t" 50) where "ord_term_conv \<equiv> (\<preceq>\<^sub>t)\<inverse>\<inverse>"
abbreviation ord_term_strict_conv (infixl "\<succ>\<^sub>t" 50) where "ord_term_strict_conv \<equiv> (\<prec>\<^sub>t)\<inverse>\<inverse>"

text \<open>The definition of @{locale ordered_term} only covers TOP and POT orderings. 
  These two types of orderings are the only interesting ones.\<close>

definition "min_term \<equiv> term_of_pair (0, the_min)"

lemma min_term_min: "min_term \<preceq>\<^sub>t v"
proof (rule ord_termI)
  show "pp_of_term min_term \<preceq> pp_of_term v" by (simp add: min_term_def zero_min term_simps)
next
  show "component_of_term min_term \<le> component_of_term v" by (simp add: min_term_def the_min_min term_simps)
qed

lemma splus_mono_strict:
  assumes "v \<prec>\<^sub>t w"
  shows "t \<oplus> v \<prec>\<^sub>t t \<oplus> w"
proof -
  from assms have "v \<preceq>\<^sub>t w" and "v \<noteq> w" by simp_all
  from this(1) have "t \<oplus> v \<preceq>\<^sub>t t \<oplus> w" by (rule splus_mono)
  moreover from \<open>v \<noteq> w\<close> have "t \<oplus> v \<noteq> t \<oplus> w" by (simp add: term_simps)
  ultimately show ?thesis using ord_term_lin.antisym_conv1 by blast
qed

lemma splus_mono_left:
  assumes "s \<preceq> t"
  shows "s \<oplus> v \<preceq>\<^sub>t t \<oplus> v"
proof (rule ord_termI, simp_all add: term_simps)
  from assms show "s + pp_of_term v \<preceq> t + pp_of_term v" by (rule plus_monotone)
qed

lemma splus_mono_strict_left:
  assumes "s \<prec> t"
  shows "s \<oplus> v \<prec>\<^sub>t t \<oplus> v"
proof -
  from assms have "s \<preceq> t" and "s \<noteq> t" by simp_all
  from this(1) have "s \<oplus> v \<preceq>\<^sub>t t \<oplus> v" by (rule splus_mono_left)
  moreover from \<open>s \<noteq> t\<close> have "s \<oplus> v \<noteq> t \<oplus> v" by (simp add: term_simps)
  ultimately show ?thesis using ord_term_lin.antisym_conv1 by blast
qed

lemma ord_term_canc:
  assumes "t \<oplus> v \<preceq>\<^sub>t t \<oplus> w"
  shows "v \<preceq>\<^sub>t w"
proof (rule ccontr)
  assume "\<not> v \<preceq>\<^sub>t w"
  hence "w \<prec>\<^sub>t v" by simp
  hence "t \<oplus> w \<prec>\<^sub>t t \<oplus> v" by (rule splus_mono_strict)
  with assms show False by simp
qed

lemma ord_term_strict_canc:
  assumes "t \<oplus> v \<prec>\<^sub>t t \<oplus> w"
  shows "v \<prec>\<^sub>t w"
proof (rule ccontr)
  assume "\<not> v \<prec>\<^sub>t w"
  hence "w \<preceq>\<^sub>t v" by simp
  hence "t \<oplus> w \<preceq>\<^sub>t t \<oplus> v" by (rule splus_mono)
  with assms show False by simp
qed

lemma ord_term_canc_left:
  assumes "t \<oplus> v \<preceq>\<^sub>t s \<oplus> v"
  shows "t \<preceq> s"
proof (rule ccontr)
  assume "\<not> t \<preceq> s"
  hence "s \<prec> t" by simp
  hence "s \<oplus> v \<prec>\<^sub>t t \<oplus> v" by (rule splus_mono_strict_left)
  with assms show False by simp
qed

lemma ord_term_strict_canc_left:
  assumes "t \<oplus> v \<prec>\<^sub>t s \<oplus> v"
  shows "t \<prec> s"
proof (rule ccontr)
  assume "\<not> t \<prec> s"
  hence "s \<preceq> t" by simp
  hence "s \<oplus> v \<preceq>\<^sub>t t \<oplus> v" by (rule splus_mono_left)
  with assms show False by simp
qed

lemma ord_adds_term:
  assumes "u adds\<^sub>t v"
  shows "u \<preceq>\<^sub>t v"
proof -
  from assms have *: "component_of_term u \<le> component_of_term v" and "pp_of_term u adds pp_of_term v"
    by (simp_all add: adds_term_def)
  from this(2) have "pp_of_term u \<preceq> pp_of_term v" by (rule ord_adds)
  from this * show ?thesis by (rule ord_termI)
qed

end

subsection \<open>Interpretations\<close>

context ordered_powerprod
begin

subsubsection \<open>Unit\<close>

sublocale punit: ordered_term to_pair_unit fst "(\<preceq>)" "(\<prec>)" "(\<preceq>)" "(\<prec>)"
  apply standard
  subgoal by (simp, fact plus_monotone_left)
  subgoal by (simp only: punit_pp_of_term punit_component_of_term)
  done

lemma punit_min_term [simp]: "punit.min_term = 0"
  by (simp add: punit.min_term_def)

end

subsection \<open>Definitions\<close>

context ordered_term
begin

definition higher :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "higher p t = except p {s. s \<preceq>\<^sub>t t}"

definition lower :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "lower p t = except p {s. t \<preceq>\<^sub>t s}"

definition lt :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 't"
  where "lt p = (if p = 0 then min_term else ord_term_lin.Max (keys p))"

abbreviation "lp p \<equiv> pp_of_term (lt p)"

definition lc :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b"
  where "lc p = lookup p (lt p)"

definition tt :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 't"
  where "tt p = (if p = 0 then min_term else ord_term_lin.Min (keys p))"

abbreviation "tp p \<equiv> pp_of_term (tt p)"

definition tc :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b"
  where "tc p \<equiv> lookup p (tt p)"

definition tail :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "tail p \<equiv> lower p (lt p)"

subsection \<open>Leading Term and Leading Coefficient: @{const lt} and @{const lc}\<close>

lemma lt_zero [simp]: "lt 0 = min_term"
  by (simp add: lt_def)

lemma lc_zero [simp]: "lc 0 = 0"
  by (simp add: lc_def)

lemma lt_uminus [simp]: "lt (- p) = lt p"
  by (simp add: lt_def keys_uminus)

lemma lc_uminus [simp]: "lc (- p) = - lc p"
  by (simp add: lc_def)

lemma lt_alt:
  assumes "p \<noteq> 0"
  shows "lt p = ord_term_lin.Max (keys p)"
  using assms unfolding lt_def by simp

lemma lt_max:
  assumes "lookup p v \<noteq> 0"
  shows "v \<preceq>\<^sub>t lt p"
proof -
  from assms have t_in: "v \<in> keys p" by (simp add: in_keys_iff)
  hence "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" using keys_zero by blast
  from lt_alt[OF this] ord_term_lin.Max_ge[OF finite_keys t_in] show ?thesis by simp
qed

lemma lt_eqI:
  assumes "lookup p v \<noteq> 0" and "\<And>u. lookup p u \<noteq> 0 \<Longrightarrow> u \<preceq>\<^sub>t v"
  shows "lt p = v"
proof -
  from assms(1) have "v \<in> keys p" by (simp add: in_keys_iff)
  hence "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0"
    using keys_zero by blast
  have "u \<preceq>\<^sub>t v" if "u \<in> keys p" for u
  proof -
    from that have "lookup p u \<noteq> 0" by (simp add: in_keys_iff)
    thus "u \<preceq>\<^sub>t v" by (rule assms(2))
  qed
  from lt_alt[OF \<open>p \<noteq> 0\<close>] ord_term_lin.Max_eqI[OF finite_keys this \<open>v \<in> keys p\<close>] show ?thesis by simp
qed

lemma lt_less:
  assumes "p \<noteq> 0" and "\<And>u. v \<preceq>\<^sub>t u \<Longrightarrow> lookup p u = 0"
  shows "lt p \<prec>\<^sub>t v"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}"
    by simp
  have "\<forall>u\<in>keys p. u \<prec>\<^sub>t v"
  proof
    fix u::'t
    assume "u \<in> keys p"
    hence "lookup p u \<noteq> 0" by (simp add: in_keys_iff)
    hence "\<not> v \<preceq>\<^sub>t u" using assms(2)[of u] by auto
    thus "u \<prec>\<^sub>t v" by simp
  qed
  with lt_alt[OF assms(1)] ord_term_lin.Max_less_iff[OF finite_keys \<open>keys p \<noteq> {}\<close>] show ?thesis by simp
qed

lemma lt_le:
  assumes "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = 0"
  shows "lt p \<preceq>\<^sub>t v"
proof (cases "p = 0")
  case True
  show ?thesis by (simp add: True min_term_min)
next
  case False
  hence "keys p \<noteq> {}" by simp
  have "\<forall>u\<in>keys p. u \<preceq>\<^sub>t v"
  proof
    fix u::'t
    assume "u \<in> keys p"
    hence "lookup p u \<noteq> 0" unfolding keys_def by simp
    hence "\<not> v \<prec>\<^sub>t u" using assms[of u] by auto
    thus "u \<preceq>\<^sub>t v" by simp
  qed
  with lt_alt[OF False] ord_term_lin.Max_le_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed

lemma lt_gr:
  assumes "lookup p s \<noteq> 0" and "t \<prec>\<^sub>t s"
  shows "t \<prec>\<^sub>t lt p"
  using assms lt_max ord_term_lin.order.strict_trans2 by blast

lemma lc_not_0:
  assumes "p \<noteq> 0"
  shows "lc p \<noteq> 0"
proof -
  from keys_zero assms have "keys p \<noteq> {}" by auto
  from lt_alt[OF assms] ord_term_lin.Max_in[OF finite_keys this] show ?thesis by (simp add: in_keys_iff lc_def)
qed

lemma lc_eq_zero_iff: "lc p = 0 \<longleftrightarrow> p = 0"
  using lc_not_0 lc_zero by blast

lemma lt_in_keys:
  assumes "p \<noteq> 0"
  shows "lt p \<in> (keys p)"
  by (metis assms in_keys_iff lc_def lc_not_0)

lemma lt_monomial:
  assumes "c \<noteq> 0"
  shows "lt (monomial c t) = t"
  by (metis assms lookup_single_eq lookup_single_not_eq lt_eqI ord_term_lin.eq_iff)

lemma lc_monomial [simp]: "lc (monomial c t) = c"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  thus ?thesis by (simp add: lc_def lt_monomial)
qed
   
lemma lt_le_iff: "lt p \<preceq>\<^sub>t v \<longleftrightarrow> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = 0)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix u
    note \<open>lt p \<preceq>\<^sub>t v\<close>
    also assume "v \<prec>\<^sub>t u"
    finally have "lt p \<prec>\<^sub>t u" .
    hence "\<not> u \<preceq>\<^sub>t lt p" by simp
    with lt_max[of p u] show "lookup p u = 0" by blast
  qed
next
  assume ?R
  thus ?L using lt_le by auto
qed

lemma lt_plus_eqI:
  assumes "lt p \<prec>\<^sub>t lt q"
  shows "lt (p + q) = lt q"
proof (cases "q = 0")
  case True
  with assms have "lt p \<prec>\<^sub>t min_term" by (simp add: lt_def)
  with min_term_min[of "lt p"] show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro lt_eqI)
    from lt_gr[of p "lt q" "lt p"] assms have "lookup p (lt q) = 0" by blast
    with lookup_add[of p q "lt q"] lc_not_0[OF False] show "lookup (p + q) (lt q) \<noteq> 0"
      unfolding lc_def by simp
  next
    fix u
    assume "lookup (p + q) u \<noteq> 0"
    show "u \<preceq>\<^sub>t lt q"
    proof (rule ccontr)
      assume "\<not> u \<preceq>\<^sub>t lt q"
      hence qs: "lt q \<prec>\<^sub>t u" by simp
      with assms have "lt p \<prec>\<^sub>t u" by simp
      with lt_gr[of p u "lt p"] have "lookup p u = 0" by blast
      moreover from qs lt_gr[of q u "lt q"] have "lookup q u = 0" by blast
      ultimately show False using \<open>lookup (p + q) u \<noteq> 0\<close> lookup_add[of p q u] by auto
    qed
  qed
qed

lemma lt_plus_eqI_2:
  assumes "lt q \<prec>\<^sub>t lt p"
  shows "lt (p + q) = lt p"
proof (cases "p = 0")
  case True
  with assms have "lt q \<prec>\<^sub>t min_term" by (simp add: lt_def)
  with min_term_min[of "lt q"] show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro lt_eqI)
    from lt_gr[of q "lt p" "lt q"] assms have "lookup q (lt p) = 0" by blast
    with lookup_add[of p q "lt p"] lc_not_0[OF False] show "lookup (p + q) (lt p) \<noteq> 0"
      unfolding lc_def by simp
  next
    fix u
    assume "lookup (p + q) u \<noteq> 0"
    show "u \<preceq>\<^sub>t lt p"
    proof (rule ccontr)
      assume "\<not> u \<preceq>\<^sub>t lt p"
      hence ps: "lt p \<prec>\<^sub>t u" by simp
      with assms have "lt q \<prec>\<^sub>t u" by simp
      with lt_gr[of q u "lt q"] have "lookup q u = 0" by blast
      also from ps lt_gr[of p u "lt p"] have "lookup p u = 0" by blast
      ultimately show False using \<open>lookup (p + q) u \<noteq> 0\<close> lookup_add[of p q u] by auto
    qed
  qed
qed

lemma lt_plus_eqI_3:
  assumes "lt q = lt p" and "lc p + lc q \<noteq> 0"
  shows "lt (p + q) = lt (p::'t \<Rightarrow>\<^sub>0 'b::monoid_add)"
proof (rule lt_eqI)
  from assms(2) show "lookup (p + q) (lt p) \<noteq> 0" by (simp add: lookup_add lc_def assms(1))
next
  fix u
  assume "lookup (p + q) u \<noteq> 0"
  hence "lookup p u + lookup q u \<noteq> 0" by (simp add: lookup_add)
  hence "lookup p u \<noteq> 0 \<or> lookup q u \<noteq> 0" by auto
  thus "u \<preceq>\<^sub>t lt p"
  proof
    assume "lookup p u \<noteq> 0"
    thus ?thesis by (rule lt_max)
  next
    assume "lookup q u \<noteq> 0"
    hence "u \<preceq>\<^sub>t lt q" by (rule lt_max)
    thus ?thesis by (simp only: assms(1))
  qed
qed

lemma lt_plus_lessE:
  assumes "lt p \<prec>\<^sub>t lt (p + q)"
  shows "lt p \<prec>\<^sub>t lt q"
proof (rule ccontr)
  assume "\<not> lt p \<prec>\<^sub>t lt q"
  hence "lt p = lt q \<or> lt q \<prec>\<^sub>t lt p" by auto
  thus False
  proof
    assume lt_eq: "lt p = lt q"
    have "lt (p + q) \<preceq>\<^sub>t lt p"
    proof (rule lt_le)
      fix u
      assume "lt p \<prec>\<^sub>t u"
      with lt_gr[of p u "lt p"] have "lookup p u = 0" by blast
      from \<open>lt p \<prec>\<^sub>t u\<close> have "lt q \<prec>\<^sub>t u" using lt_eq by simp
      with lt_gr[of q u "lt q"] have "lookup q u = 0" by blast
      with \<open>lookup p u = 0\<close> show "lookup (p + q) u = 0" by (simp add: lookup_add)
    qed
    with assms show False by simp
  next
    assume "lt q \<prec>\<^sub>t lt p"
    from lt_plus_eqI_2[OF this] assms show False by simp
  qed
qed

lemma lt_plus_lessE_2:
  assumes "lt q \<prec>\<^sub>t lt (p + q)"
  shows "lt q \<prec>\<^sub>t lt p"
proof (rule ccontr)
  assume "\<not> lt q \<prec>\<^sub>t lt p"
  hence "lt q = lt p \<or> lt p \<prec>\<^sub>t lt q" by auto
  thus False
  proof
    assume lt_eq: "lt q = lt p"
    have "lt (p + q) \<preceq>\<^sub>t lt q"
    proof (rule lt_le)
      fix u
      assume "lt q \<prec>\<^sub>t u"
      with lt_gr[of q u "lt q"] have "lookup q u = 0" by blast
      from \<open>lt q \<prec>\<^sub>t u\<close> have "lt p \<prec>\<^sub>t u" using lt_eq by simp
      with lt_gr[of p u "lt p"] have "lookup p u = 0" by blast
      with \<open>lookup q u = 0\<close> show "lookup (p + q) u = 0" by (simp add: lookup_add)
    qed
    with assms show False by simp
  next
    assume "lt p \<prec>\<^sub>t lt q"
    from lt_plus_eqI[OF this] assms show False by simp
  qed
qed

lemma lt_plus_lessI':
  fixes p q :: "'t \<Rightarrow>\<^sub>0 'b::monoid_add"
  assumes "p + q \<noteq> 0" and lt_eq: "lt q = lt p" and lc_eq: "lc p + lc q = 0"
  shows "lt (p + q) \<prec>\<^sub>t lt p"
proof (rule ccontr)
  assume "\<not> lt (p + q) \<prec>\<^sub>t lt p"
  hence "lt (p + q) = lt p \<or> lt p \<prec>\<^sub>t lt (p + q)" by auto
  thus False
  proof
    assume "lt (p + q) = lt p"
    have "lookup (p + q) (lt p) = (lookup p (lt p)) + (lookup q (lt q))" unfolding lt_eq lookup_add ..
    also have "... = lc p + lc q" unfolding lc_def ..
    also have "... = 0" unfolding lc_eq by simp
    finally have "lookup (p + q) (lt p) = 0" .
    hence "lt (p + q) \<noteq> lt p" using lc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding lc_def by auto
    with \<open>lt (p + q) = lt p\<close> show False by simp
  next
    assume "lt p \<prec>\<^sub>t lt (p + q)"
    have "lt p \<prec>\<^sub>t lt q" by (rule lt_plus_lessE, fact+)
    hence "lt p \<noteq> lt q" by simp
    with lt_eq show False by simp
  qed
qed

corollary lt_plus_lessI:
  fixes p q :: "'t \<Rightarrow>\<^sub>0 'b::group_add"
  assumes "p + q \<noteq> 0" and "lt q = lt p" and "lc q = - lc p"
  shows "lt (p + q) \<prec>\<^sub>t lt p"
  using assms(1, 2)
proof (rule lt_plus_lessI')
  from assms(3) show "lc p + lc q = 0" by simp
qed

lemma lt_plus_distinct_eq_max:
  assumes "lt p \<noteq> lt q"
  shows "lt (p + q) = ord_term_lin.max (lt p) (lt q)"
proof (rule ord_term_lin.linorder_cases)
  assume a: "lt p \<prec>\<^sub>t lt q"
  hence "lt (p + q) = lt q" by (rule lt_plus_eqI)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb2)
  finally show ?thesis .
next
  assume a: "lt q \<prec>\<^sub>t lt p"
  hence "lt (p + q) = lt p" by (rule lt_plus_eqI_2)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb1)
  finally show ?thesis .
next
  assume "lt p = lt q"
  with assms show ?thesis ..
qed

lemma lt_plus_le_max: "lt (p + q) \<preceq>\<^sub>t ord_term_lin.max (lt p) (lt q)"
proof (cases "lt p = lt q")
  case True
  show ?thesis
  proof (rule lt_le)
    fix u
    assume "ord_term_lin.max (lt p) (lt q) \<prec>\<^sub>t u"
    hence "lt p \<prec>\<^sub>t u" and "lt q \<prec>\<^sub>t u" by simp_all
    hence "lookup p u = 0" and "lookup q u = 0" using lt_max ord_term_lin.leD by blast+
    thus "lookup (p + q) u = 0" by (simp add: lookup_add)
  qed
next
  case False
  hence "lt (p + q) = ord_term_lin.max (lt p) (lt q)" by (rule lt_plus_distinct_eq_max)
  thus ?thesis by simp
qed

lemma lt_minus_eqI: "lt p \<prec>\<^sub>t lt q \<Longrightarrow> lt (p - q) = lt q" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis lt_plus_eqI_2 lt_uminus uminus_add_conv_diff)

lemma lt_minus_eqI_2: "lt q \<prec>\<^sub>t lt p \<Longrightarrow> lt (p - q) = lt p" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis lt_minus_eqI lt_uminus minus_diff_eq)

lemma lt_minus_eqI_3:
  assumes "lt q = lt p" and "lc q \<noteq> lc p"
  shows "lt (p - q) = lt (p::'t \<Rightarrow>\<^sub>0 'b::ab_group_add)"
proof (rule lt_eqI)
  from assms(2) show "lookup (p - q) (lt p) \<noteq> 0" by (simp add: lookup_minus lc_def assms(1))
next
  fix u
  assume "lookup (p - q) u \<noteq> 0"
  hence "lookup p u \<noteq> lookup q u" by (simp add: lookup_minus)
  hence "lookup p u \<noteq> 0 \<or> lookup q u \<noteq> 0" by auto
  thus "u \<preceq>\<^sub>t lt p"
  proof
    assume "lookup p u \<noteq> 0"
    thus ?thesis by (rule lt_max)
  next
    assume "lookup q u \<noteq> 0"
    hence "u \<preceq>\<^sub>t lt q" by (rule lt_max)
    thus ?thesis by (simp only: assms(1))
  qed
qed

lemma lt_minus_distinct_eq_max:
  assumes "lt p \<noteq> lt (q::'t \<Rightarrow>\<^sub>0 'b::ab_group_add)"
  shows "lt (p - q) = ord_term_lin.max (lt p) (lt q)"
proof (rule ord_term_lin.linorder_cases)
  assume a: "lt p \<prec>\<^sub>t lt q"
  hence "lt (p - q) = lt q" by (rule lt_minus_eqI)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb2)
  finally show ?thesis .
next
  assume a: "lt q \<prec>\<^sub>t lt p"
  hence "lt (p - q) = lt p" by (rule lt_minus_eqI_2)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb1)
  finally show ?thesis .
next
  assume "lt p = lt q"
  with assms show ?thesis ..
qed

lemma lt_minus_lessE: "lt p \<prec>\<^sub>t lt (p - q) \<Longrightarrow> lt p \<prec>\<^sub>t lt q" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  using lt_minus_eqI_2 by fastforce

lemma lt_minus_lessE_2: "lt q \<prec>\<^sub>t lt (p - q) \<Longrightarrow> lt q \<prec>\<^sub>t lt p" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  using lt_plus_eqI_2 by fastforce

lemma lt_minus_lessI: "p - q \<noteq> 0 \<Longrightarrow> lt q = lt p \<Longrightarrow> lc q = lc p \<Longrightarrow> lt (p - q) \<prec>\<^sub>t lt p"
  for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis (no_types, hide_lams) diff_diff_eq2 diff_self group_eq_aux lc_def lc_not_0 lookup_minus
      lt_minus_eqI ord_term_lin.antisym_conv3)
    
lemma lt_max_keys:
  assumes "v \<in> keys p"
  shows "v \<preceq>\<^sub>t lt p"
proof (rule lt_max)
  from assms show "lookup p v \<noteq> 0" by (simp add: in_keys_iff)
qed

lemma lt_eqI_keys:
  assumes "v \<in> keys p" and a2: "\<And>u. u \<in> keys p \<Longrightarrow> u \<preceq>\<^sub>t v"
  shows "lt p = v"
  by (rule lt_eqI, simp_all only: in_keys_iff[symmetric], fact+)
    
lemma lt_gr_keys:
  assumes "u \<in> keys p" and "v \<prec>\<^sub>t u"
  shows "v \<prec>\<^sub>t lt p"
proof (rule lt_gr)
  from assms(1) show "lookup p u \<noteq> 0" by (simp add: in_keys_iff)
qed fact

lemma lt_plus_eq_maxI:
  assumes "lt p = lt q \<Longrightarrow> lc p + lc q \<noteq> 0"
  shows "lt (p + q) = ord_term_lin.max (lt p) (lt q)"
proof (cases "lt p = lt q")
  case True
  show ?thesis
  proof (rule lt_eqI_keys)
    from True have "lc p + lc q \<noteq> 0" by (rule assms)
    thus "ord_term_lin.max (lt p) (lt q) \<in> keys (p + q)"
      by (simp add: in_keys_iff lc_def lookup_add True)
  next
    fix u
    assume "u \<in> keys (p + q)"
    hence "u \<preceq>\<^sub>t lt (p + q)" by (rule lt_max_keys)
    also have "... \<preceq>\<^sub>t ord_term_lin.max (lt p) (lt q)" by (fact lt_plus_le_max)
    finally show "u \<preceq>\<^sub>t ord_term_lin.max (lt p) (lt q)" .
  qed
next
  case False
  thus ?thesis by (rule lt_plus_distinct_eq_max)
qed

lemma lt_monom_mult:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)" and "p \<noteq> 0"
  shows "lt (monom_mult c t p) = t \<oplus> lt p"
proof (intro lt_eqI)
  from assms(1) show "lookup (monom_mult c t p) (t \<oplus> lt p) \<noteq> 0"
  proof (simp add: lookup_monom_mult_plus)
    show "lookup p (lt p) \<noteq> 0"
      using assms(2) lt_in_keys by auto
  qed
next
  fix u::'t
  assume "lookup (monom_mult c t p) u \<noteq> 0"
  hence "u \<in> keys (monom_mult c t p)" by (simp add: in_keys_iff)
  also have "... \<subseteq> (\<oplus>) t ` keys p" by (fact keys_monom_mult_subset)
  finally obtain v where "v \<in> keys p" and "u = t \<oplus> v" ..
  show "u \<preceq>\<^sub>t t \<oplus> lt p" unfolding \<open>u = t \<oplus> v\<close>
  proof (rule splus_mono)
    from \<open>v \<in> keys p\<close> show "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
  qed
qed

lemma lt_monom_mult_zero:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "lt (monom_mult c 0 p) = lt p"
proof (cases "p = 0")
  case True
  show ?thesis by (simp add: True)
next
  case False
  with assms show ?thesis by (simp add: lt_monom_mult term_simps)
qed

corollary lt_map_scale: "c \<noteq> (0::'b::semiring_no_zero_divisors) \<Longrightarrow> lt (c \<cdot> p) = lt p"
  by (simp add: map_scale_eq_monom_mult lt_monom_mult_zero)

lemma lc_monom_mult [simp]: "lc (monom_mult c t p) = (c::'b::semiring_no_zero_divisors) * lc p"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with \<open>c \<noteq> 0\<close> show ?thesis by (simp add: lc_def lt_monom_mult lookup_monom_mult_plus)
  qed
qed

corollary lc_map_scale [simp]: "lc (c \<cdot> p) = (c::'b::semiring_no_zero_divisors) * lc p"
  by (simp add: map_scale_eq_monom_mult)

lemma (in ordered_term) lt_mult_scalar_monomial_right:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)" and "p \<noteq> 0"
  shows "lt (p \<odot> monomial c v) = punit.lt p \<oplus> v"
proof (intro lt_eqI)
  from assms(1) show "lookup (p \<odot> monomial c v) (punit.lt p \<oplus> v) \<noteq> 0"
  proof (simp add: lookup_mult_scalar_monomial_right_plus)
    from assms(2) show "lookup p (punit.lt p) \<noteq> 0"
      using in_keys_iff punit.lt_in_keys by fastforce
  qed
next
  fix u::'t
  assume "lookup (p \<odot> monomial c v) u \<noteq> 0"
  hence "u \<in> keys (p \<odot> monomial c v)" by (simp add: in_keys_iff)
  also have "... \<subseteq> (\<lambda>t. t \<oplus> v) ` keys p" by (fact keys_mult_scalar_monomial_right_subset)
  finally obtain t where "t \<in> keys p" and "u = t \<oplus> v" ..
  show "u \<preceq>\<^sub>t punit.lt p \<oplus> v" unfolding \<open>u = t \<oplus> v\<close>
  proof (rule splus_mono_left)
    from \<open>t \<in> keys p\<close> show "t \<preceq> punit.lt p" by (rule punit.lt_max_keys)
  qed
qed

lemma lc_mult_scalar_monomial_right:
  "lc (p \<odot> monomial c v) = punit.lc p * (c::'b::semiring_no_zero_divisors)"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with \<open>c \<noteq> 0\<close> show ?thesis
      by (simp add: punit.lc_def lc_def lt_mult_scalar_monomial_right lookup_mult_scalar_monomial_right_plus)
  qed
qed

lemma lookup_monom_mult_eq_zero:
  assumes "s \<oplus> lt p \<prec>\<^sub>t v"
  shows "lookup (monom_mult (c::'b::semiring_no_zero_divisors) s p) v = 0"
  by (metis assms aux lt_gr lt_monom_mult monom_mult_zero_left monom_mult_zero_right
      ord_term_lin.order.strict_implies_not_eq)

lemma in_keys_monom_mult_le:
  assumes "v \<in> keys (monom_mult c t p)"
  shows "v \<preceq>\<^sub>t t \<oplus> lt p"
proof -
  from keys_monom_mult_subset assms have "v \<in> (\<oplus>) t ` (keys p)" ..
  then obtain u where "u \<in> keys p" and "v = t \<oplus> u" ..
  from \<open>u \<in> keys p\<close> have "u \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
  thus "v \<preceq>\<^sub>t t \<oplus> lt p" unfolding \<open>v = t \<oplus> u\<close> by (rule splus_mono)
qed

lemma lt_monom_mult_le: "lt (monom_mult c t p) \<preceq>\<^sub>t t \<oplus> lt p"
  by (metis aux in_keys_monom_mult_le lt_in_keys lt_le_iff)

lemma monom_mult_inj_2:
  assumes "monom_mult c t1 p = monom_mult c t2 p"
    and "c \<noteq> 0" and "(p::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors) \<noteq> 0"
  shows "t1 = t2"
proof -
  from assms(1) have "lt (monom_mult c t1 p) = lt (monom_mult c t2 p)" by simp
  with \<open>c \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "t1 \<oplus> lt p = t2 \<oplus> lt p" by (simp add: lt_monom_mult)
  thus ?thesis by (simp add: term_simps)
qed

subsection \<open>Trailing Term and Trailing Coefficient: @{const tt} and @{const tc}\<close>

lemma tt_zero [simp]: "tt 0 = min_term"
  by (simp add: tt_def)

lemma tc_zero [simp]: "tc 0 = 0"
  by (simp add: tc_def)

lemma tt_alt:
  assumes "p \<noteq> 0"
  shows "tt p = ord_term_lin.Min (keys p)"
  using assms unfolding tt_def by simp

lemma tt_min_keys:
  assumes "v \<in> keys p"
  shows "tt p \<preceq>\<^sub>t v"
proof -
  from assms have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from tt_alt[OF this] ord_term_lin.Min_le[OF finite_keys assms] show ?thesis by simp
qed

lemma tt_min:
  assumes "lookup p v \<noteq> 0"
  shows "tt p \<preceq>\<^sub>t v"
proof -
  from assms have "v \<in> keys p" unfolding keys_def by simp
  thus ?thesis by (rule tt_min_keys)
qed
  
lemma tt_in_keys:
  assumes "p \<noteq> 0"
  shows "tt p \<in> keys p"
  unfolding tt_alt[OF assms]
  by (rule ord_term_lin.Min_in, fact finite_keys, simp add: assms)

lemma tt_eqI:
  assumes "v \<in> keys p" and "\<And>u. u \<in> keys p \<Longrightarrow> v \<preceq>\<^sub>t u"
  shows "tt p = v"
proof -
  from assms(1) have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from assms(1) have "tt p \<preceq>\<^sub>t v" by (rule tt_min_keys)
  moreover have "v \<preceq>\<^sub>t tt p" by (rule assms(2), rule tt_in_keys, fact \<open>p \<noteq> 0\<close>)
  ultimately show ?thesis by simp
qed

lemma tt_gr:
  assumes "\<And>u. u \<in> keys p \<Longrightarrow> v \<prec>\<^sub>t u" and "p \<noteq> 0"
  shows "v \<prec>\<^sub>t tt p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" by simp
  show ?thesis by (rule assms(1), rule tt_in_keys, fact \<open>p \<noteq> 0\<close>)
qed

lemma tt_less:
  assumes "u \<in> keys p" and "u \<prec>\<^sub>t v"
  shows "tt p \<prec>\<^sub>t v"
proof -
  from \<open>u \<in> keys p\<close> have "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
  also have "... \<prec>\<^sub>t v" by fact
  finally show "tt p \<prec>\<^sub>t v" .
qed

lemma tt_ge:
  assumes "\<And>u. u \<prec>\<^sub>t v \<Longrightarrow> lookup p u = 0" and "p \<noteq> 0"
  shows "v \<preceq>\<^sub>t tt p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" by simp
  have "\<forall>u\<in>keys p. v \<preceq>\<^sub>t u"
  proof
    fix u::'t
    assume "u \<in> keys p"
    hence "lookup p u \<noteq> 0" unfolding keys_def by simp
    hence "\<not> u \<prec>\<^sub>t v" using assms(1)[of u] by auto
    thus "v \<preceq>\<^sub>t u" by simp
  qed
  with tt_alt[OF \<open>p \<noteq> 0\<close>] ord_term_lin.Min_ge_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed
  
lemma tt_ge_keys:
  assumes "\<And>u. u \<in> keys p \<Longrightarrow> v \<preceq>\<^sub>t u" and "p \<noteq> 0"
  shows "v \<preceq>\<^sub>t tt p"
  by (rule assms(1), rule tt_in_keys, fact)

lemma tt_ge_iff: "v \<preceq>\<^sub>t tt p \<longleftrightarrow> ((p \<noteq> 0 \<or> v = min_term) \<and> (\<forall>u. u \<prec>\<^sub>t v \<longrightarrow> lookup p u = 0))"
  (is "?L \<longleftrightarrow> (?A \<and> ?B)")
proof
  assume ?L
  show "?A \<and> ?B"
  proof (intro conjI allI impI)
    show "p \<noteq> 0 \<or> v = min_term"
    proof (cases "p = 0")
      case True
      show ?thesis
      proof (rule disjI2)
        from \<open>?L\<close> True have "v \<preceq>\<^sub>t min_term" by (simp add: tt_def)
        with min_term_min[of v] show "v = min_term" by simp
      qed
    next
      case False
      thus ?thesis ..
    qed
  next
    fix u
    assume "u \<prec>\<^sub>t v"
    also note \<open>v \<preceq>\<^sub>t tt p\<close>
    finally have "u \<prec>\<^sub>t tt p" .
    hence "\<not> tt p \<preceq>\<^sub>t u" by simp
    with tt_min[of p u] show "lookup p u = 0" by blast
  qed
next
  assume "?A \<and> ?B"
  hence ?A and ?B by simp_all
  show ?L
  proof (cases "p = 0")
    case True
    with \<open>?A\<close> have "v = min_term" by simp
    with True show ?thesis by (simp add: tt_def)
  next
    case False
    from \<open>?B\<close> show ?thesis using tt_ge[OF _ False] by auto
  qed
qed

lemma tc_not_0:
  assumes "p \<noteq> 0"
  shows "tc p \<noteq> 0"
  unfolding tc_def in_keys_iff[symmetric] using assms by (rule tt_in_keys)

lemma tt_monomial:
  assumes "c \<noteq> 0"
  shows "tt (monomial c v) = v"
proof (rule tt_eqI)
  from keys_of_monomial[OF assms, of v] show "v \<in> keys (monomial c v)" by simp
next
  fix u
  assume "u \<in> keys (monomial c v)"
  with keys_of_monomial[OF assms, of v] have "u = v" by simp
  thus "v \<preceq>\<^sub>t u" by simp
qed

lemma tc_monomial [simp]: "tc (monomial c t) = c"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  thus ?thesis by (simp add: tc_def tt_monomial)
qed
  
lemma tt_plus_eqI:
  assumes "p \<noteq> 0" and "tt p \<prec>\<^sub>t tt q"
  shows "tt (p + q) = tt p"
proof (intro tt_eqI)
  from tt_less[of "tt p" q "tt q"] \<open>tt p \<prec>\<^sub>t tt q\<close> have "tt p \<notin> keys q" by blast
  with lookup_add[of p q "tt p"] tc_not_0[OF \<open>p \<noteq> 0\<close>] show "tt p \<in> keys (p + q)"
    unfolding in_keys_iff tc_def by simp
next
  fix u
  assume "u \<in> keys (p + q)"
  show "tt p \<preceq>\<^sub>t u"
  proof (rule ccontr)
    assume "\<not> tt p \<preceq>\<^sub>t u"
    hence sp: "u \<prec>\<^sub>t tt p" by simp
    hence "u \<prec>\<^sub>t tt q" using \<open>tt p \<prec>\<^sub>t tt q\<close> by simp
    with tt_less[of u q "tt q"] have "u \<notin> keys q" by blast
    moreover from sp tt_less[of u p "tt p"] have "u \<notin> keys p" by blast
    ultimately show False using \<open>u \<in> keys (p + q)\<close> Poly_Mapping.keys_add[of p q] by auto
  qed
qed
    
lemma tt_plus_lessE:
  fixes p q
  assumes "p + q \<noteq> 0" and tt: "tt (p + q) \<prec>\<^sub>t tt p"
  shows "tt q \<prec>\<^sub>t tt p"
proof (cases "p = 0")
  case True
  with tt show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> tt q \<prec>\<^sub>t tt p"
    hence "tt p = tt q \<or> tt p \<prec>\<^sub>t tt q" by auto
    thus False
    proof
      assume tt_eq: "tt p = tt q"
      have "tt p \<preceq>\<^sub>t tt (p + q)"
      proof (rule tt_ge_keys)
        fix u
        assume "u \<in> keys (p + q)"
        hence "u \<in> keys p \<union> keys q"
        proof
          show "keys (p + q) \<subseteq> keys p \<union> keys q" by (fact Poly_Mapping.keys_add)
        qed
        thus "tt p \<preceq>\<^sub>t u"
        proof
          assume "u \<in> keys p"
          thus ?thesis by (rule tt_min_keys)
        next
          assume "u \<in> keys q"
          thus ?thesis unfolding tt_eq by (rule tt_min_keys)
        qed
      qed (fact \<open>p + q \<noteq> 0\<close>)
      with tt show False by simp
    next
      assume "tt p \<prec>\<^sub>t tt q"
      from tt_plus_eqI[OF False this] tt show False by (simp add: ac_simps)
    qed
  qed
qed
  
lemma tt_plus_lessI:
  fixes p q :: "_ \<Rightarrow>\<^sub>0 'b::ring"
  assumes "p + q \<noteq> 0" and tt_eq: "tt q = tt p" and tc_eq: "tc q = - tc p"
  shows "tt p \<prec>\<^sub>t tt (p + q)"
proof (rule ccontr)
  assume "\<not> tt p \<prec>\<^sub>t tt (p + q)"
  hence "tt p = tt (p + q) \<or> tt (p + q) \<prec>\<^sub>t tt p" by auto
  thus False
  proof
    assume "tt p = tt (p + q)"
    have "lookup (p + q) (tt p) = (lookup p (tt p)) + (lookup q (tt q))" unfolding tt_eq lookup_add ..
    also have "... = tc p + tc q" unfolding tc_def ..
    also have "... = 0" unfolding tc_eq by simp
    finally have "lookup (p + q) (tt p) = 0" .
    hence "tt (p + q) \<noteq> tt p" using tc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding tc_def by auto
    with \<open>tt p = tt (p + q)\<close> show False by simp
  next
    assume "tt (p + q) \<prec>\<^sub>t tt p"
    have "tt q \<prec>\<^sub>t tt p" by (rule tt_plus_lessE, fact+)
    hence "tt q \<noteq> tt p" by simp
    with tt_eq show False by simp
  qed
qed

lemma tt_uminus [simp]: "tt (- p) = tt p"
  by (simp add: tt_def keys_uminus)

lemma tc_uminus [simp]: "tc (- p) = - tc p"
  by (simp add: tc_def)

lemma tt_monom_mult:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)" and "p \<noteq> 0"
  shows "tt (monom_mult c t p) = t \<oplus> tt p"
proof (intro tt_eqI, rule keys_monom_multI, rule tt_in_keys, fact, fact)
  fix u
  assume "u \<in> keys (monom_mult c t p)"
  then obtain v where "v \<in> keys p" and u: "u = t \<oplus> v" by (rule keys_monom_multE)
  show "t \<oplus> tt p \<preceq>\<^sub>t u" unfolding u add.commute[of t] by (rule splus_mono, rule tt_min_keys, fact)
qed

lemma tt_map_scale: "c \<noteq> (0::'b::semiring_no_zero_divisors) \<Longrightarrow> tt (c \<cdot> p) = tt p"
  by (cases "p = 0") (simp_all add: map_scale_eq_monom_mult tt_monom_mult term_simps)

lemma tc_monom_mult [simp]: "tc (monom_mult c t p) = (c::'b::semiring_no_zero_divisors) * tc p"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with \<open>c \<noteq> 0\<close> show ?thesis by (simp add: tc_def tt_monom_mult lookup_monom_mult_plus)
  qed
qed

corollary tc_map_scale [simp]: "tc (c \<cdot> p) = (c::'b::semiring_no_zero_divisors) * tc p"
  by (simp add: map_scale_eq_monom_mult)

lemma in_keys_monom_mult_ge:
  assumes "v \<in> keys (monom_mult c t p)"
  shows "t \<oplus> tt p \<preceq>\<^sub>t v"
proof -
  from keys_monom_mult_subset assms have "v \<in> (\<oplus>) t ` (keys p)" ..
  then obtain u where "u \<in> keys p" and "v = t \<oplus> u" ..
  from \<open>u \<in> keys p\<close> have "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
  thus "t \<oplus> tt p \<preceq>\<^sub>t v" unfolding \<open>v = t \<oplus> u\<close> by (rule splus_mono)
qed

lemma lt_ge_tt: "tt p \<preceq>\<^sub>t lt p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True lt_def tt_def by simp
next
  case False
  show ?thesis by (rule lt_max_keys, rule tt_in_keys, fact False)
qed

lemma lt_eq_tt_monomial:
  assumes "is_monomial p"
  shows "lt p = tt p"
proof -
  from assms obtain c v where "c \<noteq> 0" and p: "p = monomial c v" by (rule is_monomial_monomial)
  from \<open>c \<noteq> 0\<close> have "lt p = v" and "tt p = v" unfolding p by (rule lt_monomial, rule tt_monomial)
  thus ?thesis by simp
qed

subsection \<open>@{const higher} and @{const lower}\<close>

lemma lookup_higher: "lookup (higher p u) v = (if u \<prec>\<^sub>t v then lookup p v else 0)"
  by (auto simp add: higher_def lookup_except)

lemma lookup_higher_when: "lookup (higher p u) v = (lookup p v when u \<prec>\<^sub>t v)"
  by (auto simp add: lookup_higher when_def)

lemma higher_plus: "higher (p + q) v = higher p v + higher q v"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_higher)

lemma higher_uminus [simp]: "higher (- p) v = -(higher p v)"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma higher_minus: "higher (p - q) v = higher p v - higher q v"
  by (auto intro!: poly_mapping_eqI simp: lookup_minus lookup_higher)

lemma higher_zero [simp]: "higher 0 t = 0"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma higher_eq_iff: "higher p v = higher q v \<longleftrightarrow> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix u
    assume "v \<prec>\<^sub>t u"
    moreover from \<open>?L\<close> have "lookup (higher p v) u = lookup (higher q v) u" by simp
    ultimately show "lookup p u = lookup q u" by (simp add: lookup_higher)
  qed
next
  assume ?R
  show ?L
  proof (rule poly_mapping_eqI, simp add: lookup_higher, rule)
    fix u
    assume "v \<prec>\<^sub>t u"
    with \<open>?R\<close> show "lookup p u = lookup q u" by simp
  qed
qed

lemma higher_eq_zero_iff: "higher p v = 0 \<longleftrightarrow> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = 0)"
proof -
  have "higher p v = higher 0 v \<longleftrightarrow> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup 0 u)" by (rule higher_eq_iff)
  thus ?thesis by simp
qed

lemma keys_higher: "keys (higher p v) = {u\<in>keys p. v \<prec>\<^sub>t u}"
  by (rule set_eqI, simp only: in_keys_iff, simp add: lookup_higher)

lemma higher_higher: "higher (higher p u) v = higher p (ord_term_lin.max u v)"
  by (rule poly_mapping_eqI, simp add: lookup_higher)

lemma lookup_lower: "lookup (lower p u) v = (if v \<prec>\<^sub>t u then lookup p v else 0)"
  by (auto simp add: lower_def lookup_except)

lemma lookup_lower_when: "lookup (lower p u) v = (lookup p v when v \<prec>\<^sub>t u)"
  by (auto simp add: lookup_lower when_def)

lemma lower_plus: "lower (p + q) v = lower p v + lower q v"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_lower)

lemma lower_uminus [simp]: "lower (- p) v = - lower p v"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

lemma lower_minus:  "lower (p - (q::_ \<Rightarrow>\<^sub>0 'b::ab_group_add)) v = lower p v - lower q v"
   by (auto intro!: poly_mapping_eqI simp: lookup_minus lookup_lower)

lemma lower_zero [simp]: "lower 0 v = 0"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

lemma lower_eq_iff: "lower p v = lower q v \<longleftrightarrow> (\<forall>u. u \<prec>\<^sub>t v \<longrightarrow> lookup p u = lookup q u)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix u
    assume "u \<prec>\<^sub>t v"
    moreover from \<open>?L\<close> have "lookup (lower p v) u = lookup (lower q v) u" by simp
    ultimately show "lookup p u = lookup q u" by (simp add: lookup_lower)
  qed
next
  assume ?R
  show ?L
  proof (rule poly_mapping_eqI, simp add: lookup_lower, rule)
    fix u
    assume "u \<prec>\<^sub>t v"
    with \<open>?R\<close> show "lookup p u = lookup q u" by simp
  qed
qed

lemma lower_eq_zero_iff: "lower p v = 0 \<longleftrightarrow> (\<forall>u. u \<prec>\<^sub>t v \<longrightarrow> lookup p u = 0)"
proof -
  have "lower p v = lower 0 v \<longleftrightarrow> (\<forall>u. u \<prec>\<^sub>t v \<longrightarrow> lookup p u = lookup 0 u)" by (rule lower_eq_iff)
  thus ?thesis by simp
qed

lemma keys_lower: "keys (lower p v) = {u\<in>keys p. u \<prec>\<^sub>t v}"
  by (rule set_eqI, simp only: in_keys_iff, simp add: lookup_lower)

lemma lower_lower: "lower (lower p u) v = lower p (ord_term_lin.min u v)"
  by (rule poly_mapping_eqI, simp add: lookup_lower)

lemma lt_higher:
  assumes "v \<prec>\<^sub>t lt p"
  shows "lt (higher p v) = lt p"
proof (rule lt_eqI_keys, simp_all add: keys_higher, rule conjI, rule lt_in_keys, rule)
  assume "p = 0"
  hence "lt p = min_term" by (simp add: lt_def)
  with min_term_min[of v] assms show False by simp
next
  fix u
  assume "u \<in> keys p \<and> v \<prec>\<^sub>t u"
  hence "u \<in> keys p" ..
  thus "u \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
qed fact

lemma lc_higher:
  assumes "v \<prec>\<^sub>t lt p"
  shows "lc (higher p v) = lc p"
  by (simp add: lc_def lt_higher assms lookup_higher)

lemma higher_eq_zero_iff': "higher p v = 0 \<longleftrightarrow> lt p \<preceq>\<^sub>t v"
  by (simp add: higher_eq_zero_iff lt_le_iff)

lemma higher_id_iff: "higher p v = p \<longleftrightarrow> (p = 0 \<or> v \<prec>\<^sub>t tt p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (cases "p = 0")
    case True
    thus ?thesis ..
  next
    case False
    show ?thesis
    proof (rule disjI2, rule tt_gr)
      fix u
      assume "u \<in> keys p"
      hence "lookup p u \<noteq> 0" by (simp add: in_keys_iff)
      from \<open>?L\<close> have "lookup (higher p v) u = lookup p u" by simp
      hence "lookup p u = (if v \<prec>\<^sub>t u then lookup p u else 0)" by (simp only: lookup_higher)
      hence "\<not> v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = 0" by simp
      with \<open>lookup p u \<noteq> 0\<close> show "v \<prec>\<^sub>t u" by auto
    qed fact
  qed
next
  assume ?R
  show ?L
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with \<open>?R\<close> have "v \<prec>\<^sub>t tt p" by simp
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_higher, intro impI)
      fix u
      assume "\<not> v \<prec>\<^sub>t u"
      hence "u \<preceq>\<^sub>t v" by simp
      from this \<open>v \<prec>\<^sub>t tt p\<close> have "u \<prec>\<^sub>t tt p" by simp
      hence "\<not> tt p \<preceq>\<^sub>t u" by simp
      with tt_min[of p u] show "lookup p u = 0" by blast
    qed
  qed
qed

lemma tt_lower:
  assumes "tt p \<prec>\<^sub>t v"
  shows "tt (lower p v) = tt p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (rule tt_eqI, simp_all add: keys_lower, rule, rule tt_in_keys)
    fix u
    assume "u \<in> keys p \<and> u \<prec>\<^sub>t v"
    hence "u \<in> keys p" ..
    thus "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
  qed fact+
qed

lemma tc_lower:
  assumes "tt p \<prec>\<^sub>t v"
  shows "tc (lower p v) = tc p"
  by (simp add: tc_def tt_lower assms lookup_lower)

lemma lt_lower: "lt (lower p v) \<preceq>\<^sub>t lt p"
proof (cases "lower p v = 0")
  case True
  thus ?thesis by (simp add: lt_def min_term_min)
next
  case False
  show ?thesis
  proof (rule lt_le, simp add: lookup_lower, rule impI, rule ccontr)
    fix u
    assume "lookup p u \<noteq> 0"
    hence "u \<preceq>\<^sub>t lt p" by (rule lt_max)
    moreover assume "lt p \<prec>\<^sub>t u"
    ultimately show False by simp
  qed
qed

lemma lt_lower_less:
  assumes "lower p v \<noteq> 0"
  shows "lt (lower p v) \<prec>\<^sub>t v"
  using assms
proof (rule lt_less)
  fix u
  assume "v \<preceq>\<^sub>t u"
  thus "lookup (lower p v) u = 0" by (simp add: lookup_lower_when)
qed

lemma lt_lower_eq_iff: "lt (lower p v) = lt p \<longleftrightarrow> (lt p = min_term \<or> lt p \<prec>\<^sub>t v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (rule ccontr, simp, elim conjE)
    assume "lt p \<noteq> min_term"
    hence "min_term \<prec>\<^sub>t lt p" using min_term_min ord_term_lin.dual_order.not_eq_order_implies_strict
      by blast
    assume "\<not> lt p \<prec>\<^sub>t v"
    hence "v \<preceq>\<^sub>t lt p" by simp
    have "lt (lower p v) \<prec>\<^sub>t lt p"
    proof (cases "lower p v = 0")
      case True
      thus ?thesis using \<open>min_term \<prec>\<^sub>t lt p\<close> by (simp add: lt_def)
    next
      case False
      show ?thesis
      proof (rule lt_less)
        fix u
        assume "lt p \<preceq>\<^sub>t u"
        with \<open>v \<preceq>\<^sub>t lt p\<close> have "\<not> u \<prec>\<^sub>t v" by simp
        thus "lookup (lower p v) u = 0" by (simp add: lookup_lower)
      qed fact
    qed
    with \<open>?L\<close> show False by simp
  qed
next
  assume ?R
  show ?L
  proof (cases "lt p = min_term")
    case True
    hence "lt p \<preceq>\<^sub>t lt (lower p v)" by (simp add: min_term_min)
    with lt_lower[of p v] show ?thesis by simp
  next
    case False
    with \<open>?R\<close> have "lt p \<prec>\<^sub>t v" by simp
    show ?thesis
    proof (rule lt_eqI_keys, simp_all add: keys_lower, rule conjI, rule lt_in_keys, rule)
      assume "p = 0"
      hence "lt p = min_term" by (simp add: lt_def)
      with False show False ..
    next
      fix u
      assume "u \<in> keys p \<and> u \<prec>\<^sub>t v"
      hence "u \<in> keys p" ..
      thus "u \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    qed fact
  qed
qed

lemma tt_higher:
  assumes "v \<prec>\<^sub>t lt p"
  shows "tt p \<preceq>\<^sub>t tt (higher p v)"
proof (rule tt_ge_keys, simp add: keys_higher)
  fix u
  assume "u \<in> keys p \<and> v \<prec>\<^sub>t u"
  hence "u \<in> keys p" ..
  thus "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
next
  show "higher p v \<noteq> 0"
  proof (simp add: higher_eq_zero_iff, intro exI conjI)
    have "p \<noteq> 0"
    proof
      assume "p = 0"
      hence "lt p \<preceq>\<^sub>t v" by (simp add: lt_def min_term_min)
      with assms show False by simp
    qed
    thus "lookup p (lt p) \<noteq> 0"
      using lt_in_keys by auto 
  qed fact
qed

lemma tt_higher_eq_iff:
  "tt (higher p v) = tt p \<longleftrightarrow> ((lt p \<preceq>\<^sub>t v \<and> tt p = min_term) \<or> v \<prec>\<^sub>t tt p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (rule ccontr, simp, elim conjE)
    assume a: "lt p \<preceq>\<^sub>t v \<longrightarrow> tt p \<noteq> min_term"
    assume "\<not> v \<prec>\<^sub>t tt p"
    hence "tt p \<preceq>\<^sub>t v" by simp
    have "tt p \<prec>\<^sub>t tt (higher p v)"
    proof (cases "higher p v = 0")
      case True
      with \<open>?L\<close> have "tt p = min_term" by (simp add: tt_def)
      with a have "v \<prec>\<^sub>t lt p" by auto
      have "lt p \<noteq> min_term"
      proof
        assume "lt p = min_term"
        with \<open>v \<prec>\<^sub>t lt p\<close> show False using min_term_min[of v] by auto
      qed
      hence "p \<noteq> 0" by (auto simp add: lt_def)
      from \<open>v \<prec>\<^sub>t lt p\<close> have "higher p v \<noteq> 0" by (simp add: higher_eq_zero_iff')
      from this True show ?thesis ..
    next
      case False
      show ?thesis
      proof (rule tt_gr)
        fix u
        assume "u \<in> keys (higher p v)"
        hence "v \<prec>\<^sub>t u" by (simp add: keys_higher)
        with \<open>tt p \<preceq>\<^sub>t v\<close> show "tt p \<prec>\<^sub>t u" by simp
      qed fact
    qed
    with \<open>?L\<close> show False by simp
  qed
next
  assume ?R
  show ?L
  proof (cases "lt p \<preceq>\<^sub>t v \<and> tt p = min_term")
    case True
    hence "lt p \<preceq>\<^sub>t v" and "tt p = min_term" by simp_all
    from \<open>lt p \<preceq>\<^sub>t v\<close> have "higher p v = 0" by (simp add: higher_eq_zero_iff')
    with \<open>tt p = min_term\<close> show ?thesis by (simp add: tt_def)
  next
    case False
    with \<open>?R\<close> have "v \<prec>\<^sub>t tt p" by simp
    show ?thesis
    proof (rule tt_eqI, simp_all add: keys_higher, rule conjI, rule tt_in_keys, rule)
      assume "p = 0"
      hence "tt p = min_term" by (simp add: tt_def)
      with \<open>v \<prec>\<^sub>t tt p\<close> min_term_min[of v] show False by simp
    next
      fix u
      assume "u \<in> keys p \<and> v \<prec>\<^sub>t u"
      hence "u \<in> keys p" ..
      thus "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
    qed fact
  qed
qed

lemma lower_eq_zero_iff': "lower p v = 0 \<longleftrightarrow> (p = 0 \<or> v \<preceq>\<^sub>t tt p)"
  by (auto simp add: lower_eq_zero_iff tt_ge_iff)

lemma lower_id_iff: "lower p v = p \<longleftrightarrow> (p = 0 \<or> lt p \<prec>\<^sub>t v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (cases "p = 0")
    case True
    thus ?thesis ..
  next
    case False
    show ?thesis
    proof (rule disjI2, rule lt_less)
      fix u
      assume "v \<preceq>\<^sub>t u"
      from \<open>?L\<close> have "lookup (lower p v) u = lookup p u" by simp
      hence "lookup p u = (if u \<prec>\<^sub>t v then lookup p u else 0)" by (simp only: lookup_lower)
      hence "v \<preceq>\<^sub>t u \<Longrightarrow> lookup p u = 0" by (meson ord_term_lin.leD)
      with \<open>v \<preceq>\<^sub>t u\<close> show "lookup p u = 0" by simp
    qed fact
  qed
next
  assume ?R
  show ?L
  proof (cases "p = 0", simp)
    case False
    with \<open>?R\<close> have "lt p \<prec>\<^sub>t v" by simp
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_lower, intro impI)
      fix u
      assume "\<not> u \<prec>\<^sub>t v"
      hence "v \<preceq>\<^sub>t u" by simp
      with \<open>lt p \<prec>\<^sub>t v\<close> have "lt p \<prec>\<^sub>t u" by simp
      hence "\<not> u \<preceq>\<^sub>t lt p" by simp
      with lt_max[of p u] show "lookup p u = 0" by blast
    qed
  qed
qed
    
lemma lower_higher_commute: "higher (lower p s) t = lower (higher p t) s"
  by (rule poly_mapping_eqI, simp add: lookup_higher lookup_lower)

lemma lt_lower_higher:
  assumes "v \<prec>\<^sub>t lt (lower p u)"
  shows "lt (lower (higher p v) u) = lt (lower p u)"
  by (simp add: lower_higher_commute[symmetric] lt_higher[OF assms])

lemma lc_lower_higher:
  assumes "v \<prec>\<^sub>t lt (lower p u)"
  shows "lc (lower (higher p v) u) = lc (lower p u)"
  using assms by (simp add: lc_def lt_lower_higher lookup_lower lookup_higher)

lemma trailing_monomial_higher:
  assumes "p \<noteq> 0"
  shows "p = (higher p (tt p)) + monomial (tc p) (tt p)"
proof (rule poly_mapping_eqI, simp only: lookup_add)
  fix v
  show "lookup p v = lookup (higher p (tt p)) v + lookup (monomial (tc p) (tt p)) v"
  proof (cases "tt p \<preceq>\<^sub>t v")
    case True
    show ?thesis
    proof (cases "v = tt p")
      assume "v = tt p"
      hence "\<not> tt p \<prec>\<^sub>t v" by simp
      hence "lookup (higher p (tt p)) v = 0" by (simp add: lookup_higher)
      moreover from \<open>v = tt p\<close> have "lookup (monomial (tc p) (tt p)) v = tc p" by (simp add: lookup_single)
      moreover from \<open>v = tt p\<close> have "lookup p v = tc p" by (simp add: tc_def)
      ultimately show ?thesis by simp
    next
      assume "v \<noteq> tt p"
      from this True have "tt p \<prec>\<^sub>t v" by simp
      hence "lookup (higher p (tt p)) v = lookup p v" by (simp add: lookup_higher)
      moreover from \<open>v \<noteq> tt p\<close> have "lookup (monomial (tc p) (tt p)) v = 0" by (simp add: lookup_single)
      ultimately show ?thesis by simp
    qed
  next
    case False
    hence "v \<prec>\<^sub>t tt p" by simp
    hence "tt p \<noteq> v" by simp
    from False have "\<not> tt p \<prec>\<^sub>t v" by simp
    have "lookup p v = 0"
    proof (rule ccontr)
      assume "lookup p v \<noteq> 0"
      from tt_min[OF this] False show False by simp
    qed
    moreover from \<open>tt p \<noteq> v\<close> have "lookup (monomial (tc p) (tt p)) v = 0" by (simp add: lookup_single)
    moreover from \<open>\<not> tt p \<prec>\<^sub>t v\<close> have "lookup (higher p (tt p)) v = 0" by (simp add: lookup_higher)
    ultimately show ?thesis by simp
  qed
qed

lemma higher_lower_decomp: "higher p v + monomial (lookup p v) v + lower p v = p"
proof (rule poly_mapping_eqI)
  fix u
  show "lookup (higher p v + monomial (lookup p v) v + lower p v) u = lookup p u"
  proof (rule ord_term_lin.linorder_cases)
    assume "u \<prec>\<^sub>t v"
    thus ?thesis by (simp add: lookup_add lookup_higher_when lookup_single lookup_lower_when)
  next
    assume "u = v"
    thus ?thesis by (simp add: lookup_add lookup_higher_when lookup_single lookup_lower_when)
  next
    assume "v \<prec>\<^sub>t u"
    thus ?thesis by (simp add: lookup_add lookup_higher_when lookup_single lookup_lower_when)
  qed
qed

subsection \<open>@{const tail}\<close>

lemma lookup_tail: "lookup (tail p) v = (if v \<prec>\<^sub>t lt p then lookup p v else 0)"
  by (simp add: lookup_lower tail_def)

lemma lookup_tail_when: "lookup (tail p) v = (lookup p v when v \<prec>\<^sub>t lt p)"
  by (simp add: lookup_lower_when tail_def)

lemma lookup_tail_2: "lookup (tail p) v = (if v = lt p then 0 else lookup p v)"
proof (rule ord_term_lin.linorder_cases[of v "lt p"])
  assume "v \<prec>\<^sub>t lt p"
  hence "v \<noteq> lt p" by simp
  from this \<open>v \<prec>\<^sub>t lt p\<close> lookup_tail[of p v] show ?thesis by simp
next
  assume "v = lt p"
  hence "\<not> v \<prec>\<^sub>t lt p" by simp
  from \<open>v = lt p\<close> this lookup_tail[of p v] show ?thesis by simp
next
  assume "lt p \<prec>\<^sub>t v"
  hence "\<not> v \<preceq>\<^sub>t lt p" by simp
  hence cp: "lookup p v = 0"
    using lt_max by blast
  from \<open>\<not> v \<preceq>\<^sub>t lt p\<close> have "\<not> v = lt p" and "\<not> v \<prec>\<^sub>t lt p" by simp_all
  thus ?thesis using cp lookup_tail[of p v] by simp
qed

lemma leading_monomial_tail: "p = monomial (lc p) (lt p) + tail p" for p::"_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add"
proof (rule poly_mapping_eqI)
  fix v
  have "lookup p v = lookup (monomial (lc p) (lt p)) v + lookup (tail p) v"
  proof (cases "v \<preceq>\<^sub>t lt p")
    case True
    show ?thesis
    proof (cases "v = lt p")
      assume "v = lt p"
      hence "\<not> v \<prec>\<^sub>t lt p" by simp
      hence c3: "lookup (tail p) v = 0" unfolding lookup_tail[of p v] by simp
      from \<open>v = lt p\<close> have c2: "lookup (monomial (lc p) (lt p)) v = lc p" by simp
      from \<open>v = lt p\<close> have c1: "lookup p v = lc p" by (simp add: lc_def)
      from c1 c2 c3 show ?thesis by simp
    next
      assume "v \<noteq> lt p"
      from this True have "v \<prec>\<^sub>t lt p" by simp
      hence c2: "lookup (tail p) v = lookup p v" unfolding lookup_tail[of p v] by simp
      from \<open>v \<noteq> lt p\<close> have c1: "lookup (monomial (lc p) (lt p)) v = 0" by (simp add: lookup_single)
      from c1 c2 show ?thesis by simp
    qed
  next
    case False
    hence "lt p \<prec>\<^sub>t v" by simp
    hence "lt p \<noteq> v" by simp
    from False have "\<not> v \<prec>\<^sub>t lt p" by simp
    have c1: "lookup p v = 0"
    proof (rule ccontr)
      assume "lookup p v \<noteq> 0"
      from lt_max[OF this] False show False by simp
    qed
    from \<open>lt p \<noteq> v\<close> have c2: "lookup (monomial (lc p) (lt p)) v = 0" by (simp add: lookup_single)
    from \<open>\<not> v \<prec>\<^sub>t lt p\<close> lookup_tail[of p v] have c3: "lookup (tail p) v = 0" by simp
    from c1 c2 c3 show ?thesis by simp
  qed
  thus "lookup p v = lookup (monomial (lc p) (lt p) + tail p) v" by (simp add: lookup_add)
qed

lemma tail_alt: "tail p = except p {lt p}"
  by (rule poly_mapping_eqI, simp add: lookup_tail_2 lookup_except)

corollary tail_alt_2: "tail p = p - monomial (lc p) (lt p)"
proof -
  have "p = monomial (lc p) (lt p) + tail p" by (fact leading_monomial_tail)
  also have "... = tail p + monomial (lc p) (lt p)" by (simp only: add.commute)
  finally have "p - monomial (lc p) (lt p) = (tail p + monomial (lc p) (lt p)) - monomial (lc p) (lt p)" by simp
  thus ?thesis by simp
qed

lemma tail_zero [simp]: "tail 0 = 0"
  by (simp only: tail_alt except_zero)

lemma lt_tail:
  assumes "tail p \<noteq> 0"
  shows "lt (tail p) \<prec>\<^sub>t lt p"
proof (intro lt_less)
  fix u
  assume "lt p \<preceq>\<^sub>t u"
  hence "\<not> u \<prec>\<^sub>t lt p" by simp
  thus "lookup (tail p) u = 0" unfolding lookup_tail[of p u] by simp
qed fact

lemma keys_tail: "keys (tail p) = keys p - {lt p}"
  by (simp add: tail_alt keys_except)

lemma tail_monomial: "tail (monomial c v) = 0"
  by (metis (no_types, lifting) lookup_tail_2 lookup_single_not_eq lt_less lt_monomial
      ord_term_lin.dual_order.strict_implies_not_eq single_zero tail_zero)

lemma (in ordered_term) mult_scalar_tail_rec_left:
  "p \<odot> q = monom_mult (punit.lc p) (punit.lt p) q + (punit.tail p) \<odot> q"
  unfolding punit.lc_def punit.tail_alt by (fact mult_scalar_rec_left)

lemma mult_scalar_tail_rec_right: "p \<odot> q = p \<odot> monomial (lc q) (lt q) + p \<odot> tail q"
  unfolding tail_alt lc_def by (rule mult_scalar_rec_right)

lemma lt_tail_max:
  assumes "tail p \<noteq> 0" and "v \<in> keys p" and "v \<prec>\<^sub>t lt p"
  shows "v \<preceq>\<^sub>t lt (tail p)"
proof (rule lt_max_keys, simp add: keys_tail assms(2))
  from assms(3) show "v \<noteq> lt p" by auto
qed

lemma keys_tail_less_lt:
  assumes "v \<in> keys (tail p)"
  shows "v \<prec>\<^sub>t lt p"
  using assms by (meson in_keys_iff lookup_tail)

lemma tt_tail:
  assumes "tail p \<noteq> 0"
  shows "tt (tail p) = tt p"
proof (rule tt_eqI, simp_all add: keys_tail)
  from assms have "p \<noteq> 0" using tail_zero by auto
  show "tt p \<in> keys p \<and> tt p \<noteq> lt p"
  proof (rule conjI, rule tt_in_keys, fact)
    have "tt p \<prec>\<^sub>t lt p"
      by (metis assms lower_eq_zero_iff' tail_def ord_term_lin.le_less_linear)
    thus "tt p \<noteq> lt p" by simp
  qed
next
  fix u
  assume "u \<in> keys p \<and> u \<noteq> lt p"
  hence "u \<in> keys p" ..
  thus "tt p \<preceq>\<^sub>t u" by (rule tt_min_keys)
qed

lemma tc_tail:
  assumes "tail p \<noteq> 0"
  shows "tc (tail p) = tc p"
proof (simp add: tc_def tt_tail[OF assms] lookup_tail_2, rule)
  assume "tt p = lt p"
  moreover have "tt p \<prec>\<^sub>t lt p"
    by (metis assms lower_eq_zero_iff' tail_def ord_term_lin.le_less_linear)
  ultimately show "lookup p (lt p) = 0" by simp
qed

lemma tt_tail_min:
  assumes "s \<in> keys p"
  shows "tt (tail p) \<preceq>\<^sub>t s"
proof (cases "tail p = 0")
  case True
  hence "tt (tail p) = min_term" by (simp add: tt_def)
  thus ?thesis by (simp add: min_term_min)
next
  case False
  from assms show ?thesis by (simp add: tt_tail[OF False], rule tt_min_keys)
qed

lemma tail_monom_mult:
  "tail (monom_mult c t p) = monom_mult (c::'b::semiring_no_zero_divisors) t (tail p)"
proof (cases "p = 0")
  case True
  hence "tail p = 0" and "monom_mult c t p = 0" by simp_all
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "c = 0")
    case True
    hence "monom_mult c t p = 0" and "monom_mult c t (tail p) = 0" by simp_all
    thus ?thesis by simp
  next
    case False
    let ?a = "monom_mult c t p"
    let ?b = "monom_mult c t (tail p)"
    from \<open>p \<noteq> 0\<close> False have "?a \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
    from False \<open>p \<noteq> 0\<close> have lt_a: "lt ?a = t \<oplus> lt p" by (rule lt_monom_mult)
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_tail lt_a, intro conjI impI)
      fix u
      assume "u \<prec>\<^sub>t t \<oplus> lt p"
      show "lookup (monom_mult c t p) u = lookup (monom_mult c t (tail p)) u"
      proof (cases "t adds\<^sub>p u")
        case True
        then obtain v where "u = t \<oplus> v" by (rule adds_ppE)
        from \<open>u \<prec>\<^sub>t t \<oplus> lt p\<close> have "v \<prec>\<^sub>t lt p" unfolding \<open>u = t \<oplus> v\<close> by (rule ord_term_strict_canc) 
        hence "lookup p v = lookup (tail p) v" by (simp add: lookup_tail)
        thus ?thesis by (simp add: \<open>u = t \<oplus> v\<close> lookup_monom_mult_plus)
      next
        case False
        hence "lookup ?a u = 0" by (simp add: lookup_monom_mult)
        moreover have "lookup ?b u = 0"
          proof (rule ccontr, simp only: in_keys_iff[symmetric] keys_monom_mult[OF \<open>c \<noteq> 0\<close>])
          assume "u \<in> (\<oplus>) t ` keys (tail p)"
          then obtain v where "u = t \<oplus> v" by auto
          hence "t adds\<^sub>p u" by (simp add: term_simps)
          with False show False ..
        qed
        ultimately show ?thesis by simp
      qed
    next
      fix u
      assume "\<not> u \<prec>\<^sub>t t \<oplus> lt p"
      hence "t \<oplus> lt p \<preceq>\<^sub>t u" by simp
      show "lookup (monom_mult c t (tail p)) u = 0"
      proof (rule ccontr, simp only: in_keys_iff[symmetric] keys_monom_mult[OF False])
        assume "u \<in> (\<oplus>) t ` keys (tail p)"
        then obtain v where "v \<in> keys (tail p)" and "u = t \<oplus> v" by auto
        from \<open>t \<oplus> lt p \<preceq>\<^sub>t u\<close> have "lt p \<preceq>\<^sub>t v" unfolding \<open>u = t \<oplus> v\<close> by (rule ord_term_canc)
        from \<open>v \<in> keys (tail p)\<close> have "v \<in> keys p" and "v \<noteq> lt p" by (simp_all add: keys_tail)
        from \<open>v \<in> keys p\<close> have "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
        with \<open>lt p \<preceq>\<^sub>t v\<close> have "v = lt p " by simp
        with \<open>v \<noteq> lt p\<close> show False ..
      qed
    qed
  qed
qed

lemma keys_plus_eq_lt_tt_D:
  assumes "keys (p + q) = {lt p, tt q}" and "lt q \<prec>\<^sub>t lt p" and "tt q \<prec>\<^sub>t tt (p::_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
  shows "tail p + higher q (tt q) = 0"
proof -
  note assms(3)
  also have "... \<preceq>\<^sub>t lt p" by (rule lt_ge_tt)
  finally have "tt q \<prec>\<^sub>t lt p" .
  hence "lt p \<noteq> tt q" by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence "tt q = min_term" by (simp add: tt_def)
    with \<open>q = 0\<close> assms(1) have "keys p = {lt p, min_term}" by simp
    hence "min_term \<in> keys p" by simp
    hence "tt p \<preceq>\<^sub>t tt q" unfolding \<open>tt q = min_term\<close> by (rule tt_min_keys)
    with assms(3) show False by simp
  qed
  hence "tc q \<noteq> 0" by (rule tc_not_0)
  have "p = monomial (lc p) (lt p) + tail p" by (rule leading_monomial_tail)
  moreover from \<open>q \<noteq> 0\<close> have "q = higher q (tt q) + monomial (tc q) (tt q)" by (rule trailing_monomial_higher)
  ultimately have pq: "p + q = (monomial (lc p) (lt p) + monomial (tc q) (tt q)) + (tail p + higher q (tt q))"
    (is "_ = (?m1 + ?m2) + ?b") by (simp add: algebra_simps)
  have keys_m1: "keys ?m1 = {lt p}"
  proof (rule keys_of_monomial, rule lc_not_0, rule)
    assume "p = 0"
    with assms(2) have "lt q \<prec>\<^sub>t min_term" by (simp add: lt_def)
    with min_term_min[of "lt q"] show False by simp
  qed
  moreover from \<open>tc q \<noteq> 0\<close> have keys_m2: "keys ?m2 = {tt q}" by (rule keys_of_monomial)
  ultimately have keys_m1_m2: "keys (?m1 + ?m2) = {lt p, tt q}"
    using \<open>lt p \<noteq> tt q\<close> keys_plus_eqI[of ?m1 ?m2] by auto
  show ?thesis
  proof (rule ccontr)
    assume "?b \<noteq> 0"
    hence "keys ?b \<noteq> {}" by simp
    then obtain t where "t \<in> keys ?b" by blast
    hence t_in: "t \<in> keys (tail p) \<union> keys (higher q (tt q))"
      using Poly_Mapping.keys_add[of "tail p" "higher q (tt q)"] by blast
    hence "t \<noteq> lt p"
    proof (rule, simp add: keys_tail, simp add: keys_higher, elim conjE)
      assume "t \<in> keys q"
      hence "t \<preceq>\<^sub>t lt q" by (rule lt_max_keys)
      from this assms(2) show ?thesis by simp
    qed
    moreover from t_in have "t \<noteq> tt q"
    proof (rule, simp add: keys_tail, elim conjE)
      assume "t \<in> keys p"
      hence "tt p \<preceq>\<^sub>t t" by (rule tt_min_keys)
      with assms(3) show ?thesis by simp
    next
      assume "t \<in> keys (higher q (tt q))"
      thus ?thesis by (auto simp only: keys_higher)
    qed
    ultimately have "t \<notin> keys (?m1 + ?m2)" by (simp add: keys_m1_m2)
    moreover from in_keys_plusI2[OF \<open>t \<in> keys ?b\<close> this] have "t \<in> keys (?m1 + ?m2)"
      by (simp only: keys_m1_m2 pq[symmetric] assms(1))
    ultimately show False ..
  qed
qed

subsection \<open>Order Relation on Polynomials\<close>

definition ord_strict_p :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" (infixl "\<prec>\<^sub>p" 50) where
  "p \<prec>\<^sub>p q \<longleftrightarrow> (\<exists>v. lookup p v = 0 \<and> lookup q v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u))"

definition ord_p :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" (infixl "\<preceq>\<^sub>p" 50) where
  "ord_p p q \<equiv> (p \<prec>\<^sub>p q \<or> p = q)"

lemma ord_strict_pI:
  assumes "lookup p v = 0" and "lookup q v \<noteq> 0" and "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u"
  shows "p \<prec>\<^sub>p q"
  unfolding ord_strict_p_def using assms by blast

lemma ord_strict_pE:
  assumes "p \<prec>\<^sub>p q"
  obtains v where "lookup p v = 0" and "lookup q v \<noteq> 0" and "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u"
  using assms unfolding ord_strict_p_def by blast

lemma not_ord_pI:
  assumes "lookup p v \<noteq> lookup q v" and "lookup p v \<noteq> 0" and "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u"
  shows "\<not> p \<preceq>\<^sub>p q"
proof
  assume "p \<preceq>\<^sub>p q"
  hence "p \<prec>\<^sub>p q \<or> p = q" by (simp only: ord_p_def)
  thus False
  proof
    assume "p \<prec>\<^sub>p q"
    then obtain v' where 1: "lookup p v' = 0" and 2: "lookup q v' \<noteq> 0"
      and 3: "\<And>u. v' \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u" by (rule ord_strict_pE, blast)
    from 1 2 have "lookup p v' \<noteq> lookup q v'" by simp
    hence "\<not> v \<prec>\<^sub>t v'" using assms(3) by blast
    hence "v' \<prec>\<^sub>t v \<or> v' = v" by auto
    thus ?thesis
    proof
      assume "v' \<prec>\<^sub>t v"
      hence "lookup p v = lookup q v" by (rule 3)
      with assms(1) show ?thesis ..
    next
      assume "v' = v"
      with assms(2) 1 show ?thesis by auto
    qed
  next
    assume "p = q"
    hence "lookup p v = lookup q v" by simp
    with assms(1) show ?thesis ..
  qed
qed

corollary not_ord_strict_pI:
  assumes "lookup p v \<noteq> lookup q v" and "lookup p v \<noteq> 0" and "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u"
  shows "\<not> p \<prec>\<^sub>p q"
proof -
  from assms have "\<not> p \<preceq>\<^sub>p q" by (rule not_ord_pI)
  thus ?thesis by (simp add: ord_p_def)
qed

lemma ord_strict_higher: "p \<prec>\<^sub>p q \<longleftrightarrow> (\<exists>v. lookup p v = 0 \<and> lookup q v \<noteq> 0 \<and> higher p v = higher q v)"
  unfolding ord_strict_p_def higher_eq_iff ..

lemma ord_strict_p_asymmetric:
  assumes "p \<prec>\<^sub>p q"
  shows "\<not> q \<prec>\<^sub>p p"
  using assms unfolding ord_strict_p_def
proof
  fix v1::'t
  assume "lookup p v1 = 0 \<and> lookup q v1 \<noteq> 0 \<and> (\<forall>u. v1 \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u)"
  hence "lookup p v1 = 0" and "lookup q v1 \<noteq> 0" and v1: "\<forall>u. v1 \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u"
    by auto
  show "\<not> (\<exists>v. lookup q v = 0 \<and> lookup p v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup q u = lookup p u))"
  proof (intro notI, erule exE)
    fix v2::'t
    assume "lookup q v2 = 0 \<and> lookup p v2 \<noteq> 0 \<and> (\<forall>u. v2 \<prec>\<^sub>t u \<longrightarrow> lookup q u = lookup p u)"
    hence "lookup q v2 = 0" and "lookup p v2 \<noteq> 0" and v2: "\<forall>u. v2 \<prec>\<^sub>t u \<longrightarrow> lookup q u = lookup p u"
      by auto
    show False
    proof (rule ord_term_lin.linorder_cases)
      assume "v1 \<prec>\<^sub>t v2"
      from v1[rule_format, OF this] \<open>lookup q v2 = 0\<close> \<open>lookup p v2 \<noteq> 0\<close> show ?thesis by simp
    next
      assume "v1 = v2"
      thus ?thesis using \<open>lookup p v1 = 0\<close> \<open>lookup p v2 \<noteq> 0\<close> by simp
    next
      assume "v2 \<prec>\<^sub>t v1"
      from v2[rule_format, OF this] \<open>lookup p v1 = 0\<close> \<open>lookup q v1 \<noteq> 0\<close> show ?thesis by simp
    qed
  qed
qed

lemma ord_strict_p_irreflexive: "\<not> p \<prec>\<^sub>p p"
  unfolding ord_strict_p_def
proof (intro notI, erule exE)
  fix v::'t
  assume "lookup p v = 0 \<and> lookup p v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup p u)"
  hence "lookup p v = 0" and "lookup p v \<noteq> 0" by auto
  thus False by simp
qed

lemma ord_strict_p_transitive:
  assumes "a \<prec>\<^sub>p b" and "b \<prec>\<^sub>p c"
  shows "a \<prec>\<^sub>p c"
proof -
  from \<open>a \<prec>\<^sub>p b\<close> obtain v1 where "lookup a v1 = 0"
                            and "lookup b v1 \<noteq> 0"
                            and v1[rule_format]: "(\<forall>u. v1 \<prec>\<^sub>t u \<longrightarrow> lookup a u = lookup b u)"
    unfolding ord_strict_p_def by auto
  from \<open>b \<prec>\<^sub>p c\<close> obtain v2 where "lookup b v2 = 0"
                            and "lookup c v2 \<noteq> 0"
                            and v2[rule_format]: "(\<forall>u. v2 \<prec>\<^sub>t u \<longrightarrow> lookup b u = lookup c u)"
    unfolding ord_strict_p_def by auto
  show "a \<prec>\<^sub>p c"
  proof (rule ord_term_lin.linorder_cases)
    assume "v1 \<prec>\<^sub>t v2"
    show ?thesis unfolding ord_strict_p_def
    proof
      show "lookup a v2 = 0 \<and> lookup c v2 \<noteq> 0 \<and> (\<forall>u. v2 \<prec>\<^sub>t u \<longrightarrow> lookup a u = lookup c u)"
      proof (intro conjI allI impI)
        from \<open>lookup b v2 = 0\<close> v1[OF \<open>v1 \<prec>\<^sub>t v2\<close>] show "lookup a v2 = 0" by simp
      next
        from \<open>lookup c v2 \<noteq> 0\<close> show "lookup c v2 \<noteq> 0" .
      next
        fix u
        assume "v2 \<prec>\<^sub>t u"
        from ord_term_lin.less_trans[OF \<open>v1 \<prec>\<^sub>t v2\<close> this] have "v1 \<prec>\<^sub>t u" .
        from v2[OF \<open>v2 \<prec>\<^sub>t u\<close>] v1[OF this] show "lookup a u = lookup c u" by simp
      qed
    qed
  next
    assume "v2 \<prec>\<^sub>t v1"
    show ?thesis unfolding ord_strict_p_def
    proof
      show "lookup a v1 = 0 \<and> lookup c v1 \<noteq> 0 \<and> (\<forall>u. v1 \<prec>\<^sub>t u \<longrightarrow> lookup a u = lookup c u)"
      proof (intro conjI allI impI)
        from \<open>lookup a v1 = 0\<close> show "lookup a v1 = 0" .
      next
        from \<open>lookup b v1 \<noteq> 0\<close> v2[OF \<open>v2 \<prec>\<^sub>t v1\<close>] show "lookup c v1 \<noteq> 0" by simp
      next
        fix u
        assume "v1 \<prec>\<^sub>t u"
        from ord_term_lin.less_trans[OF \<open>v2 \<prec>\<^sub>t v1\<close> this] have "v2 \<prec>\<^sub>t u" .
        from v1[OF \<open>v1 \<prec>\<^sub>t u\<close>] v2[OF this] show "lookup a u = lookup c u" by simp
      qed
    qed
  next
    assume "v1 = v2"
    thus ?thesis using \<open>lookup b v1 \<noteq> 0\<close> \<open>lookup b v2 = 0\<close> by simp
  qed
qed

sublocale order ord_p ord_strict_p
proof (intro order_strictI)
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  show "(p \<preceq>\<^sub>p q) = (p \<prec>\<^sub>p q \<or> p = q)" unfolding ord_p_def ..
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "p \<prec>\<^sub>p q"
  thus "\<not> q \<prec>\<^sub>p p" by (rule ord_strict_p_asymmetric)
next
  fix p::"'t \<Rightarrow>\<^sub>0 'b"
  show "\<not> p \<prec>\<^sub>p p" by (fact ord_strict_p_irreflexive)
next
  fix a b c :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "a \<prec>\<^sub>p b" and "b \<prec>\<^sub>p c"
  thus "a \<prec>\<^sub>p c" by (rule ord_strict_p_transitive)
qed

lemma ord_p_zero_min: "0 \<preceq>\<^sub>p p"
  unfolding ord_p_def ord_strict_p_def
proof (cases "p = 0")
  case True
  thus "(\<exists>v. lookup 0 v = 0 \<and> lookup p v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup 0 u = lookup p u)) \<or> 0 = p"
    by auto
next
  case False
  show "(\<exists>v. lookup 0 v = 0 \<and> lookup p v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup 0 u = lookup p u)) \<or> 0 = p"
  proof
    show "(\<exists>v. lookup 0 v = 0 \<and> lookup p v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup 0 u = lookup p u))"
    proof
      show "lookup 0 (lt p) = 0 \<and> lookup p (lt p) \<noteq> 0 \<and> (\<forall>u. (lt p) \<prec>\<^sub>t u \<longrightarrow> lookup 0 u = lookup p u)"
      proof (intro conjI allI impI)
        show "lookup 0 (lt p) = 0" by (transfer, simp)
      next
        from lc_not_0[OF False] show "lookup p (lt p) \<noteq> 0" unfolding lc_def .
      next
        fix u
        assume "lt p \<prec>\<^sub>t u"
        hence "\<not> u \<preceq>\<^sub>t lt p" by simp
        hence "lookup p u = 0" using lt_max[of p u] by metis
        thus "lookup 0 u = lookup p u" by simp
      qed
    qed
  qed
qed

lemma lt_ord_p:
  assumes "lt p \<prec>\<^sub>t lt q"
  shows "p \<prec>\<^sub>p q"
proof -
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    with assms have "lt p \<prec>\<^sub>t min_term" by (simp add: lt_def)
    with min_term_min[of "lt p"] show False by simp
  qed
  show ?thesis unfolding ord_strict_p_def
  proof (intro exI conjI allI impI)
    show "lookup p (lt q) = 0"
    proof (rule ccontr)
      assume "lookup p (lt q) \<noteq> 0"
      from lt_max[OF this] \<open>lt p \<prec>\<^sub>t lt q\<close> show False by simp
    qed
  next
    from lc_not_0[OF \<open>q \<noteq> 0\<close>] show "lookup q (lt q) \<noteq> 0" unfolding lc_def .
  next
    fix u
    assume "lt q \<prec>\<^sub>t u"
    hence "lt p \<prec>\<^sub>t u" using \<open>lt p \<prec>\<^sub>t lt q\<close> by simp
    have c1: "lookup q u = 0"
    proof (rule ccontr)
      assume "lookup q u \<noteq> 0"
      from lt_max[OF this] \<open>lt q \<prec>\<^sub>t u\<close> show False by simp
    qed
    have c2: "lookup p u = 0"
    proof (rule ccontr)
      assume "lookup p u \<noteq> 0"
      from lt_max[OF this] \<open>lt p \<prec>\<^sub>t u\<close> show False by simp
    qed
    from c1 c2 show "lookup p u = lookup q u" by simp
  qed
qed

lemma ord_p_lt:
  assumes "p \<preceq>\<^sub>p q"
  shows "lt p \<preceq>\<^sub>t lt q"
proof (rule ccontr)
  assume "\<not> lt p \<preceq>\<^sub>t lt q"
  hence "lt q \<prec>\<^sub>t lt p" by simp
  from lt_ord_p[OF this] \<open>p \<preceq>\<^sub>p q\<close> show False by simp
qed

lemma ord_p_tail:
  assumes "p \<noteq> 0" and "lt p = lt q" and "p \<prec>\<^sub>p q"
  shows "tail p \<prec>\<^sub>p tail q"
  using assms unfolding ord_strict_p_def
proof -
  assume "p \<noteq> 0" and "lt p = lt q"
    and "\<exists>v. lookup p v = 0 \<and> lookup q v \<noteq> 0 \<and> (\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u)"
  then obtain v where "lookup p v = 0"
                  and "lookup q v \<noteq> 0"
                  and a: "\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u" by auto
  from lt_max[OF \<open>lookup q v \<noteq> 0\<close>] \<open>lt p = lt q\<close> have "v \<prec>\<^sub>t lt p \<or> v = lt p" by auto
  hence "v \<prec>\<^sub>t lt p"
  proof
    assume "v \<prec>\<^sub>t lt p"
    thus ?thesis .
  next
    assume "v = lt p"
    thus ?thesis using lc_not_0[OF \<open>p \<noteq> 0\<close>] \<open>lookup p v = 0\<close> unfolding lc_def by auto
  qed
  have pt: "lookup (tail p) v = lookup p v" using lookup_tail[of p v] \<open>v \<prec>\<^sub>t lt p\<close> by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence  "p \<prec>\<^sub>p 0" using \<open>p \<prec>\<^sub>p q\<close> by simp
    hence "\<not> 0 \<preceq>\<^sub>p p" by auto
    thus False using ord_p_zero_min[of p] by simp
  qed
  have qt: "lookup (tail q) v = lookup q v"
    using lookup_tail[of q v] \<open>v \<prec>\<^sub>t lt p\<close> \<open>lt p = lt q\<close> by simp
  show "\<exists>w. lookup (tail p) w = 0 \<and> lookup (tail q) w \<noteq> 0 \<and>
        (\<forall>u. w \<prec>\<^sub>t u \<longrightarrow> lookup (tail p) u = lookup (tail q) u)"
  proof (intro exI conjI allI impI)
    from pt \<open>lookup p v = 0\<close> show "lookup (tail p) v = 0" by simp
  next
    from qt \<open>lookup q v \<noteq> 0\<close> show "lookup (tail q) v \<noteq> 0" by simp
  next
    fix u
    assume "v \<prec>\<^sub>t u"
    from a[rule_format, OF \<open>v \<prec>\<^sub>t u\<close>] lookup_tail[of p u] lookup_tail[of q u]
      \<open>lt p = lt q\<close> show "lookup (tail p) u = lookup (tail q) u" by simp
  qed
qed

lemma tail_ord_p:
  assumes "p \<noteq> 0"
  shows "tail p \<prec>\<^sub>p p"
proof (cases "tail p = 0")
  case True
  with ord_p_zero_min[of p] \<open>p \<noteq> 0\<close> show ?thesis by simp
next
  case False
  from lt_tail[OF False] show ?thesis by (rule lt_ord_p)
qed

lemma higher_lookup_eq_zero:
  assumes pt: "lookup p v = 0" and hp: "higher p v = 0" and le: "q \<preceq>\<^sub>p p"
  shows "(lookup q v = 0) \<and> (higher q v) = 0"
using le unfolding ord_p_def
proof
  assume "q \<prec>\<^sub>p p"
  thus ?thesis unfolding ord_strict_p_def
  proof
    fix w
    assume "lookup q w = 0 \<and> lookup p w \<noteq> 0 \<and> (\<forall>u. w \<prec>\<^sub>t u \<longrightarrow> lookup q u = lookup p u)"
    hence qs: "lookup q w = 0" and ps: "lookup p w \<noteq> 0" and u: "\<forall>u. w \<prec>\<^sub>t u \<longrightarrow> lookup q u = lookup p u"
      by auto
    from hp have pu: "\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = 0" by (simp only: higher_eq_zero_iff)
    from pu[rule_format, of w] ps have "\<not> v \<prec>\<^sub>t w" by auto
    hence "w \<preceq>\<^sub>t v" by simp
    hence "w \<prec>\<^sub>t v \<or> w = v" by auto
    hence st: "w \<prec>\<^sub>t v"
    proof (rule disjE, simp_all)
      assume "w = v"
      from this pt ps show False by simp
    qed
    show ?thesis
    proof
      from u[rule_format, OF st] pt show "lookup q v = 0" by simp
    next
      have "\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup q u = 0"
      proof (intro allI, intro impI)
        fix u
        assume "v \<prec>\<^sub>t u"
        from this st have "w \<prec>\<^sub>t u" by simp
        from u[rule_format, OF this] pu[rule_format, OF \<open>v \<prec>\<^sub>t u\<close>] show "lookup q u = 0" by simp
      qed
      thus "higher q v = 0" by (simp only: higher_eq_zero_iff)
    qed
  qed
next
  assume "q = p"
  thus ?thesis using assms by simp
qed

lemma ord_strict_p_recI:
  assumes "lt p = lt q" and "lc p = lc q" and tail: "tail p \<prec>\<^sub>p tail q"
  shows "p \<prec>\<^sub>p q"
proof -
  from tail obtain v where pt: "lookup (tail p) v = 0"
                      and qt: "lookup (tail q) v \<noteq> 0"
                      and a: "\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup (tail p) u = lookup (tail q) u"
    unfolding ord_strict_p_def by auto
  from qt lookup_zero[of v] have "tail q \<noteq> 0" by auto
  from lt_max[OF qt] lt_tail[OF this] have "v \<prec>\<^sub>t lt q" by simp
  hence "v \<prec>\<^sub>t lt p" using \<open>lt p = lt q\<close> by simp
  show ?thesis unfolding ord_strict_p_def
  proof (rule exI[of _ v], intro conjI allI impI)
    from lookup_tail[of p v] \<open>v \<prec>\<^sub>t lt p\<close> pt show "lookup p v = 0" by simp
  next
    from lookup_tail[of q v] \<open>v \<prec>\<^sub>t lt q\<close> qt show "lookup q v \<noteq> 0" by simp
  next
    fix u
    assume "v \<prec>\<^sub>t u"
    from this a have s: "lookup (tail p) u = lookup (tail q) u" by simp
    show "lookup p u = lookup q u"
    proof (cases "u = lt p")
      case True
      from True \<open>lc p = lc q\<close> \<open>lt p = lt q\<close> show ?thesis unfolding lc_def by simp
    next
      case False
      from False s lookup_tail_2[of p u] lookup_tail_2[of q u] \<open>lt p = lt q\<close> show ?thesis by simp
    qed
  qed
qed

lemma ord_strict_p_recE1:
  assumes "p \<prec>\<^sub>p q"
  shows "q \<noteq> 0"
proof
  assume "q = 0"
  from this assms ord_p_zero_min[of p] show False by simp
qed

lemma ord_strict_p_recE2:
  assumes "p \<noteq> 0" and "p \<prec>\<^sub>p q" and "lt p = lt q"
  shows "lc p = lc q"
proof -
  from \<open>p \<prec>\<^sub>p q\<close> obtain v where pt: "lookup p v = 0"
                          and qt: "lookup q v \<noteq> 0"
                          and a: "\<forall>u. v \<prec>\<^sub>t u \<longrightarrow> lookup p u = lookup q u"
    unfolding ord_strict_p_def by auto
  show ?thesis
  proof (cases "v \<prec>\<^sub>t lt p")
    case True
    from this a have "lookup p (lt p) = lookup q (lt p)" by simp
    thus ?thesis using \<open>lt p = lt q\<close> unfolding lc_def by simp
  next
    case False
    from this lt_max[OF qt] \<open>lt p = lt q\<close> have "v = lt p" by simp
    from this lc_not_0[OF \<open>p \<noteq> 0\<close>] pt show ?thesis unfolding lc_def by auto
  qed
qed

lemma ord_strict_p_rec [code]:
  "p \<prec>\<^sub>p q =
  (q \<noteq> 0 \<and>
    (p = 0 \<or>
      (let v1 = lt p; v2 = lt q in
        (v1 \<prec>\<^sub>t v2 \<or> (v1 = v2 \<and> lookup p v1 = lookup q v2 \<and> lower p v1 \<prec>\<^sub>p lower q v2))
      )
    )
   )"
  (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (intro conjI, rule ord_strict_p_recE1, fact)
    have "((lt p = lt q \<and> lc p = lc q \<and> tail p \<prec>\<^sub>p tail q) \<or> lt p \<prec>\<^sub>t lt q) \<or> p = 0"
    proof (intro disjCI)
      assume "p \<noteq> 0" and nl: "\<not> lt p \<prec>\<^sub>t lt q"
      from \<open>?L\<close> have "p \<preceq>\<^sub>p q" by simp
      from ord_p_lt[OF this] nl have "lt p = lt q" by simp
      show "lt p = lt q \<and> lc p = lc q \<and> tail p \<prec>\<^sub>p tail q"
        by (intro conjI, fact, rule ord_strict_p_recE2, fact+, rule ord_p_tail, fact+)
    qed
    thus "p = 0 \<or>
            (let v1 = lt p; v2 = lt q in
              (v1 \<prec>\<^sub>t v2 \<or> v1 = v2 \<and> lookup p v1 = lookup q v2 \<and> lower p v1 \<prec>\<^sub>p lower q v2)
            )"
      unfolding lc_def tail_def by auto
  qed
next
  assume ?R
  hence "q \<noteq> 0"
    and dis: "p = 0 \<or>
                (let v1 = lt p; v2 = lt q in
                  (v1 \<prec>\<^sub>t v2 \<or> v1 = v2 \<and> lookup p v1 = lookup q v2 \<and> lower p v1 \<prec>\<^sub>p lower q v2)
                )"
    by simp_all
  show ?L
  proof (cases "p = 0")
    assume "p = 0"
    hence "p \<preceq>\<^sub>p q" using ord_p_zero_min[of q] by simp
    thus ?thesis using \<open>p = 0\<close> \<open>q \<noteq> 0\<close> by simp
  next
    assume "p \<noteq> 0"
    hence "let v1 = lt p; v2 = lt q in
            (v1 \<prec>\<^sub>t v2 \<or> v1 = v2 \<and> lookup p v1 = lookup q v2 \<and> lower p v1 \<prec>\<^sub>p lower q v2)"
      using dis by simp
    hence "lt p \<prec>\<^sub>t lt q \<or> (lt p = lt q \<and> lc p = lc q \<and> tail p \<prec>\<^sub>p tail q)"
      unfolding lc_def tail_def by (simp add: Let_def)
    thus ?thesis
    proof
      assume "lt p \<prec>\<^sub>t lt q"
      from lt_ord_p[OF this] show ?thesis .
    next
      assume "lt p = lt q \<and> lc p = lc q \<and> tail p \<prec>\<^sub>p tail q"
      hence "lt p = lt q" and "lc p = lc q" and "tail p \<prec>\<^sub>p tail q" by simp_all
      thus ?thesis by (rule ord_strict_p_recI)
    qed
  qed
qed

lemma ord_strict_p_monomial_iff: "p \<prec>\<^sub>p monomial c v \<longleftrightarrow> (c \<noteq> 0 \<and> (p = 0 \<or> lt p \<prec>\<^sub>t v))"
proof -
  from ord_p_zero_min[of "tail p"] have *: "\<not> tail p \<prec>\<^sub>p 0" by auto
  show ?thesis
    by (simp add: ord_strict_p_rec[of p] Let_def tail_def[symmetric] lc_def[symmetric]
        monomial_0_iff tail_monomial *, simp add: lt_monomial cong: conj_cong)
qed

corollary ord_strict_p_monomial_plus:
  assumes "p \<prec>\<^sub>p monomial c v" and "q \<prec>\<^sub>p monomial c v"
  shows "p + q \<prec>\<^sub>p monomial c v"
proof -
  from assms(1) have "c \<noteq> 0" and "p = 0 \<or> lt p \<prec>\<^sub>t v" by (simp_all add: ord_strict_p_monomial_iff)
  from this(2) show ?thesis
  proof
    assume "p = 0"
    with assms(2) show ?thesis by simp
  next
    assume "lt p \<prec>\<^sub>t v"
    from assms(2) have "q = 0 \<or> lt q \<prec>\<^sub>t v" by (simp add: ord_strict_p_monomial_iff)
    thus ?thesis
    proof
      assume "q = 0"
      with assms(1) show ?thesis by simp
    next
      assume "lt q \<prec>\<^sub>t v"
      with \<open>lt p \<prec>\<^sub>t v\<close> have "lt (p + q) \<prec>\<^sub>t v"
        using lt_plus_le_max ord_term_lin.dual_order.strict_trans2 ord_term_lin.max_less_iff_conj
        by blast 
      with \<open>c \<noteq> 0\<close> show ?thesis by (simp add: ord_strict_p_monomial_iff)
    qed
  qed
qed

lemma ord_strict_p_monom_mult:
  assumes "p \<prec>\<^sub>p q" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "monom_mult c t p \<prec>\<^sub>p monom_mult c t q"
proof -
  from assms(1) obtain v where 1: "lookup p v = 0" and 2: "lookup q v \<noteq> 0"
    and 3: "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u" unfolding ord_strict_p_def by auto
  show ?thesis unfolding ord_strict_p_def
  proof (intro exI conjI allI impI)
    from 1 show "lookup (monom_mult c t p) (t \<oplus> v) = 0" by (simp add: lookup_monom_mult_plus)
  next
    from 2 assms(2) show "lookup (monom_mult c t q) (t \<oplus> v) \<noteq> 0" by (simp add: lookup_monom_mult_plus)
  next
    fix u
    assume "t \<oplus> v \<prec>\<^sub>t u"
    show "lookup (monom_mult c t p) u = lookup (monom_mult c t q) u"
    proof (cases "t adds\<^sub>p u")
      case True
      then obtain w where u: "u = t \<oplus> w" ..
      from \<open>t \<oplus> v \<prec>\<^sub>t u\<close> have "v \<prec>\<^sub>t w" unfolding u by (rule ord_term_strict_canc)
      hence "lookup p w = lookup q w" by (rule 3)
      thus ?thesis by (simp add: u lookup_monom_mult_plus)
    next
      case False
      thus ?thesis by (simp add: lookup_monom_mult)
    qed
  qed
qed

lemma ord_strict_p_plus:
  assumes "p \<prec>\<^sub>p q" and "keys r \<inter> keys q = {}"
  shows "p + r \<prec>\<^sub>p q + r"
proof -
  from assms(1) obtain v where 1: "lookup p v = 0" and 2: "lookup q v \<noteq> 0"
    and 3: "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u" unfolding ord_strict_p_def by auto
  have eq: "lookup r v = 0"
    by (meson "2" assms(2) disjoint_iff_not_equal in_keys_iff)
  show ?thesis unfolding ord_strict_p_def
  proof (intro exI conjI allI impI, simp_all add: lookup_add)
    from 1 show "lookup p v + lookup r v = 0" by (simp add: eq)
  next
    from 2 show "lookup q v + lookup r v \<noteq> 0" by (simp add: eq)
  next
    fix u
    assume "v \<prec>\<^sub>t u"
    hence "lookup p u = lookup q u" by (rule 3)
    thus "lookup p u + lookup r u = lookup q u + lookup r u" by simp
  qed
qed

lemma poly_mapping_tail_induct [case_names 0 tail]:
  assumes "P 0" and "\<And>p. p \<noteq> 0 \<Longrightarrow> P (tail p) \<Longrightarrow> P p"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  hence "p = 0" by simp
  from \<open>P 0\<close> show ?case unfolding \<open>p = 0\<close> .
next
  case ind: (Suc n)
  from ind(2) have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  thus ?case
  proof (rule assms(2))
    show "P (tail p)"
    proof (rule ind(1))
      from \<open>p \<noteq> 0\<close> have "lt p \<in> keys p" by (rule lt_in_keys)
      hence "card (keys (tail p)) = card (keys p) - 1" by (simp add: keys_tail)
      also have "... = n" unfolding ind(2)[symmetric] by simp
      finally show "n = card (keys (tail p))" by simp
    qed
  qed
qed

lemma poly_mapping_neqE:
  assumes "p \<noteq> q"
  obtains v where "v \<in> keys p \<union> keys q" and "lookup p v \<noteq> lookup q v"
    and "\<And>u. v \<prec>\<^sub>t u \<Longrightarrow> lookup p u = lookup q u"
proof -
  let ?A = "{v. lookup p v \<noteq> lookup q v}"
  define v where "v = ord_term_lin.Max ?A"
  have "?A \<subseteq> keys p \<union> keys q"
    using UnI2 in_keys_iff by fastforce
  also have "finite ..." by (rule finite_UnI) (fact finite_keys)+
  finally(finite_subset) have fin: "finite ?A" .
  moreover have "?A \<noteq> {}"
  proof
    assume "?A = {}"
    hence "p = q"
      using poly_mapping_eqI by fastforce
    with assms show False ..
  qed
  ultimately have "v \<in> ?A" unfolding v_def by (rule ord_term_lin.Max_in)
  show ?thesis
  proof
    from \<open>?A \<subseteq> keys p \<union> keys q\<close> \<open>v \<in> ?A\<close> show "v \<in> keys p \<union> keys q" ..
  next
    from \<open>v \<in> ?A\<close> show "lookup p v \<noteq> lookup q v" by simp
  next
    fix u
    assume "v \<prec>\<^sub>t u"
    show "lookup p u = lookup q u"
    proof (rule ccontr)
      assume "lookup p u \<noteq> lookup q u"
      hence "u \<in> ?A" by simp
      with fin have "u \<preceq>\<^sub>t v" unfolding v_def by (rule ord_term_lin.Max_ge)
      with \<open>v \<prec>\<^sub>t u\<close> show False by simp
    qed
  qed
qed

subsection \<open>Monomials\<close>

lemma keys_monomial:
  assumes "is_monomial p"
  shows "keys p = {lt p}"
  using assms by (metis is_monomial_monomial lt_monomial keys_of_monomial)

lemma monomial_eq_itself:
  assumes "is_monomial p"
  shows "monomial (lc p) (lt p) = p"
proof -
  from assms have "p \<noteq> 0" by (rule monomial_not_0)
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence keys1: "keys (monomial (lc p) (lt p)) = {lt p}" by (rule keys_of_monomial)
  show ?thesis
    by (rule poly_mapping_keys_eqI, simp only: keys_monomial[OF assms] keys1,
        simp only: keys1 lookup_single Poly_Mapping.when_def, auto simp add: lc_def)
qed

lemma lt_eq_min_term_monomial:
  assumes "lt p = min_term"
  shows "monomial (lc p) min_term = p"
proof (rule poly_mapping_eqI)
  fix v
  from min_term_min[of v] have "v = min_term \<or> min_term \<prec>\<^sub>t v" by auto
  thus "lookup (monomial (lc p) min_term) v = lookup p v"
  proof
    assume "v = min_term"
    thus ?thesis by (simp add: lookup_single lc_def assms)
  next
    assume "min_term \<prec>\<^sub>t v"
    moreover have "v \<notin> keys p"
    proof
      assume "v \<in> keys p"
      hence "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
      with \<open>min_term \<prec>\<^sub>t v\<close> show False by (simp add: assms)
    qed
    ultimately show ?thesis by (simp add: lookup_single in_keys_iff)
  qed
qed

lemma is_monomial_monomial_ordered:
  assumes "is_monomial p"
  obtains c v where "c \<noteq> 0" and "lc p = c" and "lt p = v" and "p = monomial c v"
proof -
  from assms obtain c v where "c \<noteq> 0" and p_eq: "p = monomial c v" by (rule is_monomial_monomial)
  note this(1)
  moreover have "lc p = c" unfolding p_eq by (rule lc_monomial)
  moreover from \<open>c \<noteq> 0\<close> have "lt p = v" unfolding p_eq by (rule lt_monomial)
  ultimately show ?thesis using p_eq ..
qed

lemma monomial_plus_not_0:
  assumes "c \<noteq> 0" and "lt p \<prec>\<^sub>t v"
  shows "monomial c v + p \<noteq> 0"
proof
  assume "monomial c v + p = 0"
  hence "0 = lookup (monomial c v + p) v" by simp
  also have "... = c + lookup p v" by (simp add: lookup_add)
  also have "... = c"
  proof -
    from assms(2) have "\<not> v \<preceq>\<^sub>t lt p" by simp
    with lt_max[of p v] have "lookup p v = 0" by blast
    thus ?thesis by simp
  qed
  finally show False using \<open>c \<noteq> 0\<close> by simp
qed

lemma lt_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lt p \<prec>\<^sub>t v"
  shows "lt (monomial c v + p) = v"
proof -
  have eq: "lt (monomial c v) = v" by (simp only: lt_monomial[OF \<open>c \<noteq> 0\<close>])
  moreover have "lt (p + monomial c v) = lt (monomial c v)" by (rule lt_plus_eqI, simp only: eq, fact)
  ultimately show ?thesis by (simp add: add.commute)
qed

lemma lc_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lt p \<prec>\<^sub>t v"
  shows "lc (monomial c v + p) = c"
proof -
  from assms(2) have "\<not> v \<preceq>\<^sub>t lt p" by simp
  with lt_max[of p v] have "lookup p v = 0" by blast
  thus ?thesis by (simp add: lc_def lt_monomial_plus[OF assms] lookup_add)
qed

lemma tt_monomial_plus:
  assumes "p \<noteq> (0::_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add)" and "lt p \<prec>\<^sub>t v"
  shows "tt (monomial c v + p) = tt p"
proof (cases "c = 0")
  case True
  thus ?thesis by (simp add: monomial_0I)
next
  case False
  have eq: "tt (monomial c v) = v" by (simp only: tt_monomial[OF \<open>c \<noteq> 0\<close>])
  moreover have "tt (p + monomial c v) = tt p"
  proof (rule tt_plus_eqI, fact, simp only: eq)
    from lt_ge_tt[of p] assms(2) show "tt p \<prec>\<^sub>t v" by simp
  qed
  ultimately show ?thesis by (simp add: ac_simps)
qed

lemma tc_monomial_plus:
  assumes "p \<noteq> (0::_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add)" and "lt p \<prec>\<^sub>t v"
  shows "tc (monomial c v + p) = tc p"
proof (simp add: tc_def tt_monomial_plus[OF assms] lookup_add lookup_single Poly_Mapping.when_def,
    rule impI)
  assume "v = tt p"
  with assms(2) have "lt p \<prec>\<^sub>t tt p" by simp
  with lt_ge_tt[of p] show "c + lookup p (tt p) = lookup p (tt p)" by simp
qed

lemma tail_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lt p \<prec>\<^sub>t v"
  shows "tail (monomial c v + p) = p" (is "tail ?q = _")
proof -
  from assms have "lt ?q = v" by (rule lt_monomial_plus)
  moreover have "lower (monomial c v) v = 0"
    by (simp add: lower_eq_zero_iff', rule disjI2, simp add: tt_monomial[OF \<open>c \<noteq> 0\<close>])
  ultimately show ?thesis by (simp add: tail_def lower_plus lower_id_iff, intro disjI2 assms(2))
qed

subsection \<open>Lists of Keys\<close>

text \<open>In algorithms one very often needs to compute the sorted list of all terms appearing
  in a list of polynomials.\<close>

definition pps_to_list :: "'t set \<Rightarrow> 't list" where
  "pps_to_list S = rev (ord_term_lin.sorted_list_of_set S)"

definition keys_to_list :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 't list"
  where "keys_to_list p = pps_to_list (keys p)"

definition Keys_to_list :: "('t \<Rightarrow>\<^sub>0 'b::zero) list \<Rightarrow> 't list"
  where "Keys_to_list ps = fold (\<lambda>p ts. merge_wrt (\<succ>\<^sub>t) (keys_to_list p) ts) ps []"

text \<open>Function @{const pps_to_list} turns finite sets of terms into sorted lists, where the
  lists are sorted descending (i.\,e. greater elements come before smaller ones).\<close>

lemma distinct_pps_to_list: "distinct (pps_to_list S)"
  unfolding pps_to_list_def distinct_rev by (rule ord_term_lin.distinct_sorted_list_of_set)

lemma set_pps_to_list:
  assumes "finite S"
  shows "set (pps_to_list S) = S"
  unfolding pps_to_list_def set_rev using assms by simp

lemma length_pps_to_list: "length (pps_to_list S) = card S"
proof (cases "finite S")
  case True
  from distinct_card[OF distinct_pps_to_list] have "length (pps_to_list S) = card (set (pps_to_list S))"
    by simp
  also from True have "... = card S" by (simp only: set_pps_to_list)
  finally show ?thesis .
next
  case False
  thus ?thesis by (simp add: pps_to_list_def)
qed

lemma pps_to_list_sorted_wrt: "sorted_wrt (\<succ>\<^sub>t) (pps_to_list S)"
proof -
  have "sorted_wrt (\<succeq>\<^sub>t) (pps_to_list S)"
  proof -
    have tr: "transp (\<preceq>\<^sub>t)" using transp_def by fastforce
    have *: "(\<lambda>x y. y \<succeq>\<^sub>t x) = (\<preceq>\<^sub>t)" by simp
    show ?thesis
      by (simp only: * pps_to_list_def sorted_wrt_rev ord_term_lin.sorted_sorted_wrt[symmetric],
          rule ord_term_lin.sorted_sorted_list_of_set)
  qed
  with distinct_pps_to_list have "sorted_wrt (\<lambda>x y. x \<succeq>\<^sub>t y \<and> x \<noteq> y) (pps_to_list S)"
    by (rule distinct_sorted_wrt_imp_sorted_wrt_strict)
  moreover have "(\<succ>\<^sub>t) = (\<lambda>x y. x \<succeq>\<^sub>t y \<and> x \<noteq> y)"
    using ord_term_lin.dual_order.order_iff_strict by auto
  ultimately show ?thesis by simp
qed

lemma pps_to_list_nth_leI:
  assumes "j \<le> i" and "i < card S"
  shows "(pps_to_list S) ! i \<preceq>\<^sub>t (pps_to_list S) ! j"
proof (cases "j = i")
  case True
  show ?thesis by (simp add: True)
next
  case False
  with assms(1) have "j < i" by simp
  let ?ts = "pps_to_list S"
  from pps_to_list_sorted_wrt \<open>j < i\<close> have "(\<prec>\<^sub>t)\<inverse>\<inverse> (?ts ! j) (?ts ! i)"
  proof (rule sorted_wrt_nth_less)
    from assms(2) show "i < length ?ts" by (simp only: length_pps_to_list)
  qed
  thus ?thesis by simp
qed

lemma pps_to_list_nth_lessI:
  assumes "j < i" and "i < card S"
  shows "(pps_to_list S) ! i \<prec>\<^sub>t (pps_to_list S) ! j"
proof -
  let ?ts = "pps_to_list S"
  from assms(1) have "j \<le> i" and "i \<noteq> j" by simp_all
  with assms(2) have "i < length ?ts" and "j < length ?ts" by (simp_all only: length_pps_to_list)
  show ?thesis
  proof (rule ord_term_lin.neq_le_trans)
    from \<open>i \<noteq> j\<close> show "?ts ! i \<noteq> ?ts ! j"
      by (simp add: nth_eq_iff_index_eq[OF distinct_pps_to_list \<open>i < length ?ts\<close> \<open>j < length ?ts\<close>])
  next
    from \<open>j \<le> i\<close> assms(2) show "?ts ! i \<preceq>\<^sub>t ?ts ! j" by (rule pps_to_list_nth_leI)
  qed
qed

lemma pps_to_list_nth_leD:
  assumes "(pps_to_list S) ! i \<preceq>\<^sub>t (pps_to_list S) ! j" and "j < card S"
  shows "j \<le> i"
proof (rule ccontr)
  assume "\<not> j \<le> i"
  hence "i < j" by simp
  from this \<open>j < card S\<close> have "(pps_to_list S) ! j \<prec>\<^sub>t (pps_to_list S) ! i" by (rule pps_to_list_nth_lessI)
  with assms(1) show False by simp
qed

lemma pps_to_list_nth_lessD:
  assumes "(pps_to_list S) ! i \<prec>\<^sub>t (pps_to_list S) ! j" and "j < card S"
  shows "j < i"
proof (rule ccontr)
  assume "\<not> j < i"
  hence "i \<le> j" by simp
  from this \<open>j < card S\<close> have "(pps_to_list S) ! j \<preceq>\<^sub>t (pps_to_list S) ! i" by (rule pps_to_list_nth_leI)
  with assms(1) show False by simp
qed

lemma set_keys_to_list: "set (keys_to_list p) = keys p"
  by (simp add: keys_to_list_def set_pps_to_list)

lemma length_keys_to_list: "length (keys_to_list p) = card (keys p)"
  by (simp only: keys_to_list_def length_pps_to_list)

lemma keys_to_list_zero [simp]: "keys_to_list 0 = []"
  by (simp add: keys_to_list_def pps_to_list_def)

lemma Keys_to_list_Nil [simp]: "Keys_to_list [] = []"
  by (simp add: Keys_to_list_def)

lemma set_Keys_to_list: "set (Keys_to_list ps) = Keys (set ps)"
proof -
  have "set (Keys_to_list ps) = (\<Union>p\<in>set ps. set (keys_to_list p)) \<union> set []"
    unfolding Keys_to_list_def by (rule set_fold, simp only: set_merge_wrt)
  also have "... = Keys (set ps)" by (simp add: Keys_def set_keys_to_list)
  finally show ?thesis .
qed

lemma Keys_to_list_sorted_wrt_aux:
  assumes "sorted_wrt (\<succ>\<^sub>t) ts"
  shows "sorted_wrt (\<succ>\<^sub>t) (fold (\<lambda>p ts. merge_wrt (\<succ>\<^sub>t) (keys_to_list p) ts) ps ts)"
  using assms
proof (induct ps arbitrary: ts)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (simp only: fold.simps o_def, rule Cons(1), rule sorted_merge_wrt)
    show "transp (\<succ>\<^sub>t)" unfolding transp_def by fastforce
  next
    fix x y :: 't
    assume "x \<noteq> y"
    thus "x \<succ>\<^sub>t y \<or> y \<succ>\<^sub>t x" by auto
  next
    show "sorted_wrt (\<succ>\<^sub>t) (keys_to_list p)" unfolding keys_to_list_def
      by (fact pps_to_list_sorted_wrt)
  qed fact
qed

corollary Keys_to_list_sorted_wrt: "sorted_wrt (\<succ>\<^sub>t) (Keys_to_list ps)"
  unfolding Keys_to_list_def
proof (rule Keys_to_list_sorted_wrt_aux)
  show "sorted_wrt (\<succ>\<^sub>t) []" by simp
qed

corollary distinct_Keys_to_list: "distinct (Keys_to_list ps)"
proof (rule distinct_sorted_wrt_irrefl)
  show "irreflp (\<succ>\<^sub>t)" by (simp add: irreflp_def)
next
  show "transp (\<succ>\<^sub>t)" unfolding transp_def by fastforce
next
  show "sorted_wrt (\<succ>\<^sub>t) (Keys_to_list ps)" by (fact Keys_to_list_sorted_wrt)
qed

lemma length_Keys_to_list: "length (Keys_to_list ps) = card (Keys (set ps))"
proof -
  from distinct_Keys_to_list have "card (set (Keys_to_list ps)) = length (Keys_to_list ps)"
    by (rule distinct_card)
  thus ?thesis by (simp only: set_Keys_to_list)
qed

lemma Keys_to_list_eq_pps_to_list: "Keys_to_list ps = pps_to_list (Keys (set ps))"
  using _ Keys_to_list_sorted_wrt distinct_Keys_to_list pps_to_list_sorted_wrt distinct_pps_to_list
proof (rule sorted_wrt_distinct_set_unique)
  show "antisymp (\<succ>\<^sub>t)" unfolding antisymp_def by fastforce
next
  from finite_set have fin: "finite (Keys (set ps))" by (rule finite_Keys)
  show "set (Keys_to_list ps) = set (pps_to_list (Keys (set ps)))"
    by (simp add: set_Keys_to_list set_pps_to_list[OF fin])
qed

subsection \<open>Multiplication\<close>

lemma in_keys_mult_scalar_le:
  assumes "v \<in> keys (p \<odot> q)"
  shows "v \<preceq>\<^sub>t punit.lt p \<oplus> lt q"
proof -
  from assms obtain t u where "t \<in> keys p" and "u \<in> keys q" and "v = t \<oplus> u"
    by (rule in_keys_mult_scalarE)
  from \<open>t \<in> keys p\<close> have "t \<preceq> punit.lt p" by (rule punit.lt_max_keys)
  from \<open>u \<in> keys q\<close> have "u \<preceq>\<^sub>t lt q" by (rule lt_max_keys)
  hence "v \<preceq>\<^sub>t t \<oplus> lt q" unfolding \<open>v = t \<oplus> u\<close> by (rule splus_mono)
  also from \<open>t \<preceq> punit.lt p\<close> have "... \<preceq>\<^sub>t punit.lt p \<oplus> lt q" by (rule splus_mono_left)
  finally show ?thesis .
qed

lemma in_keys_mult_scalar_ge:
  assumes "v \<in> keys (p \<odot> q)"
  shows "punit.tt p \<oplus> tt q \<preceq>\<^sub>t v"
proof -
  from assms obtain t u where "t \<in> keys p" and "u \<in> keys q" and "v = t \<oplus> u"
    by (rule in_keys_mult_scalarE)
  from \<open>t \<in> keys p\<close> have "punit.tt p \<preceq> t" by (rule punit.tt_min_keys)
  from \<open>u \<in> keys q\<close> have "tt q \<preceq>\<^sub>t u" by (rule tt_min_keys)
  hence "punit.tt p \<oplus> tt q \<preceq>\<^sub>t punit.tt p \<oplus> u" by (rule splus_mono)
  also from \<open>punit.tt p \<preceq> t\<close> have "... \<preceq>\<^sub>t v" unfolding \<open>v = t \<oplus> u\<close> by (rule splus_mono_left)
  finally show ?thesis .
qed

lemma (in ordered_term) lookup_mult_scalar_lt_lt:
  "lookup (p \<odot> q) (punit.lt p \<oplus> lt q) = punit.lc p * lc q"
proof (induct p rule: punit.poly_mapping_tail_induct)
  case 0
  show ?case by simp
next
  case step: (tail p)
  from step(1) have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
  let ?t = "punit.lt p \<oplus> lt q"
  show ?case
  proof (cases "is_monomial p")
    case True
    then obtain c t where "c \<noteq> 0" and "punit.lt p = t" and "punit.lc p = c" and p_eq: "p = monomial c t"
      by (rule punit.is_monomial_monomial_ordered)
    hence "p \<odot> q = monom_mult (punit.lc p) (punit.lt p) q" by (simp add: mult_scalar_monomial)
    thus ?thesis by (simp add: lookup_monom_mult_plus lc_def)
  next
    case False
    have "punit.lt (punit.tail p) \<noteq> punit.lt p"
    proof (simp add: punit.tail_def punit.lt_lower_eq_iff, rule)
      assume "punit.lt p = 0"
      have "keys p \<subseteq> {punit.lt p}"
      proof (rule, simp)
        fix s
        assume "s \<in> keys p"
        hence "s \<preceq> punit.lt p" by (rule punit.lt_max_keys)
        moreover have "punit.lt p \<preceq> s" unfolding \<open>punit.lt p = 0\<close> by (rule zero_min)
        ultimately show "s = punit.lt p" by simp
      qed
      hence "card (keys p) = 0 \<or> card (keys p) = 1" using subset_singletonD by fastforce
      thus False
      proof
        assume "card (keys p) = 0"
        hence "p = 0" by (meson card_0_eq keys_eq_empty finite_keys) 
        with step(1) show False ..
      next
        assume "card (keys p) = 1"
        with False show False unfolding is_monomial_def ..
      qed
    qed
    with punit.lt_lower[of p "punit.lt p"] have "punit.lt (punit.tail p) \<prec> punit.lt p"
      by (simp add: punit.tail_def)
    have eq: "lookup ((punit.tail p) \<odot> q) ?t = 0"
    proof (rule ccontr)
      assume "lookup ((punit.tail p) \<odot> q) ?t \<noteq> 0"
      hence "?t \<preceq>\<^sub>t punit.lt (punit.tail p) \<oplus> lt q"
        by (meson in_keys_mult_scalar_le lookup_not_eq_zero_eq_in_keys) 
      hence "punit.lt p \<preceq> punit.lt (punit.tail p)" by (rule ord_term_canc_left)
      also have "... \<prec> punit.lt p" by fact
      finally show False ..
    qed
    from step(2) have "lookup (monom_mult (punit.lc p) (punit.lt p) q) ?t = punit.lc p * lc q"
      by (simp only: lookup_monom_mult_plus lc_def)
    thus ?thesis by (simp add: mult_scalar_tail_rec_left[of p q] lookup_add eq)
  qed
qed

lemma lookup_mult_scalar_tt_tt: "lookup (p \<odot> q) (punit.tt p \<oplus> tt q) = punit.tc p * tc q"
proof (induct p rule: punit.poly_mapping_tail_induct)
  case 0
  show ?case by simp
next
  case step: (tail p)
  from step(1) have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
  let ?t = "punit.tt p \<oplus> tt q"
  show ?case
  proof (cases "is_monomial p")
    case True
    then obtain c t where "c \<noteq> 0" and "punit.lt p = t" and "punit.lc p = c" and p_eq: "p = monomial c t"
      by (rule punit.is_monomial_monomial_ordered)
    from \<open>c \<noteq> 0\<close> have "punit.tt p = t" and "punit.tc p = c" by (simp_all add: p_eq punit.tt_monomial)
    with p_eq have "p \<odot> q = monom_mult (punit.tc p) (punit.tt p) q" by (simp add: mult_scalar_monomial)
    thus ?thesis by (simp add: lookup_monom_mult_plus tc_def)
  next
    case False
    from step(1) have "keys p \<noteq> {}" by simp
    with finite_keys have "card (keys p) \<noteq> 0" by auto
    with False have "2 \<le> card (keys p)" unfolding is_monomial_def by linarith
    then obtain s t where "s \<in> keys p" and "t \<in> keys p" and "s \<prec> t"
      by (metis (mono_tags, lifting) card_empty card_infinite card_insert_disjoint card_mono empty_iff
          finite.emptyI insertCI lessI not_less numeral_2_eq_2 ordered_powerprod_lin.infinite_growing
          ordered_powerprod_lin.neqE preorder_class.less_le_trans subsetI)
    from this(1) this(3) have "punit.tt p \<prec> t" by (rule punit.tt_less)
    also from \<open>t \<in> keys p\<close> have "t \<preceq> punit.lt p" by (rule punit.lt_max_keys)
    finally have "punit.tt p \<prec> punit.lt p" .
    hence tt_tail: "punit.tt (punit.tail p) = punit.tt p" and tc_tail: "punit.tc (punit.tail p) = punit.tc p"
      unfolding punit.tail_def by (rule punit.tt_lower, rule punit.tc_lower)
    have eq: "lookup (monom_mult (punit.lc p) (punit.lt p) q) ?t = 0"
    proof (rule ccontr)
      assume "lookup (monom_mult (punit.lc p) (punit.lt p) q) ?t \<noteq> 0"
      hence "punit.lt p \<oplus> tt q \<preceq>\<^sub>t ?t"
        by (meson in_keys_iff in_keys_monom_mult_ge) 
      hence "punit.lt p \<preceq> punit.tt p" by (rule ord_term_canc_left)
      also have "... \<prec> punit.lt p" by fact
      finally show False ..
    qed
    from step(2) have "lookup (punit.tail p \<odot> q) ?t = punit.tc p * tc q" by (simp only: tt_tail tc_tail)
    thus ?thesis by (simp add: mult_scalar_tail_rec_left[of p q] lookup_add eq)
  qed
qed

lemma lt_mult_scalar:
  assumes "p \<noteq> 0" and "q \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "lt (p \<odot> q) = punit.lt p \<oplus> lt q"
proof (rule lt_eqI_keys, simp only: in_keys_iff lookup_mult_scalar_lt_lt)
  from assms(1) have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
  moreover from assms(2) have "lc q \<noteq> 0" by (rule lc_not_0)
  ultimately show "punit.lc p * lc q \<noteq> 0" by simp
qed (rule in_keys_mult_scalar_le)

lemma tt_mult_scalar:
  assumes "p \<noteq> 0" and "q \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "tt (p \<odot> q) = punit.tt p \<oplus> tt q"
proof (rule tt_eqI, simp only: in_keys_iff lookup_mult_scalar_tt_tt)
  from assms(1) have "punit.tc p \<noteq> 0" by (rule punit.tc_not_0)
  moreover from assms(2) have "tc q \<noteq> 0" by (rule tc_not_0)
  ultimately show "punit.tc p * tc q \<noteq> 0" by simp
qed (rule in_keys_mult_scalar_ge)

lemma lc_mult_scalar: "lc (p \<odot> q) = punit.lc p * lc (q::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: lc_def)
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp add: lc_def)
  next
    case False
    with \<open>p \<noteq> 0\<close> show ?thesis by (simp add: lc_def lt_mult_scalar lookup_mult_scalar_lt_lt)
  qed
qed

lemma tc_mult_scalar: "tc (p \<odot> q) = punit.tc p * tc (q::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: tc_def)
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp add: tc_def)
  next
    case False
    with \<open>p \<noteq> 0\<close> show ?thesis by (simp add: tc_def tt_mult_scalar lookup_mult_scalar_tt_tt)
  qed
qed

lemma mult_scalar_not_zero:
  assumes "p \<noteq> 0" and "q \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "p \<odot> q \<noteq> 0"
proof
  assume "p \<odot> q = 0"
  hence "0 = lc (p \<odot> q)" by (simp add: lc_def)
  also have "... = punit.lc p * lc q" by (rule lc_mult_scalar)
  finally have "punit.lc p * lc q = 0" by simp
  moreover from assms(1) have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
  moreover from assms(2) have "lc q \<noteq> 0" by (rule lc_not_0)
  ultimately show False by simp
qed

end (* ordered_term_powerprod *)

context ordered_powerprod
begin

lemmas in_keys_times_le = punit.in_keys_mult_scalar_le[simplified]
lemmas in_keys_times_ge = punit.in_keys_mult_scalar_ge[simplified]
lemmas lookup_times_lp_lp = punit.lookup_mult_scalar_lt_lt[simplified]
lemmas lookup_times_tp_tp = punit.lookup_mult_scalar_tt_tt[simplified]
lemmas lookup_times_monomial_right_plus = punit.lookup_mult_scalar_monomial_right_plus[simplified]
lemmas lookup_times_monomial_right = punit.lookup_mult_scalar_monomial_right[simplified]
lemmas lp_times = punit.lt_mult_scalar[simplified]
lemmas tp_times = punit.tt_mult_scalar[simplified]
lemmas lc_times = punit.lc_mult_scalar[simplified]
lemmas tc_times = punit.tc_mult_scalar[simplified]
lemmas times_not_zero = punit.mult_scalar_not_zero[simplified]
lemmas times_tail_rec_left = punit.mult_scalar_tail_rec_left[simplified]
lemmas times_tail_rec_right = punit.mult_scalar_tail_rec_right[simplified]
lemmas punit_in_keys_monom_mult_le = punit.in_keys_monom_mult_le[simplified]
lemmas punit_in_keys_monom_mult_ge = punit.in_keys_monom_mult_ge[simplified]
lemmas lp_monom_mult = punit.lt_monom_mult[simplified]
lemmas tp_monom_mult = punit.tt_monom_mult[simplified]

end

subsection \<open>@{term dgrad_p_set} and @{term dgrad_p_set_le}\<close>

locale gd_term =
    ordered_term pair_of_term term_of_pair ord ord_strict ord_term ord_term_strict
      for pair_of_term::"'t \<Rightarrow> ('a::graded_dickson_powerprod \<times> 'k::{the_min,wellorder})"
      and term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
      and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
      and ord_strict (infixl "\<prec>" 50)
      and ord_term::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<preceq>\<^sub>t" 50)
      and ord_term_strict::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<prec>\<^sub>t" 50)
begin

sublocale gd_powerprod ..

lemma adds_term_antisym:
  assumes "u adds\<^sub>t v" and "v adds\<^sub>t u"
  shows "u = v"
  using assms unfolding adds_term_def using adds_antisym by (metis term_of_pair_pair)

definition dgrad_p_set :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) set"
  where "dgrad_p_set d m = {p. pp_of_term ` keys p \<subseteq> dgrad_set d m}"

definition dgrad_p_set_le :: "('a \<Rightarrow> nat) \<Rightarrow> (('t \<Rightarrow>\<^sub>0 'b) set) \<Rightarrow> (('t \<Rightarrow>\<^sub>0 'b::zero) set) \<Rightarrow> bool"
  where "dgrad_p_set_le d F G \<longleftrightarrow> (dgrad_set_le d (pp_of_term ` Keys F) (pp_of_term ` Keys G))"

lemma in_dgrad_p_set_iff: "p \<in> dgrad_p_set d m \<longleftrightarrow> (\<forall>v\<in>keys p. d (pp_of_term v) \<le> m)"
  by (auto simp add: dgrad_p_set_def dgrad_set_def)

lemma dgrad_p_setI [intro]:
  assumes "\<And>v. v \<in> keys p \<Longrightarrow> d (pp_of_term v) \<le> m"
  shows "p \<in> dgrad_p_set d m"
  using assms by (auto simp: in_dgrad_p_set_iff)

lemma dgrad_p_setD:
  assumes "p \<in> dgrad_p_set d m" and "v \<in> keys p"
  shows "d (pp_of_term v) \<le> m"
  using assms by (simp only: in_dgrad_p_set_iff)

lemma zero_in_dgrad_p_set: "0 \<in> dgrad_p_set d m"
  by (rule, simp)

lemma dgrad_p_set_zero [simp]: "dgrad_p_set (\<lambda>_. 0) m = UNIV"
  by auto

lemma subset_dgrad_p_set_zero: "F \<subseteq> dgrad_p_set (\<lambda>_. 0) m"
  by simp

lemma dgrad_p_set_subset:
  assumes "m \<le> n"
  shows "dgrad_p_set d m \<subseteq> dgrad_p_set d n"
  using assms by (auto simp: dgrad_p_set_def dgrad_set_def)

lemma dgrad_p_setD_lp:
  assumes "p \<in> dgrad_p_set d m" and "p \<noteq> 0"
  shows "d (lp p) \<le> m"
  by (rule dgrad_p_setD, fact, rule lt_in_keys, fact)

lemma dgrad_p_set_exhaust_expl:
  assumes "finite F"
  shows "F \<subseteq> dgrad_p_set d (Max (d ` pp_of_term ` Keys F))"
proof
  fix f
  assume "f \<in> F"
  from assms have "finite (Keys F)" by (rule finite_Keys)
  have fin: "finite (d ` pp_of_term ` Keys F)" by (intro finite_imageI, fact)
  show "f \<in> dgrad_p_set d (Max (d ` pp_of_term ` Keys F))"
  proof (rule dgrad_p_setI)
    fix v
    assume "v \<in> keys f"
    from this \<open>f \<in> F\<close> have "v \<in> Keys F" by (rule in_KeysI)
    hence "d (pp_of_term v) \<in> d ` pp_of_term ` Keys F" by simp
    with fin show "d (pp_of_term v) \<le> Max (d ` pp_of_term ` Keys F)" by (rule Max_ge)
  qed
qed

lemma dgrad_p_set_exhaust:
  assumes "finite F"
  obtains m where "F \<subseteq> dgrad_p_set d m"
proof
  from assms show "F \<subseteq> dgrad_p_set d (Max (d ` pp_of_term ` Keys F))" by (rule dgrad_p_set_exhaust_expl)
qed

lemma dgrad_p_set_insert:
  assumes "F \<subseteq> dgrad_p_set d m"
  obtains n where "m \<le> n" and "f \<in> dgrad_p_set d n" and "F \<subseteq> dgrad_p_set d n"
proof -
  have "finite {f}" by simp
  then obtain m1 where "{f} \<subseteq> dgrad_p_set d m1" by (rule dgrad_p_set_exhaust)
  hence "f \<in> dgrad_p_set d m1" by simp
  define n where "n = ord_class.max m m1"
  have "m \<le> n" and "m1 \<le> n" by (simp_all add: n_def)
  from this(1) show ?thesis
  proof
    from \<open>m1 \<le> n\<close> have "dgrad_p_set d m1 \<subseteq> dgrad_p_set d n" by (rule dgrad_p_set_subset)
    with \<open>f \<in> dgrad_p_set d m1\<close> show "f \<in> dgrad_p_set d n" ..
  next
    from \<open>m \<le> n\<close> have "dgrad_p_set d m \<subseteq> dgrad_p_set d n" by (rule dgrad_p_set_subset)
    with assms show "F \<subseteq> dgrad_p_set d n" by (rule subset_trans)
  qed
qed

lemma dgrad_p_set_leI:
  assumes "\<And>f. f \<in> F \<Longrightarrow> dgrad_p_set_le d {f} G"
  shows "dgrad_p_set_le d F G"
  unfolding dgrad_p_set_le_def dgrad_set_le_def
proof
  fix s
  assume "s \<in> pp_of_term ` Keys F"
  then obtain v where "v \<in> Keys F" and "s = pp_of_term v" ..
  from this(1) obtain f where "f \<in> F" and "v \<in> keys f" by (rule in_KeysE)
  from this(2) have "s \<in> pp_of_term ` Keys {f}" by (simp add: \<open>s = pp_of_term v\<close> Keys_insert)
  from \<open>f \<in> F\<close> have "dgrad_p_set_le d {f} G" by (rule assms)
  from this \<open>s \<in> pp_of_term ` Keys {f}\<close> show "\<exists>t\<in>pp_of_term ` Keys G. d s \<le> d t"
    unfolding dgrad_p_set_le_def dgrad_set_le_def ..
qed

lemma dgrad_p_set_le_trans [trans]:
  assumes "dgrad_p_set_le d F G" and "dgrad_p_set_le d G H"
  shows "dgrad_p_set_le d F H"
  using assms unfolding dgrad_p_set_le_def by (rule dgrad_set_le_trans)

lemma dgrad_p_set_le_subset:
  assumes "F \<subseteq> G"
  shows "dgrad_p_set_le d F G"
  unfolding dgrad_p_set_le_def by (rule dgrad_set_le_subset, rule image_mono, rule Keys_mono, fact)

lemma dgrad_p_set_leI_insert_keys:
  assumes "dgrad_p_set_le d F G" and "dgrad_set_le d (pp_of_term ` keys f) (pp_of_term ` Keys G)"
  shows "dgrad_p_set_le d (insert f F) G"
  using assms by (simp add: dgrad_p_set_le_def Keys_insert dgrad_set_le_Un image_Un)

lemma dgrad_p_set_leI_insert:
  assumes "dgrad_p_set_le d F G" and "dgrad_p_set_le d {f} G"
  shows "dgrad_p_set_le d (insert f F) G"
  using assms by (simp add: dgrad_p_set_le_def Keys_insert dgrad_set_le_Un image_Un)

lemma dgrad_p_set_leI_Un:
  assumes "dgrad_p_set_le d F1 G" and "dgrad_p_set_le d F2 G"
  shows "dgrad_p_set_le d (F1 \<union> F2) G"
  using assms by (auto simp: dgrad_p_set_le_def dgrad_set_le_def Keys_Un)

lemma dgrad_p_set_le_dgrad_p_set:
  assumes "dgrad_p_set_le d F G" and "G \<subseteq> dgrad_p_set d m"
  shows "F \<subseteq> dgrad_p_set d m"
proof
  fix f
  assume "f \<in> F"
  show "f \<in> dgrad_p_set d m"
  proof (rule dgrad_p_setI)
    fix v
    assume "v \<in> keys f"
    from this \<open>f \<in> F\<close> have "v \<in> Keys F" by (rule in_KeysI)
    hence "pp_of_term v \<in> pp_of_term ` Keys F" by simp
    with assms(1) obtain s where "s \<in> pp_of_term ` Keys G" and "d (pp_of_term v) \<le> d s"
      unfolding dgrad_p_set_le_def by (rule dgrad_set_leE)
    from this(1) obtain u where "u \<in> Keys G" and s: "s = pp_of_term u" ..
    from this(1) obtain g where "g \<in> G" and "u \<in> keys g" by (rule in_KeysE)
    from this(1) assms(2) have "g \<in> dgrad_p_set d m" ..
    from this \<open>u \<in> keys g\<close> have "d s \<le> m" unfolding s by (rule dgrad_p_setD)
    with \<open>d (pp_of_term v) \<le> d s\<close> show "d (pp_of_term v) \<le> m" by (rule le_trans)
  qed
qed

lemma dgrad_p_set_le_except: "dgrad_p_set_le d {except p S} {p}"
  by (auto simp add: dgrad_p_set_le_def Keys_insert keys_except intro: dgrad_set_le_subset)

lemma dgrad_p_set_le_tail: "dgrad_p_set_le d {tail p} {p}"
  by (simp only: tail_def lower_def, fact dgrad_p_set_le_except)

lemma dgrad_p_set_le_plus: "dgrad_p_set_le d {p + q} {p, q}"
  by (simp add: dgrad_p_set_le_def Keys_insert, rule dgrad_set_le_subset, rule image_mono, fact Poly_Mapping.keys_add)

lemma dgrad_p_set_le_uminus: "dgrad_p_set_le d {-p} {p}"
  by (simp add: dgrad_p_set_le_def Keys_insert keys_uminus, fact dgrad_set_le_refl)

lemma dgrad_p_set_le_minus: "dgrad_p_set_le d {p - q} {p, q}"
  by (simp add: dgrad_p_set_le_def Keys_insert, rule dgrad_set_le_subset, rule image_mono, fact keys_minus)

lemma dgrad_set_le_monom_mult:
  assumes "dickson_grading d"
  shows "dgrad_set_le d (pp_of_term ` keys (monom_mult c t p)) (insert t (pp_of_term ` keys p))"
proof (rule dgrad_set_leI)
  fix s
  assume "s \<in> pp_of_term ` keys (monom_mult c t p)"
  with keys_monom_mult_subset have "s \<in> pp_of_term ` ((\<oplus>) t ` keys p)" by fastforce
  then obtain v where "v \<in> keys p" and s: "s = pp_of_term (t \<oplus> v)" by fastforce
  have "d s = ord_class.max (d t) (d (pp_of_term v))"
    by (simp only: s pp_of_term_splus dickson_gradingD1[OF assms(1)])
  hence "d s = d t \<or> d s = d (pp_of_term v)" by auto
  thus "\<exists>t\<in>insert t (pp_of_term ` keys p). d s \<le> d t"
  proof
    assume "d s = d t"
    thus ?thesis by simp
  next
    assume "d s = d (pp_of_term v)"
    show ?thesis
    proof
      from \<open>d s = d (pp_of_term v)\<close> show "d s \<le> d (pp_of_term v)" by simp
    next
      from \<open>v \<in> keys p\<close> show "pp_of_term v \<in> insert t (pp_of_term ` keys p)" by simp
    qed
  qed
qed

lemma dgrad_p_set_closed_plus:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "p + q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_plus have "{p + q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_uminus:
  assumes "p \<in> dgrad_p_set d m"
  shows "-p \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_uminus have "{-p} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms show "{p} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_minus:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "p - q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_minus have "{p - q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_monom_mult:
  assumes "dickson_grading d" and "d t \<le> m" and "p \<in> dgrad_p_set d m"
  shows "monom_mult c t p \<in> dgrad_p_set d m"
proof (rule dgrad_p_setI)
  fix v
  assume "v \<in> keys (monom_mult c t p)"
  hence "pp_of_term v \<in> pp_of_term ` keys (monom_mult c t p)" by simp
  with dgrad_set_le_monom_mult[OF assms(1)] obtain s where "s \<in> insert t (pp_of_term ` keys p)"
    and "d (pp_of_term v) \<le> d s" by (rule dgrad_set_leE)
  from this(1) have "s = t \<or> s \<in> pp_of_term ` keys p" by simp
  thus "d (pp_of_term v) \<le> m"
  proof
    assume "s = t"
    with \<open>d (pp_of_term v) \<le> d s\<close> assms(2) show ?thesis by simp
  next
    assume "s \<in> pp_of_term ` keys p"
    then obtain u where "u \<in> keys p" and "s = pp_of_term u" ..
    from assms(3) this(1) have "d s \<le> m" unfolding \<open>s = pp_of_term u\<close> by (rule dgrad_p_setD)
    with \<open>d (pp_of_term v) \<le> d s\<close> show ?thesis by (rule le_trans)
  qed
qed

lemma dgrad_p_set_closed_monom_mult_zero:
  assumes "p \<in> dgrad_p_set d m"
  shows "monom_mult c 0 p \<in> dgrad_p_set d m"
proof (rule dgrad_p_setI)
  fix v
  assume "v \<in> keys (monom_mult c 0 p)"
  hence "pp_of_term v \<in> pp_of_term ` keys (monom_mult c 0 p)" by simp
  then obtain u where "u \<in> keys (monom_mult c 0 p)" and eq: "pp_of_term v = pp_of_term u" ..
  from this(1) have "u \<in> keys p" by (metis keys_monom_multE splus_zero)
  with assms have "d (pp_of_term u) \<le> m" by (rule dgrad_p_setD)
  thus "d (pp_of_term v) \<le> m" by (simp only: eq)
qed

lemma dgrad_p_set_closed_except:
  assumes "p \<in> dgrad_p_set d m"
  shows "except p S \<in> dgrad_p_set d m"
  by (rule dgrad_p_setI, rule dgrad_p_setD, rule assms, simp add: keys_except)

lemma dgrad_p_set_closed_tail:
  assumes "p \<in> dgrad_p_set d m"
  shows "tail p \<in> dgrad_p_set d m"
  unfolding tail_def lower_def using assms by (rule dgrad_p_set_closed_except)

subsection \<open>Dickson's Lemma for Sequences of Terms\<close>

lemma Dickson_term:
  assumes "dickson_grading d" and "finite K"
  shows "almost_full_on (adds\<^sub>t) {t. pp_of_term t \<in> dgrad_set d m \<and> component_of_term t \<in> K}"
    (is "almost_full_on _ ?A")
proof (rule almost_full_onI)
  fix seq :: "nat \<Rightarrow> 't"
  assume *: "\<forall>i. seq i \<in> ?A"
  define seq' where "seq' = (\<lambda>i. (pp_of_term (seq i), component_of_term (seq i)))"
  have "pp_of_term ` ?A \<subseteq> {x. d x \<le> m}" by (auto dest: dgrad_setD)
  moreover from assms(1) have "almost_full_on (adds) {x. d x \<le> m}" by (rule dickson_gradingD2)
  ultimately have "almost_full_on (adds) (pp_of_term ` ?A)" by (rule almost_full_on_subset)
  moreover have "almost_full_on (=) (component_of_term ` ?A)"
  proof (rule eq_almost_full_on_finite_set)
    have "component_of_term ` ?A \<subseteq> K" by blast
    thus "finite (component_of_term ` ?A)" using assms(2) by (rule finite_subset)
  qed
  ultimately have "almost_full_on (prod_le (adds) (=)) (pp_of_term ` ?A \<times> component_of_term ` ?A)"
    by (rule almost_full_on_Sigma)
  moreover from * have "\<And>i. seq' i \<in> pp_of_term ` ?A \<times> component_of_term ` ?A" by (simp add: seq'_def)
  ultimately obtain i j where "i < j" and "prod_le (adds) (=) (seq' i) (seq' j)"
    by (rule almost_full_onD)
  from this(2) have "seq i adds\<^sub>t seq j" by (simp add: seq'_def prod_le_def adds_term_def)
  with \<open>i < j\<close> show "good (adds\<^sub>t) seq" by (rule goodI)
qed

corollary Dickson_termE:
  assumes "dickson_grading d" and "finite (component_of_term ` range (f::nat \<Rightarrow> 't))"
    and "pp_of_term ` range f \<subseteq> dgrad_set d m"
  obtains i j where "i < j" and "f i adds\<^sub>t f j"
proof -
  let ?A = "{t. pp_of_term t \<in> dgrad_set d m \<and> component_of_term t \<in> component_of_term ` range f}"
  from assms(1, 2) have "almost_full_on (adds\<^sub>t) ?A" by (rule Dickson_term)
  moreover from assms(3) have "\<And>i. f i \<in> ?A" by blast
  ultimately obtain i j where "i < j" and "f i adds\<^sub>t f j" by (rule almost_full_onD)
  thus ?thesis ..
qed

lemma ex_finite_adds_term:
  assumes "dickson_grading d" and "finite (component_of_term ` S)" and "pp_of_term ` S \<subseteq> dgrad_set d m"
  obtains T where "finite T" and "T \<subseteq> S" and "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds\<^sub>t s)"
proof -
  let ?A = "{t. pp_of_term t \<in> dgrad_set d m \<and> component_of_term t \<in> component_of_term ` S}"
  have "reflp ((adds\<^sub>t)::'t \<Rightarrow> _)" by (simp add: reflp_def adds_term_refl)
  moreover have "almost_full_on (adds\<^sub>t) S"
  proof (rule almost_full_on_subset)
    from assms(3) show "S \<subseteq> ?A" by blast
  next
    from assms(1, 2) show "almost_full_on (adds\<^sub>t) ?A" by (rule Dickson_term)
  qed
  ultimately obtain T where "finite T" and "T \<subseteq> S" and "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds\<^sub>t s)"
    by (rule almost_full_on_finite_subsetE, blast)
  thus ?thesis ..
qed

subsection \<open>Well-foundedness\<close>

definition dickson_less_v :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> bool"
  where "dickson_less_v d m v u \<longleftrightarrow> (d (pp_of_term v) \<le> m \<and> d (pp_of_term u) \<le> m \<and> v \<prec>\<^sub>t u)"

definition dickson_less_p :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "dickson_less_p d m p q \<longleftrightarrow> ({p, q} \<subseteq> dgrad_p_set d m \<and> p \<prec>\<^sub>p q)"

lemma dickson_less_vI:
  assumes "d (pp_of_term v) \<le> m" and "d (pp_of_term u) \<le> m" and "v \<prec>\<^sub>t u"
  shows "dickson_less_v d m v u"
  using assms by (simp add: dickson_less_v_def)

lemma dickson_less_vD1:
  assumes "dickson_less_v d m v u"
  shows "d (pp_of_term v) \<le> m"
  using assms by (simp add: dickson_less_v_def)

lemma dickson_less_vD2:
  assumes "dickson_less_v d m v u"
  shows "d (pp_of_term u) \<le> m"
  using assms by (simp add: dickson_less_v_def)

lemma dickson_less_vD3:
  assumes "dickson_less_v d m v u"
  shows "v \<prec>\<^sub>t u"
  using assms by (simp add: dickson_less_v_def)

lemma dickson_less_v_irrefl: "\<not> dickson_less_v d m v v"
  by (simp add: dickson_less_v_def)

lemma dickson_less_v_trans:
  assumes "dickson_less_v d m v u" and "dickson_less_v d m u w"
  shows "dickson_less_v d m v w"
  using assms by (auto simp add: dickson_less_v_def)

lemma wf_dickson_less_v_aux1:
  assumes "dickson_grading d" and "\<And>i::nat. dickson_less_v d m (seq (Suc i)) (seq i)"
  obtains i where "\<And>j. j > i \<Longrightarrow> component_of_term (seq j) < component_of_term (seq i)"
proof -
  let ?Q = "pp_of_term ` range seq"
  have "pp_of_term (seq 0) \<in> ?Q" by simp
  with wf_dickson_less[OF assms(1)] obtain t where "t \<in> ?Q" and *: "\<And>s. dickson_less d m s t \<Longrightarrow> s \<notin> ?Q"
    by (rule wfE_min[to_pred], blast)
  from this(1) obtain i where t: "t = pp_of_term (seq i)" by fastforce
  show ?thesis
  proof
    fix j
    assume "i < j"
    with _ assms(2) have dlv: "dickson_less_v d m (seq j) (seq i)"
    proof (rule transp_sequence)
      from dickson_less_v_trans show "transp (dickson_less_v d m)" by (rule transpI)
    qed
    hence "seq j \<prec>\<^sub>t seq i" by (rule dickson_less_vD3)
    define s where "s = pp_of_term (seq j)"
    have "pp_of_term (seq j) \<in> ?Q" by simp
    hence "\<not> dickson_less d m s t" unfolding s_def using * by blast
    moreover from dlv have "d s \<le> m" and "d t \<le> m" unfolding s_def t
      by (rule dickson_less_vD1, rule dickson_less_vD2)
    ultimately have "t \<preceq> s" by (simp add: dickson_less_def)
    show "component_of_term (seq j) < component_of_term (seq i)"
    proof (rule ccontr, simp only: not_less)
      assume "component_of_term (seq i) \<le> component_of_term (seq j)"
      with \<open>t \<preceq> s\<close> have "seq i \<preceq>\<^sub>t seq j" unfolding s_def t by (rule ord_termI)
      moreover from dlv have "seq j \<prec>\<^sub>t seq i" by (rule dickson_less_vD3)
      ultimately show False by simp
    qed
  qed
qed

lemma wf_dickson_less_v_aux2:
  assumes "dickson_grading d" and "\<And>i::nat. dickson_less_v d m (seq (Suc i)) (seq i)"
    and "\<And>i::nat. component_of_term (seq i) < k"
  shows thesis
  using assms(2, 3)
proof (induct k arbitrary: seq thesis rule: less_induct)
  case (less k)
  from assms(1) less(2) obtain i where *: "\<And>j. j > i \<Longrightarrow> component_of_term (seq j) < component_of_term (seq i)"
    by (rule wf_dickson_less_v_aux1, blast)
  define seq1 where "seq1 = (\<lambda>j. seq (Suc (i + j)))"
  from less(3) show ?case
  proof (rule less(1))
    fix j
    show "dickson_less_v d m (seq1 (Suc j)) (seq1 j)" by (simp add: seq1_def, fact less(2))
  next
    fix j
    show "component_of_term (seq1 j) < component_of_term (seq i)" by (simp add: seq1_def *)
  qed
qed

lemma wf_dickson_less_v:
  assumes "dickson_grading d"
  shows "wfP (dickson_less_v d m)"
proof (rule wfP_chain, rule, elim exE)
  fix seq::"nat \<Rightarrow> 't"
  assume "\<forall>i. dickson_less_v d m (seq (Suc i)) (seq i)"
  hence *: "\<And>i. dickson_less_v d m (seq (Suc i)) (seq i)" ..
  with assms obtain i where **: "\<And>j. j > i \<Longrightarrow> component_of_term (seq j) < component_of_term (seq i)"
    by (rule wf_dickson_less_v_aux1, blast)
  define seq1 where "seq1 = (\<lambda>j. seq (Suc (i + j)))"
  from assms show False
  proof (rule wf_dickson_less_v_aux2)
    fix j
    show "dickson_less_v d m (seq1 (Suc j)) (seq1 j)" by (simp add: seq1_def, fact *)
  next
    fix j
    show "component_of_term (seq1 j) < component_of_term (seq i)" by (simp add: seq1_def **)
  qed
qed

lemma dickson_less_v_zero: "dickson_less_v (\<lambda>_. 0) m = (\<prec>\<^sub>t)"
  by (rule, rule, simp add: dickson_less_v_def)

lemma dickson_less_pI:
  assumes "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m" and "p \<prec>\<^sub>p q"
  shows "dickson_less_p d m p q"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD1:
  assumes "dickson_less_p d m p q"
  shows "p \<in> dgrad_p_set d m"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD2:
  assumes "dickson_less_p d m p q"
  shows "q \<in> dgrad_p_set d m"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_pD3:
  assumes "dickson_less_p d m p q"
  shows "p \<prec>\<^sub>p q"
  using assms by (simp add: dickson_less_p_def)

lemma dickson_less_p_irrefl: "\<not> dickson_less_p d m p p"
  by (simp add: dickson_less_p_def)

lemma dickson_less_p_trans:
  assumes "dickson_less_p d m p q" and "dickson_less_p d m q r"
  shows "dickson_less_p d m p r"
  using assms by (auto simp add: dickson_less_p_def)

lemma dickson_less_p_mono:
  assumes "dickson_less_p d m p q" and "m \<le> n"
  shows "dickson_less_p d n p q"
proof -
  from assms(2) have "dgrad_p_set d m \<subseteq> dgrad_p_set d n" by (rule dgrad_p_set_subset)
  moreover from assms(1) have "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m" and "p \<prec>\<^sub>p q"
    by (rule dickson_less_pD1, rule dickson_less_pD2, rule dickson_less_pD3)
  ultimately have "p \<in> dgrad_p_set d n" and "q \<in> dgrad_p_set d n" by auto
  from this \<open>p \<prec>\<^sub>p q\<close> show ?thesis by (rule dickson_less_pI)
qed

lemma dickson_less_p_zero: "dickson_less_p (\<lambda>_. 0) m = (\<prec>\<^sub>p)"
  by (rule, rule, simp add: dickson_less_p_def)

lemma wf_dickson_less_p_aux:
  assumes "dickson_grading d"
  assumes "x \<in> Q" and "\<forall>y\<in>Q. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) u)"
  shows "\<exists>p\<in>Q. (\<forall>q\<in>Q. \<not> dickson_less_p d m q p)"
  using assms(2) assms(3)
proof (induct u arbitrary: x Q rule: wfP_induct[OF wf_dickson_less_v, OF assms(1)])
  fix u::'t and x::"'t \<Rightarrow>\<^sub>0 'b" and Q::"('t \<Rightarrow>\<^sub>0 'b) set"
  assume hyp: "\<forall>u0. dickson_less_v d m u0 u \<longrightarrow> (\<forall>x0 Q0::('t \<Rightarrow>\<^sub>0 'b) set. x0 \<in> Q0 \<longrightarrow>
                            (\<forall>y\<in>Q0. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) u0)) \<longrightarrow>
                            (\<exists>p\<in>Q0. \<forall>q\<in>Q0. \<not> dickson_less_p d m q p))"
  assume "x \<in> Q"
  assume "\<forall>y\<in>Q. y \<noteq> 0 \<longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) u)"
  hence bounded: "\<And>y. y \<in> Q \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> (y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) u)" by auto
  show "\<exists>p\<in>Q. \<forall>q\<in>Q. \<not> dickson_less_p d m q p"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      fix q::"'t \<Rightarrow>\<^sub>0 'b"
      assume "dickson_less_p d m q 0"
      hence "q \<prec>\<^sub>p 0" by (rule dickson_less_pD3)
      thus False using ord_p_zero_min[of q] by simp
    next
      from True show "0 \<in> Q" .
    qed
  next
    case False
    define Q1 where "Q1 = {lt p | p. p \<in> Q}"
    from \<open>x \<in> Q\<close> have "lt x \<in> Q1" unfolding Q1_def by auto
    with wf_dickson_less_v[OF assms(1)] obtain v
      where "v \<in> Q1" and v_min_1: "\<And>q. dickson_less_v d m q v \<Longrightarrow> q \<notin> Q1"
      by (rule wfE_min[to_pred], auto)
    have v_min: "\<And>q. q \<in> Q \<Longrightarrow> \<not> dickson_less_v d m (lt q) v"
    proof -
      fix q
      assume "q \<in> Q"
      hence "lt q \<in> Q1" unfolding Q1_def by auto
      thus "\<not> dickson_less_v d m (lt q) v" using v_min_1 by auto
    qed
    from \<open>v \<in> Q1\<close> obtain p where "lt p = v" and "p \<in> Q" unfolding Q1_def by auto
    hence "p \<noteq> 0" using False by auto
    with \<open>p \<in> Q\<close> have "p \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt p) u" by (rule bounded)
    hence "p \<in> dgrad_p_set d m" and "dickson_less_v d m (lt p) u" by simp_all
    moreover from this(1) \<open>p \<noteq> 0\<close> have "d (pp_of_term (lt p)) \<le> m" by (rule dgrad_p_setD_lp)
    ultimately have "d (pp_of_term v) \<le> m" by (simp only: \<open>lt p = v\<close>)
    define Q2 where "Q2 = {tail p | p. p \<in> Q \<and> lt p = v}"
    from \<open>p \<in> Q\<close> \<open>lt p = v\<close> have "tail p \<in> Q2" unfolding Q2_def by auto
    have "\<forall>q\<in>Q2. q \<noteq> 0 \<longrightarrow> (q \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt q) (lt p))"
    proof (intro ballI impI)
      fix q
      assume "q \<in> Q2"
      then obtain q0 where q: "q = tail q0" and "lt q0 = lt p" and "q0 \<in> Q"
        using \<open>lt p = v\<close> by (auto simp add: Q2_def)
      assume "q \<noteq> 0"
      hence "tail q0 \<noteq> 0" using \<open>q = tail q0\<close> by simp
      hence "q0 \<noteq> 0" by auto
      with \<open>q0 \<in> Q\<close> have "q0 \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt q0) u" by (rule bounded)
      hence "q0 \<in> dgrad_p_set d m" and "dickson_less_v d m (lt q0) u" by simp_all
      from this(1) have "q \<in> dgrad_p_set d m" unfolding q by (rule dgrad_p_set_closed_tail)
      show "q \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt q) (lt p)"
      proof
        show "dickson_less_v d m (lt q) (lt p)"
        proof (rule dickson_less_vI)
          from \<open>q \<in> dgrad_p_set d m\<close> \<open>q \<noteq> 0\<close> show "d (pp_of_term (lt q)) \<le> m" by (rule dgrad_p_setD_lp)
        next
          from \<open>dickson_less_v d m (lt p) u\<close> show "d (pp_of_term (lt p)) \<le> m" by (rule dickson_less_vD1)
        next
          from lt_tail[OF \<open>tail q0 \<noteq> 0\<close>] \<open>q = tail q0\<close> \<open>lt q0 = lt p\<close> show "lt q \<prec>\<^sub>t lt p" by simp
        qed
      qed fact
    qed
    with hyp \<open>dickson_less_v d m (lt p) u\<close> \<open>tail p \<in> Q2\<close> have "\<exists>p\<in>Q2. \<forall>q\<in>Q2. \<not> dickson_less_p d m q p"
      by blast
    then obtain q where "q \<in> Q2" and q_min: "\<forall>r\<in>Q2. \<not> dickson_less_p d m r q" ..
    from \<open>q \<in> Q2\<close> obtain q0 where "q = tail q0" and "q0 \<in> Q" and "lt q0 = v" unfolding Q2_def by auto
    from q_min \<open>q = tail q0\<close> have q0_tail_min: "\<And>r. r \<in> Q2 \<Longrightarrow> \<not> dickson_less_p d m r (tail q0)" by simp
    from \<open>q0 \<in> Q\<close> show ?thesis
    proof
      show "\<forall>r\<in>Q. \<not> dickson_less_p d m r q0"
      proof (intro ballI notI)
        fix r
        assume "dickson_less_p d m r q0"
        hence "r \<in> dgrad_p_set d m" and "q0 \<in> dgrad_p_set d m" and "r \<prec>\<^sub>p q0"
          by (rule dickson_less_pD1, rule dickson_less_pD2, rule dickson_less_pD3)
        from this(3) have "lt r \<preceq>\<^sub>t lt q0" by (simp add: ord_p_lt)
        with \<open>lt q0 = v\<close> have "lt r \<preceq>\<^sub>t v" by simp
        assume "r \<in> Q"
        hence "\<not> dickson_less_v d m (lt r) v" by (rule v_min)
        from False \<open>r \<in> Q\<close> have "r \<noteq> 0" using False by blast
        with \<open>r \<in> dgrad_p_set d m\<close> have "d (pp_of_term (lt r)) \<le> m" by (rule dgrad_p_setD_lp)
        have "\<not> lt r \<prec>\<^sub>t v"
        proof
          assume "lt r \<prec>\<^sub>t v"
          with \<open>d (pp_of_term (lt r)) \<le> m\<close> \<open>d (pp_of_term v) \<le> m\<close> have "dickson_less_v d m (lt r) v"
            by (rule dickson_less_vI)
          with \<open>\<not> dickson_less_v d m (lt r) v\<close> show False ..
        qed
        with \<open>lt r \<preceq>\<^sub>t v\<close> have "lt r = v" by simp
        with \<open>r \<in> Q\<close> have "tail r \<in> Q2" by (auto simp add: Q2_def)
        have "dickson_less_p d m (tail r) (tail q0)"
        proof (rule dickson_less_pI)
          show "tail r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_tail, fact)
        next
          show "tail q0 \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_tail, fact)
        next
          have "lt r = lt q0" by (simp only: \<open>lt r = v\<close> \<open>lt q0 = v\<close>)
          from \<open>r \<noteq> 0\<close> this \<open>r \<prec>\<^sub>p q0\<close> show "tail r \<prec>\<^sub>p tail q0" by (rule ord_p_tail)
        qed
        with q0_tail_min[OF \<open>tail r \<in> Q2\<close>] show False ..
      qed
    qed
  qed
qed

theorem wf_dickson_less_p:
  assumes "dickson_grading d"
  shows "wfP (dickson_less_p d m)"
proof (rule wfI_min[to_pred])
  fix Q::"('t \<Rightarrow>\<^sub>0 'b) set" and x
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. dickson_less_p d m y z \<longrightarrow> y \<notin> Q"
  proof (cases "0 \<in> Q")
    case True
    show ?thesis
    proof (rule, rule, rule)
      from True show "0 \<in> Q" .
    next
      fix q::"'t \<Rightarrow>\<^sub>0 'b"
      assume "dickson_less_p d m q 0"
      hence "q \<prec>\<^sub>p 0" by (rule dickson_less_pD3)
      thus "q \<notin> Q" using ord_p_zero_min[of q] by simp
    qed
  next
    case False
    show ?thesis
    proof (cases "Q \<subseteq> dgrad_p_set d m")
      case True
      let ?L = "lt ` Q"
      from \<open>x \<in> Q\<close> have "lt x \<in> ?L" by simp
      with wf_dickson_less_v[OF assms] obtain v where "v \<in> ?L"
        and v_min: "\<And>u. dickson_less_v d m u v \<Longrightarrow> u \<notin> ?L" by (rule wfE_min[to_pred], blast)
      from this(1) obtain x1 where "x1 \<in> Q" and "v = lt x1" ..
      from this(1) True False have "x1 \<in> dgrad_p_set d m" and "x1 \<noteq> 0" by auto
      hence "d (pp_of_term v) \<le> m" unfolding \<open>v = lt x1\<close> by (rule dgrad_p_setD_lp)
      define Q1 where "Q1 = {tail p | p. p \<in> Q \<and> lt p = v}"
      from \<open>x1 \<in> Q\<close> have "tail x1 \<in> Q1" by (auto simp add: Q1_def \<open>v = lt x1\<close>)
      with assms have "\<exists>p\<in>Q1. \<forall>q\<in>Q1. \<not> dickson_less_p d m q p"
      proof (rule wf_dickson_less_p_aux)
        show "\<forall>y\<in>Q1. y \<noteq> 0 \<longrightarrow> y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) v"
        proof (intro ballI impI)
          fix y
          assume "y \<in> Q1" and "y \<noteq> 0"
          from this(1) obtain y1 where "y1 \<in> Q" and "v = lt y1" and "y = tail y1" unfolding Q1_def
            by blast
          from this(1) True have "y1 \<in> dgrad_p_set d m" ..
          hence "y \<in> dgrad_p_set d m" unfolding \<open>y = tail y1\<close> by (rule dgrad_p_set_closed_tail)
          thus "y \<in> dgrad_p_set d m \<and> dickson_less_v d m (lt y) v"
          proof
            show "dickson_less_v d m (lt y) v"
            proof (rule dickson_less_vI)
              from \<open>y \<in> dgrad_p_set d m\<close> \<open>y \<noteq> 0\<close> show "d (pp_of_term (lt y)) \<le> m"
                by (rule dgrad_p_setD_lp)
            next
              from \<open>y \<noteq> 0\<close> show "lt y \<prec>\<^sub>t v" unfolding \<open>v = lt y1\<close> \<open>y = tail y1\<close> by (rule lt_tail)
            qed fact
          qed
        qed
      qed
      then obtain p0 where "p0 \<in> Q1" and p0_min: "\<And>q. q \<in> Q1 \<Longrightarrow> \<not> dickson_less_p d m q p0" by blast
      from this(1) obtain p where "p \<in> Q" and "v = lt p" and "p0 = tail p" unfolding Q1_def
        by blast
      from this(1) False have "p \<noteq> 0" by blast
      show ?thesis
      proof (intro bexI allI impI notI)
        fix y
        assume "y \<in> Q"
        hence "y \<noteq> 0" using False by blast
        assume "dickson_less_p d m y p"
        hence "y \<in> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "y \<prec>\<^sub>p p"
          by (rule dickson_less_pD1, rule dickson_less_pD2, rule dickson_less_pD3)
        from this(3) have "y \<preceq>\<^sub>p p" by simp
        hence "lt y \<preceq>\<^sub>t lt p" by (rule ord_p_lt)
        moreover have "\<not> lt y \<prec>\<^sub>t lt p"
        proof
          assume "lt y \<prec>\<^sub>t lt p"
          have "dickson_less_v d m (lt y) v" unfolding \<open>v = lt p\<close>
            by (rule dickson_less_vI, rule dgrad_p_setD_lp, fact+, rule dgrad_p_setD_lp, fact+)
          hence "lt y \<notin> ?L" by (rule v_min)
          hence "y \<notin> Q" by fastforce
          from this \<open>y \<in> Q\<close> show False ..
        qed
        ultimately have "lt y = lt p" by simp
        from \<open>y \<noteq> 0\<close> this \<open>y \<prec>\<^sub>p p\<close> have "tail y \<prec>\<^sub>p tail p" by (rule ord_p_tail)
        from \<open>y \<in> Q\<close> have "tail y \<in> Q1" by (auto simp add: Q1_def \<open>v = lt p\<close> \<open>lt y = lt p\<close>[symmetric])
        hence "\<not> dickson_less_p d m (tail y) p0" by (rule p0_min)
        moreover have "dickson_less_p d m (tail y) p0" unfolding \<open>p0 = tail p\<close>
          by (rule dickson_less_pI, rule dgrad_p_set_closed_tail, fact, rule dgrad_p_set_closed_tail, fact+)
        ultimately show False ..
      qed fact
    next
      case False
      then obtain q where "q \<in> Q" and "q \<notin> dgrad_p_set d m" by blast
      from this(1) show ?thesis
      proof
        show "\<forall>y. dickson_less_p d m y q \<longrightarrow> y \<notin> Q"
        proof (intro allI impI)
          fix y
          assume "dickson_less_p d m y q"
          hence "q \<in> dgrad_p_set d m" by (rule dickson_less_pD2)
          with \<open>q \<notin> dgrad_p_set d m\<close> show "y \<notin> Q" ..
        qed
      qed
    qed
  qed
qed

corollary ord_p_minimum_dgrad_p_set:
  assumes "dickson_grading d" and "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  obtains q where "q \<in> Q" and "\<And>y. y \<prec>\<^sub>p q \<Longrightarrow> y \<notin> Q"
proof -
  from assms(1) have "wfP (dickson_less_p d m)" by (rule wf_dickson_less_p)
  from this assms(2) obtain q where "q \<in> Q" and *: "\<And>y. dickson_less_p d m y q \<Longrightarrow> y \<notin> Q"
    by (rule wfE_min[to_pred], auto)
  from assms(3) \<open>q \<in> Q\<close> have "q \<in> dgrad_p_set d m" ..
  from \<open>q \<in> Q\<close> show ?thesis
  proof
    fix y
    assume "y \<prec>\<^sub>p q"
    show "y \<notin> Q"
    proof
      assume "y \<in> Q"
      with assms(3) have "y \<in> dgrad_p_set d m" ..
      from this \<open>q \<in> dgrad_p_set d m\<close> \<open>y \<prec>\<^sub>p q\<close> have "dickson_less_p d m y q"
        by (rule dickson_less_pI)
      hence "y \<notin> Q" by (rule *)
      from this \<open>y \<in> Q\<close> show False ..
    qed
  qed
qed

lemma ord_term_minimum_dgrad_set:
  assumes "dickson_grading d" and "v \<in> V" and "pp_of_term ` V \<subseteq> dgrad_set d m"
  obtains u where "u \<in> V" and "\<And>w. w \<prec>\<^sub>t u \<Longrightarrow> w \<notin> V"
proof -
  from assms(1) have "wfP (dickson_less_v d m)" by (rule wf_dickson_less_v)
  then obtain u where "u \<in> V" and *: "\<And>w. dickson_less_v d m w u \<Longrightarrow> w \<notin> V" using assms(2)
    by (rule wfE_min[to_pred]) blast
  from this(1) have "pp_of_term u \<in> pp_of_term ` V" by (rule imageI)
  with assms(3) have "pp_of_term u \<in> dgrad_set d m" ..
  hence "d (pp_of_term u) \<le> m" by (rule dgrad_setD)
  from \<open>u \<in> V\<close> show ?thesis
  proof
    fix w
    assume "w \<prec>\<^sub>t u"
    show "w \<notin> V"
    proof
      assume "w \<in> V"
      hence "pp_of_term w \<in> pp_of_term ` V" by (rule imageI)
      with assms(3) have "pp_of_term w \<in> dgrad_set d m" ..
      hence "d (pp_of_term w) \<le> m" by (rule dgrad_setD)
      from this \<open>d (pp_of_term u) \<le> m\<close> \<open>w \<prec>\<^sub>t u\<close> have "dickson_less_v d m w u"
        by (rule dickson_less_vI)
      hence "w \<notin> V" by (rule *)
      from this \<open>w \<in> V\<close> show False ..
    qed
  qed
qed

end (* gd_term *)

subsection \<open>More Interpretations\<close>

context gd_powerprod
begin

sublocale punit: gd_term to_pair_unit fst "(\<preceq>)" "(\<prec>)" "(\<preceq>)" "(\<prec>)" ..

end

locale od_term =
    ordered_term pair_of_term term_of_pair ord ord_strict ord_term ord_term_strict
      for pair_of_term::"'t \<Rightarrow> ('a::dickson_powerprod \<times> 'k::{the_min,wellorder})"
      and term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
      and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
      and ord_strict (infixl "\<prec>" 50)
      and ord_term::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<preceq>\<^sub>t" 50)
      and ord_term_strict::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<prec>\<^sub>t" 50)
begin

sublocale gd_term ..

lemma ord_p_wf: "wfP (\<prec>\<^sub>p)"
proof -
  from dickson_grading_zero have "wfP (dickson_less_p (\<lambda>_. 0) 0)" by (rule wf_dickson_less_p)
  thus ?thesis by (simp only: dickson_less_p_zero)
qed

end (* od_term *)

end (* theory *)
