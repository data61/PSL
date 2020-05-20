(* Author: Alexander Maletzky *)

section \<open>Properties of the Lexicographic Order on Power-Products\<close>

theory Lex_Order_PP
  imports Polynomials.Power_Products
begin

text \<open>We prove some useful properties of the purely lexicographic order relation on
  power-products.\<close>

lemma lex_pm_keys_leE:
  assumes "lex_pm s t" and "x \<in> keys (s::'x::linorder \<Rightarrow>\<^sub>0 'a::add_linorder_min)"
  obtains y where "y \<in> keys t" and "y \<le> x"
  using assms(1) unfolding lex_pm_alt
proof (elim disjE exE conjE)
  assume "s = t"
  show ?thesis
  proof
    from assms(2) show "x \<in> keys t" by (simp only: \<open>s = t\<close>)
  qed (fact order.refl)
next
  fix y
  assume 1: "lookup s y < lookup t y" and 2: "\<forall>y'<y. lookup s y' = lookup t y'"
  show ?thesis
  proof (cases "y \<le> x")
    case True
    from zero_min 1 have "0 < lookup t y" by (rule le_less_trans)
    hence "y \<in> keys t" by (simp add: dual_order.strict_implies_not_eq in_keys_iff)
    thus ?thesis using True ..
  next
    case False
    hence "x < y" by simp
    with 2 have "lookup s x = lookup t x" by simp
    with assms(2) have "x \<in> keys t" by (simp only: in_keys_iff not_False_eq_True)
    thus ?thesis using order.refl ..
  qed
qed

lemma lex_pm_except_max:
  assumes "lex_pm s t" and "keys s \<union> keys t \<subseteq> {..x}"
  shows "lex_pm (except s {x}) (except t {x})"
proof -
  from assms(1) have "s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y))"
    by (simp only: lex_pm_alt)
  thus ?thesis
  proof (elim disjE exE conjE)
    assume "s = t"
    thus ?thesis by (simp only: lex_pm_refl)
  next
    fix y
    assume "\<forall>z<y. lookup s z = lookup t z"
    hence eq: "lookup s z = lookup t z" if "z < y" for z using that by simp
    assume *: "lookup s y < lookup t y"
    hence "y \<in> keys s \<union> keys t" by (auto simp flip: lookup_not_eq_zero_eq_in_keys)
    with assms(2) have "y \<in> {..x}" ..
    hence "y = x \<or> y < x" by auto
    thus ?thesis
    proof
      assume y: "y = x"
      have "except s {x} = except t {x}"
      proof (rule poly_mapping_eqI)
        fix z
        show "lookup (except s {x}) z = lookup (except t {x}) z"
        proof (rule linorder_cases)
          assume "z < y"
          thus ?thesis by (simp add: lookup_except eq)
        next
          assume "y < z"
          hence "z \<notin> {..x}" by (simp add: y)
          with assms(2) have "z \<notin> keys s" and "z \<notin> keys t" by blast+
          with \<open>y < z\<close> show ?thesis by (simp add: y lookup_except in_keys_iff)
        next
          assume "z = y"
          thus ?thesis by (simp add: y lookup_except)
        qed
      qed
      thus ?thesis by (simp only: lex_pm_refl)
    next
      assume "y < x"
      show ?thesis unfolding lex_pm_alt
      proof (intro disjI2 exI conjI allI impI)
        from \<open>y < x\<close> * show "lookup (except s {x}) y < lookup (except t {x}) y"
          by (simp add: lookup_except)
      next
        fix z
        assume "z < y"
        hence "z < x" using \<open>y < x\<close> by (rule less_trans)
        with \<open>z < y\<close> show "lookup (except s {x}) z = lookup (except t {x}) z"
          by (simp add: lookup_except eq)
      qed
    qed
  qed
qed

lemma lex_pm_strict_plus_left:
  assumes "lex_pm_strict s t" and "\<And>x y. x \<in> keys t \<Longrightarrow> y \<in> keys u \<Longrightarrow> x < y"
  shows "lex_pm_strict (u + s) (t::_ \<Rightarrow>\<^sub>0 'a::add_linorder_min)"
proof -
  from assms(1) obtain x where 1: "lookup s x < lookup t x" and 2: "\<And>y. y < x \<Longrightarrow> lookup s y = lookup t y"
    by (auto simp: lex_pm_strict_def less_poly_mapping_def less_fun_def)
  from 1 have "x \<in> keys t" by (auto simp flip: lookup_not_eq_zero_eq_in_keys)
  have lookup_u: "lookup u z = 0" if "z \<le> x" for z
  proof (rule ccontr)
    assume "lookup u z \<noteq> 0"
    hence "z \<in> keys u" by (simp add: in_keys_iff)
    with \<open>x \<in> keys t\<close> have "x < z" by (rule assms(2))
    with that show False by simp
  qed
  from 1 have "lookup (u + s) x < lookup t x" by (simp add: lookup_add lookup_u)
  moreover have "lookup (u + s) y = lookup t y" if "y < x" for y using that
    by (simp add: lookup_add 2 lookup_u)
  ultimately show ?thesis by (auto simp: lex_pm_strict_def less_poly_mapping_def less_fun_def)
qed

end (* theory *)
