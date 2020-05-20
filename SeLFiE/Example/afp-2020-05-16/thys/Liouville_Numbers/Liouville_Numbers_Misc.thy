(* 
  File:    Liouville_Numbers_Misc.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

*)

section \<open>Liouville Numbers\<close>
subsection \<open>Preliminary lemmas\<close>
theory Liouville_Numbers_Misc
imports
  Complex_Main
  "HOL-Computational_Algebra.Polynomial"
begin

text \<open>
  We will require these inequalities on factorials to show properties of the standard 
  construction later.
\<close>

lemma fact_ineq: "n \<ge> 1 \<Longrightarrow> fact n + k \<le> fact (n + k)"
proof (induction k)
  case (Suc k)
  from Suc have "fact n + Suc k \<le> fact (n + k) + 1" by simp
  also from Suc have "\<dots> \<le> fact (n + Suc k)" by simp
  finally show ?case .
qed simp_all

lemma Ints_sum:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<int>"
  shows   "sum f A \<in> \<int>"
  by (cases "finite A", insert assms, induction A rule: finite_induct)
     (auto intro!: Ints_add)

lemma suminf_split_initial_segment':
  "summable (f :: nat \<Rightarrow> 'a::real_normed_vector) \<Longrightarrow> 
       suminf f = (\<Sum>n. f (n + k + 1)) + sum f {..k}"
  by (subst suminf_split_initial_segment[of _ "Suc k"], assumption, subst lessThan_Suc_atMost) 
     simp_all

lemma Rats_eq_int_div_int': "(\<rat> :: real set) = {of_int p / of_int q |p q. q > 0}"
proof safe
  fix x :: real assume "x \<in> \<rat>"
  then obtain p q where pq: "x = of_int p / of_int q" "q \<noteq> 0" 
    by (subst (asm) Rats_eq_int_div_int) auto
  show "\<exists>p q. x = real_of_int p / real_of_int q \<and> 0 < q"
  proof (cases "q > 0")
    case False
    show ?thesis by (rule exI[of _ "-p"], rule exI[of _ "-q"]) (insert False pq, auto)
  qed (insert pq, force)
qed auto

lemma Rats_cases':
  assumes "(x :: real) \<in> \<rat>"
  obtains p q where "q > 0" "x = of_int p / of_int q"
  using assms by (subst (asm) Rats_eq_int_div_int') auto


text \<open>
  The following inequality gives a lower bound for the absolute value of an 
  integer polynomial at a rational point that is not a root.
\<close>
lemma int_poly_rat_no_root_ge: 
  fixes p :: "real poly" and a b :: int
  assumes "\<And>n. coeff p n \<in> \<int>"
  assumes "b > 0" "poly p (a / b) \<noteq> 0"
  defines "n \<equiv> degree p"
  shows   "abs (poly p (a / b)) \<ge> 1 / of_int b ^ n"
proof -
  let ?S = "(\<Sum>i\<le>n. coeff p i * of_int a ^ i * (of_int b ^ (n - i)))"
  from \<open>b > 0\<close> have eq: "?S = of_int b ^ n * poly p (a / b)"
    by (simp add: poly_altdef power_divide mult_ac n_def sum_distrib_left power_diff)
  have "?S \<in> \<int>" by (intro Ints_sum Ints_mult assms Ints_power) simp_all
  moreover from assms have "?S \<noteq> 0" by (subst eq) auto
  ultimately have "abs ?S \<ge> 1" by (elim Ints_cases) simp
  with eq \<open>b > 0\<close> show ?thesis by (simp add: field_simps abs_mult)
qed

end
