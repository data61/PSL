(* Author: R. Thiemann *)

section \<open>Unsatisfiability over the Reals\<close>

text \<open>By using Farkas' Lemma we prove that a finite set of 
  linear rational inequalities is satisfiable over the rational numbers
  if and only if it is satisfiable over the real numbers.
  Hence, the simplex algorithm either gives a rational solution or
  shows unsatisfiability over the real numbers.\<close>

theory Simplex_for_Reals
  imports 
    Farkas
    Simplex.Simplex_Incremental
begin


instantiation real :: lrv
begin
definition scaleRat_real :: "rat \<Rightarrow> real \<Rightarrow> real" where
  [simp]: "x *R y = real_of_rat x * y"
instance by standard (auto simp add: field_simps of_rat_mult of_rat_add)
end

abbreviation real_satisfies_constraints :: "real valuation \<Rightarrow> constraint set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>r\<^sub>c\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs \<equiv> \<forall> c \<in> cs. v \<Turnstile>\<^sub>c c"

definition of_rat_val :: "rat valuation \<Rightarrow> real valuation" where
  "of_rat_val v x = of_rat (v x)" 

lemma of_rat_val_eval: "p \<lbrace>of_rat_val v\<rbrace> = of_rat (p \<lbrace>v\<rbrace>)" 
  unfolding of_rat_val_def linear_poly_sum of_rat_sum 
  by (rule sum.cong, auto simp: of_rat_mult)

lemma of_rat_val_constraint: "of_rat_val v \<Turnstile>\<^sub>c c \<longleftrightarrow> v \<Turnstile>\<^sub>c c" 
  by (cases c, auto simp: of_rat_val_eval of_rat_less of_rat_less_eq)

lemma of_rat_val_constraints: "of_rat_val v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s cs" 
  using of_rat_val_constraint by auto

lemma sat_scale_rat_real: assumes "(v :: real valuation) \<Turnstile>\<^sub>c c"
  shows "v \<Turnstile>\<^sub>c (r *R c)"
proof -
  have "r < 0 \<or> r = 0 \<or> r > 0" by auto
  then show ?thesis using assms by (cases c, simp_all add: right_diff_distrib 
        valuate_minus valuate_scaleRat scaleRat_leq1 scaleRat_leq2 valuate_zero
        of_rat_less of_rat_mult)
qed

fun of_rat_lec :: "rat le_constraint \<Rightarrow> real le_constraint" where
  "of_rat_lec (Le_Constraint r p c) = Le_Constraint r p (of_rat c)" 

lemma lec_of_constraint_real: 
  assumes "is_le c"
  shows "(v \<Turnstile>\<^sub>l\<^sub>e of_rat_lec (lec_of_constraint c)) \<longleftrightarrow> (v \<Turnstile>\<^sub>c c)"
  using assms by (cases c, auto)

lemma of_rat_lec_add: "of_rat_lec (c + d) = of_rat_lec c + of_rat_lec d" 
  by (cases c; cases d, auto simp: of_rat_add)

lemma of_rat_lec_zero: "of_rat_lec 0 = 0" 
  unfolding zero_le_constraint_def by simp

lemma of_rat_lec_sum: "of_rat_lec (sum_list c) = sum_list (map of_rat_lec c)" 
  by (induct c, auto simp: of_rat_lec_zero of_rat_lec_add)

text \<open>This is the main lemma: a finite set of linear constraints is 
  satisfiable over Q if and only if it is satisfiable over R.\<close>
lemma rat_real_conversion: assumes "finite cs" 
  shows "(\<exists> v :: rat valuation. v \<Turnstile>\<^sub>c\<^sub>s cs) \<longleftrightarrow> (\<exists> v :: real valuation. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs)" 
proof
  show "\<exists>v. v \<Turnstile>\<^sub>c\<^sub>s cs \<Longrightarrow> \<exists>v. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs" using of_rat_val_constraint by auto
  assume "\<exists>v. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs" 
  then obtain v where *: "v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s cs" by auto
  show "\<exists>v. v \<Turnstile>\<^sub>c\<^sub>s cs" 
  proof (rule ccontr)
    assume "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s cs" 
    from farkas_coefficients[OF assms] this
    obtain C where "farkas_coefficients cs C" by auto
    from this[unfolded farkas_coefficients_def]
    obtain d rel where
      isleq: "(\<forall>(r,c) \<in> set C. c \<in> cs \<and> is_le (r *R c) \<and> r \<noteq> 0)" and
      leq: "(\<Sum> (r,c) \<leftarrow> C. lec_of_constraint (r *R c)) = Le_Constraint rel 0 d" and
      choice: "rel = Lt_Rel \<and> d \<le> 0 \<or> rel = Leq_Rel \<and> d < 0" by blast
    {
      fix r c
      assume c: "(r,c) \<in> set C" 
      from c * isleq have "v \<Turnstile>\<^sub>c c" by auto
      hence v: "v \<Turnstile>\<^sub>c (r *R c)" by (rule sat_scale_rat_real)
      from c isleq have "is_le (r *R c)" by auto
      from lec_of_constraint_real[OF this] v 
      have "v \<Turnstile>\<^sub>l\<^sub>e of_rat_lec (lec_of_constraint (r *R c))" by blast
    } note v = this
    have "Le_Constraint rel 0 (of_rat d) = of_rat_lec (\<Sum> (r,c) \<leftarrow> C. lec_of_constraint (r *R c))" 
      unfolding leq by simp
    also have "\<dots> = (\<Sum> (r,c) \<leftarrow> C. of_rat_lec (lec_of_constraint (r *R c)))" (is "_ = ?sum")
      unfolding of_rat_lec_sum map_map o_def by (rule arg_cong[of _ _ sum_list], auto)
    finally have leq: "Le_Constraint rel 0 (of_rat d) = ?sum" by simp
    have "v \<Turnstile>\<^sub>l\<^sub>e Le_Constraint rel 0 (of_rat d)" unfolding leq
      by (rule satisfies_sumlist_le_constraints, insert v, auto)
    with choice show False by (auto simp: linear_poly_sum)
  qed
qed

text \<open>The main result of simplex, now using unsatisfiability over the reals.\<close>

fun i_satisfies_cs_real (infixl "\<Turnstile>\<^sub>r\<^sub>i\<^sub>c\<^sub>s" 100) where
  "(I,v) \<Turnstile>\<^sub>r\<^sub>i\<^sub>c\<^sub>s cs \<longleftrightarrow> v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s Simplex.restrict_to I cs"

lemma simplex_index_real:
  "simplex_index cs = Unsat I \<Longrightarrow> set I \<subseteq> fst ` set cs \<and> \<not> (\<exists> v. (set I, v) \<Turnstile>\<^sub>r\<^sub>i\<^sub>c\<^sub>s set cs) \<and> 
     (distinct_indices cs \<longrightarrow> (\<forall> J \<subset> set I. (\<exists> v. (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs)))" \<comment> \<open>minimal unsat core over the reals\<close>
  "simplex_index cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s (snd ` set cs)" \<comment> \<open>satisfying assingment\<close>
  using simplex_index(1)[of cs I] simplex_index(2)[of cs v] 
    rat_real_conversion[of "Simplex.restrict_to (set I) (set cs)"]
  by auto


lemma simplex_real:
  "simplex cs = Unsat I \<Longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set cs)" \<comment> \<open>unsat of original constraints over the reals\<close>
  "simplex cs = Unsat I \<Longrightarrow> set I \<subseteq> {0..<length cs} \<and> \<not> (\<exists> v. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s {cs ! i | i. i \<in> set I})
    \<and> (\<forall>J\<subset>set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i |i. i \<in> J})" \<comment> \<open>minimal unsat core over reals\<close>
  "simplex cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set cs"  \<comment> \<open>satisfying assignment over the rationals\<close>
proof (intro simplex(1)[unfolded rat_real_conversion[OF finite_set]])
  assume unsat: "simplex cs = Inl I" 
  have "finite {cs ! i |i. i \<in> set I}" by auto
  from simplex(2)[OF unsat, unfolded rat_real_conversion[OF this]]
  show "set I \<subseteq> {0..<length cs} \<and> \<not> (\<exists> v. v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s {cs ! i | i. i \<in> set I})
    \<and> (\<forall>J\<subset>set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i |i. i \<in> J})" by auto
qed (insert simplex(3), auto)

text \<open>Define notion of minimal unsat core over the reals:
  the subset has to be unsat over the reals, and every proper subset has
  to be satisfiable over the rational numbers.\<close>

definition minimal_unsat_core_real :: "'i set \<Rightarrow> 'i i_constraint list \<Rightarrow> bool" where
  "minimal_unsat_core_real I ics  = ((I \<subseteq> fst ` set ics) \<and> (\<not> (\<exists> v. (I,v) \<Turnstile>\<^sub>r\<^sub>i\<^sub>c\<^sub>s set ics))
     \<and> (distinct_indices ics \<longrightarrow> (\<forall> J. J \<subset> I \<longrightarrow> (\<exists> v. (J,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics))))"

text \<open>Because of equi-satisfiability the two notions of minimal unsat cores coincide.\<close>
lemma minimal_unsat_core_real_conv: "minimal_unsat_core_real I ics = minimal_unsat_core I ics" 
proof 
  show "minimal_unsat_core_real I ics \<Longrightarrow> minimal_unsat_core I ics" 
    unfolding minimal_unsat_core_real_def minimal_unsat_core_def
    using of_rat_val_constraint by simp metis
next
  assume "minimal_unsat_core I ics"     
  thus "minimal_unsat_core_real I ics" 
    unfolding minimal_unsat_core_real_def minimal_unsat_core_def
    using rat_real_conversion[of "Simplex.restrict_to I (set ics)"]
    by auto
qed

text \<open>Easy consequence: The incremental simplex algorithm is also sound wrt. 
  minimal-unsat-cores over the reals.\<close>
lemmas incremental_simplex_real = 
  init_simplex
  assert_simplex_ok
  assert_simplex_unsat[folded minimal_unsat_core_real_conv]
  assert_all_simplex_ok
  assert_all_simplex_unsat[folded minimal_unsat_core_real_conv]
  check_simplex_ok
  check_simplex_unsat[folded minimal_unsat_core_real_conv]
  solution_simplex
  backtrack_simplex
  checked_invariant_simplex

end