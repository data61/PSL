theory Lorenz_C1
  imports
    Lorenz_Approximation.Lorenz_Approximation
begin

locale check_lines_c1 =
  assumes check_lines_c1: "check_lines True ordered_lines"
begin

lemma all_coarse_results: "Ball (set coarse_results) correct_res" if NF
  apply (rule Ball_coarseI)
   apply fact
   apply (rule check_lines_c1)
  apply eval
  done

theorem lorenz_bounds:
  "\<forall>x \<in> N - \<Gamma>. x returns_to \<Sigma>"                              \<comment> \<open>\<open>R\<close> is well defined\<close>
  "R ` (N - \<Gamma>) \<subseteq> N"                                         \<comment> \<open>\<open>R\<close> is forward invariant\<close>
  "\<forall>x \<in> N - \<Gamma>. (R has_derivative DR x) (at x within \<Sigma>\<^sub>l\<^sub>e)" \<comment> \<open>\<open>DR\<close> is derivative\<close>
  "\<forall>x \<in> N - \<Gamma>. DR x ` \<CC> x \<subseteq> \<CC> (R x)"                        \<comment> \<open>\<open>\<CC>\<close> is mapped strictly into itself\<close>
  "\<forall>x \<in> N - \<Gamma>. \<forall>c \<in> \<CC> x. norm (DR x c) \<ge> \<E> x      * norm c" \<comment> \<open>expansion\<close>
  "\<forall>x \<in> N - \<Gamma>. \<forall>c \<in> \<CC> x. norm (DR x c) \<ge> \<E>\<^sub>p (R x) * norm c"\<comment> \<open>pre-expansion\<close>
  if NF
  using lorenz_bounds_lemma_asym[OF \<open>NF\<close> reduce_lorenz_symmetry, OF all_coarse_results[OF \<open>NF\<close>]]
  by auto

end

interpretation check_lines_c1
  apply unfold_locales
  oops\<comment> \<open>very very slow: about 50 CPU hours\<close>
    \<comment> \<open>\<open>by (parallel_check (* "output_c1/lorenz_c1_" *) _ 60 20)\<close>\<close>

end
