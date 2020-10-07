section \<open>Stochastic Matrices and Markov Models\<close>

text \<open>We interpret stochastic matrices as Markov chain with
  discrete time and finite state and prove that the bind-operation
  on probability mass functions is precisely matrix-vector multiplication.
  As a consequence, the notion of stationary distribution is equivalent to
  being an eigenvector with eigenvalue 1.\<close>

theory Stochastic_Matrix_Markov_Models
imports
  Markov_Models.Classifying_Markov_Chain_States
  Stochastic_Vector_PMF
begin

definition transition_of_st_mat :: "'i st_mat \<Rightarrow> 'i :: finite \<Rightarrow> 'i pmf" where
  "transition_of_st_mat a i = pmf_as_measure.pmf_of_st_vec (transition_vec_of_st_mat a i)" 

lemma st_vec_transition_vec_of_st_mat[simp]: 
  "st_vec (transition_vec_of_st_mat A a) $ i = st_mat A $ i $ a" 
  by (transfer, auto simp: column_def)

locale transition_matrix = pmf_as_measure +
  fixes A :: "'i :: finite st_mat" 
begin
sublocale MC_syntax "transition_of_st_mat A" .

lemma measure_pmf_of_st_vec[simp]: "measure_pmf (pmf_of_st_vec x) = measure_of_st_vec x" 
  by (rule pmf_as_measure.pmf_of_st_vec.rep_eq)

lemma pmf_transition_of_st_mat[simp]: "pmf (transition_of_st_mat A a) i = st_mat A $ i $ a"
  unfolding transition_of_st_mat_def
  by (transfer, auto simp: measure_def)

lemma bind_is_matrix_vector_mult: "(bind_pmf x (transition_of_st_mat A)) =
  pmf_as_measure.pmf_of_st_vec (A *st st_vec_of_pmf x)" 
proof (rule pmf_eqI, goal_cases)
  case (1 i)
  define X where "X = st_vec_of_pmf x" 
  have "pmf (bind_pmf x (transition_of_st_mat A)) i = 
    (\<Sum>a\<in>UNIV. pmf x a *\<^sub>R pmf (transition_of_st_mat A a) i)" 
    unfolding pmf_bind by (subst integral_measure_pmf[of UNIV], auto)
  also have "\<dots> = (\<Sum>a\<in>UNIV. st_mat A $ i $ a * st_vec X $ a)" 
    by (rule sum.cong[OF refl], auto simp: X_def)
  also have "\<dots> = (st_mat A *v st_vec X) $ i" 
    unfolding matrix_vector_mult_def by auto
  also have "\<dots> = st_vec (A *st X) $ i" unfolding st_mat_mult_st_vec by simp
  also have "\<dots> = pmf (pmf_of_st_vec (A *st X)) i" by simp
  finally show ?case by (simp add: X_def)
qed

lemmas stationary_distribution_alt_def = 
  stationary_distribution_def[unfolded bind_is_matrix_vector_mult]

lemma stationary_distribution_implies_pmf_of_st_vec:
  assumes "stationary_distribution N" 
  shows "\<exists> x. N = pmf_of_st_vec x" 
proof -
  from assms[unfolded stationary_distribution_alt_def] show ?thesis by auto
qed

lemma stationary_distribution_pmf_of_st_vec:
  "stationary_distribution (pmf_of_st_vec x) = (A *st x = x)" 
  unfolding stationary_distribution_alt_def pmf_of_st_vec_inj by auto
end
end