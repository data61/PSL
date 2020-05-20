section \<open>Stochastic Matrices\<close>

text \<open>We define a type for stochastic vectors and right-stochastic matrices,
 i.e., non-negative real vectors and matrices where the sum of each column is 1.
 For this type we define a matrix-vector multplication, i.e., we show that
 $A * v$ is a stochastic vector, if $A$ is a right-stochastic matrix and $v$ 
 a stochastic vector.
\<close>
theory Stochastic_Matrix
  imports Perron_Frobenius.Perron_Frobenius_Aux (* for non_neg_mat *)
begin

definition non_neg_vec :: "'a :: linordered_idom ^ 'n \<Rightarrow> bool" where
  "non_neg_vec A \<equiv> (\<forall> i. A $ i \<ge> 0)" 

definition stoch_vec :: "'a :: comm_ring_1 ^ 'n \<Rightarrow> bool" where
  "stoch_vec v = (sum (\<lambda> i. v $ i) UNIV = 1)"

definition right_stoch_mat :: "'a :: comm_ring_1 ^ 'n ^ 'm \<Rightarrow> bool" where
  "right_stoch_mat a = (\<forall> j. stoch_vec (column j a))" 

typedef 'i st_mat = "{ a :: real ^ 'i ^ 'i. non_neg_mat a \<and> right_stoch_mat a}" 
  morphisms st_mat Abs_st_mat
  by (rule exI[of _ "\<chi> i j. if i = undefined then 1 else 0"], 
      auto simp: non_neg_mat_def elements_mat_h_def right_stoch_mat_def stoch_vec_def column_def)

setup_lifting type_definition_st_mat

typedef 'i st_vec = "{ v :: real ^ 'i. non_neg_vec v \<and> stoch_vec v}" 
  morphisms st_vec Abs_st_vec
  by (rule exI[of _ "\<chi> i. if i = undefined then 1 else 0"], 
      auto simp: non_neg_vec_def stoch_vec_def)

setup_lifting type_definition_st_vec

lift_definition transition_vec_of_st_mat :: "'i :: finite st_mat \<Rightarrow> 'i \<Rightarrow> 'i st_vec" 
  is "\<lambda> a i. column i a" 
  by (auto simp: right_stoch_mat_def non_neg_mat_def stoch_vec_def 
      elements_mat_h_def non_neg_vec_def column_def)

lemma non_neg_vec_st_vec: "non_neg_vec (st_vec v)" 
  by (transfer, auto)

lemma non_neg_mat_mult_non_neg_vec: "non_neg_mat a \<Longrightarrow> non_neg_vec v \<Longrightarrow> 
  non_neg_vec (a *v v)" 
  unfolding non_neg_mat_def non_neg_vec_def  elements_mat_h_def
  by (auto simp: matrix_vector_mult_def intro!: sum_nonneg)

lemma right_stoch_mat_mult_stoch_vec: assumes "right_stoch_mat a" and "stoch_vec v" 
shows "stoch_vec (a *v v)"
proof -
  note * = assms[unfolded right_stoch_mat_def column_def stoch_vec_def, simplified]
  have "stoch_vec (a *v v) = ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. a $ i $ j * v $ j) = 1)" 
    (is "_ = (?sum = 1)")
    unfolding stoch_vec_def matrix_vector_mult_def by auto
  also have "?sum = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. a $ i $ j * v $ j)" 
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. v $ j)" 
    by (rule sum.cong[OF refl], insert *, auto simp: sum_distrib_right[symmetric])
  also have "\<dots> = 1" using * by auto
  finally show ?thesis by simp
qed

lift_definition st_mat_times_st_vec :: "'i :: finite st_mat \<Rightarrow> 'i st_vec \<Rightarrow> 'i st_vec" 
  (infixl "*st" 70) is "(*v)" 
  using right_stoch_mat_mult_stoch_vec non_neg_mat_mult_non_neg_vec by auto

lift_definition to_st_vec :: "real ^ 'i \<Rightarrow> 'i st_vec" is 
  "\<lambda> x. if stoch_vec x \<and> non_neg_vec x then x else (\<chi> i. if i = undefined then 1 else 0)" 
  by (auto simp: non_neg_vec_def stoch_vec_def)

lemma right_stoch_mat_st_mat: "right_stoch_mat (st_mat A)" 
  by transfer auto

lemma non_neg_mat_st_mat: "non_neg_mat (st_mat A)" 
  by (transfer, auto simp: non_neg_mat_def elements_mat_h_def)

lemma st_mat_mult_st_vec: "st_mat A *v st_vec X = st_vec (A *st X)" by (transfer, auto)

lemma st_vec_nonneg[simp]: "st_vec x $ i \<ge> 0"
  using non_neg_vec_st_vec[of x] by (auto simp: non_neg_vec_def)

lemma st_mat_nonneg[simp]: "st_mat x $ i $h j \<ge> 0"
  using non_neg_mat_st_mat[of x] by (auto simp: non_neg_mat_def elements_mat_h_def)

end