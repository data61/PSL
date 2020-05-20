section \<open>Stochastic Matrices and the Perron--Frobenius Theorem\<close>

text \<open>Since a stationary distribution corresponds to a non-negative real
  eigenvector of the stochastic matrix, we can apply the Perron--Frobenius
  theorem. In this way we easily derive that every stochastic matrix has 
  a stationary distribution, and moreover that this distribution is unique, if the 
  matrix is irreducible, i.e., if the graph of the matrix is strongly connected.\<close>

theory Stochastic_Matrix_Perron_Frobenius
imports   
  Perron_Frobenius.Perron_Frobenius_Irreducible
  Stochastic_Matrix_Markov_Models
  Eigenspace
begin    

hide_const (open) Coset.order

lemma pf_nonneg_mat_st_mat: "pf_nonneg_mat (st_mat A)" 
  by (unfold_locales, auto simp: non_neg_mat_st_mat)

lemma stoch_non_neg_vec_norm1: assumes "stoch_vec (v :: real ^ 'n)" "non_neg_vec v" 
  shows "norm1 v = 1" 
  unfolding assms(1)[unfolded stoch_vec_def, symmetric] norm1_def
  by (rule sum.cong, insert assms(2)[unfolded non_neg_vec_def], auto)

lemma stationary_distribution_exists: "\<exists> v. A *st v = v"
proof -
  let ?A = "st_mat A" 
  let ?c = "complex_of_real" 
  let ?B = "\<chi> i j. ?c (?A $ i $ j)" 
  have "real_non_neg_mat ?B" using non_neg_mat_st_mat[of A] 
    unfolding real_non_neg_mat_def elements_mat_h_def non_neg_mat_def
    by auto
  from Perron_Frobenius.perron_frobenius_both[OF this] obtain v a where 
    ev: "eigen_vector ?B v (?c a)" and nn: "real_non_neg_vec v" 
    and a: "a = HMA_Connect.spectral_radius ?B" by auto
  from spectral_radius_ev[of ?B, folded a] have a0: "a \<ge> 0" by auto
  define w where "w = (\<chi> i. Re (v $ i))" 
  from nn have vw: "v = (\<chi> i. ?c (w $ i))" unfolding real_non_neg_vec_def w_def
    by (auto simp: vec_elements_h_def)
  from ev[unfolded eigen_vector_def] have v0: "v \<noteq> 0" and ev: "?B *v v = ?c a *s v" by auto
  from v0 have w0: "w \<noteq> 0" unfolding vw by (auto simp: Finite_Cartesian_Product.vec_eq_iff)
  {
    fix i
    from ev have "Re ((?B *v v) $ i) = Re ((?c a *s v) $ i)" by simp
    also have "Re ((?c a *s v) $ i) = (a *s w) $ i" unfolding vw by simp
    also have "Re ((?B *v v) $ i) = (?A *v w) $ i" unfolding vw 
      by (simp add: matrix_vector_mult_def)
    also note calculation
  }
  hence ev: "?A *v w = a *s w" by (auto simp: Finite_Cartesian_Product.vec_eq_iff)
  from nn have nn: "non_neg_vec w" 
    unfolding vw by (auto simp: real_non_neg_vec_def non_neg_vec_def vec_elements_h_def)
  (* we now mainly have to prove that a = 1 *)
  let ?n = "norm1 w" 
  from w0 have n0: "?n \<noteq> 0" by auto
  hence n_pos: "?n > 0" using norm1_ge_0[of w] by linarith
  define u where "u = inverse ?n *s w" 
  have nn: "non_neg_vec u" using nn n_pos unfolding u_def non_neg_vec_def by auto
  have nu: "norm1 u = 1" unfolding u_def scalar_mult_eq_scaleR norm1_scaleR using n_pos
    by (auto simp: field_simps)
  have 1: "stoch_vec u" unfolding stoch_vec_def nu[symmetric] norm1_def
    by (rule sum.cong, insert nn[unfolded non_neg_vec_def], auto)
  from arg_cong[OF ev, of "\<lambda> x. inverse ?n *s x"]
  have ev: "?A *v u = a *s u" unfolding u_def
    by (auto simp: ac_simps vector_smult_distrib matrix_vect_scaleR)
  from right_stoch_mat_mult_stoch_vec[OF right_stoch_mat_st_mat[of A] 1, unfolded ev]
  have st: "stoch_vec (a *s u)" .
  from non_neg_mat_mult_non_neg_vec[OF non_neg_mat_st_mat[of A] nn, unfolded ev]
  have nn': "non_neg_vec (a *s u)" .
  from stoch_non_neg_vec_norm1[OF st nn', unfolded scalar_mult_eq_scaleR norm1_scaleR nu] a0
  have "a = 1" by auto
  with ev st have ev: "?A *v u = u" and st: "stoch_vec u" by auto
  show ?thesis using ev st nn
    by (intro exI[of _ "to_st_vec u"], transfer, auto)
qed

lemma stationary_distribution_unique: 
  assumes "fixed_mat.irreducible (st_mat A)" 
  shows "\<exists>! v. A *st v = v" 
proof -
  from stationary_distribution_exists obtain v where ev: "A *st v = v" by auto
  show ?thesis
  proof (intro ex1I, rule ev)
    fix w
    assume "A *st w = w" 
    thus "w = v" using ev assms
    proof (transfer, goal_cases)
      case (1 A w v)
      interpret perron_frobenius A
        by (unfold_locales, insert 1, auto)
      from 1 have *: "eigen_vector A v 1" "le_vec 0 v" "eigen_vector A w 1"
        by (auto simp: eigen_vector_def stoch_vec_def non_neg_vec_def)
      from nonnegative_eigenvector_has_ev_sr[OF *(1-2)] have sr1: "sr = 1" by auto  
      from multiplicity_sr_1[unfolded sr1] have "order 1 (charpoly A) = 1" .
      from unique_eigen_vector_real[OF this *(1,3)] obtain a where 
        vw: "v = a *s w" by auto
      from 1(2,4)[unfolded stoch_vec_def] have "sum (($h) v) UNIV = sum (($h) w) UNIV" by auto
      also have "sum (($h) v) UNIV = a * sum (($h) w) UNIV" unfolding vw 
        by (auto simp: sum_distrib_left)
      finally have "a = 1" using 1(2)[unfolded stoch_vec_def] by auto
      with vw show "v = w" by auto
    qed
  qed
qed

text \<open>Let us now convert the stationary distribution results from matrices to Markov chains.\<close>

context transition_matrix
begin

lemma stationary_distribution_exists: 
  "\<exists> x. stationary_distribution (pmf_of_st_vec x)" 
proof -
  from stationary_distribution_exists obtain x where ev: "A *st x = x" by auto
  show ?thesis
    by (intro exI[of _ x], unfold stationary_distribution_pmf_of_st_vec,
    simp add: ev)
qed

lemma stationary_distribution_unique: assumes "fixed_mat.irreducible (st_mat A)" 
  shows "\<exists>! N. stationary_distribution N" 
proof -
  from stationary_distribution_exists obtain x where
    st: "stationary_distribution (pmf_of_st_vec x)" by blast
  show ?thesis
  proof (rule ex1I, rule st)
    fix N
    assume st': "stationary_distribution N" 
    from stationary_distribution_implies_pmf_of_st_vec[OF this] obtain y where 
      N: "N = pmf_of_st_vec y" by auto
    from st'[unfolded N] st 
    have "A *st x = x" "A *st y = y" unfolding stationary_distribution_pmf_of_st_vec by auto
    from stationary_distribution_unique[OF assms] this have "x = y" by auto
    with N show "N = pmf_of_st_vec x" by auto
  qed
qed
end
end
