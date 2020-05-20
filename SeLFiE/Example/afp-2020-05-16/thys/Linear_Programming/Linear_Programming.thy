theory Linear_Programming
  imports
    "HOL-Library.Code_Target_Int"
    "LP_Preliminaries"
    Farkas.Simplex_for_Reals 
begin


section \<open> Abstract LPs \<close>

(* A b c, where A leq b are the constraints and c is the objective function *)

text \<open> Primal Problem \<close>
definition "sat_primal A b = { x. [A *\<^sub>v x]\<le>b }"

text \<open> Dual Problem \<close>
definition "sat_dual A c  = {y. [y \<^sub>v* A]=c \<and> (\<forall>i<dim_vec y. y $ i \<ge> 0)}"

definition "optimal_set f S = {x \<in> S. (\<forall>y\<in> S. f x y)}"

abbreviation max_lp where
  "max_lp A b c \<equiv> optimal_set (\<lambda>x y. (y \<bullet> c) \<le> (x \<bullet> c)) (sat_primal A b)"

abbreviation min_lp where
  "min_lp A b c \<equiv> optimal_set (\<lambda>x y. (y \<bullet> c) \<ge> (x \<bullet> c)) (sat_dual A c)"


lemma optimal_setI[intro]:
  assumes "x \<in> S"
  assumes "\<And>y. y \<in> S \<Longrightarrow> (\<lambda>x y. (y \<bullet> c) \<ge> (x \<bullet> c)) x y"
  shows "x \<in> optimal_set (\<lambda>x y. (y \<bullet> c) \<ge> (x \<bullet> c)) S"
  unfolding optimal_set_def using assms 
  by blast

lemma max_lpI [intro]:
  assumes "[A *\<^sub>v x]\<le>b"
  assumes "(\<And>y. [A *\<^sub>v y]\<le>b \<Longrightarrow> (\<lambda>x y. (y \<bullet> c) \<ge> (x \<bullet> c)) y x)"
  shows "x \<in> max_lp A b c"
  using optimal_setI[of x "{ x. [A *\<^sub>v x]\<le>b }" c] 
  unfolding optimal_set_def optimal_setI 
  by (simp add: assms(1) assms(2) sat_primal_def)

lemma min_lpI [intro]:
  assumes "[y \<^sub>v* A]=c"
    and "(\<And>i. i<dim_vec y \<Longrightarrow> y $ i \<ge> 0)"
  assumes "(\<And>x. x \<in> sat_dual A c \<Longrightarrow> (\<lambda>x y. (y \<bullet> c) \<ge> (x \<bullet> c)) y x)"
  shows "y \<in> min_lp A b c"
  using optimal_setI[of y "sat_dual A c" c] 
  unfolding optimal_set_def optimal_setI sat_dual_def
  by (simp add: assms(1) assms(2) assms(3) sat_dual_def)

lemma sat_primalD [dest]:
  assumes "x \<in> sat_primal A b"
  shows "[A *\<^sub>v x]\<le>b"
  using assms sat_primal_def by force

lemma sat_primalI [intro]:
  assumes "[A *\<^sub>v x]\<le>b"
  shows "x \<in> sat_primal A b"
  using assms sat_primal_def by force

lemma sat_dualD [dest]:
  assumes "y \<in> sat_dual A c"
  shows "[y \<^sub>v* A]=c" "(\<forall>i<dim_vec y. y $ i \<ge> 0)"
  using assms sat_dual_def apply force
  using assms sat_dual_def by force

lemma sat_dualI [intro]:
  assumes "[y \<^sub>v* A]=c" "(\<forall>i<dim_vec y. y $ i \<ge> 0)"
  shows "y \<in> sat_dual A c"
  using assms sat_dual_def by auto

lemma sol_dim_in_sat_primal: "x \<in> sat_primal A b \<Longrightarrow> dim_vec x = dim_col A"
  unfolding mat_times_vec_leq_def by (simp add: mat_times_vec_leq_def sat_primal_def)

lemma sol_dim_in_max_lp: "x \<in> max_lp A b c \<Longrightarrow> dim_vec x = dim_col A"
  unfolding optimal_set_def using sol_dim_in_sat_primal[of x A b] by blast

lemma sol_dim_in_sat_dual: "x \<in> sat_dual A c \<Longrightarrow> dim_vec x = dim_row A"
  unfolding mat_times_vec_leq_def by (simp add: sat_dual_def vec_times_mat_eq_def)

lemma sol_dim_in_min_lp: "x \<in> min_lp A b c \<Longrightarrow> dim_vec x = dim_row A"
  unfolding optimal_set_def using sol_dim_in_sat_dual[of x A] by blast

lemma min_lp_in_sat_dual: "x \<in> min_lp A b c \<Longrightarrow> x \<in> sat_dual A c"
  unfolding optimal_set_def using sol_dim_in_sat_dual[of x A] by blast

lemma max_lp_in_sat_primal: "x \<in> max_lp A b c \<Longrightarrow> x \<in> sat_primal A b"
  unfolding optimal_set_def using sol_dim_in_sat_dual[of x A] by blast


locale abstract_LP =
  fixes A :: "('a::{comm_semiring_1,ordered_semiring,linorder}) mat"
  fixes b :: "'a vec"
  fixes c :: "'a vec"
  fixes m
  fixes n
  assumes "b \<in> carrier_vec m"
  assumes "c \<in> carrier_vec n"
  assumes "A \<in> carrier_mat m n"
begin

lemma dim_b_row_A: "dim_vec b = dim_row A"
  using abstract_LP_axioms abstract_LP_def carrier_matD(1) carrier_vecD
  by metis

lemma dim_b_col_A: "dim_vec c = dim_col A"
  using abstract_LP_axioms abstract_LP_def carrier_matD(2) carrier_vecD 
  by metis

lemma weak_duality_aux:
  fixes i j
  assumes "i \<in> {c \<bullet> x |x. x \<in> sat_primal A b}"
    and "j \<in> {b \<bullet> y |y. y \<in> sat_dual A c}" 
  shows "i \<le> j"
proof -
  obtain x where x: "i = c \<bullet> x" "[A *\<^sub>v x]\<le>b"
    using assms by blast
  obtain y where y: "j = b \<bullet> y" "[y \<^sub>v* A]=c" "(\<forall>i<dim_vec y. 0 \<le> y $ i)"
    using assms by blast
  have d1: "dim_vec x = n" using mat_times_vec_leq_def[of A x b] x
    by (metis abstract_LP_axioms abstract_LP_def carrier_matD(2))
  have d2: "dim_vec y = m"
    by (metis abstract_LP_axioms abstract_LP_def carrier_matD(1) index_transpose_mat(3) vec_times_mat_eq_def y(2))
  have "i = c \<bullet> x" using x by auto
  also have "... = (A\<^sup>T *\<^sub>v y) \<bullet> x"
    using mult_right_eq carrier_vecD y abstract_LP_def 
    by (metis abstract_LP_axioms calculation d1)
  also have "... = (A *\<^sub>v x) \<bullet> y" 
    using assoc_scalar_prod_mult_mat_vec[symmetric, of y m x n A] abstract_LP_axioms abstract_LP_def d1 d2 
      carrier_vec_dim_vec by blast
  also have "... \<le> b \<bullet> y"
    using mult_right_leq
    by (metis index_transpose_mat(3) mat_times_vec_leq_def vec_times_mat_eq_def x(2) y(2) y(3))
  also have "... = j" using y by simp
  finally show "i \<le> j" .
qed

theorem weak_duality_theorem:
  assumes "x \<in> max_lp A b c"
  assumes "y \<in> min_lp A b c"
  shows "x \<bullet> c \<le> y \<bullet> b"
proof -
  define i where i: "i = x \<bullet> c"
  define j where j: "j = y \<bullet> b"
  have dx: "dim_vec x = n"
    using sol_dim_in_max_lp[of x c A b, OF assms(1)] abstract_LP_axioms abstract_LP_def 
      carrier_matD(2) by blast
  have dy: "dim_vec y = m"
    using sol_dim_in_min_lp[of y c A, OF assms(2)]  abstract_LP_axioms abstract_LP_def 
      carrier_matD(1) by blast
  have *: "i \<in> {c \<bullet> x |x. [A *\<^sub>v x]\<le>b}" using assms(1) unfolding optimal_set_def dx sat_primal_def
    using abstract_LP_axioms abstract_LP_def carrier_vec_dim_vec comm_scalar_prod dx i by blast
  have **: "j \<in> {b \<bullet> y |y. [y \<^sub>v* A]=c \<and> (\<forall>i < dim_vec y. y$i \<ge> 0)}"
    using assms(2) unfolding optimal_set_def using abstract_LP_axioms abstract_LP_def 
      carrier_vec_dim_vec comm_scalar_prod dy j by blast
  from weak_duality_aux[of i j] have "i \<le> j" unfolding sat_primal_def sat_dual_def
    using "*" "**" by blast
  then show ?thesis using i j by auto
qed

end

fun create_optimal_solutions where
  "create_optimal_solutions A b c = 
        (case simplex (x_times_c_geq_y_times_b c b #
                                      mat_leqb_eqc A b c @
                                      from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b)))
                                    of
                                      Unsat X \<Rightarrow> Unsat X
                                      | Sat X \<Rightarrow> Sat X)"

fun optimize_no_cond where "optimize_no_cond A b c = (case create_optimal_solutions A b c of 
                          Unsat X \<Rightarrow> Unsat X 
                        | Sat X \<Rightarrow>  Sat (fst (split_n_m_x (dim_vec c) (dim_vec b) X)))"

lemma create_opt_sol_satisfies:
  assumes "create_optimal_solutions A b c = Sat X"
  shows "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set ((x_times_c_geq_y_times_b c b # mat_leqb_eqc A b c @
                      from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b))))"
proof -
  have "simplex (x_times_c_geq_y_times_b c b # mat_leqb_eqc A b c @
        from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b))) = Sat X"
  proof (rule ccontr)
    assume "simplex (x_times_c_geq_y_times_b c b # mat_leqb_eqc A b c @ from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b))) \<noteq> Inr X"
    then have "\<exists>e. simplex (x_times_c_geq_y_times_b c b # mat_leqb_eqc A b c @ from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b))) = Unsat e"
      by (metis assms create_optimal_solutions.simps sum.case(2) sumE)
    then have "\<exists>e. create_optimal_solutions A b c = Unsat e"
      using assms option.split by force
    then show False using assms(1) assms by auto
  qed
  then show ?thesis using simplex(3) by blast
qed

lemma create_opt_sol_sat_leq_mat:
  assumes "dim_vec b = dim_row A"
  assumes "create_optimal_solutions A b c = Sat X"
    and "(x, y) = split_i_j_x (dim_col A) (dim_vec b) X"
  shows "[A *\<^sub>v x]\<le>b"
proof -
  have *: "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
    using create_opt_sol_satisfies[of A b c X] sat_mono[of "(mat_leqb_eqc A b c)" _ X]
    using assms(2) by (metis append_Cons append_assoc in_set_conv_decomp)
  then show ?thesis using mat_leqb_eqc_split_correct1[of b A c X x y, OF assms(1) *] assms
    by blast
qed

lemma create_opt_sol_sat_eq_mat:
  assumes "dim_vec c = dim_row A\<^sup>T" 
    and "dim_vec b = dim_col A\<^sup>T"
  assumes "create_optimal_solutions A b c = Sat X"
    and "(x, y) = split_i_j_x (dim_vec c) (dim_vec c + dim_vec b) X"
  shows "[y \<^sub>v* A]=c"
proof -
  have *: "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
    using create_opt_sol_satisfies[of A b c X] sat_mono[of "(mat_leqb_eqc A b c)" _ X]
      assms(2) assms by (metis UnCI list.set_intros(2) set_append)
  have "dim_row A\<^sup>T = dim_vec c"
    using assms(1) by linarith
  moreover have "dim_col A\<^sup>T = dim_vec b"
    by (simp add: assms(2))
  ultimately show ?thesis
    using assms by (metis mat_leqb_eqc_split_correct2[of c A b X x y, OF assms(1) assms(2) *]
        \<open>dim_vec b = dim_col A\<^sup>T\<close> \<open>dim_vec c = dim_row A\<^sup>T\<close>)
qed 

lemma create_opt_sol_satisfies_leq:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "x \<bullet> c \<ge> y \<bullet> b"
  using create_opt_sol_satisfies[of A b c X]
  by (metis assms(1) assms(2) carrier_vec_dim_vec comm_scalar_prod list.set_intros(1) 
      split_n_m_x_abbrev_dims(2) split_vec_dims(1) x_times_c_geq_y_times_b_split_dotP)

lemma create_opt_sol_satisfies_geq0:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "\<And>i. i < dim_vec y \<Longrightarrow> y$i \<ge> 0"
proof -
  fix i
  assume "i < dim_vec y"
  have *: "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (from_index_geq0_vector (dim_vec c) (0\<^sub>v (dim_vec b)))"
    using assms(1) create_opt_sol_satisfies by (metis UnCI append_Cons set_append)
  have **: "i < dim_vec b"
    by (metis \<open>i < dim_vec y\<close> assms(2) split_n_m_x_abbrev_dims(2))
  then show "0 \<le> y $ i" 
    using from_index_geq0_vector_split_snd[of "dim_vec c" "0\<^sub>v (dim_vec b)" X x y  
        "dim_vec b" i, OF * assms(2)] by simp
qed

locale rat_LP = abstract_LP A b c m n 
  for A ::"rat mat" 
    and b :: "rat vec" 
    and c :: "rat vec"
    and m  :: "nat"
    and n  :: "nat"
begin

lemma create_opt_sol_in_LP:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "[A *\<^sub>v x]\<le>b" "[y \<^sub>v* A]=c" "x \<bullet> c \<ge> y \<bullet> b" "\<And>i. i < dim_vec y \<Longrightarrow> y$i \<ge> 0"
  apply (metis Pair_inject assms(1) assms(2) create_opt_sol_sat_leq_mat dim_b_col_A dim_b_row_A split_i_j_x_def)
  using assms(1) assms(2) create_opt_sol_sat_eq_mat dim_b_col_A dim_b_row_A
    apply (metis index_transpose_mat(2) index_transpose_mat(3))
  using assms(1) assms(2) create_opt_sol_satisfies_leq apply blast
  using assms(1) assms(2) create_opt_sol_satisfies_geq0 by blast


lemma create_optim_in_sols:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "c \<bullet> x \<in> {c \<bullet> x |x. [A *\<^sub>v x]\<le>b}"
    "b \<bullet> y \<in> {b \<bullet> y |y. [y \<^sub>v* A]=c \<and> (\<forall>i < dim_vec y. y$i \<ge> 0)}"
  using assms(1) assms(2) create_opt_sol_in_LP(1) apply blast
  using assms(1) assms(2) create_opt_sol_in_LP(2) create_opt_sol_in_LP(4) by blast

lemma cx_leq_bx_in_creating_opt:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "c \<bullet> x \<le> b \<bullet> y"
  using weak_duality_aux[of "c \<bullet> x" "b \<bullet> y"]  create_optim_in_sols[of X x y, OF assms] by auto

lemma min_max_for_sol:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "c \<bullet> x = b \<bullet> y"
  using create_opt_sol_in_LP(3)[of X x y, OF assms] cx_leq_bx_in_creating_opt[OF assms]
    comm_scalar_prod[of c "dim_vec c" x] comm_scalar_prod[of b "dim_vec b" y]
  by (metis add_diff_cancel_left' antisym assms(2) carrier_vec_dim_vec split_vec_dims(1) split_vec_dims(2))

lemma create_opt_solutions_correct:
  assumes "create_optimal_solutions A b c = Sat X"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "x \<in> max_lp A b c"
proof 
  show "[A *\<^sub>v x]\<le>b"
    using assms(1) assms(2) create_opt_sol_in_LP(1) by blast
  fix z
  assume a: "[A *\<^sub>v z]\<le>b"
  have 1: "c \<bullet> z \<in> {c \<bullet> x |x. x \<in> sat_primal A b}"
    using sat_primalI[of A z b, OF a] by blast
  have 2: "b \<bullet> y \<in> {b \<bullet> y |y. y \<in> sat_dual A c}"
    using sat_dualI
    by (metis (mono_tags, lifting) assms(1) assms(2) create_opt_sol_in_LP(2)
        mem_Collect_eq rat_LP.create_opt_sol_in_LP(4) rat_LP_axioms)
  then have "c \<bullet> z \<le> b \<bullet> y"
    using weak_duality_aux[of "c \<bullet> z" "b \<bullet> y", OF 1 2] sat_primalI[of A z b, OF a] by blast      
  also have "... = x \<bullet> c"
    by (metis assms(1) assms(2) carrier_vec_dim_vec comm_scalar_prod 
        min_max_for_sol split_n_m_x_abbrev_dims(1))
  finally show "z \<bullet> c \<le> x \<bullet> c"
    by (metis a carrier_vec_dim_vec comm_scalar_prod dim_b_col_A mat_times_vec_leqD(2))
qed

lemma optimize_no_cond_correct:
  assumes "optimize_no_cond A b c = Sat x"
  shows "x \<in> max_lp A b c"
proof -
  obtain X where X: "create_optimal_solutions A b c = Sat X"
    by (metis Inr_Inl_False assms old.sum.exhaust old.sum.simps(5) optimize_no_cond.simps)
  have "x = (fst (split_n_m_x (dim_vec c) (dim_vec b) X))"
    using X assms by (metis old.sum.inject(2) old.sum.simps(6) optimize_no_cond.simps)
  then show ?thesis
    using create_opt_solutions_correct[of X x] by (metis X fst_conv old.prod.exhaust)
qed

lemma optimize_no_cond_sol_sat:
  assumes "optimize_no_cond A b c = Sat x"
  shows "x \<in> sat_primal A b"
  using max_lp_in_sat_primal[OF optimize_no_cond_correct[OF assms]] by auto
  

end (* end of \<open> rat_LP \<close> *)


fun maximize where 
  "maximize A b c = (if dim_vec b = dim_row A \<and> dim_vec c = dim_col A then
                      Some (optimize_no_cond A b c)
                    else None)"

lemma optimize_sound: 
  assumes "maximize A b c = Some (Sat x)"
  shows "x \<in> max_lp A b c"
proof -
  have *: "dim_vec b = dim_row A \<and> dim_vec c = dim_col A"
    by (metis assms maximize.simps option.distinct(1))
  then interpret rat: rat_LP A b c "dim_vec b" "dim_vec c"
    by (metis abstract_LP_def carrier_mat_triv carrier_vec_dim_vec rat_LP.intro)
  have "Sat x = optimize_no_cond A b c"
    using assms * by auto
  then show ?thesis
    by (simp add: rat.optimize_no_cond_correct)
qed

lemma maximize_option_elim:
  assumes "maximize A b c = Some x"
  shows "dim_vec b = dim_row A" "dim_vec c = dim_col A"
  by (metis assms maximize.simps option.distinct(1))+

lemma optimize_sol_dimension: 
  assumes "maximize A b c = Some (Sat x)"
  shows "x \<in> carrier_vec (dim_col A)"
  using assms carrier_dim_vec max_lp_in_sat_primal optimize_sound sol_dim_in_sat_primal by blast

lemma optimize_sat:
  assumes "maximize A b c = Some (Sat x)"
  shows "[A *\<^sub>v x]\<le>b"
  using assms maximize_option_elim[OF assms]
    max_lp_in_sat_primal[OF optimize_sound[of A b c x, OF assms]] by blast


derive (eq) ceq rat
derive (linorder) compare rat
derive (compare) ccompare rat
derive (rbt) set_impl rat

derive (eq) ceq atom QDelta
derive (linorder) compare_order QDelta
derive compare_order atom
derive ccompare atom QDelta
derive (rbt) set_impl atom QDelta


(*export_code maximize mat_of_cols_list mat_of_rows_list mat_of_cols vec_of_list quotient_of Inr Inl Some None list_of_vec nat
Rat.Fract int_of_integer in Haskell module_name LP  file "/home/julian/coding/ForGET/LPBenchmarks/HaskellLP/src" 
*)
(*
export_code  maximize mat_of_cols_list mat_of_rows_list mat_of_cols vec_of_list quotient_of Inr Inl Some None list_of_vec nat
Rat.Fract int_of_integer in Scala
*)


(*
section \<open> Testing \<close>
lemma "(let A = mat_of_rows 3 (map vec_of_list [[1, 12, 2], [1, 5, 9], [-1,0,0], [0,-1,0],[0,0,-1]]) in
       (let b = vec_of_list [10000, 8539,0,0,0] in
       (let c = vec_of_list [100, 600, 400] in
       maximize A b c))) =  Some (Inr (vec_of_list [52468 / 7, 1461 / 7, 0]))"
  by eval

lemma "(let A = mat_of_cols 4 (map vec_of_list [[2::rat, -1, -1, 1/2], [1, 2, -1, -1/2]]) in
       (let b = vec_of_list [5, 2, -1, 1/2] in
       (let c = vec_of_list [7, 1::rat] in
       maximize A b c))) = Some (Inr (vec_of_list [2::rat, 1]))"
  by eval
*)

(*
value "(let A = mat_of_cols_list 4 [[-1::rat, -1, -0, 1], [1, -1, -1, -2]] in
       (let b = vec_of_list [1, -2, -0, 4] in
       (let c = vec_of_list [-2, 1::rat] in
       maximize A b c)))"

value "(let A = mat_of_cols 4 (map vec_of_list [[2::rat, 2, -1, 0], [3, 1, 0, -1]]) in
       (let b = vec_of_list [1500::rat,1000,0,0] in
       (let c = vec_of_list [50, 40::rat] in
       maximize A b c)))"
 (*  Sol should be 375, 250 *)

value "(let A = mat_of_cols 2 (map vec_of_list [[-1::rat, 1], [-1,-1]]) in
       (let b = vec_of_list [2::rat, 2] in
       (let c = vec_of_list [0, 1::rat] in
       maximize A b c)))"
  (* Sol should be 375, 250 *)

value "(let A = mat_of_rows 2 (map vec_of_list [[2::rat,3],[2, 1], [-1,0],[0,-1]]) in
       (let b = vec_of_list [1500::rat,1000,0,0] in
       (let c = vec_of_list [50, 40::rat] in
       maximize A b c)))"
  (* Sol should be 375, 250 *)
*)


lemma of_rat_val: "simplex cs = (Sat v) \<Longrightarrow> of_rat_val \<langle>v\<rangle> \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set cs"
  using of_rat_val_constraint simplex_real(3) by blast


end