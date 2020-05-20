theory Matrix_LinPoly
  imports 
    Jordan_Normal_Form.Matrix_Impl
    Farkas.Simplex_for_Reals
    Farkas.Matrix_Farkas
begin


text \<open> Add this to linear polynomials in Simplex \<close>

lemma eval_poly_with_sum: "(v \<lbrace> X \<rbrace>) = (\<Sum>x\<in> vars v. coeff v x * X x)"
  using linear_poly_sum sum.cong by fastforce

lemma eval_poly_with_sum_superset:
  assumes "finite S"
  assumes "S \<supseteq> vars v"
  shows "(v \<lbrace>X\<rbrace>) = (\<Sum>x\<in>S. coeff v x * X x)"
proof -
  define D where D: "D = S - vars v"
  have zeros: "\<forall>x \<in> D. coeff v x = 0"
    using D coeff_zero by auto
  have fnt: "finite (vars v)"
    using finite_vars by auto
  have "(v \<lbrace>X\<rbrace>) = (\<Sum>x\<in> vars v. coeff v x * X x)" 
    using linear_poly_sum sum.cong by fastforce
  also have "... = (\<Sum>x\<in> vars v. coeff v x * X x) + (\<Sum>x\<in>D. coeff v x * X x)"
    using zeros by auto
  also have "... = (\<Sum>x\<in> vars v \<union> D. coeff v x * X x)"
    using assms(1) fnt Diff_partition[of "vars v" S, OF assms(2)] 
      sum.subset_diff[of "vars v" S, OF assms(2) assms(1)]
    by (simp add: \<open>\<And>g. sum g S = sum g (S - vars v) + sum g (vars v)\<close> D)
  also have "... = (\<Sum>x\<in>S. coeff v x * X x)"
    using D Diff_partition assms(2) by fastforce
  finally show ?thesis .
qed


text \<open> Get rid of these synonyms \<close>

section \<open> Translations of Jordan Normal Forms Matrix Library to Simplex polynomials \<close>


subsection \<open> Vectors \<close>

(* Translate rat list to linear polynomial with same coefficients *)

definition list_to_lpoly where
    "list_to_lpoly cs = sum_list (map2 (\<lambda> i c. lp_monom c i) [0..<length cs] cs)" 


lemma empty_list_0poly:
  shows "list_to_lpoly [] = 0"
  unfolding list_to_lpoly_def by simp

lemma sum_list_map_upto_coeff_limit:
  assumes "i \<ge> length L"
  shows "coeff (list_to_lpoly L) i = 0"
  using assms by (induction L rule: rev_induct) (auto simp: list_to_lpoly_def)

lemma rl_lpoly_coeff_nth_non_empty:
  assumes "i < length cs"
  assumes "cs \<noteq> []"
  shows "coeff (list_to_lpoly cs) i = cs!i"
  using assms(2) assms(1) 
proof (induction cs rule: rev_nonempty_induct)
  fix x ::rat
  assume "i < length [x]"
  have "(list_to_lpoly [x]) = lp_monom x 0"
    by (simp add: list_to_lpoly_def)
  then show "coeff (list_to_lpoly [x]) i = [x] ! i"
    using \<open>i < length [x]\<close> list_to_lpoly_def by auto
next
  fix x :: rat
  fix xs :: "rat list"
  assume "xs \<noteq> []"
  assume IH: "i < length xs \<Longrightarrow> coeff (list_to_lpoly xs) i = xs ! i"
  assume "i < length (xs @ [x])"
  consider (le) "i < length xs" | (eq) "i = length xs"
    using \<open>i < length (xs @ [x])\<close> less_Suc_eq by auto
  then show "coeff (list_to_lpoly (xs @ [x])) i = (xs @ [x]) ! i"
  proof (cases)
    case le
    have "coeff (lp_monom x (length xs)) i = 0"
      using le by auto
    have "coeff (sum_list (map2 (\<lambda>x y. lp_monom y x) 
          [0..<length (xs @ [x])] (xs @ [x]))) i = (xs @ [x]) ! i"
      apply(simp add: IH le nth_append)
      using IH le list_to_lpoly_def by auto
    then show ?thesis 
      unfolding list_to_lpoly_def by simp
  next
    case eq
    then have *: "coeff (sum_list (map2 (\<lambda>x y. lp_monom y x) [0..<length xs] xs)) i = 0"
      using sum_list_map_upto_coeff_limit[of xs i]
      by (simp add: list_to_lpoly_def)
    have **: "(sum_list (map2 (\<lambda> x y. lp_monom y x) [0..<length (xs @ [x])] (xs @ [x]))) = 
          sum_list (map (\<lambda>(x,y). lp_monom y x) (zip [0..<length xs] xs)) + lp_monom x (length xs)"
      by simp
    have "coeff ((list_to_lpoly xs) + lp_monom x (length xs)) i = x"
      unfolding list_to_lpoly_def using * ** by (simp add: eq)
    then show ?thesis
      by (simp add: eq list_to_lpoly_def)
  qed
qed

lemma list_to_lpoly_coeff_nth:
  assumes "i < length cs "
  shows "coeff (list_to_lpoly cs) i = cs ! i"
  using gr_implies_not0 rl_lpoly_coeff_nth_non_empty assms by fastforce

lemma rat_list_outside_zero:
  assumes "length cs \<le> i"
  shows "coeff (list_to_lpoly cs) i = 0"
  using sum_list_map_upto_coeff_limit[of cs i, OF assms] by simp



text \<open> Transform linear polynomials to rational vectors \<close>

fun dim_poly where
  "dim_poly p = (if (vars p) = {} then 0 else Max (vars p)+1)" 
(* 0, 0, 0, 3, 0, 0, \<dots> has dimension 4 , consistent with  dim vec  *)

definition max_dim_poly_list where
  "max_dim_poly_list lst = Max {Max (vars p) |p. p \<in> set lst}"

fun lpoly_to_vec where
    "lpoly_to_vec p = vec (dim_poly p) (coeff p)"

lemma all_greater_dim_poly_zero[simp]: 
  assumes "x \<ge> dim_poly p" 
  shows "coeff p x = 0"
  using Max_ge[of "vars p" x, OF finite_vars[of p]] coeff_zero[of p x] 
  by (metis add_cancel_left_right assms dim_poly.elims empty_iff leD le_eq_less_or_eq 
      trans_less_add1 zero_neq_one_class.zero_neq_one)

lemma lpoly_to_vec_0_iff_zero_poly [iff]:
  shows "(lpoly_to_vec p) = 0\<^sub>v 0 \<longleftrightarrow> p = 0"
proof(standard)
  show "lpoly_to_vec p = 0\<^sub>v 0 \<Longrightarrow> p = 0"
  proof (rule contrapos_pp)
    assume "p \<noteq> 0"
    then have "vars p \<noteq> {}"
      by (simp add: vars_empty_zero)
    then have "dim_poly p > 0"
      by (simp)
    then show "lpoly_to_vec p \<noteq> 0\<^sub>v 0"
      using vec_of_dim_0[of "lpoly_to_vec p"]  by simp
  qed
next
qed (auto simp: vars_empty_zero)

lemma dim_poly_dim_vec_equiv:
  "dim_vec (lpoly_to_vec p) = dim_poly p"
  using lpoly_to_vec.simps by auto

lemma dim_poly_greater_ex_coeff: "dim_poly x > d \<Longrightarrow> \<exists>i\<ge>d. coeff x i \<noteq> 0"
   by (simp split: if_splits) (meson Max_in coeff_zero finite_vars less_Suc_eq_le)

lemma dimpoly_all_zero_limit: 
  assumes "\<And>i. i \<ge> d \<Longrightarrow> coeff x i = 0"
  shows "dim_poly x \<le> d"
proof -
  have "(\<forall>i\<ge> d. coeff x i = 0) \<Longrightarrow> dim_poly x \<le> d "
  proof (rule contrapos_pp)
    assume "\<not> dim_poly x \<le> d"
    then have "dim_poly x > d" by linarith
    then have "\<exists>i \<ge> d. coeff x i \<noteq> 0"
      using dim_poly_greater_ex_coeff[of d x] by blast
    then show "\<not> (\<forall>i\<ge>d. coeff x i = 0)"
      by blast
  qed
  then show ?thesis
    using assms by blast
qed

lemma construct_poly_from_lower_dim_poly: 
  assumes "dim_poly x = d+1"
  obtains p c where "dim_poly p \<le> d" "x = p + lp_monom c d"
proof -
  define c' where c': "c' = coeff x d"
  have f: "\<forall>i>d. coeff x i = 0"
    using assms by auto  
  have *: "x = x - (lp_monom c' d) + (lp_monom c' d)"
    by simp
  have "coeff (x - (lp_monom c' d)) d = 0"
    using c' by simp
  then have "\<forall>i\<ge>d. coeff (x - (lp_monom c' d)) i = 0"
    using f by auto
  then have **: "dim_poly (x - (lp_monom c' d)) \<le> d"
    using dimpoly_all_zero_limit[of d "(x - (lp_monom c' d))"] by auto
  define p' where p': "p' = x - (lp_monom c' d)"
  have "\<exists>p c. dim_poly p \<le> d \<and> x = p + lp_monom c d" 
    using "*" "**" by blast
  then show ?thesis 
    using * p' c' that by blast
qed

lemma vars_subset_0_dim_poly:
  "vars z \<subseteq> {0..<dim_poly z}"
  by (simp add: finite_vars less_Suc_eq_le subsetI)

lemma in_dim_and_not_var_zero: "x \<in> {0..<dim_poly z} - vars z \<Longrightarrow> coeff z x = 0"
  using coeff_zero by auto

lemma valuate_with_dim_poly: "z \<lbrace> X \<rbrace> = (\<Sum>i\<in>{0..<dim_poly z}. coeff z i * X i)"
  using eval_poly_with_sum_superset[of "{0..<dim_poly z}" z X] using vars_subset_0_dim_poly by blast

lemma lin_poly_to_vec_coeff_access:
  assumes "x < dim_poly y"
  shows "(lpoly_to_vec y) $ x = coeff y x"
proof -
  have "x < dim_vec (lpoly_to_vec y)"
    using dim_poly_dim_vec_equiv[of y] assms by auto
  then show ?thesis
    by (simp add: coeff_def)
qed

lemma addition_over_lin_poly_to_vec:
  fixes x y
  assumes "a < dim_poly x"
  assumes "dim_poly x = dim_poly y"
  shows  "(lpoly_to_vec x + lpoly_to_vec y) $ a = coeff (x + y) a"
  using assms(1) assms(2) lin_poly_to_vec_coeff_access by (simp add: dim_poly_dim_vec_equiv)

lemma list_to_lpoly_dim_less: "length cs \<ge> dim_poly (list_to_lpoly cs)"
  using dimpoly_all_zero_limit sum_list_map_upto_coeff_limit by blast


text \<open> Transform rational vectors to linear polynomials \<close>

fun vec_to_lpoly where 
  "vec_to_lpoly rv = list_to_lpoly (list_of_vec rv)"

lemma vec_to_lin_poly_coeff_access:
  assumes "x < dim_vec y"           
  shows "y $ x = coeff (vec_to_lpoly y) x"
  by (simp add: assms list_to_lpoly_coeff_nth)

lemma addition_over_vec_to_lin_poly:
  fixes x y
  assumes "a < dim_vec x"
  assumes "dim_vec x = dim_vec y"
  shows  "(x + y) $ a = coeff (vec_to_lpoly x + vec_to_lpoly y) a"
  using  assms(1) assms(2) coeff_plus index_add_vec(1)
  by (metis vec_to_lin_poly_coeff_access)

lemma outside_list_coeff0:
  assumes "i \<ge> dim_vec xs"
  shows "coeff (vec_to_lpoly xs) i = 0"
  by (simp add: assms sum_list_map_upto_coeff_limit)

lemma vec_to_poly_dim_less:
  "dim_poly (vec_to_lpoly x) \<le> dim_vec x"
  using list_to_lpoly_dim_less[of "list_of_vec x"] by simp

lemma vec_to_lpoly_from_lpoly_coeff_dual1: 
  "coeff (vec_to_lpoly (lpoly_to_vec p)) i = coeff p i"
  by (metis all_greater_dim_poly_zero dim_poly_dim_vec_equiv lin_poly_to_vec_coeff_access
      not_less outside_list_coeff0 vec_to_lin_poly_coeff_access)

lemma vec_to_lpoly_from_lpoly_coeff_dual2:
  assumes "i < dim_vec (lpoly_to_vec (vec_to_lpoly v))" 
  shows "(lpoly_to_vec (vec_to_lpoly v)) $ i = v $ i"
  by (metis assms dim_poly_dim_vec_equiv less_le_trans lin_poly_to_vec_coeff_access 
      vec_to_lin_poly_coeff_access vec_to_poly_dim_less)

lemma vars_subset_dim_vec_to_lpoly_dim: "vars (vec_to_lpoly v) \<subseteq> {0..<dim_vec v}"
  by (meson ivl_subset le_numeral_extra(3) order.trans vec_to_poly_dim_less
      vars_subset_0_dim_poly)

lemma sum_dim_vec_equals_sum_dim_poly:
  shows "(\<Sum>a = 0..<dim_vec A. coeff (vec_to_lpoly  A) a * X a) = 
         (\<Sum>a = 0..<dim_poly (vec_to_lpoly A). coeff (vec_to_lpoly  A) a * X a)"
proof -
  consider (eq) "dim_vec A = dim_poly (vec_to_lpoly A)" |
           (le) "dim_vec A > dim_poly (vec_to_lpoly A)"
    using vec_to_poly_dim_less[of "A"] by fastforce
  then show ?thesis
  proof (cases)
    case le
    define dp where dp: "dp = dim_poly (vec_to_lpoly A)"
    have "(\<Sum>a = 0..<dim_vec A. coeff (vec_to_lpoly A) a * X a) = 
          (\<Sum>a = 0..<dp. coeff (vec_to_lpoly A) a * X a) +
          (\<Sum>a = dp..<dim_vec A. coeff (vec_to_lpoly A) a * X a)"
      by (metis (no_types, lifting) dp vec_to_poly_dim_less sum.atLeastLessThan_concat zero_le)
    also have "... = (\<Sum>a = 0..<dp. coeff (vec_to_lpoly A) a * X a)"
      using all_greater_dim_poly_zero by (simp add: dp)
    also have "... = (\<Sum>a = 0..<dim_poly (vec_to_lpoly A).coeff (vec_to_lpoly A) a * X a)"
      using dp by auto
    finally show ?thesis
      by blast
  qed (auto)
qed

lemma vec_to_lpoly_vNil [simp]: "vec_to_lpoly vNil = 0"
  by (simp add: empty_list_0poly)

lemma zero_vector_is_zero_poly: "coeff (vec_to_lpoly (0\<^sub>v n)) i = 0"
  by (metis index_zero_vec(1) index_zero_vec(2) not_less 
      outside_list_coeff0 vec_to_lin_poly_coeff_access)

lemma coeff_nonzero_dim_vec_non_zero:
  assumes "coeff (vec_to_lpoly v) i \<noteq> 0"
  shows "v $ i \<noteq> 0" "i < dim_vec v"
  apply (metis assms leI outside_list_coeff0 vec_to_lin_poly_coeff_access)
  using assms leI outside_list_coeff0 by blast

lemma lpoly_of_v_equals_v_append0: 
  "vec_to_lpoly v = vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)" (is "?lhs = ?rhs")
proof -
  have "\<forall>i. coeff ?lhs i = coeff ?rhs i"
  proof 
    fix i
    consider (le) "i < dim_vec v" | (ge) "i \<ge> dim_vec v"
      using leI by blast
    then show "coeff (vec_to_lpoly v) i = coeff (vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)) i"
    proof (cases)
      case le
      then show ?thesis using vec_to_lin_poly_coeff_access[of i v] index_append_vec(1)
        by (metis  index_append_vec(2) vec_to_lin_poly_coeff_access trans_less_add1)
    next
      case ge
      then have "coeff (vec_to_lpoly v) i = 0"
        using outside_list_coeff0 by blast
      moreover have "coeff (vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)) i = 0" 
      proof (rule ccontr)
        assume na: "\<not> coeff (vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)) i = 0" 
        define va where v: "va = coeff (vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)) i"
        have "i < dim_vec (v @\<^sub>v 0\<^sub>v a)"
          using coeff_nonzero_dim_vec_non_zero[of "(v @\<^sub>v 0\<^sub>v a)" i] na by blast
        moreover have "(0\<^sub>v a) $ (i - dim_vec v) = va"
          by (metis ge diff_is_0_eq' index_append_vec(1) index_append_vec(2) 
              not_less_zero vec_to_lin_poly_coeff_access v zero_less_diff calculation)
        moreover have "va \<noteq> 0" using v na by linarith
        ultimately show False
          using ge by auto
      qed
      then show "coeff (vec_to_lpoly v) i = coeff (vec_to_lpoly (v @\<^sub>v 0\<^sub>v a)) i"
        using  not_less using calculation by linarith
    qed
  qed
  then show ?thesis
    using Abstract_Linear_Poly.poly_eqI by blast
qed

lemma vec_to_lpoly_eval_dot_prod:
"(vec_to_lpoly v) \<lbrace> x \<rbrace> = v \<bullet> (vec (dim_vec v) x)"
proof -
  have "(vec_to_lpoly v) \<lbrace> x \<rbrace> = (\<Sum>i\<in>{0..<dim_vec v}. coeff (vec_to_lpoly v) i * x i)"
    using eval_poly_with_sum_superset[of "{0..<dim_vec v}" "vec_to_lpoly v" x]
      vars_subset_dim_vec_to_lpoly_dim by blast
  also have "... = (\<Sum>i\<in>{0..<dim_vec v}. v$i * x i)"
    using list_to_lpoly_coeff_nth by auto
  also have "... =  v \<bullet> (vec (dim_vec v) x)" 
    unfolding scalar_prod_def by auto
  finally show ?thesis .
qed

lemma dim_poly_of_append_vec:
  "dim_poly (vec_to_lpoly (a@\<^sub>vb)) \<le> dim_vec a + dim_vec b"
  using vec_to_poly_dim_less[of "a@\<^sub>vb"] index_append_vec(2)[of a b] by auto

lemma vec_coeff_append1: "i \<in> {0..<dim_vec a} \<Longrightarrow> coeff (vec_to_lpoly (a@\<^sub>vb)) i = a$i"
  by (metis atLeastLessThan_iff index_append_vec(1) index_append_vec(2) vec_to_lin_poly_coeff_access trans_less_add1)

lemma vec_coeff_append2: 
  "i \<in> {dim_vec a..<dim_vec (a@\<^sub>vb)} \<Longrightarrow> coeff (vec_to_lpoly (a@\<^sub>vb)) i = b$(i-dim_vec a)"
  by (metis atLeastLessThan_iff index_append_vec(1) index_append_vec(2) leD vec_to_lin_poly_coeff_access)

text \<open> Maybe Code Equation \<close>
lemma vec_to_lpoly_poly_of_vec_eq: "vec_to_lpoly v = poly_of_vec v"
proof -
  have "\<And>i. i < dim_vec v \<Longrightarrow> coeff (poly_of_vec v) i = v $ i"
    by (simp add: coeff.rep_eq poly_of_vec.rep_eq)
  moreover have "\<And>i. i < dim_vec v \<Longrightarrow> coeff (vec_to_lpoly v) i = v $ i"
    by (simp add: vec_to_lin_poly_coeff_access)
  moreover have "\<And>i. i \<ge> dim_vec v \<Longrightarrow> coeff (poly_of_vec v) i = 0"
    by (simp add: coeff.rep_eq poly_of_vec.rep_eq)
  moreover have "\<And>i. i \<ge> dim_vec v \<Longrightarrow> coeff (vec_to_lpoly v) i = 0"
    using outside_list_coeff0 by blast
  ultimately show ?thesis
    by (metis Abstract_Linear_Poly.poly_eq_iff le_less_linear)
qed

lemma vars_vec_append_subset: "vars (vec_to_lpoly (0\<^sub>v n @\<^sub>v v)) \<subseteq> {n..<n+dim_vec v}"
proof -
  let ?p = "(vec_to_lpoly (0\<^sub>v n @\<^sub>v v))"
  have "dim_poly ?p \<le> n+dim_vec v"
    using dim_poly_of_append_vec[of "0\<^sub>v n" "v"] by auto
  have "vars (vec_to_lpoly (0\<^sub>v n @\<^sub>v v)) \<subseteq> {0..<n+dim_vec v}"
    using vars_subset_dim_vec_to_lpoly_dim[of "(0\<^sub>v n @\<^sub>v v)"] by auto
  moreover have "\<forall>i < n. coeff ?p i = 0"
    using vec_coeff_append1[of _ "0\<^sub>v n" v] by auto
  ultimately show "vars (vec_to_lpoly (0\<^sub>v n @\<^sub>v v)) \<subseteq> {n..<n+dim_vec v}"
    by (meson atLeastLessThan_iff coeff_zero not_le subsetCE subsetI)
qed


section \<open> Matrices \<close>

(* \<open> From \<open> mat \<close> to \<open> linear_poly list \<close>  *)

fun matrix_to_lpolies where
  "matrix_to_lpolies A = map vec_to_lpoly (rows A)" 

lemma matrix_to_lpolies_vec_of_row: 
  "i <dim_row A \<Longrightarrow> matrix_to_lpolies A ! i = vec_to_lpoly (row A i)"
  using matrix_to_lpolies.simps[of A] by simp

lemma outside_of_col_range_is_0:
  assumes "i < dim_row A" and "j \<ge> dim_col A"
  shows "coeff ((matrix_to_lpolies A)!i) j = 0"
  using outside_list_coeff0[of "col A i" j]
  by (metis assms(1) assms(2) index_row(2) length_rows matrix_to_lpolies.simps nth_map nth_rows outside_list_coeff0)

lemma polys_greater_col_zero:
  assumes "x \<in> set (matrix_to_lpolies A)"
  assumes "j \<ge> dim_col A"
  shows "coeff x j = 0"
  using  assms(1) assms(2) outside_of_col_range_is_0[of _ A j] 
    assms(2) matrix_to_lpolies.simps by (metis in_set_conv_nth length_map length_rows)

lemma matrix_to_lp_vec_to_lpoly_row [simp]:
  assumes "i < dim_row A"
  shows "(matrix_to_lpolies A)!i = vec_to_lpoly (row A i)"
  by (simp add: assms)

lemma matrix_to_lpolies_coeff_access: 
  assumes "i < dim_row A" and "j < dim_col A"
  shows "coeff (matrix_to_lpolies A ! i) j = A $$ (i,j)"
  using matrix_to_lp_vec_to_lpoly_row[of i A, OF assms(1)]
  by (metis assms(1) assms(2) index_row(1) index_row(2) vec_to_lin_poly_coeff_access)


text \<open> From linear polynomial list to matrix \<close>

definition lin_polies_to_mat where
    "lin_polies_to_mat lst = mat (length lst) (max_dim_poly_list lst) (\<lambda>(x,y).coeff (lst!x) y)"


lemma lin_polies_to_rat_mat_coeff_index: 
  assumes "i < length L" and "j <  (max_dim_poly_list L)"
  shows "coeff (L ! i) j = (lin_polies_to_mat L) $$ (i,j)"
  unfolding lin_polies_to_mat_def by (simp add: assms(1) assms(2))


lemma vec_to_lpoly_valuate_equiv_dot_prod:
  assumes "dim_vec y = dim_vec x"  (* Can be \<ge> *)
  shows "(vec_to_lpoly y) \<lbrace> ($)x \<rbrace> = y \<bullet> x"
proof -
  let ?p = "vec_to_lpoly y"
  have 2: "?p\<lbrace> ($)x \<rbrace> = (\<Sum>j\<in>vars?p. coeff ?p j * x$j)"
    using eval_poly_with_sum[of ?p "($)x"] by blast
  have "vars ?p \<subseteq> {0..<dim_vec y}"
    using vars_subset_dim_vec_to_lpoly_dim by blast
    have 2: "?p\<lbrace> ($)x \<rbrace> = (\<Sum>j\<in>vars?p. coeff ?p j * x$j)"
    using eval_poly_with_sum[of ?p "($)x"] by blast
  also have *: "... = (\<Sum>i\<in>{0..<dim_poly ?p}. coeff ?p i * x$i)"
    using valuate_with_dim_poly by (metis (no_types, lifting) calculation sum.cong) 
  also have "... = y \<bullet> x"
  proof -
    have "\<And>j. j < dim_vec x \<Longrightarrow> coeff (vec_to_lpoly y) j = y $ j" 
      using assms vec_to_lin_poly_coeff_access by auto
    then show ?thesis
      using vec_to_lpoly_eval_dot_prod[of "y" "($)x"]
      by (metis assms calculation dim_vec index_vec vec_eq_iff)
    qed
  finally show ?thesis unfolding scalar_prod_def .
qed

lemma matrix_to_lpolies_valuate_scalarP:
  assumes "i < dim_row A"
assumes "dim_col A = dim_vec x"
shows "(matrix_to_lpolies A!i) \<lbrace> ($)x \<rbrace> = (row A i) \<bullet> x"
  using vec_to_lpoly_valuate_equiv_dot_prod[of "row A i" x]
  by (simp add: assms(1) assms(2))

lemma matrix_to_lpolies_lambda_valuate_scalarP:
  assumes "i < dim_row A"
  assumes "dim_col A = dim_vec x"
shows "(matrix_to_lpolies A!i) \<lbrace> (\<lambda>i. (if i < dim_vec x then x$i else 0)) \<rbrace> = (row A i) \<bullet> x"
proof -
  have "\<And>j. j < dim_vec x \<Longrightarrow> x$j = (\<lambda>i. (if i < dim_vec x then x$i else 0)) j"
    by simp
  let ?p = "(matrix_to_lpolies A!i)"
  have "\<And>j. coeff (matrix_to_lpolies A!i) j \<noteq> 0 \<Longrightarrow> j < dim_vec x"
    using outside_of_col_range_is_0[of i A] assms(1) assms(2) leI by auto
  then have subs: "vars ?p \<subseteq> {0..<dim_vec x}"
    using \<open>\<And>j. Abstract_Linear_Poly.coeff (matrix_to_lpolies A ! i) j \<noteq> 0 \<Longrightarrow> j < dim_vec x\<close> atLeastLessThan_iff coeff_zero by blast
  then have *: "\<And>j. j \<in> vars ?p \<Longrightarrow> x$j = (\<lambda>i. (if i < dim_vec x then x$i else 0)) j"
    by (simp add: \<open>\<And>j. Abstract_Linear_Poly.coeff (matrix_to_lpolies A ! i) j \<noteq> 0 \<Longrightarrow> j < dim_vec x\<close> coeff_zero)
   have "row A i \<bullet> x = (?p \<lbrace> ($) x \<rbrace>)"
    using assms(1) assms(2) matrix_to_lpolies_valuate_scalarP[of i A x] by linarith
  also have "... = (\<Sum>j\<in> vars ?p. coeff ?p j * x$j)"
    using eval_poly_with_sum by blast
  also have "... = (\<Sum>j\<in> vars ?p. coeff ?p j * (\<lambda>i. (if i < dim_vec x then x$i else 0)) j)"
    by (metis (full_types, hide_lams) \<open>\<And>j. Abstract_Linear_Poly.coeff (matrix_to_lpolies A ! i) j \<noteq> 0 \<Longrightarrow> j < dim_vec x\<close> mult.commute mult_zero_right)
  also have "... = (?p \<lbrace> (\<lambda>i. (if i < dim_vec x then x$i else 0)) \<rbrace>)"
    using eval_poly_with_sum by presburger
  finally show ?thesis
    by linarith 
qed


end