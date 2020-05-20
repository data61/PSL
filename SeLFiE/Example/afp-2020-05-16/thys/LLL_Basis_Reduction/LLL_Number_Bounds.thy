(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Explicit Bounds for Size of Numbers that Occur During LLL Algorithm\<close>

text \<open>The LLL invariant does not contain bounds on the number that occur during the execution. 
  We here strengthen the invariant so that it enforces bounds on the norms of the $f_i$ and $g_i$
  and we prove that the stronger invariant is maintained throughout the execution of the LLL algorithm.

  Based on the stronger invariant we prove bounds on the absolute values of the $\mu_{i,j}$,
  and on the absolute values of the numbers in the vectors $f_i$ and $g_i$. 
  Moreover, we further show that also the denominators in all of these numbers doesn't grow to much.
  Finally, we prove that each number (i.e., numerator or denominator) during the execution 
  can be represented with at most ${\cal O}(m \cdot \log(M \cdot n))$ bits, where
  $m$ is the number of input vectors, $n$ is the dimension of the input vectors,
  and $M$ is the maximum absolute value of all numbers in the input vectors.
  Hence, each arithmetic operation in the LLL algorithm can be performed in polynomial time.\<close>
theory LLL_Number_Bounds
  imports LLL
    Gram_Schmidt_Int
begin



context LLL
begin

text \<open>The bounds for the $f_i$ distinguishes whether we are inside or outside the inner for-loop.\<close>

definition f_bound :: "bool \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "f_bound outside ii fs = (\<forall> i < m. sq_norm (fs ! i) \<le> (if i \<noteq> ii \<or> outside then int (N * m) else 
     int (4 ^ (m - 1) * N ^ m * m * m)))" 

definition "\<mu>_bound_row fs bnd i = (\<forall> j \<le> i. (\<mu> fs i j)^2 \<le> bnd)" 
abbreviation "\<mu>_bound_row_inner fs i j \<equiv> \<mu>_bound_row fs (4 ^ (m - 1 - j) * of_nat (N ^ (m - 1) * m)) i"  

definition "LLL_bound_invariant outside upw i fs =
  (LLL_invariant upw i fs \<and> f_bound outside i fs \<and> g_bound fs)" 

lemma bound_invD: assumes "LLL_bound_invariant outside upw i fs" 
  shows "LLL_invariant upw i fs" "f_bound outside i fs" "g_bound fs"
  using assms unfolding LLL_bound_invariant_def by auto

lemma bound_invI: assumes "LLL_invariant upw i fs" "f_bound outside i fs" "g_bound fs" 
  shows "LLL_bound_invariant outside upw i fs"
  using assms unfolding LLL_bound_invariant_def by auto

lemma \<mu>_bound_rowI: assumes "\<And> j. j \<le> i \<Longrightarrow> (\<mu> fs i j)^2 \<le> bnd"
  shows "\<mu>_bound_row fs bnd i" 
  using assms unfolding \<mu>_bound_row_def by auto

lemma \<mu>_bound_rowD: assumes "\<mu>_bound_row fs bnd i" "j \<le> i"
  shows "(\<mu> fs i j)^2 \<le> bnd"
  using assms unfolding \<mu>_bound_row_def by auto

lemma \<mu>_bound_row_1: assumes "\<mu>_bound_row fs bnd i" 
  shows "bnd \<ge> 1"
proof -
  interpret gs1: gram_schmidt_fs n "RAT fs" .
  show ?thesis
  using \<mu>_bound_rowD[OF assms, of i]
  by (auto simp: gs1.\<mu>.simps)
qed

lemma reduced_\<mu>_bound_row: assumes red: "reduced fs i"  
  and ii: "ii < i" 
shows "\<mu>_bound_row fs 1 ii"
proof (intro \<mu>_bound_rowI)
  fix j
  assume "j \<le> ii"
  interpret gs1: gram_schmidt_fs n "RAT fs" .
  show "(\<mu> fs ii j)^2 \<le> 1"
  proof (cases "j < ii")
    case True
    from red[unfolded gram_schmidt_fs.reduced_def, THEN conjunct2, rule_format, OF ii True]
    have "abs (\<mu> fs ii j) \<le> 1/2" by auto
    from mult_mono[OF this this]
    show ?thesis by (auto simp: power2_eq_square)
  qed (auto simp: gs1.\<mu>.simps)
qed

lemma f_bound_True_arbitrary: assumes "f_bound True ii fs"
  shows "f_bound outside j fs" 
  unfolding f_bound_def 
proof (intro allI impI, rule ccontr, goal_cases)
  case (1 i)
  from 1 have nz: "\<parallel>fs ! i\<parallel>\<^sup>2 \<noteq> 0" by (auto split: if_splits)
  hence gt: "\<parallel>fs ! i\<parallel>\<^sup>2 > 0" using sq_norm_vec_ge_0[of "fs ! i"] by auto
  from assms(1)[unfolded f_bound_def, rule_format, OF 1(1)]
  have one: "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> int (N * m) * 1" by auto
  from less_le_trans[OF gt one] have N0: "N \<noteq> 0" by (cases "N = 0", auto)
  note one
  also have "int (N * m) * 1 \<le> int (N * m) * int (4 ^ (m - 1) * N ^ (m - 1) * m)"
    by (rule mult_left_mono, unfold of_nat_mult, intro mult_ge_one, insert 1 N0, auto)  
  also have "\<dots> = int (4 ^ (m - 1) * N ^ (Suc (m - 1)) * m * m)" unfolding of_nat_mult by simp
  also have "Suc (m - 1) = m" using 1 by simp
  finally show ?case using one 1 by (auto split: if_splits)
qed


context fixes fs :: "int vec list" 
  assumes lin_indep: "lin_indep fs" 
  and len: "length fs = m" 
begin

interpretation fs: fs_int_indpt n fs
  by (standard) (use lin_indep in simp)


lemma sq_norm_fs_mu_g_bound: assumes i: "i < m" 
  and mu_bound: "\<mu>_bound_row fs bnd i" 
  and g_bound: "g_bound fs" 
shows "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * N) * bnd" 
proof -
  have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2)" 
    by (rule fs.sq_norm_fs_via_sum_mu_gso) (use assms lin_indep len in auto)
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<Suc i]. bnd * of_nat N)" 
  proof (rule sum_list_ge_mono, force, unfold length_map length_upt,
    subst (1 2) nth_map_upt, force, goal_cases)
    case (1 j)
    hence ji: "j \<le> i" by auto
    from g_bound[unfolded g_bound_def] i ji 
    have GB: "sq_norm (gso fs j) \<le> of_nat N" by auto
    show ?case 
      by (rule mult_mono, insert \<mu>_bound_rowD[OF mu_bound ji]
          GB order.trans[OF zero_le_power2], auto)
  qed
  also have "\<dots> = of_nat (Suc i) * (bnd * of_nat N)" unfolding sum_list_triv length_upt by simp
  also have "\<dots> = of_nat (Suc i * N) * bnd" unfolding of_nat_mult by simp
  finally show ?thesis .
qed
end

lemma increase_i_bound: assumes LLL: "LLL_bound_invariant True upw i fs" 
  and i: "i < m" 
  and upw: "upw \<Longrightarrow> i = 0" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i)"
shows "LLL_bound_invariant True True (Suc i) fs" 
proof -
  from bound_invD[OF LLL] have LLL: "LLL_invariant upw i fs" 
    and "f_bound True i fs" and gbnd: "g_bound fs" by auto
  hence fbnd: "f_bound True (Suc i) fs" by (auto simp: f_bound_def)
  from increase_i[OF LLL i upw red_i]
  have inv: "LLL_invariant True (Suc i) fs" and "LLL_measure (Suc i) fs < LLL_measure i fs" (is ?g2) 
    by auto
  show "LLL_bound_invariant True True (Suc i) fs" 
    by (rule bound_invI[OF inv fbnd gbnd])
qed

text \<open>Addition step preserves @{term "LLL_bound_invariant False"}\<close>

lemma basis_reduction_add_row_main_bound: assumes Linv: "LLL_bound_invariant False True i fs"
  and i: "i < m"  and j: "j < i" 
  and c: "c = round (\<mu> fs i j)" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
  and mu_small: "\<mu>_small_row i fs (Suc j)" 
  and mu_bnd: "\<mu>_bound_row_inner fs i (Suc j)" 
shows "LLL_bound_invariant False True i fs'"
  "\<mu>_bound_row_inner fs' i j"
proof (rule bound_invI)
  from bound_invD[OF Linv]
  have Linv: "LLL_invariant True i fs" and fbnd: "f_bound False i fs" and gbnd: "g_bound fs"
    by auto
  note main = basis_reduction_add_row_main[OF Linv i j fs']
  note main = main(1) main(2)[OF c mu_small] main(3-)
  show Linv': "LLL_invariant True i fs'" by fact
  define bnd :: rat where bnd: "bnd = 4 ^ (m - 1 - Suc j) * of_nat (N ^ (m - 1) * m)" 
  note mu_bnd = mu_bnd[folded bnd]
  note inv = LLL_invD[OF Linv]
  let ?mu = "\<mu> fs"
  let ?mu' = "\<mu> fs'"
  from j have "j \<le> i" by simp
  let ?R = rat_of_int

  (* (squared) mu bound will increase at most by factor 4 *)
  have mu_bound_factor: "\<mu>_bound_row fs' (4 * bnd) i" 
  proof (intro \<mu>_bound_rowI)
    fix k
    assume ki: "k \<le> i" 
    from \<mu>_bound_rowD[OF mu_bnd] have bnd_i: "\<And> j. j \<le> i \<Longrightarrow> (?mu i j)^2 \<le> bnd" by auto
    have bnd_ik: "(?mu i k)\<^sup>2 \<le> bnd" using bnd_i[OF ki] by auto
    have bnd_ij: "(?mu i j)\<^sup>2 \<le> bnd" using bnd_i[OF \<open>j \<le> i\<close>] by auto
    from \<mu>_bound_row_1[OF mu_bnd] have bnd1: "bnd \<ge> 1" "bnd \<ge> 0" by auto
    show "(?mu' i k)\<^sup>2 \<le> 4 * bnd"
    proof (cases "k > j")
      case True
      show ?thesis
        by (subst main(5), (insert True ki i bnd1, auto)[3], intro order.trans[OF bnd_ik], auto)
    next
      case False
      hence kj: "k \<le> j" by auto
      show ?thesis
      proof (cases "k = j")
        case True 
        have small: "abs (?mu' i k) \<le> 1/2" using main(2) j unfolding True \<mu>_small_row_def by auto
        show ?thesis using mult_mono[OF small small] using bnd1 
          by (auto simp: power2_eq_square)
      next
        case False
        with kj have k_j: "k < j" by auto
        define M where "M = max (abs (?mu i k)) (max (abs (?mu i j)) (1/2))" 
        have M0: "M \<ge> 0" unfolding M_def by auto
        let ?new_mu = "?mu i k - ?R c * ?mu j k" 
        have "abs ?new_mu \<le> abs (?mu i k) + abs (?R c * ?mu j k)" by simp
        also have "\<dots> = abs (?mu i k) + abs (?R c) * abs (?mu j k)" unfolding abs_mult ..
        also have "\<dots> \<le> abs (?mu i k) + (abs (?mu i j) + 1/2) * (1/2)" 
        proof (rule add_left_mono[OF mult_mono], unfold c)
          show "\<bar>?R (round (?mu i j))\<bar> \<le> \<bar>?mu i j\<bar> + 1 / 2" unfolding round_def by linarith
          from inv(10)[unfolded gram_schmidt_fs.reduced_def, THEN conjunct2, rule_format, OF \<open>j < i\<close> k_j]
          show "\<bar>?mu j k\<bar> \<le> 1/2" .
        qed auto
        also have "\<dots> \<le> M + (M + M) * (1/2)" 
          by (rule add_mono[OF _ mult_right_mono[OF add_mono]], auto simp: M_def)
        also have "\<dots> = 2 * M" by auto
        finally have le: "abs ?new_mu \<le> 2 * M" .
        have "(?mu' i k)\<^sup>2 = ?new_mu\<^sup>2" 
          by (subst main(5), insert kj False i j, auto)
        also have "\<dots> \<le> (2 * M)^2" unfolding abs_le_square_iff[symmetric] using le M0 by auto
        also have "\<dots> = 4 * M^2" by simp
        also have "\<dots> \<le> 4 * bnd" 
        proof (rule mult_left_mono)            
          show "M^2 \<le> bnd" using bnd_ij bnd_ik bnd1 unfolding M_def
            by (auto simp: max_def power2_eq_square)
        qed auto
        finally show ?thesis .
      qed
    qed
  qed
  also have "4 * bnd = (4 ^ (1 + (m - 1 - Suc j)) * of_nat (N ^ (m - 1) * m))" unfolding bnd 
    by simp
  also have "1 + (m - 1 - Suc j) = m - 1 - j" using i j by auto
  finally show bnd: "\<mu>_bound_row_inner fs' i j" by auto

  show gbnd: "g_bound fs'" using gbnd unfolding g_bound_def
    using main(4) by auto

  note inv' = LLL_invD[OF Linv']
  show "f_bound False i fs'"
    unfolding f_bound_def
  proof (intro allI impI, goal_cases)
    case (1 jj)
    show ?case
    proof (cases "jj = i")
      case False
      with 1 fbnd[unfolded f_bound_def] have "\<parallel>fs ! jj\<parallel>\<^sup>2 \<le> int (N * m)" by auto
      thus ?thesis unfolding fs' using False 1 inv(2-) by auto
    next
      case True        
      have "of_int \<parallel>fs' ! i\<parallel>\<^sup>2 = \<parallel>RAT fs' ! i\<parallel>\<^sup>2" using i inv' by (auto simp: sq_norm_of_int)
      also have "... \<le> rat_of_nat (Suc i * N) * (4 ^ (m - 1 - j) * rat_of_nat (N ^ (m - 1) * m))" 
        using sq_norm_fs_mu_g_bound[OF inv'(1,6) i bnd gbnd] i inv'
        unfolding sq_norm_of_int[symmetric]
        by (auto simp: ac_simps)
      also have "\<dots> = rat_of_int ( int (Suc i * N) * (4 ^ (m - 1 - j) * (N ^ (m - 1) * m)))"
        by simp
      finally have "\<parallel>fs' ! i\<parallel>\<^sup>2 \<le> int (Suc i * N) * (4 ^ (m - 1 - j) * (N ^ (m - 1) * m))" by linarith
      also have "\<dots> = int (Suc i) * 4 ^ (m - 1 - j) * (int N ^ (Suc (m - 1))) * int m" 
        unfolding of_nat_mult by (simp add: ac_simps)
      also have "\<dots> = int (Suc i) * 4 ^ (m - 1 - j) * int N ^ m * int m" using i j by simp
      also have "\<dots> \<le> int m * 4 ^ (m - 1) * int N ^ m * int m" 
        by (rule mult_right_mono[OF mult_right_mono[OF mult_mono[OF _ pow_mono_exp]]], insert i, auto)
      finally have "\<parallel>fs' ! i\<parallel>\<^sup>2 \<le> int (4 ^ (m - 1) * N ^ m * m * m)" unfolding of_nat_mult by (simp add: ac_simps)
      thus ?thesis unfolding True by auto
    qed
  qed
qed
end

context LLL_with_assms
begin

subsubsection \<open>@{const LLL_bound_invariant} is maintained during execution of @{const reduce_basis}\<close>

lemma basis_reduction_add_rows_enter_bound: assumes binv: "LLL_bound_invariant True True i fs"
  and i: "i < m"   
shows "LLL_bound_invariant False True i fs"
  "\<mu>_bound_row_inner fs i i" 
proof (rule bound_invI)
  from bound_invD[OF binv]
  have Linv: "LLL_invariant True i fs" (is ?g1) and fbnd: "f_bound True i fs" 
    and gbnd: "g_bound fs" by auto
  interpret fs: fs_int' n m fs_init \<alpha> True i fs
    by standard (use Linv in auto)
  note inv = LLL_invD[OF Linv]
  show "LLL_invariant True i fs" by fact
  show fbndF: "f_bound False i fs" using f_bound_True_arbitrary[OF fbnd] .
  have N0: "N > 0" using LLL_inv_N_pos[OF Linv gbnd] i by auto
  {
    fix j
    assume ji: "j < i" 
    have "(\<mu> fs i j)\<^sup>2 \<le> gs.Gramian_determinant (RAT fs) j * \<parallel>RAT fs ! i\<parallel>\<^sup>2"
      using ji i inv by (intro fs.gs.mu_bound_Gramian_determinant) (auto)
    also have "gs.Gramian_determinant (RAT fs) j = of_int (d fs j)" unfolding d_def 
      by (subst fs.of_int_Gramian_determinant, insert ji i inv(2-), auto simp: set_conv_nth)
    also have "\<parallel>RAT fs ! i\<parallel>\<^sup>2 = of_int \<parallel>fs ! i\<parallel>\<^sup>2" using i inv(2-) by (auto simp: sq_norm_of_int)
    also have "of_int (d fs j) * \<dots> \<le> rat_of_nat (N^j) * of_int \<parallel>fs ! i\<parallel>\<^sup>2"
      by (rule mult_right_mono, insert ji i d_approx[OF Linv gbnd, of j], auto)
    also have "\<dots> \<le> rat_of_nat (N^(m-2)) * of_int (int (N * m))" 
      by (intro mult_mono, unfold of_nat_le_iff of_int_le_iff, rule pow_mono_exp,
      insert fbnd[unfolded f_bound_def, rule_format, of i] N0 ji i, auto)
    also have "\<dots> = rat_of_nat (N^(m-2) * N * m)" by simp
    also have "N^(m-2) * N = N^(Suc (m - 2))" by simp
    also have "Suc (m - 2) = m - 1" using ji i by auto
    finally have "(\<mu> fs i j)\<^sup>2 \<le> of_nat (N ^ (m - 1) * m)" .
  } note mu_bound = this
  show mu_bnd: "\<mu>_bound_row_inner fs i i"
  proof (rule \<mu>_bound_rowI)
    fix j
    assume j: "j \<le> i" 
    have "(\<mu> fs i j)\<^sup>2 \<le> 1 * of_nat (N ^ (m - 1) * m)" 
    proof (cases "j = i")
      case False
      with mu_bound[of j] j show ?thesis by auto
    next
      case True
      show ?thesis unfolding True fs.gs.\<mu>.simps using i N0 by auto
    qed
    also have "\<dots> \<le> 4 ^ (m - 1 - i) * of_nat (N ^ (m - 1) * m)" 
      by (rule mult_right_mono, auto)
    finally show "(\<mu> fs i j)\<^sup>2 \<le> 4 ^ (m - 1 - i) * rat_of_nat (N ^ (m - 1) * m)" . 
  qed
  show "g_bound fs" by fact 
qed

lemma basis_basis_reduction_add_rows_loop_leave:
  assumes binv: "LLL_bound_invariant False True i fs" 
  and mu_small: "\<mu>_small_row i fs 0"
  and mu_bnd: "\<mu>_bound_row_inner fs i 0" 
  and i: "i < m" 
shows "LLL_bound_invariant True False i fs" 
proof -
  note Linv = bound_invD(1)[OF binv]
  from mu_small have mu_small: "\<mu>_small fs i" unfolding \<mu>_small_row_def \<mu>_small_def by auto
  note inv = LLL_invD[OF Linv]
  interpret gs1: gram_schmidt_fs_int n "RAT fs"
    by (standard) (use inv gs.lin_indpt_list_def in \<open>auto simp add: vec_hom_Ints\<close>)
  note fbnd = bound_invD(2)[OF binv]
  note gbnd = bound_invD(3)[OF binv]
  {
    fix ii
    assume ii: "ii < m" 
    have "\<parallel>fs ! ii\<parallel>\<^sup>2 \<le> int (N * m)" 
    proof (cases "ii = i")
      case False
      thus ?thesis using ii fbnd[unfolded f_bound_def] by auto
    next
      case True
      have row: "\<mu>_bound_row fs 1 i" 
      proof (intro \<mu>_bound_rowI)
        fix j
        assume j: "j \<le> i" 
        from mu_small[unfolded \<mu>_small_def, rule_format, of j]
        have "abs (\<mu> fs i j) \<le> 1" using j unfolding \<mu>_small_def by (cases "j = i", force simp: gs1.\<mu>.simps, auto)
        from mult_mono[OF this this] show "(\<mu> fs i j)\<^sup>2 \<le> 1" by (auto simp: power2_eq_square)
      qed
      have "rat_of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> rat_of_int (int (Suc i * N))" 
        using sq_norm_fs_mu_g_bound[OF inv(1,6) i row gbnd] by auto
      hence "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> int (Suc i * N)" by linarith
      also have "\<dots> = int N * int (Suc i)" unfolding of_nat_mult by simp
      also have "\<dots> \<le> int N * int m" 
        by (rule mult_left_mono, insert i, auto)
      also have "\<dots> = int (N * m)" by simp
      finally show ?thesis unfolding True .
    qed
  }
  hence f_bound: "f_bound True i fs" unfolding f_bound_def by auto
  with binv show ?thesis using basis_reduction_add_row_done[OF Linv i assms(2)] 
    by (auto simp: LLL_bound_invariant_def)
qed


lemma basis_reduction_add_rows_loop_bound: assumes
  binv: "LLL_bound_invariant False True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and mu_bnd: "\<mu>_bound_row_inner fs i j" 
  and res: "basis_reduction_add_rows_loop i fs j = fs'" 
  and i: "i < m" 
  and j: "j \<le> i" 
shows "LLL_bound_invariant True False i fs'" 
  using assms
proof (induct j arbitrary: fs)
  case (0 fs)
  note binv = 0(1)
  from basis_basis_reduction_add_rows_loop_leave[OF 0(1-3) i] 0(4)
  show ?case by auto
next
  case (Suc j fs)
  note binv = Suc(2)
  note Linv = bound_invD(1)[OF binv]
  from Suc have j: "j < i" by auto
  let ?c = "round (\<mu> fs i j)" 
  note step = basis_reduction_add_row_main_bound[OF Suc(2) i j refl refl Suc(3-4)]
  note step' = basis_reduction_add_row_main(1,2,3)[OF Linv i j refl]
  show ?case
  proof (cases "?c = 0")
    case True
    note inv = LLL_invD[OF Linv]
    from inv(5)[OF i] inv(5)[of j] i j
    have id: "fs[i := fs ! i - 0 \<cdot>\<^sub>v fs ! j] = fs" 
      by (intro nth_equalityI, insert inv i, auto)
    show ?thesis 
      by (rule Suc(1), insert step step' id True Suc(2-), auto)
  next
    case False
    show ?thesis using Suc(1)[OF step(1) step'(2) step(2)] Suc(2-) False step'(3) by auto
  qed
qed

lemma basis_reduction_add_rows_bound: assumes 
  binv: "LLL_bound_invariant True upw i fs" 
  and res: "basis_reduction_add_rows upw i fs = fs'" 
  and i: "i < m" 
shows "LLL_bound_invariant True False i fs'"  
proof -
  note def = basis_reduction_add_rows_def
  show ?thesis
  proof (cases upw)
    case False
    with res binv show ?thesis by (simp add: def)
  next
    case True
    with binv have binv: "LLL_bound_invariant True True i fs" by auto
    note start = basis_reduction_add_rows_enter_bound[OF this i]
    from res[unfolded def] True 
    have "basis_reduction_add_rows_loop i fs i = fs'" by auto
    from basis_reduction_add_rows_loop_bound[OF start(1) \<mu>_small_row_refl start(2) this i le_refl]      
    show ?thesis by auto
  qed
qed


lemma basis_reduction_swap_bound: assumes 
  binv: "LLL_bound_invariant True False i fs" 
  and res: "basis_reduction_swap i fs = (upw',i',fs')" 
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and i: "i < m" "i \<noteq> 0" 
shows "LLL_bound_invariant True upw' i' fs'" 
proof (rule bound_invI)
  note Linv = bound_invD(1)[OF binv]
  from basis_reduction_swap[OF Linv res cond i]
  show Linv': "LLL_invariant upw' i' fs'" by auto
  from res[unfolded basis_reduction_swap_def]
  have id: "i' = i - 1" "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" by auto
  from LLL_invD(6)[OF Linv] i
  have choice: "fs' ! k = fs ! k \<or> fs' ! k = fs ! i \<or> fs' ! k = fs ! (i - 1)" for k 
    unfolding id by (cases "k = i"; cases "k = i - 1", auto) 
  from bound_invD(2)[OF binv] i 
  show "f_bound True i' fs'" unfolding id(1) f_bound_def
  proof (intro allI impI, goal_cases)
    case (1 k)
    thus ?case using choice[of k] by auto
  qed

  let ?g1 = "\<lambda> i. gso fs i"
  let ?g2 = "\<lambda> i. gso fs' i" 
  let ?n1 = "\<lambda> i. sq_norm (?g1 i)"
  let ?n2 = "\<lambda> i. sq_norm (?g2 i)" 
  from bound_invD(3)[OF binv, unfolded g_bound_def]
  have short: "\<And> k. k < m \<Longrightarrow> ?n1 k \<le> of_nat N" by auto
  from short[of "i - 1"] i 
  have short_im1: "?n1 (i - 1) \<le> of_nat N" by auto
  note swap = basis_reduction_swap_main[OF Linv i cond id(2)]
  note updates = swap(3,4)
  note Linv' = swap(1)
  note inv' = LLL_invD[OF Linv']
  note inv = LLL_invD[OF Linv]
  interpret gs1: gram_schmidt_fs_int n "RAT fs"
    by (standard) (use inv gs.lin_indpt_list_def in \<open>auto simp add: vec_hom_Ints\<close>)
  interpret gs2: gram_schmidt_fs_int n "RAT fs'"
    by (standard) (use inv' gs.lin_indpt_list_def in \<open>auto simp add: vec_hom_Ints\<close>)
  let ?mu1 = "\<mu> fs" 
  let ?mu2 = "\<mu> fs'" 
  let ?mu = "?mu1 i (i - 1)" 
  from LLL_invD[OF Linv] have "\<mu>_small fs i" by blast
  from this[unfolded \<mu>_small_def] i have mu: "abs ?mu \<le> 1/2" by auto
  have "?n2 (i - 1) = ?n1 i + ?mu * ?mu * ?n1 (i - 1)" 
   by (subst updates(2), insert i, auto)
  also have "\<dots> = inverse \<alpha> * (\<alpha> * ?n1 i) + (?mu * ?mu) * ?n1 (i - 1)" 
    using \<alpha> by auto
  also have "\<dots> \<le> inverse \<alpha> * ?n1 (i - 1) + (abs ?mu * abs ?mu) * ?n1 (i - 1)"
    by (rule add_mono[OF mult_left_mono], insert cond \<alpha>, auto)
  also have "\<dots> = (inverse \<alpha> + abs ?mu * abs ?mu) * ?n1 (i - 1)" by (auto simp: field_simps)
  also have "\<dots> \<le> (inverse \<alpha> + (1/2) * (1/2)) * ?n1 (i - 1)" 
    by (rule mult_right_mono[OF add_left_mono[OF mult_mono]], insert mu, auto)  
  also have "inverse \<alpha> + (1/2) * (1/2) = reduction" unfolding reduction_def using \<alpha>0 
    by (auto simp: field_simps)
  also have "\<dots> * ?n1 (i - 1) \<le> 1 * ?n1 (i - 1)" 
    by (rule mult_right_mono, auto simp: reduction)
  finally have n2im1: "?n2 (i - 1) \<le> ?n1 (i - 1)" by simp
  show "g_bound fs'" unfolding g_bound_def
  proof (intro allI impI)
    fix k 
    assume km: "k < m" 
    consider (ki) "k = i" | (im1) "k = i - 1" | (other) "k \<noteq> i" "k \<noteq> i-1" by blast
    thus "?n2 k \<le> of_nat N"
    proof cases
      case other
      from short[OF km] have "?n1 k \<le> of_nat N" by auto
      also have "?n1 k = ?n2 k" using km other
        by (subst updates(2), auto)
      finally show ?thesis by simp
    next
      case im1
      have "?n2 k = ?n2 (i - 1)" unfolding im1 ..
      also have "\<dots> \<le> ?n1 (i - 1)" by fact
      also have "\<dots> \<le> of_nat N" using short_im1 by auto
      finally show ?thesis by simp
    next
      case ki
      have "?n2 k = ?n2 i" unfolding ki using i by auto
      also have "\<dots> \<le> ?n1 (i - 1)" 
      proof -
        let ?f1 = "\<lambda> i. RAT fs ! i"
        let ?f2 = "\<lambda> i. RAT fs' ! i" 
        define u where "u = gs.sumlist (map (\<lambda>j. ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0..<i - 1])" 
        define U where "U = ?f1 ` {0 ..< i - 1} \<union> {?f1 i}" 
        have g2i: "?g2 i \<in> Rn" using i inv' by simp
        have U: "U \<subseteq> Rn" unfolding U_def using inv i by auto
        have uU: "u \<in> gs.span U"
        proof -
          have im1: "i - 1 \<le> m" using i by auto
          have G1: "?g1 ` {0..< i - 1} \<subseteq> Rn" using inv(5) i by auto
          have "u \<in> gs.span (?g1 ` {0 ..< i - 1})" unfolding u_def 
            by (rule gs.sumlist_in_span[OF G1], unfold set_map, insert G1,
              auto intro!: gs.smult_in_span intro: gs.span_mem)
          also have "gs.span (?g1 ` {0 ..< i - 1}) = gs.span (?f1 ` {0 ..< i - 1})" 
            apply(subst gs1.partial_span, insert im1 inv, unfold gs.lin_indpt_list_def)
             apply(blast)
            apply(rule arg_cong[of _ _ gs.span])
            apply(subst nth_image[symmetric])
            by (insert i inv, auto)
          also have "\<dots> \<subseteq> gs.span U" unfolding U_def 
            by (rule gs.span_is_monotone, auto)
          finally show ?thesis .
        qed
        from i have im1: "i - 1 < m" by auto
        have u: "u \<in> Rn" using uU U by simp
        have id_u: "u + (?g1 (i - 1) - ?g2 i) = u + ?g1 (i - 1) - ?g2 i" 
          using u g2i inv(5)[OF im1] by auto
        have list_id: "[0..<Suc (i - 1)] = [0..< i - 1] @ [i - 1]" 
          "map f [x] = [f x]" for f x by auto
        have "gs.is_oc_projection (gs2.gso i) (gs.span (gs2.gso ` {0..<i})) ((RAT fs') ! i)"
          using i inv' unfolding gs.lin_indpt_list_def
          by (intro gs2.gso_oc_projection_span(2)) (auto)
        then have "gs.is_oc_projection (?g2 i) (gs.span (gs2.gso ` {0 ..< i}))  (?f1 (i - 1))" 
          unfolding id(2) using inv(6) i by (auto)
        also have "?f1 (i - 1) = u + ?g1 (i - 1) " 
          apply(subst gs1.fi_is_sum_of_mu_gso, insert im1 inv, unfold gs.lin_indpt_list_def)
          apply(blast)
          unfolding list_id map_append u_def
          by (subst gs.M.sumlist_snoc, insert i, auto simp: gs1.\<mu>.simps intro!: inv(5))
        also have "gs.span (gs2.gso ` {0 ..< i}) = gs.span (set (take i (RAT fs')))" 
          using inv' \<open>i \<le> m\<close> unfolding gs.lin_indpt_list_def
          by (subst gs2.partial_span) auto
        also have "set (take i (RAT fs')) = ?f2 ` {0 ..< i}" using inv'(6) i 
          by (subst nth_image[symmetric], auto)
        also have "{0 ..< i} = {0 ..< i - 1} \<union> {(i - 1)}" using i by auto
        also have "?f2 ` \<dots> = ?f2 ` {0 ..< i - 1} \<union> {?f2 (i - 1)}" by auto
        also have "\<dots> = U" unfolding U_def id(2) 
          by (rule arg_cong2[of _ _ _ _ "(\<union>)"], insert i inv(6), force+)
        finally have "gs.is_oc_projection (?g2 i) (gs.span U) (u + ?g1 (i - 1))" .        
        hence proj: "gs.is_oc_projection (?g2 i) (gs.span U) (?g1 (i - 1))"
          unfolding gs.is_oc_projection_def using gs.span_add[OF U uU, of "?g1 (i - 1) - ?g2 i"] 
          inv(5)[OF im1] g2i u id_u by (auto simp: U)
        from gs.is_oc_projection_sq_norm[OF this gs.span_is_subset2[OF U]  inv(5)[OF im1]]
        show "?n2 i \<le> ?n1 (i - 1)" .
      qed
      also have "\<dots> \<le> of_nat N" by fact
      finally show ?thesis .
    qed
  qed
qed

lemma basis_reduction_step_bound: assumes 
  binv: "LLL_bound_invariant True upw i fs" 
  and res: "basis_reduction_step upw i fs = (upw',i',fs')" 
  and i: "i < m" 
shows "LLL_bound_invariant True upw' i' fs'" 
proof -
  note def = basis_reduction_step_def
  obtain fs'' where fs'': "basis_reduction_add_rows upw i fs = fs''" by auto
  show ?thesis
  proof (cases "i = 0")
    case True
    from increase_i_bound[OF binv i True] res True
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    note res = res[unfolded def id if_False fs'' Let_def]
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    from basis_reduction_add_rows_bound[OF binv fs'' i]
    have binv: "LLL_bound_invariant True False i fs''" by auto
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i_bound[OF binv i _ True] True res
      show ?thesis by auto
    next
      case gt: False
      hence "?x > ?y" by auto
      from basis_reduction_swap_bound[OF binv _ this i False] gt res
      show ?thesis by auto
    qed
  qed
qed

lemma basis_reduction_main_bound: assumes "LLL_bound_invariant True upw i fs" 
  and res: "basis_reduction_main (upw,i,fs) = fs'" 
shows "LLL_bound_invariant True True m fs'" 
  using assms
proof (induct "LLL_measure i fs" arbitrary: i fs upw rule: less_induct)
  case (less i fs upw)
  have id: "LLL_bound_invariant True upw i fs = True" using less by auto
  note res = less(3)[unfolded basis_reduction_main.simps[of upw i fs] id]
  note inv = less(2)
  note IH = less(1)
  note Linv = bound_invD(1)[OF inv]
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i' fs' upw' where step: "basis_reduction_step upw i fs = (upw',i',fs')" 
      (is "?step = _") by (cases ?step, auto)
    note decrease = basis_reduction_step(2)[OF Linv step i]
    from IH[OF decrease basis_reduction_step_bound(1)[OF inv step i]] res[unfolded step] i Linv
    show ?thesis by auto
  next
    case False
    with LLL_invD[OF Linv] have i: "i = m" by auto
    with False res inv have "LLL_bound_invariant True upw m fs'" by auto
    thus ?thesis by (auto simp: LLL_invariant_def LLL_bound_invariant_def)
  qed
qed

lemma LLL_inv_initial_state_bound: "LLL_bound_invariant True True 0 fs_init" 
proof (intro bound_invI[OF LLL_inv_initial_state _ g_bound_fs_init])
  {
    fix i
    assume i: "i < m" 
    let ?N = "map (nat o sq_norm) fs_init"
    let ?r = rat_of_int
    from i have mem: "nat (sq_norm (fs_init ! i)) \<in> set ?N" using fs_init len unfolding set_conv_nth by force
    from mem_set_imp_le_max_list[OF _ mem]
    have FN: "nat (sq_norm (fs_init ! i)) \<le> N" unfolding N_def by force
    hence "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int N" using i by auto
    also have "\<dots> \<le> int (N * m)" using i by fastforce
    finally have f_bnd:  "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int (N * m)" .
  }
  thus "f_bound True 0 fs_init" unfolding f_bound_def by auto
qed

lemma reduce_basis_bound: assumes res: "reduce_basis = fs" 
  shows "LLL_bound_invariant True True m fs" 
  using basis_reduction_main_bound[OF LLL_inv_initial_state_bound res[unfolded reduce_basis_def]] .


subsubsection \<open>Bound extracted from @{term LLL_bound_invariant}.\<close>

fun f_bnd :: "bool \<Rightarrow> nat" where
  "f_bnd False = 2 ^ (m - 1) * N ^ m * m" 
| "f_bnd True = N * m" 

lemma f_bnd_mono: "f_bnd outside \<le> f_bnd False" 
proof (cases outside)
  case out: True
  show ?thesis
  proof (cases "N = 0 \<or> m = 0")
    case True
    thus ?thesis using out by auto
  next
    case False
    hence 0: "N > 0" "m > 0" by auto
    let ?num = "(2 ^ (m - 1) * N ^ m)" 
    have "(N * m) * 1 \<le> (N * m) * (2 ^ (m - 1) * N ^ (m - 1))" 
      by (rule mult_left_mono, insert 0, auto)
    also have "\<dots> = 2 ^ (m - 1) * N ^ (Suc (m - 1)) * m " by simp
    also have "Suc (m - 1) = m" using 0 by simp
    finally show ?thesis using out by auto
  qed
qed auto 

lemma aux_bnd_mono: "N * m \<le> (4 ^ (m - 1) * N ^ m * m * m)" 
proof (cases "N = 0 \<or> m = 0")
  case False
  hence 0: "N > 0" "m > 0" by auto
  let ?num = "(4 ^ (m - 1) * N ^ m * m * m)" 
  have "(N * m) * 1 \<le> (N * m) * (4 ^ (m - 1) * N ^ (m - 1) * m)" 
    by (rule mult_left_mono, insert 0, auto)
  also have "\<dots> = 4 ^ (m - 1) * N ^ (Suc (m - 1)) * m * m" by simp
  also have "Suc (m - 1) = m" using 0 by simp
  finally show "N * m \<le> ?num" by simp
qed auto

context fixes outside upw k fs
  assumes binv: "LLL_bound_invariant outside upw k fs"
begin

lemma LLL_f_bnd: 
  assumes i: "i < m" and j: "j < n" 
shows "\<bar>fs ! i $ j\<bar> \<le> f_bnd outside" 
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs" 
    and fbnd: "f_bound outside k fs" 
    and gbnd: "g_bound fs" by auto
  from LLL_inv_N_pos[OF inv gbnd] i have N0: "N > 0" by auto
  note inv = LLL_invD[OF inv] 
  from inv i have fsi: "fs ! i \<in> carrier_vec n" by auto
  have one: "\<bar>fs ! i $ j\<bar>^1 \<le> \<bar>fs ! i $ j\<bar>^2" 
    by (cases "fs ! i $ j \<noteq> 0", intro pow_mono_exp, auto)
  let ?num = "(4 ^ (m - 1) * N ^ m * m * m)" 
  let ?sq_bnd = "if i \<noteq> k \<or> outside then int (N * m) else int ?num" 
  have "\<bar>fs ! i $ j\<bar>^2 \<le> \<parallel>fs ! i\<parallel>\<^sup>2" using fsi j by (metis vec_le_sq_norm)
  also have "\<dots> \<le> ?sq_bnd" 
    using fbnd[unfolded f_bound_def, rule_format, OF i] by auto
  finally have two: "(fs ! i $ j)^2 \<le> ?sq_bnd" by simp
  show ?thesis
  proof (cases outside)
    case True
    with one two show ?thesis by auto
  next
    case False
    let ?num2 = "(2 ^ (m - 1) * N ^ m * m)" 
    have four: "(4 :: nat) = 2^2" by auto
    have "(fs ! i $ j)^2 \<le> int (max (N * m) ?num)" 
      by (rule order.trans[OF two], auto simp: of_nat_mult[symmetric] simp del: of_nat_mult)
    also have "max (N * m) ?num = ?num" using aux_bnd_mono by presburger 
    also have "int ?num = int ?num * 1" by simp
    also have "\<dots> \<le> int ?num * N ^ m" 
      by (rule mult_left_mono, insert N0, auto)
    also have "\<dots> = int (?num * N ^ m)" by simp
    also have "?num * N ^ m = ?num2^2" unfolding power2_eq_square four power_mult_distrib
      by simp
    also have "int \<dots> = (int ?num2)^2" by simp
    finally have "(fs ! i $ j)\<^sup>2 \<le> (int (f_bnd outside))\<^sup>2" using False by simp
    thus ?thesis unfolding abs_le_square_iff[symmetric] by simp 
  qed
qed

lemma LLL_gso_bound:
  assumes i: "i < m" and j: "j < n" 
  and quot: "quotient_of (gso fs i $ j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> N ^ m" 
  and "\<bar>denom\<bar> \<le> N ^ m"
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs" 
    and gbnd: "g_bound fs" by auto
  note * = LLL_invD[OF inv]
  interpret fs: fs_int' n m fs_init \<alpha> upw k fs
    by standard (use inv in auto)
  note d_approx[OF inv gbnd i, unfolded d_def]  
  let ?r = "rat_of_int"
  have int: "(gs.Gramian_determinant (RAT fs) i \<cdot>\<^sub>v (gso fs i)) $ j \<in> \<int>"
  proof -
    have "of_int_hom.vec_hom (fs ! j) $ i \<in> \<int>" if "i < n" "j < m" for i j
      using that assms * by (intro vec_hom_Ints) (auto)
    then show ?thesis
      using * gs.gso_connect snd_gram_schmidt_int assms unfolding gs.lin_indpt_list_def
      by (intro fs.gs.d_gso_Ints) (auto)
  qed
  have gsi: "gso fs i \<in> Rn" using *(5)[OF i] .
  have gs_sq: "\<bar>(gso fs i $ j)\<bar>\<^sup>2 \<le> rat_of_nat N"
    by(rule order_trans, rule vec_le_sq_norm[of _ n])
      (use gsi assms gbnd * LLL.g_bound_def in auto)
  from i have "m * m \<noteq> 0"
    by auto
  then have N0: "N \<noteq> 0"
    using less_le_trans[OF LLL_D_pos[OF inv] D_approx[OF inv gbnd]] by auto
  have "\<bar>(gso fs i $ j)\<bar> \<le> max 1 \<bar>(gso fs i $ j)\<bar>"
    by simp
  also have "\<dots> \<le> (max 1 \<bar>gso fs i $ j\<bar>)\<^sup>2"
    by (rule self_le_power, auto) 
  also have "\<dots> \<le> of_nat N"
    using gs_sq N0 unfolding max_def by auto
  finally have gs_bound: "\<bar>(gso fs i $ j)\<bar> \<le> of_nat N" .
  have "gs.Gramian_determinant (RAT fs) i = rat_of_int (gs.Gramian_determinant fs i)"
    using  assms *(4-6) carrier_vecD nth_mem by (intro fs.of_int_Gramian_determinant) (simp, blast)
  with int have "(of_int (d fs i) \<cdot>\<^sub>v gso fs i) $ j \<in> \<int>"
    unfolding d_def by simp
  also have "(of_int (d fs i) \<cdot>\<^sub>v gso fs i) $ j = of_int (d fs i) * (gso fs i $ j)"
    using gsi i j by auto
  finally have l: "of_int (d fs i) * gso fs i $ j \<in> \<int>"
    by auto
  have num: "rat_of_int \<bar>num\<bar> \<le> of_int (d fs i * int N)" and denom: "denom \<le> d fs i"
    using quotient_of_bounds[OF quot l LLL_d_pos[OF inv] gs_bound] i by auto
  from num have num: "\<bar>num\<bar> \<le> d fs i * int N"
    by linarith
  from d_approx[OF inv gbnd i] have d: "d fs i \<le> int (N ^ i)"
    by linarith
  from denom d have denom: "denom \<le> int (N ^ i)"
    by auto
  note num also have "d fs i * int N \<le> int (N ^ i) * int N" 
    by (rule mult_right_mono[OF d], auto)
  also have "\<dots> = int (N ^ (Suc i))"
    by simp
  finally have num: "\<bar>num\<bar> \<le> int (N ^ (i + 1))"
    by auto
  {
    fix jj
    assume "jj \<le> i + 1" 
    with i have "jj \<le> m" by auto
    from pow_mono_exp[OF _ this, of N] N0
    have "N^jj \<le> N^m" by auto
    hence "int (N^jj) \<le> int (N^m)" by linarith
  } note j_m = this
  have "\<bar>denom\<bar> = denom"
    using quotient_of_denom_pos[OF quot] by auto
  also have "\<dots> \<le> int (N ^ i)"
    by fact 
  also have "\<dots> \<le> int (N ^ m)"
    by (rule j_m, auto)
  finally show "\<bar>denom\<bar> \<le> int (N ^ m)"
    by auto
  show "\<bar>num\<bar> \<le> int (N ^ m)"
    using j_m[of "i+1"] num by auto
qed

lemma LLL_f_bound:
  assumes i: "i < m" and j: "j < n" 
shows "\<bar>fs ! i $ j\<bar> \<le> N ^ m * 2 ^ (m - 1) * m" 
proof -
  have "\<bar>fs ! i $ j\<bar> \<le> int (f_bnd outside)" using LLL_f_bnd[OF i j] by auto
  also have "\<dots> \<le> int (f_bnd False)" using f_bnd_mono[of outside] by presburger
  also have "\<dots> = int (N ^ m * 2 ^ (m - 1) * m)" by simp
  finally show ?thesis .
qed

lemma LLL_d_bound: 
  assumes i: "i \<le> m"   
shows "abs (d fs i) \<le> N ^ i \<and> abs (d fs i) \<le> N ^ m" 
proof (cases "m = 0")
  case True
  with i have id: "m = 0" "i = 0" by auto
  show ?thesis unfolding id(2) using id unfolding gs.Gramian_determinant_0 d_def by auto
next
  case m: False  
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and gbnd: "g_bound fs" by auto
  from LLL_inv_N_pos[OF inv gbnd] m have N: "N > 0" by auto 
  let ?r = rat_of_int 
  from d_approx_main[OF inv gbnd i m] 
  have "rat_of_int (d fs i) \<le> of_nat (N ^ i)" 
    by auto
  hence one: "d fs i \<le> N ^ i" by linarith
  also have "\<dots> \<le> N ^ m" unfolding of_nat_le_iff
    by (rule pow_mono_exp, insert N i, auto)
  finally have "d fs i \<le> N ^ m" by simp
  with LLL_d_pos[OF inv i] one
  show ?thesis by auto
qed

lemma LLL_mu_abs_bound: 
  assumes i: "i < m"
  and j: "j < i" 
shows "\<bar>\<mu> fs i j\<bar> \<le> rat_of_nat (N ^ (m - 1) * 2 ^ (m - 1) * m)" 
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs"
     and gbnd: "g_bound fs" by auto
  from LLL_inv_N_pos[OF inv gbnd] i have N: "N > 0" by auto 
  note * = LLL_invD[OF inv]
  interpret fs: fs_int' n m fs_init \<alpha> upw k fs
    by standard (use inv in auto)
  let ?mu = "\<mu> fs i j" 
  from j i have jm: "j < m" by auto
  from d_approx[OF inv gbnd jm]
  have dj: "d fs j \<le> int (N ^ j)" by linarith
  let ?num = "4 ^ (m - 1) * N ^ m * m * m" 
  let ?bnd = "N^(m - 1) * 2 ^ (m - 1) * m" 
  from fbnd[unfolded f_bound_def, rule_format, OF i]
    aux_bnd_mono[folded of_nat_le_iff[where ?'a = int]]
  have sq_f_bnd: "sq_norm (fs ! i) \<le> int ?num" by (auto split: if_splits)
  have four: "(4 :: nat) = 2^2" by auto
  have "?mu^2 \<le> (gs.Gramian_determinant (RAT fs) j) * sq_norm (RAT fs ! i)"
  proof -
    have 1: "of_int_hom.vec_hom (fs ! j) $ i \<in> \<int>" if "i < n" "j < length fs" for j i
      using * that by (metis vec_hom_Ints)
    then show ?thesis
      by (intro fs.gs.mu_bound_Gramian_determinant[OF j], insert * j i, 
          auto simp: set_conv_nth gs.lin_indpt_list_def)
  qed
  also have "sq_norm (RAT fs ! i) = of_int (sq_norm (fs ! i))" 
    unfolding sq_norm_of_int[symmetric] using *(6) i by auto
  also have "(gs.Gramian_determinant (RAT fs) j) = of_int (d fs j)" 
    unfolding d_def by (rule fs.of_int_Gramian_determinant, insert i j *(3,6), auto simp: set_conv_nth)
  also have "\<dots> * of_int (sq_norm (fs ! i)) = of_int (d fs j * sq_norm (fs ! i))" by simp 
  also have "\<dots> \<le> of_int (int (N^j) * int ?num)" unfolding of_int_le_iff 
    by (rule mult_mono[OF dj sq_f_bnd], auto)
  also have "\<dots> = of_nat (N^(j + m) * (4 ^ (m - 1) * m * m))" by (simp add: power_add)
  also have "\<dots> \<le> of_nat (N^( (m - 1) + (m-1)) * (4 ^ (m - 1) * m * m))" unfolding of_nat_le_iff
    by (rule mult_right_mono[OF pow_mono_exp], insert N j i jm, auto)
  also have "\<dots> = of_nat (?bnd^2)" 
    unfolding four power_mult_distrib power2_eq_square of_nat_mult by (simp add: power_add)
  finally have "?mu^2 \<le> (of_nat ?bnd)^2" by auto
  from this[folded abs_le_square_iff] 
  show "abs ?mu \<le> of_nat ?bnd" by auto
qed



lemma LLL_d\<mu>_bound: 
  assumes i: "i < m" and j: "j < i"  
shows "abs (d\<mu> fs i j) \<le> N ^ (2 * (m - 1)) * 2 ^ (m - 1) * m" 
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs"
     and gbnd: "g_bound fs" by auto
  interpret fs: fs_int' n m fs_init \<alpha> upw k fs
    by standard (use inv in auto)
  from LLL_inv_N_pos[OF inv gbnd] i have N: "N > 0" by auto 
  from j i have jm: "j < m - 1" "j < m" by auto
  let ?r = rat_of_int 
  from LLL_d_bound[of "Suc j"] jm
  have "abs (d fs (Suc j)) \<le> N ^ Suc j" by linarith
  also have "\<dots> \<le> N ^ (m - 1)" unfolding of_nat_le_iff
    by (rule pow_mono_exp, insert N jm, auto)
  finally have dsj: "abs (d fs (Suc j)) \<le> int N ^ (m - 1)" by auto
  from fs.d\<mu>[of j i] j i LLL_invD[OF inv]
  have "?r (abs (d\<mu> fs i j)) = abs (?r (d fs (Suc j)) * \<mu> fs i j)"
    unfolding d_def fs.d_def d\<mu>_def fs.d\<mu>_def by auto
  also have "\<dots> = ?r (abs (d fs (Suc j))) * abs (\<mu> fs i j)" by (simp add: abs_mult)
  also have "\<dots> \<le> ?r (int N ^ (m - 1)) * rat_of_nat (N ^ (m - 1) * 2 ^ (m - 1) * m)" 
    by (rule mult_mono[OF _ LLL_mu_abs_bound[OF i j]], insert dsj, linarith, auto)
  also have "\<dots> = ?r (int (N ^ ((m - 1) + (m - 1)) * 2 ^ (m - 1) * m))" 
    by (simp add: power_add)
  also have "(m - 1) + (m - 1) = 2 * (m - 1)" by simp
  finally show "abs (d\<mu> fs i j) \<le> N ^ (2 * (m - 1)) * 2 ^ (m - 1) * m" by linarith
qed

lemma LLL_mu_num_denom_bound: 
  assumes i: "i < m"                 
  and quot: "quotient_of (\<mu> fs i j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> N ^ (2 * m) * 2 ^ m * m" 
  and "\<bar>denom\<bar> \<le> N ^ m" 
proof (atomize(full))
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs"
     and gbnd: "g_bound fs" by auto
  from LLL_inv_N_pos[OF inv gbnd] i have N: "N > 0" by auto 
  note * = LLL_invD[OF inv]
  interpret fs: fs_int' n m fs_init \<alpha> upw k fs
    by standard (use inv in auto)
  let ?mu = "\<mu> fs i j" 
  let ?bnd = "N^(m - 1) * 2 ^ (m - 1) * m" 
  show "\<bar>num\<bar> \<le> N ^ (2 * m) * 2 ^ m * m \<and> \<bar>denom\<bar> \<le> N ^ m" 
  proof (cases "j < i")
    case j: True
    with i have jm: "j < m" by auto
    from LLL_d_pos[OF inv, of "Suc j"] i j have dsj: "0 < d fs (Suc j)" by auto
    from quotient_of_square[OF quot] 
    have quot_sq: "quotient_of (?mu^2) = (num * num, denom * denom)" 
      unfolding power2_eq_square by auto
    from LLL_mu_abs_bound[OF assms(1) j]
    have mu_bound: "abs ?mu \<le> of_nat ?bnd" by auto
    have "gs.Gramian_determinant (RAT fs) (Suc j) * ?mu \<in> \<int>" 
      by (rule fs.gs.d_mu_Ints,
      insert j *(1,3-6) i, auto simp: set_conv_nth gs.lin_indpt_list_def vec_hom_Ints)
    also have "(gs.Gramian_determinant (RAT fs) (Suc j)) = of_int (d fs (Suc j))" 
      unfolding d_def by (rule fs.of_int_Gramian_determinant, insert i j *(3,6), auto simp: set_conv_nth)
    finally have ints: "of_int (d fs (Suc j)) * ?mu \<in> \<int>" .
    from LLL_d_bound[of "Suc j"] jm
    have d_j: "d fs (Suc j) \<le> N ^ m" by auto
    note quot_bounds = quotient_of_bounds[OF quot ints dsj mu_bound]
    have "abs denom \<le> denom" using quotient_of_denom_pos[OF quot] by auto
    also have "\<dots> \<le> d fs (Suc j)" by fact
    also have "\<dots> \<le> N ^ m" by fact
    finally have denom: "abs denom \<le> N ^ m" by auto
    from quot_bounds(1) have "\<bar>num\<bar> \<le> d fs (Suc j) * int ?bnd" 
      unfolding of_int_le_iff[symmetric, where ?'a = rat] by simp
    also have "\<dots> \<le> N ^ m * int ?bnd" by (rule mult_right_mono[OF d_j], auto)
    also have "\<dots> = (int N ^ (m + (m - 1))) * (2 ^ (m - 1)) * int m" unfolding power_add of_nat_mult by simp
    also have "\<dots> \<le> (int N ^ (2 * m)) * (2 ^ m) * int m" unfolding of_nat_mult
      by (intro mult_mono pow_mono_exp, insert N, auto)
    also have "\<dots> = int (N ^ (2 * m) * 2 ^ m * m)" by simp
    finally have num: "\<bar>num\<bar> \<le> N ^ (2 * m) * 2 ^ m * m" .
    from denom num show ?thesis by blast
  next
    case False
    hence "?mu = 0 \<or> ?mu = 1" unfolding fs.gs.\<mu>.simps by auto
    hence "quotient_of ?mu = (1,1) \<or> quotient_of ?mu = (0,1)" by auto
    from this[unfolded quot] show ?thesis using N i by (auto intro!: mult_ge_one)
  qed
qed

text \<open>Now we have bounds on each number $(f_i)_j$, $(g_i)_j$, and $\mu_{i,j}$, i.e.,
  for rational numbers bounds on the numerators and denominators.\<close>

lemma logN_le_2log_Mn: assumes m: "m \<noteq> 0" "n \<noteq> 0" and N: "N > 0" 
  shows "log 2 N \<le> 2 * log 2 (M * n)" 
proof -
  have "N \<le> nat M * nat M * n * 1" using N_le_MMn m by auto
  also have "\<dots> \<le> nat M * nat M * n * n" by (intro mult_mono, insert m, auto)
  finally have NM: "N \<le> nat M * nat M * n * n" by simp
  with N have "nat M \<noteq> 0" by auto
  hence M: "M > 0" by simp

  have "log 2 N \<le> log 2 (M * M * n * n)" 
  proof (subst log_le_cancel_iff)      
    show "real N \<le> (M * M * int n * int n)" using NM[folded of_nat_le_iff[where ?'a = real]] M
      by simp
  qed (insert N M m, auto)
  also have "\<dots> = log 2 (of_int (M * n) * of_int (M * n))" 
    unfolding of_int_mult by (simp  add: ac_simps)
  also have "\<dots> = 2 * log 2 (M * n)" 
    by (subst log_mult, insert m M, auto)
  finally show "log 2 N \<le> 2 * log 2 (M * n)" by auto
qed


text \<open>We now prove a combined size-bound for all of these numbers. The bounds clearly indicate
  that the size of the numbers grows at most polynomial, namely the sizes are roughly 
  bounded by ${\cal O}(m \cdot \log(M \cdot n))$ where $m$ is the number of vectors, $n$ is the dimension
  of the vectors, and $M$ is the maximum absolute value that occurs in the input to the LLL algorithm.\<close>

lemma combined_size_bound: fixes number :: int 
  assumes i: "i < m" and j: "j < n"
  and x: "x \<in> {of_int (fs ! i $ j), gso fs i $ j, \<mu> fs i j}" 
  and quot: "quotient_of x = (num, denom)" 
  and number: "number \<in> {num, denom}" 
  and number0: "number \<noteq> 0" 
shows "log 2 \<bar>number\<bar> \<le> 2 * m * log 2 N       + m + log 2 m" 
      "log 2 \<bar>number\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m"
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs" 
     and gbnd: "g_bound fs" 
    by auto
  from LLL_inv_N_pos[OF inv gbnd] i have N: "N > 0" by auto
  let ?bnd = "N ^ (2 * m) * 2 ^ m * m" 
  have "N ^ m * int 1 \<le> N ^ (2 * m) * (2^m * int m)" 
    by (rule mult_mono, unfold of_nat_le_iff, rule pow_mono_exp, insert N i, auto)
  hence le: "int (N ^ m) \<le> N ^ (2 * m) * 2^m * m" by auto
  from x consider (xfs) "x = of_int (fs ! i $ j)" | (xgs) "x = gso fs i $ j" | (xmu) "x = \<mu> fs i j" 
    by auto
  hence num_denom_bound: "\<bar>num\<bar> \<le> ?bnd \<and> \<bar>denom\<bar> \<le> N ^ m" 
  proof (cases)
    case xgs
    from LLL_gso_bound[OF i j quot[unfolded xgs]] le
    show ?thesis by auto
  next
    case xmu
    from LLL_mu_num_denom_bound[OF i, of j, OF quot[unfolded xmu]]
    show ?thesis by auto
  next
    case xfs
    have "\<bar>denom\<bar> = 1" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> N ^ m" using N by auto
    finally have denom: "\<bar>denom\<bar> \<le> N ^ m" .
    have "\<bar>num\<bar> = \<bar>fs ! i $ j\<bar>" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> int (N ^ m * 2 ^ (m - 1) * m)" using LLL_f_bound[OF i j] by auto
    also have "\<dots> \<le> ?bnd" unfolding of_nat_mult of_nat_power
      by (intro mult_mono pow_mono_exp, insert N, auto)
    finally show ?thesis using denom by auto
  qed
  from number consider (num) "number = num" | (denom) "number = denom" by auto
  hence number_bound: "\<bar>number\<bar> \<le> ?bnd" 
  proof (cases)
    case num
    with num_denom_bound show ?thesis by auto
  next
    case denom
    with num_denom_bound have "\<bar>number\<bar> \<le> N ^ m" by auto
    with le show ?thesis by auto
  qed
  from number_bound have bnd: "of_int \<bar>number\<bar> \<le> real ?bnd" by linarith
  have "log 2 \<bar>number\<bar> \<le> log 2 ?bnd" 
    by (subst log_le_cancel_iff, insert number0 bnd, auto)
  also have "\<dots> = log 2 (N^(2 * m) * 2^m) + log 2 m" 
    by (subst log_mult[symmetric], insert i N, auto)
  also have "\<dots> = log 2 (N^(2 * m)) + log 2 (2^m) + log 2 m" 
    by (subst log_mult[symmetric], insert i N, auto)
  also have "log 2 (N^(2 * m)) = log 2 (N powr (2 * m))" 
    by (rule arg_cong[of _ _ "log 2"], subst powr_realpow, insert N, auto) 
  also have "\<dots> = (2 * m) * log 2 N" 
    by (subst log_powr, insert N, auto)
  finally show boundN: "log 2 \<bar>number\<bar> \<le> 2 * m * log 2 N + m + log 2 m" by simp
  also have "\<dots> \<le> 2 * m * (2 * log 2 (M * n)) + m + log 2 m" 
    by (intro add_right_mono mult_mono logN_le_2log_Mn N, insert i j N, auto)
  finally show "log 2 \<bar>number\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m" by simp
qed

text \<open>And a combined size bound for an integer implementation which stores values 
  $f_i$, $d_{j+1}\mu_{ij}$ and $d_i$.\<close>

interpretation fs: fs_int_indpt n fs_init
  by (standard) (use lin_dep in auto)

lemma fs_gs_N_N': assumes "m \<noteq> 0"
  shows "fs.gs.N = of_nat N"
proof -
  have 0: "Max (sq_norm ` set fs_init)  \<in>  sq_norm ` set fs_init"
    using len assms by auto
  then have 1: " nat (Max (sq_norm ` set fs_init)) \<in> (nat \<circ> sq_norm) ` set fs_init"
    by (auto)
  have [simp]: "0 \<le> Max (sq_norm ` set fs_init)"
    using 0 by force
  have [simp]: "sq_norm ` of_int_hom.vec_hom ` set fs_init = rat_of_int ` sq_norm ` set fs_init"
    by (auto simp add: sq_norm_of_int image_iff)
  then have [simp]: "rat_of_int (Max (sq_norm ` set fs_init)) \<in> rat_of_int ` sq_norm ` set fs_init"
    using 0 by auto
  have "(Missing_Lemmas.max_list (map (nat \<circ> sq_norm) fs_init)) = Max ((nat \<circ> sq_norm) ` set fs_init)"
    using assms len by (subst max_list_Max) (auto)
  also have "\<dots> = nat (Max (sq_norm_vec ` set fs_init))"
    using assms 1 by (auto intro!: nat_mono Max_eqI)
  also have "int \<dots> = Max (sq_norm_vec ` set fs_init)"
    by (subst int_nat_eq) (auto)
  also have "rat_of_int \<dots> = Max (sq_norm ` set (map of_int_hom.vec_hom fs_init))"
    by (rule Max_eqI[symmetric]) (auto simp add: sq_norm_of_int)
  finally show ?thesis
  unfolding N_def fs.gs.N_def by (auto)
qed

lemma fs_gs_N_N: "m \<noteq> 0 \<Longrightarrow> real_of_rat fs.gs.N = real N"
  using fs_gs_N_N' by simp

lemma combined_size_bound_gso_integer:
  assumes "x \<in> 
    {fs.\<mu>' i j |i j. j \<le> i \<and> i < m} \<union> 
    {fs.\<sigma>s l i j |i j l. i < m \<and> j \<le> i \<and> l < j}"
  and m: "m \<noteq> 0" and "x \<noteq> 0" "n \<noteq> 0"
shows "log 2 \<bar>real_of_int x\<bar> \<le> (6 + 6 * m) * log 2 (M * n) + log 2 m + m"
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and gbnd: "g_bound fs" 
    by auto 
  from LLL_inv_N_pos[OF inv gbnd m] have N: "N > 0" by auto
  have "log 2 \<bar>real_of_int x\<bar> \<le> log 2 m + real (3 + 3 * m) * log 2 N"
    using assms len fs.combined_size_bound_integer_log by (auto simp add: fs_gs_N_N)
  also have "\<dots> \<le> log 2 m + (3 + 3 * m) * (2 * log 2 (M * n))"
    using logN_le_2log_Mn assms N by (intro add_left_mono, intro mult_left_mono) (auto)
  also have "\<dots> = log 2 m + (6 + 6 * m) * log 2 (M * n)"
    by (auto simp add: algebra_simps)
  finally show ?thesis
    by auto
qed

lemma combined_size_bound_integer':  
  assumes x: "x \<in> {fs ! i $ j | i j. i < m \<and> j < n} 
    \<union> {d\<mu> fs i j | i j. j < i \<and> i < m} 
    \<union> {d fs i | i. i \<le> m}" 
    (is "x \<in> ?fs \<union> ?d\<mu> \<union> ?d")
  and m: "m \<noteq> 0" and n: "n \<noteq> 0" 
shows "abs x \<le> N ^ (2 * m) * 2 ^ m * m"
  "x \<noteq> 0 \<Longrightarrow> log 2 \<bar>x\<bar> \<le> 2 * m * log 2 N       + m + log 2 m" (is "_ \<Longrightarrow> ?l1 \<le> ?b1")
  "x \<noteq> 0 \<Longrightarrow> log 2 \<bar>x\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m" (is "_ \<Longrightarrow> _ \<le> ?b2")
proof -
  let ?bnd = "int N ^ (2 * m) * 2 ^ m * int m" 
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs" 
     and gbnd: "g_bound fs" 
    by auto 
  from LLL_inv_N_pos[OF inv gbnd m] have N: "N > 0" by auto
  let ?r = real_of_int
  from x consider (fs) "x \<in> ?fs" | (d\<mu>) "x \<in> ?d\<mu>" | (d) "x \<in> ?d" by auto
  hence "abs x \<le> ?bnd" 
  proof cases
    case fs
    then obtain i j where i: "i < m" and j: "j < n" and x: "x = fs ! i $ j" by auto
    from LLL_f_bound[OF i j, folded x]
    have "\<bar>x\<bar> \<le> int N ^ m * 2 ^ (m - 1) * int m" by simp
    also have "\<dots> \<le> ?bnd" 
      by (intro mult_mono pow_mono_exp, insert N, auto)
    finally show ?thesis .
  next
    case d\<mu>
    then obtain i j where i: "i < m" and j: "j < i" and x: "x = d\<mu> fs i j" by auto
    from LLL_d\<mu>_bound[OF i j, folded x]
    have "\<bar>x\<bar> \<le> int N ^ (2 * (m - 1)) * 2 ^ (m - 1) * int m" by simp
    also have "\<dots> \<le> ?bnd" 
      by (intro mult_mono pow_mono_exp, insert N, auto)
    finally show ?thesis .
  next
    case d
    then obtain i where i: "i \<le> m" and x: "x = d fs i" by auto
    from LLL_d_bound[OF i, folded x]
    have "\<bar>x\<bar> \<le> int N ^ m * 2 ^ 0 * 1" by simp
    also have "\<dots> \<le> ?bnd" 
      by (intro mult_mono pow_mono_exp, insert N m, auto)
    finally show ?thesis .
  qed
  thus "abs x \<le> N ^ (2 * m) * 2 ^ m * m" by simp
  hence abs: "?r (abs x) \<le> ?r (N ^ (2 * m) * 2 ^ m * m)" by linarith
  assume "x \<noteq> 0" hence x: "abs x > 0" by auto
  from abs have "log 2 (abs x) \<le> log 2 (?r (N ^ (2 * m)) * 2 ^ m * ?r m)" 
    by (subst log_le_cancel_iff, insert x N m, auto)
  also have "\<dots> = log 2 (?r N ^ (2 * m)) + m + log 2 (?r m)" 
    using N m by (auto simp: log_mult)
  also have "log 2 (?r N ^ (2 * m)) = real (2 * m) * log 2 (?r N)" 
    by (subst log_nat_power, insert N, auto)
  finally show "?l1 \<le> ?b1" by simp
  also have "\<dots> \<le> 2 * m * (2 * log 2 (M * n)) + m + log 2 m" 
    by (intro add_right_mono mult_left_mono logN_le_2log_Mn, insert m n N, auto)
  finally show "?l1 \<le> ?b2" by simp  
qed

lemma combined_size_bound_integer:  
  assumes x: "x \<in> 
      {fs ! i $ j | i j. i < m \<and> j < n} 
    \<union> {d\<mu> fs i j | i j. j < i \<and> i < m} 
    \<union> {d fs i | i. i \<le> m}
    \<union> {fs.\<mu>' i j |i j. j \<le> i \<and> i < m}
    \<union> {fs.\<sigma>s l i j |i j l. i < m \<and> j \<le> i \<and> l < j}"
    (is "?x \<in> ?s1 \<union> ?s2 \<union> ?s3 \<union> ?g1 \<union> ?g2")
  and m: "m \<noteq> 0" and n: "n \<noteq> 0" and "x \<noteq> 0" and "0 < M"
shows "log 2 \<bar>x\<bar> \<le> (6 + 6 * m) * log 2 (M * n) + log 2 m + m"
proof -
  show ?thesis
  proof (cases "?x \<in> ?g1 \<union> ?g2")
    case True
    then show ?thesis
      using combined_size_bound_gso_integer assms by simp
  next
    case False
    then have x: "x \<in> ?s1 \<union> ?s2 \<union> ?s3" using x by auto
    from combined_size_bound_integer'(3)[OF this m n \<open>x \<noteq> 0\<close>]
    have "log 2 \<bar>x\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m" by simp
    also have "\<dots> \<le> (6 + 6 * m) * log 2 (M * n) + m + log 2 m"
       using assms by (intro add_right_mono, intro mult_right_mono) auto
    finally show ?thesis
      by simp
  qed
qed

end (* LLL_bound_invariant *)  
end (* LLL locale *)
end
