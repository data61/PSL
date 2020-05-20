theory LP_Preliminaries
 imports 
    More_Jordan_Normal_Forms
    Matrix_LinPoly
    Jordan_Normal_Form.Matrix_Impl
    Farkas.Simplex_for_Reals
    "HOL-Library.Mapping"
begin

(*
        Component wise greater equal constraints for vector b starting at index 
            \<open> [x\<^sub>i\<^sub>n\<^sub>d\<^sub>e\<^sub>x, x\<^sub>i\<^sub>n\<^sub>d\<^sub>e\<^sub>x\<^sub>+\<^sub>1,\<dots>,x\<^sub>i\<^sub>n\<^sub>d\<^sub>e\<^sub>x\<^sub>+\<^sub>n] \<ge> [b\<^sub>0, b\<^sub>1,\<dots>,b\<^sub>n] \<close> 
*)

fun vars_from_index_geq_vec where
  "vars_from_index_geq_vec index b = [GEQ (lp_monom 1 (i+index)) (b$i). i \<leftarrow> [0..<dim_vec b]]"


lemma constraints_set_vars_geq_vec_def:
  "set (vars_from_index_geq_vec start b) = 
   {GEQ (lp_monom 1 (i+start)) (b$i) |i. i \<in> {0..<dim_vec b}}"
  using set_comprehension_list_comprehension[of 
      "(\<lambda>i. GEQ (lp_monom 1 (i+start)) (b$i))" "dim_vec b"] by auto

lemma vars_from_index_geq_sat:
  assumes "\<langle>x\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (vars_from_index_geq_vec start b)"
  assumes "i < dim_vec b"
  shows "\<langle>x\<rangle> (i+start) \<ge> b$i"
proof -
  have e_e:"GEQ (lp_monom 1 (i+start)) (b$i) \<in> set (vars_from_index_geq_vec start b)"
    using constraints_set_vars_geq_vec_def[of start b] using assms(2) by auto
  then have "\<langle>x\<rangle> \<Turnstile>\<^sub>c GEQ (lp_monom 1 (i+start)) (b$i)"
    using assms(1) by blast
  then have "(lp_monom 1 (i+start)) \<lbrace>\<langle>x\<rangle>\<rbrace> \<ge> (b$i)"
    using satisfies_constraint.simps(4)[of "\<langle>x\<rangle>" "lp_monom 1 (i + start)" "b$i"]
    by simp
  then show ?thesis 
    by simp
qed


(* Matrix A less equal vector b (A \<le> b):
           a1 b1 c1 d1 \<bullet> X \<le> b_1,
           a2 b2 c2 d2 \<bullet> X \<le> b_2,
           ...
*)

fun mat_x_leq_vec where
    "mat_x_leq_vec A b = [LEQ (matrix_to_lpolies A!i) (b$i) . i <- [0..<dim_vec b]]"

lemma mat_x_leq_vec_sol:
  assumes "\<langle>x\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (mat_x_leq_vec A b)"
  assumes "i < dim_vec b"
  shows "((matrix_to_lpolies A)!i) \<lbrace>\<langle>x\<rangle>\<rbrace> \<le> b$i"
proof -
  have e_e: "LEQ ((matrix_to_lpolies A)!i) (b$i) \<in> set (mat_x_leq_vec A b)"
    by (simp add: assms(2))
  then have "\<langle>x\<rangle> \<Turnstile>\<^sub>c LEQ ((matrix_to_lpolies A)!i) (b$i)"
    using assms(1) by blast
  then show ?thesis 
    using satisfies_constraint.simps by auto
qed


(* Matrix A less equal vector b (A = b):
           a1 b1 c1 d1 \<bullet> X = b_1,
           a2 b2 c2 d2 \<bullet> X = b_2,
           ... 
*)
fun x_mat_eq_vec where
    "x_mat_eq_vec b A = [EQ (matrix_to_lpolies A!i) (b$i) . i <- [0..<dim_vec b]]"

lemma x_mat_eq_vec_sol:
  assumes "x \<Turnstile>\<^sub>c\<^sub>s set (x_mat_eq_vec b A)"
  assumes "i < dim_vec b"
  shows "((matrix_to_lpolies A)!i) \<lbrace> x \<rbrace> = b$i"
proof -
  have e_e: "EQ ((matrix_to_lpolies A)!i) (b$i) \<in> set (x_mat_eq_vec b A)"
    by (simp add: assms(2))
  then have "x \<Turnstile>\<^sub>c EQ ((matrix_to_lpolies A)!i) (b$i)"
    using assms(1) by blast
  then show ?thesis 
    using satisfies_constraint.simps by auto
qed


section \<open> Get different matrices into same space, without interference \<close>

(* Given matrix A and B create: 
               A 0
               0 B  
*)
fun two_block_non_interfering where
  "two_block_non_interfering A B = (let z1 = 0\<^sub>m (dim_row A) (dim_col B);
                                        z2 = 0\<^sub>m (dim_row B) (dim_col A) in
                                    four_block_mat A z1 z2 B)"

lemma split_two_block_non_interfering:
  assumes "split_block (two_block_non_interfering A B) (dim_row A) (dim_col A) = (Q1, Q2, Q3, Q4)"
  shows "Q1 = A" "Q4 = B"
  using split_four_block_dual_fst_lst[of A _ _ B Q1 Q2 Q3 Q4] 
    assms by auto

lemma two_block_non_interfering_dims: 
  "dim_row (two_block_non_interfering A B) = dim_row A + dim_row B"
  "dim_col (two_block_non_interfering A B) = dim_col A + dim_col B"
  by (simp)+

lemma two_block_non_interfering_zeros_are_0:
  assumes "i < dim_row A"
    and "j \<ge> dim_col A"
    and "j < dim_col (two_block_non_interfering A B)"
  shows "(two_block_non_interfering A B)$$(i,j) = 0" "(two_block_non_interfering A B)$$(i,j) = 0"
  using four_block_mat_def assms two_block_non_interfering_dims[of A B] by auto 

lemma two_block_non_interfering_row_comp1:
  assumes "i <dim_row A"
  shows "row (two_block_non_interfering A B) i = row A i @\<^sub>v (0\<^sub>v (dim_col B))"
  using assms by auto

lemma two_block_non_interfering_row_comp2:
  assumes "i <dim_row (two_block_non_interfering A B)"
    and "i \<ge> dim_row A"
  shows "row (two_block_non_interfering A B) i = (0\<^sub>v (dim_col A)) @\<^sub>v row B (i - dim_row A)"
  using assms by (auto)

lemma first_vec_two_block_non_inter_is_first_vec:
  assumes "dim_col A + dim_col B = dim_vec v"
  assumes "dim_row A = n"
  shows "vec_first (two_block_non_interfering A B *\<^sub>v v) n = A *\<^sub>v (vec_first v (dim_col A))"
proof
  fix i
  assume a: "i < dim_vec (A *\<^sub>v vec_first v (dim_col A))"
  let ?tb = "two_block_non_interfering A B"
  have i_n: "i < n" using a assms(2) by auto
  have "vec_first (?tb *\<^sub>v v) n $ i = vec_first (vec (dim_row ?tb) (\<lambda> i. row ?tb i \<bullet> v)) n $ i"
    unfolding mult_mat_vec_def by simp
  also have "... = (vec n  (\<lambda> i. row ?tb i \<bullet> v)) $ i"
    unfolding vec_first_def using trans_less_add1
    by (metis a assms(2) dim_mult_mat_vec index_vec  two_block_non_interfering_dims(1))
  also have "... = row ?tb i \<bullet> v" by (simp add: i_n)
  also have "... = (row A i @\<^sub>v 0\<^sub>v (dim_col B)) \<bullet> v"
    using assms(2) i_n two_block_non_interfering_row_comp1 by fastforce
  also have "... = row A i \<bullet> vec_first v (dim_vec (row A i)) + 
                   0\<^sub>v (dim_col B) \<bullet> vec_last v (dim_vec (0\<^sub>v (dim_col B)))"
    using append_split_vec_distrib_scalar_prod[of "row A i" "0\<^sub>v (dim_col B)" v] assms(1) by auto
  then have "vec_first (two_block_non_interfering A B *\<^sub>v v) n $ i = 
             row A i \<bullet> vec_first v (dim_vec (row A i))"
    using calculation by auto
  then show "vec_first (two_block_non_interfering A B *\<^sub>v v) n $ i = 
             (A *\<^sub>v vec_first v (dim_col A)) $ i"
    by (simp add: assms(2) i_n)
next
  have "dim_vec (A *\<^sub>v v) = dim_row A" using dim_vec_def dim_mult_mat_vec[of A v] by auto
  then have "dim_vec (vec_first (two_block_non_interfering A B *\<^sub>v v) n) = n" by auto
  then show "dim_vec (vec_first (two_block_non_interfering A B *\<^sub>v v) n) = 
             dim_vec (A *\<^sub>v vec_first v (dim_col A))"
    by (simp add: assms(2))
qed

lemma last_vec_two_block_non_inter_is_last_vec:
  assumes "dim_col A + dim_col B = dim_vec v"
  assumes "dim_row B = n"
  shows "vec_last ((two_block_non_interfering A B) *\<^sub>v v) n = B *\<^sub>v (vec_last v (dim_col B))"
proof
  fix i
  assume a: "i < dim_vec (B *\<^sub>v vec_last v (dim_col B))"
  let ?tb = "two_block_non_interfering A B"
  let ?vl = "(vec (dim_row ?tb) (\<lambda> i. row ?tb i \<bullet> v))"
  have i_n: "i < n" using  assms(2) using a by auto
  have in3: "(dim_row ?tb) - n + i \<ge> dim_row A"
    by (simp add: assms(2))
  have in3': "(dim_row ?tb) - n + i < dim_row ?tb"
    by (simp add: assms(2) i_n two_block_non_interfering_dims(1)) 
  have "dim_row A + n = dim_row (two_block_non_interfering A B)"
    by (simp add: assms(2) two_block_non_interfering_dims(1))
  then have dim_a: "dim_row A = dim_row (two_block_non_interfering A B) - n"
    by (metis (no_types) diff_add_inverse2)
  have "vec_last (?tb *\<^sub>v v) n $ i = vec_last (vec (dim_row ?tb) (\<lambda> i. row ?tb i \<bullet> v)) n $ i"
    unfolding mult_mat_vec_def by auto
  also have "... = ?vl $ (dim_vec ?vl - n + i)"
    unfolding vec_last_def using i_n index_vec by blast
  also have "... = row ?tb ((dim_row ?tb) - n + i) \<bullet> v"
    unfolding index_vec by (simp add: assms(2) i_n two_block_non_interfering_dims(1))
  also have "... = row B i \<bullet> vec_last v (dim_vec (row B i))"
  proof -
    have "dim_vec (0\<^sub>v (dim_col A) @\<^sub>v row B i) = dim_vec v"
      by (simp add: \<open>dim_col A + dim_col B = dim_vec v\<close>)
    then show ?thesis using dim_a assms(1) in3' two_block_non_interfering_row_comp2
        append_split_vec_distrib_scalar_prod[of "0\<^sub>v (dim_col A)" "row B i" v]
      by (metis add.commute add.right_neutral diff_add_inverse
          in3 index_zero_vec(2) scalar_prod_left_zero  vec_first_carrier)
  qed
  also have "... = row B i \<bullet> vec_last v (dim_col B)" by simp
  thus "vec_last (two_block_non_interfering A B *\<^sub>v v) n $ i = (B *\<^sub>v vec_last v (dim_col B)) $ i"
    using assms(2) calculation i_n by auto
qed (simp add: assms(2))

lemma two_block_non_interfering_mult_decomposition:
  assumes "dim_col A + dim_col B = dim_vec v"      
  shows "two_block_non_interfering A B *\<^sub>v v =
         A *\<^sub>v vec_first v (dim_col A) @\<^sub>v B *\<^sub>v vec_last v (dim_col B)"
proof -
  let ?tb = "two_block_non_interfering A B"
  from first_vec_two_block_non_inter_is_first_vec[of A B v "dim_row A", OF assms]
  have "vec_first (?tb *\<^sub>v v) (dim_row A) = A *\<^sub>v vec_first v (dim_col A)"
    by blast
  moreover from last_vec_two_block_non_inter_is_last_vec[of A B v "dim_row B", OF assms]
  have "vec_last (?tb *\<^sub>v v) (dim_row B) = B *\<^sub>v vec_last v (dim_col B)"
    by blast
  ultimately show ?thesis using vec_first_last_append[of "?tb *\<^sub>v v" "(dim_row A)" "(dim_row B)"]
      dim_mult_mat_vec[of "?tb" v] two_block_non_interfering_dims(1)[of A B] 
    by (metis carrier_vec_dim_vec)
qed


(* A \<le> b   
   A = c *)
fun mat_leqb_eqc where
    "mat_leqb_eqc A b c = (let lst = matrix_to_lpolies (two_block_non_interfering A A\<^sup>T) in
                         [LEQ (lst!i) (b$i) . i <- [0..<dim_vec b]] @
                         [EQ  (lst!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]])"

lemma mat_leqb_eqc_for_LEQ:
  assumes "i < dim_vec b"
  assumes "i < dim_row A"
  shows "(mat_leqb_eqc A b c)!i = LEQ ((matrix_to_lpolies A)!i) (b$i)"
proof -
  define lst where lst: "lst = (mat_leqb_eqc A b c)"
  define l where l: "l = matrix_to_lpolies (two_block_non_interfering A A\<^sup>T)"
  have ileqA: "i < dim_row A" using assms by auto
  have "l!i = vec_to_lpoly ((row A i)@\<^sub>v 0\<^sub>v (dim_row A))"
    unfolding l using two_block_non_interfering_row_comp1[of i A "A\<^sup>T", OF ileqA]
    by (metis ileqA lpoly_of_v_equals_v_append0 matrix_to_lp_vec_to_lpoly_row 
        trans_less_add1 two_block_non_interfering_dims(1))
  then have leq: "l!i = (matrix_to_lpolies A)!i"
    using lpoly_of_v_equals_v_append0[of "row A i" "(dim_row A)"] l
    by (simp add: ileqA)
  have *: "lst = [LEQ (l!i) (b$i) . i <- [0..<dim_vec b]] @
                         [EQ  (l!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)] ]"
    unfolding l lst by (metis mat_leqb_eqc.simps)
  have "([LEQ (l!i) (b$i). i <- [0..<dim_vec b]] @ 
         [EQ (l!i) ((b@\<^sub>vc)$i). i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]]) ! i = 
         [LEQ (l!i) (b$i). i <- [0..<dim_vec b]]!i"
    using assms(2) lst by (simp add: assms(1) nth_append)
  also have "... = LEQ (l!i) (b$i)"
    using l lst
    by (simp add: assms(1))
  finally show ?thesis
    using "*" leq lst  using mat_leqb_eqc.simps[of A b c] by auto

qed

lemma mat_leqb_eqc_for_EQ:
  assumes "dim_vec b \<le> i" and "i < dim_vec (b@\<^sub>vc)"
  assumes "dim_row A = dim_vec b" and "dim_col A \<ge> dim_vec c"
  shows "(mat_leqb_eqc A b c)!i = 
    EQ (vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T (i-dim_vec b))) (c$(i-dim_vec b))"
proof -
  define lst where lst: "lst = (mat_leqb_eqc A b c)"
  define l where l: "l = matrix_to_lpolies (two_block_non_interfering A A\<^sup>T)"
  have i_s: "i < dim_row (two_block_non_interfering A A\<^sup>T)"
    using assms by (simp add: assms(2) assms(3) two_block_non_interfering_dims(1))
  have l':"l!i = vec_to_lpoly ((0\<^sub>v (dim_col A)) @\<^sub>v (row A\<^sup>T (i - dim_vec b)))"
    using l two_block_non_interfering_row_comp2[of i A "A\<^sup>T", OF i_s]
      assms(1) assms(3) i_s matrix_to_lp_vec_to_lpoly_row by presburger
  have "([LEQ (l!i) (b$i) . i <- [0..<dim_vec b]] @
                         [EQ  (l!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]])!i =
        [EQ  (l!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b..< dim_vec (b@\<^sub>vc)]] ! (i - dim_vec b)"
    by (simp add: assms(1) leD nth_append)
  also have "... = EQ (l!i) ((b@\<^sub>vc)$i)" 
    using assms(1) assms(2) by auto
  also have "... = EQ (l!i) (c$(i-dim_vec b))"
    using assms(1) assms(2) by auto
  then show ?thesis
    using mat_leqb_eqc.simps by (metis (full_types) calculation l l')
qed

lemma mat_leqb_eqc_satisfies1:
  assumes "x \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
  assumes "i < dim_vec b"
    and "i < dim_row A"
  shows "(matrix_to_lpolies A!i) \<lbrace>x\<rbrace> \<le> b$i"
proof -
  have e_e: "LEQ (matrix_to_lpolies A ! i) (b$i) \<in> set (mat_leqb_eqc A b c)"
    using mat_leqb_eqc_for_LEQ[of i b A c, OF assms(2) assms(3)] 
      nth_mem[of i "matrix_to_lpolies A"] mat_leqb_eqc.simps 
    by (metis (no_types, lifting) assms(2) diff_zero in_set_conv_nth length_append length_map 
        length_upt trans_less_add1)
  then have "x \<Turnstile>\<^sub>c LEQ ((matrix_to_lpolies A)!i) (b$i)"
    using assms by blast
  then show ?thesis 
    using satisfies_constraint.simps by auto
qed

lemma mat_leqb_eqc_satisfies2:
  assumes "x \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
  assumes "dim_vec b \<le> i" and "i < dim_vec (b@\<^sub>vc)"
    and "dim_row A = dim_vec b" and "dim_vec c \<le> dim_col A"
  shows "(matrix_to_lpolies (two_block_non_interfering A A\<^sup>T) ! i) \<lbrace>x\<rbrace> = (b @\<^sub>v c) $ i"
proof -
  have e_e: "EQ (vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T (i - dim_vec b))) (c $ (i - dim_vec b))
              \<in> set (mat_leqb_eqc A b c)"
    using assms(2) mat_leqb_eqc.simps[of A b c] 
      nth_mem[of i "(mat_leqb_eqc A b c)"]
    using  mat_leqb_eqc_for_EQ[of b i c A, OF assms(2) assms(3) assms(4) assms(5)]
    by (metis (mono_tags, lifting) add_diff_cancel_left' assms(3) diff_zero index_append_vec(2) 
        length_append length_map length_upt)
  hence sateq: "x \<Turnstile>\<^sub>c EQ (vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v 
                row A\<^sup>T (i - dim_vec b))) (c $ (i - dim_vec b))"
    using assms(1) by blast
  have *: "i < dim_row (two_block_non_interfering A A\<^sup>T)"
    by (metis assms(3) assms(4) assms(5) dual_order.order_iff_strict dual_order.strict_trans 
        index_append_vec(2) index_transpose_mat(2) nat_add_left_cancel_less 
        two_block_non_interfering_dims(1))
  have **: "dim_row A \<le> i"
    by (simp add: assms(2) assms(4))
  then have "x \<Turnstile>\<^sub>c EQ ((matrix_to_lpolies (two_block_non_interfering A A\<^sup>T))!i) ((b@\<^sub>vc)$i)"
    using two_block_non_interfering_row_comp2[of i A "A\<^sup>T", OF * **]
    by (metis "*" sateq assms(3) assms(4) index_append_vec(1) index_append_vec(2) leD
        matrix_to_lp_vec_to_lpoly_row)
  then show ?thesis
    using satisfies_constraint.simps(5) by simp
qed

lemma mat_leqb_eqc_simplex_satisfies2:
  assumes "simplex (mat_leqb_eqc A b c) = Sat x"
  assumes "dim_vec b \<le> i" and "i < dim_vec (b@\<^sub>vc)"
    and "dim_row A = dim_vec b" and "dim_vec c \<le> dim_col A"
  shows "(matrix_to_lpolies (two_block_non_interfering A A\<^sup>T) ! i) \<lbrace>\<langle>x\<rangle>\<rbrace> = (b @\<^sub>v c) $ i"
  using mat_leqb_eqc_satisfies2 assms(1) assms(2) assms(3) assms(4) assms(5) simplex(3) by blast

fun index_geq_n where
  "index_geq_n i n = GEQ (lp_monom 1 i) n"

lemma index_geq_n_simplex: 
  assumes "\<langle>x\<rangle>  \<Turnstile>\<^sub>c (index_geq_n i n)"
  shows "\<langle>x\<rangle> i \<ge> n"
  using assms by simp


(* In the variables x_i to x_i+(length v) we synthesise a vector that is pointwise
       greater than v *)
fun from_index_geq0_vector where
  "from_index_geq0_vector i v = [GEQ (lp_monom 1 (i+j)) (v$j) . j <-[0..<dim_vec v]]"

lemma from_index_geq_vector_simplex: 
  assumes "x \<Turnstile>\<^sub>c\<^sub>s set (from_index_geq0_vector i v)"
  "j < dim_vec v"
  shows "x (i + j) \<ge> v$j"
proof -
  have "GEQ (lp_monom 1 (i+j)) (v$j)\<in> set (from_index_geq0_vector i v)"
    by (simp add: assms(2))
  moreover have "x \<Turnstile>\<^sub>c GEQ (lp_monom 1 (i+j)) (v$j)"
    using calculation(1) assms  by force
  ultimately show ?thesis by simp
qed

lemma from_index_geq0_vector_simplex2: 
  assumes "\<langle>x\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (from_index_geq0_vector i v)"
  assumes "i \<le> j" and "j < (dim_vec v) + i"
  shows "\<langle>x\<rangle> j \<ge> v$(j - i)"
  by (metis assms(1) assms(2) assms(3) from_index_geq_vector_simplex 
      le_add_diff_inverse less_diff_conv2)


(* [c1, ... cm, 01, ... 0n] * X \<ge> [01, ... 0m, b1,...,bn] * X *)
fun x_times_c_geq_y_times_b where
  "x_times_c_geq_y_times_b c b = GEQPP (vec_to_lpoly (c @\<^sub>v 0\<^sub>v (dim_vec b)))
                                       (vec_to_lpoly (0\<^sub>v (dim_vec c) @\<^sub>v b))"

lemma x_times_c_geq_y_times_b_correct:
  assumes "simplex [x_times_c_geq_y_times_b c b] = Sat x"
  shows "((vec_to_lpoly (c @\<^sub>v 0\<^sub>v (dim_vec b))) \<lbrace> \<langle>x\<rangle> \<rbrace>) \<ge>
         ((vec_to_lpoly (0\<^sub>v (dim_vec c) @\<^sub>v b)) \<lbrace> \<langle>x\<rangle> \<rbrace>)"
 using assms simplex(3) by fastforce


(* Splitting an assignment into two vectors *)

(* The first [0...(i-1)] elements and [i...j] elements *)
definition split_i_j_x where
  "split_i_j_x i j x = (vec i \<langle>x\<rangle>, vec (j - i) (\<lambda>y. \<langle>x\<rangle> (y+i)))"

abbreviation split_n_m_x where 
  "split_n_m_x n m x \<equiv> split_i_j_x n (n+m) x"


lemma split_vec_dims:
  assumes "split_i_j_x i j x = (a ,b)"
  shows "dim_vec a = i" "dim_vec b = (j - i)"
  using assms(1) unfolding split_i_j_x_def by auto+

lemma split_n_m_x_abbrev_dims: 
  assumes "split_n_m_x n m x = (a, b)"
  shows "dim_vec a = n" "dim_vec b = m"
  using split_vec_dims 
  using assms apply blast
  using assms split_vec_dims(2) by fastforce

lemma split_access_fst_1:
  assumes "k < i"
  assumes "split_i_j_x i j x = (a, b)"
  shows "a $ k = \<langle>x\<rangle> k"
  by (metis Pair_inject assms(1) assms(2) index_vec split_i_j_x_def)

lemma split_access_snd_1:
  assumes "i \<le> k" and "k < j"
  assumes "split_i_j_x i j x = (a, b)"
  shows "b $ (k - i) = \<langle>x\<rangle> k"
proof -
  have "vec (j - i) (\<lambda>n. \<langle>x\<rangle> (n + i)) = b"
    by (metis (no_types) assms(3) prod.sel(2) split_i_j_x_def)
  then show ?thesis
    using assms(1) assms(2) by fastforce
qed

lemma split_access_fst_2:
  assumes "(x, y) = split_i_j_x i j Z"
  assumes "k < dim_vec x"
  shows "x$k = \<langle>Z\<rangle> k"
  by (metis assms(1) assms(2) split_access_fst_1 split_vec_dims(1))

lemma split_access_snd_2:
  assumes "(x, y) = split_i_j_x i j Z"
  assumes "k < dim_vec y"
  shows "y$k = \<langle>Z\<rangle> (k+dim_vec x)"
  using assms split_i_j_x_def[of i j Z] by auto

lemma from_index_geq0_vector_split_snd:
  assumes "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (from_index_geq0_vector d v)"
  assumes "(x, y) = split_n_m_x d m X"
  shows "\<And>i. i < dim_vec v \<Longrightarrow> i < m \<Longrightarrow> y$i \<ge> v$i"
  using assms unfolding split_i_j_x_def 
  using from_index_geq_vector_simplex[of d v "\<langle>X\<rangle>" _] index_vec by (simp add: add.commute)

lemma split_coeff_vec_index_sum:
  assumes "(x,y) = split_i_j_x (dim_vec (lpoly_to_vec v)) l X"
  shows "(\<Sum>i = 0..<dim_vec x. Abstract_Linear_Poly.coeff v i * \<langle>X\<rangle> i) = 
         (\<Sum>i = 0..<dim_vec x. lpoly_to_vec v $ i * x $ i)"
proof -
  from valuate_with_dim_poly[of v "\<langle>X\<rangle>", symmetric] 
  have "(\<Sum>i = 0..<dim_vec x. (lpoly_to_vec v) $ i * \<langle>X\<rangle> i) = 
        (\<Sum>i = 0..<dim_vec x. (lpoly_to_vec v) $ i * x $ i)"
    by (metis (no_types, lifting) assms split_access_fst_1 split_vec_dims(1) sum.ivl_cong)
  then show ?thesis
    by (metis (no_types, lifting) assms dim_poly_dim_vec_equiv 
        lin_poly_to_vec_coeff_access split_vec_dims(1) sum.ivl_cong)
qed

lemma scalar_prod_valuation_after_split_equiv1:
  assumes "(x,y) = split_i_j_x (dim_vec (lpoly_to_vec v)) l X"
  shows "(lpoly_to_vec v) \<bullet> x = (v \<lbrace>\<langle>X\<rangle>\<rbrace>)"
proof -
  from valuate_with_dim_poly[of v "\<langle>X\<rangle>", symmetric] 
  have 1: "(v \<lbrace>\<langle>X\<rangle>\<rbrace>) = (\<Sum>i = 0..<dim_poly v. Abstract_Linear_Poly.coeff v i * \<langle>X\<rangle> i)" by simp
  have "(\<Sum>i = 0..<dim_vec x. (lpoly_to_vec v) $ i * \<langle>X\<rangle> i) = 
    (\<Sum>i = 0..<dim_vec x. (lpoly_to_vec v) $ i * x $ i)"
    by (metis (no_types, lifting) assms split_access_fst_1 split_vec_dims(1) sum.ivl_cong)
  also have "... =  (lpoly_to_vec v) \<bullet> x"
    unfolding scalar_prod_def by blast
  finally show ?thesis
    by (metis (no_types, lifting) "1" dim_poly_dim_vec_equiv lin_poly_to_vec_coeff_access 
        split_vec_dims(1) sum.ivl_cong assms)
qed


definition mat_times_vec_leq ("[_*\<^sub>v_]\<le>_" [1000,1000,100])
  where
    "[A *\<^sub>v x]\<le>b \<longleftrightarrow> (\<forall>i < dim_vec b. (A *\<^sub>v x)$i \<le> b$i) \<and>
                    (dim_row A = dim_vec b) \<and>
                    (dim_col A = dim_vec x)"

definition vec_times_mat_eq ("[_\<^sub>v*_]=_" [1000,1000,100])
  where
    "[y \<^sub>v* A]=c \<longleftrightarrow> (\<forall>i < dim_vec c. (A\<^sup>T *\<^sub>v y)$i = c$i) \<and>
                    (dim_col A\<^sup>T = dim_vec y) \<and>
                    (dim_row A\<^sup>T = dim_vec c)"

definition vec_times_mat_leq ("[_\<^sub>v*_]\<le>_" [1000,1000,100])
  where
    "[y \<^sub>v* A]\<le>c \<longleftrightarrow> (\<forall>i < dim_vec c. (A\<^sup>T *\<^sub>v y)$i \<le> c$i) \<and>
                    (dim_col A\<^sup>T = dim_vec y) \<and>
                    (dim_row A\<^sup>T = dim_vec c)"

lemma mat_times_vec_leqI[intro]:
  assumes "dim_row A = dim_vec b"
  assumes "dim_col A = dim_vec x"
  assumes "\<And>i. i < dim_vec b \<Longrightarrow> (A *\<^sub>v x)$i \<le> b$i"
  shows "[A *\<^sub>v x]\<le>b"
  unfolding mat_times_vec_leq_def using assms by auto

lemma mat_times_vec_leqD[dest]:
  assumes "[A *\<^sub>v x]\<le>b"
  shows "dim_row A = dim_vec b" "dim_col A = dim_vec x" "\<And>i. i < dim_vec b \<Longrightarrow> (A *\<^sub>v x)$i \<le> b$i"
  using assms mat_times_vec_leq_def by blast+

lemma vec_times_mat_eqD[dest]:
  assumes "[y \<^sub>v* A]=c"
  shows "(\<forall>i < dim_vec c. (A\<^sup>T *\<^sub>v y)$i = c$i)" "(dim_col A\<^sup>T = dim_vec y)" "(dim_row A\<^sup>T = dim_vec c)"
  using assms vec_times_mat_eq_def by blast+

lemma vec_times_mat_leqD[dest]:
  assumes "[y \<^sub>v* A]\<le>c"
  shows "(\<forall>i < dim_vec c. (A\<^sup>T *\<^sub>v y)$i \<le> c$i)" "(dim_col A\<^sup>T = dim_vec y)" "(dim_row A\<^sup>T = dim_vec c)"
  using assms vec_times_mat_leq_def by blast+

lemma mat_times_vec_eqI[intro]:  
  assumes "dim_col A\<^sup>T = dim_vec x"
  assumes "dim_row A\<^sup>T = dim_vec c"
  assumes "\<And>i. i < dim_vec c \<Longrightarrow> (A\<^sup>T *\<^sub>v x)$i = c$i"
  shows "[x \<^sub>v* A]=c"
  unfolding vec_times_mat_eq_def using assms by blast

lemma mat_leqb_eqc_split_correct1:
  assumes "dim_vec b = dim_row A"
  assumes "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
  assumes "(x,y) = split_i_j_x (dim_col A) l X"  
  shows "[A *\<^sub>v x]\<le>b"
proof (standard, goal_cases)
  case 1
  then show ?case using assms(1)[symmetric] .
  case 2
  then show ?case using assms(3) unfolding split_i_j_x_def 
    using split_vec_dims[of  0 "dim_col A" X x y] by auto
  case (3 i)
  with mat_leqb_eqc_satisfies1[of A b c "\<langle>X\<rangle>" i] 
  have m: "(matrix_to_lpolies A ! i) \<lbrace> \<langle>X\<rangle> \<rbrace> \<le> b $ i"
    using assms(1) assms(2) by linarith
  have leq: "dim_poly (vec_to_lpoly (row A i)) \<le> dim_col A"
    using vec_to_poly_dim_less[of "row A i"] by simp
  have i: "i < dim_row A"
    using "3" assms(1) by linarith
  from two_block_non_interfering_row_comp1[of i A "A\<^sup>T"]
  have "row (two_block_non_interfering A A\<^sup>T) i = row A i @\<^sub>v 0\<^sub>v (dim_col A\<^sup>T)"
    using "3" assms(1) by linarith
  have "(vec_to_lpoly (row A i @\<^sub>v 0\<^sub>v (dim_col A\<^sup>T))) \<lbrace>\<langle>X\<rangle>\<rbrace> = ((vec_to_lpoly (row A i)) \<lbrace>\<langle>X\<rangle>\<rbrace>)"
    using lpoly_of_v_equals_v_append0 by auto
  also have "... = (\<Sum>a = 0..<dim_poly (vec_to_lpoly (row A i)). 
                      Abstract_Linear_Poly.coeff (vec_to_lpoly (row A i)) a * \<langle>X\<rangle> a)" 
    using valuate_with_dim_poly[of "vec_to_lpoly (row A i)" "\<langle>X\<rangle>"] by blast
  also have "... = (\<Sum>a = 0..<dim_col A. Abstract_Linear_Poly.coeff (vec_to_lpoly (row A i)) a * \<langle>X\<rangle> a)"
    using split_coeff_vec_index_sum[of x y]
      sum_dim_vec_equals_sum_dim_poly[of "row A i" "\<langle>X\<rangle>"] by auto
  also have "... = row A i \<bullet> x" 
    unfolding scalar_prod_def using \<open>dim_col A = dim_vec x\<close> i assms(3)
    using matrix_to_lpolies_coeff_access[of i A] matrix_to_lp_vec_to_lpoly_row[of i A] 
      split_access_fst_1[of _ "(dim_col A)" l X x y] by fastforce
  finally show ?case
    using m i lpoly_of_v_equals_v_append0 by auto
qed

lemma mat_leqb_eqc_split_simplex_correct1:
  assumes "dim_vec b = dim_row A"
  assumes "simplex (mat_leqb_eqc A b c) = Sat X"
  assumes "(x,y) = split_i_j_x (dim_col A) l X"  
  shows "[A *\<^sub>v x]\<le>b"
  using mat_leqb_eqc_split_correct1[of b A c X x y] assms(1) assms(2) assms(3) simplex(3) by blast

lemma sat_mono:
  assumes "set A \<subseteq> set B"
  shows "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set B \<Longrightarrow> \<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set A"
  using assms(1) assms by blast

lemma mat_leqb_eqc_split_subset_correct1:
  assumes "dim_vec b = dim_row A"
  assumes "set (mat_leqb_eqc A b c) \<subseteq> set S"
  assumes "simplex S = Sat X"
  assumes "(x,y) = split_i_j_x (dim_col A) l X"  
  shows "[A *\<^sub>v x]\<le>b"
  using sat_mono assms(1) assms(2) assms(3) assms(4) 
    mat_leqb_eqc_split_correct1 simplex(3) by blast

lemma mat_leqb_eqc_split_correct2:
  assumes "dim_vec c = dim_row A\<^sup>T"
  assumes "dim_vec b = dim_col A\<^sup>T"
  assumes "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
  assumes "(x, y) = split_n_m_x (dim_row A\<^sup>T) (dim_col A\<^sup>T) X"  
  shows "[y \<^sub>v* A]=c"
proof (standard, goal_cases)
case 1
  then show ?case 
    using assms split_n_m_x_abbrev_dims(2)[OF assms(4)[symmetric]] by linarith
  case 2
  then show ?case using assms(1)[symmetric] .
  case (3 i)
  define lst where lst: "lst = matrix_to_lpolies (two_block_non_interfering A A\<^sup>T)"
  define db where db: "db = dim_vec b"
  define dc where dc: "dc = dim_vec c"
  have cA: "dim_vec c \<le> dim_col A"
    by (simp add: assms(1))
  have dbi_dim: "db+i < dim_vec (b @\<^sub>v c)"
    by (simp add: "3" db)
  have *: "dim_vec b \<le> db+i"
    by (simp add: db)
  have "([LEQ (lst!i) (b$i) . i <- [0..<dim_vec b]] @
        [EQ  (lst!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]]) ! (db + i) =
         EQ (lst!(db+i)) ((b@\<^sub>vc)$(db+i))" using mat_leqb_eqc_for_EQ[of b "db+i" c A]
    nth_append[of "[LEQ (lst!i) (b$i) . i <- [0..<dim_vec b]]" 
      "[EQ  (lst!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]]"]
    by (simp add: "3" db)
  have rowA: "dim_vec b = dim_row A"
    using assms index_transpose_mat(3)[of A] by linarith
  have "\<langle>X\<rangle> \<Turnstile>\<^sub>c EQ (lst!(db+i)) (c$i)"
  proof -
    have "db + i - dim_vec b = i"
      using db diff_add_inverse by blast
    then have "(lst ! (db + i)) \<lbrace> \<langle>X\<rangle> \<rbrace> = c $ i"
      by (metis dbi_dim rowA * cA assms(3) index_append_vec(1)
          index_append_vec(2) leD lst mat_leqb_eqc_satisfies2)
    then show ?thesis
      using satisfies_constraint.simps(5)[of "\<langle>X\<rangle>" "(lst ! (db + i))" "(c $ i)"] by simp
  qed
  then have sat: "(lst!(db+i)) \<lbrace>\<langle>X\<rangle>\<rbrace> = c$i"
    by simp
  define V where V: "V = vec (db+dc) (\<lambda>i. \<langle>X\<rangle> i)"
  have vdim: "dim_vec V = dim_vec (b@\<^sub>vc)" using V db dc by simp
  have *: "db + i < dim_row (two_block_non_interfering A A\<^sup>T)"
    by (metis dbi_dim assms(1) index_append_vec(2) rowA two_block_non_interfering_dims(1))
  have **: "dim_row A \<le> db + i"
    by (simp add: assms(2) db)
  from two_block_non_interfering_row_comp2[of "db+i" A "A\<^sup>T", OF * **]
  have eql: "row (two_block_non_interfering A A\<^sup>T) (db + i) = 0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i"
    by (simp add: assms(2) db)
  with matrix_to_lp_vec_to_lpoly_row[of i "A\<^sup>T"]
  have eqv: "lst!(db+i) = vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)"
    using "*" lst matrix_to_lp_vec_to_lpoly_row by presburger
  then  have "\<forall>j<dim_col A. Abstract_Linear_Poly.coeff (lst!(db+i)) j = 0"
    by (metis index_append_vec(1) index_append_vec(2) index_zero_vec(1) index_zero_vec(2) 
        vec_to_lin_poly_coeff_access trans_less_add1)
  moreover have "\<forall>j\<ge>db+dc. Abstract_Linear_Poly.coeff (lst!(db+i)) j = 0"
    by (metis (mono_tags, lifting) eqv index_transpose_mat(3) index_zero_vec(2) leD
        add.commute assms(1) assms(2) coeff_nonzero_dim_vec_non_zero(2) index_append_vec(2) 
        index_row(2) index_transpose_mat(2) db dc)
  moreover have "vars (lst!(db+i)) \<subseteq> {dim_col A..<db+dc}"
    by (meson atLeastLessThan_iff calculation(1) calculation(2) coeff_zero not_le subsetI)
  ultimately have "(lst!(db+i))\<lbrace>\<langle>X\<rangle>\<rbrace> = (\<Sum>j\<in>{dim_col A..<db+dc}. Abstract_Linear_Poly.coeff (lst!(db+i)) j * \<langle>X\<rangle> j)"
    using eval_poly_with_sum_superset[of "{dim_col A..<db+dc}" "lst!(db+i)" "\<langle>X\<rangle>"] by blast
  also have "... = (\<Sum>j\<in>{dim_col A..<db+dc}. Abstract_Linear_Poly.coeff (lst!(db+i)) j * V$j)" 
    using V by auto
  also have "... = (\<Sum>j\<in>{dim_col A..<db+dc}. (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)$j * V$j)"
  proof - 
    have "\<forall>j\<in>{dim_col A..<db+dc}. Abstract_Linear_Poly.coeff (lst!(db+i)) j = (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)$j"
      by (metis \<open>V \<equiv> vec (db + dc) \<langle>X\<rangle>\<close> vdim assms(1) assms(2) index_transpose_mat(2)
          atLeastLessThan_iff dim_vec eql eqv index_append_vec(2) index_row(2) 
          vec_to_lin_poly_coeff_access semiring_normalization_rules(24) 
          two_block_non_interfering_dims(2))
    then show ?thesis
      by (metis (mono_tags, lifting) sum.cong)
  qed
  also have "... = (\<Sum>j\<in>{0..<dim_col A}. (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)$j * V$j) + 
                   (\<Sum>j\<in>{dim_col A..<db+dc}. (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)$j * V$j)"
    by (metis (no_types, lifting) add_cancel_left_left atLeastLessThan_iff mult_eq_0_iff
        class_semiring.add.finprod_all1 index_append_vec(1) index_zero_vec(1)
        index_zero_vec(2) trans_less_add1)
  also have "... = (\<Sum>j\<in>{0..<db+dc}. (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i)$j * V$j)"
    by (metis (no_types, lifting) add.commute assms(1) dc index_transpose_mat(2) 
        le_add1 le_add_same_cancel1 sum.atLeastLessThan_concat)
  also have "... = (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T i) \<bullet> V"
    unfolding scalar_prod_def by (simp add: V)
  also have "... = 0\<^sub>v (dim_col A) \<bullet> vec_first V (dim_vec (0\<^sub>v (dim_col A))) + 
                   row A\<^sup>T i \<bullet> vec_last V (dim_vec (row A\<^sup>T i))"
    using append_split_vec_distrib_scalar_prod[of "0\<^sub>v (dim_col A)" "row A\<^sup>T i" V]
    by (metis (no_types, lifting) \<open>dim_vec V = dim_vec (b @\<^sub>v c)\<close> add.commute assms(1) 
        assms(2) index_append_vec(2) index_row(2) index_transpose_mat(2) 
        index_transpose_mat(3) index_zero_vec(2))
  also have  "0\<^sub>v (dim_col A) \<bullet> vec_first V (dim_vec (0\<^sub>v (dim_col A))) + 
                   row A\<^sup>T i \<bullet> vec_last V (dim_vec (row A\<^sup>T i)) = (row A\<^sup>T i) \<bullet> y"
  proof - 
    have "vec_last V (dim_vec (row A\<^sup>T i)) = y"
    proof (standard, goal_cases)
      case (1 i)
      then show ?case 
      proof -
        have f1: "dim_col A\<^sup>T = db"
          by (simp add: assms(2) db)
        then have "\<forall>v va. vec db (\<lambda>n. \<langle>X\<rangle> (n + dc)) = v \<or> (x, y) \<noteq> (va, v)"
          by (metis Pair_inject add_diff_cancel_left' assms(1) assms(4) dc split_i_j_x_def)
        then show ?case
          unfolding V vec_last_def
          using split_access_fst_1[of "(dim_row A\<^sup>T)"  i "(dim_col A\<^sup>T)" X x y]
          by (metis "1" add.commute add_diff_cancel_left' add_less_cancel_left 
              dim_vec f1 index_row(2) index_vec)
      qed
    next
      case 2
      then show ?case
        using \<open>dim_col A\<^sup>T = dim_vec y\<close> by auto
    qed
    then show ?thesis
      by (simp add: assms(1))
  qed
  then show ?case unfolding mult_mat_vec_def by (metis "3" assms(1) calculation index_vec sat)
qed

lemma mat_leqb_eqc_split_simplex_correct2:
  assumes "dim_vec c = dim_row A\<^sup>T"
  assumes "dim_vec b = dim_col A\<^sup>T"
  assumes "simplex (mat_leqb_eqc A b c) = Sat X"
  assumes "(x, y) = split_n_m_x (dim_row A\<^sup>T) (dim_col A\<^sup>T) X"  
  shows "[y \<^sub>v* A]=c"
  using assms(1) assms(2) assms(3) assms(4) mat_leqb_eqc_split_correct2 simplex(3) by blast

lemma mat_leqb_eqc_correct:
  assumes "dim_vec c = dim_row A\<^sup>T"
    and "dim_vec b = dim_col A\<^sup>T"
  assumes "simplex (mat_leqb_eqc A b c) = Sat X"
  assumes "(x, y) = split_n_m_x (dim_row A\<^sup>T) (dim_col A\<^sup>T) X"
  shows "[y \<^sub>v* A]=c" "[A *\<^sub>v x]\<le>b"
  using mat_leqb_eqc_split_simplex_correct1[of b A c X x y]
  using assms(1) assms(2) assms(3) assms(4) mat_leqb_eqc_split_simplex_correct2 apply blast
  using mat_leqb_eqc_split_correct2[of b A c X x y]
  by (metis (no_types) Matrix.transpose_transpose assms(2) assms(3) assms(4) index_transpose_mat(3)
      mat_leqb_eqc_split_simplex_correct1[of b A c X x y])

lemma eval_lpoly_eq_dot_prod_split1:
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows"(vec_to_lpoly c) \<lbrace>\<langle>X\<rangle>\<rbrace> =  c \<bullet> x"
proof -
  have *: "(vec_to_lpoly c) \<lbrace>\<langle>X\<rangle>\<rbrace> =
           (\<Sum>i\<in>vars (vec_to_lpoly c). Abstract_Linear_Poly.coeff (vec_to_lpoly c) i * \<langle>X\<rangle> i)"
    using linear_poly_sum sum.cong eval_poly_with_sum by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec c}. Abstract_Linear_Poly.coeff (vec_to_lpoly c) i * \<langle>X\<rangle> i)"
    using vars_subset_dim_vec_to_lpoly_dim[of c] linear_poly_sum[of "vec_to_lpoly c" "\<langle>X\<rangle>"] 
      eval_poly_with_sum_superset[of "{0..<dim_vec c}" "vec_to_lpoly c" "\<langle>X\<rangle>"] by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec c}. c$i * x$i)"
    using split_access_fst_1[of _ "dim_vec c" "(dim_vec c) + (dim_vec b)" X x y]
      split_access_snd_1[of "dim_vec c" _ "((dim_vec c) + (dim_vec b))" X x y]
      vec_to_lin_poly_coeff_access[of _ c] using assms by auto
  also have "... = c \<bullet> x"
    unfolding scalar_prod_def
    using split_vec_dims(1)[of "dim_vec c" "(dim_vec c) + (dim_vec b)" X x y] assms by auto
  finally show ?thesis .
qed

lemma eval_lpoly_eq_dot_prod_split2:
  assumes "(x, y) = split_n_m_x (dim_vec b) (dim_vec c) X"
  shows"(vec_to_lpoly (0\<^sub>v (dim_vec b) @\<^sub>v c)) \<lbrace>\<langle>X\<rangle>\<rbrace> =  c \<bullet> y"
proof -
  let ?p = "(vec_to_lpoly ((0\<^sub>v (dim_vec b) @\<^sub>v c)))"
  let ?v0 = "(0\<^sub>v (dim_vec b) @\<^sub>v c)"
  have *: "\<forall>i<dim_vec b. Abstract_Linear_Poly.coeff ?p i = 0"
    using coeff_nonzero_dim_vec_non_zero(1) by fastforce
  have **: "dim_vec ?v0 = dim_vec b + dim_vec c"
    by simp
  have "?p \<lbrace>\<langle>X\<rangle>\<rbrace> = (\<Sum>i\<in>vars ?p. Abstract_Linear_Poly.coeff ?p i * \<langle>X\<rangle> i)"
    using eval_poly_with_sum by blast
  also have "... = (\<Sum>i\<in>{0..<dim_vec ?v0}. Abstract_Linear_Poly.coeff ?p i * \<langle>X\<rangle> i)" 
    using eval_poly_with_sum_superset[of "{0..<dim_vec ?v0}" ?p "\<langle>X\<rangle>"] calculation
      vars_subset_dim_vec_to_lpoly_dim[of ?v0] by force
  also have "... = (\<Sum>i\<in>{0..<dim_vec b}. Abstract_Linear_Poly.coeff ?p i * \<langle>X\<rangle> i) + 
                   (\<Sum>i\<in>{(dim_vec b)..<dim_vec ?v0}. Abstract_Linear_Poly.coeff ?p i * \<langle>X\<rangle> i)"
    by (simp add: sum.atLeastLessThan_concat)
  also have "... = (\<Sum>i\<in>{(dim_vec b)..<dim_vec ?v0}. Abstract_Linear_Poly.coeff ?p i * \<langle>X\<rangle> i)"
    using * by simp
  also have "... = (\<Sum>i\<in>{(dim_vec b)..<dim_vec ?v0}. ?v0$i * \<langle>X\<rangle> i)"
    using vec_to_lin_poly_coeff_access by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec c}. ?v0$(i+dim_vec b) * \<langle>X\<rangle> (i+dim_vec b))"
    using index_zero_vec(2)[of "dim_vec b"] index_append_vec(2)[of "0\<^sub>v (dim_vec b)" c] ** *
       sum.shift_bounds_nat_ivl[of "(\<lambda>i. ?v0$i * \<langle>X\<rangle> i)" 0 "dim_vec b" "dim_vec c"]
    by (simp add: add.commute)
  also have "... = (\<Sum>i\<in>{0..<dim_vec c}. c$i * \<langle>X\<rangle> (i+dim_vec b))"
    by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec c}. c$i * y$i)"
    using split_access_snd_2[of x y "(dim_vec b)" "(dim_vec c)" X] assms
    by (metis (mono_tags, lifting) atLeastLessThan_iff split_access_snd_2 
        split_n_m_x_abbrev_dims(2) split_vec_dims(1) sum.cong)
  also have "... = c \<bullet> y"
    by (metis assms scalar_prod_def split_n_m_x_abbrev_dims(2))
  finally show ?thesis .
qed

lemma x_times_c_geq_y_times_b_split_dotP:
  assumes "\<langle>X\<rangle> \<Turnstile>\<^sub>c x_times_c_geq_y_times_b c b"
  assumes "(x, y) = split_n_m_x (dim_vec c) (dim_vec b) X"
  shows "c \<bullet> x \<ge> b \<bullet> y"
  using assms lpoly_of_v_equals_v_append0 eval_lpoly_eq_dot_prod_split2[of x y c b X]
   eval_lpoly_eq_dot_prod_split1[of x y c b X]  by auto

lemma mult_right_leq:
  fixes A :: "('a::{comm_semiring_1,ordered_semiring}) mat"
  assumes "dim_vec y = dim_vec b"
    and "\<forall>i < dim_vec y. y$i \<ge> 0"
    and "[A *\<^sub>v x]\<le> b"
  shows "(A *\<^sub>v x) \<bullet> y \<le> b \<bullet> y"
proof -
  have "(\<Sum>n<dim_vec b. (A *\<^sub>v x) $ n * y $ n) \<le> (\<Sum>n<dim_vec b. b $ n * y $ n)"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) lessThan_iff 
        mat_times_vec_leq_def mult_right_mono sum_mono)
  then show ?thesis
    by (metis (no_types) assms(1) atLeast0LessThan scalar_prod_def)
qed

lemma mult_right_eq:
  assumes "dim_vec x = dim_vec c"
    and "[y \<^sub>v* A]=c"
  shows "(A\<^sup>T *\<^sub>v y) \<bullet> x = c \<bullet> x"
  unfolding scalar_prod_def 
  using atLeastLessThan_iff[of _ 0 "dim_vec x"] vec_times_mat_eq_def[of y A c] 
    sum.cong[of _ _ "\<lambda>i. (A\<^sup>T *\<^sub>v y) $ i * x $ i" "\<lambda>i. c $ i * x $ i"]
  by (metis (mono_tags, lifting) assms(1) assms(2))

lemma soundness_mat_x_leq:
  assumes "dim_row A = dim_vec b"
  assumes "simplex (mat_x_leq_vec A b) = Sat X"
  shows "\<exists>x. [A *\<^sub>v x]\<le>b"
proof
  define x where x: "x = fst (split_n_m_x (dim_col A) (dim_row A) X)"
  have *: "dim_vec x = dim_col A" by (simp add: split_i_j_x_def x)
  have "\<forall>i<dim_vec b. (A *\<^sub>v x) $ i \<le> b $ i"
  proof (standard, standard)
    fix i
    assume "i < dim_vec b"
    have "row A i \<bullet> x \<le> b$i"
      using mat_x_leq_vec_sol[of A b X i]
      by (metis \<open>i < dim_vec b\<close> assms(1) assms(2) eval_lpoly_eq_dot_prod_split1 
          fst_conv index_row(2) matrix_to_lp_vec_to_lpoly_row simplex(3) split_i_j_x_def x)
    then show "(A *\<^sub>v x) $ i \<le> b $ i"
      by (simp add: \<open>i < dim_vec b\<close> assms(1))
  qed
  then show "[A *\<^sub>v x]\<le>b"
    using mat_times_vec_leqI[of A b x, OF assms(1) *[symmetric]] by auto
qed

lemma completeness_mat_x_leq:
  assumes "\<exists>x. [A *\<^sub>v x]\<le>b"
  shows "\<exists>X. simplex (mat_x_leq_vec A b) = Sat X"
proof (rule ccontr)
  assume 1: "\<nexists>X. simplex (mat_x_leq_vec A b) = Inr X"
  have *: "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (mat_x_leq_vec A b)"
    using simplex(1)[of "mat_x_leq_vec A b"] using "1" sum.exhaust_sel by blast
  then have "dim_vec b = dim_row A" using assms mat_times_vec_leqD(1)[of A _ b] by auto
  then obtain x where x: "[A *\<^sub>v x]\<le>b" 
    using assms by blast
  have x_A: "dim_vec x = dim_col A"
    using x by auto
  define v where v: "v = (\<lambda>i. (if i < dim_vec x then x$i else 0))"
  have v_d: "\<forall>i < dim_vec x. x$i = v i"
    by (simp add: v)
  have "v \<Turnstile>\<^sub>c\<^sub>s set (mat_x_leq_vec A b)"
  proof 
    fix c
    assume "c \<in> set (mat_x_leq_vec A b)"
    then obtain i where i: "c = LEQ (matrix_to_lpolies A!i) (b$i)" "i < dim_vec b"
      by auto
    let ?p = "matrix_to_lpolies A!i"
    have 2: "?p\<lbrace> v \<rbrace> = (row A i) \<bullet> x"
      using matrix_to_lpolies_lambda_valuate_scalarP[of i A x] v
      by (metis \<open>dim_vec b = dim_row A\<close> i(2) x_A)
    also have "... \<le> b$i"
      by (metis i(2) index_mult_mat_vec mat_times_vec_leq_def x)
    finally show "v \<Turnstile>\<^sub>c c"
      using i(1) satisfies_constraint.simps(3)[of v "(matrix_to_lpolies A ! i)" "b $ i"] 
        2 \<open>row A i \<bullet> x \<le> b $ i\<close> by simp
  qed
  then show False using * by auto
qed

lemma soundness_mat_x_eq_vec:
  assumes "dim_row A\<^sup>T = dim_vec c"
  assumes "simplex (x_mat_eq_vec c A\<^sup>T) = Sat X"
  shows  "\<exists>x. [x \<^sub>v* A]=c"
proof 
  define x where x: "x = fst (split_n_m_x (dim_col A\<^sup>T) (dim_row A\<^sup>T) X)"
  have "dim_vec x = dim_col A\<^sup>T"
    unfolding split_i_j_x_def using split_vec_dims(1)[of "(dim_col A\<^sup>T)" _ X x] fst_conv[of x]
    by (simp add: split_i_j_x_def x)
  have "\<forall>i < dim_vec c. (A\<^sup>T *\<^sub>v x)$i = c$i"
  proof (standard, standard)
    fix i
    assume a: "i < dim_vec c"
    have *: "\<langle>X\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (x_mat_eq_vec c A\<^sup>T)"
      using assms(2) simplex(3) by blast
    then have "row A\<^sup>T i \<bullet> x = c$i"
      using x_mat_eq_vec_sol[of c "A\<^sup>T" "\<langle>X\<rangle>" i, OF * a] eval_lpoly_eq_dot_prod_split1 fstI       
      by (metis a assms(1) index_row(2) matrix_to_lpolies_vec_of_row split_i_j_x_def x)
    then show "(A\<^sup>T *\<^sub>v x) $ i = c $ i"
      unfolding mult_mat_vec_def using a assms(1) by auto
  qed
  then show "[x \<^sub>v* A]=c"
    using mat_times_vec_eqI[of A x c, OF \<open>dim_vec x = dim_col A\<^sup>T\<close>[symmetric] assms(1)] by auto
qed

lemma completeness_mat_x_eq_vec:
  assumes "\<exists>x. [x \<^sub>v* A]=c"
  shows "\<exists>X. simplex (x_mat_eq_vec c A\<^sup>T) = Sat X"
proof (rule ccontr)
  assume 1: "\<nexists>X. simplex (x_mat_eq_vec c A\<^sup>T) = Inr X"
  then have *: "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (x_mat_eq_vec c A\<^sup>T)"
    using simplex(1)[of "x_mat_eq_vec c A\<^sup>T"] using sum.exhaust_sel 1 by blast
  then have "dim_vec c = dim_col A" using assms
    by (metis index_transpose_mat(2) vec_times_mat_eqD(3))
  obtain x where " [x \<^sub>v* A]=c" using assms by auto
  then have "dim_vec x = dim_col A\<^sup>T" using assms
    by (metis \<open>[x \<^sub>v* A]=c\<close> vec_times_mat_eq_def)
  define v where v: "v = (\<lambda>i. (if i < dim_vec x then x$i else 0))"
  have v_d: "\<forall>i < dim_vec x. x$i = v i"
    by (simp add: v)
  have "v \<Turnstile>\<^sub>c\<^sub>s set (x_mat_eq_vec c A\<^sup>T)"
  proof 
    fix a
    assume "a \<in> set (x_mat_eq_vec c A\<^sup>T)"
    then obtain i where i: "a = EQ (matrix_to_lpolies A\<^sup>T!i) (c$i)" "i < dim_vec c"
      by (metis (no_types, lifting) add_cancel_right_left diff_zero in_set_conv_nth length_map length_upt nth_map_upt x_mat_eq_vec.simps)
    let ?p = "matrix_to_lpolies A\<^sup>T!i"
    have 2: "?p\<lbrace> v \<rbrace> = (row A\<^sup>T i) \<bullet> x"
      using matrix_to_lpolies_lambda_valuate_scalarP[of i "A\<^sup>T" x] v
      by (metis \<open>dim_vec c = dim_col A\<close> \<open>dim_vec x = dim_col A\<^sup>T\<close> i(2) index_transpose_mat(2))
    also have "... = c$i"
      by (metis \<open>[x \<^sub>v* A]=c\<close> \<open>dim_vec c = dim_col A\<close> i(2) index_mult_mat_vec index_transpose_mat(2) vec_times_mat_eqD(1))
    finally show "v \<Turnstile>\<^sub>c a"
      using i(1) satisfies_constraint.simps(5)[of v "(matrix_to_lpolies A\<^sup>T ! i)" "(c $ i)"] by simp
  qed
  then show False
    using "*" by blast
qed

lemma soundness_mat_leqb_eqc1:
  assumes "dim_row A = dim_vec b"
  assumes "simplex (mat_leqb_eqc A b c) = Sat X"
  shows "\<exists>x. [A *\<^sub>v x]\<le>b"
proof
  define x where x: "x = fst (split_n_m_x (dim_col A) (dim_row A) X)"
  have *: "dim_vec x = dim_col A" by (simp add: split_i_j_x_def x)
  have "\<forall>i<dim_vec b. (A *\<^sub>v x) $ i \<le> b $ i"
  proof (standard, standard)
    fix i
    assume "i < dim_vec b"
    have "row A i \<bullet> x \<le> b$i"
      using mat_x_leq_vec_sol[of A b X i]
      by (metis \<open>i < dim_vec b\<close> assms(1) assms(2) fst_conv split_i_j_x_def x
          index_mult_mat_vec mat_leqb_eqc_split_simplex_correct1 mat_times_vec_leqD(3))
    then show "(A *\<^sub>v x) $ i \<le> b $ i"
      by (simp add: \<open>i < dim_vec b\<close> assms(1))
  qed
  then show "[A *\<^sub>v x]\<le>b"
    using mat_times_vec_leqI[of A b x, OF assms(1) *[symmetric]] by auto
qed

lemma soundness_mat_leqb_eqc2:
  assumes "dim_row A\<^sup>T = dim_vec c"
  assumes "dim_col A\<^sup>T = dim_vec b"
  assumes "simplex (mat_leqb_eqc A b c) = Sat X"
  shows "\<exists>y. [y \<^sub>v* A]=c"
proof (standard, intro mat_times_vec_eqI)
  define y where x: "y = snd (split_n_m_x (dim_col A) (dim_row A) X)"
  have *: "dim_vec y = dim_row A" by (simp add: split_i_j_x_def x)
  show "dim_col A\<^sup>T = dim_vec y" by (simp add: "*")
  show "dim_row A\<^sup>T = dim_vec c" using assms(1) by blast
  show "\<And>i. i < dim_vec c \<Longrightarrow> (A\<^sup>T *\<^sub>v y) $ i = c $ i"
  proof -
    fix i
    assume a: "i < dim_vec c"
    have "[y \<^sub>v* A]=c"
      using mat_leqb_eqc_split_correct2[of c A b _ _ y, OF assms(1)[symmetric] assms(2)[symmetric]]
      by (metis Matrix.transpose_transpose assms(3) index_transpose_mat(2) 
          simplex(3) snd_conv split_i_j_x_def x)
    then show "(A\<^sup>T *\<^sub>v y) $ i = c $ i"
      by (metis a vec_times_mat_eq_def)
  qed
qed

lemma completeness_mat_leqb_eqc:  
  assumes "\<exists>x. [A *\<^sub>v x]\<le>b" 
    and "\<exists>y. [y \<^sub>v* A]=c"
  shows "\<exists>X. simplex (mat_leqb_eqc A b c) = Sat X"
proof (rule ccontr)
  assume 1: "\<nexists>X. simplex (mat_leqb_eqc A b c) = Sat X"
  have *: "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
    using simplex(1)[of "mat_leqb_eqc A b c"] using "1" sum.exhaust_sel by blast
  then have "dim_vec b = dim_row A" 
    using assms mat_times_vec_leqD(1)[of A _ b] by presburger
  then obtain x y where x: "[A *\<^sub>v x]\<le>b" "[y \<^sub>v* A]=c"
    using assms by blast
  have x_A: "dim_vec x = dim_col A"
    using x by auto
  have yr: "dim_vec y = dim_row A"
    using vec_times_mat_eq_def x(2) by force
  define v where v: "v = (\<lambda>i. (if i < dim_vec (x@\<^sub>vy) then (x@\<^sub>vy)$i else 0))"
  have v_d: "\<forall>i < dim_vec (x@\<^sub>vy). (x@\<^sub>vy)$i = v i"
    by (simp add: v)
  have i_in: "\<forall>i \<in> {0..< dim_vec y}. y$i = v (i+dim_vec x)"
    by (simp add: v)
  have "v \<Turnstile>\<^sub>c\<^sub>s set (mat_leqb_eqc A b c)"
  proof
    fix e
    assume asm: "e \<in> set (mat_leqb_eqc A b c)"
    define lst where lst: "lst = matrix_to_lpolies (two_block_non_interfering A A\<^sup>T)"
    let ?L = "[LEQ (lst!i) (b$i) . i <- [0..<dim_vec b]] @
              [EQ  (lst!i) ((b@\<^sub>vc)$i) . i <- [dim_vec b ..< dim_vec (b@\<^sub>vc)]]"
    have L: "mat_leqb_eqc A b c = ?L"
      by (metis (full_types) lst mat_leqb_eqc.simps)
    then obtain i where i: "e = ?L!i" "i \<in>{0..<length ?L}"
      using asm by (metis atLeastLessThan_iff in_set_conv_nth not_le not_less0)
    have ldimbc: "length ?L = dim_vec (b@\<^sub>vc)"
      using i(2) by auto
    consider (leqb) "i \<in> {0..<dim_vec b}" | (eqc) "i \<in> {dim_vec b..<length ?L}"
      using i(2) leI by auto
    then show "v \<Turnstile>\<^sub>c e"
    proof (cases)
      case leqb
      have il: "i < dim_vec b"
        using atLeastLessThan_iff leqb by blast
      have iA: "i < dim_row A"
        using \<open>dim_vec b = dim_row A\<close> \<open>i < dim_vec b\<close> by linarith
      then have *: "e = LEQ (lst!i) (b$i)"
        by (simp add: i(1) nth_append il)
      then have "... = LEQ ((matrix_to_lpolies A)!i) (b$i)"
        using mat_leqb_eqc_for_LEQ[of i b A c, OF il \<open>i < dim_row A\<close>] L i(1) by simp
      then have eqmp: "lst!i = ((matrix_to_lpolies A)!i)"
        by blast
      have sset: "vars (lst!i) \<subseteq> {0..<dim_vec x}" using matrix_to_lpolies_vec_of_row
        by (metis \<open>i < dim_row A\<close> eqmp index_row(2)  
            vars_subset_dim_vec_to_lpoly_dim x_A)
      have **: "((lst!i) \<lbrace> v \<rbrace>) = ((vec_to_lpoly (row A i)) \<lbrace> v \<rbrace>)"
        by (simp add: \<open>i < dim_row A\<close> eqmp)
      also have "... = (\<Sum>j\<in>vars(lst!i). Abstract_Linear_Poly.coeff (lst!i) j * v j)"
        using ** eval_poly_with_sum by auto
      also have "... = (\<Sum>j\<in>{0..<dim_vec x}. Abstract_Linear_Poly.coeff (lst!i) j * v j)"
        using sset eval_poly_with_sum_superset[of "{0..<dim_vec x}" "lst!i" v, 
            OF finite_atLeastLessThan sset] "**" using calculation by linarith
      also have "... = (\<Sum>j\<in>{0..<dim_vec x}. Abstract_Linear_Poly.coeff (lst!i) j * x$j)"
        using v by (auto split: if_split)
      also have "... = (\<Sum>j\<in>{0..<dim_vec x}. (row A i)$j * x$j)"
        using matrix_to_lpolies_vec_of_row[of i A, OF iA] 
          vec_to_lin_poly_coeff_access[of _ "row A i"] index_row(2)[of A i] 
          atLeastLessThan_iff by (metis (no_types, lifting) eqmp sum.cong x_A)
      also have  "... = row A i \<bullet> x" unfolding scalar_prod_def by (simp)
      also have "... \<le> b$i"
        by (metis \<open>i < dim_vec b\<close> index_mult_mat_vec mat_times_vec_leq_def x(1))
      finally show ?thesis 
        by (simp add: "*")
    next
      case eqc
      have igeq: "i \<ge> dim_vec b"
        using atLeastLessThan_iff eqc by blast
      have *: "i < length ?L"
        using atLeastLessThan_iff eqc by blast
      have "e =?L!i"
        using L i(1) by presburger
      have "?L!i \<in> set [EQ  (lst!i) ((b@\<^sub>vc)$i). i <- [dim_vec b..< dim_vec (b@\<^sub>vc)]]"
        using in_second_append_list length_map
        by (metis (no_types, lifting) igeq *  length_upt minus_nat.diff_0)
      then have "?L!i = [EQ  (lst!i) ((b@\<^sub>vc)$i). i <- [dim_vec b..< dim_vec (b@\<^sub>vc)]]!(i-dim_vec b)"
        by (metis (no_types, lifting) \<open>dim_vec b \<le> i\<close> diff_zero leD 
            length_map length_upt nth_append)
      then have "?L!i = EQ (lst!i) ((b@\<^sub>vc)$i)"
        using add_diff_inverse_nat diff_less_mono
        by (metis (no_types, lifting) \<open>dim_vec b \<le> i\<close> * ldimbc  leD nth_map_upt)
      then have e: "e = EQ (lst!i) ((b@\<^sub>vc)$i)"
        using i(1) by blast
      with mat_leqb_eqc_for_EQ[of b i c A, OF igeq] 
      have lsta: "(lst!i) = (vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T (i - dim_vec b)))"
        by (metis (no_types, lifting) \<open>dim_vec b = dim_row A\<close> * ldimbc assms(2) igeq 
            index_append_vec(2) lst matrix_to_lpolies_vec_of_row vec_times_mat_eq_def
            two_block_non_interfering_dims(1) two_block_non_interfering_row_comp2 )
      let ?p = "(vec_to_lpoly (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T (i - dim_vec b)))"
      have "dim_poly ?p \<le> dim_col A + dim_row A" 
        using dim_poly_of_append_vec[of "0\<^sub>v (dim_col A)" "row A\<^sup>T (i - dim_vec b)"]
          index_zero_vec(2)[of "dim_col A"]
        by (metis \<open>dim_vec (0\<^sub>v (dim_col A)) = dim_col A\<close> index_row(2) index_transpose_mat(3))
      have "\<forall>i < dim_col A. Abstract_Linear_Poly.coeff ?p i = 0"
        using vec_coeff_append1[of _ "0\<^sub>v (dim_col A)" "row A\<^sup>T (i - dim_vec b)"]
        by (metis atLeastLessThan_iff index_zero_vec(1) index_zero_vec(2) zero_le)
      then have "dim_vec (0\<^sub>v (dim_col A) @\<^sub>v row A\<^sup>T (i - dim_vec b)) = dim_col A + dim_row A"
        by (metis index_append_vec(2) index_row(2) index_transpose_mat(3) index_zero_vec(2))
      then have allcr: "\<forall>j\<in>{0..<dim_row A}. Abstract_Linear_Poly.coeff ?p (j+dim_col A) = (row A\<^sup>T (i - dim_vec b))$j" 
        by (metis add_diff_cancel_right' atLeastLessThan_iff diff_add_inverse index_zero_vec(2) 
            le_add_same_cancel2 less_diff_conv vec_coeff_append2)
      have vs: "vars ?p \<subseteq> {dim_col A..<dim_col A + dim_row A}"
        using vars_vec_append_subset by (metis index_row(2) index_transpose_mat(3))
      have "?p \<lbrace> v \<rbrace> = (\<Sum>j\<in>vars ?p. Abstract_Linear_Poly.coeff ?p j * v j)"
        using eval_poly_with_sum by blast
      also have "... = (\<Sum>j\<in>{dim_col A..<dim_col A + dim_row A}. Abstract_Linear_Poly.coeff ?p j * v j)"     
        by (metis (mono_tags, lifting) DiffD2 vs coeff_zero finite_atLeastLessThan
            mult_not_zero sum.mono_neutral_left)
      also have "... = (\<Sum>j\<in>{0..<dim_row A}. Abstract_Linear_Poly.coeff ?p (j+dim_col A) * v (j+dim_col A))"
        using sum.shift_bounds_nat_ivl[of "\<lambda>j. Abstract_Linear_Poly.coeff ?p j * v j" 0 "dim_col A" "dim_row A"]
        by (metis (no_types, lifting) add.commute add_cancel_left_left)
      also have "... = (\<Sum>j\<in>{0..<dim_row A}. Abstract_Linear_Poly.coeff ?p (j+dim_col A) * y$j)"
        using v i_in yr by (metis (no_types, lifting) sum.cong x_A) 
      also have "... = (\<Sum>j\<in>{0..<dim_row A}. (row A\<^sup>T (i - dim_vec b))$j * y$j)"
        using allcr by (metis (no_types, lifting) sum.cong)
      also have "... = (row A\<^sup>T (i - dim_vec b)) \<bullet> y"
        by (metis \<open>dim_vec y = dim_row A\<close> scalar_prod_def)
      also have "... = (b@\<^sub>vc)$i"
        using vec_times_mat_eqD[OF x(2)] * igeq by auto
      finally show ?thesis
        using e lsta satisfies_constraint.simps(5)[of _ "(lst ! i)" "((b @\<^sub>v c) $ i)"] by simp
    qed
  qed
  then show False using * by blast
qed

lemma sound_and_compltete_mat_leqb_eqc [iff]:  
  assumes "dim_row A\<^sup>T = dim_vec c"
  assumes "dim_col A\<^sup>T = dim_vec b"
  shows "(\<exists>x. [A *\<^sub>v x]\<le>b) \<and> (\<exists>y. [y \<^sub>v* A]=c) \<longleftrightarrow> (\<exists>X. simplex (mat_leqb_eqc A b c) = Sat X)"
  by (metis assms(1) assms(2) completeness_mat_leqb_eqc index_transpose_mat(3) 
      soundness_mat_leqb_eqc1 soundness_mat_leqb_eqc2)



section \<open> Translate Inequalities to Matrix Form \<close>

(* We (obviously) cannot use strict inequalities hence we use the option type *)

fun nonstrict_constr where 
  "nonstrict_constr (LEQ p r) = True" |
  "nonstrict_constr (GEQ p r) = True" |
  "nonstrict_constr (EQ p r) = True" |
  "nonstrict_constr (LEQPP p q) = True" |
  "nonstrict_constr (GEQPP p q) = True" |
  "nonstrict_constr (EQPP p q) = True" |
  "nonstrict_constr _ = False"

abbreviation "nonstrict_constrs cs \<equiv> (\<forall>a \<in> set cs. nonstrict_constr a)"

fun transf_constraint where
  "transf_constraint (LEQ p r) = [LEQ p r]" |
  "transf_constraint (GEQ p r) = [LEQ (-p) (-r)]" |
  "transf_constraint (EQ p r) = [LEQ p r, LEQ (-p) (-r)]" |
  "transf_constraint (LEQPP p q) = [LEQ (p - q) 0]" |
  "transf_constraint (GEQPP p q) = [LEQ (-(p - q)) 0]" |
  "transf_constraint (EQPP p q) = [LEQ (p - q) 0, LEQ (-(p - q)) 0]" |
  "transf_constraint _ = []"


fun transf_constraints where
"transf_constraints [] = []" |
"transf_constraints (x#xs) = transf_constraint x @ (transf_constraints xs)"


lemma trans_constraint_creats_LEQ_only:
  assumes "transf_constraint x \<noteq> []"
  shows "(\<forall>x \<in> set (transf_constraint x). \<exists>a b. x = LEQ a b)"
  using assms by (cases x, auto+)

lemma trans_constraints_creats_LEQ_only:
  assumes "transf_constraints xs \<noteq> []"
  assumes "x \<in> set (transf_constraints xs)"
  shows "\<exists>p r. LEQ p r = x"
  using assms apply(induction xs) 
  using trans_constraint_creats_LEQ_only apply(auto) 
    apply fastforce
   apply (metis in_set_simps(3) trans_constraint_creats_LEQ_only) 
  by fastforce

lemma non_strict_constr_no_LT: 
  assumes "nonstrict_constrs cs"
  shows "\<forall>x \<in> set cs. \<not>(\<exists>a b. LT a b = x)"
  using assms nonstrict_constr.simps(7) by blast

lemma non_strict_constr_no_GT: 
  assumes "nonstrict_constrs cs"
  shows "\<forall>x \<in> set cs. \<not>(\<exists>a b. GT a b = x)"
  using assms nonstrict_constr.simps(8) by blast

lemma non_strict_constr_no_LTPP: 
  assumes "nonstrict_constrs cs"
  shows "\<forall>x \<in> set cs. \<not>(\<exists>a b. LTPP a b = x)"
  using assms nonstrict_constr.simps(9) by blast

lemma non_strict_constr_no_GTPP: 
  assumes "nonstrict_constrs cs"
  shows "\<forall>x \<in> set cs. \<not>(\<exists>a b. GTPP a b = x)"
  using assms nonstrict_constr.simps(10) by blast

lemma non_strict_consts_cond:
  assumes "\<And>x. x \<in> set cs \<Longrightarrow> \<not>(\<exists>a b. LT a b = x)"
  assumes "\<And>x. x \<in> set cs \<Longrightarrow> \<not>(\<exists>a b. GT a b = x)"
  assumes "\<And>x. x \<in> set cs \<Longrightarrow> \<not>(\<exists>a b. LTPP a b = x)"
  assumes "\<And>x. x \<in> set cs \<Longrightarrow> \<not>(\<exists>a b. GTPP a b = x)"
  shows "nonstrict_constrs cs"
  by (metis assms(1) assms(2) assms(3) assms(4) nonstrict_constr.elims(3))

lemma sat_constr_sat_transf_constrs:
  assumes "v \<Turnstile>\<^sub>c cs" 
  shows "v \<Turnstile>\<^sub>c\<^sub>s set (transf_constraint cs)"
  using assms by (cases cs) (simp add: valuate_uminus valuate_minus)+

lemma sat_constrs_sat_transf_constrs:
  assumes "v \<Turnstile>\<^sub>c\<^sub>s set cs" 
  shows "v \<Turnstile>\<^sub>c\<^sub>s set (transf_constraints cs)"
  using assms by(induction cs, simp) (metis UnE list.set_intros(1) 
      list.set_intros(2) sat_constr_sat_transf_constrs set_append transf_constraints.simps(2))

lemma sat_transf_constrs_sat_constr: 
  assumes "nonstrict_constr cs"
  assumes "v \<Turnstile>\<^sub>c\<^sub>s set (transf_constraint cs)"
  shows "v \<Turnstile>\<^sub>c cs"
  using assms by (cases cs) (simp add: valuate_uminus valuate_minus)+

lemma sat_transf_constrs_sat_constrs:
  assumes "nonstrict_constrs cs"
  assumes "v \<Turnstile>\<^sub>c\<^sub>s set (transf_constraints cs)"
  shows "v \<Turnstile>\<^sub>c\<^sub>s set cs"
  using assms by (induction cs, auto) (simp add: sat_transf_constrs_sat_constr)

end