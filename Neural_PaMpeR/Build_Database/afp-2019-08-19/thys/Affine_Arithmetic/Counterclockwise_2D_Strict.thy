section \<open>CCW for Nonaligned Points in the Plane\<close>
theory Counterclockwise_2D_Strict
  imports
    Counterclockwise_Vector
    Affine_Arithmetic_Auxiliarities
begin
text \<open>\label{sec:counterclockwise2d}\<close>

subsection \<open>Determinant\<close>

type_synonym point = "real*real"

fun det3::"point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> real" where "det3 (xp, yp) (xq, yq) (xr, yr) =
  xp * yq + yp * xr + xq * yr - yq * xr - yp * xq - xp * yr"

lemma det3_def':
  "det3 p q r = fst p * snd q + snd p * fst r + fst q * snd r -
    snd q * fst r - snd p * fst q - fst p * snd r"
  by (cases p q r rule: prod.exhaust[case_product prod.exhaust[case_product prod.exhaust]]) auto

lemma det3_eq_det: "det3 (xa, ya) (xb, yb) (xc, yc) =
  det (vector [vector [xa, ya, 1], vector [xb, yb, 1], vector [xc, yc, 1]]::real^3^3)"
  unfolding Determinants.det_def UNIV_3
  by (auto simp: sum_over_permutations_insert
    vector_3 sign_swap_id permutation_swap_id sign_compose)

declare det3.simps[simp del]

lemma det3_self23[simp]: "det3 a b b = 0"
  and det3_self12[simp]: "det3 b b a = 0"
  by (auto simp: det3_def')

lemma
  coll_ex_scaling:
  assumes "b \<noteq> c"
  assumes d: "det3 a b c = 0"
  shows "\<exists>r. a = b + r *\<^sub>R (c - b)"
proof -
  from assms have "fst b \<noteq> fst c \<or> snd b \<noteq> snd c" by (auto simp: prod_eq_iff)
  thus ?thesis
  proof
    assume neq: "fst b \<noteq> fst c"
    with d have "snd a = ((fst a - fst b) * snd c + (fst c - fst a) * snd b) / (fst c - fst b)"
      by (auto simp: det3_def' field_simps)
    hence "snd a = ((fst a - fst b)/ (fst c - fst b)) * snd c +
      ((fst c - fst a)/ (fst c - fst b)) * snd b"
      by (simp add: add_divide_distrib)
    hence "snd a = snd b + (fst a - fst b) * snd c / (fst c - fst b) +
      ((fst c - fst a) - (fst c - fst b)) * snd b / (fst c - fst b)"
      using neq
      by (simp add: field_simps)
    hence "snd a = snd b + ((fst a - fst b) * snd c + (- fst a + fst b) * snd b) / (fst c - fst b)"
      unfolding add_divide_distrib
      by (simp add: algebra_simps)
    also
    have "(fst a - fst b) * snd c + (- fst a + fst b) * snd b = (fst a - fst b) * (snd c - snd b)"
      by (simp add: algebra_simps)
    finally have "snd a = snd b + (fst a - fst b) / (fst c - fst b) * (snd c - snd b)"
      by simp
    moreover
    hence "fst a = fst b + (fst a - fst b) / (fst c - fst b) * (fst c - fst b)"
      using neq by simp
    ultimately have "a = b + ((fst a - fst b) / (fst c - fst b)) *\<^sub>R (c - b)"
      by (auto simp: prod_eq_iff)
    thus ?thesis by blast
  next
    assume neq: "snd b \<noteq> snd c"
    with d have "fst a = ((snd a - snd b) * fst c + (snd c - snd a) * fst b) / (snd c - snd b)"
      by (auto simp: det3_def' field_simps)
    hence "fst a = ((snd a - snd b)/ (snd c - snd b)) * fst c +
      ((snd c - snd a)/ (snd c - snd b)) * fst b"
      by (simp add: add_divide_distrib)
    hence "fst a = fst b + (snd a - snd b) * fst c / (snd c - snd b) +
      ((snd c - snd a) - (snd c - snd b)) * fst b / (snd c - snd b)"
      using neq
      by (simp add: field_simps)
    hence "fst a = fst b + ((snd a - snd b) * fst c + (- snd a + snd b) * fst b) / (snd c - snd b)"
      unfolding add_divide_distrib
      by (simp add: algebra_simps)
    also
    have "(snd a - snd b) * fst c + (- snd a + snd b) * fst b = (snd a - snd b) * (fst c - fst b)"
      by (simp add: algebra_simps)
    finally have "fst a = fst b + (snd a - snd b) / (snd c - snd b) * (fst c - fst b)"
      by simp
    moreover
    hence "snd a = snd b + (snd a - snd b) / (snd c - snd b) * (snd c - snd b)"
      using neq by simp
    ultimately have "a = b + ((snd a - snd b) / (snd c - snd b)) *\<^sub>R (c - b)"
      by (auto simp: prod_eq_iff)
    thus ?thesis by blast
  qed
qed

lemma cramer: "\<not>det3 s t q = 0 \<Longrightarrow>
  (det3 t p r) = ((det3 t q r) * (det3 s t p) + (det3 t p q) * (det3 s t r))/(det3 s t q)"
  by (auto simp: det3_def' field_simps)

lemma convex_comb_dets:
  assumes "det3 p q r > 0"
  shows "s = (det3 s q r / det3 p q r) *\<^sub>R p + (det3 p s r /  det3 p q r) *\<^sub>R q +
      (det3 p q s / det3 p q r) *\<^sub>R r"
    (is "?lhs = ?rhs")
proof -
  from assms have "det3 p q r *\<^sub>R ?lhs = det3 p q r *\<^sub>R ?rhs"
    by (simp add: field_simps prod_eq_iff scaleR_add_right) (simp add: algebra_simps det3_def')
  thus ?thesis using assms by simp
qed

lemma four_points_aligned:
  assumes c: "det3 t p q = 0" "det3 t q r = 0"
  assumes distinct: "distinct5 t s p q r"
  shows "det3 t r p = 0" "det3 p q r = 0"
proof -
  from distinct have d: "p \<noteq> q" "q \<noteq> r" by (auto)
  from coll_ex_scaling[OF d(1) c(1)] obtain s1 where s1: "t = p + s1 *\<^sub>R (q - p)" by auto
  from coll_ex_scaling[OF d(2) c(2)] obtain s2 where s2: "t = q + s2 *\<^sub>R (r - q)" by auto
  from distinct s1 have ne: "1 - s1 \<noteq> 0" by auto
  from s1 s2 have "(1 - s1) *\<^sub>R p = (1 - s1 - s2) *\<^sub>R q + s2 *\<^sub>R r"
    by (simp add: algebra_simps)
  hence "(1 - s1) *\<^sub>R p /\<^sub>R (1 - s1)= ((1 - s1 - s2) *\<^sub>R q + s2 *\<^sub>R r) /\<^sub>R (1 - s1)"
    by simp
  with ne have p: "p = ((1 - s1 - s2) / (1 - s1)) *\<^sub>R q + (s2 / (1 - s1)) *\<^sub>R r"
    using ne
    by (simp add: prod_eq_iff inverse_eq_divide add_divide_distrib)
  define k1 where "k1 = (1 - s1 - s2) / (1 - s1)"
  define k2 where "k2 = s2 / (1 - s1)"
  have "det3 t r p = det3 0 (k1 *\<^sub>R q + (k2 - 1) *\<^sub>R r)
    (k1 *\<^sub>R q + (k2 - 1) *\<^sub>R r + (- s1 * (k1 - 1)) *\<^sub>R q - (s1 * k2) *\<^sub>R r)"
    unfolding s1 p k1_def[symmetric] k2_def[symmetric]
    by (simp add: algebra_simps det3_def')
  also have "- s1 * (k1 - 1) = s1 * k2"
    using ne by (auto simp: k1_def field_simps k2_def)
  also
  have "1 - k1 = k2"
    using ne
    by (auto simp: k2_def k1_def field_simps)
  have k21: "k2 - 1 = -k1"
    using ne
    by (auto simp: k2_def k1_def field_simps)
  finally have "det3 t r p = det3 0 (k1 *\<^sub>R (q - r)) ((k1 + (s1 * k2)) *\<^sub>R (q - r))"
    by (auto simp: algebra_simps)
  also have "\<dots> = 0"
    by (simp add: algebra_simps det3_def')
  finally show "det3 t r p = 0" .
  have "det3 p q r = det3 (k1 *\<^sub>R q + k2 *\<^sub>R r) q r"
    unfolding p k1_def[symmetric] k2_def[symmetric] ..
  also have "\<dots> = det3 0 (r - q) (k1 *\<^sub>R q + (-k1) *\<^sub>R r)"
    unfolding k21[symmetric]
    by (auto simp: algebra_simps det3_def')
  also have "\<dots> = det3 0 (r - q) (-k1 *\<^sub>R (r - q))"
    by (auto simp: det3_def' algebra_simps)
  also have "\<dots> = 0"
    by (auto simp: det3_def')
  finally show "det3 p q r = 0" .
qed

lemma det_identity:
  "det3 t p q * det3 t s r + det3 t q r * det3 t s p + det3 t r p * det3 t s q = 0"
  by (auto simp: det3_def' algebra_simps)

lemma det3_eq_zeroI:
  assumes "p = q + x *\<^sub>R (t - q)"
  shows "det3 q t p = 0"
  unfolding assms
  by (auto simp: det3_def' algebra_simps)

lemma det3_rotate: "det3 a b c = det3 c a b"
  by (auto simp: det3_def')

lemma det3_switch: "det3 a b c = - det3 a c b"
  by (auto simp: det3_def')

lemma det3_switch': "det3 a b c = - det3 b a c"
  by (auto simp: det3_def')

lemma det3_pos_transitive_coll:
  "det3 t s p > 0 \<Longrightarrow> det3 t s r \<ge> 0 \<Longrightarrow> det3 t p q \<ge> 0 \<Longrightarrow>
  det3 t q r > 0 \<Longrightarrow> det3 t s q = 0 \<Longrightarrow> det3 t p r > 0"
  using det_identity[of t p q s r]
  by (metis add.commute add_less_same_cancel1 det3_switch det3_switch' less_eq_real_def
    less_not_sym monoid_add_class.add.left_neutral mult_pos_pos mult_zero_left mult_zero_right)

lemma det3_pos_transitive:
  "det3 t s p > 0 \<Longrightarrow> det3 t s q \<ge> 0 \<Longrightarrow> det3 t s r \<ge> 0 \<Longrightarrow> det3 t p q \<ge> 0 \<Longrightarrow>
  det3 t q r > 0 \<Longrightarrow> det3 t p r > 0"
  apply (cases "det3 t s q \<noteq> 0")
   using cramer[of q t s p r]
   apply (force simp: det3_rotate[of q t p] det3_rotate[of p q t] det3_switch[of t p s]
     det3_switch'[of q t r] det3_rotate[of q t s] det3_rotate[of s q t]
     intro!: divide_pos_pos add_nonneg_pos)
  apply (metis det3_pos_transitive_coll)
  done

lemma det3_zero_translate_plus[simp]: "det3 (a + x) (b + x) (c + x) = 0 \<longleftrightarrow> det3 a b c = 0"
  by (auto simp: algebra_simps det3_def')

lemma det3_zero_translate_plus'[simp]: "det3 (a) (a + b) (a + c) = 0 \<longleftrightarrow> det3 0 b c = 0"
  by (auto simp: algebra_simps det3_def')

lemma
  det30_zero_scaleR1:
  "0 < e \<Longrightarrow> det3 0 xr P = 0 \<Longrightarrow> det3 0 (e *\<^sub>R xr) P = 0"
  by (auto simp: zero_prod_def algebra_simps det3_def')

lemma det3_same[simp]: "det3 a x x = 0"
  by (auto simp: det3_def')

lemma
  det30_zero_scaleR2:
  "0 < e \<Longrightarrow> det3 0 P xr = 0 \<Longrightarrow> det3 0 P (e *\<^sub>R xr) = 0"
  by (auto simp: zero_prod_def algebra_simps det3_def')

lemma det3_eq_zero: "e \<noteq> 0 \<Longrightarrow> det3 0 xr (e *\<^sub>R Q) = 0 \<longleftrightarrow> det3 0 xr Q = 0"
  by (auto simp: det3_def')

lemma det30_plus_scaled3[simp]: "det3 0 a (b + x *\<^sub>R a) = 0 \<longleftrightarrow> det3 0 a b = 0"
  by (auto simp: det3_def' algebra_simps)

lemma det30_plus_scaled2[simp]:
  shows "det3 0 (a + x *\<^sub>R a) b = 0 \<longleftrightarrow> (if x = -1 then True else det3 0 a b = 0)"
    (is "?lhs = ?rhs")
proof
  assume "det3 0 (a + x *\<^sub>R a) b = 0"
  hence "fst a * snd b * (1 + x) = fst b * snd a * (1 + x)"
    by (simp add: algebra_simps det3_def')
  thus ?rhs
    by (auto simp add: det3_def')
qed (auto simp: det3_def' algebra_simps split: if_split_asm)

lemma det30_uminus2[simp]: "det3 0 (-a) (b) = 0 \<longleftrightarrow> det3 0 a b = 0"
  and det30_uminus3[simp]: "det3 0 a (-b) = 0 \<longleftrightarrow> det3 0 a b = 0"
  by (auto simp: det3_def' algebra_simps)

lemma det30_minus_scaled3[simp]: "det3 0 a (b - x *\<^sub>R a) = 0 \<longleftrightarrow> det3 0 a b = 0"
  using det30_plus_scaled3[of a b "-x"] by simp

lemma det30_scaled_minus3[simp]: "det3 0 a (e *\<^sub>R a - b) = 0 \<longleftrightarrow> det3 0 a b = 0"
  using det30_plus_scaled3[of a "-b" e]
  by (simp add: algebra_simps)

lemma det30_minus_scaled2[simp]:
  "det3 0 (a - x *\<^sub>R a) b = 0 \<longleftrightarrow> (if x = 1 then True else det3 0 a b = 0)"
  using det30_plus_scaled2[of a  "-x" b] by simp

lemma det3_nonneg_scaleR1:
  "0 < e \<Longrightarrow> det3 0 xr P \<ge> 0 \<Longrightarrow> det3 0 (e*\<^sub>Rxr) P \<ge> 0"
  by (auto simp add: det3_def' algebra_simps)

lemma det3_nonneg_scaleR1_eq:
  "0 < e \<Longrightarrow> det3 0 (e*\<^sub>Rxr) P \<ge> 0 \<longleftrightarrow> det3 0 xr P \<ge> 0"
  by (auto simp add: det3_def' algebra_simps)

lemma det3_translate_origin: "NO_MATCH 0 p \<Longrightarrow> det3 p q r = det3 0 (q - p) (r - p)"
  by (auto simp: det3_def' algebra_simps)

lemma det3_nonneg_scaleR_segment2:
  assumes "det3 x y z \<ge> 0"
  assumes "a > 0"
  shows "det3 x ((1 - a) *\<^sub>R x + a *\<^sub>R y) z \<ge> 0"
proof -
  from assms have "0 \<le> det3 0 (a *\<^sub>R (y - x)) (z - x)"
    by (intro det3_nonneg_scaleR1) (simp_all add: det3_translate_origin)
  thus ?thesis
    by (simp add: algebra_simps det3_translate_origin)
qed

lemma det3_nonneg_scaleR_segment1:
  assumes "det3 x y z \<ge> 0"
  assumes "0 \<le> a" "a < 1"
  shows "det3 ((1 - a) *\<^sub>R x + a *\<^sub>R y) y z \<ge> 0"
proof -
  from assms have "det3 0 ((1 - a) *\<^sub>R (y - x)) (z - x + (- a) *\<^sub>R (y - x)) \<ge> 0"
    by (subst det3_nonneg_scaleR1_eq) (auto simp add: det3_def' algebra_simps)
  thus ?thesis
    by (auto simp: algebra_simps det3_translate_origin)
qed


subsection \<open>Strict CCW Predicate\<close>

definition "ccw' p q r \<longleftrightarrow> 0 < det3 p q r"

interpretation ccw': ccw_vector_space ccw'
  by unfold_locales (auto simp: ccw'_def det3_def' algebra_simps)

interpretation ccw': linorder_list0 "ccw' x" for x .

lemma ccw'_contra: "ccw' t r q \<Longrightarrow> ccw' t q r = False"
  by (auto simp: ccw'_def det3_def' algebra_simps)

lemma not_ccw'_eq: "\<not> ccw' t p s \<longleftrightarrow> ccw' t s p \<or> det3 t s p = 0"
  by (auto simp: ccw'_def det3_def' algebra_simps)

lemma neq_left_right_of: "ccw' a b c \<Longrightarrow> ccw' a c d \<Longrightarrow> b \<noteq> d"
  by (auto simp: ccw'_def det3_def' algebra_simps)

lemma ccw'_subst_collinear:
  assumes "det3 t r s = 0"
  assumes "s \<noteq> t"
  assumes "ccw' t r p"
  shows "ccw' t s p \<or> ccw' t p s"
proof cases
  assume "r \<noteq> s"
  from assms have "det3 r s t = 0"
    by (auto simp: algebra_simps det3_def')
  from coll_ex_scaling[OF assms(2) this]
  obtain x where s: "r = s + x *\<^sub>R (t - s)" by auto
  from assms(3)[simplified ccw'_def s]
  have "0 < det3 0 (s + x *\<^sub>R (t - s) - t) (p - t)"
    by (auto simp: algebra_simps det3_def')
  also have "s + x *\<^sub>R (t - s) - t = (1 - x) *\<^sub>R (s - t)"
    by (simp add: algebra_simps)
  finally have ccw': "ccw' 0 ((1 - x) *\<^sub>R (s - t)) (p - t)"
    by (simp add: ccw'_def)
  hence "x \<noteq> 1" by (auto simp add: det3_def' ccw'_def)
  {
    assume "x < 1"
    hence ?thesis using ccw'
      by (auto simp: not_ccw'_eq ccw'.translate_origin)
  } moreover {
    assume "x > 1"
    hence ?thesis using ccw'
      by (auto simp: not_ccw'_eq ccw'.translate_origin)
  } ultimately show ?thesis using \<open>x \<noteq> 1\<close> by arith
qed (insert assms, simp)

lemma ccw'_sorted_scaleR: "ccw'.sortedP 0 xs \<Longrightarrow> r > 0 \<Longrightarrow> ccw'.sortedP 0 (map ((*\<^sub>R) r) xs)"
  by (induct xs) (auto intro!: ccw'.sortedP.Cons  elim!: ccw'.sortedP_Cons simp del: scaleR_Pair)


subsection \<open>Collinearity\<close>

abbreviation "coll a b c \<equiv> det3 a b c = 0"

lemma coll_zero[intro, simp]: "coll 0 z 0"
  by (auto simp: det3_def')

lemma coll_zero1[intro, simp]: "coll 0 0 z"
  by (auto simp: det3_def')

lemma coll_self[intro, simp]: "coll 0 z z"
  by (auto simp: )

lemma ccw'_not_coll:
  "ccw' a b c \<Longrightarrow> \<not>coll a b c"
  "ccw' a b c \<Longrightarrow> \<not>coll a c b"
  "ccw' a b c \<Longrightarrow> \<not>coll b a c"
  "ccw' a b c \<Longrightarrow> \<not>coll b c a"
  "ccw' a b c \<Longrightarrow> \<not>coll c a b"
  "ccw' a b c \<Longrightarrow> \<not>coll c b a"
  by (auto simp: det3_def' ccw'_def algebra_simps)

lemma coll_add: "coll 0 x y \<Longrightarrow> coll 0 x z \<Longrightarrow> coll 0 x (y + z)"
  by (auto simp: det3_def' algebra_simps)

lemma coll_scaleR_left_eq[simp]: "coll 0 (r *\<^sub>R x) y \<longleftrightarrow> r = 0 \<or> coll 0 x y"
  by (auto simp: det3_def' algebra_simps)

lemma coll_scaleR_right_eq[simp]: "coll 0 y (r *\<^sub>R x) \<longleftrightarrow> r = 0 \<or> coll 0 y x"
  by (auto simp: det3_def' algebra_simps)

lemma coll_scaleR: "coll 0 x y \<Longrightarrow> coll 0 (r *\<^sub>R x) y"
  by (auto simp: det3_def' algebra_simps)

lemma coll_sum_list: "(\<And>y. y \<in> set ys \<Longrightarrow> coll 0 x y) \<Longrightarrow> coll 0 x (sum_list ys)"
  by (induct ys) (auto intro!: coll_add)

lemma scaleR_left_normalize:
  fixes a ::real and b c::"'a::real_vector"
  shows "a *\<^sub>R b = c \<longleftrightarrow> (if a = 0 then c = 0 else b = c /\<^sub>R a)"
  by (auto simp: field_simps)

lemma coll_scale_pair: "coll 0 (a, b) (c, d) \<Longrightarrow> (a, b) \<noteq> 0 \<Longrightarrow> (\<exists>x. (c, d) = x *\<^sub>R (a, b))"
  by (auto intro: exI[where x="c/a"] exI[where x="d/b"] simp: det3_def' field_simps prod_eq_iff)

lemma coll_scale: "coll 0 r q \<Longrightarrow> r \<noteq> 0 \<Longrightarrow> (\<exists>x. q = x *\<^sub>R r)"
  using coll_scale_pair[of "fst r" "snd r" "fst q" "snd q"]
  by simp

lemma coll_add_trans:
  assumes "coll 0 x (y + z)"
  assumes "coll 0 y z"
  assumes "x \<noteq> 0"
  assumes "y \<noteq> 0"
  assumes "z \<noteq> 0"
  assumes "y + z \<noteq> 0"
  shows "coll 0 x z"
proof (cases "snd z = 0")
  case True
  hence "snd y = 0"
    using assms
    by (cases z) (auto simp add: zero_prod_def det3_def')
  with True assms have "snd x = 0"
    by (cases y, cases z) (auto simp add: zero_prod_def det3_def')
  from \<open>snd x = 0\<close> \<open>snd y = 0\<close> \<open>snd z = 0\<close>
  show ?thesis
    by (auto simp add: zero_prod_def det3_def')
next
  case False
  note z = False
  hence "snd y \<noteq> 0"
    using assms
    by (cases y) (auto simp add: zero_prod_def det3_def')
  with False assms have "snd x \<noteq> 0"
    apply (cases x)
    apply (cases y)
    apply (cases z)
    apply (auto simp add: zero_prod_def det3_def')
    apply (metis mult.commute mult_eq_0_iff ring_class.ring_distribs(1))
    done
  with False assms \<open>snd y \<noteq> 0\<close> have yz: "snd (y + z) \<noteq> 0"
    by (cases x; cases y; cases z) (auto simp add: det3_def' zero_prod_def)
  from coll_scale[OF assms(1) assms(3)] coll_scale[OF assms(2) assms(4)]
  obtain r s where rs: "y + z = r *\<^sub>R x" "z = s *\<^sub>R y"
    by auto
  with z have "s \<noteq> 0"
    by (cases x; cases y; cases z) (auto simp: zero_prod_def)
  with rs z yz have "r \<noteq> 0"
    by (cases x; cases y; cases z) (auto simp: zero_prod_def)
  from \<open>s \<noteq> 0\<close> rs have "y = r *\<^sub>R x - z" "y = z /\<^sub>R s"
    by (auto simp: inverse_eq_divide algebra_simps)
  hence "r *\<^sub>R x - z = z /\<^sub>R s" by simp
  hence "r *\<^sub>R x = (1 + inverse s) *\<^sub>R z"
    by (auto simp: inverse_eq_divide algebra_simps)
  hence "x = (inverse r * (1 + inverse s)) *\<^sub>R z"
    using \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close>
    by (auto simp: field_simps scaleR_left_normalize)
  from this
  show ?thesis
    by (auto intro: coll_scaleR)
qed

lemma coll_commute: "coll 0 a b \<longleftrightarrow> coll 0 b a"
  by (metis det3_rotate det3_switch' diff_0 diff_self)

lemma coll_add_cancel: "coll 0 a (a + b) \<Longrightarrow> coll 0 a b"
  by (cases a, cases b) (auto simp: det3_def' algebra_simps)

lemma coll_trans:
  "coll 0 a b \<Longrightarrow> coll 0 a c \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coll 0 b c"
  by (metis coll_scale coll_scaleR)

lemma sum_list_posI:
  fixes xs::"'a::ordered_comm_monoid_add list"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> x > 0) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> sum_list xs > 0"
proof (induct xs)
  case (Cons x xs)
  thus ?case
    by (cases "xs = []") (auto intro!: add_pos_pos)
qed simp

lemma nonzero_fstI[intro, simp]: "fst x \<noteq> 0 \<Longrightarrow> x \<noteq> 0"
  and nonzero_sndI[intro, simp]: "snd x \<noteq> 0 \<Longrightarrow> x \<noteq> 0"
  by auto

lemma coll_sum_list_trans:
  "xs \<noteq> [] \<Longrightarrow> coll 0 a (sum_list xs) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> coll 0 x y) \<Longrightarrow>
    (\<And>x. x \<in> set xs \<Longrightarrow> coll 0 x (sum_list xs)) \<Longrightarrow>
    (\<And>x. x \<in> set xs \<Longrightarrow> snd x > 0) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coll 0 a y"
proof (induct xs rule: list_nonempty_induct)
  case (single x)
  from single(1) single(2)[of x] single(4)[of x] have "coll 0 x a" "coll 0 x y" "x \<noteq> 0"
    by (auto simp: coll_commute)
  thus ?case by (rule coll_trans)
next
  case (cons x xs)
  from cons(5)[of x] \<open>a \<noteq> 0\<close> cons(6)[of x]
  have *: "coll 0 x (sum_list xs)" "a \<noteq> 0" "x \<noteq> 0" by (force simp add: coll_add_cancel)+
  have "0 < snd (sum_list (x#xs))"
    unfolding snd_sum_list
    by (rule sum_list_posI) (auto intro!: add_pos_pos cons simp: snd_sum_list)
  hence "x + sum_list xs \<noteq> 0" by simp
  from coll_add_trans[OF cons(3)[simplified] * _ this]
  have cH: "coll 0 a (sum_list xs)"
    by (cases "sum_list xs = 0") auto
  from cons(4) have cy: "(\<And>x. x \<in> set xs \<Longrightarrow> coll 0 x y)" by simp
  {
    fix y assume "y \<in> set xs"
    hence "snd (sum_list xs) > 0"
      unfolding snd_sum_list
      by (intro sum_list_posI) (auto intro!: add_pos_pos cons simp: snd_sum_list)
    hence "sum_list xs \<noteq> 0" by simp
    from cons(5)[of x] have "coll 0 x (sum_list xs)"
      by (simp add: coll_add_cancel)
    from cons(5)[of y]
    have "coll 0 y (sum_list xs)"
      using \<open>y \<in> set xs\<close> cons(6)[of y] \<open>x + sum_list xs \<noteq> 0\<close>
      apply (cases "y = x")
      subgoal by (force simp add: coll_add_cancel)
      subgoal by (force simp: dest!: coll_add_trans[OF _ *(1) _ *(3)])
      done
  } note cl = this
  show ?case
    by (rule cons(2)[OF cH cy cl cons(6) \<open>a \<noteq> 0\<close>]) auto
qed

lemma sum_list_coll_ex_scale:
  assumes coll: "\<And>x. x \<in> set xs \<Longrightarrow> coll 0 z x"
  assumes nz: "z \<noteq> 0"
  shows "\<exists>r. sum_list xs = r *\<^sub>R z"
proof -
  {
    fix i assume i: "i < length xs"
    hence nth: "xs ! i \<in> set xs" by simp
    note coll_scale[OF coll[OF nth] \<open>z \<noteq> 0\<close>]
  } then obtain r where r: "\<And>i. i < length xs \<Longrightarrow> r i *\<^sub>R z = xs ! i"
    by metis
  have "xs = map ((!) xs) [0..<length xs]" by (simp add: map_nth)
  also have "\<dots> = map (\<lambda>i. r i *\<^sub>R z) [0..<length xs]"
    by (auto simp: r)
  also have "sum_list \<dots> = (\<Sum>i\<leftarrow>[0..<length xs]. r i) *\<^sub>R z"
    by (simp add: sum_list_sum_nth scaleR_sum_left)
  finally show ?thesis ..
qed

lemma sum_list_filter_coll_ex_scale: "z \<noteq> 0 \<Longrightarrow> \<exists>r. sum_list (filter (coll 0 z) zs) = r *\<^sub>R z"
  by (rule sum_list_coll_ex_scale) simp

end
