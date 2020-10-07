(*  Title:      Cayley_Hamilton/Cayley_Hamilton.thy
    Author:     Johannes Hölzl, TU München
    Author:     Stefan Hetzl, TU Wien
    Author:     Stephan Adelsberge, WU Wien
    Author:     Florian Pollak, TU Wien
*)

(*<*)
theory Cayley_Hamilton
imports
  Square_Matrix
  "HOL-Computational_Algebra.Polynomial"  
begin

definition C :: "'a \<Rightarrow> 'a::ring_1 poly" where "C c = [:c:]"
abbreviation CC ("\<^bold>C") where "\<^bold>C \<equiv> map_sq_matrix C"

lemma degree_C[simp]: "degree (C a) = 0"
  by (simp add: C_def)

lemma coeff_C_0[simp]: "coeff (C x) 0 = x"
  by (simp add: C_def)

lemma coeff_C_gt0[simp]: "0 < n \<Longrightarrow> coeff (C x) n = 0"
  by (cases n) (simp_all add: C_def)

lemma coeff_C_eq: "coeff (C x) n = (if n = 0 then x else 0)"
  by simp

lemma coeff_mult_C[simp]: "coeff (a * C x) n = coeff a n * x"
  by (simp add: coeff_mult coeff_C_eq if_distrib[where f="\<lambda>x. a * x" for a] sum.If_cases)

lemma coeff_C_mult[simp]: "coeff (C x * a) n = x * coeff a n"
  by (simp add: coeff_mult coeff_C_eq if_distrib[where f="\<lambda>x. x * a" for a] sum.If_cases)

lemma C_0[simp]: "C 0 = 0"
  by (simp add: C_def) 

lemma C_1[simp]: "C 1 = 1"
  by (simp add: C_def)

lemma C_linear:
  shows C_mult: "C (a * b) = C b * C a"
    and C_add: "C (a + b) = C a + C b"
    and C_minus: "C (- a) = - C a"
    and C_diff: "C (a - b) = C a - C b"
  by (simp_all add: C_def)

definition X :: "'a::ring_1 poly" where "X = [:0, 1:]"
abbreviation XX ("\<^bold>X") where "\<^bold>X \<equiv> diag X"

lemma degree_X[simp]: "degree X = 1"
  by (simp add: X_def)

lemma coeff_X_Suc_0[simp]: "coeff X (Suc 0) = 1"
  by (auto simp: X_def)

lemma coeff_X_mult[simp]: "coeff (X * p) (Suc i) = coeff p i"
  by (auto simp: X_def)

lemma coeff_mult_X[simp]: "coeff (p * X) (Suc i) = coeff p i"
  by (auto simp: X_def)

lemma coeff_X_mult_0[simp]: "coeff (X * p) 0 = 0"
  by (auto simp: X_def)

lemma coeff_mult_X_0[simp]: "coeff (p * X) 0 = 0"
  by (auto simp: X_def)

lemma coeff_X: "coeff X i = (if i = 1 then 1 else 0)"
  by (cases i) (auto simp: X_def gr0_conv_Suc)

lemma coeff_pow_X: "coeff (X ^ i) n = (if i = n then 1 else 0)"
proof (induction i arbitrary: n)
  case (Suc i) then show ?case
    by (cases n) simp_all
qed auto

lemma coeff_pow_X_eq[simp]: "coeff (X^i) i = 1"
  by (simp add: coeff_pow_X)

lemma (in monoid_mult) power_ac: "a * (a^n * x) = a^n * (a * x)"
  by (metis power_Suc2 power_Suc mult.assoc)

text\<open>This theory contains auxiliary lemmas on polynomials.\<close>

lemma degree_prod_le: "degree (\<Prod>i\<in>S. f i) \<le> (\<Sum>i\<in>S. degree (f i))"
  by (induction S rule: infinite_finite_induct)
     (simp_all, metis (lifting) degree_mult_le dual_order.trans nat_add_left_cancel_le)

lemma coeff_mult_sum:
  "degree p \<le> m \<Longrightarrow> degree q \<le> n \<Longrightarrow> coeff (p * q) (m + n) = coeff p m * coeff q n"
  using degree_mult_le[of p q] by (auto simp add: le_less coeff_eq_0 coeff_mult_degree_sum)

lemma coeff_mult_prod_sum:
  "coeff (\<Prod>i\<in>S. f i) (\<Sum>i\<in>S. degree (f i)) = (\<Prod>i\<in>S. coeff (f i) (degree (f i)))"
  by (induct rule: infinite_finite_induct)(simp_all add: coeff_mult_sum degree_prod_le)

lemma degree_sum_less:
  "0 < n \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> degree (f x) < n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) < n" 
  by (induct rule: infinite_finite_induct) (simp_all add: degree_add_less)

lemma degree_sum_le:
  shows "(\<And>x. x \<in> A \<Longrightarrow> degree (f x) \<le> n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) \<le> n"
  by (induct rule: infinite_finite_induct) (auto intro!: degree_add_le)

lemma degree_sum_le_Max:
  "finite F \<Longrightarrow> degree (sum f F) \<le> Max ((\<lambda>x. degree (f x))`F)"
  by (intro degree_sum_le) (auto intro!: Max.coboundedI)

lemma poly_as_sum_of_monoms': assumes n: "degree p \<le> n" shows "(\<Sum>i\<le>n. X^i * C (coeff p i)) = p"
proof -
  have eq: "\<And>i. {..n} \<inter> {i} = (if i \<le> n then {i} else {})"
    by auto
  show ?thesis
    using n
    by (simp add: poly_eq_iff coeff_sum coeff_eq_0 sum.If_cases eq coeff_pow_X
                  if_distrib[where f="\<lambda>x. x * a" for a])
qed

lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. X^i * C (coeff p i)) = p"
  by (intro poly_as_sum_of_monoms' order_refl)

lemma degree_sum_unique':
  assumes I: "finite I" "i \<notin> I" "\<And>j. j \<in> I \<Longrightarrow> degree (p j) < degree (p i)"
  shows "degree (\<Sum>i\<in>insert i I. p i) = degree (p i)"
  using I
proof (induction I)
  case (insert j I) then show ?case
    by (subst insert_commute) (auto simp: degree_add_eq_right) 
qed simp

lemma degree_sum_unique:
  "finite I \<Longrightarrow> i \<in> I \<Longrightarrow> (\<And>j. j \<in> I \<Longrightarrow> j \<noteq> i \<Longrightarrow> degree (p j) < degree (p i)) \<Longrightarrow>
    degree (\<Sum>i\<in>I. p i) = degree (p i)"
  using degree_sum_unique'[of "I - {i}" i p] by (auto simp: insert_absorb)

lemma coeff_sum_unique:
  fixes p :: "'a \<Rightarrow> 'b::semiring_0 poly"
  assumes I: "finite I" "i \<in> I" "\<And>j. j \<in> I \<Longrightarrow> j \<noteq> i \<Longrightarrow> degree (p j) < degree (p i)"
  shows "coeff (\<Sum>i\<in>I. p i) (degree (p i)) = coeff (p i) (degree (p i))"
proof -
  have "(\<Sum>j\<in>I. coeff (p j) (degree (p i))) = (\<Sum>i\<in>{i}. coeff (p i) (degree (p i)))"
    using I by (intro sum.mono_neutral_cong_right) (auto intro!: coeff_eq_0)
  then show ?thesis
    by (simp add: coeff_sum)
qed

lemma diag_coeff: "diag (coeff x i) = map_sq_matrix (\<lambda>x. coeff x i) (diag x)"
  by transfer' (simp add: vec_eq_iff)

lemma smult_one: "x *\<^sub>S 1 = diag x"
  by transfer (simp add: fun_eq_iff)

lemma sum_telescope_Ico: "a \<le> b \<Longrightarrow> (\<Sum>i=a ..< b. f i - f (Suc i) ::_::ab_group_add) = f a - f b"
  by (induction b rule: dec_induct) auto

lemmas map_sq_matrix = map_sq_matrix_diff map_sq_matrix_add map_sq_matrix_smult map_sq_matrix_sum

lemma sign_permut: "degree (of_int (sign p) * q) = degree q" 
  by (simp add: sign_def)

lemma degree_det:
  assumes "\<And>j. j permutes UNIV \<Longrightarrow> j \<noteq> id \<Longrightarrow> degree (\<Prod>i\<in>UNIV. to_fun A i (j i)) < degree (\<Prod>i\<in>UNIV. to_fun A i i)"
  shows "degree (det A) = degree (\<Prod>i\<in>UNIV. to_fun A i i)"
  unfolding det_eq
  by (subst degree_sum_unique[where i=id])
     (simp_all add: sign_permut permutes_id assms)

definition max_degree :: "'a::zero poly^^'n \<Rightarrow> nat" where
  "max_degree A = Max (range (\<lambda>(i, j). degree (to_fun A i j)))"

lemma degree_le_max_degree: "degree (to_fun A i j) \<le> max_degree A"
  unfolding max_degree_def by (auto simp add: Max_ge_iff)

definition "charpoly A = det (\<^bold>X - \<^bold>C A)"

lemma degree_diff_cancel: "degree q < degree p \<Longrightarrow> degree (p - q::_::ab_group_add poly) = degree p"
  by (metis add_uminus_conv_diff degree_add_eq_left degree_minus)

lemma
  fixes A :: "'a::comm_ring_1^^'n"
  shows degree_charpoly: "degree (charpoly A) = CARD('n)"
    and coeff_charpoly: "coeff (charpoly A) (degree (charpoly A)) = 1"
proof -
  let ?B = "diag X - map_sq_matrix C A"
  let ?f = "\<lambda>p. \<Prod>i\<in>UNIV. to_fun ?B i (p i)"
  let ?g = "\<lambda>p. of_int (sign p) * ?f p"

  have dB: "\<And>i j. degree (to_fun ?B i j) = (if i = j then 1 else 0)"
    by transfer' (simp add: degree_diff_cancel)
  have cB: "\<And>i j. coeff (to_fun ?B i j) (Suc 0) = (if i = j then 1 else 0)"
    by transfer' simp

  have degree_f_id: "degree (?f (\<lambda>i. i)) = CARD('n)"
    using coeff_mult_prod_sum[of "\<lambda>i. to_fun ?B i i" UNIV]
    by (intro antisym degree_prod_le[THEN order_trans] le_degree)
       (simp_all add: dB cB)

  have degree_less: "\<And>p. p \<noteq> id \<Longrightarrow> degree (?f p) < degree (?f (\<lambda>i. i))"
    unfolding degree_f_id
    by (rule le_less_trans[OF degree_prod_le])
       (auto simp add: dB sum.If_cases set_eq_iff intro!: psubset_card_mono)

  have degree_charpoly: "degree (charpoly A) = degree (?f (\<lambda>i. i))"
    using degree_less unfolding charpoly_def by (rule degree_det)

  show degree_eq: "degree (charpoly A) = CARD('n)"
    using degree_charpoly degree_f_id by simp

  have "coeff (\<Sum>p | p permutes UNIV. ?g p) (degree (?g id)) = 1"
  proof (subst coeff_sum_unique)
    show "coeff (?g id) (degree (?g id)) = 1"
      using coeff_mult_prod_sum[of "\<lambda>i. to_fun ?B i i" UNIV]
      by (simp add: dB cB sign_id degree_f_id)
  qed (auto simp: degree_less sign_permut permutes_id)

  then show "coeff (charpoly A) (degree (charpoly A)) = 1"
    unfolding degree_charpoly by (simp add: sign_permut charpoly_def det_eq)
qed

definition "max_perm_degree A = Max ((\<lambda>p. \<Sum>i\<in>UNIV. degree (to_fun A i (p i)))`{p. p permutes UNIV})"

lemma max_perm_degree_eqI:
  "(\<And>p. p permutes (UNIV::'a::finite set) \<Longrightarrow> (\<Sum>i\<in>UNIV. degree (to_fun A i (p i))) \<le> x) \<Longrightarrow>
    (\<exists>p. p permutes UNIV \<and> (\<Sum>i\<in>UNIV. degree (to_fun A i (p i))) = x) \<Longrightarrow>
    max_perm_degree A = x"
  by (auto intro!: Max_eqI  simp: max_perm_degree_def)

lemma degree_prod_le_max_perm_degree:
  "j permutes (UNIV::'a::finite set) \<Longrightarrow> degree (\<Prod>i\<in>UNIV. to_fun A i (j i)) \<le> max_perm_degree A"
  unfolding max_perm_degree_def by (rule order_trans[OF degree_prod_le]) auto

lemma degree_le_max_perm_degree: "degree (det A) \<le> max_perm_degree A"
  unfolding det_eq
  by (rule order_trans[OF degree_sum_le_Max])
     (auto intro!: degree_prod_le_max_perm_degree Max_le_iff[THEN iffD2] permutes_id simp: sign_permut)

lemma max_degree_adjugate:
  fixes A :: "_^^'n"
  shows "max_degree (adjugate (\<^bold>X - \<^bold>C A)) = CARD('n) - 1"
    (is "?R = _")
proof -
  let ?M = "minor (\<^bold>X - \<^bold>C A)"
  let ?D = "\<lambda>i j k l. degree (to_fun (?M i j) k l)"

  have M: "\<And>i j k l. to_fun (?M i j) k l = (if k = i \<and> l = j then 1
    else if k = i \<or> l = j then 0
    else if k = l then [: - to_fun A k l, 1 :] else [: - to_fun A k l :])"
    by transfer' (simp add: vec_eq_iff C_def X_def)

  have "?R = Max (range (\<lambda>(i, j). degree (det (?M j i))))" (is "_ = Max ?Max")
    unfolding max_degree_def by (simp add: transpose.rep_eq cofactor_def adjugate_def of_fun_inverse)
  also have "\<dots> = CARD('n) - 1"
  proof (rule antisym)
    show "Max ?Max \<le> CARD('n) - 1"
    proof (safe intro!: Max.boundedI)
      fix i j
      have "max_perm_degree (?M j i) = card (UNIV - {i, j})"
        by (intro max_perm_degree_eqI)
           (auto simp: M sum.If_cases if_distrib[of degree] simp del: card_Diff_insert
                 intro!: card_mono permutes_id arg_cong[where f=card])
      then show "degree (det (?M j i)) \<le> CARD('n) - 1"
        using degree_le_max_perm_degree[of "?M j i"] by (cases "i = j") auto
    qed auto
  next
    obtain x :: 'n where True by auto
    let ?P = "\<lambda>j k p. \<Prod>i\<in>UNIV. to_fun (?M j k) i (p i)"

    have "degree (det (?M x x)) = CARD('n) - 1"
    proof (subst degree_det)
      have "CARD('n) - 1 = (\<Sum>i\<in>UNIV. ?D x x i i)"
        by (simp add: M if_distrib[where f="degree"] sum.If_cases Collect_neg_eq Compl_eq_Diff_UNIV)
      also have "\<dots> = degree (?P x x id)"
        by (auto intro!: antisym degree_prod_le le_degree simp add: coeff_mult_prod_sum)
           (simp add: M if_distrib[where f="\<lambda>x. coeff x b" for b] prod.If_cases)
      finally show *: "degree (?P x x (\<lambda>x. x)) = CARD('n) - 1"
        by simp

      fix p :: "'n \<Rightarrow> 'n" assume "p permutes UNIV" "p \<noteq> id"
      then obtain i j where ij: "i \<noteq> j" "p i = j"  and p: "i \<noteq> p i" "j \<noteq> p j"
        unfolding id_def by simp (metis permutes_univ)
      then have "card {i,j} \<le> CARD('n)"
        by (intro card_mono) auto
      have "degree (?P x x p) \<le> card (UNIV - {i, j})"
        using degree_prod_le
        by (rule order_trans)
           (auto simp: M if_distrib[where f="degree"] sum.If_cases Collect_neg_eq Compl_eq_Diff_UNIV p intro!: card_mono)
      also have "\<dots> < CARD('n) - 1"
        using \<open>card {i, j} \<le> CARD('n)\<close> ij by auto
      finally show "degree (?P x x p) < degree (?P x x (\<lambda>x. x))"
        using * by simp
    qed
    then show "CARD('n) - 1 \<le> Max ?Max"
      by (auto simp add: Max_ge_iff intro!: exI[of _ x])
  qed
  finally show ?thesis .
qed

definition poly_mat :: "'a::ring_1 poly \<Rightarrow> 'a^^'n \<Rightarrow> 'a^^'n" where
  "poly_mat p A = (\<Sum>i\<le>degree p. coeff p i *\<^sub>S A^i)"

lemma zero_smult[simp]: "0 *\<^sub>S M = (0::'a::semiring_1^^'n)"
  by transfer (simp add: vec_eq_iff)

lemma smult_smult: "a *\<^sub>S b *\<^sub>S M = (a * b::'a::monoid_mult) *\<^sub>S M"
  by transfer (simp add: mult_ac)

lemma map_sq_matrix_mult_eq_smult[simp]: "map_sq_matrix ((*) a) M = a *\<^sub>S M"
  by transfer rule

lemma coeff_smult_1: "coeff p i *\<^sub>S m = m * map_sq_matrix (\<lambda>p. coeff p i) (p *\<^sub>S 1::_::comm_ring_1 ^^ 'n)"
  by (simp add: smult_one mult_diag)

lemma map_sq_matrix_if_distrib[simp]:
  "map_sq_matrix (\<lambda>x. if P then f x else g x) = (if P then map_sq_matrix f else map_sq_matrix g)"
  by simp
(*>*)

theorem Cayley_Hamilton:
  fixes A :: "'a::comm_ring_1 ^^ 'n"
  shows "poly_mat (charpoly A) A = 0"
proof -
text %visible \<open>\hrulefill ~~ Part 1 ~~ \hrulefill\<close>
  define n where "n = CARD('n) - 1"
  then have d_charpoly: "n + 1 = degree (charpoly A)" and 
      d_adj: "n = max_degree (adjugate (\<^bold>X - \<^bold>C A))"
    by %invisible (simp_all add: degree_charpoly n_def max_degree_adjugate monom_0 diag_1[symmetric])

  define B where "B i = map_sq_matrix (\<lambda>p. coeff p i) (adjugate (\<^bold>X - \<^bold>C A))" for i
  have A_eq_B: "adjugate (\<^bold>X - \<^bold>C A) = (\<Sum>i\<le>n. X^i *\<^sub>S \<^bold>C (B i))"
    by %invisible (simp add: map_sq_matrix_smult sum_map_sq_matrix B_def d_adj
                        degree_le_max_degree poly_as_sum_of_monoms' cong: map_sq_matrix_cong)
text %visible \<open>\hrulefill ~~ Part 2 ~~ \hrulefill\<close>
  have "charpoly A *\<^sub>S 1 = X *\<^sub>S adjugate (\<^bold>X - \<^bold>C A) - \<^bold>C A * adjugate (\<^bold>X - \<^bold>C A)" 
    by %invisible (simp add: smult_one charpoly_def mult_adjugate_det[symmetric] field_simps diag_mult)
  also have "\<dots> = (\<Sum>i\<le>n. X^(i + 1) *\<^sub>S \<^bold>C (B i)) - (\<Sum>i\<le>n. X^i *\<^sub>S \<^bold>C (A * B i))"
    unfolding %invisible A_eq_B by %invisible (simp add: sum_distrib_left smult_mult2[symmetric]
      map_sq_matrix_mult[symmetric] C_linear smult_sum[symmetric] smult_smult)
  also have "(\<Sum>i\<le>n. X^(i + 1) *\<^sub>S \<^bold>C (B i)) =
      (\<Sum>i<n. X^(i + 1) *\<^sub>S \<^bold>C (B i)) + X^(n + 1) *\<^sub>S \<^bold>C (B n)"
    by %invisible (simp add: lessThan_Suc_atMost[symmetric])
  also have "(\<Sum>i\<le>n. X^i *\<^sub>S \<^bold>C (A * B i)) =
      (\<Sum>i<n. X^(i + 1) *\<^sub>S \<^bold>C (A * B (i + 1))) + \<^bold>C (A * B 0)"
    unfolding %invisible lessThan_Suc_atMost[symmetric] lessThan_Suc_eq_insert_0
    by %invisible (simp add: zero_notin_Suc_image monom_0 sum.reindex one_poly_def[symmetric] diag_mult)
  finally have diag_charpoly:
    "charpoly A *\<^sub>S 1 = X^(n + 1) *\<^sub>S \<^bold>C (B n) +
      (\<Sum>i<n. X^(i + 1) *\<^sub>S \<^bold>C (B i - A * B (i + 1))) - \<^bold>C (A * B 0)"
    by %invisible (simp add: map_sq_matrix_diff C_linear sum_subtractf smult_diff)
text %visible \<open>\hrulefill ~~ Part 3 ~~ \hrulefill\<close>
  let ?p = "\<lambda>i. coeff (charpoly A) i *\<^sub>S A^i"
  let ?AB = "\<lambda>i. A^(i + 1) * B i"
  have "(\<Sum>i\<le>n+1. ?p i) = ?p 0 + (\<Sum>i<n. ?p (i + 1)) + ?p (n + 1)"
    unfolding %invisible sum.atMost_Suc_shift Suc_eq_plus1[symmetric]
    by %invisible (simp add: lessThan_Suc_atMost[symmetric])
  also have "?p 0 = - ?AB 0"
    by %invisible (simp add: coeff_smult_1 diag_charpoly map_sq_matrix)
  also have "(\<Sum>i<n. ?p (i + 1)) = (\<Sum>i=0..<n. ?AB i - ?AB (i + 1))"
      by %invisible (rule sum.cong)
         (auto simp: coeff_smult_1 coeff_pow_X diag_charpoly map_sq_matrix sum_subtractf
                     if_distrib[where f="\<lambda>x. x a" for a] if_distrib[where f="\<lambda>x. a * x" for a]
                     field_simps sum.If_cases power_Suc2
               simp del: power_Suc)
  also have "\<dots> = ?AB 0 - ?AB n"
    unfolding %invisible Suc_eq_plus1[symmetric]
    by %invisible (subst sum_telescope_Ico) auto
  also have "?AB n = ?p (n + 1)"
    unfolding %invisible coeff_smult_1 diag_charpoly
    by %invisible (simp add: mult_diag map_sq_matrix coeff_pow_X)
  also have "coeff (charpoly A) (n + 1) = 1"
    by %invisible (simp add: coeff_charpoly d_charpoly[simplified])
  finally show ?thesis
    by %invisible (simp add: poly_mat_def d_charpoly[simplified] diag_0_eq mult_diag)
qed
(*<*)

end
(*>*)
