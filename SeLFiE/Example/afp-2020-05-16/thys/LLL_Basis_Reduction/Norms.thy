(*
    Authors:    Jose Divasón
                Maximilian Haslbeck
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Norms\<close>

text \<open>In this theory we provide the basic definitions and properties of several 
  norms of vectors and polynomials.
\<close> 

theory Norms
  imports "HOL-Computational_Algebra.Polynomial" 
    "HOL-Library.Adhoc_Overloading"
    "Jordan_Normal_Form.Conjugate"
    "Algebraic_Numbers.Resultant" (* only for poly_of_vec *)
    Missing_Lemmas
begin

subsection \<open>L-\<open>\<infinity>\<close> Norms\<close>

consts linf_norm :: "'a \<Rightarrow> 'b" ("\<parallel>(_)\<parallel>\<^sub>\<infinity>")

definition linf_norm_vec where "linf_norm_vec v \<equiv> max_list (map abs (list_of_vec v) @ [0])"
adhoc_overloading linf_norm linf_norm_vec

definition linf_norm_poly where "linf_norm_poly f \<equiv> max_list (map abs (coeffs f) @ [0])"
adhoc_overloading linf_norm linf_norm_poly

lemma linf_norm_vec: "\<parallel>vec n f\<parallel>\<^sub>\<infinity> = max_list (map (abs \<circ> f) [0..<n] @ [0])"
  by (simp add: linf_norm_vec_def)

lemma linf_norm_vec_vCons[simp]: "\<parallel>vCons a v\<parallel>\<^sub>\<infinity> = max \<bar>a\<bar> \<parallel>v\<parallel>\<^sub>\<infinity>"
  by (auto simp: linf_norm_vec_def max_list_Cons)

lemma linf_norm_vec_0 [simp]: "\<parallel>vec 0 f\<parallel>\<^sub>\<infinity> = 0" by (simp add: linf_norm_vec_def)

lemma linf_norm_zero_vec [simp]: "\<parallel>0\<^sub>v n :: 'a :: ordered_ab_group_add_abs vec\<parallel>\<^sub>\<infinity> = 0"
  by (induct n, simp add: zero_vec_def, auto simp: zero_vec_Suc)

lemma linf_norm_vec_ge_0 [intro!]:
  fixes v :: "'a :: ordered_ab_group_add_abs vec"
  shows "\<parallel>v\<parallel>\<^sub>\<infinity> \<ge> 0"
  by (induct v, auto simp: max_def)

lemma linf_norm_vec_eq_0 [simp]:
  fixes v :: "'a :: ordered_ab_group_add_abs vec"
  assumes "v \<in> carrier_vec n"
  shows "\<parallel>v\<parallel>\<^sub>\<infinity> = 0 \<longleftrightarrow> v = 0\<^sub>v n"
  by (insert assms, induct rule: carrier_vec_induct, auto simp: zero_vec_Suc max_def)

lemma linf_norm_vec_greater_0 [simp]:
  fixes v :: "'a :: ordered_ab_group_add_abs vec"
  assumes "v \<in> carrier_vec n"
  shows "\<parallel>v\<parallel>\<^sub>\<infinity> > 0 \<longleftrightarrow> v \<noteq> 0\<^sub>v n"
  by (insert assms, induct rule: carrier_vec_induct, auto simp: zero_vec_Suc max_def)

lemma linf_norm_poly_0 [simp]: "\<parallel>0::_ poly\<parallel>\<^sub>\<infinity> = 0"
  by (simp add: linf_norm_poly_def)

lemma linf_norm_pCons [simp]:
  fixes p :: "'a :: ordered_ab_group_add_abs poly"
  shows "\<parallel>pCons a p\<parallel>\<^sub>\<infinity> = max \<bar>a\<bar> \<parallel>p\<parallel>\<^sub>\<infinity>"
  by (cases "p = 0", cases "a = 0", auto simp: linf_norm_poly_def max_list_Cons)

lemma linf_norm_poly_ge_0 [intro!]:
  fixes f :: "'a :: ordered_ab_group_add_abs poly"
  shows "\<parallel>f\<parallel>\<^sub>\<infinity> \<ge> 0"
  by (induct f, auto simp: max_def)

lemma linf_norm_poly_eq_0 [simp]:
  fixes f :: "'a :: ordered_ab_group_add_abs poly"
  shows "\<parallel>f\<parallel>\<^sub>\<infinity> = 0 \<longleftrightarrow> f = 0"
  by (induct f, auto simp: max_def)

lemma linf_norm_poly_greater_0 [simp]:
  fixes f :: "'a :: ordered_ab_group_add_abs poly"
  shows "\<parallel>f\<parallel>\<^sub>\<infinity> > 0 \<longleftrightarrow> f \<noteq> 0"
  by (induct f, auto simp: max_def)

subsection \<open>Square Norms\<close>

consts sq_norm :: "'a \<Rightarrow> 'b" ("\<parallel>(_)\<parallel>\<^sup>2")

abbreviation "sq_norm_conjugate x \<equiv> x * conjugate x"
adhoc_overloading sq_norm sq_norm_conjugate

subsubsection \<open>Square norms for vectors\<close>

text \<open>We prefer sum\_list over sum because it is not essentially dependent on commutativity,
  and easier for proving.
\<close>
definition "sq_norm_vec v \<equiv> \<Sum>x \<leftarrow> list_of_vec v. \<parallel>x\<parallel>\<^sup>2"
adhoc_overloading sq_norm sq_norm_vec

lemma sq_norm_vec_vCons[simp]: "\<parallel>vCons a v\<parallel>\<^sup>2 = \<parallel>a\<parallel>\<^sup>2 + \<parallel>v\<parallel>\<^sup>2"
  by (simp add: sq_norm_vec_def)

lemma sq_norm_vec_0[simp]: "\<parallel>vec 0 f\<parallel>\<^sup>2 = 0"
  by (simp add: sq_norm_vec_def)

lemma sq_norm_vec_as_cscalar_prod:
  fixes v :: "'a :: conjugatable_ring vec"
  shows "\<parallel>v\<parallel>\<^sup>2 = v \<bullet>c v"
  by (induct v, simp_all add: sq_norm_vec_def)

lemma sq_norm_zero_vec[simp]: "\<parallel>0\<^sub>v n :: 'a :: conjugatable_ring vec\<parallel>\<^sup>2 = 0"
  by (simp add: sq_norm_vec_as_cscalar_prod)

lemmas sq_norm_vec_ge_0 [intro!] = conjugate_square_ge_0_vec[folded sq_norm_vec_as_cscalar_prod]

lemmas sq_norm_vec_eq_0 [simp] = conjugate_square_eq_0_vec[folded sq_norm_vec_as_cscalar_prod]

lemmas sq_norm_vec_greater_0 [simp] = conjugate_square_greater_0_vec[folded sq_norm_vec_as_cscalar_prod]

subsubsection \<open>Square norm for polynomials\<close>

definition sq_norm_poly where "sq_norm_poly p \<equiv> \<Sum>a\<leftarrow>coeffs p. \<parallel>a\<parallel>\<^sup>2"

adhoc_overloading sq_norm sq_norm_poly

lemma sq_norm_poly_0 [simp]: "\<parallel>0::_poly\<parallel>\<^sup>2 = 0"
  by (auto simp: sq_norm_poly_def)

lemma sq_norm_poly_pCons [simp]:
  fixes a :: "'a :: conjugatable_ring"
  shows "\<parallel>pCons a p\<parallel>\<^sup>2 = \<parallel>a\<parallel>\<^sup>2 + \<parallel>p\<parallel>\<^sup>2"
  by (cases "p = 0"; cases "a = 0", auto simp: sq_norm_poly_def)

lemma sq_norm_poly_ge_0 [intro!]:
  fixes p :: "'a :: conjugatable_ordered_ring poly"
  shows "\<parallel>p\<parallel>\<^sup>2 \<ge> 0"
  by (unfold sq_norm_poly_def, rule sum_list_nonneg, auto intro!:conjugate_square_positive)

lemma sq_norm_poly_eq_0 [simp]:
  fixes p :: "'a :: {conjugatable_ordered_ring,ring_no_zero_divisors} poly"
  shows "\<parallel>p\<parallel>\<^sup>2 = 0 \<longleftrightarrow> p = 0"
proof (induct p)
  case IH: (pCons a p)
  show ?case
  proof (cases "a = 0")
    case True
    with IH show ?thesis by simp
  next
    case False
    then have "\<parallel>a\<parallel>\<^sup>2 + \<parallel>p\<parallel>\<^sup>2 > 0" by (intro add_pos_nonneg, auto)
    then show ?thesis by auto
  qed
qed simp

lemma sq_norm_poly_pos [simp]:
  fixes p :: "'a :: {conjugatable_ordered_ring,ring_no_zero_divisors} poly"
  shows "\<parallel>p\<parallel>\<^sup>2 > 0 \<longleftrightarrow> p \<noteq> 0"
  by (auto simp: less_le)

lemma sq_norm_vec_of_poly [simp]:
  fixes p :: "'a :: conjugatable_ring poly"
  shows "\<parallel>vec_of_poly p\<parallel>\<^sup>2 = \<parallel>p\<parallel>\<^sup>2"
  apply (unfold sq_norm_poly_def sq_norm_vec_def)
  apply (fold sum_mset_sum_list)
  apply auto.

lemma sq_norm_poly_of_vec [simp]:
  fixes v :: "'a :: conjugatable_ring vec"
  shows "\<parallel>poly_of_vec v\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2"
  apply (unfold sq_norm_poly_def sq_norm_vec_def coeffs_poly_of_vec)
  apply (fold rev_map)
  apply (fold sum_mset_sum_list)
  apply (unfold mset_rev)
  apply (unfold sum_mset_sum_list)
  by (auto intro: sum_list_map_dropWhile0)

subsection \<open>Relating Norms\<close>

text \<open>A class where ordering around 0 is linear.\<close>
abbreviation (in ordered_semiring) is_real where "is_real a \<equiv> a < 0 \<or> a = 0 \<or> 0 < a"

class semiring_real_line = ordered_semiring_strict + ordered_semiring_0 +
  assumes add_pos_neg_is_real: "a > 0 \<Longrightarrow> b < 0 \<Longrightarrow> is_real (a + b)"
      and mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
      and pos_pos_linear: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> a < b \<or> a = b \<or> b < a"
      and neg_neg_linear: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> a < b \<or> a = b \<or> b < a"
begin

lemma add_neg_pos_is_real: "a < 0 \<Longrightarrow> b > 0 \<Longrightarrow> is_real (a + b)"
  using add_pos_neg_is_real[of b a] by (simp add: ac_simps)

lemma nonneg_linorder_cases [consumes 2, case_names less eq greater]:
  assumes "0 \<le> a" and "0 \<le> b"
      and "a < b \<Longrightarrow> thesis" "a = b \<Longrightarrow> thesis" "b < a \<Longrightarrow> thesis"
  shows thesis
  using assms pos_pos_linear by (auto simp: le_less)

lemma nonpos_linorder_cases [consumes 2, case_names less eq greater]:
  assumes "a \<le> 0" "b \<le> 0"
      and "a < b \<Longrightarrow> thesis" "a = b \<Longrightarrow> thesis" "b < a \<Longrightarrow> thesis"
  shows thesis
  using assms neg_neg_linear by (auto simp: le_less)

lemma real_linear:
  assumes "is_real a" and "is_real b" shows "a < b \<or> a = b \<or> b < a"
  using pos_pos_linear neg_neg_linear assms by (auto dest: less_trans[of _ 0])

lemma real_linorder_cases [consumes 2, case_names less eq greater]:
  assumes real: "is_real a" "is_real b"
      and cases: "a < b \<Longrightarrow> thesis" "a = b \<Longrightarrow> thesis" "b < a \<Longrightarrow> thesis"
  shows thesis
  using real_linear[OF real] cases by auto

lemma
  assumes a: "is_real a" and b: "is_real b"
  shows real_add_le_cancel_left_pos: "c + a \<le> c + b \<longleftrightarrow> a \<le> b"
    and real_add_less_cancel_left_pos: "c + a < c + b \<longleftrightarrow> a < b"
    and real_add_le_cancel_right_pos: "a + c \<le> b + c \<longleftrightarrow> a \<le> b"
    and real_add_less_cancel_right_pos: "a + c < b + c \<longleftrightarrow> a < b"
  using add_strict_left_mono[of b a c] add_strict_left_mono[of a b c]
  using add_strict_right_mono[of b a c] add_strict_right_mono[of a b c]
  by (atomize(full), cases rule: real_linorder_cases[OF a b], auto)

lemma
  assumes a: "is_real a" and b: "is_real b" and c: "0 < c"
  shows real_mult_le_cancel_left_pos: "c * a \<le> c * b \<longleftrightarrow> a \<le> b"
    and real_mult_less_cancel_left_pos: "c * a < c * b \<longleftrightarrow> a < b"
    and real_mult_le_cancel_right_pos: "a * c \<le> b * c \<longleftrightarrow> a \<le> b"
    and real_mult_less_cancel_right_pos: "a * c < b * c \<longleftrightarrow> a < b"
  using mult_strict_left_mono[of b a c] mult_strict_left_mono[of a b c] c
  using mult_strict_right_mono[of b a c] mult_strict_right_mono[of a b c] c
  by (atomize(full), cases rule: real_linorder_cases[OF a b], auto)

lemma
  assumes a: "is_real a" and b: "is_real b"
  shows not_le_real: "\<not> a \<ge> b \<longleftrightarrow> a < b"
    and not_less_real: "\<not> a > b \<longleftrightarrow> a \<le> b"
  by (atomize(full), cases rule: real_linorder_cases[OF a b], auto simp: less_imp_le)

lemma real_mult_eq_0_iff:
  assumes a: "is_real a" and b: "is_real b"
  shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
proof-
  { assume l: "a * b = 0" and "a \<noteq> 0" and "b \<noteq> 0"
    with a b have "a < 0 \<or> 0 < a" and "b < 0 \<or> 0 < b" by auto
    then have "False" using mult_pos_pos[of a b] mult_pos_neg[of a b] mult_neg_pos[of a b] mult_neg_neg[of a b]
      by (auto simp:l)
  } then show ?thesis by auto
qed

end

lemma real_pos_mult_max:
  fixes a b c :: "'a :: semiring_real_line"
  assumes c: "c > 0" and a: "is_real a" and b: "is_real b"
  shows "c * max a b = max (c * a) (c * b)"
  by (rule hom_max, simp add: real_mult_le_cancel_left_pos[OF a b c])

class ring_abs_real_line = ordered_ring_abs + semiring_real_line

class semiring_1_real_line = semiring_real_line + monoid_mult + zero_less_one
begin

subclass ordered_semiring_1 by (unfold_locales, auto)

lemma power_both_mono: "1 \<le> a \<Longrightarrow> m \<le> n \<Longrightarrow> a \<le> b \<Longrightarrow> a ^ m \<le> b ^ n"
  using power_mono[of a b n] power_increasing[of m n a]
  by (auto simp: order.trans[OF zero_le_one])

lemma power_pos:
  assumes a0: "0 < a" shows "0 < a ^ n"
  by (induct n, insert mult_strict_mono[OF a0] a0, auto)

lemma power_neg:
  assumes a0: "a < 0" shows "odd n \<Longrightarrow> a ^ n < 0" and "even n \<Longrightarrow> a ^ n > 0"
  by (atomize(full), induct n, insert a0, auto simp add: mult_pos_neg2 mult_neg_neg)

lemma power_ge_0_iff:
  assumes a: "is_real a"
  shows "0 \<le> a ^ n \<longleftrightarrow> 0 \<le> a \<or> even n"
using a proof (elim disjE)
  assume "a < 0"
  with power_neg[OF this, of n] show ?thesis by(cases "even n", auto)
next
  assume "0 < a"
  with power_pos[OF this] show ?thesis by auto
next
  assume "a = 0"
  then show ?thesis by (auto simp:power_0_left)
qed

lemma nonneg_power_less:
  assumes "0 \<le> a" and "0 \<le> b" shows "a^n < b^n \<longleftrightarrow> n > 0 \<and> a < b"
proof (insert assms, induct n arbitrary: a b)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note a = \<open>0 \<le> a\<close>
  note b = \<open>0 \<le> b\<close>
  show ?case
  proof (cases "n > 0")
    case True
    from a b show ?thesis
    proof (cases rule: nonneg_linorder_cases)
      case less
      then show ?thesis by (auto simp: Suc.hyps[OF a b] True intro!:mult_strict_mono' a b zero_le_power)
    next
      case eq
      then show ?thesis by simp
    next
      case greater
      with Suc.hyps[OF b a] True have "b ^ n < a ^ n" by auto
      with mult_strict_mono'[OF greater this] b greater
      show ?thesis by auto
    qed
  qed auto
qed

lemma power_strict_mono:
  shows "a < b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 < n \<Longrightarrow> a ^ n < b ^ n"
  by (subst nonneg_power_less, auto)

lemma nonneg_power_le:
  assumes "0 \<le> a" and "0 \<le> b" shows "a^n \<le> b^n \<longleftrightarrow> n = 0 \<or> a \<le> b"
using assms proof (cases rule: nonneg_linorder_cases)
  case less
  with power_strict_mono[OF this, of n] assms show ?thesis by (cases n, auto)
next
  case eq
  then show ?thesis by auto
next
  case greater
  with power_strict_mono[OF this, of n] assms show ?thesis by (cases n, auto)
qed

end

subclass (in linordered_idom) semiring_1_real_line
  apply unfold_locales
  by (auto simp: mult_strict_left_mono mult_strict_right_mono mult_neg_neg)

class ring_1_abs_real_line = ring_abs_real_line + semiring_1_real_line
begin

subclass ring_1..

lemma abs_cases:
  assumes "a = 0 \<Longrightarrow> thesis" and "\<bar>a\<bar> > 0 \<Longrightarrow> thesis" shows thesis
  using assms by auto

lemma abs_linorder_cases[case_names less eq greater]:
  assumes "\<bar>a\<bar> < \<bar>b\<bar> \<Longrightarrow> thesis" and "\<bar>a\<bar> = \<bar>b\<bar> \<Longrightarrow> thesis" and "\<bar>b\<bar> < \<bar>a\<bar> \<Longrightarrow> thesis"
  shows thesis
  apply (cases rule: nonneg_linorder_cases[of "\<bar>a\<bar>" "\<bar>b\<bar>"])
  using assms by auto

lemma [simp]:
  shows not_le_abs_abs: "\<not> \<bar>a\<bar> \<ge> \<bar>b\<bar> \<longleftrightarrow> \<bar>a\<bar> < \<bar>b\<bar>"
    and not_less_abs_abs: "\<not> \<bar>a\<bar> > \<bar>b\<bar> \<longleftrightarrow> \<bar>a\<bar> \<le> \<bar>b\<bar>"
  by (atomize(full), cases a b rule: abs_linorder_cases, auto simp: less_imp_le)

lemma abs_power_less [simp]: "\<bar>a\<bar>^n < \<bar>b\<bar>^n \<longleftrightarrow> n > 0 \<and> \<bar>a\<bar> < \<bar>b\<bar>"
  by (subst nonneg_power_less, auto)

lemma abs_power_le [simp]: "\<bar>a\<bar>^n \<le> \<bar>b\<bar>^n \<longleftrightarrow> n = 0 \<or> \<bar>a\<bar> \<le> \<bar>b\<bar>"
  by (subst nonneg_power_le, auto)

lemma abs_power_pos [simp]: "\<bar>a\<bar>^n > 0 \<longleftrightarrow> a \<noteq> 0 \<or> n = 0"
  using power_pos[of "\<bar>a\<bar>"] by (cases "n", auto)

lemma abs_power_nonneg [intro!]: "\<bar>a\<bar>^n \<ge> 0" by auto

lemma abs_power_eq_0 [simp]: "\<bar>a\<bar>^n = 0 \<longleftrightarrow> a = 0 \<and> n \<noteq> 0"
  apply (induct n, force)
  apply (unfold power_Suc)
  apply (subst real_mult_eq_0_iff, auto).

end

instance nat :: semiring_1_real_line by (intro_classes, auto)
instance int :: ring_1_abs_real_line..

lemma vec_index_vec_of_list [simp]: "vec_of_list xs $ i = xs ! i"
  by transfer (auto simp: mk_vec_def undef_vec_def dest: empty_nth)

lemma vec_of_list_append: "vec_of_list (xs @ ys) = vec_of_list xs @\<^sub>v vec_of_list ys"
  by (auto simp: nth_append)

lemma linf_norm_vec_of_list:
  "\<parallel>vec_of_list xs\<parallel>\<^sub>\<infinity> = max_list (map abs xs @ [0])"
  by (simp add: linf_norm_vec_def)

lemma linf_norm_vec_as_Greatest:
  fixes v :: "'a :: ring_1_abs_real_line vec"
  shows "\<parallel>v\<parallel>\<^sub>\<infinity> = (GREATEST a. a \<in> abs ` set (list_of_vec v) \<union> {0})"
  unfolding linf_norm_vec_of_list[of "list_of_vec v", simplified]
  by (subst max_list_as_Greatest, auto)

lemma vec_of_poly_pCons:
  assumes "f \<noteq> 0"
  shows "vec_of_poly (pCons a f) = vec_of_poly f @\<^sub>v vec_of_list [a]"
  using assms
  by (auto simp: vec_eq_iff Suc_diff_le)

lemma vec_of_poly_as_vec_of_list:
  assumes "f \<noteq> 0"
  shows "vec_of_poly f = vec_of_list (rev (coeffs f))"
proof (insert assms, induct f)
  case 0
  then show ?case by auto
next
  case (pCons a f)
  then show ?case
    by (cases "f = 0", auto simp: vec_of_list_append vec_of_poly_pCons)
qed

lemma linf_norm_vec_of_poly [simp]:
  fixes f :: "'a :: ring_1_abs_real_line poly"
  shows "\<parallel>vec_of_poly f\<parallel>\<^sub>\<infinity> = \<parallel>f\<parallel>\<^sub>\<infinity>"
proof (cases "f = 0")
  case False
  then show ?thesis
    apply (unfold vec_of_poly_as_vec_of_list linf_norm_vec_of_list linf_norm_poly_def)
    apply (subst (1 2) max_list_as_Greatest, auto).
qed simp

lemma linf_norm_poly_as_Greatest:
  fixes f :: "'a :: ring_1_abs_real_line poly"
  shows "\<parallel>f\<parallel>\<^sub>\<infinity> = (GREATEST a. a \<in> abs ` set (coeffs f) \<union> {0})"
  using linf_norm_vec_as_Greatest[of "vec_of_poly f"]
  by simp

lemma vec_index_le_linf_norm:
  fixes v :: "'a :: ring_1_abs_real_line vec"
  assumes "i < dim_vec v"
  shows "\<bar>v$i\<bar> \<le> \<parallel>v\<parallel>\<^sub>\<infinity>"
apply (unfold linf_norm_vec_def, rule le_max_list) using assms
apply (auto simp:  in_set_conv_nth intro!: imageI exI[of _ i]).

lemma coeff_le_linf_norm:
  fixes f :: "'a :: ring_1_abs_real_line poly"
  shows "\<bar>coeff f i\<bar> \<le> \<parallel>f\<parallel>\<^sub>\<infinity>"
  using vec_index_le_linf_norm[of "degree f - i" "vec_of_poly f"]
  by (cases "i \<le> degree f", auto simp: coeff_eq_0)

class conjugatable_ring_1_abs_real_line = conjugatable_ring + ring_1_abs_real_line + power +
  assumes sq_norm_as_sq_abs [simp]: "\<parallel>a\<parallel>\<^sup>2 = \<bar>a\<bar>\<^sup>2"
begin
subclass conjugatable_ordered_ring by (unfold_locales, simp)
end

instance int :: conjugatable_ring_1_abs_real_line
  by (intro_classes, simp add: numeral_2_eq_2)

instance rat :: conjugatable_ring_1_abs_real_line
  by (intro_classes, simp add: numeral_2_eq_2)

instance real :: conjugatable_ring_1_abs_real_line
  by (intro_classes, simp add: numeral_2_eq_2)

instance complex :: semiring_1_real_line
  apply intro_classes
  by (auto simp: complex_eq_iff mult_le_cancel_left mult_le_cancel_right mult_neg_neg)

text \<open>
  Due to the assumption @{thm abs_ge_self} from Groups.thy,
  @{type complex} cannot be @{class ring_1_abs_real_line}!
\<close>
instance complex :: ordered_ab_group_add_abs oops

lemma sq_norm_as_sq_abs [simp]: "(sq_norm :: 'a :: conjugatable_ring_1_abs_real_line \<Rightarrow> 'a) = power2 \<circ> abs"
  by auto

lemma sq_norm_vec_le_linf_norm:
  fixes v :: "'a :: {conjugatable_ring_1_abs_real_line} vec"
  assumes "v \<in> carrier_vec n"
  shows "\<parallel>v\<parallel>\<^sup>2 \<le> of_nat n * \<parallel>v\<parallel>\<^sub>\<infinity>\<^sup>2"
proof (insert assms, induct rule: carrier_vec_induct)
  case (Suc n a v)
  have [dest!]: "\<not> \<bar>a\<bar> \<le> \<parallel>v\<parallel>\<^sub>\<infinity> \<Longrightarrow> of_nat n * \<parallel>v\<parallel>\<^sub>\<infinity>\<^sup>2 \<le> of_nat n * \<bar>a\<bar>\<^sup>2"
    by (rule real_linorder_cases[of "\<bar>a\<bar>" "\<parallel>v\<parallel>\<^sub>\<infinity>"], insert Suc, auto simp: less_le intro!: power_mono mult_left_mono)
  from Suc show ?case
    by (auto simp: ring_distribs max_def intro!:add_mono power_mono)
qed simp
 
lemma sq_norm_poly_le_linf_norm:
  fixes p :: "'a :: {conjugatable_ring_1_abs_real_line} poly"
  shows "\<parallel>p\<parallel>\<^sup>2 \<le> of_nat (degree p + 1) * \<parallel>p\<parallel>\<^sub>\<infinity>\<^sup>2"
  using sq_norm_vec_le_linf_norm[of "vec_of_poly p" "degree p + 1"]
    by (auto simp: carrier_dim_vec)

lemma coeff_le_sq_norm:
  fixes f :: "'a :: {conjugatable_ring_1_abs_real_line} poly"
  shows "\<bar>coeff f i\<bar>\<^sup>2 \<le> \<parallel>f\<parallel>\<^sup>2"
proof (induct f arbitrary: i)
  case (pCons a f)
  show ?case
  proof (cases i)
    case (Suc ii)
    note pCons(2)[of ii]
    also have "\<parallel>f\<parallel>\<^sup>2 \<le> \<bar>a\<bar>\<^sup>2 + \<parallel>f\<parallel>\<^sup>2" by auto
    finally show ?thesis unfolding Suc by auto
  qed auto
qed simp

lemma max_norm_witness:
  fixes f :: "'a :: ordered_ring_abs poly"
  shows "\<exists> i. \<parallel>f\<parallel>\<^sub>\<infinity> = \<bar>coeff f i\<bar>"
  by (induct f, auto simp add: max_def intro: exI[of _ "Suc _"] exI[of _ 0])

lemma max_norm_le_sq_norm:
  fixes f ::  "'a :: conjugatable_ring_1_abs_real_line poly"
shows "\<parallel>f\<parallel>\<^sub>\<infinity>\<^sup>2 \<le> \<parallel>f\<parallel>\<^sup>2" 
proof -
  from max_norm_witness[of f] obtain i where id: "\<parallel>f\<parallel>\<^sub>\<infinity> = \<bar>coeff f i\<bar>" by auto
  show ?thesis unfolding id using coeff_le_sq_norm[of f i] by auto
qed

(*TODO MOVE*)
lemma (in conjugatable_ring) conjugate_minus: "conjugate (x - y) = conjugate x - conjugate y"
  by (unfold diff_conv_add_uminus conjugate_dist_add conjugate_neg, rule)

lemma conjugate_1[simp]: "(conjugate 1 :: 'a :: {conjugatable_ring, ring_1}) = 1"
proof-
  have "conjugate 1 * 1 = (conjugate 1 :: 'a)" by simp
  also have "conjugate \<dots> = 1" by simp
  finally show ?thesis by (unfold conjugate_dist_mul, simp)
qed

lemma conjugate_of_int [simp]:
  "(conjugate (of_int x) :: 'a :: {conjugatable_ring,ring_1}) = of_int x"
proof (induct x)
  case (nonneg n)
  then show ?case by (induct n, auto simp: conjugate_dist_add)
next
  case (neg n)
  then show ?case apply (induct n, auto simp: conjugate_minus conjugate_neg)
    by (metis conjugate_1 conjugate_dist_add one_add_one)
qed


lemma sq_norm_of_int: "\<parallel>map_vec of_int v :: 'a :: {conjugatable_ring,ring_1} vec\<parallel>\<^sup>2 = of_int \<parallel>v\<parallel>\<^sup>2" 
  unfolding sq_norm_vec_as_cscalar_prod scalar_prod_def
  unfolding hom_distribs
  by (rule sum.cong, auto)

definition "norm1 p = sum_list (map abs (coeffs p))"

lemma norm1_ge_0: "norm1 (f :: 'a :: {abs,ordered_semiring_0,ordered_ab_group_add_abs}poly) \<ge> 0" 
  unfolding norm1_def by (rule sum_list_nonneg, auto)

lemma norm2_norm1_main_equality: fixes f :: "nat \<Rightarrow> 'a :: linordered_idom" 
  shows "(\<Sum>i = 0..<n. \<bar>f i\<bar>)\<^sup>2 = (\<Sum>i = 0..<n. f i * f i)
      + (\<Sum>i = 0..<n. \<Sum>j = 0..<n. if i = j then 0 else \<bar>f i\<bar> * \<bar>f j\<bar>)"  
proof (induct n)
  case (Suc n)
  have id: "{0 ..< Suc n} = insert n {0 ..< n}" by auto
  have id: "sum f {0 ..< Suc n} = f n + sum f {0 ..< n}" for f :: "nat \<Rightarrow> 'a" 
    unfolding id by (rule sum.insert, auto)
  show ?case unfolding id power2_sum unfolding Suc
    by (auto simp: power2_eq_square sum_distrib_left sum.distrib ac_simps)
qed auto

lemma norm2_norm1_main_inequality: fixes f :: "nat \<Rightarrow> 'a :: linordered_idom" 
  shows "(\<Sum>i = 0..<n. f i * f i) \<le> (\<Sum>i = 0..<n. \<bar>f i\<bar>)\<^sup>2"  
  unfolding norm2_norm1_main_equality 
  by (auto intro!: sum_nonneg)  

lemma norm2_le_norm1_int: "\<parallel>f :: int poly\<parallel>\<^sup>2 \<le> (norm1 f)^2" 
proof -
  define F where "F = (!) (coeffs f)" 
  define n where "n = length (coeffs f)" 
  have 1: "\<parallel>f\<parallel>\<^sup>2 = (\<Sum>i = 0..<n. F i * F i)" 
    unfolding norm1_def sq_norm_poly_def sum_list_sum_nth F_def n_def
    by (subst sum.cong, auto simp: power2_eq_square)
  have 2: "norm1 f = (\<Sum>i = 0..<n. \<bar>F i\<bar>)" 
    unfolding norm1_def sq_norm_poly_def sum_list_sum_nth F_def n_def
    by (subst sum.cong, auto)
  show ?thesis unfolding 1 2 by (rule norm2_norm1_main_inequality)
qed

lemma sq_norm_smult_vec: "sq_norm ((c :: 'a :: {conjugatable_ring,comm_semiring_0}) \<cdot>\<^sub>v v) = (c * conjugate c) * sq_norm v" 
  unfolding sq_norm_vec_as_cscalar_prod 
  by (subst scalar_prod_smult_left, force, unfold conjugate_smult_vec, 
    subst scalar_prod_smult_right, force, simp add: ac_simps)

lemma vec_le_sq_norm:
  fixes v :: "'a :: conjugatable_ring_1_abs_real_line vec"
  assumes "v \<in> carrier_vec n" "i < n"
  shows "\<bar>v $ i\<bar>\<^sup>2 \<le> \<parallel>v\<parallel>\<^sup>2"
using assms proof (induction v arbitrary: i)
  case (Suc n a v i)
  note IH = Suc
  show ?case 
  proof (cases i)
    case (Suc ii)
    then show ?thesis
      using IH IH(2)[of ii] le_add_same_cancel2 order_trans by fastforce
  qed auto
qed auto

class trivial_conjugatable =
  conjugate +
  assumes conjugate_id [simp]: "conjugate x = x"

class trivial_conjugatable_ordered_field = 
  conjugatable_ordered_field + trivial_conjugatable

class trivial_conjugatable_linordered_field = 
  trivial_conjugatable_ordered_field + linordered_field
begin
subclass conjugatable_ring_1_abs_real_line
  by (standard) (auto simp add: semiring_normalization_rules)
end

instance rat :: trivial_conjugatable_linordered_field 
  by (standard, auto)

instance real :: trivial_conjugatable_linordered_field 
  by (standard, auto)

lemma scalar_prod_ge_0: "(x :: 'a :: linordered_idom vec) \<bullet> x \<ge> 0" 
  unfolding scalar_prod_def
  by (rule sum_nonneg, auto)

lemma cscalar_prod_is_scalar_prod[simp]: "(x :: 'a :: trivial_conjugatable_ordered_field vec) \<bullet>c y = x \<bullet> y"
  unfolding conjugate_id
  by (rule arg_cong[of _ _ "scalar_prod x"], auto)


lemma scalar_prod_Cauchy:
  fixes u v::"'a :: {trivial_conjugatable_linordered_field} Matrix.vec"
  assumes "u \<in> carrier_vec n" "v \<in> carrier_vec n"
  shows "(u \<bullet> v)\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2 * \<parallel>v\<parallel>\<^sup>2 "
proof -
  { assume v_0: "v \<noteq> 0\<^sub>v n"
    have "0 \<le> (u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v)" for r
      by (simp add: scalar_prod_ge_0)
    also have "(u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v) = u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v)" for r::'a
    proof -
      have "(u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v) = (u - r \<cdot>\<^sub>v v) \<bullet> u - (u - r \<cdot>\<^sub>v v) \<bullet> (r \<cdot>\<^sub>v v)"
        using assms by (subst scalar_prod_minus_distrib) auto
      also have "\<dots> = u \<bullet> u - (r \<cdot>\<^sub>v v) \<bullet> u - r * ((u - r \<cdot>\<^sub>v v) \<bullet> v)"
        using assms by (subst minus_scalar_prod_distrib) auto
      also have "\<dots> = u \<bullet> u - r * (v \<bullet> u) - r * (u \<bullet> v - r * (v \<bullet> v))"
        using assms by (subst minus_scalar_prod_distrib) auto
      also have "\<dots> = u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v)"
        using assms comm_scalar_prod by (auto simp add: field_simps)
      finally show ?thesis
        by simp
    qed
    also have "u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v) = sq_norm u - (u \<bullet> v)\<^sup>2 / sq_norm v"
      if "r = (u \<bullet> v) / (v \<bullet> v)" for r
      unfolding that by (auto simp add: sq_norm_vec_as_cscalar_prod power2_eq_square)
    finally have "0 \<le> \<parallel>u\<parallel>\<^sup>2 - (u \<bullet> v)\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
      by auto
    then have "(u \<bullet> v)\<^sup>2 / \<parallel>v\<parallel>\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2"
      by auto
    then have "(u \<bullet> v)\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2 * \<parallel>v\<parallel>\<^sup>2"
      using pos_divide_le_eq[of "\<parallel>v\<parallel>\<^sup>2"] v_0 assms by (auto)
  }
  then show ?thesis
    by (fastforce simp add: assms)
qed

end
