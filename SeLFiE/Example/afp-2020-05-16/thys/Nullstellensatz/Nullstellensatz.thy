(* Author: Alexander Maletzky *)

section \<open>Hilbert's Nullstellensatz\<close>

theory Nullstellensatz
  imports Algebraically_Closed_Fields
          "HOL-Computational_Algebra.Fraction_Field"
          Lex_Order_PP
          Univariate_PM
          Groebner_Bases.Groebner_PM
begin

text \<open>We prove the geometric version of Hilbert's Nullstellensatz, i.e. the precise correspondence
  between algebraic varieties and radical ideals.
  The field-theoretic version of the Nullstellensatz is proved in theory \<open>Nullstellensatz_Field\<close>.\<close>

subsection \<open>Preliminaries\<close>

lemma finite_linorder_induct [consumes 1, case_names empty insert]:
  assumes "finite (A::'a::linorder set)" and "P {}"
    and "\<And>a A. finite A \<Longrightarrow> A \<subseteq> {..<a} \<Longrightarrow> P A \<Longrightarrow> P (insert a A)"
  shows "P A"
proof -
  define k where "k = card A"
  thus ?thesis using assms(1)
  proof (induct k arbitrary: A)
    case 0
    with assms(2) show ?case by simp
  next
    case (Suc k)
    define a where "a = Max A"
    from Suc.prems(1) have "A \<noteq> {}" by auto
    with Suc.prems(2) have "a \<in> A" unfolding a_def by (rule Max_in)
    with Suc.prems have "k = card (A - {a})" by simp
    moreover from Suc.prems(2) have "finite (A - {a})" by simp
    ultimately have "P (A - {a})" by (rule Suc.hyps)
    with \<open>finite (A - {a})\<close> _ have "P (insert a (A - {a}))"
    proof (rule assms(3))
      show "A - {a} \<subseteq> {..<a}"
      proof
        fix b
        assume "b \<in> A - {a}"
        hence "b \<in> A" and "b \<noteq> a" by simp_all
        moreover from Suc.prems(2) this(1) have "b \<le> a" unfolding a_def by (rule Max_ge)
        ultimately show "b \<in> {..<a}" by simp
      qed
    qed
    with \<open>a \<in> A\<close> show ?case by (simp add: insert_absorb)
  qed
qed

lemma Fract_same: "Fract a a = (1 when a \<noteq> 0)"
  by (simp add: One_fract_def Zero_fract_def eq_fract when_def)

lemma Fract_eq_zero_iff: "Fract a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (metis (no_types, lifting) Zero_fract_def eq_fract(1) eq_fract(2) mult_eq_0_iff one_neq_zero)

lemma poly_plus_rightE:
  obtains c where "poly p (x + y) = poly p x + c * y"
proof (induct p arbitrary: thesis)
  case 0
  have "poly 0 (x + y) = poly 0 x + 0 * y" by simp
  thus ?case by (rule 0)
next
  case (pCons a p)
  obtain c where "poly p (x + y) = poly p x + c * y" by (rule pCons.hyps)
  hence "poly (pCons a p) (x + y) = a + (x + y) * (poly p x + c * y)" by simp
  also have "\<dots> = poly (pCons a p) x + (x * c + (poly p x + c * y)) * y" by (simp add: algebra_simps)
  finally show ?case by (rule pCons.prems)
qed

lemma poly_minus_rightE:
  obtains c where "poly p (x - y) = poly p x - c * (y::_::comm_ring)"
  by (metis add_diff_cancel_right' diff_add_cancel poly_plus_rightE)

lemma map_poly_plus:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b"
  shows "map_poly f (p + q) = map_poly f p + map_poly f q"
  by (rule Polynomial.poly_eqI) (simp add: coeff_map_poly assms)

lemma map_poly_minus:
  assumes "f 0 = 0" and "\<And>a b. f (a - b) = f a - f b"
  shows "map_poly f (p - q) = map_poly f p - map_poly f q"
  by (rule Polynomial.poly_eqI) (simp add: coeff_map_poly assms)

lemma map_poly_sum:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b"
  shows "map_poly f (sum g A) = (\<Sum>a\<in>A. map_poly f (g a))"
  by (induct A rule: infinite_finite_induct) (simp_all add: map_poly_plus assms)

lemma map_poly_times:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b" and "\<And>a b. f (a * b) = f a * f b"
  shows "map_poly f (p * q) = map_poly f p * map_poly f q"
proof (induct p)
  case 0
  show ?case by simp
next
  case (pCons c p)
  show ?case by (simp add: assms map_poly_plus map_poly_smult map_poly_pCons pCons)
qed

lemma poly_Fract:
  assumes "set (Polynomial.coeffs p) \<subseteq> range (\<lambda>x. Fract x 1)"
  obtains q m where "poly p (Fract a b) = Fract q (b ^ m)"
  using assms
proof (induct p arbitrary: thesis)
  case 0
  have "poly 0 (Fract a b) = Fract 0 (b ^ 1)" by (simp add: fract_collapse)
  thus ?case by (rule 0)
next
  case (pCons c p)
  from pCons.hyps(1) have "insert c (set (Polynomial.coeffs p)) = set (Polynomial.coeffs (pCons c p))"
    by auto
  with pCons.prems(2) have "c \<in> range (\<lambda>x. Fract x 1)" and "set (Polynomial.coeffs p) \<subseteq> range (\<lambda>x. Fract x 1)"
    by blast+
  from this(2) obtain q0 m0 where poly_p: "poly p (Fract a b) = Fract q0 (b ^ m0)"
    using pCons.hyps(2) by blast
  from \<open>c \<in> _\<close> obtain c0 where c: "c = Fract c0 1" ..
  show ?case
  proof (cases "b = 0")
    case True
    hence "poly (pCons c p) (Fract a b) = Fract c0 (b ^ 0)" by (simp add: c fract_collapse)
    thus ?thesis by (rule pCons.prems)
  next
    case False
    hence "poly (pCons c p) (Fract a b) = Fract (c0 * b ^ Suc m0 + a * q0) (b ^ Suc m0)"
      by (simp add: poly_p c)
    thus ?thesis by (rule pCons.prems)
  qed
qed

lemma (in ordered_term) lt_sum_le_Max: "lt (sum f A) \<preceq>\<^sub>t ord_term_lin.Max {lt (f a) | a. a \<in> A}"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  thus ?case by (simp add: min_term_min)
next
  case empty
  thus ?case by (simp add: min_term_min)
next
  case (insert a A)
  show ?case
  proof (cases "A = {}")
    case True
    thus ?thesis by simp
  next
    case False
    from insert.hyps(1, 2) have "lt (sum f (insert a A)) = lt (f a + sum f A)" by simp
    also have "\<dots> \<preceq>\<^sub>t ord_term_lin.max (lt (f a)) (lt (sum f A))" by (rule lt_plus_le_max)
    also have "\<dots> \<preceq>\<^sub>t ord_term_lin.max (lt (f a)) (ord_term_lin.Max {lt (f a) |a. a \<in> A})"
      using insert.hyps(3) ord_term_lin.max.mono by blast
    also from insert.hyps(1) False have "\<dots> = ord_term_lin.Max (insert (lt (f a)) {lt (f x) |x. x \<in> A})"
      by simp
    also have "\<dots> = ord_term_lin.Max {lt (f x) |x. x \<in> insert a A}"
      by (rule arg_cong[where f=ord_term_lin.Max]) blast
    finally show ?thesis .
  qed
qed

subsection \<open>Ideals and Varieties\<close>

definition variety_of :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> ('x \<Rightarrow> 'a::comm_semiring_1) set"
  where "variety_of F = {a. \<forall>f\<in>F. poly_eval a f = 0}"

definition ideal_of :: "('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  where "ideal_of A = {f. \<forall>a\<in>A. poly_eval a f = 0}"

abbreviation "\<V> \<equiv> variety_of"
abbreviation "\<I> \<equiv> ideal_of"

lemma variety_ofI: "(\<And>f. f \<in> F \<Longrightarrow> poly_eval a f = 0) \<Longrightarrow> a \<in> \<V> F"
  by (simp add: variety_of_def)

lemma variety_ofI_alt: "poly_eval a ` F \<subseteq> {0} \<Longrightarrow> a \<in> \<V> F"
  by (auto intro: variety_ofI)

lemma variety_ofD: "a \<in> \<V> F \<Longrightarrow> f \<in> F \<Longrightarrow> poly_eval a f = 0"
  by (simp add: variety_of_def)

lemma variety_of_empty [simp]: "\<V> {} = UNIV"
  by (simp add: variety_of_def)

lemma variety_of_UNIV [simp]: "\<V> UNIV = {}"
  by (metis (mono_tags, lifting) Collect_empty_eq UNIV_I one_neq_zero poly_eval_one variety_of_def)

lemma variety_of_antimono: "F \<subseteq> G \<Longrightarrow> \<V> G \<subseteq> \<V> F"
  by (auto simp: variety_of_def)

lemma variety_of_ideal [simp]: "\<V> (ideal F) = \<V> F"
proof
  show "\<V> (ideal F) \<subseteq> \<V> F" by (intro variety_of_antimono ideal.span_superset)
next
  show "\<V> F \<subseteq> \<V> (ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F" and "f \<in> ideal F"
    from this(2) show "poly_eval a f = 0"
    proof (induct f rule: ideal.span_induct_alt)
      case base
      show ?case by simp
    next
      case (step c f g)
      with \<open>a \<in> \<V> F\<close> show ?case by (auto simp: poly_eval_plus poly_eval_times dest: variety_ofD)
    qed
  qed
qed

lemma ideal_ofI: "(\<And>a. a \<in> A \<Longrightarrow> poly_eval a f = 0) \<Longrightarrow> f \<in> \<I> A"
  by (simp add: ideal_of_def)

lemma ideal_ofD: "f \<in> \<I> A \<Longrightarrow> a \<in> A \<Longrightarrow> poly_eval a f = 0"
  by (simp add: ideal_of_def)

lemma ideal_of_empty [simp]: "\<I> {} = UNIV"
  by (simp add: ideal_of_def)

lemma ideal_of_antimono: "A \<subseteq> B \<Longrightarrow> \<I> B \<subseteq> \<I> A"
  by (auto simp: ideal_of_def)

lemma ideal_ideal_of [simp]: "ideal (\<I> A) = \<I> A"
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  show "0 \<in> \<I> A" by (rule ideal_ofI) simp
next
  fix f g
  assume "f \<in> \<I> A"
  hence f: "poly_eval a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  assume "g \<in> \<I> A"
  hence g: "poly_eval a g = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "f + g \<in> \<I> A" by (rule ideal_ofI) (simp add: poly_eval_plus f g)
next
  fix c f
  assume "f \<in> \<I> A"
  hence f: "poly_eval a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "c * f \<in> \<I> A" by (rule ideal_ofI) (simp add: poly_eval_times f)
qed

lemma ideal_of_UN: "\<I> (\<Union> (A ` J)) = (\<Inter>j\<in>J. \<I> (A j))"
proof (intro set_eqI iffI ideal_ofI INT_I)
  fix p j a
  assume "p \<in> \<I> (\<Union> (A ` J))"
  assume "j \<in> J" and "a \<in> A j"
  hence "a \<in> \<Union> (A ` J)" ..
  with \<open>p \<in> _\<close> show "poly_eval a p = 0" by (rule ideal_ofD)
next
  fix p a
  assume "a \<in> \<Union> (A ` J)"
  then obtain j where "j \<in> J" and "a \<in> A j" ..
  assume "p \<in> (\<Inter>j\<in>J. \<I> (A j))"
  hence "p \<in> \<I> (A j)" using \<open>j \<in> J\<close> ..
  thus "poly_eval a p = 0" using \<open>a \<in> A j\<close> by (rule ideal_ofD)
qed

corollary ideal_of_Un: "\<I> (A \<union> B) = \<I> A \<inter> \<I> B"
  using ideal_of_UN[of id "{A, B}"] by simp

lemma variety_of_ideal_of_variety [simp]: "\<V> (\<I> (\<V> F)) = \<V> F" (is "_ = ?V")
proof
  have "F \<subseteq> \<I> (\<V> F)" by (auto intro!: ideal_ofI dest: variety_ofD)
  thus "\<V> (\<I> ?V) \<subseteq> ?V" by (rule variety_of_antimono)
next
  show "?V \<subseteq> \<V> (\<I> ?V)" by (auto intro!: variety_ofI dest: ideal_ofD)
qed

lemma ideal_of_inj_on: "inj_on \<I> (range (\<V>::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix A B :: "('x \<Rightarrow> 'a) set"
  assume "A \<in> range \<V>"
  then obtain F where A: "A = \<V> F" ..
  assume "B \<in> range \<V>"
  then obtain G where B: "B = \<V> G" ..
  assume "\<I> A = \<I> B"
  hence "\<V> (\<I> A) = \<V> (\<I> B)" by simp
  thus "A = B" by (simp add: A B)
qed

lemma ideal_of_variety_of_ideal [simp]: "\<I> (\<V> (\<I> A)) = \<I> A" (is "_ = ?I")
proof
  have "A \<subseteq> \<V> (\<I> A)" by (auto intro!: variety_ofI dest: ideal_ofD)
  thus "\<I> (\<V> ?I) \<subseteq> ?I" by (rule ideal_of_antimono)
next
  show "?I \<subseteq> \<I> (\<V> ?I)" by (auto intro!: ideal_ofI dest: variety_ofD)
qed

lemma variety_of_inj_on: "inj_on \<V> (range (\<I>::('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix F G :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  assume "F \<in> range \<I>"
  then obtain A where F: "F = \<I> A" ..
  assume "G \<in> range \<I>"
  then obtain B where G: "G = \<I> B" ..
  assume "\<V> F = \<V> G"
  hence "\<I> (\<V> F) = \<I> (\<V> G)" by simp
  thus "F = G" by (simp add: F G)
qed

lemma image_map_indets_ideal_of:
  assumes "inj f"
  shows "map_indets f ` \<I> A = \<I> ((\<lambda>a. a \<circ> f) -` (A::('x \<Rightarrow> 'a::comm_semiring_1) set)) \<inter> P[range f]"
proof -
  {
    fix p and a::"'x \<Rightarrow> 'a"
    assume "\<forall>a\<in>(\<lambda>a. a \<circ> f) -` A. poly_eval (a \<circ> f) p = 0"
    hence eq: "poly_eval (a \<circ> f) p = 0" if "a \<circ> f \<in> A" for a using that by simp
    have "the_inv f \<circ> f = id" by (rule ext) (simp add: assms the_inv_f_f)
    hence a: "a = a \<circ> the_inv f \<circ> f" by (simp add: comp_assoc)
    moreover assume "a \<in> A"
    ultimately have "(a \<circ> the_inv f) \<circ> f \<in> A" by simp
    hence "poly_eval ((a \<circ> the_inv f) \<circ> f) p = 0" by (rule eq)
    hence "poly_eval a p = 0" by (simp flip: a)
  }
  thus ?thesis
    by (auto simp: ideal_of_def poly_eval_map_indets simp flip: range_map_indets intro!: imageI)
qed

lemma variety_of_map_indets: "\<V> (map_indets f ` F) = (\<lambda>a. a \<circ> f) -` \<V> F"
  by (auto simp: variety_of_def poly_eval_map_indets)

subsection \<open>Radical Ideals\<close>

definition radical :: "'a::monoid_mult set \<Rightarrow> 'a set" ("\<surd>(_)" [999] 999)
  where "radical F = {f. \<exists>m. f ^ m \<in> F}"

lemma radicalI: "f ^ m \<in> F \<Longrightarrow> f \<in> \<surd>F"
  by (auto simp: radical_def)

lemma radicalE:
  assumes "f \<in> \<surd>F"
  obtains m where "f ^ m \<in> F"
  using assms by (auto simp: radical_def)

lemma radical_empty [simp]: "\<surd>{} = {}"
  by (simp add: radical_def)

lemma radical_UNIV [simp]: "\<surd>UNIV = UNIV"
  by (simp add: radical_def)

lemma radical_ideal_eq_UNIV_iff: "\<surd>ideal F = UNIV \<longleftrightarrow> ideal F = UNIV"
proof
  assume "\<surd>ideal F = UNIV"
  hence "1 \<in> \<surd>ideal F" by simp
  then obtain m where "1 ^ m \<in> ideal F" by (rule radicalE)
  thus "ideal F = UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
qed simp

lemma zero_in_radical_ideal [simp]: "0 \<in> \<surd>ideal F"
proof (rule radicalI)
  show "0 ^ 1 \<in> ideal F" by (simp add: ideal.span_zero)
qed

lemma radical_mono: "F \<subseteq> G \<Longrightarrow> \<surd>F \<subseteq> \<surd>G"
  by (auto elim!: radicalE intro: radicalI)

lemma radical_superset: "F \<subseteq> \<surd>F"
proof
  fix f
  assume "f \<in> F"
  hence "f ^ 1 \<in> F" by simp
  thus "f \<in> \<surd>F" by (rule radicalI)
qed

lemma radical_idem [simp]: "\<surd>\<surd>F = \<surd>F"
proof
  show "\<surd>\<surd>F \<subseteq> \<surd>F" by (auto elim!: radicalE intro: radicalI simp flip: power_mult)
qed (fact radical_superset)

lemma radical_Int_subset: "\<surd>(A \<inter> B) \<subseteq> \<surd>A \<inter> \<surd>B"
  by (auto intro: radicalI elim: radicalE)

lemma radical_ideal_Int: "\<surd>(ideal F \<inter> ideal G) = \<surd>ideal F \<inter> \<surd>ideal G"
  using radical_Int_subset
proof (rule subset_antisym)
  show "\<surd>ideal F \<inter> \<surd>ideal G \<subseteq> \<surd>(ideal F \<inter> ideal G)"
  proof
    fix p
    assume "p \<in> \<surd>ideal F \<inter> \<surd>ideal G"
    hence "p \<in> \<surd>ideal F" and "p \<in> \<surd>ideal G" by simp_all
    from this(1) obtain m1 where p1: "p ^ m1 \<in> ideal F" by (rule radicalE)
    from \<open>p \<in> \<surd>ideal G\<close> obtain m2 where "p ^ m2 \<in> ideal G" by (rule radicalE)
    hence "p ^ m1 * p ^ m2 \<in> ideal G" by (rule ideal.span_scale)
    moreover from p1 have "p ^ m2 * p ^ m1 \<in> ideal F" by (rule ideal.span_scale)
    ultimately have "p ^ (m1 + m2) \<in> ideal F \<inter> ideal G" by (simp add: power_add mult.commute)
    thus "p \<in> \<surd>(ideal F \<inter> ideal G)" by (rule radicalI)
  qed
qed

lemma ideal_radical_ideal [simp]: "ideal (\<surd>ideal F) = \<surd>ideal F" (is "_ = ?R")
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  have "0 ^ 1 \<in> ideal F" by (simp add: ideal.span_zero)
  thus "0 \<in> ?R" by (rule radicalI)
next
  fix a b
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  have a: "a ^ k \<in> ideal F" if "m \<le> k" for k
  proof -
    from \<open>a ^ m \<in> _\<close> have "a ^ (k - m + m) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  assume "b \<in> ?R"
  then obtain n where "b ^ n \<in> ideal F" by (rule radicalE)
  have b: "b ^ k \<in> ideal F" if "n \<le> k" for k
  proof -
    from \<open>b ^ n \<in> _\<close> have "b ^ (k - n + n) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  have "(a + b) ^ (m + n) \<in> ideal F" unfolding binomial_ring
  proof (rule ideal.span_sum)
    fix k
    show "of_nat (m + n choose k) * a ^ k * b ^ (m + n - k) \<in> ideal F"
    proof (cases "k \<le> m")
      case True
      hence "n \<le> m + n - k" by simp
      hence "b ^ (m + n - k) \<in> ideal F" by (rule b)
      thus ?thesis by (rule ideal.span_scale)
    next
      case False
      hence "m \<le> k" by simp
      hence "a ^ k \<in> ideal F" by (rule a)
      hence "of_nat (m + n choose k) * b ^ (m + n - k) * a ^ k \<in> ideal F" by (rule ideal.span_scale)
      thus ?thesis by (simp only: ac_simps)
    qed
  qed
  thus "a + b \<in> ?R" by (rule radicalI)
next
  fix c a
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  hence "(c * a) ^ m \<in> ideal F" by (simp only: power_mult_distrib ideal.span_scale)
  thus "c * a \<in> ?R" by (rule radicalI)
qed

lemma radical_ideal_of [simp]: "\<surd>\<I> A = \<I> (A::(_ \<Rightarrow> _::semiring_1_no_zero_divisors) set)"
proof
  show "\<surd>\<I> A \<subseteq> \<I> A" by (auto elim!: radicalE dest!: ideal_ofD intro!: ideal_ofI simp: poly_eval_power)
qed (fact radical_superset)

lemma variety_of_radical_ideal [simp]: "\<V> (\<surd>ideal F) = \<V> (F::(_ \<Rightarrow>\<^sub>0 _::semiring_1_no_zero_divisors) set)"
proof
  have "F \<subseteq> ideal F" by (rule ideal.span_superset)
  also have "\<dots> \<subseteq> \<surd>ideal F" by (rule radical_superset)
  finally show "\<V> (\<surd>ideal F) \<subseteq> \<V> F" by (rule variety_of_antimono)
next
  show "\<V> F \<subseteq> \<V> (\<surd>ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F"
    hence "a \<in> \<V> (ideal F)" by simp
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    with \<open>a \<in> \<V> (ideal F)\<close> have "poly_eval a (f ^ m) = 0" by (rule variety_ofD)
    thus "poly_eval a f = 0" by (simp add: poly_eval_power)
  qed
qed

lemma image_map_indets_radical:
  assumes "inj f"
  shows "map_indets f ` \<surd>F = \<surd>(map_indets f ` (F::(_ \<Rightarrow>\<^sub>0 'a::comm_ring_1) set)) \<inter> P[range f]"
proof
  show "map_indets f ` \<surd>F \<subseteq> \<surd>(map_indets f ` F) \<inter> P[range f]"
    by (auto simp: radical_def simp flip: map_indets_power range_map_indets intro!: imageI)
next
  show "\<surd>(map_indets f ` F) \<inter> P[range f] \<subseteq> map_indets f ` \<surd>F"
  proof
    fix p
    assume "p \<in> \<surd>(map_indets f ` F) \<inter> P[range f]"
    hence "p \<in> \<surd>(map_indets f ` F)" and "p \<in> range (map_indets f)"
      by (simp_all add: range_map_indets)
    from this(1) obtain m where "p ^ m \<in> map_indets f ` F" by (rule radicalE)
    then obtain q where "q \<in> F" and p_m: "p ^ m = map_indets f q" ..
    from assms obtain g where "g \<circ> f = id" and "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a)"
      by (rule map_indets_inverseE)
    hence eq: "map_indets g (map_indets f p') = p'" for p'::"_ \<Rightarrow>\<^sub>0 'a"
      by (simp add: pointfree_idE)
    from p_m have "map_indets g (p ^ m) = map_indets g (map_indets f q)" by (rule arg_cong)
    hence "(map_indets g p) ^ m = q" by (simp add: eq)
    from \<open>p \<in> range _\<close> obtain p' where "p = map_indets f p'" ..
    hence "p = map_indets f (map_indets g p)" by (simp add: eq)
    moreover have "map_indets g p \<in> \<surd>F"
    proof (rule radicalI)
      from \<open>q \<in> F\<close> show "map_indets g p ^ m \<in> F" by (simp add: p_m eq flip: map_indets_power)
    qed
    ultimately show "p \<in> map_indets f ` \<surd>F" by (rule image_eqI)
  qed
qed

subsection \<open>Geometric Version of the Nullstellensatz\<close>

lemma weak_Nullstellensatz_aux_1:
  assumes "\<And>i. i \<in> I \<Longrightarrow> g i \<in> ideal B"
  obtains c where "c \<in> ideal B" and "(\<Prod>i\<in>I. (f i + g i) ^ m i) = (\<Prod>i\<in>I. f i ^ m i) + c"
  using assms
proof (induct I arbitrary: thesis rule: infinite_finite_induct)
  case (infinite I)
  from ideal.span_zero show ?case by (rule infinite) (simp add: infinite(1))
next
  case empty
  from ideal.span_zero show ?case by (rule empty) simp
next
  case (insert j I)
  have "g i \<in> ideal B" if "i \<in> I" for i by (rule insert.prems) (simp add: that)
  with insert.hyps(3) obtain c where c: "c \<in> ideal B"
    and 1: "(\<Prod>i\<in>I. (f i + g i) ^ m i) = (\<Prod>i\<in>I. f i ^ m i) + c" by blast
  define k where "k = m j"
  obtain d where 2: "(f j + g j) ^ m j = f j ^ m j + d * g j" unfolding k_def[symmetric]
  proof (induct k arbitrary: thesis)
    case 0
    have "(f j + g j) ^ 0 = f j ^ 0 + 0 * g j" by simp
    thus ?case by (rule 0)
  next
    case (Suc k)
    obtain d where "(f j + g j) ^ k = f j ^ k + d * g j" by (rule Suc.hyps)
    hence "(f j + g j) ^ Suc k = (f j ^ k + d * g j) * (f j + g j)" by simp
    also have "\<dots> = f j ^ Suc k + (f j ^ k + d * (f j + g j)) * g j" by (simp add: algebra_simps)
    finally show ?case by (rule Suc.prems)
  qed
  from c have *: "f j ^ m j * c + (((\<Prod>i\<in>I. f i ^ m i) + c) * d) * g j \<in> ideal B" (is "?c \<in> _")
    by (intro ideal.span_add ideal.span_scale insert.prems insertI1)
  from insert.hyps(1, 2) have "(\<Prod>i\<in>insert j I. (f i + g i) ^ m i) =
                                (f j ^ m j + d * g j) * ((\<Prod>i\<in>I. f i ^ m i) + c)"
    by (simp add: 1 2)
  also from insert.hyps(1, 2) have "\<dots> = (\<Prod>i\<in>insert j I. f i ^ m i) + ?c" by (simp add: algebra_simps)
  finally have "(\<Prod>i\<in>insert j I. (f i + g i) ^ m i) = (\<Prod>i\<in>insert j I. f i ^ m i) + ?c" .
  with * show ?case by (rule insert.prems)
qed

lemma weak_Nullstellensatz_aux_2:
  assumes "finite X" and "F \<subseteq> P[insert x X]" and "X \<subseteq> {..<x::'x::{countable,linorder}}"
    and "1 \<notin> ideal F" and "ideal F \<inter> P[{x}] \<subseteq> {0}"
  obtains a::"'a::alg_closed_field" where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
proof -
  let ?x = "monomial 1 (Poly_Mapping.single x 1)"
  from assms(3) have "x \<notin> X" by blast
  hence eq1: "insert x X - {x} = X" and eq2: "insert x X - X = {x}" by blast+

  interpret i: pm_powerprod lex_pm "lex_pm_strict::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _"
    unfolding lex_pm_def lex_pm_strict_def
    by standard (simp_all add: lex_pm_zero_min lex_pm_plus_monotone flip: lex_pm_def)
  have lpp_focus: "i.lpp (focus X g) = except (i.lpp g) {x}" if "g \<in> P[insert x X]" for g::"_ \<Rightarrow>\<^sub>0 'a"
  proof (cases "g = 0")
    case True
    thus ?thesis by simp
  next
    case False
    have keys_focus_g: "keys (focus X g) = (\<lambda>t. except t {x}) ` keys g"
      unfolding keys_focus using refl
    proof (rule image_cong)
      fix t
      assume "t \<in> keys g"
      also from that have "\<dots> \<subseteq> .[insert x X]" by (rule PolysD)
      finally have "keys t \<subseteq> insert x X" by (rule PPsD)
      hence "except t (- X) = except t (insert x X \<inter> - X)"
        by (metis (no_types, lifting) Int_commute except_keys_Int inf.orderE inf_left_commute)
      also from \<open>x \<notin> X\<close> have "insert x X \<inter> - X = {x}" by simp
      finally show "except t (- X) = except t {x}" .
    qed
    show ?thesis
    proof (rule i.punit.lt_eqI_keys)
      from False have "i.lpp g \<in> keys g" by (rule i.punit.lt_in_keys)
      thus "except (i.lpp g) {x} \<in> keys (focus X g)" unfolding keys_focus_g by (rule imageI)

      fix t
      assume "t \<in> keys (focus X g)"
      then obtain s where "s \<in> keys g" and t: "t = except s {x}" unfolding keys_focus_g ..
      from this(1) have "lex_pm s (i.lpp g)" by (rule i.punit.lt_max_keys)
      moreover have "keys s \<union> keys (i.lpp g) \<subseteq> {..x}"
      proof (rule Un_least)
        from \<open>g \<in> P[_]\<close> have "keys g \<subseteq> .[insert x X]" by (rule PolysD)
        with \<open>s \<in> keys g\<close> have "s \<in> .[insert x X]" ..
        hence "keys s \<subseteq> insert x X" by (rule PPsD)
        thus "keys s \<subseteq> {..x}" using assms(3) by auto

        from \<open>i.lpp g \<in> keys g\<close> \<open>keys g \<subseteq> _\<close> have "i.lpp g \<in> .[insert x X]" ..
        hence "keys (i.lpp g) \<subseteq> insert x X" by (rule PPsD)
        thus "keys (i.lpp g) \<subseteq> {..x}" using assms(3) by auto
      qed
      ultimately show "lex_pm t (except (i.lpp g) {x})" unfolding t by (rule lex_pm_except_max)
    qed
  qed

  define G where "G = i.punit.reduced_GB F"
  from assms(1) have "finite (insert x X)" by simp
  hence fin_G: "finite G" and G_sub: "G \<subseteq> P[insert x X]" and ideal_G: "ideal G = ideal F"
    and "0 \<notin> G" and G_isGB: "i.punit.is_Groebner_basis G" unfolding G_def using assms(2)
    by (rule i.finite_reduced_GB_Polys, rule i.reduced_GB_Polys, rule i.reduced_GB_ideal_Polys,
        rule i.reduced_GB_nonzero_Polys, rule i.reduced_GB_is_GB_Polys)
  define G' where "G' = focus X ` G"
  from fin_G \<open>0 \<notin> G\<close> have fin_G': "finite G'" and "0 \<notin> G'" by (auto simp: G'_def)
  have G'_sub: "G' \<subseteq> P[X]" by (auto simp: G'_def intro: focus_in_Polys)
  define G'' where "G'' = i.lcf ` G'"
  from \<open>0 \<notin> G'\<close> have "0 \<notin> G''" by (auto simp: G''_def i.punit.lc_eq_zero_iff)
  have lookup_focus_in: "lookup (focus X g) t \<in> P[{x}]" if "g \<in> G" for g t
  proof -
    have "lookup (focus X g) t \<in> range (lookup (focus X g))" by (rule rangeI)
    from that G_sub have "g \<in> P[insert x X]" ..
    hence "range (lookup (focus X g)) \<subseteq> P[insert x X - X]" by (rule focus_coeffs_subset_Polys')
    with \<open>_ \<in> range _\<close> have "lookup (focus X g) t \<in> P[insert x X - X]" ..
    also have "insert x X - X = {x}" by (simp only: eq2)
    finally show ?thesis .
  qed
  hence lcf_in: "i.lcf (focus X g) \<in> P[{x}]" if "g \<in> G" for g
    unfolding i.punit.lc_def using that by blast
  have G''_sub: "G'' \<subseteq> P[{x}]"
  proof
    fix c
    assume "c \<in> G''"
    then obtain g' where "g' \<in> G'" and c: "c = i.lcf g'" unfolding G''_def ..
    from \<open>g' \<in> G'\<close> obtain g where "g \<in> G" and g': "g' = focus X g" unfolding G'_def ..
    from this(1) show "c \<in> P[{x}]" unfolding c g' by (rule lcf_in)
  qed
  define P where "P = poly_of_pm x ` G''"
  from fin_G' have fin_P: "finite P" by (simp add: P_def G''_def)
  have "0 \<notin> P"
  proof
    assume "0 \<in> P"
    then obtain g'' where "g'' \<in> G''" and "0 = poly_of_pm x g''" unfolding P_def ..
    from this(2) have *: "keys g'' \<inter> .[{x}] = {}" by (simp add: poly_of_pm_eq_zero_iff)
    from \<open>g'' \<in> G''\<close> G''_sub have "g'' \<in> P[{x}]" ..
    hence "keys g'' \<subseteq> .[{x}]" by (rule PolysD)
    with * have "keys g'' = {}" by blast
    with \<open>g'' \<in> G''\<close> \<open>0 \<notin> G''\<close> show False by simp
  qed
  define Z where "Z = (\<Union>p\<in>P. {z. poly p z = 0})"
  have "finite Z" unfolding Z_def using fin_P
  proof (rule finite_UN_I)
    fix p
    assume "p \<in> P"
    with \<open>0 \<notin> P\<close> have "p \<noteq> 0" by blast
    thus "finite {z. poly p z = 0}" by (rule poly_roots_finite)
  qed
  with infinite_UNIV[where 'a='a] have "- Z \<noteq> {}" using finite_compl by fastforce
  then obtain a where "a \<notin> Z" by blast

  have a_nz: "poly_eval (\<lambda>_. a) (i.lcf (focus X g)) \<noteq> 0" if "g \<in> G" for g
  proof -
    from that G_sub have "g \<in> P[insert x X]" ..
    have "poly_eval (\<lambda>_. a) (i.lcf (focus X g)) = poly (poly_of_pm x (i.lcf (focus X g))) a"
      by (rule sym, intro poly_eq_poly_eval' lcf_in that)
    moreover have "poly_of_pm x (i.lcf (focus X g)) \<in> P"
      by (auto simp: P_def G''_def G'_def that intro!: imageI)
    ultimately show ?thesis using \<open>a \<notin> Z\<close> by (simp add: Z_def)
  qed

  let ?e = "poly_eval (\<lambda>_. monomial a 0)"
  have lookup_e_focus: "lookup (?e (focus {x} g)) t = poly_eval (\<lambda>_. a) (lookup (focus X g) t)"
    if "g \<in> P[insert x X]" for g t
  proof -
    have "focus (- {x}) g = focus (- {x} \<inter> insert x X) g" by (rule sym) (rule focus_Int, fact)
    also have "\<dots> = focus X g" by (simp add: Int_commute eq1 flip: Diff_eq)
    finally show ?thesis by (simp add: lookup_poly_eval_focus)
  qed
  have lpp_e_focus: "i.lpp (?e (focus {x} g)) = except (i.lpp g) {x}" if "g \<in> G" for g
  proof (rule i.punit.lt_eqI_keys)
    from that G_sub have "g \<in> P[insert x X]" ..
    hence "lookup (?e (focus {x} g)) (except (i.lpp g) {x}) = poly_eval (\<lambda>_. a) (i.lcf (focus X g))"
      by (simp only: lookup_e_focus lpp_focus i.punit.lc_def)
    also from that have "\<dots> \<noteq> 0" by (rule a_nz)
    finally show "except (i.lpp g) {x} \<in> keys (?e (focus {x} g))" by (simp add: in_keys_iff)

    fix t
    assume "t \<in> keys (?e (focus {x} g))"
    hence "0 \<noteq> lookup (?e (focus {x} g)) t" by (simp add: in_keys_iff)
    also from \<open>g \<in> P[_]\<close> have "lookup (?e (focus {x} g)) t = poly_eval (\<lambda>_. a) (lookup (focus X g) t)"
      by (rule lookup_e_focus)
    finally have "t \<in> keys (focus X g)" by (auto simp flip: lookup_not_eq_zero_eq_in_keys)
    hence "lex_pm t (i.lpp (focus X g))" by (rule i.punit.lt_max_keys)
    with \<open>g \<in> P[_]\<close> show "lex_pm t (except (i.lpp g) {x})" by (simp only: lpp_focus)
  qed

  show ?thesis
  proof
    define G3 where "G3 = ?e ` focus {x} ` G"
    have "G3 \<subseteq> P[X]"
    proof
      fix h
      assume "h \<in> G3"
      then obtain h0 where "h0 \<in> G" and h: "h = ?e (focus {x} h0)" by (auto simp: G3_def)
      from this(1) G_sub have "h0 \<in> P[insert x X]" ..
      hence "h \<in> P[insert x X - {x}]" unfolding h by (rule poly_eval_focus_in_Polys)
      thus "h \<in> P[X]" by (simp only: eq1)
    qed
    from fin_G have "finite G3" by (simp add: G3_def)
    
    have "ideal G3 \<inter> P[- {x}] = ?e ` focus {x} ` ideal G"
      by (simp only: G3_def image_poly_eval_focus_ideal)
    also have "\<dots> = ideal (?e ` focus {x} ` F) \<inter> P[- {x}]"
      by (simp only: ideal_G image_poly_eval_focus_ideal)
    finally have eq3: "ideal G3 \<inter> P[- {x}] = ideal (?e ` focus {x} ` F) \<inter> P[- {x}]" .
    from assms(1) \<open>G3 \<subseteq> P[X]\<close> \<open>finite G3\<close> have G3_isGB: "i.punit.is_Groebner_basis G3"
    proof (rule i.punit.isGB_I_spoly_rep[simplified, OF dickson_grading_varnum,
                                          where m=0, simplified i.dgrad_p_set_varnum])
      fix g1 g2
      assume "g1 \<in> G3"
      then obtain g1' where "g1' \<in> G" and g1: "g1 = ?e (focus {x} g1')"
        unfolding G3_def by blast
      from this(1) have lpp1: "i.lpp g1 = except (i.lpp g1') {x}" unfolding g1 by (rule lpp_e_focus)
      from \<open>g1' \<in> G\<close> G_sub have "g1' \<in> P[insert x X]" ..
      assume "g2 \<in> G3"
      then obtain g2' where "g2' \<in> G" and g2: "g2 = ?e (focus {x} g2')"
        unfolding G3_def by blast
      from this(1) have lpp2: "i.lpp g2 = except (i.lpp g2') {x}" unfolding g2 by (rule lpp_e_focus)
      from \<open>g2' \<in> G\<close> G_sub have "g2' \<in> P[insert x X]" ..

      define l where "l = lcs (except (i.lpp g1') {x}) (except (i.lpp g2') {x})"
      define c1 where "c1 = i.lcf (focus X g1')"
      define c2 where "c2 = i.lcf (focus X g2')"
      define c where "c = poly_eval (\<lambda>_. a) c1 * poly_eval (\<lambda>_. a) c2"
      define s where "s = c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) g1' -
                          c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) g2'"
      have "c1 \<in> P[{x}]" unfolding c1_def using \<open>g1' \<in> G\<close> by (rule lcf_in)
      hence eval_c1: "poly_eval (\<lambda>_. monomial a 0) (focus {x} c1) = monomial (poly_eval (\<lambda>_. a) c1) 0"
        by (simp add: focus_Polys poly_eval_sum poly_eval_monomial monomial_power_map_scale
                  times_monomial_monomial flip: punit.monomial_prod_sum monomial_sum)
           (simp add: poly_eval_alt)
      have "c2 \<in> P[{x}]" unfolding c2_def using \<open>g2' \<in> G\<close> by (rule lcf_in)
      hence eval_c2: "poly_eval (\<lambda>_. monomial a 0) (focus {x} c2) = monomial (poly_eval (\<lambda>_. a) c2) 0"
        by (simp add: focus_Polys poly_eval_sum poly_eval_monomial monomial_power_map_scale
                  times_monomial_monomial flip: punit.monomial_prod_sum monomial_sum)
           (simp add: poly_eval_alt)

      assume spoly_nz: "i.punit.spoly g1 g2 \<noteq> 0"
      assume "g1 \<noteq> 0" and "g2 \<noteq> 0"
      hence "g1' \<noteq> 0" and "g2' \<noteq> 0" by (auto simp: g1 g2)
      have c1_nz: "poly_eval (\<lambda>_. a) c1 \<noteq> 0" unfolding c1_def using \<open>g1' \<in> G\<close> by (rule a_nz)
      moreover have c2_nz: "poly_eval (\<lambda>_. a) c2 \<noteq> 0" unfolding c2_def using \<open>g2' \<in> G\<close> by (rule a_nz)
      ultimately have "c \<noteq> 0" by (simp add: c_def)
      hence "inverse c \<noteq> 0" by simp
      from \<open>g1' \<in> P[_]\<close> have "except (i.lpp g1') {x} \<in> .[insert x X - {x}]"
        by (intro PPs_closed_except' i.PPs_closed_lpp)
      moreover from \<open>g2' \<in> P[_]\<close> have "except (i.lpp g2') {x} \<in> .[insert x X - {x}]"
        by (intro PPs_closed_except' i.PPs_closed_lpp)
      ultimately have "l \<in> .[insert x X - {x}]" unfolding l_def by (rule PPs_closed_lcs)
      hence "l \<in> .[X]" by (simp only: eq1)
      hence "l \<in> .[insert x X]" by rule (rule PPs_mono, blast)
      moreover from \<open>c1 \<in> P[{x}]\<close> have "c1 \<in> P[insert x X]" by rule (intro Polys_mono, simp)
      moreover from \<open>c2 \<in> P[{x}]\<close> have "c2 \<in> P[insert x X]" by rule (intro Polys_mono, simp)
      ultimately have "s \<in> P[insert x X]" using \<open>g1' \<in> P[_]\<close> \<open>g2' \<in> P[_]\<close> unfolding s_def
        by (intro Polys_closed_minus Polys_closed_times Polys_closed_monom_mult PPs_closed_minus)
      have "s \<in> ideal G" unfolding s_def times_monomial_left[symmetric]
        by (intro ideal.span_diff ideal.span_scale ideal.span_base \<open>g1' \<in> G\<close> \<open>g2' \<in> G\<close>)
      with G_isGB have "(i.punit.red G)\<^sup>*\<^sup>* s 0" by (rule i.punit.GB_imp_zero_reducibility[simplified])
      with \<open>finite (insert x X)\<close> G_sub fin_G \<open>s \<in> P[_]\<close>
      obtain q0 where 1: "s = 0 + (\<Sum>g\<in>G. q0 g * g)" and 2: "\<And>g. q0 g \<in> P[insert x X]"
        and 3: "\<And>g. lex_pm (i.lpp (q0 g * g)) (i.lpp s)"
        by (rule i.punit.red_rtrancl_repE[simplified, OF dickson_grading_varnum, where m=0,
                                            simplified i.dgrad_p_set_varnum]) blast

      define q where "q = (\<lambda>g. inverse c \<cdot> (\<Sum>h\<in>{y\<in>G. ?e (focus {x} y) = g}. ?e (focus {x} (q0 h))))"

      have eq4: "?e (focus {x} (monomial 1 (l - t))) = monomial 1 (l - t)" for t
      proof -
        have "focus {x} (monomial (1::'a) (l - t)) = monomial (monomial 1 (l - t)) 0"
        proof (intro focus_Polys_Compl Polys_closed_monomial PPs_closed_minus)
          from \<open>x \<notin> X\<close> have "X \<subseteq> - {x}" by simp
          hence ".[X] \<subseteq> .[- {x}]" by (rule PPs_mono)
          with \<open>l \<in> .[X]\<close> show "l \<in> .[- {x}]" ..
        qed
        thus ?thesis by (simp add: poly_eval_monomial)
      qed
      from c2_nz have eq5: "inverse c * poly_eval (\<lambda>_. a) c2 = 1 / lookup g1 (i.lpp g1)"
        unfolding lpp1 using \<open>g1' \<in> P[_]\<close>
        by (simp add: c_def mult.assoc divide_inverse_commute g1 lookup_e_focus
                flip: lpp_focus i.punit.lc_def c1_def)
      from c1_nz have eq6: "inverse c * poly_eval (\<lambda>_. a) c1 = 1 / lookup g2 (i.lpp g2)"
        unfolding lpp2 using \<open>g2' \<in> P[_]\<close>
        by (simp add: c_def mult.assoc mult.left_commute[of "inverse (poly_eval (\<lambda>_. a) c1)"]
                    divide_inverse_commute g2 lookup_e_focus flip: lpp_focus i.punit.lc_def c2_def)
      have l_alt: "l = lcs (i.lpp g1) (i.lpp g2)" by (simp only: l_def lpp1 lpp2)
      have spoly_eq: "i.punit.spoly g1 g2 = (inverse c) \<cdot> ?e (focus {x} s)"
        by (simp add: s_def focus_minus focus_times poly_eval_minus poly_eval_times eval_c1 eval_c2
                      eq4 eq5 eq6 map_scale_eq_times times_monomial_monomial right_diff_distrib
                      i.punit.spoly_def Let_def
                 flip: mult.assoc times_monomial_left g1 g2 lpp1 lpp2 l_alt)
      also have "\<dots> = (\<Sum>g\<in>G. inverse c \<cdot> (?e (focus {x} (q0 g)) * ?e (focus {x} g)))"
        by (simp add: 1 focus_sum poly_eval_sum focus_times poly_eval_times map_scale_sum_distrib_left)
      also have "\<dots> = (\<Sum>g\<in>G3. \<Sum>h\<in>{y\<in>G. ?e (focus{x} y) = g}.
                                      inverse c \<cdot> (?e (focus {x} (q0 h)) * ?e (focus {x} h)))"
        unfolding G3_def image_image using fin_G by (rule sum.image_gen)
      also have "\<dots> = (\<Sum>g\<in>G3. inverse c \<cdot> (\<Sum>h\<in>{y\<in>G. ?e (focus{x} y) = g}. ?e (focus {x} (q0 h))) * g)"
        by (intro sum.cong refl) (simp add: map_scale_eq_times sum_distrib_left sum_distrib_right mult.assoc)
      also from refl have "\<dots> = (\<Sum>g\<in>G3. q g * g)" by (rule sum.cong) (simp add: q_def sum_distrib_right)
      finally have "i.punit.spoly g1 g2 = (\<Sum>g\<in>G3. q g * g)" .
      thus "i.punit.spoly_rep (varnum X) 0 G3 g1 g2"
      proof (rule i.punit.spoly_repI[simplified, where m=0 and d="varnum X",
                                        simplified i.dgrad_p_set_varnum])
        fix g
        show "q g \<in> P[X]" unfolding q_def
        proof (intro Polys_closed_map_scale Polys_closed_sum)
          fix g0
          from \<open>q0 g0 \<in> P[insert x X]\<close> have "?e (focus {x} (q0 g0)) \<in> P[insert x X - {x}]"
            by (rule poly_eval_focus_in_Polys)
          thus "?e (focus {x} (q0 g0)) \<in> P[X]" by (simp only: eq1)
        qed

        assume "q g \<noteq> 0 \<and> g \<noteq> 0"
        hence "q g \<noteq> 0" ..
        have "i.lpp (q g * g) = i.lpp (\<Sum>h\<in>{y\<in>G. ?e (focus {x} y) = g}. inverse c \<cdot> ?e (focus {x} (q0 h)) * g)"
          by (simp add: q_def map_scale_sum_distrib_left sum_distrib_right)
        also have "lex_pm \<dots> (i.ordered_powerprod_lin.Max
                {i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g) | h. h \<in> {y\<in>G. ?e (focus {x} y) = g}})"
          (is "lex_pm _ (i.ordered_powerprod_lin.Max ?A)") by (fact i.punit.lt_sum_le_Max)
        also have "lex_pm \<dots> (i.lpp s)"
        proof (rule i.ordered_powerprod_lin.Max.boundedI)
          from fin_G show "finite ?A" by simp
        next
          show "?A \<noteq> {}"
          proof
            assume "?A = {}"
            hence "{h \<in> G. ?e (focus {x} h) = g} = {}" by simp
            hence "q g = 0" by (simp only: q_def sum.empty map_scale_zero_right)
            with \<open>q g \<noteq> 0\<close> show False ..
          qed
        next
          fix t
          assume "t \<in> ?A"
          then obtain h where "h \<in> G" and g[symmetric]: "?e (focus {x} h) = g"
            and "t = i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g)" by blast
          note this(3)
          also have "i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g) =
                      i.lpp (inverse c \<cdot> (?e (focus {x} (q0 h * h))))"
            by (simp only: map_scale_eq_times mult.assoc g poly_eval_times focus_times)
          also from \<open>inverse c \<noteq> 0\<close> have "\<dots> = i.lpp (?e (focus {x} (q0 h * h)))"
            by (rule i.punit.lt_map_scale)
          also have "lex_pm \<dots> (i.lpp (q0 h * h))"
          proof (rule i.punit.lt_le, rule ccontr)
            fix u
            assume "lookup (?e (focus {x} (q0 h * h))) u \<noteq> 0"
            hence "u \<in> keys (?e (focus {x} (q0 h * h)))" by (simp add: in_keys_iff)
            with keys_poly_eval_focus_subset have "u \<in> (\<lambda>v. except v {x}) ` keys (q0 h * h)" ..
            then obtain v where "v \<in> keys (q0 h * h)" and u: "u = except v {x}" ..
            have "lex_pm u (Poly_Mapping.single x (lookup v x) + u)"
              by (metis add.commute add.right_neutral i.plus_monotone_left lex_pm_zero_min)
            also have "\<dots> = v" by (simp only: u flip: plus_except)
            also from \<open>v \<in> _\<close> have "lex_pm v (i.lpp (q0 h * h))" by (rule i.punit.lt_max_keys)
            finally have "lex_pm u (i.lpp (q0 h * h))" .
            moreover assume "lex_pm_strict (i.lpp (q0 h * h)) u"
            ultimately show False by simp
          qed
          also have "lex_pm \<dots> (i.lpp s)" by fact
          finally show "lex_pm t (i.lpp s)" .
        qed
        also have "lex_pm_strict \<dots> l"
        proof (rule i.punit.lt_less)
          from spoly_nz show "s \<noteq> 0" by (auto simp: spoly_eq)
        next
          fix t
          assume "lex_pm l t"

          have "g1' = flatten (focus X g1')" by simp
          also have "\<dots> = flatten (monomial c1 (i.lpp (focus X g1')) + i.punit.tail (focus X g1'))"
            by (simp only: c1_def flip: i.punit.leading_monomial_tail)
          also from \<open>g1' \<in> P[_]\<close> have "\<dots> = punit.monom_mult 1 (except (i.lpp g1') {x}) c1 +
                                              flatten (i.punit.tail (focus X g1'))"
            by (simp only: flatten_plus flatten_monomial lpp_focus)
          finally have "punit.monom_mult 1 (except (i.lpp g1') {x}) c1 +
                              flatten (i.punit.tail (focus X g1')) = g1'" (is "?l = _") by (rule sym)
          moreover have "c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) ?l =
                          punit.monom_mult 1 l (c1 * c2) +
                          c2 * punit.monom_mult 1 (l - i.lpp (focus X g1'))
                                                  (flatten (i.punit.tail (focus X g1')))"
            (is "_ = punit.monom_mult 1 l (c1 * c2) + ?a")
            by (simp add: punit.monom_mult_dist_right punit.monom_mult_assoc l_def minus_plus adds_lcs)
               (simp add: distrib_left lpp_focus \<open>g1' \<in> P[_]\<close> flip: times_monomial_left)
          ultimately have a: "c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) g1' =
                                punit.monom_mult 1 l (c1 * c2) + ?a" by simp

          have "g2' = flatten (focus X g2')" by simp
          also have "\<dots> = flatten (monomial c2 (i.lpp (focus X g2')) + i.punit.tail (focus X g2'))"
            by (simp only: c2_def flip: i.punit.leading_monomial_tail)
          also from \<open>g2' \<in> P[_]\<close> have "\<dots> = punit.monom_mult 1 (except (i.lpp g2') {x}) c2 +
                                              flatten (i.punit.tail (focus X g2'))"
            by (simp only: flatten_plus flatten_monomial lpp_focus)
          finally have "punit.monom_mult 1 (except (i.lpp g2') {x}) c2 +
                              flatten (i.punit.tail (focus X g2')) = g2'" (is "?l = _") by (rule sym)
          moreover have "c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) ?l =
                          punit.monom_mult 1 l (c1 * c2) +
                          c1 * punit.monom_mult 1 (l - i.lpp (focus X g2'))
                                                  (flatten (i.punit.tail (focus X g2')))"
            (is "_ = punit.monom_mult 1 l (c1 * c2) + ?b")
            by (simp add: punit.monom_mult_dist_right punit.monom_mult_assoc l_def minus_plus adds_lcs_2)
               (simp add: distrib_left lpp_focus \<open>g2' \<in> P[_]\<close> flip: times_monomial_left)
          ultimately have b: "c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) g2' =
                                punit.monom_mult 1 l (c1 * c2) + ?b" by simp

          have lex_pm_strict_t: "lex_pm_strict t (l - i.lpp (focus X h) + i.lpp (focus X h))"
            if "t \<in> keys (d * punit.monom_mult 1 (l - i.lpp (focus X h))
                                            (flatten (i.punit.tail (focus X h))))"
            and "h \<in> G" and "d \<in> P[{x}]" for d h
          proof -
            have 0: "lex_pm_strict (u + v) w" if "lex_pm_strict v w" and "w \<in> .[X]" and "u \<in> .[{x}]"
              for u v w using that(1)
            proof (rule lex_pm_strict_plus_left)
              fix y z
              assume "y \<in> keys w"
              also from that(2) have "\<dots> \<subseteq> X" by (rule PPsD)
              also have "\<dots> \<subseteq> {..<x}" by fact
              finally have "y < x" by simp
              assume "z \<in> keys u"
              also from that(3) have "\<dots> \<subseteq> {x}" by (rule PPsD)
              finally show "y < z" using \<open>y < x\<close> by simp
            qed
            let ?h = "focus X h"
            from that(2) have "?h \<in> G'" by (simp add: G'_def)
            with \<open>G' \<subseteq> P[X]\<close> have "?h \<in> P[X]" ..
            hence "i.lpp ?h \<in> .[X]" by (rule i.PPs_closed_lpp)
            from that(1) obtain t1 t2 where "t1 \<in> keys d"
              and "t2 \<in> keys (punit.monom_mult 1 (l - i.lpp ?h) (flatten (i.punit.tail ?h)))"
              and t: "t = t1 + t2" by (rule in_keys_timesE)
            from this(2) obtain t3 where "t3 \<in> keys (flatten (i.punit.tail ?h))"
              and t2: "t2 = l - i.lpp ?h + t3" by (auto simp: punit.keys_monom_mult)
            from this(1) obtain t4 t5 where "t4 \<in> keys (i.punit.tail ?h)"
              and t5_in: "t5 \<in> keys (lookup (i.punit.tail ?h) t4)" and t3: "t3 = t4 + t5"
              using keys_flatten_subset by blast
            from this(1) have 1: "lex_pm_strict t4 (i.lpp ?h)" by (rule i.punit.keys_tail_less_lt)
            from that(2) have "lookup ?h t4 \<in> P[{x}]" by (rule lookup_focus_in)
            hence "keys (lookup ?h t4) \<subseteq> .[{x}]" by (rule PolysD)
            moreover from t5_in have t5_in: "t5 \<in> keys (lookup ?h t4)"
              by (simp add: i.punit.lookup_tail split: if_split_asm)
            ultimately have "t5 \<in> .[{x}]" ..
            with 1 \<open>i.lpp ?h \<in> _\<close> have "lex_pm_strict (t5 + t4) (i.lpp ?h)" by (rule 0)
            hence "lex_pm_strict t3 (i.lpp ?h)" by (simp only: t3 add.commute)
            hence "lex_pm_strict t2 (l - i.lpp ?h + i.lpp ?h)" unfolding t2
              by (rule i.plus_monotone_strict_left)
            moreover from \<open>l \<in> .[X]\<close> \<open>i.lpp ?h \<in> .[X]\<close> have "l - i.lpp ?h + i.lpp ?h \<in> .[X]"
              by (intro PPs_closed_plus PPs_closed_minus)
            moreover from \<open>t1 \<in> keys d\<close> that(3) have "t1 \<in> .[{x}]" by (auto dest: PolysD)
            ultimately show ?thesis unfolding t by (rule 0)
          qed
          show "lookup s t = 0"
          proof (rule ccontr)
            assume "lookup s t \<noteq> 0"
            hence "t \<in> keys s" by (simp add: in_keys_iff)
            also have "\<dots> = keys (?a - ?b)" by (simp add: s_def a b)
            also have "\<dots> \<subseteq> keys ?a \<union> keys ?b" by (fact keys_minus)
            finally show False
            proof
              assume "t \<in> keys ?a"
              hence "lex_pm_strict t (l - i.lpp (focus X g1') + i.lpp (focus X g1'))"
                using \<open>g1' \<in> G\<close> \<open>c2 \<in> P[{x}]\<close> by (rule lex_pm_strict_t)
              with \<open>g1' \<in> P[_]\<close> have "lex_pm_strict t l"
                by (simp add: lpp_focus l_def minus_plus adds_lcs)
              with \<open>lex_pm l t\<close> show ?thesis by simp
            next
              assume "t \<in> keys ?b"
              hence "lex_pm_strict t (l - i.lpp (focus X g2') + i.lpp (focus X g2'))"
                using \<open>g2' \<in> G\<close> \<open>c1 \<in> P[{x}]\<close> by (rule lex_pm_strict_t)
              with \<open>g2' \<in> P[_]\<close> have "lex_pm_strict t l"
                by (simp add: lpp_focus l_def minus_plus adds_lcs_2)
              with \<open>lex_pm l t\<close> show ?thesis by simp
            qed
          qed
        qed
        also have "\<dots> = lcs (i.lpp g1) (i.lpp g2)" by (simp only: l_def lpp1 lpp2)
        finally show "lex_pm_strict (i.lpp (q g * g)) (lcs (i.lpp g1) (i.lpp g2))" .
      qed
    qed
    have "1 \<in> ideal (?e ` focus {x} ` F) \<longleftrightarrow> 1 \<in> ideal (?e ` focus {x} ` F) \<inter> P[- {x}]"
      by (simp add: one_in_Polys)
    also have "\<dots> \<longleftrightarrow> 1 \<in> ideal G3" by (simp add: one_in_Polys flip: eq3)
    also have "\<not> \<dots>"
    proof
      note G3_isGB
      moreover assume "1 \<in> ideal G3"
      moreover have "1 \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a)" by simp
      ultimately obtain g where "g \<in> G3" and "g \<noteq> 0" and "i.lpp g adds i.lpp (1::_ \<Rightarrow>\<^sub>0 'a)"
        by (rule i.punit.GB_adds_lt[simplified])
      from this(3) have "i.lpp g = 0" by (simp add: i.punit.lt_monomial adds_zero flip: single_one)
      hence "monomial (i.lcf g) 0 = g" by (rule i.punit.lt_eq_min_term_monomial[simplified])
      from \<open>g \<in> G3\<close> obtain g' where "g' \<in> G" and g: "g = ?e (focus {x} g')" by (auto simp: G3_def)
      from this(1) have "i.lpp g = except (i.lpp g') {x}" unfolding g by (rule lpp_e_focus)
      hence "keys (i.lpp g') \<subseteq> {x}" by (simp add: \<open>i.lpp g = 0\<close> except_eq_zero_iff)
      have "g' \<in> P[{x}]"
      proof (intro PolysI subsetI PPsI)
        fix t y
        assume "t \<in> keys g'"
        hence "lex_pm t (i.lpp g')" by (rule i.punit.lt_max_keys)
        moreover assume "y \<in> keys t"
        ultimately obtain z where "z \<in> keys (i.lpp g')" and "z \<le> y" by (rule lex_pm_keys_leE)
        with \<open>keys (i.lpp g') \<subseteq> {x}\<close> have "x \<le> y" by blast
        from \<open>g' \<in> G\<close> G_sub have "g' \<in> P[insert x X]" ..
        hence "indets g' \<subseteq> insert x X" by (rule PolysD)
        moreover from \<open>y \<in> _\<close> \<open>t \<in> _\<close> have "y \<in> indets g'" by (rule in_indetsI)
        ultimately have "y \<in> insert x X" ..
        thus "y \<in> {x}"
        proof
          assume "y \<in> X"
          with assms(3) have "y \<in> {..<x}" ..
          with \<open>x \<le> y\<close> show ?thesis by simp
        qed simp
      qed
      moreover from \<open>g' \<in> G\<close> have "g' \<in> ideal G" by (rule ideal.span_base)
      ultimately have "g' \<in> ideal F \<inter> P[{x}]" by (simp add: ideal_G)
      with assms(5) have "g' = 0" by blast
      hence "g = 0" by (simp add: g)
      with \<open>g \<noteq> 0\<close> show False ..
    qed
    finally show "1 \<notin> ideal (?e ` focus {x} ` F)" .
  qed
qed

lemma weak_Nullstellensatz_aux_3:
  assumes "F \<subseteq> P[insert x X]" and "x \<notin> X" and "1 \<notin> ideal F" and "\<not> ideal F \<inter> P[{x}] \<subseteq> {0}"
  obtains a::"'a::alg_closed_field" where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
proof -
  let ?x = "monomial 1 (Poly_Mapping.single x 1)"
  from assms(4) obtain f where "f \<in> ideal F" and "f \<in> P[{x}]" and "f \<noteq> 0" by blast
  define p where "p = poly_of_pm x f"
  from \<open>f \<in> P[{x}]\<close> \<open>f \<noteq> 0\<close> have "p \<noteq> 0"
    by (auto simp: p_def poly_of_pm_eq_zero_iff simp flip: keys_eq_empty dest!: PolysD(1))
  obtain c A m where A: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
    by (rule linear_factorsE) blast
  from this(4, 5) have "c \<noteq> 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> z \<in> A" by (simp_all add: \<open>p \<noteq> 0\<close>)
  have "\<exists>a\<in>A. 1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
  proof (rule ccontr)
    assume asm: "\<not> (\<exists>a\<in>A. 1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F))"
    obtain g h where "g a \<in> ideal F" and 1: "h a * (?x - monomial a 0) + g a = 1"
      if "a \<in> A" for a
    proof -
      define P where "P = (\<lambda>gh a. fst gh \<in> ideal F \<and> fst gh + snd gh * (?x - monomial a 0) = 1)"
      define gh where "gh = (\<lambda>a. SOME gh. P gh a)"
      show ?thesis
      proof
        fix a
        assume "a \<in> A"
        with asm have "1 \<in> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)" by blast
        hence "1 \<in> poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` ideal F"
          by (simp add: image_poly_eval_focus_ideal one_in_Polys)
        then obtain g where "g \<in> ideal F" and "1 = poly_eval (\<lambda>_. monomial a 0) (focus {x} g)"
          unfolding image_image ..
        note this(2)
        also have "poly_eval (\<lambda>_. monomial a 0) (focus {x} g) = poly (poly_of_focus x g) (monomial a 0)"
          by (simp only: poly_poly_of_focus)
        also have "\<dots> = poly (poly_of_focus x g) (?x - (?x - monomial a 0))" by simp
        also obtain h where "\<dots> = poly (poly_of_focus x g) ?x - h * (?x - monomial a 0)"
          by (rule poly_minus_rightE)
        also have "\<dots> = g - h * (?x - monomial a 0)" by (simp only: poly_poly_of_focus_monomial)
        finally have "g - h * (?x - monomial a 0) = 1" by (rule sym)
        with \<open>g \<in> ideal F\<close> have "P (g, - h) a" by (simp add: P_def)
        hence "P (gh a) a" unfolding gh_def by (rule someI)
        thus "fst (gh a) \<in> ideal F" and "snd (gh a) * (?x - monomial a 0) + fst (gh a) = 1"
          by (simp_all only: P_def add.commute)
      qed
    qed
    from this(1) obtain g' where "g' \<in> ideal F"
      and 2: "(\<Prod>a\<in>A. (h a * (?x - monomial a 0) + g a) ^ m a) =
                (\<Prod>a\<in>A. (h a * (?x - monomial a 0)) ^ m a) + g'"
      by (rule weak_Nullstellensatz_aux_1)
    have "1 = (\<Prod>a\<in>A. (h a * (?x - monomial a 0) + g a) ^ m a)"
      by (rule sym) (intro prod.neutral ballI, simp only: 1 power_one)
    also have "\<dots> = (\<Prod>a\<in>A. h a ^ m a) * (\<Prod>a\<in>A. (?x - monomial a 0) ^ m a) + g'"
      by (simp only: 2 power_mult_distrib prod.distrib)
    also have "(\<Prod>a\<in>A. (?x - monomial a 0) ^ m a) = pm_of_poly x (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
      by (simp add: pm_of_poly_prod pm_of_poly_pCons single_uminus punit.monom_mult_monomial
              flip: single_one)
    also from \<open>c \<noteq> 0\<close> have "\<dots> = monomial (inverse c) 0 * pm_of_poly x p"
      by (simp add: p map_scale_assoc flip: map_scale_eq_times)
    also from \<open>f \<in> P[{x}]\<close> have "\<dots> = monomial (inverse c) 0 * f"
      by (simp only: \<open>p = poly_of_pm x f\<close> pm_of_poly_of_pm)
    finally have "1 = ((\<Prod>a\<in>A. h a ^ m a) * monomial (inverse c) 0) * f + g'"
      by (simp only: mult.assoc)
    also from \<open>f \<in> ideal F\<close> \<open>g' \<in> ideal F\<close> have "\<dots> \<in> ideal F" by (intro ideal.span_add ideal.span_scale)
    finally have "1 \<in> ideal F" .
    with assms(3) show False ..
  qed
  then obtain a where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)" ..
  thus ?thesis ..
qed

theorem weak_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = ({}::('x::{countable,linorder} \<Rightarrow> 'a::alg_closed_field) set)"
  shows "ideal F = UNIV"
  unfolding ideal_eq_UNIV_iff_contains_one
proof (rule ccontr)
  assume "1 \<notin> ideal F"
  with assms(1, 2) obtain a where "1 \<notin> ideal (poly_eval a ` F)"
  proof (induct X arbitrary: F thesis rule: finite_linorder_induct)
    case empty
    have "F \<subseteq> {0}"
    proof
      fix f
      assume "f \<in> F"
      with empty.prems(2) have "f \<in> P[{}]" ..
      then obtain c where f: "f = monomial c 0" unfolding Polys_empty ..
      also have "c = 0"
      proof (rule ccontr)
        assume "c \<noteq> 0"
        from \<open>f \<in> F\<close> have "f \<in> ideal F" by (rule ideal.span_base)
        hence "monomial (inverse c) 0 * f \<in> ideal F" by (rule ideal.span_scale)
        with \<open>c \<noteq> 0\<close> have "1 \<in> ideal F" by (simp add: f times_monomial_monomial)
        with empty.prems(3) show False ..
      qed
      finally show "f \<in> {0}" by simp
    qed
    hence "poly_eval 0 ` F \<subseteq> {0}" by auto
    hence "ideal (poly_eval 0 ` F) = {0}" by simp
    hence "1 \<notin> ideal (poly_eval 0 ` F)" by (simp del: ideal_eq_zero_iff)
    thus ?case by (rule empty.prems)
  next
    case (insert x X)
    obtain a0 where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)" (is "_ \<notin> ideal ?F")
    proof (cases "ideal F \<inter> P[{x}] \<subseteq> {0}")
      case True
      with insert.hyps(1) insert.prems(2) insert.hyps(2) insert.prems(3) obtain a0
        where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)"
        by (rule weak_Nullstellensatz_aux_2)
      thus ?thesis ..
    next
      case False
      from insert.hyps(2) have "x \<notin> X" by blast
      with insert.prems(2) obtain a0 where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)"
        using insert.prems(3) False by (rule weak_Nullstellensatz_aux_3)
      thus ?thesis ..
    qed
    moreover have "?F \<subseteq> P[X]"
    proof -
      {
        fix f
        assume "f \<in> F"
        with insert.prems(2) have "f \<in> P[insert x X]" ..
        hence "poly_eval (\<lambda>_. monomial a0 0) (focus {x} f) \<in> P[insert x X - {x}]"
          by (rule poly_eval_focus_in_Polys)
        also have "\<dots> \<subseteq> P[X]" by (rule Polys_mono) simp
        finally have "poly_eval (\<lambda>_. monomial a0 0) (focus {x} f) \<in> P[X]" .
      }
      thus ?thesis by blast
    qed
    ultimately obtain a1 where "1 \<notin> ideal (poly_eval a1 ` ?F)" using insert.hyps(3) by blast
    also have "poly_eval a1 ` ?F = poly_eval (a1(x := poly_eval a1 (monomial a0 0))) ` F"
      by (simp add: image_image poly_eval_poly_eval_focus fun_upd_def)
    finally show ?case by (rule insert.prems)
  qed
  hence "ideal (poly_eval a ` F) \<noteq> UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
  hence "ideal (poly_eval a ` F) = {0}" using ideal_field_disj[of "poly_eval a ` F"] by blast
  hence "poly_eval a ` F \<subseteq> {0}" by simp
  hence "a \<in> \<V> F" by (rule variety_ofI_alt)
  thus False by (simp add: assms(3))
qed

lemma radical_idealI:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F) = {}"
  shows "(f::('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) \<in> \<surd>ideal F"
proof (cases "f = 0")
  case True
  thus ?thesis by simp
next
  case False
  from assms(4) have "P[X] \<subseteq> P[- {x}]" by (auto simp: Polys_alt)
  with assms(3) have "f \<in> P[- {x}]" ..
  let ?x = "Poly_Mapping.single x 1"
  let ?f = "punit.monom_mult 1 ?x f"
  from assms(1) have "finite (insert x X)" by simp
  moreover have "insert (1 - ?f) F \<subseteq> P[insert x X]" unfolding insert_subset
  proof (intro conjI Polys_closed_minus one_in_Polys Polys_closed_monom_mult PPs_closed_single)
    have "P[X] \<subseteq> P[insert x X]" by (rule Polys_mono) blast
    with assms(2, 3) show "f \<in> P[insert x X]" and "F \<subseteq> P[insert x X]" by blast+
  qed simp
  ultimately have "ideal (insert (1 - ?f) F) = UNIV"
    using assms(5) by (rule weak_Nullstellensatz)
  hence "1 \<in> ideal (insert (1 - ?f) F)" by simp
  then obtain F' q where fin': "finite F'" and F'_sub: "F' \<subseteq> insert (1 - ?f) F"
    and eq: "1 = (\<Sum>f'\<in>F'. q f' * f')" by (rule ideal.spanE)
  show "f \<in> \<surd>ideal F"
  proof (cases "1 - ?f \<in> F'")
    case True
    define g where "g = (\<lambda>x::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. Fract x 1)"
    define F'' where "F'' = F' - {1 - ?f}"
    define q0 where "q0 = q (1 - ?f)"
    have g_0: "g 0 = 0" by (simp add: g_def fract_collapse)
    have g_1: "g 1 = 1" by (simp add: g_def fract_collapse)
    have g_plus: "g (a + b) = g a + g b" for a b by (simp add: g_def)
    have g_minus: "g (a - b) = g a - g b" for a b by (simp add: g_def)
    have g_times: "g (a * b) = g a * g b" for a b by (simp add: g_def)
    from fin' have fin'': "finite F''" by (simp add: F''_def)
    from F'_sub have F''_sub: "F'' \<subseteq> F" by (auto simp: F''_def)

    have "focus {x} ?f = monomial 1 ?x * focus {x} f"
      by (simp add: focus_times focus_monomial except_single flip: times_monomial_left)
    also from \<open>f \<in> P[- {x}]\<close> have "focus {x} f = monomial f 0" by (rule focus_Polys_Compl)
    finally have "focus {x} ?f = monomial f ?x" by (simp add: times_monomial_monomial)
    hence eq1: "poly (map_poly g (poly_of_focus x (1 - ?f))) (Fract 1 f) = 0"
      by (simp add: poly_of_focus_def focus_minus poly_of_pm_minus poly_of_pm_monomial
                PPs_closed_single map_poly_minus g_0 g_1 g_minus map_poly_monom poly_monom)
         (simp add: g_def Fract_same \<open>f \<noteq> 0\<close>)
    have eq2: "poly (map_poly g (poly_of_focus x f')) (Fract 1 f) = Fract f' 1" if "f' \<in> F''" for f'
    proof -
      from that F''_sub have "f' \<in> F" ..
      with assms(2) have "f' \<in> P[X]" ..
      with \<open>P[X] \<subseteq> _\<close> have "f' \<in> P[- {x}]" ..
      hence "focus {x} f' = monomial f' 0" by (rule focus_Polys_Compl)
      thus ?thesis
        by (simp add: poly_of_focus_def focus_minus poly_of_pm_minus poly_of_pm_monomial
                zero_in_PPs map_poly_minus g_0 g_1 g_minus map_poly_monom poly_monom)
           (simp only: g_def)
    qed

    define p0m0 where "p0m0 = (\<lambda>f'. SOME z. poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) =
                                              Fract (fst z) (f ^ snd z))"
    define p0 where "p0 = fst \<circ> p0m0"
    define m0 where "m0 = snd \<circ> p0m0"
    define m where "m = Max (m0 ` F'')"
    have eq3: "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract (p0 f') (f ^ m0 f')"
      for f'
    proof -
      have "g a = 0 \<longleftrightarrow> a = 0" for a by (simp add: g_def Fract_eq_zero_iff)
      hence "set (Polynomial.coeffs (map_poly g (poly_of_focus x (q f')))) \<subseteq> range (\<lambda>x. Fract x 1)"
        by (auto simp: set_coeffs_map_poly g_def)
      then obtain p m' where "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract p (f ^ m')"
        by (rule poly_Fract)
      hence "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract (fst (p, m')) (f ^ snd (p, m'))"
        by simp
      thus ?thesis unfolding p0_def m0_def p0m0_def o_def by (rule someI)
    qed
    
    note eq
    also from True fin' have "(\<Sum>f'\<in>F'. q f' * f') = q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f')"
      by (simp add: q0_def F''_def sum.remove)
    finally have "poly_of_focus x 1 = poly_of_focus x (q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f'))"
      by (rule arg_cong)
    hence "1 = poly (map_poly g (poly_of_focus x (q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f')))) (Fract 1 f)"
      by (simp add: g_1)
    also have "\<dots> = poly (map_poly g (poly_of_focus x (\<Sum>f'\<in>F''. q f' * f'))) (Fract 1 f)"
      by (simp only: poly_of_focus_plus map_poly_plus g_0 g_plus g_times poly_add
                poly_of_focus_times map_poly_times poly_mult eq1 mult_zero_right add_0_left)
    also have "\<dots> = (\<Sum>f'\<in>F''. Fract (p0 f') (f ^ m0 f') * Fract f' 1)"
      by (simp only: poly_of_focus_sum poly_of_focus_times map_poly_sum map_poly_times
                g_0 g_plus g_times poly_sum poly_mult eq2 eq3 cong: sum.cong)
    finally have "Fract (f ^ m) 1 = Fract (f ^ m) 1 * (\<Sum>f'\<in>F''. Fract (p0 f' * f') (f ^ m0 f'))"
      by simp
    also have "\<dots> = (\<Sum>f'\<in>F''. Fract (f ^ m * (p0 f' * f')) (f ^ m0 f'))"
      by (simp add: sum_distrib_left)
    also from refl have "\<dots> = (\<Sum>f'\<in>F''. Fract ((f ^ (m - m0 f') * p0 f') * f') 1)"
    proof (rule sum.cong)
      fix f'
      assume "f' \<in> F''"
      hence "m0 f' \<in> m0 ` F''" by (rule imageI)
      with _ have "m0 f' \<le> m" unfolding m_def by (rule Max_ge) (simp add: fin'')
      hence "f ^ m = f ^ (m0 f') * f ^ (m - m0 f')" by (simp flip: power_add)
      hence "Fract (f ^ m * (p0 f' * f')) (f ^ m0 f') = Fract (f ^ m0 f') (f ^ m0 f') *
                                                        Fract (f ^ (m - m0 f') * (p0 f' * f')) 1"
        by (simp add: ac_simps)
      also from \<open>f \<noteq> 0\<close> have "Fract (f ^ m0 f') (f ^ m0 f') = 1" by (simp add: Fract_same)
      finally show "Fract (f ^ m * (p0 f' * f')) (f ^ m0 f') = Fract (f ^ (m - m0 f') * p0 f' * f') 1"
        by (simp add: ac_simps)
    qed
    also from fin'' have "\<dots> = Fract (\<Sum>f'\<in>F''. (f ^ (m - m0 f') * p0 f') * f') 1"
      by (induct F'') (simp_all add: fract_collapse)
    finally have "f ^ m = (\<Sum>f'\<in>F''. (f ^ (m - m0 f') * p0 f') * f')"
      by (simp add: eq_fract)
    also have "\<dots> \<in> ideal F''" by (rule ideal.sum_in_spanI)
    also from \<open>F'' \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
    finally show "f \<in> \<surd>ideal F" by (rule radicalI)
  next
    case False
    with F'_sub have "F' \<subseteq> F" by blast
    have "1 \<in> ideal F'" unfolding eq by (rule ideal.sum_in_spanI)
    also from \<open>F' \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
    finally have "ideal F = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
    thus ?thesis by simp
  qed
qed

corollary radical_idealI_extend_indets:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single None 1) (extend_indets f))
                            (extend_indets ` F)) = {}"
  shows "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F"
proof -
  define Y where "Y = X \<union> indets f"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def finite_indets)
  have "P[X] \<subseteq> P[Y]" by (rule Polys_mono) (simp add: Y_def)
  with assms(2) have F_sub: "F \<subseteq> P[Y]" by (rule subset_trans)
  have f_in: "f \<in> P[Y]" by (simp add: Y_def Polys_alt)

  let ?F = "extend_indets ` F"
  let ?f = "extend_indets f"
  let ?X = "Some ` Y"
  from fin_Y have "finite ?X" by (rule finite_imageI)
  moreover from F_sub have "?F \<subseteq> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2) subsetD[of F])
  moreover from f_in have "?f \<in> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2))
  moreover have "None \<notin> ?X" by simp
  ultimately have "?f \<in> \<surd>ideal ?F" using assms(3) by (rule radical_idealI)
  also have "?f \<in> \<surd>ideal ?F \<longleftrightarrow> f \<in> \<surd>ideal F"
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    hence "extend_indets (f ^ m) \<in> extend_indets ` ideal F" by (rule imageI)
    with extend_indets_ideal_subset have "?f ^ m \<in> ideal ?F" unfolding extend_indets_power ..
    thus "?f \<in> \<surd>ideal ?F" by (rule radicalI)
  next
    assume "?f \<in> \<surd>ideal ?F"
    then obtain m where "?f ^ m \<in> ideal ?F" by (rule radicalE)
    moreover have "?f ^ m \<in> P[- {None}]"
      by (rule Polys_closed_power) (auto intro!: PolysI_alt simp: indets_extend_indets)
    ultimately have "extend_indets (f ^ m) \<in> extend_indets ` ideal F"
      by (simp add: extend_indets_ideal extend_indets_power)
    hence "f ^ m \<in> ideal F" by (simp only: inj_image_mem_iff[OF inj_extend_indets])
    thus "f \<in> \<surd>ideal F" by (rule radicalI)
  qed
  finally show ?thesis .
qed

theorem Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<I> (\<V> F)"
  shows "f \<in> \<surd>ideal F"
  using assms(1, 2)
proof (rule radical_idealI_extend_indets)
  let ?f = "punit.monom_mult 1 (monomial 1 None) (extend_indets f)"
  show "\<V> (insert (1 - ?f) (extend_indets ` F)) = {}"
  proof (intro subset_antisym subsetI)
    fix a
    assume "a \<in> \<V> (insert (1 - ?f) (extend_indets ` F))"
    moreover have "1 - ?f \<in> insert (1 - ?f) (extend_indets ` F)" by simp
    ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
    hence "poly_eval a (extend_indets f) \<noteq> 0"
      by (auto simp: poly_eval_minus poly_eval_times simp flip: times_monomial_left)
    hence "poly_eval (a \<circ> Some) f \<noteq> 0" by (simp add: poly_eval_extend_indets)
    have "a \<circ> Some \<in> \<V> F"
    proof (rule variety_ofI)
      fix f'
      assume "f' \<in> F"
      hence "extend_indets f' \<in> insert (1 - ?f) (extend_indets ` F)" by simp
      with \<open>a \<in> _\<close> have "poly_eval a (extend_indets f') = 0" by (rule variety_ofD)
      thus "poly_eval (a \<circ> Some) f' = 0" by (simp only: poly_eval_extend_indets)
    qed
    with assms(3) have "poly_eval (a \<circ> Some) f = 0" by (rule ideal_ofD)
    with \<open>poly_eval (a \<circ> Some) f \<noteq> 0\<close> show "a \<in> {}" ..
  qed simp
qed

theorem strong_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::((_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof (intro subset_antisym subsetI)
  fix f
  assume "f \<in> \<I> (\<V> F)"
  with assms show "f \<in> \<surd>ideal F" by (rule Nullstellensatz)
qed (metis ideal_ofI variety_ofD variety_of_radical_ideal)

text \<open>The following lemma can be used for actually \<^emph>\<open>deciding\<close> whether a polynomial is contained in
  the radical of an ideal or not.\<close>

lemma radical_ideal_iff:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
  shows "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F \<longleftrightarrow>
            1 \<in> ideal (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F)"
proof -
  let ?f = "punit.monom_mult 1 (Poly_Mapping.single x 1) f"
  show ?thesis
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    from assms(1) have "finite (insert x X)" by simp
    moreover have "insert (1 - ?f) F \<subseteq> P[insert x X]" unfolding insert_subset
    proof (intro conjI Polys_closed_minus one_in_Polys Polys_closed_monom_mult PPs_closed_single)
      have "P[X] \<subseteq> P[insert x X]" by (rule Polys_mono) blast
      with assms(2, 3) show "f \<in> P[insert x X]" and "F \<subseteq> P[insert x X]" by blast+
    qed simp
    moreover have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      moreover have "1 - ?f \<in> insert (1 - ?f) F" by simp
      ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
      hence "poly_eval a (f ^ m) \<noteq> 0"
        by (auto simp: poly_eval_minus poly_eval_times poly_eval_power simp flip: times_monomial_left)
      from \<open>a \<in> _\<close> have "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      moreover from \<open>f ^ m \<in> ideal F\<close> ideal.span_mono have "f ^ m \<in> ideal (insert (1 - ?f) F)"
        by (rule rev_subsetD) blast
      ultimately have "poly_eval a (f ^ m) = 0" by (rule variety_ofD)
      with \<open>poly_eval a (f ^ m) \<noteq> 0\<close> show "a \<in> {}" ..
    qed simp
    ultimately have "ideal (insert (1 - ?f) F) = UNIV" by (rule weak_Nullstellensatz)
    thus "1 \<in> ideal (insert (1 - ?f) F)" by simp
  next
    assume "1 \<in> ideal (insert (1 - ?f) F)"
    have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      hence "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      hence "poly_eval a 1 = 0" using \<open>1 \<in> _\<close> by (rule variety_ofD)
      thus "a \<in> {}" by simp
    qed simp
    with assms show "f \<in> \<surd>ideal F" by (rule radical_idealI)
  qed
qed

end (* theory *)
