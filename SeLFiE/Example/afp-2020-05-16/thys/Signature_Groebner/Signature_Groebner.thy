(* Author: Alexander Maletzky *)

section \<open>Signature-Based Algorithms for Computing Gr\"obner Bases\<close>

theory Signature_Groebner
  imports More_MPoly Groebner_Bases.Syzygy Polynomials.Quasi_PM_Power_Products
begin

text \<open>First, we develop the whole theory for elements of the module $K[X]^r$, i.\,e. objects of type
  @{typ "'t \<Rightarrow>\<^sub>0 'b"}. Later, we transfer all algorithms defined on such objects to algorithms
  efficiently operating on sig-poly-pairs, i.\,e. objects of type @{typ "'t \<times> ('a \<Rightarrow>\<^sub>0 'b)"}.\<close>

subsection \<open>More Preliminaries\<close>

lemma (in gd_term) lt_spoly_less_lcs:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "spoly p q \<noteq> 0"
  shows "lt (spoly p q) \<prec>\<^sub>t term_of_pair (lcs (lp p) (lp q), component_of_term (lt p))"
proof -
  let ?l = "lcs (lp p) (lp q)"
  let ?p = "monom_mult (1 / lc p) (?l - lp p) p"
  let ?q = "monom_mult (1 / lc q) (?l - lp q) q"
  from assms(3) have eq1: "component_of_term (lt p) = component_of_term (lt q)"
    and eq2: "spoly p q = ?p - ?q"
    by (simp_all add: spoly_def Let_def lc_def split: if_split_asm)
  from \<open>p \<noteq> 0\<close> have "lc p \<noteq> 0" by (rule lc_not_0)
  with assms(1) have "lt ?p = (?l - lp p) \<oplus> lt p" and "lc ?p = 1" by (simp_all add: lt_monom_mult)
  from this(1) have lt_p: "lt ?p = term_of_pair (?l, component_of_term (lt p))"
    by (simp add: splus_def adds_minus adds_lcs)
  from \<open>q \<noteq> 0\<close> have "lc q \<noteq> 0" by (rule lc_not_0)
  with assms(2) have "lt ?q = (?l - lp q) \<oplus> lt q" and "lc ?q = 1" by (simp_all add: lt_monom_mult)
  from this(1) have lt_q: "lt ?q = term_of_pair (?l, component_of_term (lt p))"
    by (simp add: eq1 splus_def adds_minus adds_lcs_2)
  from assms(3) have "?p - ?q \<noteq> 0" by (simp add: eq2)
  moreover have "lt ?q = lt ?p" by (simp only: lt_p lt_q)
  moreover have "lc ?q = lc ?p" by (simp only: \<open>lc ?p = 1\<close> \<open>lc ?q = 1\<close>)
  ultimately have "lt (?p - ?q) \<prec>\<^sub>t lt ?p" by (rule lt_minus_lessI)
  thus ?thesis by (simp only: eq2 lt_p)
qed

subsection \<open>Module Polynomials\<close>

locale qpm_inf_term =
    gd_term pair_of_term term_of_pair ord ord_strict ord_term ord_term_strict
      for pair_of_term::"'t \<Rightarrow> ('a::quasi_pm_powerprod \<times> nat)"
      and term_of_pair::"('a \<times> nat) \<Rightarrow> 't"
      and ord::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50)
      and ord_strict (infixl "\<prec>" 50)
      and ord_term::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<preceq>\<^sub>t" 50)
      and ord_term_strict::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<prec>\<^sub>t" 50)
begin

lemma in_idealE_rep_dgrad_p_set:
  assumes "hom_grading d" and "B \<subseteq> punit.dgrad_p_set d m" and "p \<in> punit.dgrad_p_set d m" and "p \<in> ideal B"
  obtains r where "keys r \<subseteq> B" and "Poly_Mapping.range r \<subseteq> punit.dgrad_p_set d m" and "p = ideal.rep r"
proof -
  from assms obtain A q where "finite A" and "A \<subseteq> B" and 0: "\<And>b. q b \<in> punit.dgrad_p_set d m"
    and p: "p = (\<Sum>a\<in>A. q a * a)" by (rule punit.in_pmdlE_dgrad_p_set[simplified], blast)
  define r where "r = Abs_poly_mapping (\<lambda>k. q k when k \<in> A)"
  have 1: "lookup r = (\<lambda>k. q k when k \<in> A)" unfolding r_def
    by (rule Abs_poly_mapping_inverse, simp add: \<open>finite A\<close>)
  have 2: "keys r \<subseteq> A" by (auto simp: in_keys_iff 1)
  show ?thesis
  proof
    show "Poly_Mapping.range r \<subseteq> punit.dgrad_p_set d m"
    proof
      fix f
      assume "f \<in> Poly_Mapping.range r"
      then obtain b where "b \<in> keys r" and f: "f = lookup r b" by (rule poly_mapping_rangeE)
      from this(1) 2 have "b \<in> A" ..
      hence "f = q b" by (simp add: f 1)
      show "f \<in> punit.dgrad_p_set d m" unfolding \<open>f = q b\<close> by (rule 0)
    qed
  next
    have "p = (\<Sum>a\<in>A. lookup r a * a)" unfolding p by (rule sum.cong, simp_all add: 1)
    also from \<open>finite A\<close> 2 have "... = (\<Sum>a\<in>keys r. lookup r a * a)"
    proof (rule sum.mono_neutral_right)
      show "\<forall>a\<in>A - keys r. lookup r a * a = 0"
        by (simp add: in_keys_iff)
    qed
    finally show "p = ideal.rep r" by (simp only: ideal.rep_def)
  next
    from 2 \<open>A \<subseteq> B\<close> show "keys r \<subseteq> B" by (rule subset_trans)
  qed
qed

context fixes fs :: "('a \<Rightarrow>\<^sub>0 'b::field) list"
begin

definition sig_inv_set' :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set"
  where "sig_inv_set' j = {r. keys (vectorize_poly r) \<subseteq> {0..<j}}"

abbreviation "sig_inv_set \<equiv> sig_inv_set' (length fs)"

definition rep_list :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "rep_list r = ideal.rep (pm_of_idx_pm fs (vectorize_poly r))"

lemma sig_inv_setI: "keys (vectorize_poly r) \<subseteq> {0..<j} \<Longrightarrow> r \<in> sig_inv_set' j"
  by (simp add: sig_inv_set'_def)

lemma sig_inv_setD: "r \<in> sig_inv_set' j \<Longrightarrow> keys (vectorize_poly r) \<subseteq> {0..<j}"
  by (simp add: sig_inv_set'_def)

lemma sig_inv_setI':
  assumes "\<And>v. v \<in> keys r \<Longrightarrow> component_of_term v < j"
  shows "r \<in> sig_inv_set' j"
proof (rule sig_inv_setI, rule)
  fix k
  assume "k \<in> keys (vectorize_poly r)"
  then obtain v where "v \<in> keys r" and k: "k = component_of_term v" unfolding keys_vectorize_poly ..
  from this(1) have "k < j" unfolding k by (rule assms)
  thus "k \<in> {0..<j}" by simp
qed

lemma sig_inv_setD':
  assumes "r \<in> sig_inv_set' j" and "v \<in> keys r"
  shows "component_of_term v < j"
proof -
  from assms(2) have "component_of_term v \<in> component_of_term ` keys r" by (rule imageI)
  also have "... = keys (vectorize_poly r)" by (simp only: keys_vectorize_poly)
  also from assms(1) have "... \<subseteq> {0..<j}" by (rule sig_inv_setD)
  finally show ?thesis by simp
qed

corollary sig_inv_setD_lt:
  assumes "r \<in> sig_inv_set' j" and "r \<noteq> 0"
  shows "component_of_term (lt r) < j"
  by (rule sig_inv_setD', fact, rule lt_in_keys, fact)

lemma sig_inv_set_mono:
  assumes "i \<le> j"
  shows "sig_inv_set' i \<subseteq> sig_inv_set' j"
proof
  fix r
  assume "r \<in> sig_inv_set' i"
  hence "keys (vectorize_poly r) \<subseteq> {0..<i}" by (rule sig_inv_setD)
  also from assms have "... \<subseteq> {0..<j}" by fastforce
  finally show "r \<in> sig_inv_set' j" by (rule sig_inv_setI)
qed

lemma sig_inv_set_zero: "0 \<in> sig_inv_set' j"
  by (rule sig_inv_setI', simp)

lemma sig_inv_set_closed_uminus: "r \<in> sig_inv_set' j \<Longrightarrow> - r \<in> sig_inv_set' j"
  by (auto dest!: sig_inv_setD' intro!: sig_inv_setI' simp: keys_uminus)

lemma sig_inv_set_closed_plus:
  assumes "r \<in> sig_inv_set' j" and "s \<in> sig_inv_set' j"
  shows "r + s \<in> sig_inv_set' j"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (r + s)"
  hence "v \<in> keys r \<union> keys s" using Poly_Mapping.keys_add ..
  thus "component_of_term v < j"
  proof
    assume "v \<in> keys r"
    with assms(1) show ?thesis by (rule sig_inv_setD')
  next
    assume "v \<in> keys s"
    with assms(2) show ?thesis by (rule sig_inv_setD')
  qed
qed

lemma sig_inv_set_closed_minus:
  assumes "r \<in> sig_inv_set' j" and "s \<in> sig_inv_set' j"
  shows "r - s \<in> sig_inv_set' j"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (r - s)"
  hence "v \<in> keys r \<union> keys s" using keys_minus ..
  thus "component_of_term v < j"
  proof
    assume "v \<in> keys r"
    with assms(1) show ?thesis by (rule sig_inv_setD')
  next
    assume "v \<in> keys s"
    with assms(2) show ?thesis by (rule sig_inv_setD')
  qed
qed

lemma sig_inv_set_closed_monom_mult:
  assumes "r \<in> sig_inv_set' j"
  shows "monom_mult c t r \<in> sig_inv_set' j"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (monom_mult c t r)"
  hence "v \<in> (\<oplus>) t ` keys r" using keys_monom_mult_subset ..
  then obtain u where "u \<in> keys r" and v: "v = t \<oplus> u" ..
  from assms this(1) have "component_of_term u < j" by (rule sig_inv_setD')
  thus "component_of_term v < j" by (simp add: v term_simps)
qed

lemma sig_inv_set_closed_mult_scalar:
  assumes "r \<in> sig_inv_set' j"
  shows "p \<odot> r \<in> sig_inv_set' j"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (p \<odot> r)"
  then obtain t u where "u \<in> keys r" and v: "v = t \<oplus> u" by (rule in_keys_mult_scalarE)
  from assms this(1) have "component_of_term u < j" by (rule sig_inv_setD')
  thus "component_of_term v < j" by (simp add: v term_simps)
qed

lemma rep_list_zero: "rep_list 0 = 0"
  by (simp add: rep_list_def vectorize_zero)

lemma rep_list_uminus: "rep_list (- r) = - rep_list r"
  by (simp add: rep_list_def vectorize_uminus pm_of_idx_pm_uminus)

lemma rep_list_plus: "rep_list (r + s) = rep_list r + rep_list s"
  by (simp add: rep_list_def vectorize_plus pm_of_idx_pm_plus ideal.rep_plus)

lemma rep_list_minus: "rep_list (r - s) = rep_list r - rep_list s"
  by (simp add: rep_list_def vectorize_minus pm_of_idx_pm_minus ideal.rep_minus)

lemma vectorize_mult_scalar:
  "vectorize_poly (p \<odot> q) = MPoly_Type_Class.punit.monom_mult p 0 (vectorize_poly q)"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly MPoly_Type_Class.punit.lookup_monom_mult_zero proj_mult_scalar)

lemma rep_list_mult_scalar: "rep_list (c \<odot> r) = c * rep_list r"
  by (simp add: rep_list_def vectorize_mult_scalar pm_of_idx_pm_monom_mult punit.rep_mult_scalar[simplified])

lemma rep_list_monom_mult: "rep_list (monom_mult c t r) = punit.monom_mult c t (rep_list r)"
  unfolding mult_scalar_monomial[symmetric] times_monomial_left[symmetric] by (rule rep_list_mult_scalar)

lemma rep_list_monomial:
  assumes "distinct fs"
  shows "rep_list (monomial c u) =
            (punit.monom_mult c (pp_of_term u) (fs ! (component_of_term u))
              when component_of_term u < length fs)"
  by (simp add: rep_list_def vectorize_monomial pm_of_idx_pm_monomial[OF assms] when_def times_monomial_left)

lemma rep_list_in_ideal_sig_inv_set:
  assumes "r \<in> sig_inv_set' j"
  shows "rep_list r \<in> ideal (set (take j fs))"
proof -
  let ?fs = "take j fs"
  from assms have "keys (vectorize_poly r) \<subseteq> {0..<j}" by (rule sig_inv_setD)
  hence eq: "pm_of_idx_pm fs (vectorize_poly r) = pm_of_idx_pm ?fs (vectorize_poly r)"
    by (simp only: pm_of_idx_pm_take)
  have "rep_list r \<in> ideal (keys (pm_of_idx_pm fs (vectorize_poly r)))"
    unfolding rep_list_def by (rule ideal.rep_in_span)
  also have "... = ideal (keys (pm_of_idx_pm ?fs (vectorize_poly r)))" by (simp only: eq)
  also from keys_pm_of_idx_pm_subset have "... \<subseteq> ideal (set ?fs)" by (rule ideal.span_mono)
  finally show ?thesis .
qed

corollary rep_list_subset_ideal_sig_inv_set:
  "B \<subseteq> sig_inv_set' j \<Longrightarrow> rep_list ` B \<subseteq> ideal (set (take j fs))"
  by (auto dest: rep_list_in_ideal_sig_inv_set)

lemma rep_list_in_ideal: "rep_list r \<in> ideal (set fs)"
proof -
  have "rep_list r \<in> ideal (keys (pm_of_idx_pm fs (vectorize_poly r)))"
    unfolding rep_list_def by (rule ideal.rep_in_span)
  also from keys_pm_of_idx_pm_subset have "... \<subseteq> ideal (set fs)" by (rule ideal.span_mono)
  finally show ?thesis .
qed

corollary rep_list_subset_ideal: "rep_list ` B \<subseteq> ideal (set fs)"
  by (auto intro: rep_list_in_ideal)

lemma in_idealE_rep_list:
  assumes "p \<in> ideal (set fs)"
  obtains r where "p = rep_list r" and "r \<in> sig_inv_set"
proof -
  from assms obtain r0 where r0: "keys r0 \<subseteq> set fs" and p: "p = ideal.rep r0"
    by (rule ideal.spanE_rep)
  show ?thesis
  proof
    show "p = rep_list (atomize_poly (idx_pm_of_pm fs r0))"
      by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p)
  next
    show "atomize_poly (idx_pm_of_pm fs r0) \<in> sig_inv_set"
      by (rule sig_inv_setI, simp add: vectorize_atomize_poly keys_idx_pm_of_pm_subset)
  qed
qed

lemma keys_rep_list_subset:
  assumes "t \<in> keys (rep_list r)"
  obtains v s where "v \<in> keys r" and "s \<in> Keys (set fs)" and "t = pp_of_term v + s"
proof -
  from assms obtain v0 s where v0: "v0 \<in> Keys (Poly_Mapping.range (pm_of_idx_pm fs (vectorize_poly r)))"
    and s: "s \<in> Keys (keys (pm_of_idx_pm fs (vectorize_poly r)))" and t: "t = v0 + s"
    unfolding rep_list_def by (rule punit.keys_rep_subset[simplified])
  note s
  also from keys_pm_of_idx_pm_subset have "Keys (keys (pm_of_idx_pm fs (vectorize_poly r))) \<subseteq> Keys (set fs)"
    by (rule Keys_mono)
  finally have "s \<in> Keys (set fs)" .
  note v0
  also from range_pm_of_idx_pm_subset'
  have "Keys (Poly_Mapping.range (pm_of_idx_pm fs (vectorize_poly r))) \<subseteq> Keys (Poly_Mapping.range (vectorize_poly r))"
    by (rule Keys_mono)
  also have "... = pp_of_term ` keys r" by (fact Keys_range_vectorize_poly)
  finally obtain v where "v \<in> keys r" and "v0 = pp_of_term v" ..
  from this(2) have "t = pp_of_term v + s" by (simp only: t)
  with \<open>v \<in> keys r\<close> \<open>s \<in> Keys (set fs)\<close> show ?thesis ..
qed

lemma dgrad_p_set_le_rep_list:
  assumes "dickson_grading d" and "dgrad_set_le d (pp_of_term ` keys r) (Keys (set fs))"
  shows "punit.dgrad_p_set_le d {rep_list r} (set fs)"
proof (simp add: punit.dgrad_p_set_le_def Keys_insert, rule dgrad_set_leI)
  fix t
  assume "t \<in> keys (rep_list r)"
  then obtain v s1 where "v \<in> keys r" and "s1 \<in> Keys (set fs)" and t: "t = pp_of_term v + s1"
    by (rule keys_rep_list_subset)
  from this(1) have "pp_of_term v \<in> pp_of_term ` keys r" by fastforce
  with assms(2) obtain s2 where "s2 \<in> Keys (set fs)" and "d (pp_of_term v) \<le> d s2"
    by (rule dgrad_set_leE)
  from assms(1) have "d t = ord_class.max (d (pp_of_term v)) (d s1)" unfolding t
    by (rule dickson_gradingD1)
  hence "d t = d (pp_of_term v) \<or> d t = d s1" by (simp add: ord_class.max_def)
  thus "\<exists>s\<in>Keys (set fs). d t \<le> d s"
  proof
    assume "d t = d (pp_of_term v)"
    with \<open>d (pp_of_term v) \<le> d s2\<close> have "d t \<le> d s2" by simp
    with \<open>s2 \<in> Keys (set fs)\<close> show ?thesis ..
  next
    assume "d t = d s1"
    hence "d t \<le> d s1" by simp
    with \<open>s1 \<in> Keys (set fs)\<close> show ?thesis ..
  qed
qed

corollary dgrad_p_set_le_rep_list_image:
  assumes "dickson_grading d" and "dgrad_set_le d (pp_of_term ` Keys F) (Keys (set fs))"
  shows "punit.dgrad_p_set_le d (rep_list ` F) (set fs)"
proof (rule punit.dgrad_p_set_leI, elim imageE, simp)
  fix f
  assume "f \<in> F"
  have "pp_of_term ` keys f \<subseteq> pp_of_term ` Keys F" by (rule image_mono, rule keys_subset_Keys, fact)
  hence "dgrad_set_le d (pp_of_term ` keys f) (pp_of_term ` Keys F)" by (rule dgrad_set_le_subset)
  hence "dgrad_set_le d (pp_of_term ` keys f) (Keys (set fs))" using assms(2) by (rule dgrad_set_le_trans)
  with assms(1) show "punit.dgrad_p_set_le d {rep_list f} (set fs)" by (rule dgrad_p_set_le_rep_list)
qed
term Max

definition dgrad_max :: "('a \<Rightarrow> nat) \<Rightarrow> nat"
  where "dgrad_max d = (Max (d ` (insert 0 (Keys (set fs)))))"

abbreviation "dgrad_max_set d \<equiv> dgrad_p_set d (dgrad_max d)"
abbreviation "punit_dgrad_max_set d \<equiv> punit.dgrad_p_set d (dgrad_max d)"

lemma dgrad_max_0: "d 0 \<le> dgrad_max d"
proof -
  from finite_Keys have "finite (d ` insert 0 (Keys (set fs)))" by auto
  moreover have "d 0 \<in> d ` insert 0 (Keys (set fs))" by blast
  ultimately show ?thesis unfolding dgrad_max_def by (rule Max_ge)
qed

lemma dgrad_max_1: "set fs \<subseteq> punit_dgrad_max_set d"
proof (cases "Keys (set fs) = {}")
  case True
  show ?thesis
  proof (rule, rule punit.dgrad_p_setI[simplified])
    fix f v
    assume "f \<in> set fs" and "v \<in> keys f"
    with True show "d v \<le> dgrad_max d" by (auto simp: Keys_def)
  qed
next
  case False
  show ?thesis
  proof (rule subset_trans)
    from finite_set show "set fs \<subseteq> punit.dgrad_p_set d (Max (d ` (Keys (set fs))))"
      by (rule punit.dgrad_p_set_exhaust_expl[simplified])
  next
    from finite_set have "finite (Keys (set fs))" by (rule finite_Keys)
    hence "finite (d ` Keys (set fs))" by (rule finite_imageI)
    moreover from False have 2: "d ` Keys (set fs) \<noteq> {}" by simp
    ultimately have "dgrad_max d = ord_class.max (d 0) (Max (d ` Keys (set fs)))"
      by (simp add: dgrad_max_def)
    hence "Max (d ` (Keys (set fs))) \<le> dgrad_max d" by simp
    thus "punit.dgrad_p_set d (Max (d ` (Keys (set fs)))) \<subseteq> punit_dgrad_max_set d"
      by (rule punit.dgrad_p_set_subset)
  qed
qed

lemma dgrad_max_2:
  assumes "dickson_grading d" and "r \<in> dgrad_max_set d"
  shows "rep_list r \<in> punit_dgrad_max_set d"
proof (rule punit.dgrad_p_setI[simplified])
  fix t
  assume "t \<in> keys (rep_list r)"
  then obtain v s where "v \<in> keys r" and "s \<in> Keys (set fs)" and t: "t = pp_of_term v + s"
    by (rule keys_rep_list_subset)
  from assms(2) \<open>v \<in> keys r\<close> have "d (pp_of_term v) \<le> dgrad_max d" by (rule dgrad_p_setD)
  moreover have "d s \<le> dgrad_max d" by (simp add: \<open>s \<in> Keys (set fs)\<close> dgrad_max_def finite_Keys)
  ultimately show "d t \<le> dgrad_max d" by (simp add: t dickson_gradingD1[OF assms(1)])
qed

corollary dgrad_max_3:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
  shows "rep_list ` F \<subseteq> punit_dgrad_max_set d"
proof (rule, elim imageE, simp)
  fix f
  assume "f \<in> F"
  hence "f \<in> dgrad_p_set d (dgrad_max d)" using assms(2) ..
  with assms(1) show "rep_list f \<in> punit.dgrad_p_set d (dgrad_max d)" by (rule dgrad_max_2)
qed

lemma punit_dgrad_max_set_subset_dgrad_p_set:
  assumes "dickson_grading d" and "set fs \<subseteq> punit.dgrad_p_set d m" and "\<not> set fs \<subseteq> {0}"
  shows "punit_dgrad_max_set d \<subseteq> punit.dgrad_p_set d m"
proof (rule punit.dgrad_p_set_subset)
  show "dgrad_max d \<le> m" unfolding dgrad_max_def
  proof (rule Max.boundedI)
    show "finite (d ` insert 0 (Keys (set fs)))" by (simp add: finite_Keys)
  next
    show "d ` insert 0 (Keys (set fs)) \<noteq> {}" by simp
  next
    fix a
    assume "a \<in> d ` insert 0 (Keys (set fs))"
    then obtain t where "t \<in> insert 0 (Keys (set fs))" and "a = d t" ..
    from this(1) show "a \<le> m" unfolding \<open>a = d t\<close>
    proof
      assume "t = 0"
      from assms(3) obtain f where "f \<in> set fs" and "f \<noteq> 0" by auto
      from this(1) assms(2) have "f \<in> punit.dgrad_p_set d m" ..
      from \<open>f \<noteq> 0\<close> have "keys f \<noteq> {}" by simp
      then obtain s where "s \<in> keys f" by blast
      have "d s = d (t + s)" by (simp add: \<open>t = 0\<close>)
      also from assms(1) have "... = ord_class.max (d t) (d s)" by (rule dickson_gradingD1)
      finally have "d t \<le> d s" by (simp add: max_def)
      also from \<open>f \<in> punit.dgrad_p_set d m\<close> \<open>s \<in> keys f\<close> have "... \<le> m"
        by (rule punit.dgrad_p_setD[simplified])
      finally show "d t \<le> m" .
    next
      assume "t \<in> Keys (set fs)"
      then obtain f where "f \<in> set fs" and "t \<in> keys f" by (rule in_KeysE)
      from this(1) assms(2) have "f \<in> punit.dgrad_p_set d m" ..
      thus "d t \<le> m" using \<open>t \<in> keys f\<close> by (rule punit.dgrad_p_setD[simplified])
    qed
  qed
qed

definition dgrad_sig_set' :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set"
  where "dgrad_sig_set' j d = dgrad_max_set d \<inter> sig_inv_set' j"

abbreviation "dgrad_sig_set \<equiv> dgrad_sig_set' (length fs)"

lemma dgrad_sig_set_set_mono: "i \<le> j \<Longrightarrow> dgrad_sig_set' i d \<subseteq> dgrad_sig_set' j d"
  by (auto simp: dgrad_sig_set'_def dest: sig_inv_set_mono)

lemma dgrad_sig_set_closed_uminus: "r \<in> dgrad_sig_set' j d \<Longrightarrow> - r \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: dgrad_p_set_closed_uminus sig_inv_set_closed_uminus)

lemma dgrad_sig_set_closed_plus:
  "r \<in> dgrad_sig_set' j d \<Longrightarrow> s \<in> dgrad_sig_set' j d \<Longrightarrow> r + s \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: dgrad_p_set_closed_plus sig_inv_set_closed_plus)

lemma dgrad_sig_set_closed_minus:
  "r \<in> dgrad_sig_set' j d \<Longrightarrow> s \<in> dgrad_sig_set' j d \<Longrightarrow> r - s \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: dgrad_p_set_closed_minus sig_inv_set_closed_minus)

lemma dgrad_sig_set_closed_monom_mult:
  assumes "dickson_grading d" and "d t \<le> dgrad_max d"
  shows "p \<in> dgrad_sig_set' j d \<Longrightarrow> monom_mult c t p \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: assms dgrad_p_set_closed_monom_mult sig_inv_set_closed_monom_mult)

lemma dgrad_sig_set_closed_monom_mult_zero:
  "p \<in> dgrad_sig_set' j d \<Longrightarrow> monom_mult c 0 p \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: dgrad_p_set_closed_monom_mult_zero sig_inv_set_closed_monom_mult)

lemma dgrad_sig_set_closed_mult_scalar:
  "dickson_grading d \<Longrightarrow> p \<in> punit_dgrad_max_set d \<Longrightarrow> r \<in> dgrad_sig_set' j d \<Longrightarrow> p \<odot> r \<in> dgrad_sig_set' j d"
  unfolding dgrad_sig_set'_def by (auto intro: dgrad_p_set_closed_mult_scalar sig_inv_set_closed_mult_scalar)

lemma dgrad_sig_set_closed_monomial:
  assumes "d (pp_of_term u) \<le> dgrad_max d" and "component_of_term u < j"
  shows "monomial c u \<in> dgrad_sig_set' j d"
proof (simp add: dgrad_sig_set'_def, rule)
  show "monomial c u \<in> dgrad_max_set d"
  proof (rule dgrad_p_setI)
    fix v
    assume "v \<in> keys (monomial c u)"
    also have "... \<subseteq> {u}" by simp
    finally show "d (pp_of_term v) \<le> dgrad_max d" using assms(1) by simp
  qed
next
  show "monomial c u \<in> sig_inv_set' j"
  proof (rule sig_inv_setI')
    fix v
    assume "v \<in> keys (monomial c u)"
    also have "... \<subseteq> {u}" by simp
    finally show "component_of_term v < j" using assms(2) by simp
  qed
qed

lemma rep_list_in_ideal_dgrad_sig_set:
  "r \<in> dgrad_sig_set' j d \<Longrightarrow> rep_list r \<in> ideal (set (take j fs))"
  by (auto simp: dgrad_sig_set'_def dest: rep_list_in_ideal_sig_inv_set)

lemma in_idealE_rep_list_dgrad_sig_set_take:
  assumes "hom_grading d" and "p \<in> punit_dgrad_max_set d" and "p \<in> ideal (set (take j fs))"
  obtains r where "r \<in> dgrad_sig_set d" and "r \<in> dgrad_sig_set' j d" and "p = rep_list r"
proof -
  let ?fs = "take j fs"
  from set_take_subset dgrad_max_1 have "set ?fs \<subseteq> punit_dgrad_max_set d"
    by (rule subset_trans)
  with assms(1) obtain r0 where r0: "keys r0 \<subseteq> set ?fs"
    and 1: "Poly_Mapping.range r0 \<subseteq> punit_dgrad_max_set d" and p: "p = ideal.rep r0"
    using assms(2, 3) by (rule in_idealE_rep_dgrad_p_set)
  define q where "q = idx_pm_of_pm ?fs r0"
  have "keys q \<subseteq> {0..<length ?fs}" unfolding q_def by (rule keys_idx_pm_of_pm_subset)
  also have "... \<subseteq> {0..<j}" by fastforce
  finally have keys_q: "keys q \<subseteq> {0..<j}" .
  have *: "atomize_poly q \<in> dgrad_max_set d"
  proof
    fix v
    assume "v \<in> keys (atomize_poly q)"
    then obtain i where i: "i \<in> keys q"
      and v_in: "v \<in> (\<lambda>t. term_of_pair (t, i)) ` keys (lookup q i)"
      unfolding keys_atomize_poly ..
    from i keys_idx_pm_of_pm_subset[of ?fs r0] have "i < length ?fs" by (auto simp: q_def)
    from v_in obtain t where "t \<in> keys (lookup q i)" and v: "v = term_of_pair (t, i)" ..
    from this(1) \<open>i < length ?fs\<close> have t: "t \<in> keys (lookup r0 (?fs ! i))"
      by (simp add: lookup_idx_pm_of_pm q_def)
    hence "lookup r0 (?fs ! i) \<noteq> 0" by fastforce
    hence "lookup r0 (?fs ! i) \<in> Poly_Mapping.range r0" by (simp add: in_keys_iff)
    hence "lookup r0 (?fs ! i) \<in> punit_dgrad_max_set d" using 1 ..
    hence "d t \<le> dgrad_max d" using t by (rule punit.dgrad_p_setD[simplified])
    thus "d (pp_of_term v) \<le> dgrad_max d" by (simp add: v pp_of_term_of_pair)
  qed
  show ?thesis
  proof
    have "atomize_poly q \<in> sig_inv_set' j"
      by (rule sig_inv_setI, simp add: vectorize_atomize_poly keys_q)
    with * show "atomize_poly q \<in> dgrad_sig_set' j d" unfolding dgrad_sig_set'_def ..
  next
    from \<open>keys q \<subseteq> {0..<length ?fs}\<close> have keys_q': "keys q \<subseteq> {0..<length fs}" by auto
    have "atomize_poly q \<in> sig_inv_set"
      by (rule sig_inv_setI, simp add: vectorize_atomize_poly keys_q')
    with * show "atomize_poly q \<in> dgrad_sig_set d" unfolding dgrad_sig_set'_def ..
  next
    from keys_q have "pm_of_idx_pm fs q = pm_of_idx_pm ?fs q" by (simp only: pm_of_idx_pm_take)
    thus "p = rep_list (atomize_poly q)"
      by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p q_def)
  qed
qed

corollary in_idealE_rep_list_dgrad_sig_set:
  assumes "hom_grading d" and "p \<in> punit_dgrad_max_set d" and "p \<in> ideal (set fs)"
  obtains r where "r \<in> dgrad_sig_set d" and "p = rep_list r"
proof -
  from assms(3) have "p \<in> ideal (set (take (length fs) fs))" by simp
  with assms(1, 2) obtain r where "r \<in> dgrad_sig_set d" and "p = rep_list r"
    by (rule in_idealE_rep_list_dgrad_sig_set_take)
  thus ?thesis ..
qed

lemma dgrad_sig_setD_lp:
  assumes "p \<in> dgrad_sig_set' j d"
  shows "d (lp p) \<le> dgrad_max d"
proof (cases "p = 0")
  case True
  show ?thesis by (simp add: True min_term_def pp_of_term_of_pair dgrad_max_0)
next
  case False
  from assms have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  thus ?thesis using False by (rule dgrad_p_setD_lp)
qed

lemma dgrad_sig_setD_lt:
  assumes "p \<in> dgrad_sig_set' j d" and "p \<noteq> 0"
  shows "component_of_term (lt p) < j"
proof -
  from assms have "p \<in> sig_inv_set' j" by (simp add: dgrad_sig_set'_def)
  thus ?thesis using assms(2) by (rule sig_inv_setD_lt)
qed

lemma dgrad_sig_setD_rep_list_lt:
  assumes "dickson_grading d" and "p \<in> dgrad_sig_set' j d"
  shows "d (punit.lt (rep_list p)) \<le> dgrad_max d"
proof (cases "rep_list p = 0")
  case True
  show ?thesis by (simp add: True dgrad_max_0)
next
  case False
  from assms(2) have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  with assms(1) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
  thus ?thesis using False by (rule punit.dgrad_p_setD_lp[simplified])
qed

definition spp_of :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))"
  where "spp_of r = (lt r, rep_list r)"

text \<open>``spp'' stands for ``sig-poly-pair''.\<close>

lemma fst_spp_of: "fst (spp_of r) = lt r"
  by (simp add: spp_of_def)

lemma snd_spp_of: "snd (spp_of r) = rep_list r"
  by (simp add: spp_of_def)

subsubsection \<open>Signature Reduction\<close>

lemma term_is_le_rel_canc_left:
  assumes "ord_term_lin.is_le_rel rel"
  shows "rel (t \<oplus> u) (t \<oplus> v) \<longleftrightarrow> rel u v"
  using assms
  by (rule ord_term_lin.is_le_relE,
      auto simp: splus_left_canc dest: ord_term_canc ord_term_strict_canc splus_mono splus_mono_strict)

lemma term_is_le_rel_minus:
  assumes "ord_term_lin.is_le_rel rel" and "s adds t"
  shows "rel ((t - s) \<oplus> u) v \<longleftrightarrow> rel (t \<oplus> u) (s \<oplus> v)"
proof -
  from assms(2) have eq: "s + (t - s) = t" unfolding add.commute[of s] by (rule adds_minus)
  from assms(1) have "rel ((t - s) \<oplus> u) v = rel (s \<oplus> ((t - s) \<oplus> u)) (s \<oplus> v)"
    by (simp only: term_is_le_rel_canc_left)
  also have "... = rel (t \<oplus> u) (s \<oplus> v)" by (simp only: splus_assoc[symmetric] eq)
  finally show ?thesis .
qed

lemma term_is_le_rel_minus_minus:
  assumes "ord_term_lin.is_le_rel rel" and "a adds t" and "b adds t"
  shows "rel ((t - a) \<oplus> u) ((t - b) \<oplus> v) \<longleftrightarrow> rel (b \<oplus> u) (a \<oplus> v)"
proof -
  from assms(2) have eq1: "a + (t - a) = t" unfolding add.commute[of a] by (rule adds_minus)
  from assms(3) have eq2: "b + (t - b) = t" unfolding add.commute[of b] by (rule adds_minus)
  from assms(1) have "rel ((t - a) \<oplus> u) ((t - b) \<oplus> v) = rel ((a + b) \<oplus> ((t - a) \<oplus> u)) ((a + b) \<oplus> ((t - b) \<oplus> v))"
    by (simp only: term_is_le_rel_canc_left)
  also have "... = rel ((t + b) \<oplus> u) ((t + a) \<oplus> v)" unfolding splus_assoc[symmetric]
    by (metis (no_types, lifting) add.assoc add.commute eq1 eq2)
  also from assms(1) have "... = rel (b \<oplus> u) (a \<oplus> v)" by (simp only: splus_assoc term_is_le_rel_canc_left)
  finally show ?thesis .
qed

lemma pp_is_le_rel_canc_right:
  assumes "ordered_powerprod_lin.is_le_rel rel"
  shows "rel (s + u) (t + u) \<longleftrightarrow> rel s t"
  using assms
  by (rule ordered_powerprod_lin.is_le_relE, auto dest: ord_canc ord_strict_canc plus_monotone plus_monotone_strict)

lemma pp_is_le_rel_canc_left: "ordered_powerprod_lin.is_le_rel rel \<Longrightarrow> rel (t + u) (t + v) \<longleftrightarrow> rel u v"
  by (simp add: add.commute[of t] pp_is_le_rel_canc_right)

definition sig_red_single :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "sig_red_single sing_reg top_tail p q f t \<longleftrightarrow>
                (rep_list f \<noteq> 0 \<and> lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0 \<and>
                 q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f \<and>
                 ord_term_lin.is_le_rel sing_reg \<and> ordered_powerprod_lin.is_le_rel top_tail \<and>
                 sing_reg (t \<oplus> lt f) (lt p) \<and> top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p)))"

text \<open>The first two parameters of @{const sig_red_single}, \<open>sing_reg\<close> and \<open>top_tail\<close>, specify whether
  the reduction is a singular/regular/arbitrary top/tail/arbitrary signature-reduction.
  \<^item> If \<open>sing_reg\<close> is @{const HOL.eq}, the reduction is singular.
  \<^item> If \<open>sing_reg\<close> is @{term "(\<prec>\<^sub>t)"}, the reduction is regular.
  \<^item> If \<open>sing_reg\<close> is @{term "(\<preceq>\<^sub>t)"}, the reduction is an arbitrary signature-reduction.
  \<^item> If \<open>top_tail\<close> is @{const HOL.eq}, it is a top reduction.
  \<^item> If \<open>top_tail\<close> is @{term "(\<prec>)"}, it is a tail reduction.
  \<^item> If \<open>top_tail\<close> is @{term "(\<preceq>)"}, the reduction is an arbitrary signature-reduction.\<close>

definition sig_red :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red sing_reg top_tail F p q \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t. sig_red_single sing_reg top_tail p q f t)"

definition is_sig_red :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_sig_red sing_reg top_tail F p \<longleftrightarrow> (\<exists>q. sig_red sing_reg top_tail F p q)"

lemma sig_red_singleI:
  assumes "rep_list f \<noteq> 0" and "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    and "ord_term_lin.is_le_rel sing_reg" and "ordered_powerprod_lin.is_le_rel top_tail"
    and "sing_reg (t \<oplus> lt f) (lt p)"
    and "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
  shows "sig_red_single sing_reg top_tail p q f t"
  unfolding sig_red_single_def using assms by blast

lemma sig_red_singleD1:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "rep_list f \<noteq> 0"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD2:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
  using assms unfolding sig_red_single_def by (simp add: in_keys_iff)

lemma sig_red_singleD3:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD4:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "ord_term_lin.is_le_rel sing_reg"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD5:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "ordered_powerprod_lin.is_le_rel top_tail"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD6:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sing_reg (t \<oplus> lt f) (lt p)"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD7:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD8:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t \<oplus> lt f \<preceq>\<^sub>t lt p"
proof -
  from assms have "ord_term_lin.is_le_rel sing_reg" and "sing_reg (t \<oplus> lt f) (lt p)"
    by (rule sig_red_singleD4, rule sig_red_singleD6)
  thus ?thesis by (rule ord_term_lin.is_le_rel_le)
qed

lemma sig_red_singleD9:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t + punit.lt (rep_list f) \<preceq> punit.lt (rep_list p)"
proof -
  from assms have "ordered_powerprod_lin.is_le_rel top_tail"
    and "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
    by (rule sig_red_singleD5, rule sig_red_singleD7)
  thus ?thesis by (rule ordered_powerprod_lin.is_le_rel_le)
qed

lemmas sig_red_singleD = sig_red_singleD1 sig_red_singleD2 sig_red_singleD3 sig_red_singleD4
                         sig_red_singleD5 sig_red_singleD6 sig_red_singleD7 sig_red_singleD8 sig_red_singleD9

lemma sig_red_single_red_single:
  "sig_red_single sing_reg top_tail p q f t \<Longrightarrow> punit.red_single (rep_list p) (rep_list q) (rep_list f) t"
  by (simp add: sig_red_single_def punit.red_single_def rep_list_minus rep_list_monom_mult)

lemma sig_red_single_regular_lt:
  assumes "sig_red_single (\<prec>\<^sub>t) top_tail p q f t"
  shows "lt q = lt p"
proof -
  let ?f = "monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
  from assms have lt: "t \<oplus> lt f \<prec>\<^sub>t lt p" and q: "q = p - ?f"
    by (rule sig_red_singleD6, rule sig_red_singleD3)
  from lt_monom_mult_le lt have "lt ?f \<prec>\<^sub>t lt p" by (rule ord_term_lin.order.strict_trans1)
  thus ?thesis unfolding q by (rule lt_minus_eqI_2)
qed

lemma sig_red_single_regular_lc:
  assumes "sig_red_single (\<prec>\<^sub>t) top_tail p q f t"
  shows "lc q = lc p"
proof -
  from assms have "lt q = lt p" by (rule sig_red_single_regular_lt)
  from assms have lt: "t \<oplus> lt f \<prec>\<^sub>t lt p"
    and q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ - ?f") by (rule sig_red_singleD6, rule sig_red_singleD3)
  from lt_monom_mult_le lt have "lt ?f \<prec>\<^sub>t lt p" by (rule ord_term_lin.order.strict_trans1)
  hence "lookup ?f (lt p) = 0" using lt_max ord_term_lin.leD by blast
  thus ?thesis unfolding lc_def \<open>lt q = lt p\<close> by (simp add: q lookup_minus)
qed

lemma sig_red_single_lt:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "lt q \<preceq>\<^sub>t lt p"
proof -
  from assms have lt: "t \<oplus> lt f \<preceq>\<^sub>t lt p"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD8, rule sig_red_singleD3)
  from this(2) have q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ + ?f") by (simp add: monom_mult_uminus_left)
  from lt_monom_mult_le lt have 1: "lt ?f \<preceq>\<^sub>t lt p" by (rule ord_term_lin.order.trans)
  have "lt q \<preceq>\<^sub>t ord_term_lin.max (lt p) (lt ?f)" unfolding q by (fact lt_plus_le_max)
  also from 1 have "ord_term_lin.max (lt p) (lt ?f) = lt p" by (rule ord_term_lin.max.absorb1)
  finally show ?thesis .
qed

lemma sig_red_single_lt_rep_list:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
proof -
  from assms have "punit.red_single (rep_list p) (rep_list q) (rep_list f) t"
    by (rule sig_red_single_red_single)
  hence "punit.ord_strict_p (rep_list q) (rep_list p)" by (rule punit.red_single_ord)
  hence "punit.ord_p (rep_list q) (rep_list p)" by simp
  thus ?thesis by (rule punit.ord_p_lt)
qed

lemma sig_red_single_tail_lt_in_keys_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lt (rep_list p) \<in> keys (rep_list q)"
proof -
  from assms have "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD3)
  hence q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (simp add: monom_mult_uminus_left)
  show ?thesis unfolding q rep_list_plus rep_list_monom_mult
  proof (rule in_keys_plusI1)
    from assms have "t + punit.lt (rep_list f) \<in> keys (rep_list p)" by (rule sig_red_singleD2)
    hence "rep_list p \<noteq> 0" by auto
    thus "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
  next
    show "punit.lt (rep_list p) \<notin>
      keys (punit.monom_mult (- lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t (rep_list f))"
        (is "_ \<notin> keys ?f")
    proof
      assume "punit.lt (rep_list p) \<in> keys ?f"
      hence "punit.lt (rep_list p) \<preceq> punit.lt ?f" by (rule punit.lt_max_keys)
      also have "... \<preceq> t + punit.lt (rep_list f)" by (fact punit.lt_monom_mult_le[simplified])
      also from assms have "... \<prec> punit.lt (rep_list p)" by (rule sig_red_singleD7)
      finally show False by simp
    qed
  qed
qed

corollary sig_red_single_tail_lt_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lt (rep_list q) = punit.lt (rep_list p)"
proof (rule ordered_powerprod_lin.antisym)
  from assms show "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)" by (rule sig_red_single_lt_rep_list)
next
  from assms have "punit.lt (rep_list p) \<in> keys (rep_list q)" by (rule sig_red_single_tail_lt_in_keys_rep_list)
  thus "punit.lt (rep_list p) \<preceq> punit.lt (rep_list q)" by (rule punit.lt_max_keys)
qed

lemma sig_red_single_tail_lc_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lc (rep_list q) = punit.lc (rep_list p)"
proof -
  from assms have *: "punit.lt (rep_list q) = punit.lt (rep_list p)"
    by (rule sig_red_single_tail_lt_rep_list)
  from assms have lt: "t + punit.lt (rep_list f) \<prec> punit.lt (rep_list p)"
    and q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ - ?f") by (rule sig_red_singleD7, rule sig_red_singleD3)
  from punit.lt_monom_mult_le[simplified] lt have "punit.lt (rep_list ?f) \<prec> punit.lt (rep_list p)"
    unfolding rep_list_monom_mult by (rule ordered_powerprod_lin.order.strict_trans1)
  hence "lookup (rep_list ?f) (punit.lt (rep_list p)) = 0"
    using punit.lt_max ordered_powerprod_lin.leD by blast
  thus ?thesis unfolding punit.lc_def * by (simp add: q lookup_minus rep_list_minus punit.lc_def)
qed

lemma sig_red_single_top_lt_rep_list:
  assumes "sig_red_single sing_reg (=) p q f t" and "rep_list q \<noteq> 0"
  shows "punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
proof -
  from assms(1) have "rep_list f \<noteq> 0" and in_keys: "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and lt: "t + punit.lt (rep_list f) = punit.lt (rep_list p)"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD)+
  from this(4) have q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ + monom_mult ?c _ _") by (simp add: monom_mult_uminus_left)
  from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  from assms(2) have *: "rep_list p + punit.monom_mult ?c t (rep_list f) \<noteq> 0"
    by (simp add: q rep_list_plus rep_list_monom_mult)
  from in_keys have "lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0"
    by (simp add: in_keys_iff)
  moreover from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have "?c \<noteq> 0" by simp
  hence "punit.lt (punit.monom_mult ?c t (rep_list f)) = t + punit.lt (rep_list f)"
    using \<open>rep_list f \<noteq> 0\<close> by (rule lp_monom_mult)
  hence "punit.lt (punit.monom_mult ?c t (rep_list f)) = punit.lt (rep_list p)" by (simp only: lt)
  moreover have "punit.lc (punit.monom_mult ?c t (rep_list f)) = - punit.lc (rep_list p)"
    by (simp add: lt punit.lc_def[symmetric] \<open>punit.lc (rep_list f) \<noteq> 0\<close>)
  ultimately show ?thesis unfolding rep_list_plus rep_list_monom_mult q by (rule punit.lt_plus_lessI[OF *])
qed

lemma sig_red_single_monom_mult:
  assumes "sig_red_single sing_reg top_tail p q f t" and "c \<noteq> 0"
  shows "sig_red_single sing_reg top_tail (monom_mult c s p) (monom_mult c s q) f (s + t)"
proof -
  from assms(1) have a: "ord_term_lin.is_le_rel sing_reg" and b: "ordered_powerprod_lin.is_le_rel top_tail"
    by (rule sig_red_singleD4, rule sig_red_singleD5)
  have eq1: "(s + t) \<oplus> lt f = s \<oplus> (t \<oplus> lt f)" by (simp only: splus_assoc)
  from assms(1) have 1: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" by (rule sig_red_singleD2)
  hence "rep_list p \<noteq> 0" by auto
  hence "p \<noteq> 0" by (auto simp: rep_list_zero)
  with assms(2) have eq2: "lt (monom_mult c s p) = s \<oplus> lt p" by (rule lt_monom_mult)
  show ?thesis
  proof (rule sig_red_singleI)
    from assms(1) show "rep_list f \<noteq> 0" by (rule sig_red_singleD1)
  next
    show "s + t + punit.lt (rep_list f) \<in> keys (rep_list (monom_mult c s p))"
      by (auto simp: rep_list_monom_mult punit.keys_monom_mult[OF assms(2)] ac_simps intro: 1)
  next
    from assms(1) have q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
      by (rule sig_red_singleD3)
    show "monom_mult c s q =
          monom_mult c s p -
            monom_mult (lookup (rep_list (monom_mult c s p)) (s + t + punit.lt (rep_list f)) / punit.lc (rep_list f)) (s + t) f"
      by (simp add: q monom_mult_dist_right_minus ac_simps rep_list_monom_mult
          punit.lookup_monom_mult_plus[simplified] monom_mult_assoc)
  next
    from assms(1) have "sing_reg (t \<oplus> lt f) (lt p)" by (rule sig_red_singleD6)
    thus "sing_reg ((s + t) \<oplus> lt f) (lt (monom_mult c s p))"
      by (simp only: eq1 eq2 term_is_le_rel_canc_left[OF a])
  next
    from assms(1) have "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
      by (rule sig_red_singleD7)
    thus "top_tail (s + t + punit.lt (rep_list f)) (punit.lt (rep_list (monom_mult c s p)))"
      by (simp add: rep_list_monom_mult punit.lt_monom_mult[OF assms(2) \<open>rep_list p \<noteq> 0\<close>] add.assoc pp_is_le_rel_canc_left[OF b])
  qed (fact a, fact b)
qed

lemma sig_red_single_sing_reg_cases:
  "sig_red_single (\<preceq>\<^sub>t) top_tail p q f t = (sig_red_single (=) top_tail p q f t \<or> sig_red_single (\<prec>\<^sub>t) top_tail p q f t)"
  by (auto simp: sig_red_single_def)

corollary sig_red_single_sing_regI:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sig_red_single (\<preceq>\<^sub>t) top_tail p q f t"
proof -
  from assms have "ord_term_lin.is_le_rel sing_reg" by (rule sig_red_singleD)
  with assms show ?thesis unfolding ord_term_lin.is_le_rel_def
    by (auto simp: sig_red_single_sing_reg_cases)
qed

lemma sig_red_single_top_tail_cases:
  "sig_red_single sing_reg (\<preceq>) p q f t = (sig_red_single sing_reg (=) p q f t \<or> sig_red_single sing_reg (\<prec>) p q f t)"
  by (auto simp: sig_red_single_def)

corollary sig_red_single_top_tailI:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sig_red_single sing_reg (\<preceq>) p q f t"
proof -
  from assms have "ordered_powerprod_lin.is_le_rel top_tail" by (rule sig_red_singleD)
  with assms show ?thesis unfolding ordered_powerprod_lin.is_le_rel_def
    by (auto simp: sig_red_single_top_tail_cases)
qed

lemma dgrad_max_set_closed_sig_red_single:
  assumes "dickson_grading d" and "p \<in> dgrad_max_set d" and "f \<in> dgrad_max_set d"
    and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> dgrad_max_set d"
proof -
  let ?f = "monom_mult (lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
  from assms(4) have t: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" and q: "q = p - ?f"
    by (rule sig_red_singleD2, rule sig_red_singleD3)
  from assms(1, 2) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
  show ?thesis unfolding q using assms(2)
  proof (rule dgrad_p_set_closed_minus)
    from assms(1) _ assms(3) show "?f \<in> dgrad_max_set d"
    proof (rule dgrad_p_set_closed_monom_mult)
      from assms(1) have "d t \<le> d (t + punit.lt (rep_list f))" by (simp add: dickson_gradingD1)
      also from \<open>rep_list p \<in> punit_dgrad_max_set d\<close> t have "... \<le> dgrad_max d"
        by (rule punit.dgrad_p_setD[simplified])
      finally show "d t \<le> dgrad_max d" .
    qed
  qed
qed

lemma sig_inv_set_closed_sig_red_single:
  assumes "p \<in> sig_inv_set" and "f \<in> sig_inv_set" and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> sig_inv_set"
proof -
  let ?f = "monom_mult (lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
  from assms(3) have t: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" and q: "q = p - ?f"
    by (rule sig_red_singleD2, rule sig_red_singleD3)
  show ?thesis unfolding q using assms(1)
  proof (rule sig_inv_set_closed_minus)
    from assms(2) show "?f \<in> sig_inv_set" by (rule sig_inv_set_closed_monom_mult)
  qed
qed

corollary dgrad_sig_set_closed_sig_red_single:
  assumes "dickson_grading d" and "p \<in> dgrad_sig_set d" and "f \<in> dgrad_sig_set d"
    and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> dgrad_sig_set d"
  using assms unfolding dgrad_sig_set'_def
  by (auto intro: dgrad_max_set_closed_sig_red_single sig_inv_set_closed_sig_red_single)

lemma sig_red_regular_lt: "sig_red (\<prec>\<^sub>t) top_tail F p q \<Longrightarrow> lt q = lt p"
  by (auto simp: sig_red_def intro: sig_red_single_regular_lt)

lemma sig_red_regular_lc: "sig_red (\<prec>\<^sub>t) top_tail F p q \<Longrightarrow> lc q = lc p"
  by (auto simp: sig_red_def intro: sig_red_single_regular_lc)

lemma sig_red_lt: "sig_red sing_reg top_tail F p q \<Longrightarrow> lt q \<preceq>\<^sub>t lt p"
  by (auto simp: sig_red_def intro: sig_red_single_lt)

lemma sig_red_tail_lt_rep_list: "sig_red sing_reg (\<prec>) F p q \<Longrightarrow> punit.lt (rep_list q) = punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_tail_lt_rep_list)

lemma sig_red_tail_lc_rep_list: "sig_red sing_reg (\<prec>) F p q \<Longrightarrow> punit.lc (rep_list q) = punit.lc (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_tail_lc_rep_list)

lemma sig_red_top_lt_rep_list:
  "sig_red sing_reg (=) F p q \<Longrightarrow> rep_list q \<noteq> 0 \<Longrightarrow> punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_top_lt_rep_list)

lemma sig_red_lt_rep_list: "sig_red sing_reg top_tail F p q \<Longrightarrow> punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_lt_rep_list)

lemma sig_red_red: "sig_red sing_reg top_tail F p q \<Longrightarrow> punit.red (rep_list ` F) (rep_list p) (rep_list q)"
  by (auto simp: sig_red_def punit.red_def dest: sig_red_single_red_single)

lemma sig_red_monom_mult:
  "sig_red sing_reg top_tail F p q \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> sig_red sing_reg top_tail F (monom_mult c s p) (monom_mult c s q)"
  by (auto simp: sig_red_def punit.red_def dest: sig_red_single_monom_mult)

lemma sig_red_sing_reg_cases:
  "sig_red (\<preceq>\<^sub>t) top_tail F p q = (sig_red (=) top_tail F p q \<or> sig_red (\<prec>\<^sub>t) top_tail F p q)"
  by (auto simp: sig_red_def sig_red_single_sing_reg_cases)

corollary sig_red_sing_regI: "sig_red sing_reg top_tail F p q \<Longrightarrow> sig_red (\<preceq>\<^sub>t) top_tail F p q"
  by (auto simp: sig_red_def intro: sig_red_single_sing_regI)

lemma sig_red_top_tail_cases:
  "sig_red sing_reg (\<preceq>) F p q = (sig_red sing_reg (=) F p q \<or> sig_red sing_reg (\<prec>) F p q)"
  by (auto simp: sig_red_def sig_red_single_top_tail_cases)

corollary sig_red_top_tailI: "sig_red sing_reg top_tail F p q \<Longrightarrow> sig_red sing_reg (\<preceq>) F p q"
  by (auto simp: sig_red_def intro: sig_red_single_top_tailI)

lemma sig_red_wf_dgrad_max_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
  shows "wfP (sig_red sing_reg top_tail F)\<inverse>\<inverse>"
proof -
  from assms have "rep_list ` F \<subseteq> punit_dgrad_max_set d" by (rule dgrad_max_3)
  with assms(1) have "wfP (punit.red (rep_list ` F))\<inverse>\<inverse>" by (rule punit.red_wf_dgrad_p_set)
  hence *: "\<nexists>f. \<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> (f (Suc i)) (f i)"
    by (simp add: wf_iff_no_infinite_down_chain[to_pred])
  show ?thesis unfolding wf_iff_no_infinite_down_chain[to_pred]
  proof (rule, elim exE)
    fix seq
    assume "\<forall>i. (sig_red sing_reg top_tail F)\<inverse>\<inverse> (seq (Suc i)) (seq i)"
    hence "sig_red sing_reg top_tail F (seq i) (seq (Suc i))" for i by simp
    hence "punit.red (rep_list ` F) ((rep_list \<circ> seq) i) ((rep_list \<circ> seq) (Suc i))" for i
      by (auto intro: sig_red_red)
    hence "\<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> ((rep_list \<circ> seq) (Suc i)) ((rep_list \<circ> seq) i)" by simp
    hence "\<exists>f. \<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> (f (Suc i)) (f i)" by blast
    with * show False ..
  qed
qed

lemma dgrad_sig_set_closed_sig_red:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_sig_set d" and "p \<in> dgrad_sig_set d"
    and "sig_red sing_red top_tail F p q"
  shows "q \<in> dgrad_sig_set d"
  using assms by (auto simp: sig_red_def intro: dgrad_sig_set_closed_sig_red_single)

lemma sig_red_mono: "sig_red sing_reg top_tail F p q \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> sig_red sing_reg top_tail F' p q"
  by (auto simp: sig_red_def)

lemma sig_red_Un:
  "sig_red sing_reg top_tail (A \<union> B) p q \<longleftrightarrow> (sig_red sing_reg top_tail A p q \<or> sig_red sing_reg top_tail B p q)"
  by (auto simp: sig_red_def)

lemma sig_red_subset:
  assumes "sig_red sing_reg top_tail F p q" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "sig_red sing_reg top_tail {f\<in>F. sing_reg (lt f) (lt p)} p q"
proof -
  from assms(1) obtain f t where "f \<in> F" and *: "sig_red_single sing_reg top_tail p q f t"
    unfolding sig_red_def by blast
  have "lt f = 0 \<oplus> lt f" by (simp only: term_simps)
  also from zero_min have "... \<preceq>\<^sub>t t \<oplus> lt f" by (rule splus_mono_left)
  finally have 1: "lt f \<preceq>\<^sub>t t \<oplus> lt f" .
  from * have 2: "sing_reg (t \<oplus> lt f) (lt p)" by (rule sig_red_singleD6)
  from assms(2) have "sing_reg (lt f) (lt p)"
  proof
    assume "sing_reg = (\<preceq>\<^sub>t)"
    with 1 2 show ?thesis by simp
  next
    assume "sing_reg = (\<prec>\<^sub>t)"
    with 1 2 show ?thesis by simp
  qed
  with \<open>f \<in> F\<close> have "f \<in> {f\<in>F. sing_reg (lt f) (lt p)}" by simp
  thus ?thesis using * unfolding sig_red_def by blast
qed

lemma sig_red_regular_rtrancl_lt:
  assumes "(sig_red (\<prec>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  shows "lt q = lt p"
  using assms by (induct, auto dest: sig_red_regular_lt)

lemma sig_red_regular_rtrancl_lc:
  assumes "(sig_red (\<prec>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  shows "lc q = lc p"
  using assms by (induct, auto dest: sig_red_regular_lc)

lemma sig_red_rtrancl_lt:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "lt q \<preceq>\<^sub>t lt p"
  using assms by (induct, auto dest: sig_red_lt)

lemma sig_red_tail_rtrancl_lt_rep_list:
  assumes "(sig_red sing_reg (\<prec>) F)\<^sup>*\<^sup>* p q"
  shows "punit.lt (rep_list q) = punit.lt (rep_list p)"
  using assms by (induct, auto dest: sig_red_tail_lt_rep_list)

lemma sig_red_tail_rtrancl_lc_rep_list:
  assumes "(sig_red sing_reg (\<prec>) F)\<^sup>*\<^sup>* p q"
  shows "punit.lc (rep_list q) = punit.lc (rep_list p)"
  using assms by (induct, auto dest: sig_red_tail_lc_rep_list)

lemma sig_red_rtrancl_lt_rep_list:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
  using assms by (induct, auto dest: sig_red_lt_rep_list)

lemma sig_red_red_rtrancl:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "(punit.red (rep_list ` F))\<^sup>*\<^sup>* (rep_list p) (rep_list q)"
  using assms by (induct, auto dest: sig_red_red)

lemma sig_red_rtrancl_monom_mult:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* (monom_mult c s p) (monom_mult c s q)"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  from assms(1) show ?thesis
  proof induct
    case base
    show ?case ..
  next
    case (step y z)
    from step(2) False have "sig_red sing_reg top_tail F (monom_mult c s y) (monom_mult c s z)"
      by (rule sig_red_monom_mult)
    with step(3) show ?case ..
  qed
qed

lemma sig_red_rtrancl_sing_regI: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q \<Longrightarrow> (sig_red (\<preceq>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  by (induct rule: rtranclp_induct, auto dest: sig_red_sing_regI)

lemma sig_red_rtrancl_top_tailI: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q \<Longrightarrow> (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* p q"
  by (induct rule: rtranclp_induct, auto dest: sig_red_top_tailI)

lemma dgrad_sig_set_closed_sig_red_rtrancl:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_sig_set d" and "p \<in> dgrad_sig_set d"
    and "(sig_red sing_red top_tail F)\<^sup>*\<^sup>* p q"
  shows "q \<in> dgrad_sig_set d"
  using assms(4, 1, 2, 3) by (induct, auto intro: dgrad_sig_set_closed_sig_red)

lemma sig_red_rtrancl_mono:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q" and "F \<subseteq> F'"
  shows "(sig_red sing_reg top_tail F')\<^sup>*\<^sup>* p q"
  using assms(1) by (induct rule: rtranclp_induct, auto dest: sig_red_mono[OF _ assms(2)])

lemma sig_red_rtrancl_subset:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "(sig_red sing_reg top_tail {f\<in>F. sing_reg (lt f) (lt p)})\<^sup>*\<^sup>* p q"
  using assms(1)
proof (induct rule: rtranclp_induct)
  case base
  show ?case by (fact rtranclp.rtrancl_refl)
next
  case (step y z)
  from step(2) assms(2) have "sig_red sing_reg top_tail {f \<in> F. sing_reg (lt f) (lt y)} y z"
    by (rule sig_red_subset)
  moreover have "{f \<in> F. sing_reg (lt f) (lt y)} \<subseteq> {f \<in> F. sing_reg (lt f) (lt p)}"
  proof
    fix f
    assume "f \<in> {f \<in> F. sing_reg (lt f) (lt y)}"
    hence "f \<in> F" and 1: "sing_reg (lt f) (lt y)" by simp_all
    from step(1) have 2: "lt y \<preceq>\<^sub>t lt p" by (rule sig_red_rtrancl_lt)
    from assms(2) have "sing_reg (lt f) (lt p)"
    proof
      assume "sing_reg = (\<preceq>\<^sub>t)"
      with 1 2 show ?thesis by simp
    next
      assume "sing_reg = (\<prec>\<^sub>t)"
      with 1 2 show ?thesis by simp
    qed
    with \<open>f \<in> F\<close> show "f \<in> {f \<in> F. sing_reg (lt f) (lt p)}" by simp
  qed
  ultimately have "sig_red sing_reg top_tail {f \<in> F. sing_reg (lt f) (lt p)} y z"
    by (rule sig_red_mono)
  with step(3) show ?case ..
qed

lemma is_sig_red_is_red: "is_sig_red sing_reg top_tail F p \<Longrightarrow> punit.is_red (rep_list ` F) (rep_list p)"
  by (auto simp: is_sig_red_def punit.is_red_alt dest: sig_red_red)

lemma is_sig_red_monom_mult:
  assumes "is_sig_red sing_reg top_tail F p" and "c \<noteq> 0"
  shows "is_sig_red sing_reg top_tail F (monom_mult c s p)"
proof -
  from assms(1) obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  hence "sig_red sing_reg top_tail F (monom_mult c s p) (monom_mult c s q)"
    using assms(2) by (rule sig_red_monom_mult)
  thus ?thesis unfolding is_sig_red_def ..
qed

lemma is_sig_red_sing_reg_cases:
  "is_sig_red (\<preceq>\<^sub>t) top_tail F p = (is_sig_red (=) top_tail F p \<or> is_sig_red (\<prec>\<^sub>t) top_tail F p)"
  by (auto simp: is_sig_red_def sig_red_sing_reg_cases)

corollary is_sig_red_sing_regI: "is_sig_red sing_reg top_tail F p \<Longrightarrow> is_sig_red (\<preceq>\<^sub>t) top_tail F p"
  by (auto simp: is_sig_red_def intro: sig_red_sing_regI)

lemma is_sig_red_top_tail_cases:
  "is_sig_red sing_reg (\<preceq>) F p = (is_sig_red sing_reg (=) F p \<or> is_sig_red sing_reg (\<prec>) F p)"
  by (auto simp: is_sig_red_def sig_red_top_tail_cases)

corollary is_sig_red_top_tailI: "is_sig_red sing_reg top_tail F p \<Longrightarrow> is_sig_red sing_reg (\<preceq>) F p"
  by (auto simp: is_sig_red_def intro: sig_red_top_tailI)

lemma is_sig_red_singletonI:
  assumes "is_sig_red sing_reg top_tail F r"
  obtains f where "f \<in> F" and "is_sig_red sing_reg top_tail {f} r"
proof -
  from assms obtain r' where "sig_red sing_reg top_tail F r r'" unfolding is_sig_red_def ..
  then obtain f t where "f \<in> F" and t: "sig_red_single sing_reg top_tail r r' f t"
    by (auto simp: sig_red_def)
  have "is_sig_red sing_reg top_tail {f} r" unfolding is_sig_red_def sig_red_def
  proof (intro exI bexI)
    show "f \<in> {f}" by simp
  qed fact
  with \<open>f \<in> F\<close> show ?thesis ..
qed

lemma is_sig_red_singletonD:
  assumes "is_sig_red sing_reg top_tail {f} r" and "f \<in> F"
  shows "is_sig_red sing_reg top_tail F r"
proof -
  from assms(1) obtain r' where "sig_red sing_reg top_tail {f} r r'" unfolding is_sig_red_def ..
  then obtain t where "sig_red_single sing_reg top_tail r r' f t" by (auto simp: sig_red_def)
  show ?thesis unfolding is_sig_red_def sig_red_def by (intro exI bexI, fact+)
qed

lemma is_sig_redD1:
  assumes "is_sig_red sing_reg top_tail F p"
  shows "ord_term_lin.is_le_rel sing_reg"
proof -
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) show ?thesis by (rule sig_red_singleD)
qed

lemma is_sig_redD2:
  assumes "is_sig_red sing_reg top_tail F p"
  shows "ordered_powerprod_lin.is_le_rel top_tail"
proof -
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) show ?thesis by (rule sig_red_singleD)
qed

lemma is_sig_red_addsI:
  assumes "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0" and "punit.lt (rep_list f) adds t"
    and "ord_term_lin.is_le_rel sing_reg" and "ordered_powerprod_lin.is_le_rel top_tail"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)" and "top_tail t (punit.lt (rep_list p))"
  shows "is_sig_red sing_reg top_tail F p"
  unfolding is_sig_red_def
proof
  let ?q = "p - monom_mult ((lookup (rep_list p) t) / punit.lc (rep_list f)) (t - punit.lt (rep_list f)) f"
  show "sig_red sing_reg top_tail F p ?q" unfolding sig_red_def
  proof (intro bexI exI)
    from assms(4) have eq: "(t - punit.lt (rep_list f)) + punit.lt (rep_list f) = t" by (rule adds_minus)
    from assms(4, 5, 7) have "sing_reg ((t - punit.lt (rep_list f)) \<oplus> lt f) (lt p)"
      by (simp only: term_is_le_rel_minus)
    thus "sig_red_single sing_reg top_tail p ?q f (t - punit.lt (rep_list f))"
      by (simp add: assms eq sig_red_singleI)
  qed fact
qed

lemma is_sig_red_addsE:
  assumes "is_sig_red sing_reg top_tail F p"
  obtains f t where "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0"
    and "punit.lt (rep_list f) adds t"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and "top_tail t (punit.lt (rep_list p))"
proof -
  from assms have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) have 1: "rep_list f \<noteq> 0" and 2: "s + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and 3: "sing_reg (s \<oplus> lt f) (lt p)" and 4: "top_tail (s + punit.lt (rep_list f)) (punit.lt (rep_list p))"
    by (rule sig_red_singleD)+
  note \<open>f \<in> F\<close> 2 1
  moreover have "punit.lt (rep_list f) adds s + punit.lt (rep_list f)" by simp
  moreover from 3 have "sing_reg ((s + punit.lt (rep_list f)) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (simp add: add.commute[of s] splus_assoc term_is_le_rel_canc_left[OF *])
  moreover from 4 have "top_tail (s + punit.lt (rep_list f)) (punit.lt (rep_list p))" by simp
  ultimately show ?thesis ..
qed

lemma is_sig_red_top_addsI:
  assumes "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)" and "ord_term_lin.is_le_rel sing_reg"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
  shows "is_sig_red sing_reg (=) F p"
proof -
  note assms(1)
  moreover from assms(3) have "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
  moreover note assms(2, 4, 5) ordered_powerprod_lin.is_le_relI(1) assms(6) refl
  ultimately show ?thesis by (rule is_sig_red_addsI)
qed

lemma is_sig_red_top_addsE:
  assumes "is_sig_red sing_reg (=) F p"
  obtains f where "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
proof -
  from assms obtain f t where 1: "f \<in> F" and 2: "t \<in> keys (rep_list p)" and 3: "rep_list f \<noteq> 0"
    and 4: "punit.lt (rep_list f) adds t"
    and 5: "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and t: "t = punit.lt (rep_list p)" by (rule is_sig_red_addsE)
  note 1 3
  moreover from 2 have "rep_list p \<noteq> 0" by auto
  moreover from 4 have "punit.lt (rep_list f) adds punit.lt (rep_list p)" by (simp only: t)
  moreover from 5 have "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (simp only: t)
  ultimately show ?thesis ..
qed

lemma is_sig_red_top_plusE:
  assumes "is_sig_red sing_reg (=) F p" and "is_sig_red sing_reg (=) F q"
    and "lt p \<preceq>\<^sub>t lt (p + q)" and "lt q \<preceq>\<^sub>t lt (p + q)" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  assumes 1: "is_sig_red sing_reg (=) F (p + q) \<Longrightarrow> thesis"
  assumes 2: "punit.lt (rep_list p) = punit.lt (rep_list q) \<Longrightarrow> punit.lc (rep_list p) + punit.lc (rep_list q) = 0 \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) obtain f1 where "f1 \<in> F" and "rep_list f1 \<noteq> 0" and "rep_list p \<noteq> 0"
    and a: "punit.lt (rep_list f1) adds punit.lt (rep_list p)"
    and b: "sing_reg (punit.lt (rep_list p) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt p)"
    by (rule is_sig_red_top_addsE)
  from assms(2) obtain f2 where "f2 \<in> F" and "rep_list f2 \<noteq> 0" and "rep_list q \<noteq> 0"
    and c: "punit.lt (rep_list f2) adds punit.lt (rep_list q)"
    and d: "sing_reg (punit.lt (rep_list q) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt q)"
    by (rule is_sig_red_top_addsE)
  show ?thesis
  proof (cases "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> punit.lc (rep_list p) + punit.lc (rep_list q) = 0")
    case True
    hence "punit.lt (rep_list p) = punit.lt (rep_list q)" and "punit.lc (rep_list p) + punit.lc (rep_list q) = 0"
      by simp_all
    thus ?thesis by (rule 2)
  next
    case False
    hence disj: "punit.lt (rep_list p) \<noteq> punit.lt (rep_list q) \<or> punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0"
      by simp
    from assms(5) have "ord_term_lin.is_le_rel sing_reg" by (simp add: ord_term_lin.is_le_rel_def)
    have "rep_list (p + q) \<noteq> 0" unfolding rep_list_plus
    proof
      assume eq: "rep_list p + rep_list q = 0"
      have eq2: "punit.lt (rep_list p) = punit.lt (rep_list q)"
      proof (rule ordered_powerprod_lin.linorder_cases)
        assume *: "punit.lt (rep_list p) \<prec> punit.lt (rep_list q)"
        hence "punit.lt (rep_list p + rep_list q) = punit.lt (rep_list q)" by (rule punit.lt_plus_eqI)
        with * zero_min[of "punit.lt (rep_list p)"] show ?thesis by (simp add: eq)
      next
        assume *: "punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
        hence "punit.lt (rep_list p + rep_list q) = punit.lt (rep_list p)" by (rule punit.lt_plus_eqI_2)
        with * zero_min[of "punit.lt (rep_list q)"] show ?thesis by (simp add: eq)
      qed
      with disj have "punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0" by simp
      thus False by (simp add: punit.lc_def eq2 lookup_add[symmetric] eq)
    qed
    have "punit.lt (rep_list (p + q)) = ordered_powerprod_lin.max (punit.lt (rep_list p)) (punit.lt (rep_list q))"
      unfolding rep_list_plus
    proof (rule punit.lt_plus_eq_maxI)
      assume "punit.lt (rep_list p) = punit.lt (rep_list q)"
      with disj show "punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0" by simp
    qed
    hence "punit.lt (rep_list (p + q)) = punit.lt (rep_list p) \<or> punit.lt (rep_list (p + q)) = punit.lt (rep_list q)"
      by (simp add: ordered_powerprod_lin.max_def)
    thus ?thesis
    proof
      assume eq: "punit.lt (rep_list (p + q)) = punit.lt (rep_list p)"
      show ?thesis
      proof (rule 1, rule is_sig_red_top_addsI)
        from a show "punit.lt (rep_list f1) adds punit.lt (rep_list (p + q))" by (simp only: eq)
      next
        from b have "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt p)"
          by (simp only: eq)
        moreover from assms(3) have "... \<preceq>\<^sub>t punit.lt (rep_list f1) \<oplus> lt (p + q)" by (rule splus_mono)
        ultimately show "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt (p + q))"
          using assms(5) by auto
      qed fact+
    next
      assume eq: "punit.lt (rep_list (p + q)) = punit.lt (rep_list q)"
      show ?thesis
      proof (rule 1, rule is_sig_red_top_addsI)
        from c show "punit.lt (rep_list f2) adds punit.lt (rep_list (p + q))" by (simp only: eq)
      next
        from d have "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt q)"
          by (simp only: eq)
        moreover from assms(4) have "... \<preceq>\<^sub>t punit.lt (rep_list f2) \<oplus> lt (p + q)" by (rule splus_mono)
        ultimately show "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt (p + q))"
          using assms(5) by auto
      qed fact+
    qed
  qed
qed

lemma is_sig_red_singleton_monom_multD:
  assumes "is_sig_red sing_reg top_tail {monom_mult c t f} p"
  shows "is_sig_red sing_reg top_tail {f} p"
proof -
  let ?f = "monom_mult c t f"
  from assms obtain s where "s \<in> keys (rep_list p)" and 2: "rep_list ?f \<noteq> 0"
    and 3: "punit.lt (rep_list ?f) adds s"
    and 4: "sing_reg (s \<oplus> lt ?f) (punit.lt (rep_list ?f) \<oplus> lt p)"
    and "top_tail s (punit.lt (rep_list p))"
    by (auto elim: is_sig_red_addsE)
  from 2 have "c \<noteq> 0" and "rep_list f \<noteq> 0"
    by (simp_all add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "f \<noteq> 0" by (auto simp: rep_list_zero)
  with \<open>c \<noteq> 0\<close> have eq1: "lt ?f = t \<oplus> lt f" by (simp add: lt_monom_mult)
  from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> have eq2: "punit.lt (rep_list ?f) = t + punit.lt (rep_list f)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  from assms have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  show ?thesis
  proof (rule is_sig_red_addsI)
    show "f \<in> {f}" by simp
  next
    have "punit.lt (rep_list f) adds t + punit.lt (rep_list f)" by (rule adds_triv_right)
    also from 3 have "... adds s" by (simp only: eq2)
    finally show "punit.lt (rep_list f) adds s" .
  next
    from 4 have "sing_reg (t \<oplus> (s \<oplus> lt f)) (t \<oplus> (punit.lt (rep_list f) \<oplus> lt p))"
      by (simp add: eq1 eq2 splus_assoc splus_left_commute)
    with * show "sing_reg (s \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
      by (simp add: term_is_le_rel_canc_left)
  next
    from assms show "ordered_powerprod_lin.is_le_rel top_tail" by (rule is_sig_redD2)
  qed fact+
qed

lemma is_sig_red_top_singleton_monom_multI:
  assumes "is_sig_red sing_reg (=) {f} p" and "c \<noteq> 0"
    and "t adds punit.lt (rep_list p) - punit.lt (rep_list f)"
  shows "is_sig_red sing_reg (=) {monom_mult c t f} p"
proof -
  let ?f = "monom_mult c t f"
  from assms have 2: "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and 3: "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and 4: "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (auto elim: is_sig_red_top_addsE)
  hence "f \<noteq> 0" by (auto simp: rep_list_zero)
  with \<open>c \<noteq> 0\<close> have eq1: "lt ?f = t \<oplus> lt f" by (simp add: lt_monom_mult)
  from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> have eq2: "punit.lt (rep_list ?f) = t + punit.lt (rep_list f)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  from assms(1) have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  show ?thesis
  proof (rule is_sig_red_top_addsI)
    show "?f \<in> {?f}" by simp
  next
    from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> show "rep_list ?f \<noteq> 0"
      by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  next
    from assms(3) have "t + punit.lt (rep_list f) adds
                        (punit.lt (rep_list p) - punit.lt (rep_list f)) + punit.lt (rep_list f)"
      by (simp only: adds_canc)
    also from 3 have "... = punit.lt (rep_list p)" by (rule adds_minus)
    finally show "punit.lt (rep_list ?f) adds punit.lt (rep_list p)" by (simp only: eq2)
  next
    from 4 * show "sing_reg (punit.lt (rep_list p) \<oplus> lt ?f) (punit.lt (rep_list ?f) \<oplus> lt p)"
      by (simp add: eq1 eq2 term_is_le_rel_canc_left splus_assoc splus_left_commute)
  qed fact+
qed

lemma is_sig_red_cong':
  assumes "is_sig_red sing_reg top_tail F p" and "lt p = lt q" and "rep_list p = rep_list q"
  shows "is_sig_red sing_reg top_tail F q"
proof -
  from assms(1) have 1: "ord_term_lin.is_le_rel sing_reg" and 2: "ordered_powerprod_lin.is_le_rel top_tail"
    by (rule is_sig_redD1, rule is_sig_redD2)
  from assms(1) obtain f t where "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0"
    and "punit.lt (rep_list f) adds t"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and "top_tail t (punit.lt (rep_list p))" by (rule is_sig_red_addsE)
  from this(1-4) 1 2 this(5, 6) show ?thesis unfolding assms(2, 3) by (rule is_sig_red_addsI)
qed

lemma is_sig_red_cong:
  "lt p = lt q \<Longrightarrow> rep_list p = rep_list q \<Longrightarrow>
      is_sig_red sing_reg top_tail F p \<longleftrightarrow> is_sig_red sing_reg top_tail F q"
  by (auto intro: is_sig_red_cong')

lemma is_sig_red_top_cong:
  assumes "is_sig_red sing_reg (=) F p" and "rep_list q \<noteq> 0" and "lt p = lt q"
    and "punit.lt (rep_list p) = punit.lt (rep_list q)"
  shows "is_sig_red sing_reg (=) F q"
proof -
  from assms(1) have 1: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  from assms(1) obtain f where "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (rule is_sig_red_top_addsE)
  from this(1, 2) assms(2) this(4) 1 this(5) show ?thesis
    unfolding assms(3, 4) by (rule is_sig_red_top_addsI)
qed

lemma sig_irredE_dgrad_max_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
  obtains q where "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q" and "\<not> is_sig_red sing_reg top_tail F q"
proof -
  let ?Q = "{q. (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q}"
  from assms have "wfP (sig_red sing_reg top_tail F)\<inverse>\<inverse>" by (rule sig_red_wf_dgrad_max_set)
  moreover have "p \<in> ?Q" by simp
  ultimately obtain q where "q \<in> ?Q" and "\<And>x. (sig_red sing_reg top_tail F)\<inverse>\<inverse> x q \<Longrightarrow> x \<notin> ?Q"
    by (rule wfE_min[to_pred], blast)
  hence 1: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
    and 2: "\<And>x. sig_red sing_reg top_tail F q x \<Longrightarrow> \<not> (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x"
    by simp_all
  show ?thesis
  proof
    show "\<not> is_sig_red sing_reg top_tail F q"
    proof
      assume "is_sig_red sing_reg top_tail F q"
      then obtain x where 3: "sig_red sing_reg top_tail F q x" unfolding is_sig_red_def ..
      hence "\<not> (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x" by (rule 2)
      moreover from 1 3 have "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x" ..
      ultimately show False ..
    qed
  qed fact
qed

lemma is_sig_red_mono:
  "is_sig_red sing_reg top_tail F p \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> is_sig_red sing_reg top_tail F' p"
  by (auto simp: is_sig_red_def dest: sig_red_mono)

lemma is_sig_red_Un:
  "is_sig_red sing_reg top_tail (A \<union> B) p \<longleftrightarrow> (is_sig_red sing_reg top_tail A p \<or> is_sig_red sing_reg top_tail B p)"
  by (auto simp: is_sig_red_def sig_red_Un)

lemma is_sig_redD_lt:
  assumes "is_sig_red (\<preceq>\<^sub>t) top_tail {f} p"
  shows "lt f \<preceq>\<^sub>t lt p"
proof -
  from assms obtain s where "rep_list f \<noteq> 0" and "s \<in> keys (rep_list p)"
    and 1: "punit.lt (rep_list f) adds s" and 2: "s \<oplus> lt f \<preceq>\<^sub>t punit.lt (rep_list f) \<oplus> lt p"
    by (auto elim!: is_sig_red_addsE)
  from 1 obtain t where eq: "s = punit.lt (rep_list f) + t" by (rule addsE)
  hence "punit.lt (rep_list f) \<oplus> (t \<oplus> lt f) = s \<oplus> lt f" by (simp add: splus_assoc)
  also note 2
  finally have "t \<oplus> lt f \<preceq>\<^sub>t lt p" by (rule ord_term_canc)
  have "0 \<preceq> t" by (fact zero_min)
  hence "0 \<oplus> lt f \<preceq>\<^sub>t t \<oplus> lt f" by (rule splus_mono_left)
  hence "lt f \<preceq>\<^sub>t t \<oplus> lt f" by (simp add: term_simps)
  thus ?thesis using \<open>t \<oplus> lt f \<preceq>\<^sub>t lt p\<close> by simp
qed

lemma is_sig_red_regularD_lt:
  assumes "is_sig_red (\<prec>\<^sub>t) top_tail {f} p"
  shows "lt f \<prec>\<^sub>t lt p"
proof -
  from assms obtain s where "rep_list f \<noteq> 0" and "s \<in> keys (rep_list p)"
    and 1: "punit.lt (rep_list f) adds s" and 2: "s \<oplus> lt f \<prec>\<^sub>t punit.lt (rep_list f) \<oplus> lt p"
    by (auto elim!: is_sig_red_addsE)
  from 1 obtain t where eq: "s = punit.lt (rep_list f) + t" by (rule addsE)
  hence "punit.lt (rep_list f) \<oplus> (t \<oplus> lt f) = s \<oplus> lt f" by (simp add: splus_assoc)
  also note 2
  finally have "t \<oplus> lt f \<prec>\<^sub>t lt p" by (rule ord_term_strict_canc)
  have "0 \<preceq> t" by (fact zero_min)
  hence "0 \<oplus> lt f \<preceq>\<^sub>t t \<oplus> lt f" by (rule splus_mono_left)
  hence "lt f \<preceq>\<^sub>t t \<oplus> lt f" by (simp add: term_simps)
  thus ?thesis using \<open>t \<oplus> lt f \<prec>\<^sub>t lt p\<close> by (rule ord_term_lin.le_less_trans)
qed

lemma sig_irred_regular_self: "\<not> is_sig_red (\<prec>\<^sub>t) top_tail {p} p"
  by (auto dest: is_sig_red_regularD_lt)

subsubsection \<open>Signature Gr\"obner Bases\<close>

definition sig_red_zero :: "('t \<Rightarrow>'t \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red_zero sing_reg F r \<longleftrightarrow> (\<exists>s. (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s \<and> rep_list s = 0)"

definition is_sig_GB_in :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_in d G u \<longleftrightarrow> (\<forall>r. lt r = u \<longrightarrow> r \<in> dgrad_sig_set d \<longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r)"

definition is_sig_GB_upt :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_upt d G u \<longleftrightarrow>
            (G \<subseteq> dgrad_sig_set d \<and> (\<forall>v. v \<prec>\<^sub>t u \<longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<longrightarrow>
                                          component_of_term v < length fs \<longrightarrow> is_sig_GB_in d G v))"

definition is_min_sig_GB :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> bool"
  where "is_min_sig_GB d G \<longleftrightarrow> G \<subseteq> dgrad_sig_set d \<and>
                                (\<forall>u. d (pp_of_term u) \<le> dgrad_max d \<longrightarrow> component_of_term u < length fs \<longrightarrow>
                                      is_sig_GB_in d G u) \<and>
                                (\<forall>g\<in>G. \<not> is_sig_red (\<preceq>\<^sub>t) (=) (G - {g}) g)"

definition is_syz_sig :: "('a \<Rightarrow> nat) \<Rightarrow> 't \<Rightarrow> bool"
  where "is_syz_sig d u \<longleftrightarrow> (\<exists>s\<in>dgrad_sig_set d. s \<noteq> 0 \<and> lt s = u \<and> rep_list s = 0)"

lemma sig_red_zeroI:
  assumes "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  shows "sig_red_zero sing_reg F r"
  unfolding sig_red_zero_def using assms by blast

lemma sig_red_zeroE:
  assumes "sig_red_zero sing_reg F r"
  obtains s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  using assms unfolding sig_red_zero_def by blast

lemma sig_red_zero_monom_mult:
  assumes "sig_red_zero sing_reg F r"
  shows "sig_red_zero sing_reg F (monom_mult c t r)"
proof -
  from assms obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) have "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* (monom_mult c t r) (monom_mult c t s)"
    by (rule sig_red_rtrancl_monom_mult)
  moreover have "rep_list (monom_mult c t s) = 0" by (simp add: rep_list_monom_mult \<open>rep_list s = 0\<close>)
  ultimately show ?thesis by (rule sig_red_zeroI)
qed

lemma sig_red_zero_sing_regI:
  assumes "sig_red_zero sing_reg G p"
  shows "sig_red_zero (\<preceq>\<^sub>t) G p"
proof -
  from assms obtain s where "(sig_red sing_reg (\<preceq>) G)\<^sup>*\<^sup>* p s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) have "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p s" by (rule sig_red_rtrancl_sing_regI)
  thus ?thesis using \<open>rep_list s = 0\<close> by (rule sig_red_zeroI)
qed

lemma sig_red_zero_nonzero:
  assumes "sig_red_zero sing_reg F r" and "rep_list r \<noteq> 0" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "is_sig_red sing_reg (=) F r"
proof -
  from assms(1) obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) assms(2) show ?thesis
  proof (induct rule: converse_rtranclp_induct)
    case base
    thus ?case using \<open>rep_list s = 0\<close> ..
  next
    case (step y z)
    from step(1) obtain f t where "f \<in> F" and *: "sig_red_single sing_reg (\<preceq>) y z f t"
      unfolding sig_red_def by blast
    from this(2) have 1: "rep_list f \<noteq> 0" and 2: "t + punit.lt (rep_list f) \<in> keys (rep_list y)"
      and 3: "z = y - monom_mult (lookup (rep_list y) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
      and 4: "ord_term_lin.is_le_rel sing_reg" and 5: "sing_reg (t \<oplus> lt f) (lt y)"
      by (rule sig_red_singleD)+
    show ?case
    proof (cases "t + punit.lt (rep_list f) = punit.lt (rep_list y)")
      case True
      show ?thesis unfolding is_sig_red_def
      proof
        show "sig_red sing_reg (=) F y z" unfolding sig_red_def
        proof (intro bexI exI)
          from 1 2 3 4 ordered_powerprod_lin.is_le_relI(1) 5 True
          show "sig_red_single sing_reg (=) y z f t" by (rule sig_red_singleI)
        qed fact
      qed
    next
      case False
      from 2 have "t + punit.lt (rep_list f) \<preceq> punit.lt (rep_list y)" by (rule punit.lt_max_keys)
      with False have "t + punit.lt (rep_list f) \<prec> punit.lt (rep_list y)" by simp
      with 1 2 3 4 ordered_powerprod_lin.is_le_relI(3) 5 have "sig_red_single sing_reg (\<prec>) y z f t"
        by (rule sig_red_singleI)
      hence "punit.lt (rep_list y) \<in> keys (rep_list z)"
        and lt_z: "punit.lt (rep_list z) = punit.lt (rep_list y)"
        by (rule sig_red_single_tail_lt_in_keys_rep_list, rule sig_red_single_tail_lt_rep_list)
      from this(1) have "rep_list z \<noteq> 0" by auto
      hence "is_sig_red sing_reg (=) F z" by (rule step(3))
      then obtain g where "g \<in> F" and "rep_list g \<noteq> 0"
        and "punit.lt (rep_list g) adds punit.lt (rep_list z)"
        and a: "sing_reg (punit.lt (rep_list z) \<oplus> lt g) (punit.lt (rep_list g) \<oplus> lt z)"
        by (rule is_sig_red_top_addsE)
      from this(3) have "punit.lt (rep_list g) adds punit.lt (rep_list y)" by (simp only: lt_z)
      with \<open>g \<in> F\<close> \<open>rep_list g \<noteq> 0\<close> step(4) show ?thesis
      proof (rule is_sig_red_top_addsI)
        from \<open>is_sig_red sing_reg (=) F z\<close> show "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
      next
        from \<open>sig_red_single sing_reg (\<prec>) y z f t\<close> have "lt z \<preceq>\<^sub>t lt y" by (rule sig_red_single_lt)
        from assms(3) show "sing_reg (punit.lt (rep_list y) \<oplus> lt g) (punit.lt (rep_list g) \<oplus> lt y)"
        proof
          assume "sing_reg = (\<preceq>\<^sub>t)"
          from a have "punit.lt (rep_list y) \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt z"
            by (simp only: lt_z \<open>sing_reg = (\<preceq>\<^sub>t)\<close>)
          also from \<open>lt z \<preceq>\<^sub>t lt y\<close> have "... \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt y" by (rule splus_mono)
          finally show ?thesis by (simp only: \<open>sing_reg = (\<preceq>\<^sub>t)\<close>)
        next
          assume "sing_reg = (\<prec>\<^sub>t)"
          from a have "punit.lt (rep_list y) \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt z"
            by (simp only: lt_z \<open>sing_reg = (\<prec>\<^sub>t)\<close>)
          also from \<open>lt z \<preceq>\<^sub>t lt y\<close> have "... \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt y" by (rule splus_mono)
          finally show ?thesis by (simp only: \<open>sing_reg = (\<prec>\<^sub>t)\<close>)
        qed
      qed
    qed
  qed
qed

lemma sig_red_zero_mono: "sig_red_zero sing_reg F p \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> sig_red_zero sing_reg F' p"
  by (auto simp: sig_red_zero_def dest: sig_red_rtrancl_mono)

lemma sig_red_zero_subset:
  assumes "sig_red_zero sing_reg F p" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "sig_red_zero sing_reg {f\<in>F. sing_reg (lt f) (lt p)} p"
proof -
  from assms(1) obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* p s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) assms(2) have "(sig_red sing_reg (\<preceq>) {f\<in>F. sing_reg (lt f) (lt p)})\<^sup>*\<^sup>* p s"
    by (rule sig_red_rtrancl_subset)
  thus ?thesis using \<open>rep_list s = 0\<close> by (rule sig_red_zeroI)
qed

lemma sig_red_zero_idealI:
  assumes "sig_red_zero sing_reg F p"
  shows "rep_list p \<in> ideal (rep_list ` F)"
proof -
  from assms obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* p s" and "rep_list s = 0" by (rule sig_red_zeroE)
  from this(1) have "(punit.red (rep_list ` F))\<^sup>*\<^sup>* (rep_list p) (rep_list s)" by (rule sig_red_red_rtrancl)
  hence "(punit.red (rep_list ` F))\<^sup>*\<^sup>* (rep_list p) 0" by (simp only: \<open>rep_list s = 0\<close>)
  thus ?thesis by (rule punit.red_rtranclp_0_in_pmdl[simplified])
qed

lemma is_sig_GB_inI:
  assumes "\<And>r. lt r = u \<Longrightarrow> r \<in> dgrad_sig_set d \<Longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r"
  shows "is_sig_GB_in d G u"
  unfolding is_sig_GB_in_def using assms by blast

lemma is_sig_GB_inD:
  assumes "is_sig_GB_in d G u" and "r \<in> dgrad_sig_set d" and "lt r = u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  using assms unfolding is_sig_GB_in_def by blast

lemma is_sig_GB_inI_triv:
  assumes "\<not> d (pp_of_term u) \<le> dgrad_max d \<or> \<not> component_of_term u < length fs"
  shows "is_sig_GB_in d G u"
proof (rule is_sig_GB_inI)
  fix r::"'t \<Rightarrow>\<^sub>0 'b"
  assume "lt r = u" and "r \<in> dgrad_sig_set d"
  show "sig_red_zero (\<preceq>\<^sub>t) G r"
  proof (cases "r = 0")
    case True
    hence "rep_list r = 0" by (simp only: rep_list_zero)
    with rtrancl_refl[to_pred] show ?thesis by (rule sig_red_zeroI)
  next
    case False
    from \<open>r \<in> dgrad_sig_set d\<close> have "d (lp r) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
    moreover from \<open>r \<in> dgrad_sig_set d\<close> False have "component_of_term (lt r) < length fs"
      by (rule dgrad_sig_setD_lt)
    ultimately show ?thesis using assms by (simp add: \<open>lt r = u\<close>)
  qed
qed

lemma is_sig_GB_in_mono: "is_sig_GB_in d G u \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> is_sig_GB_in d G' u"
  by (auto simp: is_sig_GB_in_def dest: sig_red_zero_mono)

lemma is_sig_GB_uptI:
  assumes "G \<subseteq> dgrad_sig_set d"
    and "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<Longrightarrow> component_of_term v < length fs \<Longrightarrow>
          is_sig_GB_in d G v"
  shows "is_sig_GB_upt d G u"
  unfolding is_sig_GB_upt_def using assms by blast

lemma is_sig_GB_uptD1:
  assumes "is_sig_GB_upt d G u"
  shows "G \<subseteq> dgrad_sig_set d"
  using assms unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD2:
  assumes "is_sig_GB_upt d G u" and "v \<prec>\<^sub>t u"
  shows "is_sig_GB_in d G v"
  using assms is_sig_GB_inI_triv unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD3:
  assumes "is_sig_GB_upt d G u" and "r \<in> dgrad_sig_set d" and "lt r \<prec>\<^sub>t u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  by (rule is_sig_GB_inD, rule is_sig_GB_uptD2, fact+, fact refl)

lemma is_sig_GB_upt_le:
  assumes "is_sig_GB_upt d G u" and "v \<preceq>\<^sub>t u"
  shows "is_sig_GB_upt d G v"
proof (rule is_sig_GB_uptI)
  from assms(1) show "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
next
  fix w
  assume "w \<prec>\<^sub>t v"
  hence "w \<prec>\<^sub>t u" using assms(2) by (rule ord_term_lin.less_le_trans)
  with assms(1) show "is_sig_GB_in d G w" by (rule is_sig_GB_uptD2)
qed

lemma is_sig_GB_upt_mono:
  "is_sig_GB_upt d G u \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> G' \<subseteq> dgrad_sig_set d \<Longrightarrow> is_sig_GB_upt d G' u"
  by (auto simp: is_sig_GB_upt_def dest!: is_sig_GB_in_mono)

lemma is_sig_GB_upt_is_Groebner_basis:
  assumes "dickson_grading d" and "hom_grading d" and "G \<subseteq> dgrad_sig_set' j d"
    and "\<And>u. component_of_term u < j \<Longrightarrow> is_sig_GB_in d G u"
  shows "punit.is_Groebner_basis (rep_list ` G)"
  using assms(1)
proof (rule punit.weak_GB_is_strong_GB_dgrad_p_set[simplified])
  from assms(3) have "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  with assms(1) show "rep_list ` G \<subseteq> punit_dgrad_max_set d" by (rule dgrad_max_3)
next
  fix f::"'a \<Rightarrow>\<^sub>0 'b"
  assume "f \<in> punit_dgrad_max_set d"
  from assms(3) have G_sub: "G \<subseteq> sig_inv_set' j" by (simp add: dgrad_sig_set'_def)
  assume "f \<in> ideal (rep_list ` G)"
  also from rep_list_subset_ideal_sig_inv_set[OF G_sub] have "... \<subseteq> ideal (set (take j fs))"
    by (rule ideal.span_subset_spanI)
  finally have "f \<in> ideal (set (take j fs))" .
  with assms(2) \<open>f \<in> punit_dgrad_max_set d\<close> obtain r where "r \<in> dgrad_sig_set d"
    and "r \<in> dgrad_sig_set' j d" and f: "f = rep_list r"
    by (rule in_idealE_rep_list_dgrad_sig_set_take)
  from this(2) have "r \<in> sig_inv_set' j" by (simp add: dgrad_sig_set'_def)
  show "(punit.red (rep_list ` G))\<^sup>*\<^sup>* f 0"
  proof (cases "r = 0")
    case True
    thus ?thesis by (simp add: f rep_list_zero)
  next
    case False
    hence "lt r \<in> keys r" by (rule lt_in_keys)
    with \<open>r \<in> sig_inv_set' j\<close> have "component_of_term (lt r) < j" by (rule sig_inv_setD')
    hence "is_sig_GB_in d G (lt r)" by (rule assms(4))
    hence "sig_red_zero (\<preceq>\<^sub>t) G r" using \<open>r \<in> dgrad_sig_set d\<close> refl by (rule is_sig_GB_inD)
    then obtain s where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" and s: "rep_list s = 0" by (rule sig_red_zeroE)
    from this(1) have "(punit.red (rep_list ` G))\<^sup>*\<^sup>* (rep_list r) (rep_list s)"
      by (rule sig_red_red_rtrancl)
    thus ?thesis by (simp only: f s)
  qed
qed

lemma is_sig_GB_is_Groebner_basis:
  assumes "dickson_grading d" and "hom_grading d" and "G \<subseteq> dgrad_max_set d" and "\<And>u. is_sig_GB_in d G u"
  shows "punit.is_Groebner_basis (rep_list ` G)"
  using assms(1)
proof (rule punit.weak_GB_is_strong_GB_dgrad_p_set[simplified])
  from assms(1, 3) show "rep_list ` G \<subseteq> punit_dgrad_max_set d" by (rule dgrad_max_3)
next
  fix f::"'a \<Rightarrow>\<^sub>0 'b"
  assume "f \<in> punit_dgrad_max_set d"
  assume "f \<in> ideal (rep_list ` G)"
  also from rep_list_subset_ideal have "... \<subseteq> ideal (set fs)" by (rule ideal.span_subset_spanI)
  finally have "f \<in> ideal (set fs)" .
  with assms(2) \<open>f \<in> punit_dgrad_max_set d\<close> obtain r where "r \<in> dgrad_sig_set d" and f: "f = rep_list r"
    by (rule in_idealE_rep_list_dgrad_sig_set)
  from assms(4) this(1) refl have "sig_red_zero (\<preceq>\<^sub>t) G r" by (rule is_sig_GB_inD)
  then obtain s where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" and s: "rep_list s = 0" by (rule sig_red_zeroE)
  from this(1) have "(punit.red (rep_list ` G))\<^sup>*\<^sup>* (rep_list r) (rep_list s)"
    by (rule sig_red_red_rtrancl)
  thus "(punit.red (rep_list ` G))\<^sup>*\<^sup>* f 0" by (simp only: f s)
qed

lemma sig_red_zero_is_red:
  assumes "sig_red_zero sing_reg F r" and "rep_list r \<noteq> 0"
  shows "is_sig_red sing_reg (\<preceq>) F r"
proof -
  from assms(1) obtain s where *: "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(2) assms(2) have "r \<noteq> s" by auto
  with * show ?thesis by (induct rule: converse_rtranclp_induct, auto simp: is_sig_red_def)
qed

lemma is_sig_red_sing_top_is_red_zero:
  assumes "dickson_grading d" and "is_sig_GB_upt d G u" and "a \<in> dgrad_sig_set d" and "lt a = u"
    and "is_sig_red (=) (=) G a" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G a"
  shows "sig_red_zero (\<preceq>\<^sub>t) G a"
proof -
  from assms(5) obtain g where "g \<in> G" and "rep_list g \<noteq> 0" and "rep_list a \<noteq> 0"
    and 1: "punit.lt (rep_list g) adds punit.lt (rep_list a)"
    and 2: "punit.lt (rep_list a) \<oplus> lt g = punit.lt (rep_list g) \<oplus> lt a"
    by (rule is_sig_red_top_addsE)
  from this(2, 3) have "g \<noteq> 0" and "a \<noteq> 0" by (auto simp: rep_list_zero)
  hence "lc g \<noteq> 0" and "lc a \<noteq> 0" using lc_not_0 by blast+
  from 1 have 3: "(punit.lt (rep_list a) - punit.lt (rep_list g)) \<oplus> lt g = lt a"
    by (simp add: term_is_le_rel_minus 2)
  define g' where "g' = monom_mult (lc a / lc g) (punit.lt (rep_list a) - punit.lt (rep_list g)) g"
  from \<open>g \<noteq> 0\<close> \<open>lc a \<noteq> 0\<close> \<open>lc g \<noteq> 0\<close> have lt_g': "lt g' = lt a" by (simp add: g'_def lt_monom_mult 3)
  from \<open>lc g \<noteq> 0\<close> have lc_g': "lc g' = lc a" by (simp add: g'_def)
  from assms(1) have "g' \<in> dgrad_sig_set d" unfolding g'_def
  proof (rule dgrad_sig_set_closed_monom_mult)
    from assms(1) 1 have "d (punit.lt (rep_list a) - punit.lt (rep_list g)) \<le> d (punit.lt (rep_list a))"
      by (rule dickson_grading_minus)
    also from assms(1, 3) have "... \<le> dgrad_max d" by (rule dgrad_sig_setD_rep_list_lt)
    finally show "d (punit.lt (rep_list a) - punit.lt (rep_list g)) \<le> dgrad_max d" .
  next
    from assms(2) have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
    with \<open>g \<in> G\<close> show "g \<in> dgrad_sig_set d" ..
  qed
  with assms(3) have b_in: "a - g' \<in> dgrad_sig_set d" (is "?b \<in> _")
    by (rule dgrad_sig_set_closed_minus)
  from 1 have 4: "punit.lt (rep_list a) - punit.lt (rep_list g) + punit.lt (rep_list g) =
                  punit.lt (rep_list a)"
    by (rule adds_minus)

  show ?thesis
  proof (cases "lc a / lc g = punit.lc (rep_list a) / punit.lc (rep_list g)")
    case True
    have "sig_red_single (=) (=) a ?b g (punit.lt (rep_list a) - punit.lt (rep_list g))"
    proof (rule sig_red_singleI)
      show "punit.lt (rep_list a) - punit.lt (rep_list g) + punit.lt (rep_list g) \<in> keys (rep_list a)"
        unfolding 4 using \<open>rep_list a \<noteq> 0\<close> by (rule punit.lt_in_keys)
    next
      show "?b =
            a - monom_mult
             (lookup (rep_list a) (punit.lt (rep_list a) - punit.lt (rep_list g) + punit.lt (rep_list g)) /
              punit.lc (rep_list g))
             (punit.lt (rep_list a) - punit.lt (rep_list g)) g"
        by (simp add: g'_def 4 punit.lc_def True)
    qed (simp_all add: 3 4 \<open>rep_list g \<noteq> 0\<close>)
    hence "sig_red (=) (=) G a ?b" unfolding sig_red_def using \<open>g \<in> G\<close> by blast
    hence "sig_red (\<preceq>\<^sub>t) (\<preceq>) G a ?b" by (auto dest: sig_red_sing_regI sig_red_top_tailI)
    hence 5: "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* a ?b" ..
    show ?thesis
    proof (cases "?b = 0")
      case True
      hence "rep_list ?b = 0" by (simp only: rep_list_zero)
      with 5 show ?thesis by (rule sig_red_zeroI)
    next
      case False
      hence "lt ?b \<prec>\<^sub>t lt a" using lt_g' lc_g' by (rule lt_minus_lessI)
      hence "lt ?b \<prec>\<^sub>t u" by (simp only: assms(4))
      with assms(2) b_in have "sig_red_zero (\<preceq>\<^sub>t) G ?b" by (rule is_sig_GB_uptD3)
      then obtain s where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* ?b s" and "rep_list s = 0" by (rule sig_red_zeroE)
      from 5 this(1) have "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* a s" by (rule rtranclp_trans)
      thus ?thesis using \<open>rep_list s = 0\<close> by (rule sig_red_zeroI)
    qed
  next
    case False
    from \<open>rep_list g \<noteq> 0\<close> \<open>lc g \<noteq> 0\<close> \<open>lc a \<noteq> 0\<close> have 5: "punit.lt (rep_list g') = punit.lt (rep_list a)"
      by (simp add: g'_def rep_list_monom_mult punit.lt_monom_mult 4)
    have 6: "punit.lc (rep_list g') = (lc a / lc g) * punit.lc (rep_list g)"
      by (simp add: g'_def rep_list_monom_mult)
    also have 7: "... \<noteq> punit.lc (rep_list a)"
    proof
      assume "lc a / lc g * punit.lc (rep_list g) = punit.lc (rep_list a)"
      moreover from \<open>rep_list g \<noteq> 0\<close> have "punit.lc (rep_list g) \<noteq> 0" by (rule punit.lc_not_0)
      ultimately have "lc a / lc g = punit.lc (rep_list a) / punit.lc (rep_list g)"
        by (simp add: field_simps)
      with False show False ..
    qed
    finally have "punit.lc (rep_list g') \<noteq> punit.lc (rep_list a)" .
    with 5 have 8: "punit.lt (rep_list ?b) = punit.lt (rep_list a)" unfolding rep_list_minus
      by (rule punit.lt_minus_eqI_3)
    hence "punit.lc (rep_list ?b) = punit.lc (rep_list a) - (lc a / lc g) * punit.lc (rep_list g)"
      unfolding 6[symmetric] by (simp only: punit.lc_def lookup_minus rep_list_minus 5)
    also have "... \<noteq> 0"
    proof
      assume "punit.lc (rep_list a) - lc a / lc g * punit.lc (rep_list g) = 0"
      hence "lc a / lc g * punit.lc (rep_list g) = punit.lc (rep_list a)" by simp
      with 7 show False ..
    qed
    finally have "rep_list ?b \<noteq> 0" by (simp add: punit.lc_eq_zero_iff)
    hence "?b \<noteq> 0" by (auto simp: rep_list_zero)
    hence "lt ?b \<prec>\<^sub>t lt a" using lt_g' lc_g' by (rule lt_minus_lessI)
    hence "lt ?b \<prec>\<^sub>t u" by (simp only: assms(4))
    with assms(2) b_in have "sig_red_zero (\<preceq>\<^sub>t) G ?b" by (rule is_sig_GB_uptD3)
    moreover note \<open>rep_list ?b \<noteq> 0\<close>
    moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
    ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G ?b" by (rule sig_red_zero_nonzero)
    then obtain g0 where "g0 \<in> G" and "rep_list g0 \<noteq> 0"
      and 9: "punit.lt (rep_list g0) adds punit.lt (rep_list ?b)"
      and 10: "punit.lt (rep_list ?b) \<oplus> lt g0 \<preceq>\<^sub>t punit.lt (rep_list g0) \<oplus> lt ?b"
      by (rule is_sig_red_top_addsE)
    from 9 have "punit.lt (rep_list g0) adds punit.lt (rep_list a)" by (simp only: 8)
    from 10 have "punit.lt (rep_list a) \<oplus> lt g0 \<preceq>\<^sub>t punit.lt (rep_list g0) \<oplus> lt ?b" by (simp only: 8)
    also from \<open>lt ?b \<prec>\<^sub>t lt a\<close> have "... \<prec>\<^sub>t punit.lt (rep_list g0) \<oplus> lt a" by (rule splus_mono_strict)
    finally have "punit.lt (rep_list a) \<oplus> lt g0 \<prec>\<^sub>t punit.lt (rep_list g0) \<oplus> lt a" .
    have "is_sig_red (\<prec>\<^sub>t) (=) G a"
    proof (rule is_sig_red_top_addsI)
      show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
    qed fact+
    with assms(6) show ?thesis ..
  qed
qed

lemma sig_regular_reduced_unique:
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
    and "lt p = lt q" and "lc p = lc q" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q"
  shows "rep_list p = rep_list q"
proof (rule ccontr)
  assume "rep_list p \<noteq> rep_list q"
  hence "rep_list (p - q) \<noteq> 0" by (auto simp: rep_list_minus)
  hence "p - q \<noteq> 0" by (auto simp: rep_list_zero)
  hence "p + (- q) \<noteq> 0" by simp
  moreover from assms(4) have "lt (- q) = lt p" by simp
  moreover from assms(5) have "lc (- q) = - lc p" by simp
  ultimately have "lt (p + (- q)) \<prec>\<^sub>t lt p" by (rule lt_plus_lessI)
  hence "lt (p - q) \<prec>\<^sub>t lt q" using assms(4) by simp
  with assms(1) have "is_sig_GB_in d G (lt (p - q))" by (rule is_sig_GB_uptD2)
  moreover from assms(2, 3) have "p - q \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_minus)
  ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (p - q)" using refl by (rule is_sig_GB_inD)
  hence "is_sig_red (\<preceq>\<^sub>t) (\<preceq>) G (p - q)" using \<open>rep_list (p - q) \<noteq> 0\<close> by (rule sig_red_zero_is_red)
  then obtain g t where "g \<in> G" and t: "t \<in> keys (rep_list (p - q))" and "rep_list g \<noteq> 0"
    and adds: "punit.lt (rep_list g) adds t" and "t \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt (p - q)"
    by (rule is_sig_red_addsE)
  note this(5)
  also from \<open>lt (p - q) \<prec>\<^sub>t lt q\<close> have "punit.lt (rep_list g) \<oplus> lt (p - q) \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt q"
    by (rule splus_mono_strict)
  finally have 1: "t \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt q" .
  hence 2: "t \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt p" by (simp only: assms(4))
  from t keys_minus have "t \<in> keys (rep_list p) \<union> keys (rep_list q)" unfolding rep_list_minus ..
  thus False
  proof
    assume t_in: "t \<in> keys (rep_list p)"
    hence "t \<preceq> punit.lt (rep_list p)" by (rule punit.lt_max_keys)
    with \<open>g \<in> G\<close> t_in \<open>rep_list g \<noteq> 0\<close> adds ord_term_lin.is_le_relI(3) ordered_powerprod_lin.is_le_relI(2) 2
    have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" by (rule is_sig_red_addsI)
    with assms(6) show False ..
  next
    assume t_in: "t \<in> keys (rep_list q)"
    hence "t \<preceq> punit.lt (rep_list q)" by (rule punit.lt_max_keys)
    with \<open>g \<in> G\<close> t_in \<open>rep_list g \<noteq> 0\<close> adds ord_term_lin.is_le_relI(3) ordered_powerprod_lin.is_le_relI(2) 1
    have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q" by (rule is_sig_red_addsI)
    with assms(7) show False ..
  qed
qed

corollary sig_regular_reduced_unique':
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
    and "lt p = lt q" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q"
  shows "punit.monom_mult (lc q) 0 (rep_list p) = punit.monom_mult (lc p) 0 (rep_list q)"
proof (cases "p = 0 \<or> q = 0")
  case True
  thus ?thesis by (auto simp: rep_list_zero)
next
  case False
  hence "p \<noteq> 0" and "q \<noteq> 0" by simp_all
  hence "lc p \<noteq> 0" and "lc q \<noteq> 0" by (simp_all add: lc_not_0)
  let ?p = "monom_mult (lc q) 0 p"
  let ?q = "monom_mult (lc p) 0 q"
  have "lt ?q = lt q" by (simp add: lt_monom_mult[OF \<open>lc p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>] splus_zero)
  with assms(1) have "is_sig_GB_upt d G (lt ?q)" by simp
  moreover from assms(2) have "?p \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult_zero)
  moreover from assms(3) have "?q \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult_zero)
  moreover from \<open>lt ?q = lt q\<close> have "lt ?p = lt ?q"
    by (simp add: lt_monom_mult[OF \<open>lc q \<noteq> 0\<close> \<open>p \<noteq> 0\<close>] splus_zero assms(4))
  moreover have "lc ?p = lc ?q" by simp
  moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?p"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?p"
    moreover from \<open>lc q \<noteq> 0\<close> have "1 / (lc q) \<noteq> 0" by simp
    ultimately have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (monom_mult (1 / lc q) 0 ?p)" by (rule is_sig_red_monom_mult)
    hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" by (simp add: monom_mult_assoc \<open>lc q \<noteq> 0\<close>)
    with assms(5) show False ..
  qed
  moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?q"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?q"
    moreover from \<open>lc p \<noteq> 0\<close> have "1 / (lc p) \<noteq> 0" by simp
    ultimately have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (monom_mult (1 / lc p) 0 ?q)" by (rule is_sig_red_monom_mult)
    hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q" by (simp add: monom_mult_assoc \<open>lc p \<noteq> 0\<close>)
    with assms(6) show False ..
  qed
  ultimately have "rep_list ?p = rep_list ?q" by (rule sig_regular_reduced_unique)
  thus ?thesis by (simp only: rep_list_monom_mult)
qed

lemma sig_regular_top_reduced_lt_lc_unique:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
    and "lt p = lt q" and "(p = 0) \<longleftrightarrow> (q = 0)" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
proof (cases "p = 0")
  case True
  with assms(6) have "q = 0" by simp
  thus ?thesis by (simp add: True)
next
  case False
  with assms(6) have "q \<noteq> 0" by simp
  from False have "lc p \<noteq> 0" by (rule lc_not_0)
  from \<open>q \<noteq> 0\<close> have "lc q \<noteq> 0" by (rule lc_not_0)
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  with assms(1) obtain p' where p'_red: "(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* p p'" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G p'"
    by (rule sig_irredE_dgrad_max_set)
  from this(1) have lt_p': "lt p' = lt p" and lt_p'': "punit.lt (rep_list p') = punit.lt (rep_list p)"
    and lc_p': "lc p' = lc p" and lc_p'': "punit.lc (rep_list p') = punit.lc (rep_list p)"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_tail_rtrancl_lt_rep_list,
        rule sig_red_regular_rtrancl_lc, rule sig_red_tail_rtrancl_lc_rep_list)
  have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p'"
  proof
    assume a: "is_sig_red (\<prec>\<^sub>t) (=) G p'"
    hence "rep_list p' \<noteq> 0" using is_sig_red_top_addsE by blast
    hence "rep_list p \<noteq> 0" using \<open>(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* p p'\<close>
      by (auto simp: punit.rtrancl_0 dest!: sig_red_red_rtrancl)
    with a have "is_sig_red (\<prec>\<^sub>t) (=) G p" using lt_p' lt_p'' by (rule is_sig_red_top_cong)
    with assms(7) show False ..
  qed
  with \<open>\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G p'\<close> have 1: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p'" by (simp add: is_sig_red_top_tail_cases)
  from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain q' where q'_red: "(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* q q'"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G q'" by (rule sig_irredE_dgrad_max_set)
  from this(1) have lt_q': "lt q' = lt q" and lt_q'': "punit.lt (rep_list q') = punit.lt (rep_list q)"
    and lc_q': "lc q' = lc q" and lc_q'': "punit.lc (rep_list q') = punit.lc (rep_list q)"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_tail_rtrancl_lt_rep_list,
        rule sig_red_regular_rtrancl_lc, rule sig_red_tail_rtrancl_lc_rep_list)
  have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q'"
  proof
    assume a: "is_sig_red (\<prec>\<^sub>t) (=) G q'"
    hence "rep_list q' \<noteq> 0" using is_sig_red_top_addsE by blast
    hence "rep_list q \<noteq> 0" using \<open>(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* q q'\<close>
      by (auto simp: punit.rtrancl_0 dest!: sig_red_red_rtrancl)
    with a have "is_sig_red (\<prec>\<^sub>t) (=) G q" using lt_q' lt_q'' by (rule is_sig_red_top_cong)
    with assms(8) show False ..
  qed
  with \<open>\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G q'\<close> have 2: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q'" by (simp add: is_sig_red_top_tail_cases)
  from assms(2) have "is_sig_GB_upt d G (lt q')" by (simp only: lt_q')
  moreover from assms(1) G_sub assms(3) p'_red have "p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover from assms(1) G_sub assms(4) q'_red have "q' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover have "lt p' = lt q'" by (simp only: lt_p' lt_q' assms(5))
  ultimately have eq: "punit.monom_mult (lc q') 0 (rep_list p') = punit.monom_mult (lc p') 0 (rep_list q')"
    using 1 2 by (rule sig_regular_reduced_unique')

  have "lc q * punit.lc (rep_list p) = lc q * punit.lc (rep_list p')" by (simp only: lc_p'')
  also from \<open>lc q \<noteq> 0\<close> have "... = punit.lc (punit.monom_mult (lc q') 0 (rep_list p'))"
    by (simp add: lc_q')
  also have "... = punit.lc (punit.monom_mult (lc p') 0 (rep_list q'))" by (simp only: eq)
  also from \<open>lc p \<noteq> 0\<close> have "... = lc p * punit.lc (rep_list q')" by (simp add: lc_p')
  also have "... = lc p * punit.lc (rep_list q)" by (simp only: lc_q'')
  finally have *: "lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)" .

  have "punit.lt (rep_list p) = punit.lt (rep_list p')" by (simp only: lt_p'')
  also from \<open>lc q \<noteq> 0\<close> have "... = punit.lt (punit.monom_mult (lc q') 0 (rep_list p'))"
    by (simp add: lc_q' punit.lt_monom_mult_zero)
  also have "... = punit.lt (punit.monom_mult (lc p') 0 (rep_list q'))" by (simp only: eq)
  also from \<open>lc p \<noteq> 0\<close> have "... = punit.lt (rep_list q')" by (simp add: lc_p' punit.lt_monom_mult_zero)
  also have "... = punit.lt (rep_list q)" by (fact lt_q'')
  finally show ?thesis using * ..
qed

corollary sig_regular_top_reduced_lt_unique:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d"
    and "q \<in> dgrad_sig_set d" and "lt p = lt q" and "p \<noteq> 0" and "q \<noteq> 0"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lt (rep_list p) = punit.lt (rep_list q)"
proof -
  from assms(6, 7) have "(p = 0) \<longleftrightarrow> (q = 0)" by simp
  with assms(1, 2, 3, 4, 5)
  have "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
    using assms(8, 9) by (rule sig_regular_top_reduced_lt_lc_unique)
  thus ?thesis ..
qed

corollary sig_regular_top_reduced_lc_unique:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
    and "lt p = lt q" and "lc p = lc q" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lc (rep_list p) = punit.lc (rep_list q)"
proof (cases "p = 0")
  case True
  with assms(6) have "q = 0" by (simp add: lc_eq_zero_iff)
  with True show ?thesis by simp
next
  case False
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence "lc q \<noteq> 0" by (simp add: assms(6))
  hence "q \<noteq> 0" by (simp add: lc_eq_zero_iff)
  with False have "(p = 0) \<longleftrightarrow> (q = 0)" by simp
  with assms(1, 2, 3, 4, 5)
  have "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
    using assms(7, 8) by (rule sig_regular_top_reduced_lt_lc_unique)
  hence "lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)" ..
  also have "... = lc q * punit.lc (rep_list q)" by (simp only: assms(6))
  finally show ?thesis using \<open>lc q \<noteq> 0\<close> by simp
qed

text \<open>Minimal signature Gr\"obner bases are indeed minimal, at least up to sig-lead-pairs:\<close>

lemma is_min_sig_GB_minimal:
  assumes "is_min_sig_GB d G" and "G' \<subseteq> dgrad_sig_set d"
    and "\<And>u. d (pp_of_term u) \<le> dgrad_max d \<Longrightarrow> component_of_term u < length fs \<Longrightarrow> is_sig_GB_in d G' u"
    and "g \<in> G" and "rep_list g \<noteq> 0"
  obtains g' where "g' \<in> G'" and "rep_list g' \<noteq> 0" and "lt g' = lt g"
    and "punit.lt (rep_list g') = punit.lt (rep_list g)"
proof -
  from assms(1) have "G \<subseteq> dgrad_sig_set d"
    and 1: "\<And>u. d (pp_of_term u) \<le> dgrad_max d \<Longrightarrow> component_of_term u < length fs \<Longrightarrow> is_sig_GB_in d G u"
    and 2: "\<And>g0. g0 \<in> G \<Longrightarrow> \<not> is_sig_red (\<preceq>\<^sub>t) (=) (G - {g0}) g0"
    by (simp_all add: is_min_sig_GB_def)
  from assms(4) have 3: "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (G - {g}) g" by (rule 2)

  from assms(5) have "g \<noteq> 0" by (auto simp: rep_list_zero)
  from assms(4) \<open>G \<subseteq> dgrad_sig_set d\<close> have "g \<in> dgrad_sig_set d" ..
  hence "d (lp g) \<le> dgrad_max d" and "component_of_term (lt g) < length fs"
    by (rule dgrad_sig_setD_lp, rule dgrad_sig_setD_lt[OF _ \<open>g \<noteq> 0\<close>])
  hence "is_sig_GB_in d G' (lt g)" by (rule assms(3))
  hence "sig_red_zero (\<preceq>\<^sub>t) G' g" using \<open>g \<in> dgrad_sig_set d\<close> refl by (rule is_sig_GB_inD)
  moreover note assms(5)
  moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
  ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G' g" by (rule sig_red_zero_nonzero)
  then obtain g' where "g' \<in> G'" and "rep_list g' \<noteq> 0"
    and adds1: "punit.lt (rep_list g') adds punit.lt (rep_list g)"
    and le1: "punit.lt (rep_list g) \<oplus> lt g' \<preceq>\<^sub>t punit.lt (rep_list g') \<oplus> lt g"
    by (rule is_sig_red_top_addsE)

  from \<open>rep_list g' \<noteq> 0\<close> have "g' \<noteq> 0" by (auto simp: rep_list_zero)
  from \<open>g' \<in> G'\<close> assms(2) have "g' \<in> dgrad_sig_set d" ..
  hence "d (lp g') \<le> dgrad_max d" and "component_of_term (lt g') < length fs"
    by (rule dgrad_sig_setD_lp, rule dgrad_sig_setD_lt[OF _ \<open>g' \<noteq> 0\<close>])
  hence "is_sig_GB_in d G (lt g')" by (rule 1)
  hence "sig_red_zero (\<preceq>\<^sub>t) G g'" using \<open>g' \<in> dgrad_sig_set d\<close> refl by (rule is_sig_GB_inD)
  moreover note \<open>rep_list g' \<noteq> 0\<close>
  moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
  ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G g'" by (rule sig_red_zero_nonzero)
  then obtain g0 where "g0 \<in> G" and "rep_list g0 \<noteq> 0"
    and adds2: "punit.lt (rep_list g0) adds punit.lt (rep_list g')"
    and le2: "punit.lt (rep_list g') \<oplus> lt g0 \<preceq>\<^sub>t punit.lt (rep_list g0) \<oplus> lt g'"
    by (rule is_sig_red_top_addsE)

  have eq1: "g0 = g"
  proof (rule ccontr)
    assume "g0 \<noteq> g"
    with \<open>g0 \<in> G\<close> have "g0 \<in> G - {g}" by simp
    moreover note \<open>rep_list g0 \<noteq> 0\<close> assms(5)
    moreover from adds2 adds1 have "punit.lt (rep_list g0) adds punit.lt (rep_list g)"
      by (rule adds_trans)
    moreover have "ord_term_lin.is_le_rel (\<preceq>\<^sub>t)" by simp
    moreover have "punit.lt (rep_list g) \<oplus> lt g0 \<preceq>\<^sub>t punit.lt (rep_list g0) \<oplus> lt g"
    proof (rule ord_term_canc)
      have "punit.lt (rep_list g') \<oplus> (punit.lt (rep_list g) \<oplus> lt g0) =
            punit.lt (rep_list g) \<oplus> (punit.lt (rep_list g') \<oplus> lt g0)" by (fact splus_left_commute)
      also from le2 have "... \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> (punit.lt (rep_list g0) \<oplus> lt g')"
        by (rule splus_mono)
      also have "... = punit.lt (rep_list g0) \<oplus> (punit.lt (rep_list g) \<oplus> lt g')"
        by (fact splus_left_commute)
      also from le1 have "... \<preceq>\<^sub>t punit.lt (rep_list g0) \<oplus> (punit.lt (rep_list g') \<oplus> lt g)"
        by (rule splus_mono)
      also have "... = punit.lt (rep_list g') \<oplus> (punit.lt (rep_list g0) \<oplus> lt g)"
        by (fact splus_left_commute)
      finally show "punit.lt (rep_list g') \<oplus> (punit.lt (rep_list g) \<oplus> lt g0) \<preceq>\<^sub>t
                    punit.lt (rep_list g') \<oplus> (punit.lt (rep_list g0) \<oplus> lt g)" .
    qed
    ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) (G - {g}) g" by (rule is_sig_red_top_addsI)
    with 3 show False ..
  qed

  from adds2 adds1 have eq2: "punit.lt (rep_list g') = punit.lt (rep_list g)" by (simp add: eq1 adds_antisym)
  with le1 le2 have "punit.lt (rep_list g) \<oplus> lt g' = punit.lt (rep_list g) \<oplus> lt g" by (simp add: eq1)
  hence "lt g' = lt g" by (simp only: splus_left_canc)
  with \<open>g' \<in> G'\<close> \<open>rep_list g' \<noteq> 0\<close> show ?thesis using eq2 ..
qed

lemma sig_red_zero_regularI_adds:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)"
    and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d" and "p \<noteq> 0" and "sig_red_zero (\<prec>\<^sub>t) G p"
    and "lt p adds\<^sub>t lt q"
  shows "sig_red_zero (\<prec>\<^sub>t) G q"
proof (cases "q = 0")
  case True
  hence "rep_list q = 0" by (simp only: rep_list_zero)
  with rtrancl_refl[to_pred] show ?thesis by (rule sig_red_zeroI)
next
  case False
  hence "lc q \<noteq> 0" by (rule lc_not_0)
  moreover from assms(5) have "lc p \<noteq> 0" by (rule lc_not_0)
  ultimately have "lc q / lc p \<noteq> 0" by simp
  from assms(7) have eq1: "(lp q - lp p) \<oplus> lt p = lt q"
    by (metis add_diff_cancel_right' adds_termE pp_of_term_splus)
  from assms(7) have "lp p adds lp q" by (simp add: adds_term_def)
  with assms(1) have "d (lp q - lp p) \<le> d (lp q)" by (rule dickson_grading_minus)
  also from assms(4) have "... \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
  finally have "d (lp q - lp p) \<le> dgrad_max d" .
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)

  let ?mult = "\<lambda>r. monom_mult (lc q / lc p) (lp q - lp p) r"
  from assms(6) obtain p' where p_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p p'" and "rep_list p' = 0"
    by (rule sig_red_zeroE)
  from p_red have "lt p' = lt p" and "lc p' = lc p"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  hence "p' \<noteq> 0" using \<open>lc p \<noteq> 0\<close> by auto
  with \<open>lc q / lc p \<noteq> 0\<close> have "?mult p' \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  from \<open>lc q / lc p \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "lt (?mult p') = lt q"
    by (simp add: lt_monom_mult \<open>lt p' = lt p\<close> eq1)
  from \<open>lc p \<noteq> 0\<close> have "lc (?mult p') = lc q" by (simp add: \<open>lc p' = lc p\<close>)
  from p_red have mult_p_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (?mult p) (?mult p')"
    by (rule sig_red_rtrancl_monom_mult)
  have "rep_list (?mult p') = 0" by (simp add: rep_list_monom_mult \<open>rep_list p' = 0\<close>)
  hence mult_p'_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (?mult p')"
    using is_sig_red_addsE by fastforce
  from assms(1) G_sub assms(3) p_red have "p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  with assms(1) \<open>d (lp q - lp p) \<le> dgrad_max d\<close> have "?mult p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_monom_mult)

  from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain q' where q_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* q q'"
    and q'_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q'" by (rule sig_irredE_dgrad_max_set)
  from q_red have "lt q' = lt q" and "lc q' = lc q"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  hence "q' \<noteq> 0" using \<open>lc q \<noteq> 0\<close> by auto

  from assms(2) have "is_sig_GB_upt d G (lt (?mult p'))" by (simp only: \<open>lt (?mult p') = lt q\<close>)
  moreover from assms(1) G_sub assms(4) q_red have "q' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover note \<open>?mult p' \<in> dgrad_sig_set d\<close>
  moreover have "lt q' = lt (?mult p')" by (simp only: \<open>lt (?mult p') = lt q\<close> \<open>lt q' = lt q\<close>)
  moreover have "lc q' = lc (?mult p')" by (simp only: \<open>lc (?mult p') = lc q\<close> \<open>lc q' = lc q\<close>)
  ultimately have "rep_list q' = rep_list (?mult p')" using q'_irred mult_p'_irred
    by (rule sig_regular_reduced_unique)
  with \<open>rep_list (?mult p') = 0\<close> have "rep_list q' = 0" by simp
  with q_red show ?thesis by (rule sig_red_zeroI)
qed

lemma is_syz_sigI:
  assumes "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d" and "rep_list s = 0"
  shows "is_syz_sig d u"
  unfolding is_syz_sig_def using assms by blast

lemma is_syz_sigE:
  assumes "is_syz_sig d u"
  obtains r where "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d" and "rep_list r = 0"
  using assms unfolding is_syz_sig_def by blast

lemma is_syz_sig_adds:
  assumes "dickson_grading d" and "is_syz_sig d u" and "u adds\<^sub>t v"
    and "d (pp_of_term v) \<le> dgrad_max d"
  shows "is_syz_sig d v"
proof -
  from assms(2) obtain s where "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d"
    and "rep_list s = 0" by (rule is_syz_sigE)
  from assms(3) obtain t where v: "v = t \<oplus> u" by (rule adds_termE)
  show ?thesis
  proof (rule is_syz_sigI)
    from \<open>s \<noteq> 0\<close> show "monom_mult 1 t s \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  next
    from \<open>s \<noteq> 0\<close> show "lt (monom_mult 1 t s) = v" by (simp add: lt_monom_mult v \<open>lt s = u\<close>)
  next
    from assms(4) have "d (t + pp_of_term u) \<le> dgrad_max d" by (simp add: v term_simps)
    with assms(1) have "d t \<le> dgrad_max d" by (simp add: dickson_gradingD1)
    with assms(1) show "monom_mult 1 t s \<in> dgrad_sig_set d" using \<open>s \<in> dgrad_sig_set d\<close>
      by (rule dgrad_sig_set_closed_monom_mult)
  next
    show "rep_list (monom_mult 1 t s) = 0" by (simp add: \<open>rep_list s = 0\<close> rep_list_monom_mult)
  qed
qed

lemma syzygy_crit:
  assumes "dickson_grading d" and "is_sig_GB_upt d G u" and "is_syz_sig d u"
    and "p \<in> dgrad_sig_set d" and "lt p = u"
  shows "sig_red_zero (\<prec>\<^sub>t) G p"
proof -
  from assms(3) obtain s where "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d"
    and "rep_list s = 0" by (rule is_syz_sigE)
  note assms(1)
  moreover from assms(2) have "is_sig_GB_upt d G (lt p)" by (simp only: assms(5))
  moreover note \<open>s \<in> dgrad_sig_set d\<close> assms(4) \<open>s \<noteq> 0\<close>
  moreover from rtranclp.rtrancl_refl \<open>rep_list s = 0\<close> have "sig_red_zero (\<prec>\<^sub>t) G s"
    by (rule sig_red_zeroI)
  moreover have "lt s adds\<^sub>t lt p" by (simp only: assms(5) \<open>lt s = u\<close> adds_term_refl)
  ultimately show ?thesis by (rule sig_red_zero_regularI_adds)
qed

lemma lemma_21:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt p)" and "p \<in> dgrad_sig_set d" and "g \<in> G"
    and "rep_list p \<noteq> 0" and "rep_list g \<noteq> 0" and "lt g adds\<^sub>t lt p"
    and "punit.lt (rep_list g) adds punit.lt (rep_list p)"
  shows "is_sig_red (\<preceq>\<^sub>t) (=) G p"
proof -
  let ?lp = "punit.lt (rep_list p)"
  define s where "s = ?lp - punit.lt (rep_list g)"
  from assms(8) have s: "?lp = s + punit.lt (rep_list g)" by (simp add: s_def minus_plus)
  from assms(7) obtain t where lt_p: "lt p = t \<oplus> lt g" by (rule adds_termE)
  show ?thesis
  proof (cases "s \<oplus> lt g \<preceq>\<^sub>t lt p")
    case True
    hence "?lp \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt p"
      by (simp add: s splus_assoc splus_left_commute[of s] splus_mono)
    with assms(4, 6, 5, 8) ord_term_lin.is_le_relI(2) show ?thesis
      by (rule is_sig_red_top_addsI)
  next
    case False
    hence "lt p \<prec>\<^sub>t s \<oplus> lt g" by simp
    hence "t \<prec> s" by (simp add: lt_p ord_term_strict_canc_left)
    hence "t + punit.lt (rep_list g) \<prec> s + punit.lt (rep_list g)" by (rule plus_monotone_strict)
    hence "t + punit.lt (rep_list g) \<prec> ?lp" by (simp only: s)
    from assms(5) have "p \<noteq> 0" by (auto simp: rep_list_zero)
    hence "lc p \<noteq> 0" by (rule lc_not_0)
    from assms(6) have "g \<noteq> 0" by (auto simp: rep_list_zero)
    hence "lc g \<noteq> 0" by (rule lc_not_0)
    with \<open>lc p \<noteq> 0\<close> have 1: "lc p / lc g \<noteq> 0" by simp

    let ?g = "monom_mult (lc p / lc g) t g"
    from 1 \<open>g \<noteq> 0\<close> have "lt ?g = lt p" unfolding lt_p by (rule lt_monom_mult)
    from \<open>lc g \<noteq> 0\<close> have "lc ?g = lc p" by simp
    have "punit.lt (rep_list ?g) = t + punit.lt (rep_list g)"
      unfolding rep_list_monom_mult using 1 assms(6) by (rule punit.lt_monom_mult[simplified])
    also have "... \<prec> ?lp" by fact
    finally have "punit.lt (rep_list ?g) \<prec> ?lp" .
    hence lt_pg: "punit.lt (rep_list (p - ?g)) = ?lp" and "rep_list p \<noteq> rep_list ?g"
      by (auto simp: rep_list_minus punit.lt_minus_eqI_2)
    from this(2) have "rep_list (p - ?g) \<noteq> 0" and "p - ?g \<noteq> 0"
      by (auto simp: rep_list_minus rep_list_zero)

    from assms(2) have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
    note assms(1)
    moreover have "d t \<le> dgrad_max d"
    proof (rule le_trans)
      have "lp p = t + lp g" by (simp add: lt_p term_simps)
      with assms(1) show "d t \<le> d (lp p)" by (simp add: dickson_grading_adds_imp_le)
    next
      from assms(3) show "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
    qed
    moreover from assms(4) \<open>G \<subseteq> dgrad_sig_set d\<close> have "g \<in> dgrad_sig_set d" ..
    ultimately have "?g \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult)

    note assms(2)
    moreover from assms(3) \<open>?g \<in> dgrad_sig_set d\<close> have "p - ?g \<in> dgrad_sig_set d"
      by (rule dgrad_sig_set_closed_minus)
    moreover from \<open>p - ?g \<noteq> 0\<close> \<open>lt ?g = lt p\<close> \<open>lc ?g = lc p\<close> have "lt (p - ?g) \<prec>\<^sub>t lt p"
      by (rule lt_minus_lessI)
    ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (p - ?g)"
      by (rule is_sig_GB_uptD3)
    moreover note \<open>rep_list (p - ?g) \<noteq> 0\<close>
    moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
    ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G (p - ?g)" by (rule sig_red_zero_nonzero)
    then obtain g1 where "g1 \<in> G" and "rep_list g1 \<noteq> 0"
      and 2: "punit.lt (rep_list g1) adds punit.lt (rep_list (p - ?g))"
      and 3: "punit.lt (rep_list (p - ?g)) \<oplus> lt g1 \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt (p - ?g)"
      by (rule is_sig_red_top_addsE)
    from \<open>g1 \<in> G\<close> \<open>rep_list g1 \<noteq> 0\<close> assms(5) show ?thesis
    proof (rule is_sig_red_top_addsI)
      from 2 show "punit.lt (rep_list g1) adds punit.lt (rep_list p)" by (simp only: lt_pg)
    next
      have "?lp \<oplus> lt g1 = punit.lt (rep_list (p - ?g)) \<oplus> lt g1" by (simp only: lt_pg)
      also have "... \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt (p - ?g)" by (fact 3)
      also from \<open>lt (p - ?g) \<prec>\<^sub>t lt p\<close> have "... \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p"
        by (rule splus_mono_strict)
      finally show "?lp \<oplus> lt g1 \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p" by (rule ord_term_lin.less_imp_le)
    qed simp
  qed
qed

subsubsection \<open>Rewrite Bases\<close>

definition is_rewrite_ord :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_rewrite_ord rword \<longleftrightarrow> (reflp rword \<and> transp rword \<and> (\<forall>a b. rword a b \<or> rword b a) \<and>
                                  (\<forall>a b. rword a b \<longrightarrow> rword b a \<longrightarrow> fst a = fst b) \<and>
                                  (\<forall>d G a b. dickson_grading d \<longrightarrow> is_sig_GB_upt d G (lt b) \<longrightarrow>
                                          a \<in> G \<longrightarrow> b \<in> G \<longrightarrow> a \<noteq> 0 \<longrightarrow> b \<noteq> 0 \<longrightarrow> lt a adds\<^sub>t lt b \<longrightarrow>
                                          \<not> is_sig_red (\<prec>\<^sub>t) (=) G b \<longrightarrow> rword (spp_of a) (spp_of b)))"

definition is_canon_rewriter :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_canon_rewriter rword A u p \<longleftrightarrow>
                  (p \<in> A \<and> p \<noteq> 0 \<and> lt p adds\<^sub>t u \<and> (\<forall>a\<in>A. a \<noteq> 0 \<longrightarrow> lt a adds\<^sub>t u \<longrightarrow> rword (spp_of a) (spp_of p)))"

definition is_RB_in :: "('a \<Rightarrow> nat) \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_RB_in d rword G u \<longleftrightarrow>
            ((\<exists>g. is_canon_rewriter rword G u g \<and> \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)) \<or>
             is_syz_sig d u)"

definition is_RB_upt :: "('a \<Rightarrow> nat) \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_RB_upt d rword G u \<longleftrightarrow>
            (G \<subseteq> dgrad_sig_set d \<and> (\<forall>v. v \<prec>\<^sub>t u \<longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<longrightarrow>
                                      component_of_term v < length fs \<longrightarrow> is_RB_in d rword G v))"

lemma is_rewrite_ordI:
  assumes "reflp rword" and "transp rword" and "\<And>a b. rword a b \<or> rword b a"
    and "\<And>a b. rword a b \<Longrightarrow> rword b a \<Longrightarrow> fst a = fst b"
    and "\<And>d G a b. dickson_grading d \<Longrightarrow> is_sig_GB_upt d G (lt b) \<Longrightarrow> a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow>
                   a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t lt b \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (=) G b \<Longrightarrow> rword (spp_of a) (spp_of b)"
  shows "is_rewrite_ord rword"
  unfolding is_rewrite_ord_def using assms by blast

lemma is_rewrite_ordD1: "is_rewrite_ord rword \<Longrightarrow> rword a a"
  by (simp add: is_rewrite_ord_def reflpD)

lemma is_rewrite_ordD2: "is_rewrite_ord rword \<Longrightarrow> rword a b \<Longrightarrow> rword b c \<Longrightarrow> rword a c"
  by (auto simp: is_rewrite_ord_def dest: transpD)

lemma is_rewrite_ordD3:
  assumes "is_rewrite_ord rword"
    and "rword a b \<Longrightarrow> thesis"
    and "\<not> rword a b \<Longrightarrow> rword b a \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have disj: "rword a b \<or> rword b a"
    by (simp add: is_rewrite_ord_def del: split_paired_All)
  show ?thesis
  proof (cases "rword a b")
    case True
    thus ?thesis by (rule assms(2))
  next
    case False
    moreover from this disj have "rword b a" by simp
    ultimately show ?thesis by (rule assms(3))
  qed
qed

lemma is_rewrite_ordD4:
  assumes "is_rewrite_ord rword" and "rword a b" and "rword b a"
  shows "fst a = fst b"
  using assms unfolding is_rewrite_ord_def by blast

lemma is_rewrite_ordD4':
  assumes "is_rewrite_ord rword" and "rword (spp_of a) (spp_of b)" and "rword (spp_of b) (spp_of a)"
  shows "lt a = lt b"
proof -
  from assms have "fst (spp_of a) = fst (spp_of b)" by (rule is_rewrite_ordD4)
  thus ?thesis by (simp add: spp_of_def)
qed

lemma is_rewrite_ordD5:
  assumes "is_rewrite_ord rword" and "dickson_grading d" and "is_sig_GB_upt d G (lt b)"
    and "a \<in> G" and "b \<in> G" and "a \<noteq> 0" and "b \<noteq> 0" and "lt a adds\<^sub>t lt b"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G b"
  shows "rword (spp_of a) (spp_of b)"
  using assms unfolding is_rewrite_ord_def by blast

lemma is_canon_rewriterI:
  assumes "p \<in> A" and "p \<noteq> 0" and "lt p adds\<^sub>t u"
    and "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
  shows "is_canon_rewriter rword A u p"
  unfolding is_canon_rewriter_def using assms by blast

lemma is_canon_rewriterD1: "is_canon_rewriter rword A u p \<Longrightarrow> p \<in> A"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD2: "is_canon_rewriter rword A u p \<Longrightarrow> p \<noteq> 0"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD3: "is_canon_rewriter rword A u p \<Longrightarrow> lt p adds\<^sub>t u"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD4:
  "is_canon_rewriter rword A u p \<Longrightarrow> a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
  by (simp add: is_canon_rewriter_def)

lemmas is_canon_rewriterD = is_canon_rewriterD1 is_canon_rewriterD2 is_canon_rewriterD3 is_canon_rewriterD4

lemma is_rewrite_ord_finite_canon_rewriterE:
  assumes "is_rewrite_ord rword" and "finite A" and "a \<in> A" and "a \<noteq> 0" and "lt a adds\<^sub>t u"
  obtains p where "is_canon_rewriter rword A u p"
proof -
  let ?A = "{x. x \<in> A \<and> x \<noteq> 0 \<and> lt x adds\<^sub>t u}"
  let ?rel = "\<lambda>x y. strict rword (spp_of y) (spp_of x)"
  have "finite ?A"
  proof (rule finite_subset)
    show "?A \<subseteq> A" by blast
  qed fact
  moreover have "?A \<noteq> {}"
  proof
    from assms(3, 4, 5) have "a \<in> ?A" by simp
    also assume "?A = {}"
    finally show False by simp
  qed
  moreover have "irreflp ?rel"
  proof -
    from assms(1) have "reflp rword" by (simp add: is_rewrite_ord_def)
    thus ?thesis by (simp add: reflp_def irreflp_def)
  qed
  moreover have "transp ?rel"
  proof -
    from assms(1) have "transp rword" by (simp add: is_rewrite_ord_def)
    thus ?thesis by (auto simp: transp_def simp del: split_paired_All)
  qed
  ultimately obtain p where "p \<in> ?A" and *: "\<And>b. ?rel b p \<Longrightarrow> b \<notin> ?A" by (rule finite_minimalE, blast)
  from this(1) have "p \<in> A" and "p \<noteq> 0" and "lt p adds\<^sub>t u" by simp_all
  show ?thesis
  proof (rule, rule is_canon_rewriterI)
    fix q
    assume "q \<in> A" and "q \<noteq> 0" and "lt q adds\<^sub>t u"
    hence "q \<in> ?A" by simp
    with * have "\<not> ?rel q p" by blast
    hence disj: "\<not> rword (spp_of p) (spp_of q) \<or> rword (spp_of q) (spp_of p)" by simp
    from assms(1) show "rword (spp_of q) (spp_of p)"
    proof (rule is_rewrite_ordD3)
      assume "\<not> rword (spp_of q) (spp_of p)" and "rword (spp_of p) (spp_of q)"
      with disj show ?thesis by simp
    qed
  qed fact+
qed

lemma is_rewrite_ord_canon_rewriterD1:
  assumes "is_rewrite_ord rword" and "is_canon_rewriter rword A u p" and "is_canon_rewriter rword A v q"
    and "lt p adds\<^sub>t v" and "lt q adds\<^sub>t u"
  shows "lt p = lt q"
proof -
  from assms(2) have "p \<in> A" and "p \<noteq> 0"
    and 1: "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
    by (rule is_canon_rewriterD)+
  from assms(3) have "q \<in> A" and "q \<noteq> 0"
    and 2: "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t v \<Longrightarrow> rword (spp_of a) (spp_of q)"
    by (rule is_canon_rewriterD)+
  note assms(1)
  moreover from \<open>p \<in> A\<close> \<open>p \<noteq> 0\<close> assms(4) have "rword (spp_of p) (spp_of q)" by (rule 2)
  moreover from \<open>q \<in> A\<close> \<open>q \<noteq> 0\<close> assms(5) have "rword (spp_of q) (spp_of p)" by (rule 1)
  ultimately show ?thesis by (rule is_rewrite_ordD4')
qed

corollary is_rewrite_ord_canon_rewriterD2:
  assumes "is_rewrite_ord rword" and "is_canon_rewriter rword A u p" and "is_canon_rewriter rword A u q"
  shows "lt p = lt q"
  using assms
proof (rule is_rewrite_ord_canon_rewriterD1)
  from assms(2) show "lt p adds\<^sub>t u" by (rule is_canon_rewriterD)
next
  from assms(3) show "lt q adds\<^sub>t u" by (rule is_canon_rewriterD)
qed

lemma is_rewrite_ord_canon_rewriterD3:
  assumes "is_rewrite_ord rword" and "dickson_grading d" and "is_canon_rewriter rword A u p"
    and "a \<in> A" and "a \<noteq> 0" and "lt a adds\<^sub>t u" and "is_sig_GB_upt d A (lt a)"
    and "lt p adds\<^sub>t lt a" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) A a"
  shows "lt p = lt a"
proof -
  note assms(1)
  moreover from assms(1, 2, 7) _ assms(4) _ assms(5, 8, 9) have "rword (spp_of p) (spp_of a)"
  proof (rule is_rewrite_ordD5)
    from assms(3) show "p \<in> A" and "p \<noteq> 0" by (rule is_canon_rewriterD)+
  qed
  moreover from assms(3, 4, 5, 6) have "rword (spp_of a) (spp_of p)" by (rule is_canon_rewriterD4)
  ultimately show ?thesis by (rule is_rewrite_ordD4')
qed

lemma is_RB_inI1:
  assumes "is_canon_rewriter rword G u g" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)"
  shows "is_RB_in d rword G u"
  unfolding is_RB_in_def using assms is_canon_rewriterD1 by blast

lemma is_RB_inI2:
  assumes "is_syz_sig d u"
  shows "is_RB_in d rword G u"
  unfolding is_RB_in_def Let_def using assms by blast

lemma is_RB_inE:
  assumes "is_RB_in d rword G u"
    and "is_syz_sig d u \<Longrightarrow> thesis"
    and "\<And>g. \<not> is_syz_sig d u \<Longrightarrow> is_canon_rewriter rword G u g \<Longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g) \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding is_RB_in_def by blast

lemma is_RB_inD:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_sig_set d" and "is_RB_in d rword G u"
    and "\<not> is_syz_sig d u" and "d (pp_of_term u) \<le> dgrad_max d"
    and "is_canon_rewriter rword G u g"
  shows "rep_list g \<noteq> 0"
proof
  assume a: "rep_list g = 0"
  from assms(1) have "is_syz_sig d u"
  proof (rule is_syz_sig_adds)
    show "is_syz_sig d (lt g)"
    proof (rule is_syz_sigI)
      from assms(6) show "g \<noteq> 0" by (rule is_canon_rewriterD2)
    next
      from assms(6) have "g \<in> G" by (rule is_canon_rewriterD1)
      thus "g \<in> dgrad_sig_set d" using assms(2) ..
    qed (fact refl, fact a)
  next
    from assms(6) show "lt g adds\<^sub>t u" by (rule is_canon_rewriterD3)
  qed fact
  with assms(4) show False ..
qed

lemma is_RB_uptI:
  assumes "G \<subseteq> dgrad_sig_set d"
    and "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<Longrightarrow> component_of_term v < length fs \<Longrightarrow>
            is_RB_in d canon G v"
  shows "is_RB_upt d canon G u"
  unfolding is_RB_upt_def using assms by blast

lemma is_RB_uptD1:
  assumes "is_RB_upt d canon G u"
  shows "G \<subseteq> dgrad_sig_set d"
  using assms unfolding is_RB_upt_def by blast

lemma is_RB_uptD2:
  assumes "is_RB_upt d canon G u" and "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d"
    and "component_of_term v < length fs"
  shows "is_RB_in d canon G v"
  using assms unfolding is_RB_upt_def by blast

lemma is_RB_in_UnI:
  assumes "is_RB_in d rword G u" and "\<And>h. h \<in> H \<Longrightarrow> u \<prec>\<^sub>t lt h"
  shows "is_RB_in d rword (H \<union> G) u"
  using assms(1)
proof (rule is_RB_inE)
  assume "is_syz_sig d u"
  thus "is_RB_in d rword (H \<union> G) u" by (rule is_RB_inI2)
next
  fix g'
  assume crw: "is_canon_rewriter rword G u g'"
    and irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g') g')"
  from crw have "g' \<in> G" and "g' \<noteq> 0" and "lt g' adds\<^sub>t u"
    and max: "\<And>a. a \<in> G \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of g')"
    by (rule is_canon_rewriterD)+
  show "is_RB_in d rword (H \<union> G) u"
  proof (rule is_RB_inI1)
    show "is_canon_rewriter rword (H \<union> G) u g'"
    proof (rule is_canon_rewriterI)
      from \<open>g' \<in> G\<close> show "g' \<in> H \<union> G" by simp
    next
      fix a
      assume "a \<in> H \<union> G" and "a \<noteq> 0" and "lt a adds\<^sub>t u"
      from this(1) show "rword (spp_of a) (spp_of g')"
      proof
        assume "a \<in> H"
        with \<open>lt a adds\<^sub>t u\<close> have "lt a adds\<^sub>t u" by simp
        hence "lt a \<preceq>\<^sub>t u" by (rule ord_adds_term)
        moreover from \<open>a \<in> H\<close> have "u \<prec>\<^sub>t lt a" by (rule assms(2))
        ultimately show ?thesis by simp
      next
        assume "a \<in> G"
        thus ?thesis using \<open>a \<noteq> 0\<close> \<open>lt a adds\<^sub>t u\<close> by (rule max)
      qed
    qed fact+
  next
    show "\<not> is_sig_red (\<prec>\<^sub>t) (=) (H \<union> G) (monom_mult 1 (pp_of_term u - lp g') g')"
      (is "\<not> is_sig_red _ _ _ ?g")
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) (H \<union> G) ?g"
      with irred have "is_sig_red (\<prec>\<^sub>t) (=) H ?g" by (simp add: is_sig_red_Un del: Un_insert_left)
      then obtain h where "h \<in> H" and "is_sig_red (\<prec>\<^sub>t) (=) {h} ?g" by (rule is_sig_red_singletonI)
      from this(2) have "lt h \<prec>\<^sub>t lt ?g" by (rule is_sig_red_regularD_lt)
      also from \<open>g' \<noteq> 0\<close> \<open>lt g' adds\<^sub>t u\<close> have "... = u"
        by (auto simp: lt_monom_mult adds_term_alt pp_of_term_splus)
      finally have "lt h \<prec>\<^sub>t u" .
      moreover from \<open>h \<in> H\<close> have "u \<prec>\<^sub>t lt h" by (rule assms(2))
      ultimately show False by simp
    qed
  qed
qed

corollary is_RB_in_insertI:
  assumes "is_RB_in d rword G u" and "u \<prec>\<^sub>t lt g"
  shows "is_RB_in d rword (insert g G) u"
proof -
  from assms(1) have "is_RB_in d rword ({g} \<union> G) u"
  proof (rule is_RB_in_UnI)
    fix h
    assume "h \<in> {g}"
    with assms(2) show "u \<prec>\<^sub>t lt h" by simp
  qed
  thus ?thesis by simp
qed

corollary is_RB_upt_UnI:
  assumes "is_RB_upt d rword G u" and "H \<subseteq> dgrad_sig_set d" and "\<And>h. h \<in> H \<Longrightarrow> u \<preceq>\<^sub>t lt h"
  shows "is_RB_upt d rword (H \<union> G) u"
proof (rule is_RB_uptI)
  from assms(1) have "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  with assms(2) show "H \<union> G \<subseteq> dgrad_sig_set d" by (rule Un_least)
next
  fix v
  assume "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
  with assms(1) have "is_RB_in d rword G v" by (rule is_RB_uptD2)
  moreover from \<open>v \<prec>\<^sub>t u\<close> assms(3) have "\<And>h. h \<in> H \<Longrightarrow> v \<prec>\<^sub>t lt h" by (rule ord_term_lin.less_le_trans)
  ultimately show "is_RB_in d rword (H \<union> G) v" by (rule is_RB_in_UnI)
qed

corollary is_RB_upt_insertI:
  assumes "is_RB_upt d rword G u" and "g \<in> dgrad_sig_set d" and "u \<preceq>\<^sub>t lt g"
  shows "is_RB_upt d rword (insert g G) u"
proof -
  from assms(1) have "is_RB_upt d rword ({g} \<union> G) u"
  proof (rule is_RB_upt_UnI)
    from assms(2) show "{g} \<subseteq> dgrad_sig_set d" by simp
  next
    fix h
    assume "h \<in> {g}"
    with assms(3) show "u \<preceq>\<^sub>t lt h" by simp
  qed
  thus ?thesis by simp
qed

lemma is_RB_upt_is_sig_GB_upt:
  assumes "dickson_grading d" and "is_RB_upt d rword G u"
  shows "is_sig_GB_upt d G u"
proof (rule ccontr)
  let ?Q = "{v. v \<prec>\<^sub>t u \<and> d (pp_of_term v) \<le> dgrad_max d \<and> component_of_term v < length fs \<and> \<not> is_sig_GB_in d G v}"
  have Q_sub: "pp_of_term ` ?Q \<subseteq> dgrad_set d (dgrad_max d)" by blast
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  assume "\<not> is_sig_GB_upt d G u"
  with G_sub obtain v' where "v' \<in> ?Q" unfolding is_sig_GB_upt_def by blast
  with assms(1) obtain v where "v \<in> ?Q" and min: "\<And>y. y \<prec>\<^sub>t v \<Longrightarrow> y \<notin> ?Q" using Q_sub
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>v \<in> ?Q\<close> have "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
    and "\<not> is_sig_GB_in d G v" by simp_all
  from assms(2) this(1, 2, 3) have "is_RB_in d rword G v" by (rule is_RB_uptD2)
  from \<open>\<not> is_sig_GB_in d G v\<close> obtain r where "lt r = v" and "r \<in> dgrad_sig_set d" and "\<not> sig_red_zero (\<preceq>\<^sub>t) G r"
    unfolding is_sig_GB_in_def by blast
  from this(3) have "rep_list r \<noteq> 0" by (auto simp: sig_red_zero_def)
  hence "r \<noteq> 0" by (auto simp: rep_list_zero)
  hence "lc r \<noteq> 0" by (rule lc_not_0)

  from G_sub have "is_sig_GB_upt d G v"
  proof (rule is_sig_GB_uptI)
    fix w
    assume dw: "d (pp_of_term w) \<le> dgrad_max d" and cp: "component_of_term w < length fs"
    assume "w \<prec>\<^sub>t v"
    hence "w \<notin> ?Q" by (rule min)
    hence "\<not> w \<prec>\<^sub>t u \<or> is_sig_GB_in d G w" by (simp add: dw cp)
    thus "is_sig_GB_in d G w"
    proof
      assume "\<not> w \<prec>\<^sub>t u"
      moreover from \<open>w \<prec>\<^sub>t v\<close> \<open>v \<prec>\<^sub>t u\<close> have "w \<prec>\<^sub>t u" by (rule ord_term_lin.less_trans)
      ultimately show ?thesis ..
    qed
  qed

  from \<open>is_RB_in d rword G v\<close> have "sig_red_zero (\<preceq>\<^sub>t) G r"
  proof (rule is_RB_inE)
    assume "is_syz_sig d v"
    have "sig_red_zero (\<prec>\<^sub>t) G r" by (rule syzygy_crit, fact+)
    thus ?thesis by (rule sig_red_zero_sing_regI)
  next
    fix g
    assume a: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
    assume "is_canon_rewriter rword G v g"
    hence "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t v" by (rule is_canon_rewriterD)+
    assume "\<not> is_syz_sig d v"
    from \<open>g \<in> G\<close> G_sub have "g \<in> dgrad_sig_set d" ..
    from \<open>g \<noteq> 0\<close> have "lc g \<noteq> 0" by (rule lc_not_0)
    with \<open>lc r \<noteq> 0\<close> have "lc r / lc g \<noteq> 0" by simp
    from \<open>lt g adds\<^sub>t v\<close> have "lt g adds\<^sub>t lt r" by (simp only: \<open>lt r = v\<close>)
    hence eq1: "(lp r - lp g) \<oplus> lt g = lt r" by (metis add_implies_diff adds_termE pp_of_term_splus)

    let ?h = "monom_mult (lc r / lc g) (lp r - lp g) g"
    from \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> \<open>g \<noteq> 0\<close> have "?h \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
    have h_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G ?h"
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) G ?h"
      moreover from \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> have "lc g / lc r \<noteq> 0" by simp
      ultimately have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult (lc g / lc r) 0 ?h)" by (rule is_sig_red_monom_mult)
      with \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
        by (simp add: monom_mult_assoc \<open>lt r = v\<close>)
      with a show False ..
    qed
    from \<open>lc r / lc g \<noteq> 0\<close> \<open>g \<noteq> 0\<close> have "lt ?h = lt r" by (simp add: lt_monom_mult eq1)
    hence "lt ?h = v" by (simp only: \<open>lt r = v\<close>)
    from \<open>lc g \<noteq> 0\<close> have "lc ?h = lc r" by simp
    from assms(1) _ \<open>g \<in> dgrad_sig_set d\<close> have "?h \<in> dgrad_sig_set d"
    proof (rule dgrad_sig_set_closed_monom_mult)
      from \<open>lt g adds\<^sub>t lt r\<close> have "lp g adds lp r" by (simp add: adds_term_def)
      with assms(1) have "d (lp r - lp g) \<le> d (lp r)" by (rule dickson_grading_minus)
      also from \<open>r \<in> dgrad_sig_set d\<close> have "... \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
      finally show "d (lp r - lp g) \<le> dgrad_max d" .
    qed
    have "rep_list ?h \<noteq> 0"
    proof
      assume "rep_list ?h = 0"
      with \<open>?h \<noteq> 0\<close> \<open>lt ?h = v\<close> \<open>?h \<in> dgrad_sig_set d\<close> have "is_syz_sig d v" by (rule is_syz_sigI)
      with \<open>\<not> is_syz_sig d v\<close> show False ..
    qed
    hence "rep_list g \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    hence "punit.lc (rep_list g) \<noteq> 0" by (rule punit.lc_not_0)
    from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain s where s_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s"
      and s_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G s" by (rule sig_irredE_dgrad_max_set)
    from s_red have s_red': "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" by (rule sig_red_rtrancl_sing_regI)
    have "rep_list s \<noteq> 0"
    proof
      assume "rep_list s = 0"
      with s_red' have "sig_red_zero (\<preceq>\<^sub>t) G r" by (rule sig_red_zeroI)
      with \<open>\<not> sig_red_zero (\<preceq>\<^sub>t) G r\<close> show False ..
    qed
    from assms(1) G_sub \<open>r \<in> dgrad_sig_set d\<close> s_red have "s \<in> dgrad_sig_set d"
      by (rule dgrad_sig_set_closed_sig_red_rtrancl)
    from s_red have "lt s = lt r" and "lc s = lc r"
      by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
    hence "lt ?h = lt s" and "lc ?h = lc s" and "s \<noteq> 0"
      using \<open>lc r \<noteq> 0\<close> by (auto simp: \<open>lt ?h = lt r\<close> \<open>lc ?h = lc r\<close> simp del: lc_monom_mult)
    from s_irred have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G s" by (simp add: is_sig_red_top_tail_cases)
    from \<open>is_sig_GB_upt d G v\<close> have "is_sig_GB_upt d G (lt s)" by (simp only: \<open>lt s = lt r\<close> \<open>lt r = v\<close>)
    have "punit.lt (rep_list ?h) = punit.lt (rep_list s)"
      by (rule sig_regular_top_reduced_lt_unique, fact+)
    hence eq2: "lp r - lp g + punit.lt (rep_list g) = punit.lt (rep_list s)"
      using \<open>lc r / lc g \<noteq> 0\<close> \<open>rep_list g \<noteq> 0\<close> by (simp add: rep_list_monom_mult punit.lt_monom_mult)
    have "punit.lc (rep_list ?h) = punit.lc (rep_list s)"
      by (rule sig_regular_top_reduced_lc_unique, fact+)
    hence eq3: "lc r / lc g = punit.lc (rep_list s) / punit.lc (rep_list g)"
      using \<open>punit.lc (rep_list g) \<noteq> 0\<close> by (simp add: rep_list_monom_mult field_simps)
    have "sig_red_single (=) (=) s (s - ?h) g (lp r - lp g)"
      by (rule sig_red_singleI, auto simp: eq1 eq2 eq3 punit.lc_def[symmetric] \<open>lt s = lt r\<close>
            \<open>rep_list g \<noteq> 0\<close> \<open>rep_list s \<noteq> 0\<close> intro!: punit.lt_in_keys)
    with \<open>g \<in> G\<close> have "sig_red (=) (=) G s (s - ?h)" unfolding sig_red_def by blast
    hence "sig_red (\<preceq>\<^sub>t) (\<preceq>) G s (s - ?h)" by (auto dest: sig_red_sing_regI sig_red_top_tailI)
    with s_red' have r_red: "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r (s - ?h)" ..
    show ?thesis
    proof (cases "s - ?h = 0")
      case True
      hence "rep_list (s - ?h) = 0" by (simp only: rep_list_zero)
      with r_red show ?thesis by (rule sig_red_zeroI)
    next
      case False
      note \<open>is_sig_GB_upt d G (lt s)\<close>
      moreover from \<open>s \<in> dgrad_sig_set d\<close> \<open>?h \<in> dgrad_sig_set d\<close> have "s - ?h \<in> dgrad_sig_set d"
        by (rule dgrad_sig_set_closed_minus)
      moreover from False \<open>lt ?h = lt s\<close> \<open>lc ?h = lc s\<close> have "lt (s - ?h) \<prec>\<^sub>t lt s" by (rule lt_minus_lessI)
      ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (s - ?h)" by (rule is_sig_GB_uptD3)
      then obtain s' where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (s - ?h) s'" and "rep_list s' = 0"
        by (rule sig_red_zeroE)
      from r_red this(1) have "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s'" by simp
      thus ?thesis using \<open>rep_list s' = 0\<close> by (rule sig_red_zeroI)
    qed
  qed
  with \<open>\<not> sig_red_zero (\<preceq>\<^sub>t) G r\<close> show False ..
qed

corollary is_RB_upt_is_syz_sigD:
  assumes "dickson_grading d" and "is_RB_upt d rword G u"
    and "is_syz_sig d u" and "p \<in> dgrad_sig_set d" and "lt p = u"
  shows "sig_red_zero (\<prec>\<^sub>t) G p"
proof -
  note assms(1)
  moreover from assms(1, 2) have "is_sig_GB_upt d G u" by (rule is_RB_upt_is_sig_GB_upt)
  ultimately show ?thesis using assms(3, 4, 5) by (rule syzygy_crit)
qed

subsubsection \<open>S-Pairs\<close>

definition spair :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "spair p q = (let t1 = punit.lt (rep_list p); t2 = punit.lt (rep_list q); l = lcs t1 t2 in
                        (monom_mult (1 / punit.lc (rep_list p)) (l - t1) p) -
                        (monom_mult (1 / punit.lc (rep_list q)) (l - t2) q))"

definition is_regular_spair :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_regular_spair p q \<longleftrightarrow>
                    (rep_list p \<noteq> 0 \<and> rep_list q \<noteq> 0 \<and>
                      (let t1 = punit.lt (rep_list p); t2 = punit.lt (rep_list q); l = lcs t1 t2 in
                        (l - t1) \<oplus> lt p \<noteq> (l - t2) \<oplus> lt q))"

lemma rep_list_spair: "rep_list (spair p q) = punit.spoly (rep_list p) (rep_list q)"
  by (simp add: spair_def punit.spoly_def Let_def rep_list_minus rep_list_monom_mult punit.lc_def)

lemma spair_comm: "spair p q = - spair q p"
  by (simp add: spair_def Let_def lcs_comm)

lemma dgrad_sig_set_closed_spair:
  assumes "dickson_grading d" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
  shows "spair p q \<in> dgrad_sig_set d"
proof -
  define t1 where "t1 = punit.lt (rep_list p)"
  define t2 where "t2 = punit.lt (rep_list q)"
  let ?l = "lcs t1 t2"
  have "d t1 \<le> dgrad_max d"
  proof (cases "rep_list p = 0")
    case True
    show ?thesis by (simp add: t1_def True dgrad_max_0)
  next
    case False
    from assms(2) have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
    with assms(1) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
    thus ?thesis unfolding t1_def using False by (rule punit.dgrad_p_setD_lp[simplified])
  qed
  moreover have "d t2 \<le> dgrad_max d"
  proof (cases "rep_list q = 0")
    case True
    show ?thesis by (simp add: t2_def True dgrad_max_0)
  next
    case False
    from assms(3) have "q \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
    with assms(1) have "rep_list q \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
    thus ?thesis unfolding t2_def using False by (rule punit.dgrad_p_setD_lp[simplified])
  qed
  ultimately have "ord_class.max (d t1) (d t2) \<le> dgrad_max d" by simp
  moreover from assms(1) have "d ?l \<le> ord_class.max (d t1) (d t2)" by (rule dickson_grading_lcs)
  ultimately have *: "d ?l \<le> dgrad_max d" by auto
  thm dickson_grading_minus
  show ?thesis
  proof (simp add: spair_def Let_def t1_def[symmetric] t2_def[symmetric],
      intro dgrad_sig_set_closed_minus dgrad_sig_set_closed_monom_mult[OF assms(1)])
    from assms(1) adds_lcs have "d (?l - t1) \<le> d ?l" by (rule dickson_grading_minus)
    thus "d (?l - t1) \<le> dgrad_max d" using * by (rule le_trans)
  next
    from assms(1) adds_lcs_2 have "d (?l - t2) \<le> d ?l" by (rule dickson_grading_minus)
    thus "d (?l - t2) \<le> dgrad_max d" using * by (rule le_trans)
  qed fact+
qed

lemma lt_spair:
  assumes "rep_list p \<noteq> 0" and "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
  shows "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
proof -
  define l where "l = lcs (punit.lt (rep_list p)) (punit.lt (rep_list q))"
  have 1: "punit.lt (rep_list p) adds l" and 2: "punit.lt (rep_list q) adds l"
    unfolding l_def by (rule adds_lcs, rule adds_lcs_2)
  have eq1: "spair p q = (monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) p) +
                         (monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) q)"
    by (simp add: spair_def Let_def l_def monom_mult_uminus_left)
  from assms(1) have "punit.lc (rep_list p) \<noteq> 0" by (rule punit.lc_not_0)
  hence "1 / punit.lc (rep_list p) \<noteq> 0" by simp
  moreover from assms(1) have "p \<noteq> 0" by (auto simp: rep_list_zero)
  ultimately have eq2: "lt (monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) p) =
                        (l - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_monom_mult)
  have "lt (monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) q) \<preceq>\<^sub>t
                        (l - punit.lt (rep_list q)) \<oplus> lt q"
    by (fact lt_monom_mult_le)
  also from assms(2) have "... \<prec>\<^sub>t (l - punit.lt (rep_list p)) \<oplus> lt p"
    by (simp add: term_is_le_rel_minus_minus[OF _ 2 1])
  finally show ?thesis unfolding eq2[symmetric] eq1 l_def[symmetric] by (rule lt_plus_eqI_2)
qed

lemma lt_spair':
  assumes "rep_list p \<noteq> 0" and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)" and "b \<oplus> lt q \<prec>\<^sub>t a \<oplus> lt p"
  shows "lt (spair p q) = (a - gcs a b) \<oplus> lt p"
proof -
  from assms(3) have "punit.lt (rep_list p) \<oplus> (b \<oplus> lt q) \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> (a \<oplus> lt p)"
    by (fact splus_mono_strict)
  hence "(b + punit.lt (rep_list p)) \<oplus> lt q \<prec>\<^sub>t (b + punit.lt (rep_list q)) \<oplus> lt p"
    by (simp only: splus_assoc[symmetric] add.commute assms(2))
  hence "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
    by (simp only: splus_assoc ord_term_strict_canc)
  with assms(1)
  have "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_spair)
  with assms(2) show ?thesis by (simp add: lcs_minus_1)
qed

lemma lt_rep_list_spair:
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0" and "rep_list (spair p q) \<noteq> 0"
    and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)"
  shows "punit.lt (rep_list (spair p q)) \<prec> (a - gcs a b) + punit.lt (rep_list p)"
proof -
  from assms(1) have 1: "punit.lc (rep_list p) \<noteq> 0" by (rule punit.lc_not_0)
  from assms(2) have 2: "punit.lc (rep_list q) \<noteq> 0" by (rule punit.lc_not_0)
  define l where "l = lcs (punit.lt (rep_list p)) (punit.lt (rep_list q))"
  have eq: "rep_list (spair p q) = (punit.monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) (rep_list p)) +
                               (punit.monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) (rep_list q))"
    (is "_ = ?a + ?b")
    by (simp add: spair_def Let_def rep_list_minus rep_list_monom_mult punit.monom_mult_uminus_left l_def)
  have "?a + ?b \<noteq> 0" unfolding eq[symmetric] by (fact assms(3))
  moreover from 1 2 assms(1, 2) have "punit.lt ?b = punit.lt ?a"
    by (simp add: lp_monom_mult l_def minus_plus adds_lcs adds_lcs_2)
  moreover have "punit.lc ?b = - punit.lc ?a" by (simp add: 1 2)
  ultimately have "punit.lt (rep_list (spair p q)) \<prec> punit.lt ?a" unfolding eq by (rule punit.lt_plus_lessI)
  also from 1 assms(1) have "... = (l - punit.lt (rep_list p)) + punit.lt (rep_list p)" by (simp add: lp_monom_mult)
  also have "... = l" by (simp add: l_def minus_plus adds_lcs)
  also have "... = (a + punit.lt (rep_list p)) - gcs a b" unfolding l_def using assms(4) by (rule lcs_alt_1)
  also have "... = (a - gcs a b) + punit.lt (rep_list p)" by (simp add: minus_plus gcs_adds)
  finally show ?thesis .
qed

lemma is_regular_spair_sym: "is_regular_spair p q \<Longrightarrow> is_regular_spair q p"
  by (auto simp: is_regular_spair_def Let_def lcs_comm)

lemma is_regular_spairI:
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0"
  and "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
  shows "is_regular_spair p q"
proof -
  have *: "(lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p \<noteq>
           (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list q)) \<oplus> lt q"
    (is "?l \<noteq> ?r")
  proof
    assume "?l = ?r"
    hence "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    with assms(3) show False ..
  qed
  with assms(1, 2) show ?thesis by (simp add: is_regular_spair_def)
qed

lemma is_regular_spairI':
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0"
  and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)" and "a \<oplus> lt p \<noteq> b \<oplus> lt q"
  shows "is_regular_spair p q"
proof -
  have "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
  proof
    assume "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
    hence "a \<oplus> (punit.lt (rep_list q) \<oplus> lt p) = a \<oplus> (punit.lt (rep_list p) \<oplus> lt q)" by (simp only:)
    hence "(a + punit.lt (rep_list q)) \<oplus> lt p = (b + punit.lt (rep_list q)) \<oplus> lt q"
      by (simp add: splus_assoc[symmetric] assms(3))
    hence "punit.lt (rep_list q) \<oplus> (a \<oplus> lt p) = punit.lt (rep_list q) \<oplus> (b \<oplus> lt q)"
      by (simp only: add.commute[of _ "punit.lt (rep_list q)"] splus_assoc)
    hence "a \<oplus> lt p = b \<oplus> lt q" by (simp only: splus_left_canc)
    with assms(4) show False ..
  qed
  with assms(1, 2) show ?thesis by (rule is_regular_spairI)
qed

lemma is_regular_spairD1: "is_regular_spair p q \<Longrightarrow> rep_list p \<noteq> 0"
  by (simp add: is_regular_spair_def)

lemma is_regular_spairD2: "is_regular_spair p q \<Longrightarrow> rep_list q \<noteq> 0"
  by (simp add: is_regular_spair_def)

lemma is_regular_spairD3:
  fixes p q
  defines "t1 \<equiv> punit.lt (rep_list p)"
  defines "t2 \<equiv> punit.lt (rep_list q)"
  assumes "is_regular_spair p q"
  shows "t2 \<oplus> lt p \<noteq> t1 \<oplus> lt q" (is ?thesis1)
    and "lt (monom_mult (1 / punit.lc (rep_list p)) (lcs t1 t2 - t1) p) \<noteq>
         lt (monom_mult (1 / punit.lc (rep_list q)) (lcs t1 t2 - t2) q)"  (is "?l \<noteq> ?r")
proof -
  from assms(3) have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
  hence "punit.lc (rep_list p) \<noteq> 0" and "p \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
  from assms(3) have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
  hence "punit.lc (rep_list q) \<noteq> 0" and "q \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)

  have "?l = (lcs t1 t2 - t1) \<oplus> lt p"
    using \<open>punit.lc (rep_list p) \<noteq> 0\<close> \<open>p \<noteq> 0\<close> by (simp add: lt_monom_mult)
  also from assms(3) have *: "... \<noteq> (lcs t1 t2 - t2) \<oplus> lt q"
    by (simp add: is_regular_spair_def t1_def t2_def Let_def)
  also have "(lcs t1 t2 - t2) \<oplus> lt q = ?r"
    using \<open>punit.lc (rep_list q) \<noteq> 0\<close> \<open>q \<noteq> 0\<close> by (simp add: lt_monom_mult)
  finally show "?l \<noteq> ?r" .

  show ?thesis1
  proof
    assume "t2 \<oplus> lt p = t1 \<oplus> lt q"
    hence "(lcs t1 t2 - t1) \<oplus> lt p = (lcs t1 t2 - t2) \<oplus> lt q"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    with * show False ..
  qed
qed

lemma is_regular_spair_nonzero: "is_regular_spair p q \<Longrightarrow> spair p q \<noteq> 0"
  by (auto simp: spair_def Let_def dest: is_regular_spairD3)

lemma is_regular_spair_lt:
  assumes "is_regular_spair p q"
  shows "lt (spair p q) = ord_term_lin.max
              ((lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p)
              ((lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list q)) \<oplus> lt q)"
proof -
  let ?t1 = "punit.lt (rep_list p)"
  let ?t2 = "punit.lt (rep_list q)"
  let ?l = "lcs ?t1 ?t2"
  show ?thesis
  proof (rule ord_term_lin.linorder_cases)
    assume a: "?t2 \<oplus> lt p \<prec>\<^sub>t ?t1 \<oplus> lt q"
    hence "(?l - ?t1) \<oplus> lt p \<prec>\<^sub>t (?l - ?t2) \<oplus> lt q"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    hence le: "(?l - ?t1) \<oplus> lt p \<preceq>\<^sub>t (?l - ?t2) \<oplus> lt q" by (rule ord_term_lin.less_imp_le)
    from assms have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
    have "lt (spair p q) = lt (spair q p)" by (simp add: spair_comm[of p])
    also from \<open>rep_list q \<noteq> 0\<close> a have "... = (lcs ?t2 ?t1 - ?t2) \<oplus> lt q" by (rule lt_spair)
    also have "... = (?l - ?t2) \<oplus> lt q" by (simp only: lcs_comm)
    finally show ?thesis using le by (simp add: ord_term_lin.max_def)
  next
    assume a: "?t1 \<oplus> lt q \<prec>\<^sub>t ?t2 \<oplus> lt p"
    hence "(?l - ?t2) \<oplus> lt q \<prec>\<^sub>t (?l - ?t1) \<oplus> lt p"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    hence le: "\<not> ((?l - ?t1) \<oplus> lt p \<preceq>\<^sub>t (?l - ?t2) \<oplus> lt q)" by simp
    from assms have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
    hence "lt (spair p q) = (lcs ?t1 ?t2 - ?t1) \<oplus> lt p" using a by (rule lt_spair)
    thus ?thesis using le by (simp add: ord_term_lin.max_def)
  next
    from assms have "?t2 \<oplus> lt p \<noteq> ?t1 \<oplus> lt q" by (rule is_regular_spairD3)
    moreover assume "?t2 \<oplus> lt p = ?t1 \<oplus> lt q"
    ultimately show ?thesis ..
  qed
qed

lemma is_regular_spair_lt_ge_1:
  assumes "is_regular_spair p q"
  shows "lt p \<preceq>\<^sub>t lt (spair p q)"
proof -
  have "lt p = 0 \<oplus> lt p" by (simp only: term_simps)
  also from zero_min have "... \<preceq>\<^sub>t (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule splus_mono_left)
  also have "... \<preceq>\<^sub>t ord_term_lin.max
              ((lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p)
              ((lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list q)) \<oplus> lt q)"
    by (rule ord_term_lin.max.cobounded1)
  also from assms have "... = lt (spair p q)" by (simp only: is_regular_spair_lt)
  finally show ?thesis .
qed

corollary is_regular_spair_lt_ge_2:
  assumes "is_regular_spair p q"
  shows "lt q \<preceq>\<^sub>t lt (spair p q)"
proof -
  from assms have "is_regular_spair q p" by (rule is_regular_spair_sym)
  hence "lt q \<preceq>\<^sub>t lt (spair q p)" by (rule is_regular_spair_lt_ge_1)
  also have "... = lt (spair p q)" by (simp add: spair_comm[of q])
  finally show ?thesis .
qed

lemma is_regular_spair_component_lt_cases:
  assumes "is_regular_spair p q"
  shows "component_of_term (lt (spair p q)) = component_of_term (lt p) \<or>
          component_of_term (lt (spair p q)) = component_of_term (lt q)"
proof (rule ord_term_lin.linorder_cases)
  from assms have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
  moreover assume "punit.lt (rep_list q) \<oplus> lt p \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> lt q"
  ultimately have "lt (spair q p) = (lcs (punit.lt (rep_list q)) (punit.lt (rep_list p)) - punit.lt (rep_list q)) \<oplus> lt q"
    by (rule lt_spair)
  thus ?thesis by (simp add: spair_comm[of p] term_simps)
next
  from assms have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
  moreover assume "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
  ultimately have "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_spair)
  thus ?thesis by (simp add: term_simps)
next
  from assms have "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
    by (rule is_regular_spairD3)
  moreover assume "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
  ultimately show ?thesis ..
qed

lemma lemma_9:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "is_RB_upt d rword G u"
    and "inj_on lt G" and "\<not> is_syz_sig d u" and "is_canon_rewriter rword G u g1" and "h \<in> G"
    and "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 (pp_of_term u - lp g1) g1)"
    and "d (pp_of_term u) \<le> dgrad_max d"
  shows "lcs (punit.lt (rep_list g1)) (punit.lt (rep_list h)) - punit.lt (rep_list g1) =
            pp_of_term u - lp g1" (is ?thesis1)
    and "lcs (punit.lt (rep_list g1)) (punit.lt (rep_list h)) - punit.lt (rep_list h) =
            ((pp_of_term u - lp g1) + punit.lt (rep_list g1)) - punit.lt (rep_list h)" (is ?thesis2)
    and "is_regular_spair g1 h" (is ?thesis3)
    and "lt (spair g1 h) = u" (is ?thesis4)
proof -
  from assms(8) have "rep_list (monom_mult 1 (pp_of_term u - lp g1) g1) \<noteq> 0"
    using is_sig_red_top_addsE by fastforce
  hence "rep_list g1 \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "g1 \<noteq> 0" by (auto simp: rep_list_zero)
  from assms(6) have "g1 \<in> G" and "lt g1 adds\<^sub>t u" by (rule is_canon_rewriterD)+
  from assms(3) have "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  with \<open>g1 \<in> G\<close> have "g1 \<in> dgrad_sig_set d" ..
  hence "component_of_term (lt g1) < length fs" using \<open>g1 \<noteq> 0\<close> by (rule dgrad_sig_setD_lt)
  with \<open>lt g1 adds\<^sub>t u\<close> have "component_of_term u < length fs" by (simp add: adds_term_def)

  from \<open>lt g1 adds\<^sub>t u\<close> obtain a where u: "u = a \<oplus> lt g1" by (rule adds_termE)
  hence a: "a = pp_of_term u - lp g1" by (simp add: term_simps)
  from assms(8) have "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 a g1)" by (simp only: a)
  hence "rep_list h \<noteq> 0" and "rep_list (monom_mult 1 a g1) \<noteq> 0" and
      2: "punit.lt (rep_list h) adds punit.lt (rep_list (monom_mult 1 a g1))" and
      3: "punit.lt (rep_list (monom_mult 1 a g1)) \<oplus> lt h \<prec>\<^sub>t punit.lt (rep_list h) \<oplus> lt (monom_mult 1 a g1)"
    by (auto elim: is_sig_red_top_addsE)
  from this(2) have "rep_list g1 \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "g1 \<noteq> 0" by (auto simp: rep_list_zero)
  from \<open>rep_list h \<noteq> 0\<close> have "h \<noteq> 0" by (auto simp: rep_list_zero)
  from 2 \<open>rep_list g1 \<noteq> 0\<close> have "punit.lt (rep_list h) adds a + punit.lt (rep_list g1)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  then obtain b where eq1: "a + punit.lt (rep_list g1) = b + punit.lt (rep_list h)"
    by (auto elim: addsE simp: add.commute)
  hence b: "b = ((pp_of_term u - lp g1) + punit.lt (rep_list g1)) - punit.lt (rep_list h)"
    by (simp add: a)

  define g where "g = gcs a b"
  have "g = 0"
  proof (rule ccontr)
    assume "g \<noteq> 0"
    have "g adds a" unfolding g_def by (fact gcs_adds)
    also have "... adds\<^sub>p u" unfolding u by (fact adds_pp_triv)
    finally obtain v where u2: "u = g \<oplus> v" by (rule adds_ppE)
    hence v: "v = u \<ominus> g" by (simp add: term_simps)
    from u2 have "v adds\<^sub>t u" by (rule adds_termI)
    hence "v \<preceq>\<^sub>t u" by (rule ord_adds_term)
    moreover have "v \<noteq> u"
    proof
      assume "v = u"
      hence "g \<oplus> v = 0 \<oplus> v" by (simp add: u2 term_simps)
      hence "g = 0" by (simp only: splus_right_canc)
      with \<open>g \<noteq> 0\<close> show False ..
    qed
    ultimately have "v \<prec>\<^sub>t u" by simp
    note assms(3) \<open>v \<prec>\<^sub>t u\<close>
    moreover have "d (pp_of_term v) \<le> dgrad_max d"
    proof (rule le_trans)
      from assms(1) show "d (pp_of_term v) \<le> d (pp_of_term u)"
        by (simp add: u2 term_simps dickson_gradingD1)
    qed fact
    moreover from \<open>component_of_term u < length fs\<close> have "component_of_term v < length fs"
      by (simp only: v term_simps)
    ultimately have "is_RB_in d rword G v" by (rule is_RB_uptD2)
    thus False
    proof (rule is_RB_inE)
      assume "is_syz_sig d v"
      with assms(1) have "is_syz_sig d u" using \<open>v adds\<^sub>t u\<close> assms(9) by (rule is_syz_sig_adds)
      with assms(5) show False ..
    next
      fix g2
      assume *: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g2) g2)"
      assume "is_canon_rewriter rword G v g2"
      hence "g2 \<in> G" and "g2 \<noteq> 0" and "lt g2 adds\<^sub>t v" by (rule is_canon_rewriterD)+
      assume "\<not> is_syz_sig d v"
      note assms(2) \<open>is_canon_rewriter rword G v g2\<close> assms(6)
      moreover from \<open>lt g2 adds\<^sub>t v\<close> \<open>v adds\<^sub>t u\<close> have "lt g2 adds\<^sub>t u" by (rule adds_term_trans)
      moreover from \<open>g adds a\<close> have "lt g1 adds\<^sub>t v" by (simp add: v u minus_splus[symmetric] adds_termI)
      ultimately have "lt g2 = lt g1" by (rule is_rewrite_ord_canon_rewriterD1)
      with assms(4) have "g2 = g1" using \<open>g2 \<in> G\<close> \<open>g1 \<in> G\<close> by (rule inj_onD)
      have "pp_of_term v - lp g1 = a - g" by (simp add: u v term_simps diff_diff_add)
  
      have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g2) g2)"
        unfolding \<open>g2 = g1\<close> \<open>pp_of_term v - lp g1 = a - g\<close> using assms(7) \<open>rep_list h \<noteq> 0\<close>
      proof (rule is_sig_red_top_addsI)
        from \<open>rep_list g1 \<noteq> 0\<close> show "rep_list (monom_mult 1 (a - g) g1) \<noteq> 0"
          by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
      next
        have eq3: "(a - g) + punit.lt (rep_list g1) = lcs (punit.lt (rep_list g1)) (punit.lt (rep_list h))"
          by (simp add: g_def lcs_minus_1[OF eq1, symmetric] adds_minus adds_lcs)
        from \<open>rep_list g1 \<noteq> 0\<close>
        show "punit.lt (rep_list h) adds punit.lt (rep_list (monom_mult 1 (a - g) g1))"
          by (simp add: rep_list_monom_mult punit.lt_monom_mult eq3 adds_lcs_2)
      next
        from 3 \<open>rep_list g1 \<noteq> 0\<close> \<open>g1 \<noteq> 0\<close>
        show "punit.lt (rep_list (monom_mult 1 (a - g) g1)) \<oplus> lt h \<prec>\<^sub>t
              punit.lt (rep_list h) \<oplus> lt (monom_mult 1 (a - g) g1)"
          by (auto simp: rep_list_monom_mult punit.lt_monom_mult lt_monom_mult splus_assoc splus_left_commute
                dest!: ord_term_strict_canc intro: splus_mono_strict)
      next
        show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by (fact ord_term_lin.is_le_relI)
      qed
      with * show False ..
    qed
  qed
  thus ?thesis1 and ?thesis2 by (simp_all add: a b lcs_minus_1[OF eq1] lcs_minus_2[OF eq1] g_def)
  hence eq3: "spair g1 h = monom_mult (1 / punit.lc (rep_list g1)) a g1 -
                            monom_mult (1 / punit.lc (rep_list h)) b h"
    by (simp add: spair_def Let_def a b)

  from 3 \<open>rep_list g1 \<noteq> 0\<close> \<open>g1 \<noteq> 0\<close> have "b \<oplus> lt h \<prec>\<^sub>t a \<oplus> lt g1"
    by (auto simp: rep_list_monom_mult punit.lt_monom_mult lt_monom_mult eq1 splus_assoc
        splus_left_commute[of b] dest!: ord_term_strict_canc)
  hence "a \<oplus> lt g1 \<noteq> b \<oplus> lt h" by simp
  with \<open>rep_list g1 \<noteq> 0\<close> \<open>rep_list h \<noteq> 0\<close> eq1 show ?thesis3
    by (rule is_regular_spairI')

  have "lt (monom_mult (1 / punit.lc (rep_list h)) b h) = b \<oplus> lt h"
  proof (rule lt_monom_mult)
    from \<open>rep_list h \<noteq> 0\<close> show "1 / punit.lc (rep_list h) \<noteq> 0" by (simp add: punit.lc_eq_zero_iff)
  qed fact
  also have "... \<prec>\<^sub>t a \<oplus> lt g1" by fact
  also have "... = lt (monom_mult (1 / punit.lc (rep_list g1)) a g1)"
  proof (rule HOL.sym, rule lt_monom_mult)
    from \<open>rep_list g1 \<noteq> 0\<close> show "1 / punit.lc (rep_list g1) \<noteq> 0" by (simp add: punit.lc_eq_zero_iff)
  qed fact
  finally have "lt (spair g1 h) = lt (monom_mult (1 / punit.lc (rep_list g1)) a g1)"
    unfolding eq3 by (rule lt_minus_eqI_2)
  also have "... = a \<oplus> lt g1" by (rule HOL.sym, fact)
  finally show ?thesis4 by (simp only: u)
qed

lemma is_RB_upt_finite:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "G \<subseteq> dgrad_sig_set d" and "inj_on lt G"
    and "finite G"
    and "\<And>g1 g2. g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> is_regular_spair g1 g2 \<Longrightarrow> lt (spair g1 g2) \<prec>\<^sub>t u \<Longrightarrow>
              is_RB_in d rword G (lt (spair g1 g2))"
    and "\<And>i. i < length fs \<Longrightarrow> term_of_pair (0, i) \<prec>\<^sub>t u \<Longrightarrow> is_RB_in d rword G (term_of_pair (0, i))"
  shows "is_RB_upt d rword G u"
proof (rule ccontr)
  let ?Q = "{v. v \<prec>\<^sub>t u \<and> d (pp_of_term v) \<le> dgrad_max d \<and> component_of_term v < length fs \<and> \<not> is_RB_in d rword G v}"
  have Q_sub: "pp_of_term ` ?Q \<subseteq> dgrad_set d (dgrad_max d)" by blast
  from assms(3) have "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  assume "\<not> is_RB_upt d rword G u"
  with assms(3) obtain v' where "v' \<in> ?Q" unfolding is_RB_upt_def by blast
  with assms(1) obtain v where "v \<in> ?Q" and min: "\<And>y. y \<prec>\<^sub>t v \<Longrightarrow> y \<notin> ?Q" using Q_sub
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>v \<in> ?Q\<close> have "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
    and "\<not> is_RB_in d rword G v" by simp_all
  from this(4)
  have impl: "\<And>g. g \<in> G \<Longrightarrow> is_canon_rewriter rword G v g \<Longrightarrow>
                    is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
    and "\<not> is_syz_sig d v" by (simp_all add: is_RB_in_def Let_def)

  from assms(3) have "is_RB_upt d rword G v"
  proof (rule is_RB_uptI)
    fix w
    assume dw: "d (pp_of_term w) \<le> dgrad_max d" and cp: "component_of_term w < length fs"
    assume "w \<prec>\<^sub>t v"
    hence "w \<notin> ?Q" by (rule min)
    hence "\<not> w \<prec>\<^sub>t u \<or> is_RB_in d rword G w" by (simp add: dw cp)
    thus "is_RB_in d rword G w"
    proof
      assume "\<not> w \<prec>\<^sub>t u"
      moreover from \<open>w \<prec>\<^sub>t v\<close> \<open>v \<prec>\<^sub>t u\<close> have "w \<prec>\<^sub>t u" by (rule ord_term_lin.less_trans)
      ultimately show ?thesis ..
    qed
  qed

  show False
  proof (cases "\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t v")
    case False
    hence x: "\<And>g. g \<in> G \<Longrightarrow> lt g adds\<^sub>t v \<Longrightarrow> g = 0" by blast
    let ?w = "term_of_pair (0, component_of_term v)"
    have "?w adds\<^sub>t v" by (simp add: adds_term_def term_simps)
    hence "?w \<preceq>\<^sub>t v" by (rule ord_adds_term)
    also have "... \<prec>\<^sub>t u" by fact
    finally have "?w \<prec>\<^sub>t u" .
    with \<open>component_of_term v < length fs\<close> have "is_RB_in d rword G ?w" by (rule assms(7))
    thus ?thesis
    proof (rule is_RB_inE)
      assume "is_syz_sig d ?w"
      with assms(1) have "is_syz_sig d v" using \<open>?w adds\<^sub>t v\<close> \<open>d (pp_of_term v) \<le> dgrad_max d\<close>
        by (rule is_syz_sig_adds)
      with \<open>\<not> is_syz_sig d v\<close> show ?thesis ..
    next
      fix g1
      assume "is_canon_rewriter rword G ?w g1"
      hence "g1 \<noteq> 0" and "g1 \<in> G" and "lt g1 adds\<^sub>t ?w" by (rule is_canon_rewriterD)+
      from this(3) have "lt g1 adds\<^sub>t v" using \<open>?w adds\<^sub>t v\<close> by (rule adds_term_trans)
      with \<open>g1 \<in> G\<close> have "g1 = 0" by (rule x)
      with \<open>g1 \<noteq> 0\<close> show ?thesis ..
    qed
  next
    case True
    then obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lt g' adds\<^sub>t v" by blast
    with assms(2, 5) obtain g1 where crw: "is_canon_rewriter rword G v g1"
      by (rule is_rewrite_ord_finite_canon_rewriterE)
    hence "g1 \<in> G" by (rule is_canon_rewriterD1)
    hence "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g1) g1)" using crw by (rule impl)
    then obtain h where "h \<in> G" and "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 (pp_of_term v - lp g1) g1)"
      by (rule is_sig_red_singletonI)
    with assms(1, 2) \<open>is_RB_upt d rword G v\<close> assms(4) \<open>\<not> is_syz_sig d v\<close> crw
    have "is_regular_spair g1 h" and eq: "lt (spair g1 h) = v"
      using \<open>d (pp_of_term v) \<le> dgrad_max d\<close> by (rule lemma_9)+
    from \<open>v \<prec>\<^sub>t u\<close> have "lt (spair g1 h) \<prec>\<^sub>t u" by (simp only: eq)
    with \<open>g1 \<in> G\<close> \<open>h \<in> G\<close> \<open>is_regular_spair g1 h\<close> have "is_RB_in d rword G (lt (spair g1 h))"
      by (rule assms(6))
    hence "is_RB_in d rword G v" by (simp only: eq)
    with \<open>\<not> is_RB_in d rword G v\<close> show ?thesis ..
  qed
qed

text \<open>Note that the following lemma actually holds for @{emph \<open>all\<close>} regularly reducible power-products
  in @{term "rep_list p"}, not just for the leading power-product.\<close>

lemma lemma_11:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "is_RB_upt d rword G (lt p)"
    and "p \<in> dgrad_sig_set d" and "is_sig_red (\<prec>\<^sub>t) (=) G p"
  obtains u g where "u \<prec>\<^sub>t lt p" and "d (pp_of_term u) \<le> dgrad_max d" and "component_of_term u < length fs"
    and "\<not> is_syz_sig d u" and "is_canon_rewriter rword G u g"
    and "u = (punit.lt (rep_list p) - punit.lt (rep_list g)) \<oplus> lt g" and "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
proof -
  from assms(3) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  from assms(5) have "rep_list p \<noteq> 0" using is_sig_red_addsE by fastforce
  hence "p \<noteq> 0" by (auto simp: rep_list_zero)
  let ?lc = "punit.lc (rep_list p)"
  let ?lp = "punit.lt (rep_list p)"
  from \<open>rep_list p \<noteq> 0\<close> have "?lc \<noteq> 0" by (rule punit.lc_not_0)
  from assms(4) have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  from assms(4) have "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
  from assms(4) \<open>p \<noteq> 0\<close> have "component_of_term (lt p) < length fs" by (rule dgrad_sig_setD_lt)
  from assms(1) \<open>p \<in> dgrad_max_set d\<close> have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
  hence "d ?lp \<le> dgrad_max d" using \<open>rep_list p \<noteq> 0\<close> by (rule punit.dgrad_p_setD_lp[simplified])

  from assms(5) obtain g0 where "g0 \<in> G" and "is_sig_red (\<prec>\<^sub>t) (=) {g0} p"
    by (rule is_sig_red_singletonI)
  from \<open>g0 \<in> G\<close> G_sub have "g0 \<in> dgrad_sig_set d" ..
  let ?g0 = "monom_mult (?lc / punit.lc (rep_list g0)) (?lp - punit.lt (rep_list g0)) g0"

  define M where "M = {monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g |
                          g. g \<in> dgrad_sig_set d \<and> is_sig_red (\<prec>\<^sub>t) (=) {g} p}"
  from \<open>g0 \<in> dgrad_sig_set d\<close> \<open>is_sig_red (\<prec>\<^sub>t) (=) {g0} p\<close> have "?g0 \<in> M" by (auto simp: M_def)
  have "0 \<notin> rep_list ` M"
  proof
    assume "0 \<in> rep_list ` M"
    then obtain g where 1: "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
      and 2: "rep_list (monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g) = 0"
      unfolding M_def by fastforce
    from 1 have "rep_list g \<noteq> 0" using is_sig_red_addsE by fastforce
    moreover from this have "punit.lc (rep_list g) \<noteq> 0" by (rule punit.lc_not_0)
    ultimately have "rep_list (monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g) \<noteq> 0"
      using \<open>?lc \<noteq> 0\<close> by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    thus False using 2 ..
  qed
  with rep_list_zero have "0 \<notin> M" by auto
  have "M \<subseteq> dgrad_sig_set d"
  proof
    fix m
    assume "m \<in> M"
    then obtain g where "g \<in> dgrad_sig_set d" and 1: "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
      and m: "m = monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g"
      unfolding M_def by fastforce
    from 1 have "punit.lt (rep_list g) adds ?lp" using is_sig_red_top_addsE by fastforce
    note assms(1)
    thm dickson_grading_minus
    moreover have "d (?lp - punit.lt (rep_list g)) \<le> dgrad_max d"
      by (rule le_trans, rule dickson_grading_minus, fact+)
    ultimately show "m \<in> dgrad_sig_set d" unfolding m using \<open>g \<in> dgrad_sig_set d\<close>
      by (rule dgrad_sig_set_closed_monom_mult)
  qed
  hence "M \<subseteq> sig_inv_set" by (simp add: dgrad_sig_set'_def)

  let ?M = "lt ` M"
  note assms(1)
  moreover from \<open>?g0 \<in> M\<close> have "lt ?g0 \<in> ?M" by (rule imageI)
  moreover from \<open>M \<subseteq> dgrad_sig_set d\<close> have "pp_of_term ` ?M \<subseteq> dgrad_set d (dgrad_max d)"
    by (auto intro!: dgrad_sig_setD_lp)
  ultimately obtain u where "u \<in> ?M" and min: "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> v \<notin> ?M"
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>u \<in> ?M\<close> obtain m where "m \<in> M" and u': "u = lt m" ..
  from this(1) obtain g1 where "g1 \<in> dgrad_sig_set d" and 1: "is_sig_red (\<prec>\<^sub>t) (=) {g1} p"
    and m: "m = monom_mult (?lc / punit.lc (rep_list g1)) (?lp - punit.lt (rep_list g1)) g1"
    unfolding M_def by fastforce
  from 1 have adds: "punit.lt (rep_list g1) adds ?lp" and "?lp \<oplus> lt g1 \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p"
    and "rep_list g1 \<noteq> 0" using is_sig_red_top_addsE by fastforce+
  from this(3) have lc_g1: "punit.lc (rep_list g1) \<noteq> 0" by (rule punit.lc_not_0)
  from \<open>m \<in> M\<close> \<open>0 \<notin> rep_list ` M\<close> have "rep_list m \<noteq> 0" by fastforce
  from \<open>m \<in> M\<close> \<open>0 \<notin> M\<close> have "m \<noteq> 0" by blast
  hence "lc m \<noteq> 0" by (rule lc_not_0)
  from lc_g1 have eq0: "punit.lc (rep_list m) = ?lc" by (simp add: m rep_list_monom_mult)
  from \<open>?lc \<noteq> 0\<close> \<open>rep_list g1 \<noteq> 0\<close> adds have eq1: "punit.lt (rep_list m) = ?lp"
    by (simp add: m rep_list_monom_mult punit.lt_monom_mult punit.lc_eq_zero_iff adds_minus)
  from \<open>m \<in> M\<close> \<open>M \<subseteq> dgrad_sig_set d\<close> have "m \<in> dgrad_sig_set d" ..

  from \<open>rep_list g1 \<noteq> 0\<close> have "punit.lc (rep_list g1) \<noteq> 0" and "g1 \<noteq> 0"
    by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
  with \<open>?lc \<noteq> 0\<close> have u: "u = (?lp - punit.lt (rep_list g1)) \<oplus> lt g1"
    by (simp add: u' m lt_monom_mult lc_eq_zero_iff)
  hence "punit.lt (rep_list g1) \<oplus> u = punit.lt (rep_list g1) \<oplus> ((?lp - punit.lt (rep_list g1)) \<oplus> lt g1)"
    by simp
  also from adds have "... = ?lp \<oplus> lt g1"
    by (simp only: splus_assoc[symmetric], metis add.commute adds_minus)
  also have "... \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p" by fact
  finally have "u \<prec>\<^sub>t lt p" by (rule ord_term_strict_canc)

  from \<open>u \<in> ?M\<close> have "pp_of_term u \<in> pp_of_term ` ?M" by (rule imageI)
  also have "... \<subseteq> dgrad_set d (dgrad_max d)" by fact
  finally have "d (pp_of_term u) \<le> dgrad_max d" by (rule dgrad_setD)

  from \<open>u \<in> ?M\<close> have "component_of_term u \<in> component_of_term ` ?M" by (rule imageI)
  also from \<open>M \<subseteq> sig_inv_set\<close> \<open>0 \<notin> M\<close> sig_inv_setD_lt have "... \<subseteq> {0..<length fs}" by fastforce
  finally have "component_of_term u < length fs" by simp

  have "\<not> is_syz_sig d u"
  proof
    assume "is_syz_sig d u"
    then obtain s where "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d" and "rep_list s = 0"
      by (rule is_syz_sigE)
    let ?s = "monom_mult (lc m / lc s) 0 s"
    have "rep_list ?s = 0" by (simp add: rep_list_monom_mult \<open>rep_list s = 0\<close>)
    from \<open>s \<noteq> 0\<close> have "lc s \<noteq> 0" by (rule lc_not_0)
    hence "lc m / lc s \<noteq> 0" using \<open>lc m \<noteq> 0\<close> by simp
    have "m - ?s \<noteq> 0"
    proof
      assume "m - ?s = 0"
      hence "m = ?s" by simp
      with \<open>rep_list ?s = 0\<close> have "rep_list m = 0" by simp
      with \<open>rep_list m \<noteq> 0\<close> show False ..
    qed
    moreover from \<open>lc m / lc s \<noteq> 0\<close> have "lt ?s = lt m" by (simp add: lt_monom_mult_zero \<open>lt s = u\<close> u')
    moreover from \<open>lc s \<noteq> 0\<close> have "lc ?s = lc m" by simp
    ultimately have "lt (m - ?s) \<prec>\<^sub>t u" unfolding u' by (rule lt_minus_lessI)
    hence "lt (m - ?s) \<notin> ?M" by (rule min)
    hence "m - ?s \<notin> M" by blast
    moreover have "m - ?s \<in> M"
    proof -
      have "?s = monom_mult (?lc / lc s) 0 (monom_mult (lc g1 / punit.lc (rep_list g1)) 0 s)"
        by (simp add: m monom_mult_assoc mult.commute)
      define m' where "m' = m - ?s"
      have eq: "rep_list m' = rep_list m" by (simp add: m'_def rep_list_minus \<open>rep_list ?s = 0\<close>)
      from \<open>?lc \<noteq> 0\<close> have "m' = monom_mult (?lc / punit.lc (rep_list m')) (?lp - punit.lt (rep_list m')) m'"
        by (simp add: eq eq0 eq1)
      also have "... \<in> M" unfolding M_def
      proof (rule, intro exI conjI)
        from \<open>s \<in> dgrad_sig_set d\<close> have "?s \<in> dgrad_sig_set d"
          by (rule dgrad_sig_set_closed_monom_mult_zero)
        with \<open>m \<in> dgrad_sig_set d\<close> show "m' \<in> dgrad_sig_set d" unfolding m'_def
          by (rule dgrad_sig_set_closed_minus)
      next
        show "is_sig_red (\<prec>\<^sub>t) (=) {m'} p"
        proof (rule is_sig_red_top_addsI)
          show "m' \<in> {m'}" by simp
        next
          from \<open>rep_list m \<noteq> 0\<close> show "rep_list m' \<noteq> 0" by (simp add: eq)
        next
          show "punit.lt (rep_list m') adds punit.lt (rep_list p)" by (simp add: eq eq1)
        next
          have "punit.lt (rep_list p) \<oplus> lt m' \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> u"
            by (rule splus_mono_strict, simp only: m'_def \<open>lt (m - ?s) \<prec>\<^sub>t u\<close>)
          also have "... \<prec>\<^sub>t punit.lt (rep_list m') \<oplus> lt p"
            unfolding eq eq1 using \<open>u \<prec>\<^sub>t lt p\<close> by (rule splus_mono_strict)
          finally show "punit.lt (rep_list p) \<oplus> lt m' \<prec>\<^sub>t punit.lt (rep_list m') \<oplus> lt p" .
        next
          show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
        qed fact
      qed (fact refl)
      finally show ?thesis by (simp only: m'_def)
    qed
    ultimately show False ..
  qed

  have "is_RB_in d rword G u" by (rule is_RB_uptD2, fact+)
  thus ?thesis
  proof (rule is_RB_inE)
    assume "is_syz_sig d u"
    with \<open>\<not> is_syz_sig d u\<close> show ?thesis ..
  next
    fix g
    assume "is_canon_rewriter rword G u g"
    hence "g \<in> G" and "g \<noteq> 0" and adds': "lt g adds\<^sub>t u" by (rule is_canon_rewriterD)+
    assume irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)"

    define b where "b = monom_mult 1 (pp_of_term u - lp g) g"
    note assms(1)
    moreover have "is_sig_GB_upt d G (lt m)" unfolding u'[symmetric]
      by (rule is_sig_GB_upt_le, rule is_RB_upt_is_sig_GB_upt, fact+, rule ord_term_lin.less_imp_le, fact)
    moreover from assms(1) have "b \<in> dgrad_sig_set d" unfolding b_def
    proof (rule dgrad_sig_set_closed_monom_mult)
      from adds' have "lp g adds pp_of_term u" by (simp add: adds_term_def)
      with assms(1) have "d (pp_of_term u - lp g) \<le> d (pp_of_term u)" by (rule dickson_grading_minus)
      thus "d (pp_of_term u - lp g) \<le> dgrad_max d" using \<open>d (pp_of_term u) \<le> dgrad_max d\<close>
        by (rule le_trans)
    next
      from \<open>g \<in> G\<close> G_sub show "g \<in> dgrad_sig_set d" ..
    qed
    moreover note \<open>m \<in> dgrad_sig_set d\<close>
    moreover from \<open>g \<noteq> 0\<close> have "lt b = lt m"
      by (simp add: b_def u'[symmetric] lt_monom_mult,
          metis adds' add_diff_cancel_right' adds_termE pp_of_term_splus)
    moreover from \<open>g \<noteq> 0\<close> have "b \<noteq> 0" by (simp add: b_def monom_mult_eq_zero_iff)
    moreover note \<open>m \<noteq> 0\<close>
    moreover from irred have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G b" by (simp add: b_def)
    moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G m"
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) G m"
      then obtain g2 where 1: "g2 \<in> G" and 2: "rep_list g2 \<noteq> 0"
        and 3: "punit.lt (rep_list g2) adds punit.lt (rep_list m)"
        and 4: "punit.lt (rep_list m) \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt m"
        by (rule is_sig_red_top_addsE)
      from 2 have "g2 \<noteq> 0" and "punit.lc (rep_list g2) \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
      with 3 4 have "lt (monom_mult (?lc / punit.lc (rep_list g2)) (?lp - punit.lt (rep_list g2)) g2) \<prec>\<^sub>t u"
        (is "lt ?g2 \<prec>\<^sub>t u")
        using \<open>?lc \<noteq> 0\<close> by (simp add: term_is_le_rel_minus u' eq1 lt_monom_mult)
      hence "lt ?g2 \<notin> ?M" by (rule min)
      hence "?g2 \<notin> M" by blast
      hence "g2 \<notin> dgrad_sig_set d \<or> \<not> is_sig_red (\<prec>\<^sub>t) (=) {g2} p" by (simp add: M_def)
      thus False
      proof
        assume "g2 \<notin> dgrad_sig_set d"
        moreover from \<open>g2 \<in> G\<close> G_sub have "g2 \<in> dgrad_sig_set d" ..
        ultimately show ?thesis ..
      next
        assume "\<not> is_sig_red (\<prec>\<^sub>t) (=) {g2} p"
        moreover have "is_sig_red (\<prec>\<^sub>t) (=) {g2} p"
        proof (rule is_sig_red_top_addsI)
          show "g2 \<in> {g2}" by simp
        next
          from 3 show "punit.lt (rep_list g2) adds punit.lt (rep_list p)" by (simp only: eq1)
        next
          from 4 have "?lp \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> u" by (simp only: eq1 u')
          also from \<open>u \<prec>\<^sub>t lt p\<close> have "... \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt p" by (rule splus_mono_strict)
          finally show "?lp \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt p" .
        next
          show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
        qed fact+
        ultimately show ?thesis ..
      qed
    qed
    ultimately have eq2: "punit.lt (rep_list b) = punit.lt (rep_list m)"
      by (rule sig_regular_top_reduced_lt_unique)
    have "rep_list g \<noteq> 0" by (rule is_RB_inD, fact+)
    moreover from adds' have "lp g adds pp_of_term u" and "component_of_term (lt g) = component_of_term u"
      by (simp_all add: adds_term_def)
    ultimately have "u = (?lp - punit.lt (rep_list g)) \<oplus> lt g"
      by (simp add: eq1[symmetric] eq2[symmetric] b_def rep_list_monom_mult punit.lt_monom_mult
          splus_def adds_minus term_simps)
    have "is_sig_red (\<prec>\<^sub>t) (=) {b} p"
    proof (rule is_sig_red_top_addsI)
      show "b \<in> {b}" by simp
    next
      from \<open>rep_list g \<noteq> 0\<close> show "rep_list b \<noteq> 0"
        by (simp add: b_def rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    next
      show "punit.lt (rep_list b) adds punit.lt (rep_list p)" by (simp add: eq1 eq2)
    next
      show "punit.lt (rep_list p) \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt p"
        by (simp add: eq1 eq2 \<open>lt b = lt m\<close> u'[symmetric] \<open>u \<prec>\<^sub>t lt p\<close> splus_mono_strict)
    next
      show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
    qed fact
    hence "is_sig_red (\<prec>\<^sub>t) (=) {g} p" unfolding b_def by (rule is_sig_red_singleton_monom_multD)
    show ?thesis by (rule, fact+)
  qed
qed

subsubsection \<open>Termination\<close>

definition term_pp_rel :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<times> 'a) \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool"
  where "term_pp_rel r a b \<longleftrightarrow> r (snd b \<oplus> fst a) (snd a \<oplus> fst b)"

definition canon_term_pp_pair :: "('t \<times> 'a) \<Rightarrow> bool"
  where "canon_term_pp_pair a \<longleftrightarrow> (gcs (pp_of_term (fst a)) (snd a) = 0)"

definition cancel_term_pp_pair :: "('t \<times> 'a) \<Rightarrow> ('t \<times> 'a)"
  where "cancel_term_pp_pair a = (fst a \<ominus> (gcs (pp_of_term (fst a)) (snd a)), snd a - (gcs (pp_of_term (fst a)) (snd a)))"

lemma term_pp_rel_refl: "reflp r \<Longrightarrow> term_pp_rel r a a"
  by (simp add: term_pp_rel_def reflp_def)

lemma term_pp_rel_irrefl: "irreflp r \<Longrightarrow> \<not> term_pp_rel r a a"
  by (simp add: term_pp_rel_def irreflp_def)

lemma term_pp_rel_sym: "symp r \<Longrightarrow> term_pp_rel r a b \<Longrightarrow> term_pp_rel r b a"
  by (auto simp: term_pp_rel_def symp_def)

lemma term_pp_rel_trans:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel r a b" and "term_pp_rel r b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "r (snd b \<oplus> fst a) (snd a \<oplus> fst b)" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "r (snd c \<oplus> fst b) (snd b \<oplus> fst c)" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd c \<oplus> fst a) = snd c \<oplus> (snd b \<oplus> fst a)" by (rule splus_left_commute)
  also from assms(1) 1 have "r ... (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"] term_is_le_rel_canc_left)
  also from assms(1) 2 have "r ... (snd b \<oplus> (snd a \<oplus> fst c))"
    by (simp add: splus_left_commute[of "snd b"] term_is_le_rel_canc_left)
  finally(transpD[OF \<open>transp r\<close>]) show ?thesis using assms(1)
    by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma term_pp_rel_trans_eq_left:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel (=) a b" and "term_pp_rel r b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "snd b \<oplus> fst a = snd a \<oplus> fst b" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "r (snd c \<oplus> fst b) (snd b \<oplus> fst c)" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd c \<oplus> fst a) = snd c \<oplus> (snd b \<oplus> fst a)" by (rule splus_left_commute)
  also from assms(1) 1 have "... = (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"])
  finally have eq: "snd b \<oplus> (snd c \<oplus> fst a) = snd a \<oplus> (snd c \<oplus> fst b)" .
  from assms(1) 2 have "r (snd b \<oplus> (snd c \<oplus> fst a)) (snd b \<oplus> (snd a \<oplus> fst c))"
    unfolding eq by (simp add: splus_left_commute[of "snd b"] term_is_le_rel_canc_left)
  thus ?thesis using assms(1) by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma term_pp_rel_trans_eq_right:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel r a b" and "term_pp_rel (=) b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "r (snd b \<oplus> fst a) (snd a \<oplus> fst b)" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "snd c \<oplus> fst b = snd b \<oplus> fst c" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd a \<oplus> fst c) = snd a \<oplus> (snd b \<oplus> fst c)" by (rule splus_left_commute)
  also from assms(1) 2 have "... = (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"])
  finally have eq: "snd b \<oplus> (snd a \<oplus> fst c) = snd a \<oplus> (snd c \<oplus> fst b)" .
  from assms(1) 1 have "r (snd b \<oplus> (snd c \<oplus> fst a)) (snd b \<oplus> (snd a \<oplus> fst c))"
    unfolding eq by (simp add: splus_left_commute[of _ "snd c"] term_is_le_rel_canc_left)
  thus ?thesis using assms(1) by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma canon_term_pp_cancel: "canon_term_pp_pair (cancel_term_pp_pair a)"
  by (simp add: cancel_term_pp_pair_def canon_term_pp_pair_def gcs_minus_gcs term_simps)

lemma term_pp_rel_cancel:
  assumes "reflp r"
  shows "term_pp_rel r a (cancel_term_pp_pair a)"
proof -
  obtain u s where a: "a = (u, s)" by (rule prod.exhaust)
  show ?thesis
  proof (simp add: a cancel_term_pp_pair_def)
    let ?g = "gcs (pp_of_term u) s"
    have "?g adds s" by (fact gcs_adds_2)
    hence "(s - ?g) \<oplus> (u \<ominus> 0) = s \<oplus> u \<ominus> (?g + 0)" using zero_adds_pp
      by (rule minus_splus_sminus)
    also have "... = s \<oplus> (u \<ominus> ?g)"
      by (metis add.left_neutral add.right_neutral adds_pp_def diff_zero gcs_adds_2 gcs_comm
          minus_splus_sminus zero_adds)
    finally have "r ((s - ?g) \<oplus> u) (s \<oplus> (u \<ominus> ?g))" using assms by (simp add: term_simps reflp_def)
    thus "term_pp_rel r (u, s) (u \<ominus> ?g, s - ?g)" by (simp add: a term_pp_rel_def)
  qed
qed

lemma canon_term_pp_rel_id:
  assumes "term_pp_rel (=) a b" and "canon_term_pp_pair a" and "canon_term_pp_pair b"
  shows "a = b"
proof -
  obtain u s where a: "a = (u, s)" by (rule prod.exhaust)
  obtain v t where b: "b = (v, t)" by (rule prod.exhaust)
  from assms(1) have "t \<oplus> u = s \<oplus> v" by (simp add: term_pp_rel_def a b)
  hence 1: "t + pp_of_term u = s + pp_of_term v" by (metis pp_of_term_splus)
  from assms(2) have 2: "gcs (pp_of_term u) s = 0" by (simp add: canon_term_pp_pair_def a)
  from assms(3) have 3: "gcs (pp_of_term v) t = 0" by (simp add: canon_term_pp_pair_def b)
  have "t = t + gcs (pp_of_term u) s" by (simp add: 2)
  also have "... = gcs (t + pp_of_term u) (t + s)" by (simp only: gcs_plus_left)
  also have "... = gcs (s + pp_of_term v) (s + t)" by (simp only: 1 add.commute)
  also have "... = s + gcs (pp_of_term v) t" by (simp only: gcs_plus_left)
  also have "... = s" by (simp add: 3)
  finally have "t = s" .
  moreover from \<open>t \<oplus> u = s \<oplus> v\<close> have "u = v" by (simp only: \<open>t = s\<close> splus_left_canc)
  ultimately show ?thesis by (simp add: a b)
qed

lemma min_set_finite:
  fixes seq :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  assumes "dickson_grading d" and "range seq \<subseteq> dgrad_sig_set d" and "0 \<notin> rep_list ` range seq"
    and "\<And>i j. i < j \<Longrightarrow> lt (seq i) \<prec>\<^sub>t lt (seq j)"
  shows "finite {i. \<not> (\<exists>j<i. lt (seq j) adds\<^sub>t lt (seq i) \<and>
                             punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i)))}"
proof -
  have "inj (\<lambda>i. lt (seq i))"
  proof
    fix i j
    assume eq: "lt (seq i) = lt (seq j)"
    show "i = j"
    proof (rule linorder_cases)
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    next
      assume "j < i"
      hence "lt (seq j) \<prec>\<^sub>t lt (seq i)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    qed
  qed
  hence "inj seq" unfolding comp_def[symmetric] by (rule inj_on_imageI2)

  let ?P1 = "\<lambda>p q. lt p adds\<^sub>t lt q"
  let ?P2 = "\<lambda>p q. punit.lt (rep_list p) adds punit.lt (rep_list q)"
  let ?P = "\<lambda>p q. ?P1 p q \<and> ?P2 p q"
  have "reflp ?P" by (simp add: reflp_def adds_term_refl)
  have "almost_full_on ?P1 (range seq)"
  proof (rule almost_full_on_map)
    let ?B = "{t. pp_of_term t \<in> dgrad_set d (dgrad_max d) \<and> component_of_term t \<in> {0..<length fs}}"
    from assms(1) finite_atLeastLessThan show "almost_full_on (adds\<^sub>t) ?B" by (rule Dickson_term)
    show "lt ` range seq \<subseteq> ?B"
    proof
      fix v
      assume "v \<in> lt ` range seq"
      then obtain p where "p \<in> range seq" and v: "v = lt p" ..
      from this(1) assms(3) have "rep_list p \<noteq> 0" by auto
      hence "p \<noteq> 0" by (auto simp: rep_list_zero)
      from \<open>p \<in> range seq\<close> assms(2) have "p \<in> dgrad_sig_set d" ..
      hence "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
      hence "lp p \<in> dgrad_set d (dgrad_max d)" by (simp add: dgrad_set_def)
      moreover from \<open>p \<in> dgrad_sig_set d\<close> \<open>p \<noteq> 0\<close> have "component_of_term (lt p) < length fs"
        by (rule dgrad_sig_setD_lt)
      ultimately show "v \<in> ?B" by (simp add: v)
    qed
  qed
  moreover have "almost_full_on ?P2 (range seq)"
  proof (rule almost_full_on_map)
    let ?B = "dgrad_set d (dgrad_max d)"
    from assms(1) show "almost_full_on (adds) ?B" by (rule dickson_gradingD_dgrad_set)
    show "(\<lambda>p. punit.lt (rep_list p)) ` range seq \<subseteq> ?B"
    proof
      fix t
      assume "t \<in> (\<lambda>p. punit.lt (rep_list p)) ` range seq"
      then obtain p where "p \<in> range seq" and t: "t = punit.lt (rep_list p)" ..
      from this(1) assms(3) have "rep_list p \<noteq> 0" by auto
      from \<open>p \<in> range seq\<close> assms(2) have "p \<in> dgrad_sig_set d" ..
      hence "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
      with assms(1) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
      from this \<open>rep_list p \<noteq> 0\<close> have "d (punit.lt (rep_list p)) \<le> dgrad_max d"
        by (rule punit.dgrad_p_setD_lp[simplified])
      thus "t \<in> ?B" by (simp add: t dgrad_set_def)
    qed
  qed
  ultimately have "almost_full_on ?P (range seq)" by (rule almost_full_on_same)
  with \<open>reflp ?P\<close> obtain T where "finite T" and "T \<subseteq> range seq" and *: "\<And>p. p \<in> range seq \<Longrightarrow> (\<exists>q\<in>T. ?P q p)"
    by (rule almost_full_on_finite_subsetE, blast)
  from \<open>T \<subseteq> range seq\<close> obtain I where T: "T = seq ` I" by (meson subset_image_iff)
  have "{i. \<not> (\<exists>j<i. ?P (seq j) (seq i))} \<subseteq> I"
  proof
    fix i
    assume "i \<in> {i. \<not> (\<exists>j<i. ?P (seq j) (seq i))}"
    hence x: "\<not> (\<exists>j<i. ?P (seq j) (seq i))" by simp
    obtain j where "j \<in> I" and "?P (seq j) (seq i)"
    proof -
      have "seq i \<in> range seq" by simp
      hence "\<exists>q\<in>T. ?P q (seq i)" by (rule *)
      then obtain q where "q \<in> T" and "?P q (seq i)" ..
      from this(1) obtain j where "j \<in> I" and "q = seq j" unfolding T ..
      from this(1) \<open>?P q (seq i)\<close> show ?thesis unfolding \<open>q = seq j\<close> ..
    qed
    from this(2) x have "i \<le> j" by auto
    moreover have "\<not> i < j"
    proof
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      hence "\<not> ?P1 (seq j) (seq i)" using ord_adds_term ord_term_lin.leD by blast
      with \<open>?P (seq j) (seq i)\<close> show False by simp
    qed
    ultimately show "i \<in> I" using \<open>j \<in> I\<close> by simp
  qed
  moreover from \<open>inj seq\<close> \<open>finite T\<close> have "finite I" by (simp add: finite_image_iff inj_on_subset T)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma rb_termination:
  fixes seq :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  assumes "dickson_grading d" and "range seq \<subseteq> dgrad_sig_set d" and "0 \<notin> rep_list ` range seq"
    and "\<And>i j. i < j \<Longrightarrow> lt (seq i) \<prec>\<^sub>t lt (seq j)"
    and "\<And>i. \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}) (seq i)"
    and "\<And>i. (\<exists>j<length fs. lt (seq i) = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
                punit.lt (rep_list (seq i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
              (\<exists>j k. is_regular_spair (seq j) (seq k) \<and> rep_list (spair (seq j) (seq k)) \<noteq> 0 \<and>
                    lt (seq i) = lt (spair (seq j) (seq k)) \<and>
                    punit.lt (rep_list (seq i)) \<preceq> punit.lt (rep_list (spair (seq j) (seq k))))"
    and "\<And>i. is_sig_GB_upt d (seq ` {0..<i}) (lt (seq i))"
  shows thesis
proof -
  from assms(3) have "0 \<notin> range seq" using rep_list_zero by auto
  have "ord_term_lin.is_le_rel (=)" and "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by (rule ord_term_lin.is_le_relI)+
  have "reflp (=)" and "symp (=)" by (simp_all add: symp_def)
  have "irreflp (\<prec>\<^sub>t)" by (simp add: irreflp_def)
  have "inj (\<lambda>i. lt (seq i))"
  proof
    fix i j
    assume eq: "lt (seq i) = lt (seq j)"
    show "i = j"
    proof (rule linorder_cases)
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    next
      assume "j < i"
      hence "lt (seq j) \<prec>\<^sub>t lt (seq i)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    qed
  qed
  hence "inj seq" unfolding comp_def[symmetric] by (rule inj_on_imageI2)

  define R where "R = (\<lambda>x. {i. term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) x})"
  let ?A = "{x. canon_term_pp_pair x \<and> R x \<noteq> {}}"

  have "finite ?A"
  proof -
    define min_set where "min_set = {i. \<not> (\<exists>j<i. lt (seq j) adds\<^sub>t lt (seq i) \<and>
                                      punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i)))}"
    have "?A \<subseteq> (\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set"
    proof
      fix u t
      assume "(u, t) \<in> ?A"
      hence "canon_term_pp_pair (u, t)" and "R (u, t) \<noteq> {}" by simp_all
      from this(2) obtain i where x: "term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) (u, t)"
        by (auto simp: R_def)
      let ?equiv = "(\<lambda>i j. term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) (lt (seq j), punit.lt (rep_list (seq j))))"
      obtain j where "j \<in> min_set" and "?equiv j i"
      proof (cases "i \<in> min_set")
        case True
        moreover have "?equiv i i" by (simp add: term_pp_rel_refl)
        ultimately show ?thesis ..
      next
        case False
        let ?Q = "{seq j | j. j < i \<and> is_sig_red (=) (=) {seq j} (seq i)}"
        have "?Q \<subseteq> range seq" by blast
        also have "... \<subseteq> dgrad_sig_set d" by (fact assms(2))
        finally have "?Q \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
        moreover from \<open>?Q \<subseteq> range seq\<close> \<open>0 \<notin> range seq\<close> have "0 \<notin> ?Q" by blast
        ultimately have Q_sub: "pp_of_term ` lt ` ?Q \<subseteq> dgrad_set d (dgrad_max d)"
          unfolding image_image by (smt CollectI dgrad_p_setD_lp dgrad_set_def image_subset_iff subsetCE)
        have *: "\<exists>g\<in>seq ` {0..<k}. is_sig_red (=) (=) {g} (seq k)" if "k \<notin> min_set" for k
          proof -
          from that obtain j where "j < k" and a: "lt (seq j) adds\<^sub>t lt (seq k)"
            and b: "punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq k))" by (auto simp: min_set_def)
          note assms(1, 7)
          moreover from assms(2) have "seq k \<in> dgrad_sig_set d" by fastforce
          moreover from \<open>j < k\<close> have "seq j \<in> seq ` {0..<k}" by simp
          moreover from assms(3) have "rep_list (seq k) \<noteq> 0" and "rep_list (seq j) \<noteq> 0" by fastforce+
          ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) (seq ` {0..<k}) (seq k)" using a b by (rule lemma_21)
          moreover from assms(5)[of k] have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (seq ` {0..<k}) (seq k)"
            by (simp add: is_sig_red_top_tail_cases)
          ultimately have "is_sig_red (=) (=) (seq ` {0..<k}) (seq k)"
            by (simp add: is_sig_red_sing_reg_cases)
          then obtain g0 where "g0 \<in> seq ` {0..<k}" and "is_sig_red (=) (=) {g0} (seq k)"
            by (rule is_sig_red_singletonI)
          thus ?thesis ..
        qed

        from this[OF False] obtain g0 where "g0 \<in> seq ` {0..<i}" and "is_sig_red (=) (=) {g0} (seq i)" ..
        hence "g0 \<in> ?Q" by fastforce
        hence "lt g0 \<in> lt ` ?Q" by (rule imageI)
        with assms(1) obtain v where "v \<in> lt ` ?Q" and min: "\<And>v'. v' \<prec>\<^sub>t v \<Longrightarrow> v' \<notin> lt ` ?Q"
          using Q_sub by (rule ord_term_minimum_dgrad_set, blast)
        from this(1) obtain j where "j < i" and "is_sig_red (=) (=) {seq j} (seq i)"
          and v: "v = lt (seq j)" by fastforce
        hence 1: "punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i))"
          and 2: "punit.lt (rep_list (seq i)) \<oplus> lt (seq j) = punit.lt (rep_list (seq j)) \<oplus> lt (seq i)"
          by (auto elim: is_sig_red_top_addsE)
        show ?thesis
        proof
          show "?equiv j i" by (simp add: term_pp_rel_def 2)
        next
          show "j \<in> min_set"
          proof (rule ccontr)
            assume "j \<notin> min_set"
            from *[OF this] obtain g1 where "g1 \<in> seq ` {0..<j}" and red: "is_sig_red (=) (=) {g1} (seq j)" ..
            from this(1) obtain j0 where "j0 < j" and "g1 = seq j0" by fastforce+

            from red have 3: "punit.lt (rep_list (seq j0)) adds punit.lt (rep_list (seq j))"
              and 4: "punit.lt (rep_list (seq j)) \<oplus> lt (seq j0) = punit.lt (rep_list (seq j0)) \<oplus> lt (seq j)"
              by (auto simp: \<open>g1 = seq j0\<close> elim: is_sig_red_top_addsE)

            from \<open>j0 < j\<close> \<open>j < i\<close> have "j0 < i" by simp
            from \<open>j0 < j\<close> have "lt (seq j0) \<prec>\<^sub>t v" unfolding v by (rule assms(4))
            hence "lt (seq j0) \<notin> lt `?Q" by (rule min)
            with \<open>j0 < i\<close> have "\<not> is_sig_red (=) (=) {seq j0} (seq i)" by blast
            moreover have "is_sig_red (=) (=) {seq j0} (seq i)"
            proof (rule is_sig_red_top_addsI)
              from assms(3) show "rep_list (seq j0) \<noteq> 0" by fastforce
            next
              from assms(3) show "rep_list (seq i) \<noteq> 0" by fastforce
            next
              from 3 1 show "punit.lt (rep_list (seq j0)) adds punit.lt (rep_list (seq i))"
                by (rule adds_trans)
            next
              from 4 have "?equiv j0 j" by (simp add: term_pp_rel_def)
              also from 2 have "?equiv j i" by (simp add: term_pp_rel_def)
              finally(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>])
              show "punit.lt (rep_list (seq i)) \<oplus> lt (seq j0) = punit.lt (rep_list (seq j0)) \<oplus> lt (seq i)"
                by (simp add: term_pp_rel_def)
            next
              show "ord_term_lin.is_le_rel (=)" by simp
            qed simp_all
            ultimately show False ..
          qed
        qed
      qed
      have "term_pp_rel (=) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))) (lt (seq j), punit.lt (rep_list (seq j)))"
        by (rule term_pp_rel_sym, fact \<open>symp (=)\<close>, rule term_pp_rel_cancel, fact \<open>reflp (=)\<close>)
      also note \<open>?equiv j i\<close>
      also(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>]) note x
      finally(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>])
      have "term_pp_rel (=) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))) (u, t)" .
      with \<open>symp (=)\<close> have "term_pp_rel (=) (u, t) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j))))"
        by (rule term_pp_rel_sym)
      hence "(u, t) = cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))"
        using \<open>canon_term_pp_pair (u, t)\<close> canon_term_pp_cancel by (rule canon_term_pp_rel_id)
      with \<open>j \<in> min_set\<close> show "(u, t) \<in> (\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set"
        by fastforce
    qed
    moreover have "finite ((\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set)"
    proof (rule finite_imageI)
      show "finite min_set" unfolding min_set_def using assms(1-4) by (rule min_set_finite)
    qed
    ultimately show ?thesis by (rule finite_subset)
  qed

  have "range seq \<subseteq> seq ` (\<Union> (R ` ?A))"
  proof (rule image_mono, rule)
    fix i
    show "i \<in> (\<Union> (R ` ?A))"
    proof
      show "i \<in> R (cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i))))"
        by (simp add: R_def term_pp_rel_cancel)
      thus "cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i))) \<in> ?A"
        using canon_term_pp_cancel by blast
    qed
  qed
  moreover from \<open>inj seq\<close> have "infinite (range seq)" by (rule range_inj_infinite)
  ultimately have "infinite (seq ` (\<Union> (R ` ?A)))" by (rule infinite_super)
  moreover have "finite (seq ` (\<Union> (R ` ?A)))"
  proof (rule finite_imageI, rule finite_UN_I)
    fix x
    assume "x \<in> ?A"
    let ?rel = "term_pp_rel (\<prec>\<^sub>t)"
    have "irreflp ?rel" by (rule irreflpI, rule term_pp_rel_irrefl, fact)
    moreover have "transp ?rel" by (rule transpI, drule term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>])
    ultimately have "wfp_on ?rel ?A" using \<open>finite ?A\<close> by (rule wfp_on_finite)
    thus "finite (R x)" using \<open>x \<in> ?A\<close>
    proof (induct rule: wfp_on_induct)
      case (less x)
      from less(1) have "canon_term_pp_pair x" by simp
      define R' where " R' = \<Union> (R ` ({x. canon_term_pp_pair x \<and> R x \<noteq> {}} \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x}))"
      define red_set where "red_set = (\<lambda>p::'t \<Rightarrow>\<^sub>0 'b. {k. lt (seq k) = lt p \<and>
                                              punit.lt (rep_list (seq k)) \<preceq> punit.lt (rep_list p)})"
      have finite_red_set: "finite (red_set p)" for p
      proof (cases "red_set p = {}")
        case True
        thus ?thesis by simp
      next
        case False
        then obtain k where lt_k: "lt (seq k) = lt p" by (auto simp: red_set_def)
        have "red_set p \<subseteq> {k}"
        proof
          fix k'
          assume "k' \<in> red_set p"
          hence "lt (seq k') = lt p" by (simp add: red_set_def)
          hence "lt (seq k') = lt (seq k)" by (simp only: lt_k)
          with \<open>inj (\<lambda>i. lt (seq i))\<close> have "k' = k" by (rule injD)
          thus "k' \<in> {k}" by simp
        qed
        thus ?thesis using infinite_super by auto
      qed

      have "R x \<subseteq> (\<Union>i\<in>R'. \<Union>j\<in>R'. red_set (spair (seq i) (seq j))) \<union>
                   (\<Union>j\<in>{0..<length fs}. red_set (monomial 1 (term_of_pair (0, j))))"
        (is "_ \<subseteq> ?B \<union> ?C")
      proof
        fix i
        assume "i \<in> R x"
        hence i_x: "term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) x"
          by (simp add: R_def term_pp_rel_def)
        from assms(6)[of i] show "i \<in> ?B \<union> ?C"
        proof (elim disjE exE conjE)
          fix j
          assume "j < length fs"
          hence "j \<in> {0..<length fs}" by simp
          assume "lt (seq i) = lt (monomial (1::'b) (term_of_pair (0, j)))"
            and "punit.lt (rep_list (seq i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))"
          hence "i \<in> red_set (monomial 1 (term_of_pair (0, j)))" by (simp add: red_set_def)
          with \<open>j \<in> {0..<length fs}\<close> have "i \<in> ?C" ..
          thus ?thesis ..
        next
          fix j k
          let ?li = "punit.lt (rep_list (seq i))"
          let ?lj = "punit.lt (rep_list (seq j))"
          let ?lk = "punit.lt (rep_list (seq k))"
          assume lt_i: "lt (seq i) = lt (spair (seq j) (seq k))"
            and lt_i': "?li \<preceq> punit.lt (rep_list (spair (seq j) (seq k)))"
            and spair_0: "rep_list (spair (seq j) (seq k)) \<noteq> 0"
          hence "i \<in> red_set (spair (seq j) (seq k))" by (simp add: red_set_def)
          from assms(3) have i_0: "rep_list (seq i) \<noteq> 0" and j_0: "rep_list (seq j) \<noteq> 0"
            and k_0: "rep_list (seq k) \<noteq> 0" by fastforce+

          have R'I: "a \<in> R'" if "term_pp_rel (\<prec>\<^sub>t) (lt (seq a), punit.lt (rep_list (seq a))) x" for a
          proof -
            let ?x = "cancel_term_pp_pair (lt (seq a), punit.lt (rep_list (seq a)))"
            show ?thesis unfolding R'_def
            proof (rule UN_I, simp, intro conjI)
              show "a \<in> R ?x" by (simp add: R_def term_pp_rel_cancel)
              thus "R ?x \<noteq> {}" by blast
            next
              note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
              moreover have "term_pp_rel (=) ?x (lt (seq a), punit.lt (rep_list (seq a)))"
                by (rule term_pp_rel_sym, fact, rule term_pp_rel_cancel, fact)
              ultimately show "term_pp_rel (\<prec>\<^sub>t) ?x x" using that by (rule term_pp_rel_trans_eq_left)
            qed (fact canon_term_pp_cancel)
          qed

          assume "is_regular_spair (seq j) (seq k)"
          hence "?lk \<oplus> lt (seq j) \<noteq> ?lj \<oplus> lt (seq k)" by (rule is_regular_spairD3)
          hence "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x \<and> term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x"
          proof (rule ord_term_lin.neqE)
            assume c: "?lk \<oplus> lt (seq j) \<prec>\<^sub>t ?lj \<oplus> lt (seq k)"
            hence j_k: "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) (lt (seq k), ?lk)"
              by (simp add: term_pp_rel_def)
            note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
            moreover have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) (lt (seq i), ?li)"
            proof (simp add: term_pp_rel_def)
              from lt_i' have "?li \<oplus> lt (seq k) \<preceq>\<^sub>t
                                punit.lt (rep_list (spair (seq j) (seq k))) \<oplus> lt (seq k)"
                by (rule splus_mono_left)
              also have "... \<prec>\<^sub>t (?lk - gcs ?lk ?lj + ?lj) \<oplus> lt (seq k)"
                by (rule splus_mono_strict_left, rule lt_rep_list_spair, fact+, simp only: add.commute)
              also have "... = ((?lk + ?lj) - gcs ?lj ?lk) \<oplus> lt (seq k)"
                by (simp add: minus_plus gcs_adds_2 gcs_comm)
              also have "... = ?lk \<oplus> ((?lj - gcs ?lj ?lk) \<oplus> lt (seq k))"
                by (simp add: minus_plus' gcs_adds splus_assoc[symmetric])
              also have "... = ?lk \<oplus> lt (seq i)"
                by (simp add: lt_spair'[OF k_0 _ c] add.commute spair_comm[of "seq j"] lt_i)
              finally show "?li \<oplus> lt (seq k) \<prec>\<^sub>t ?lk \<oplus> lt (seq i)" .
            qed
            ultimately have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x" using i_x
              by (rule term_pp_rel_trans_eq_right)
            moreover from \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close> j_k this
            have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x" by (rule term_pp_rel_trans)
            ultimately show ?thesis by simp
          next
            assume c: "?lj \<oplus> lt (seq k) \<prec>\<^sub>t ?lk \<oplus> lt (seq j)"
            hence j_k: "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) (lt (seq j), ?lj)"
              by (simp add: term_pp_rel_def)
            note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
            moreover have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) (lt (seq i), ?li)"
            proof (simp add: term_pp_rel_def)
              from lt_i' have "?li \<oplus> lt (seq j) \<preceq>\<^sub>t
                                punit.lt (rep_list (spair (seq j) (seq k))) \<oplus> lt (seq j)"
                by (rule splus_mono_left)
              thm lt_rep_list_spair
              also have "... \<prec>\<^sub>t (?lk - gcs ?lk ?lj + ?lj) \<oplus> lt (seq j)"
                by (rule splus_mono_strict_left, rule lt_rep_list_spair, fact+, simp only: add.commute)
              also have "... = ((?lk + ?lj) - gcs ?lk ?lj) \<oplus> lt (seq j)"
                by (simp add: minus_plus gcs_adds_2 gcs_comm)
              also have "... = ?lj \<oplus> ((?lk - gcs ?lk ?lj) \<oplus> lt (seq j))"
                by (simp add: minus_plus' gcs_adds splus_assoc[symmetric] add.commute)
              also have "... = ?lj \<oplus> lt (seq i)" by (simp add: lt_spair'[OF j_0 _ c] lt_i add.commute)
              finally show "?li \<oplus> lt (seq j) \<prec>\<^sub>t ?lj \<oplus> lt (seq i)" .
            qed
            ultimately have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x" using i_x
              by (rule term_pp_rel_trans_eq_right)
            moreover from \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close> j_k this
            have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x" by (rule term_pp_rel_trans)
            ultimately show ?thesis by simp
          qed
          with \<open>i \<in> red_set (spair (seq j) (seq k))\<close> have "i \<in> ?B" using R'I by blast
          thus ?thesis ..
        qed
      qed
      moreover have "finite (?B \<union> ?C)"
      proof (rule finite_UnI)
        have "finite R'" unfolding R'_def
        proof (rule finite_UN_I)
          from \<open>finite ?A\<close> show "finite (?A \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x})" by simp
        next
          fix y
          assume "y \<in> ?A \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x}"
          hence "y \<in> ?A" and "term_pp_rel (\<prec>\<^sub>t) y x" by simp_all
          thus "finite (R y)" by (rule less(2))
        qed
        show "finite ?B" by (intro finite_UN_I \<open>finite R'\<close> finite_red_set)
      next
        show "finite ?C" by (intro finite_UN_I finite_atLeastLessThan finite_red_set)
      qed
      ultimately show ?case by (rule finite_subset)
    qed
  qed fact
  ultimately show ?thesis ..
qed

subsubsection \<open>Concrete Rewrite Orders\<close>

definition is_strict_rewrite_ord :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_strict_rewrite_ord rel \<longleftrightarrow> is_rewrite_ord (\<lambda>x y. \<not> rel y x)"

lemma is_strict_rewrite_ordI: "is_rewrite_ord (\<lambda>x y. \<not> rel y x) \<Longrightarrow> is_strict_rewrite_ord rel"
  unfolding is_strict_rewrite_ord_def by blast

lemma is_strict_rewrite_ordD: "is_strict_rewrite_ord rel \<Longrightarrow> is_rewrite_ord (\<lambda>x y. \<not> rel y x)"
  unfolding is_strict_rewrite_ord_def by blast

lemma is_strict_rewrite_ord_antisym:
  assumes "is_strict_rewrite_ord rel" and "\<not> rel x y" and "\<not> rel y x"
  shows "fst x = fst y"
  by (rule is_rewrite_ordD4, rule is_strict_rewrite_ordD, fact+)

lemma is_strict_rewrite_ord_asym:
  assumes "is_strict_rewrite_ord rel" and "rel x y"
  shows "\<not> rel y x"
proof -
  from assms(1) have "is_rewrite_ord (\<lambda>x y. \<not> rel y x)" by (rule is_strict_rewrite_ordD)
  thus ?thesis
  proof (rule is_rewrite_ordD3)
    assume "\<not> \<not> rel y x"
    assume "\<not> rel x y"
    thus ?thesis using \<open>rel x y\<close> ..
  qed
qed

lemma is_strict_rewrite_ord_irrefl: "is_strict_rewrite_ord rel \<Longrightarrow> \<not> rel x x"
  using is_strict_rewrite_ord_asym by blast

definition rw_rat :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_rat p q \<longleftrightarrow> (let u = punit.lt (snd q) \<oplus> fst p; v = punit.lt (snd p) \<oplus> fst q in
                          u \<prec>\<^sub>t v \<or> (u = v \<and> fst p \<preceq>\<^sub>t fst q))"

definition rw_rat_strict :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_rat_strict p q \<longleftrightarrow> (let u = punit.lt (snd q) \<oplus> fst p; v = punit.lt (snd p) \<oplus> fst q in
                          u \<prec>\<^sub>t v \<or> (u = v \<and> fst p \<prec>\<^sub>t fst q))"

definition rw_add :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_add p q \<longleftrightarrow> (fst p \<preceq>\<^sub>t fst q)"

definition rw_add_strict :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_add_strict p q \<longleftrightarrow> (fst p \<prec>\<^sub>t fst q)"

lemma rw_rat_alt: "rw_rat = (\<lambda>p q. \<not> rw_rat_strict q p)"
  by (intro ext, auto simp: rw_rat_def rw_rat_strict_def Let_def)

lemma rw_rat_is_rewrite_ord: "is_rewrite_ord rw_rat"
proof (rule is_rewrite_ordI)
  show "reflp rw_rat" by (simp add: reflp_def rw_rat_def)
next
  have 1: "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" and 2: "ord_term_lin.is_le_rel (=)"
    by (rule ord_term_lin.is_le_relI)+
  have "rw_rat p q \<longleftrightarrow> (term_pp_rel (\<prec>\<^sub>t) (fst p, punit.lt (snd p)) (fst q, punit.lt (snd q)) \<or>
                        (term_pp_rel (=) (fst p, punit.lt (snd p)) (fst q, punit.lt (snd q)) \<and>
                          fst p \<preceq>\<^sub>t fst q))"
    for p q
  by (simp add: rw_rat_def term_pp_rel_def Let_def)
  thus "transp rw_rat"
    by (auto simp: transp_def dest: term_pp_rel_trans[OF 1] term_pp_rel_trans_eq_left[OF 1]
        term_pp_rel_trans_eq_right[OF 1] term_pp_rel_trans[OF 2])
next
  fix p q
  show "rw_rat p q \<or> rw_rat q p" by (auto simp: rw_rat_def Let_def)
next
  fix p q
  assume "rw_rat p q" and "rw_rat q p"
  thus "fst p = fst q" by (auto simp: rw_rat_def Let_def)
next
  fix d G p q
  assume d: "dickson_grading d" and gb: "is_sig_GB_upt d G (lt q)" and "p \<in> G" and "q \<in> G"
    and "p \<noteq> 0" and "q \<noteq> 0" and "lt p adds\<^sub>t lt q" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  let ?u = "punit.lt (rep_list q) \<oplus> lt p"
  let ?v = "punit.lt (rep_list p) \<oplus> lt q"
  from \<open>lt p adds\<^sub>t lt q\<close> obtain t where lt_q: "lt q = t \<oplus> lt p" by (rule adds_termE)
  from gb have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set'_def)
  with d obtain p' where red: "(sig_red (\<prec>\<^sub>t) (=) G)\<^sup>*\<^sup>* (monom_mult 1 t p) p'"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p'" by (rule sig_irredE_dgrad_max_set)
  from red have "lt p' = lt (monom_mult 1 t p)" and "lc p' = lc (monom_mult 1 t p)"
    and 2: "punit.lt (rep_list p') \<preceq> punit.lt (rep_list (monom_mult 1 t p))"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc, rule sig_red_rtrancl_lt_rep_list)
  with \<open>p \<noteq> 0\<close> have "lt p' = lt q" and "lc p' = lc p" by (simp_all add: lt_q lt_monom_mult)
  from 2 punit.lt_monom_mult_le[simplified] have 3: "punit.lt (rep_list p') \<preceq> t + punit.lt (rep_list p)"
    unfolding rep_list_monom_mult by (rule ordered_powerprod_lin.order_trans)
  have "punit.lt (rep_list p') = punit.lt (rep_list q)"
  proof (rule sig_regular_top_reduced_lt_unique)
    show "p' \<in> dgrad_sig_set d"
    proof (rule dgrad_sig_set_closed_sig_red_rtrancl)
      note d
      moreover have "d t \<le> dgrad_max d"
      proof (rule le_trans)
        have "t adds lp q" by (simp add: lt_q term_simps)
        with d show "d t \<le> d (lp q)" by (rule dickson_grading_adds_imp_le)
      next
        from \<open>q \<in> G\<close> \<open>G \<subseteq> dgrad_max_set d\<close> have "q \<in> dgrad_max_set d" ..
        thus "d (lp q) \<le> dgrad_max d" using \<open>q \<noteq> 0\<close> by (rule dgrad_p_setD_lp)
      qed
      moreover from \<open>p \<in> G\<close> \<open>G \<subseteq> dgrad_sig_set d\<close> have "p \<in> dgrad_sig_set d" ..
      ultimately show "monom_mult 1 t p \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult)
    qed fact+
  next
    from \<open>q \<in> G\<close> \<open>G \<subseteq> dgrad_sig_set d\<close> show "q \<in> dgrad_sig_set d" ..
  next
    from \<open>p \<noteq> 0\<close> \<open>lc p' = lc p\<close> show "p' \<noteq> 0" by (auto simp: lc_eq_zero_iff)
  qed fact+
  with 3 have "punit.lt (rep_list q) \<preceq> t + punit.lt (rep_list p)" by simp
  hence "?u \<preceq>\<^sub>t (t + punit.lt (rep_list p)) \<oplus> lt p" by (rule splus_mono_left)
  also have "... = ?v" by (simp add: lt_q splus_assoc splus_left_commute)
  finally have "?u \<preceq>\<^sub>t ?v" by (simp only: rel_def)
  moreover from \<open>lt p adds\<^sub>t lt q\<close> have "lt p \<preceq>\<^sub>t lt q" by (rule ord_adds_term)
  ultimately show "rw_rat (spp_of p) (spp_of q)" by (auto simp: rw_rat_def Let_def spp_of_def)
qed

lemma rw_rat_strict_is_strict_rewrite_ord: "is_strict_rewrite_ord rw_rat_strict"
proof (rule is_strict_rewrite_ordI)
  show "is_rewrite_ord (\<lambda>x y. \<not> rw_rat_strict y x)"
    unfolding rw_rat_alt[symmetric] by (fact rw_rat_is_rewrite_ord)
qed

lemma rw_add_alt: "rw_add = (\<lambda>p q. \<not> rw_add_strict q p)"
  by (intro ext, auto simp: rw_add_def rw_add_strict_def)

lemma rw_add_is_rewrite_ord: "is_rewrite_ord rw_add"
proof (rule is_rewrite_ordI)
  show "reflp rw_add" by (simp add: reflp_def rw_add_def)
next
  show "transp rw_add" by (auto simp: transp_def rw_add_def)
next
  fix p q
  show "rw_add p q \<or> rw_add q p" by (simp only: rw_add_def ord_term_lin.linear)
next
  fix p q
  assume "rw_add p q" and "rw_add q p"
  thus "fst p = fst q" unfolding rw_add_def by (rule ord_term_lin.antisym)
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "lt p adds\<^sub>t lt q"
  thus "rw_add (spp_of p) (spp_of q)" unfolding rw_add_def spp_of_def fst_conv by (rule ord_adds_term)
qed

lemma rw_add_strict_is_strict_rewrite_ord: "is_strict_rewrite_ord rw_add_strict"
proof (rule is_strict_rewrite_ordI)
  show "is_rewrite_ord (\<lambda>x y. \<not> rw_add_strict y x)"
    unfolding rw_add_alt[symmetric] by (fact rw_add_is_rewrite_ord)
qed

subsubsection \<open>Preparations for Sig-Poly-Pairs\<close>

context
  fixes dgrad :: "'a \<Rightarrow> nat"
begin

definition spp_rel :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "spp_rel sp r \<longleftrightarrow> (r \<noteq> 0 \<and> r \<in> dgrad_sig_set dgrad \<and> lt r = fst sp \<and> rep_list r = snd sp)"

definition spp_inv :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "spp_inv sp \<longleftrightarrow> Ex (spp_rel sp)"

definition vec_of :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "vec_of sp = (if spp_inv sp then Eps (spp_rel sp) else 0)"

lemma spp_inv_spp_of:
  assumes "r \<noteq> 0" and "r \<in> dgrad_sig_set dgrad"
  shows "spp_inv (spp_of r)"
  unfolding spp_inv_def spp_rel_def
proof (intro exI conjI)
  show "lt r = fst (spp_of r)" by (simp add: spp_of_def)
next
  show "rep_list r = snd (spp_of r)" by (simp add: spp_of_def)
qed fact+

context
  fixes sp :: "'t \<times> ('a \<Rightarrow>\<^sub>0 'b)"
  assumes spi: "spp_inv sp"
begin

lemma sig_poly_rel_vec_of: "spp_rel sp (vec_of sp)"
proof -
  from spi have eq: "vec_of sp = Eps (spp_rel sp)" by (simp add: vec_of_def)
  from spi show ?thesis unfolding eq spp_inv_def by (rule someI_ex)
qed

lemma vec_of_nonzero: "vec_of sp \<noteq> 0"
  using sig_poly_rel_vec_of by (simp add: spp_rel_def)

lemma lt_vec_of: "lt (vec_of sp) = fst sp"
  using sig_poly_rel_vec_of by (simp add: spp_rel_def)

lemma rep_list_vec_of: "rep_list (vec_of sp) = snd sp"
  using sig_poly_rel_vec_of by (simp add: spp_rel_def)

lemma spp_of_vec_of: "spp_of (vec_of sp) = sp"
  by (simp add: spp_of_def lt_vec_of rep_list_vec_of)

end

lemma map_spp_of_vec_of:
  assumes "list_all spp_inv sps"
  shows "map (spp_of \<circ> vec_of) sps = sps"
proof (rule map_idI)
  fix sp
  assume "sp \<in> set sps"
  with assms have "spp_inv sp" by (simp add: list_all_def)
  hence "spp_of (vec_of sp) = sp" by (rule spp_of_vec_of)
  thus "(spp_of \<circ> vec_of) sp = sp" by simp
qed

lemma vec_of_dgrad_sig_set: "vec_of sp \<in> dgrad_sig_set dgrad"
proof (cases "spp_inv sp")
  case True
  hence "spp_rel sp (vec_of sp)" by (rule sig_poly_rel_vec_of)
  thus ?thesis by (simp add: spp_rel_def)
next
  case False
  moreover have "0 \<in> dgrad_sig_set dgrad" unfolding dgrad_sig_set'_def
  proof
    show "0 \<in> dgrad_max_set dgrad" by (rule dgrad_p_setI) simp
  next
    show "0 \<in> sig_inv_set" by (rule sig_inv_setI) (simp add: term_simps)
  qed
  ultimately show ?thesis by (simp add: vec_of_def)
qed

lemma spp_invD_fst:
  assumes "spp_inv sp"
  shows "dgrad (pp_of_term (fst sp)) \<le> dgrad_max dgrad" and "component_of_term (fst sp) < length fs"
proof -
  from vec_of_dgrad_sig_set have "dgrad (lp (vec_of sp)) \<le> dgrad_max dgrad" by (rule dgrad_sig_setD_lp)
  with assms show "dgrad (pp_of_term (fst sp)) \<le> dgrad_max dgrad" by (simp add: lt_vec_of)
  from vec_of_dgrad_sig_set vec_of_nonzero[OF assms] have "component_of_term (lt (vec_of sp)) < length fs"
    by (rule dgrad_sig_setD_lt)
  with assms show "component_of_term (fst sp) < length fs" by (simp add: lt_vec_of)
qed

lemma spp_invD_snd:
  assumes "dickson_grading dgrad" and "spp_inv sp"
  shows "snd sp \<in> punit_dgrad_max_set dgrad"
proof -
  from vec_of_dgrad_sig_set[of sp] have "vec_of sp \<in> dgrad_max_set dgrad" by (simp add: dgrad_sig_set'_def)
  with assms(1) have "rep_list (vec_of sp) \<in> punit_dgrad_max_set dgrad" by (rule dgrad_max_2)
  with assms(2) show ?thesis by (simp add: rep_list_vec_of)
qed

lemma vec_of_inj:
  assumes "spp_inv sp" and "vec_of sp = vec_of sp'"
  shows "sp = sp'"
proof -
  from assms(1) have "vec_of sp \<noteq> 0" by (rule vec_of_nonzero)
  hence "vec_of sp' \<noteq> 0" by (simp add: assms(2))
  hence "spp_inv sp'" by (simp add: vec_of_def split: if_split_asm)
  from assms(1) have "sp = spp_of (vec_of sp)" by (simp only: spp_of_vec_of)
  also have "... = spp_of (vec_of sp')" by (simp only: assms(2))
  also from \<open>spp_inv sp'\<close> have "... = sp'" by (rule spp_of_vec_of)
  finally show ?thesis .
qed

lemma spp_inv_alt: "spp_inv sp \<longleftrightarrow> (vec_of sp \<noteq> 0)"
proof -
  have "spp_inv sp" if "vec_of sp \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> spp_inv sp"
    hence "vec_of sp = 0" by (simp add: vec_of_def)
    with that show False ..
  qed
  thus ?thesis by (auto dest: vec_of_nonzero)
qed

lemma spp_of_vec_of_spp_of:
  assumes "p \<in> dgrad_sig_set dgrad"
  shows "spp_of (vec_of (spp_of p)) = spp_of p"
proof (cases "p = 0")
  case True
  show ?thesis
  proof (cases "spp_inv (spp_of p)")
    case True
    thus ?thesis by (rule spp_of_vec_of)
  next
    case False
    hence "vec_of (spp_of p) = 0" by (simp add: spp_inv_alt)
    thus ?thesis by (simp only: True)
  qed
next
  case False
  have "spp_inv (spp_of p)" unfolding spp_inv_def
  proof
    from False assms show "spp_rel (spp_of p) p" by (simp add: spp_rel_def spp_of_def)
  qed
  thus ?thesis by (rule spp_of_vec_of)
qed

subsubsection \<open>Total Reduction\<close>

primrec find_sig_reducer :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_sig_reducer [] _ _ _ = None"|
  "find_sig_reducer (b # bs) u t i =
          (if snd b \<noteq> 0 \<and> punit.lt (snd b) adds t \<and> (t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u then Some i
           else find_sig_reducer bs u t (Suc i))"

lemma find_sig_reducer_SomeD_aux:
  assumes "find_sig_reducer bs u t i = Some j"
  shows "i \<le> j" and "j - i < length bs"
proof -
  from assms have "i \<le> j \<and> j - i < length bs"
  proof (induct bs arbitrary: i)
    case Nil
    thus ?case by simp
  next
    case (Cons b bs)
    from Cons(2) show ?case
    proof (simp split: if_split_asm)
      assume "find_sig_reducer bs u t (Suc i) = Some j"
      hence "Suc i \<le> j \<and> j - Suc i < length bs" by (rule Cons(1))
      thus "i \<le> j \<and> j - i < Suc (length bs)" by auto
    qed
  qed
  thus "i \<le> j" and "j - i < length bs" by simp_all
qed

lemma find_sig_reducer_SomeD':
  assumes "find_sig_reducer bs u t i = Some j" and "b = bs ! (j - i)"
  shows "b \<in> set bs" and "snd b \<noteq> 0" and "punit.lt (snd b) adds t" and "(t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u"
proof -
  from assms(1) have "j - i < length bs" by (rule find_sig_reducer_SomeD_aux)
  thus "b \<in> set bs" unfolding assms(2) by (rule nth_mem)
next
  from assms have "snd b \<noteq> 0 \<and> punit.lt (snd b) adds t \<and> (t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u"
  proof (induct bs arbitrary: i)
    case Nil
    from Nil(1) show ?case by simp
  next
    case (Cons a bs)
    from Cons(2) show ?case
    proof (simp split: if_split_asm)
      assume "i = j"
      with Cons(3) have "b = a" by simp
      moreover assume "snd a \<noteq> 0" and "punit.lt (snd a) adds t" and "(t - punit.lt (snd a)) \<oplus> fst a \<prec>\<^sub>t u"
      ultimately show ?case by simp
    next
      assume *: "find_sig_reducer bs u t (Suc i) = Some j"
      hence "Suc i \<le> j" by (rule find_sig_reducer_SomeD_aux)
      note Cons(3)
      also from \<open>Suc i \<le> j\<close> have "(a # bs) ! (j - i) = bs ! (j - Suc i)" by simp
      finally have "b = bs ! (j - Suc i)" .
      with * show ?case by (rule Cons(1))
    qed
  qed
  thus "snd b \<noteq> 0" and "punit.lt (snd b) adds t" and "(t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u" by simp_all
qed

corollary find_sig_reducer_SomeD:
  assumes "find_sig_reducer (map spp_of bs) u t 0 = Some i"
  shows "i < length bs" and "rep_list (bs ! i) \<noteq> 0" and "punit.lt (rep_list (bs ! i)) adds t"
    and "(t - punit.lt (rep_list (bs ! i))) \<oplus> lt (bs ! i) \<prec>\<^sub>t u"
proof -
  from assms have "i - 0 < length (map spp_of bs)" by (rule find_sig_reducer_SomeD_aux)
  thus "i < length bs" by simp
  hence "spp_of (bs ! i) = (map spp_of bs) ! (i - 0)" by simp
  with assms have "snd (spp_of (bs ! i)) \<noteq> 0" and "punit.lt (snd (spp_of (bs ! i))) adds t"
    and "(t - punit.lt (snd (spp_of (bs ! i)))) \<oplus> fst (spp_of (bs ! i)) \<prec>\<^sub>t u"
    by (rule find_sig_reducer_SomeD')+
  thus "rep_list (bs ! i) \<noteq> 0" and "punit.lt (rep_list (bs ! i)) adds t"
    and "(t - punit.lt (rep_list (bs ! i))) \<oplus> lt (bs ! i) \<prec>\<^sub>t u" by (simp_all add: fst_spp_of snd_spp_of)
qed

lemma find_sig_reducer_NoneE:
  assumes "find_sig_reducer bs u t i = None" and "b \<in> set bs"
  assumes "snd b = 0 \<Longrightarrow> thesis" and "snd b \<noteq> 0 \<Longrightarrow> \<not> punit.lt (snd b) adds t \<Longrightarrow> thesis"
    and "snd b \<noteq> 0 \<Longrightarrow> punit.lt (snd b) adds t \<Longrightarrow> \<not> (t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct bs arbitrary: thesis i)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons a bs)
  from Cons(2) have 1: "snd a = 0 \<or> \<not> punit.lt (snd a) adds t \<or> \<not> (t - punit.lt (snd a)) \<oplus> fst a \<prec>\<^sub>t u"
    and eq: "find_sig_reducer bs u t (Suc i) = None" by (simp_all split: if_splits)
  from Cons(3) have "b = a \<or> b \<in> set bs" by simp
  thus ?case
  proof
    assume "b = a"
    show ?thesis
    proof (cases "snd a = 0")
      case True
      show ?thesis by (rule Cons(4), simp add: \<open>b = a\<close> True)
    next
      case False
      with 1 have 2: "\<not> punit.lt (snd a) adds t \<or> \<not> (t - punit.lt (snd a)) \<oplus> fst a \<prec>\<^sub>t u" by simp
      show ?thesis
      proof (cases "punit.lt (snd a) adds t")
        case True
        with 2 have 3: "\<not> (t - punit.lt (snd a)) \<oplus> fst a \<prec>\<^sub>t u" by simp
        show ?thesis by (rule Cons(6), simp_all add: \<open>b = a\<close> \<open>snd a \<noteq> 0\<close> True 3)
      next
        case False
        show ?thesis by (rule Cons(5), simp_all add: \<open>b = a\<close> \<open>snd a \<noteq> 0\<close> False)
      qed
    qed
  next
    assume "b \<in> set bs"
    with eq show ?thesis
    proof (rule Cons(1))
      assume "snd b = 0"
      thus ?thesis by (rule Cons(4))
    next
      assume "snd b \<noteq> 0" and "\<not> punit.lt (snd b) adds t"
      thus ?thesis by (rule Cons(5))
    next
      assume "snd b \<noteq> 0" and "punit.lt (snd b) adds t" and "\<not> (t - punit.lt (snd b)) \<oplus> fst b \<prec>\<^sub>t u"
      thus ?thesis by (rule Cons(6))
    qed
  qed
qed

lemma find_sig_reducer_SomeD_red_single:
  assumes "t \<in> keys (rep_list p)" and "find_sig_reducer (map spp_of bs) (lt p) t 0 = Some i"
  shows "sig_red_single (\<prec>\<^sub>t) (\<preceq>) p (p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
            (t - punit.lt (rep_list (bs ! i))) (bs ! i)) (bs ! i) (t - punit.lt (rep_list (bs ! i)))"
proof -
  from assms(2) have "punit.lt (rep_list (bs ! i)) adds t" and 1: "rep_list (bs ! i) \<noteq> 0"
    and 2: "(t - punit.lt (rep_list (bs ! i))) \<oplus> lt (bs ! i) \<prec>\<^sub>t lt p"
    by (rule find_sig_reducer_SomeD)+
  from this(1) have eq: "t - punit.lt (rep_list (bs ! i)) + punit.lt (rep_list (bs ! i)) = t"
    by (rule adds_minus)
  from assms(1) have 3: "t \<preceq> punit.lt (rep_list p)" by (rule punit.lt_max_keys)
  show ?thesis by (rule sig_red_singleI, simp_all add: eq 1 2 3 assms(1))
qed

corollary find_sig_reducer_SomeD_red:
  assumes "t \<in> keys (rep_list p)" and "find_sig_reducer (map spp_of bs) (lt p) t 0 = Some i"
  shows "sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p (p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
            (t - punit.lt (rep_list (bs ! i))) (bs ! i))"
  unfolding sig_red_def
proof (intro bexI exI, rule find_sig_reducer_SomeD_red_single)
  from assms(2) have "i - 0 < length (map spp_of bs)" by (rule find_sig_reducer_SomeD_aux)
  hence "i < length bs" by simp
  thus "bs ! i \<in> set bs" by (rule nth_mem)
qed fact+

context
  fixes bs :: "('t \<Rightarrow>\<^sub>0 'b) list"
begin

definition sig_trd_term :: "('a \<Rightarrow> nat) \<Rightarrow> (('a \<times> ('t \<Rightarrow>\<^sub>0 'b)) \<times> ('a \<times> ('t \<Rightarrow>\<^sub>0 'b))) set"
  where "sig_trd_term d = {(x, y). punit.dgrad_p_set_le d {rep_list (snd x)}
                                      (insert (rep_list (snd y)) (rep_list ` set bs)) \<and>
                                 fst x \<in> keys (rep_list (snd x)) \<and> fst y \<in> keys (rep_list (snd y)) \<and>
                                 fst x \<prec> fst y}"

lemma sig_trd_term_wf:
  assumes "dickson_grading d"
  shows "wf (sig_trd_term d)"
proof (rule wfI_min)
  fix x :: "'a \<times> ('t \<Rightarrow>\<^sub>0 'b)" and Q
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> sig_trd_term d \<longrightarrow> y \<notin> Q"
  proof (cases "fst x \<in> keys (rep_list (snd x))")
    case True
    define X where "X = rep_list ` set bs"
    let ?A = "insert (rep_list (snd x)) X"
    have "finite X" unfolding X_def by simp
    hence "finite ?A" by (simp only: finite_insert)
    then obtain m where A: "?A \<subseteq> punit.dgrad_p_set d m" by (rule punit.dgrad_p_set_exhaust)
    hence x: "rep_list (snd x) \<in> punit.dgrad_p_set d m" and X: "X \<subseteq> punit.dgrad_p_set d m"
      by simp_all
    let ?Q = "{q \<in> Q. rep_list (snd q) \<in> punit.dgrad_p_set d m \<and> fst q \<in> keys (rep_list (snd q))}"
    from \<open>x \<in> Q\<close> x True have "x \<in> ?Q" by simp
    have "\<forall>Q x. x \<in> Q \<and> Q \<subseteq> {q. d q \<le> m} \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. y \<prec> z \<longrightarrow> y \<notin> Q)"
      by (rule wfp_on_imp_minimal, rule wfp_on_ord_strict, fact assms)
    hence 1: "fst x \<in> fst ` ?Q \<Longrightarrow> fst ` ?Q \<subseteq> {q. d q \<le> m} \<Longrightarrow> (\<exists>z\<in>fst ` ?Q. \<forall>y. y \<prec> z \<longrightarrow> y \<notin> fst ` ?Q)"
      by meson
  
    have "fst x \<in> fst ` ?Q" by (rule, fact refl, fact)
    moreover have "fst ` ?Q \<subseteq> {q. d q \<le> m}"
    proof -
      {
        fix q
        assume a: "rep_list (snd q) \<in> punit.dgrad_p_set d m" and b: "fst q \<in> keys (rep_list (snd q))"
        from a have "keys (rep_list (snd q)) \<subseteq> dgrad_set d m" by (simp add: punit.dgrad_p_set_def)
        with b have "fst q \<in> dgrad_set d m" ..
        hence "d (fst q) \<le> m" by (simp add: dgrad_set_def)
      }
      thus ?thesis by auto
    qed
    ultimately have "\<exists>z\<in>fst ` ?Q. \<forall>y. y \<prec> z \<longrightarrow> y \<notin> fst ` ?Q" by (rule 1)
    then obtain z0 where "z0 \<in> fst ` ?Q" and 2: "\<And>y. y \<prec> z0 \<Longrightarrow> y \<notin> fst ` ?Q" by blast
    from this(1) obtain z where "z \<in> ?Q" and z0: "z0 = fst z" ..
    hence "z \<in> Q" and z: "rep_list (snd z) \<in> punit.dgrad_p_set d m" by simp_all
    from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> sig_trd_term d \<longrightarrow> y \<notin> Q"
    proof
      show "\<forall>y. (y, z) \<in> sig_trd_term d \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y
        assume "(y, z) \<in> sig_trd_term d"
        hence 3: "punit.dgrad_p_set_le d {rep_list (snd y)} (insert (rep_list (snd z)) X)"
          and 4: "fst y \<in> keys (rep_list (snd y))" and "fst y \<prec> z0"
          by (simp_all add: sig_trd_term_def X_def z0)
        from this(3) have "fst y \<notin> fst ` ?Q" by (rule 2)
        hence "y \<notin> Q \<or> rep_list (snd y) \<notin> punit.dgrad_p_set d m \<or> fst y \<notin> keys (rep_list (snd y))"
          by auto
        thus "y \<notin> Q"
        proof (elim disjE)
          assume 5: "rep_list (snd y) \<notin> punit.dgrad_p_set d m"
          from z X have "insert (rep_list (snd z)) X \<subseteq> punit.dgrad_p_set d m" by simp
          with 3 have "{rep_list (snd y)} \<subseteq> punit.dgrad_p_set d m" by (rule punit.dgrad_p_set_le_dgrad_p_set)
          hence "rep_list (snd y) \<in> punit.dgrad_p_set d m" by simp
          with 5 show ?thesis ..
        next
          assume "fst y \<notin> keys (rep_list (snd y))"
          thus ?thesis using 4 ..
        qed
      qed
    qed
  next
    case False
    from \<open>x \<in> Q\<close> show ?thesis
    proof
      show "\<forall>y. (y, x) \<in> sig_trd_term d \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y
        assume "(y, x) \<in> sig_trd_term d"
        hence "fst x \<in> keys (rep_list (snd x))" by (simp add: sig_trd_term_def)
        with False show "y \<notin> Q" ..
      qed
    qed
  qed
qed

function (domintros) sig_trd_aux :: "('a \<times> ('t \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)" where
  "sig_trd_aux (t, p) =
    (let p' =
      (case find_sig_reducer (map spp_of bs) (lt p) t 0 of
          None   \<Rightarrow> p
        | Some i \<Rightarrow> p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                          (t - punit.lt (rep_list (bs ! i))) (bs ! i));
      p'' = punit.lower (rep_list p') t in
    if p'' = 0 then p' else sig_trd_aux (punit.lt p'', p'))"
  by auto

lemma sig_trd_aux_domI:
  assumes "fst args0 \<in> keys (rep_list (snd args0))"
  shows "sig_trd_aux_dom args0"
proof -
  from ex_hgrad obtain d::"'a \<Rightarrow> nat" where "dickson_grading d \<and> hom_grading d" ..
  hence dg: "dickson_grading d" ..
  hence "wf (sig_trd_term d)" by (rule sig_trd_term_wf)
  thus ?thesis using assms
  proof (induct args0)
    case (less args)
    obtain t p where args: "args = (t, p)" using prod.exhaust by blast
    with less(1) have 1: "\<And>s q. ((s, q), (t, p)) \<in> sig_trd_term d \<Longrightarrow> s \<in> keys (rep_list q) \<Longrightarrow> sig_trd_aux_dom (s, q)"
      using prod.exhaust by auto
    from less(2) have "t \<in> keys (rep_list p)" by (simp add: args)
    show ?case unfolding args
    proof (rule sig_trd_aux.domintros)
      define p' where "p' = (case find_sig_reducer (map spp_of bs) (lt p) t 0 of
                                None \<Rightarrow> p
                              | Some i \<Rightarrow> p -
                                  monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                   (t - punit.lt (rep_list (bs ! i))) (bs ! i))"
      define p'' where "p'' = punit.lower (rep_list p') t"
      assume "p'' \<noteq> 0"
      from \<open>p'' \<noteq> 0\<close> have "punit.lt p'' \<in> keys p''" by (rule punit.lt_in_keys)
      also have "... \<subseteq> keys (rep_list p')" by (auto simp: p''_def punit.keys_lower)
      finally have "punit.lt p'' \<in> keys (rep_list p')" .
      with _ show "sig_trd_aux_dom (punit.lt p'', p')"
      proof (rule 1)
        have "punit.dgrad_p_set_le d {rep_list p'} (insert (rep_list p) (rep_list ` set bs))"
        proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
          case None
          hence "p' = p" by (simp add: p'_def)
          hence "{rep_list p'} \<subseteq> insert (rep_list p) (rep_list ` set bs)" by simp
          thus ?thesis by (rule punit.dgrad_p_set_le_subset)
        next
          case (Some i)
          hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                    (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
          have "sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p p'" unfolding p' using \<open>t \<in> keys (rep_list p)\<close> Some
            by (rule find_sig_reducer_SomeD_red)
          hence "punit.red (rep_list ` set bs) (rep_list p) (rep_list p')" by (rule sig_red_red)
          with dg show ?thesis by (rule punit.dgrad_p_set_le_red)
        qed
        moreover note \<open>punit.lt p'' \<in> keys (rep_list p')\<close> \<open>t \<in> keys (rep_list p)\<close>
        moreover from \<open>p'' \<noteq> 0\<close> have "punit.lt p'' \<prec> t" unfolding p''_def by (rule punit.lt_lower_less)
        ultimately show "((punit.lt p'', p'), t, p) \<in> sig_trd_term d" by (simp add: sig_trd_term_def)
      qed
    qed
  qed
qed

definition sig_trd :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "sig_trd p = (if rep_list p = 0 then p else sig_trd_aux (punit.lt (rep_list p), p))"

lemma sig_trd_aux_red_rtrancl:
  assumes "fst args0 \<in> keys (rep_list (snd args0))"
  shows "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (snd args0) (sig_trd_aux args0)"
proof -
  from assms have "sig_trd_aux_dom args0" by (rule sig_trd_aux_domI)
  thus ?thesis using assms
  proof (induct args0 rule: sig_trd_aux.pinduct)
    case (1 t p)
    define p' where "p' = (case find_sig_reducer (map spp_of bs) (lt p) t 0 of
                              None \<Rightarrow> p
                            | Some i \<Rightarrow> p -
                                monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                 (t - punit.lt (rep_list (bs ! i))) (bs ! i))"
    define p'' where "p'' = punit.lower (rep_list p') t"
    from 1(3) have "t \<in> keys (rep_list p)" by simp
    have *: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* p p'"
    proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
      case None
      hence "p' = p" by (simp add: p'_def)
      thus ?thesis by simp
    next
      case (Some i)
      hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                  (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
      have "sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p p'" unfolding p' using \<open>t \<in> keys (rep_list p)\<close> Some
        by (rule find_sig_reducer_SomeD_red)
      thus ?thesis ..
    qed
    show ?case
    proof (simp add: sig_trd_aux.psimps[OF 1(1)] Let_def p'_def[symmetric] p''_def[symmetric] *, intro impI)
      assume "p'' \<noteq> 0"
      from * have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* p (snd (punit.lt p'', p'))" by (simp only: snd_conv)
      moreover have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (snd (punit.lt p'', p')) (sig_trd_aux (punit.lt p'', p'))"
        using p'_def p''_def \<open>p'' \<noteq> 0\<close>
      proof (rule 1(2))
        from \<open>p'' \<noteq> 0\<close> have "punit.lt p'' \<in> keys p''" by (rule punit.lt_in_keys)
        also have "... \<subseteq> keys (rep_list p')" by (auto simp: p''_def punit.keys_lower)
        finally show "fst (punit.lt p'', p') \<in> keys (rep_list (snd (punit.lt p'', p')))" by simp
      qed
      ultimately show "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* p (sig_trd_aux (punit.lt p'', p'))"
        by (rule rtranclp_trans)
    qed
  qed
qed

corollary sig_trd_red_rtrancl: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* p (sig_trd p)"
  unfolding sig_trd_def
proof (split if_split, intro conjI impI rtranclp.rtrancl_refl)
  let ?args = "(punit.lt (rep_list p), p)"
  assume "rep_list p \<noteq> 0"
  hence "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
  hence "fst (punit.lt (rep_list p), p) \<in> keys (rep_list (snd (punit.lt (rep_list p), p)))"
    by (simp only: fst_conv snd_conv)
  hence "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (snd ?args) (sig_trd_aux ?args)" by (rule sig_trd_aux_red_rtrancl)
  thus "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* p (sig_trd_aux (punit.lt (rep_list p), p))" by (simp only: snd_conv)
qed

lemma sig_trd_aux_irred:
  assumes "fst args0 \<in> keys (rep_list (snd args0))"
    and "\<And>b s. b \<in> set bs \<Longrightarrow> rep_list b \<noteq> 0 \<Longrightarrow> fst args0 \<prec> s + punit.lt (rep_list b) \<Longrightarrow>
              s \<oplus> lt b \<prec>\<^sub>t lt (snd (args0)) \<Longrightarrow> lookup (rep_list (snd args0)) (s + punit.lt (rep_list b)) = 0"
  shows "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) (sig_trd_aux args0)"
proof -
  from assms(1) have "sig_trd_aux_dom args0" by (rule sig_trd_aux_domI)
  thus ?thesis using assms
  proof (induct args0 rule: sig_trd_aux.pinduct)
    case (1 t p)
    define p' where "p' = (case find_sig_reducer (map spp_of bs) (lt p) t 0 of
                              None \<Rightarrow> p
                            | Some i \<Rightarrow> p -
                                monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                 (t - punit.lt (rep_list (bs ! i))) (bs ! i))"
    define p'' where "p'' = punit.lower (rep_list p') t"
    from 1(3) have "t \<in> keys (rep_list p)" by simp
    from 1(4) have a: "b \<in> set bs \<Longrightarrow> rep_list b \<noteq> 0 \<Longrightarrow> t \<prec> s + punit.lt (rep_list b) \<Longrightarrow>
                       s \<oplus> lt b \<prec>\<^sub>t lt p \<Longrightarrow> lookup (rep_list p) (s + punit.lt (rep_list b)) = 0"
      for b s by (simp only: fst_conv snd_conv)
    have "lt p' = lt p \<and> (\<forall>s. t \<prec> s \<longrightarrow> lookup (rep_list p') s = lookup (rep_list p) s)"
    proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
      case None
      thus ?thesis by (simp add: p'_def)
    next
      case (Some i)
      hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                  (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
      have "sig_red_single (\<prec>\<^sub>t) (\<preceq>) p p' (bs ! i) (t - punit.lt (rep_list (bs ! i)))"
        unfolding p' using \<open>t \<in> keys (rep_list p)\<close> Some by (rule find_sig_reducer_SomeD_red_single)
      hence r: "punit.red_single (rep_list p) (rep_list p') (rep_list (bs ! i)) (t - punit.lt (rep_list (bs ! i)))"
        and "lt p' = lt p" by (rule sig_red_single_red_single, rule sig_red_single_regular_lt)
      have "\<forall>s. t \<prec> s \<longrightarrow> lookup (rep_list p') s = lookup (rep_list p) s"
      proof (intro allI impI)
        fix s
        assume "t \<prec> s"
        from Some have "punit.lt (rep_list (bs ! i)) adds t" by (rule find_sig_reducer_SomeD)
        hence eq0: "(t - punit.lt (rep_list (bs ! i))) + punit.lt (rep_list (bs ! i)) = t" (is "?t = t")
          by (rule adds_minus)
        from \<open>t \<prec> s\<close> have "lookup (rep_list p') s = lookup (punit.higher (rep_list p') ?t) s"
          by (simp add: eq0 punit.lookup_higher_when)
        also from r have "... = lookup (punit.higher (rep_list p) ?t) s"
          by (simp add: punit.red_single_higher[simplified])
        also from \<open>t \<prec> s\<close> have "... = lookup (rep_list p) s" by (simp add: eq0 punit.lookup_higher_when)
        finally show "lookup (rep_list p') s = lookup (rep_list p) s" .
      qed
      with \<open>lt p' = lt p\<close> show ?thesis ..
    qed
    hence lt_p': "lt p' = lt p" and b: "\<And>s. t \<prec> s \<Longrightarrow> lookup (rep_list p') s = lookup (rep_list p) s"
      by blast+
    have c: "lookup (rep_list p') (s + punit.lt (rep_list b)) = 0"
      if "b \<in> set bs" and "rep_list b \<noteq> 0" and "t \<preceq> s + punit.lt (rep_list b)" and "s \<oplus> lt b \<prec>\<^sub>t lt p'" for b s
    proof (cases "t \<prec> s + punit.lt (rep_list b)")
      case True
      hence "lookup (rep_list p') (s + punit.lt (rep_list b)) =
             lookup (rep_list p) (s + punit.lt (rep_list b))" by (rule b)
      also from that(1, 2) True that(4) have "... = 0" unfolding lt_p' by (rule a)
      finally show ?thesis .
    next
      case False
      with that(3) have t: "t = s + punit.lt (rep_list b)" by simp
      show ?thesis
      proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
        case None
        from that(1) have "spp_of b \<in> set (map spp_of bs)" by fastforce
        with None show ?thesis
        proof (rule find_sig_reducer_NoneE)
          assume "snd (spp_of b) = 0"
          with that(2) show ?thesis by (simp add: snd_spp_of)
        next
          assume "\<not> punit.lt (snd (spp_of b)) adds t"
          thus ?thesis by (simp add: snd_spp_of t)
        next
          assume "\<not> (t - punit.lt (snd (spp_of b))) \<oplus> fst (spp_of b) \<prec>\<^sub>t lt p"
          with that(4) show ?thesis by (simp add: fst_spp_of snd_spp_of t lt_p')
        qed
      next
        case (Some i)
        hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                  (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
        have "sig_red_single (\<prec>\<^sub>t) (\<preceq>) p p' (bs ! i) (t - punit.lt (rep_list (bs ! i)))"
          unfolding p' using \<open>t \<in> keys (rep_list p)\<close> Some by (rule find_sig_reducer_SomeD_red_single)
        hence r: "punit.red_single (rep_list p) (rep_list p') (rep_list (bs ! i)) (t - punit.lt (rep_list (bs ! i)))"
          by (rule sig_red_single_red_single)
        from Some have "punit.lt (rep_list (bs ! i)) adds t" by (rule find_sig_reducer_SomeD)
        hence eq0: "(t - punit.lt (rep_list (bs ! i))) + punit.lt (rep_list (bs ! i)) = t" (is "?t = t")
          by (rule adds_minus)
        from r have "lookup (rep_list p') ((t - punit.lt (rep_list (bs ! i))) + punit.lt (rep_list (bs ! i))) = 0"
          by (rule punit.red_single_lookup[simplified])
        thus ?thesis by (simp only: eq0 t[symmetric])
      qed
    qed
    show ?case
    proof (simp add: sig_trd_aux.psimps[OF 1(1)] Let_def p'_def[symmetric] p''_def[symmetric], intro conjI impI)
      assume "p'' = 0"
      show "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p'"
      proof
        assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p'"
        then obtain b s where "b \<in> set bs" and "s \<in> keys (rep_list p')" and "rep_list b \<noteq> 0"
          and adds: "punit.lt (rep_list b) adds s" and "s \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt p'"
          by (rule is_sig_red_addsE)
        let ?s = "s - punit.lt (rep_list b)"
        from adds have eq0: "?s + punit.lt (rep_list b) = s" by (simp add: adds_minus)
        show False
        proof (cases "t \<preceq> s")
          case True
          note \<open>b \<in> set bs\<close> \<open>rep_list b \<noteq> 0\<close>
          moreover from True have "t \<preceq> ?s + punit.lt (rep_list b)" by (simp only: eq0)
          moreover from adds \<open>s \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt p'\<close> have "?s \<oplus> lt b \<prec>\<^sub>t lt p'"
            by (simp add: term_is_le_rel_minus)
          ultimately have "lookup (rep_list p') (?s + punit.lt (rep_list b)) = 0" by (rule c)
          hence "s \<notin> keys (rep_list p')" by (simp add: eq0 in_keys_iff)
          thus ?thesis using \<open>s \<in> keys (rep_list p')\<close> ..
        next
          case False
          hence "s \<prec> t" by simp
          hence "lookup (rep_list p') s = lookup (punit.lower (rep_list p') t) s"
            by (simp add: punit.lookup_lower_when)
          also from \<open>p'' = 0\<close> have "... = 0" by (simp add: p''_def)
          finally have "s \<notin> keys (rep_list p')" by (simp add: in_keys_iff)
          thus ?thesis using \<open>s \<in> keys (rep_list p')\<close> ..
        qed
      qed
    next
      assume "p'' \<noteq> 0"
      with p'_def p''_def show "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) (sig_trd_aux (punit.lt p'', p'))"
      proof (rule 1(2))
        from \<open>p'' \<noteq> 0\<close> have "punit.lt p'' \<in> keys p''" by (rule punit.lt_in_keys)
        also have "... \<subseteq> keys (rep_list p')" by (auto simp: p''_def punit.keys_lower)
        finally show "fst (punit.lt p'', p') \<in> keys (rep_list (snd (punit.lt p'', p')))" by simp
      next
        fix b s
        assume "b \<in> set bs" and "rep_list b \<noteq> 0"
        assume "fst (punit.lt p'', p') \<prec> s + punit.lt (rep_list b)"
          and "s \<oplus> lt b \<prec>\<^sub>t lt (snd (punit.lt p'', p'))"
        hence "punit.lt p'' \<prec> s + punit.lt (rep_list b)" and "s \<oplus> lt b \<prec>\<^sub>t lt p'" by simp_all
        have "lookup (rep_list p') (s + punit.lt (rep_list b)) = 0"
        proof (cases "t \<preceq> s + punit.lt (rep_list b)")
          case True
          with \<open>b \<in> set bs\<close> \<open>rep_list b \<noteq> 0\<close> show ?thesis using \<open>s \<oplus> lt b \<prec>\<^sub>t lt p'\<close> by (rule c)
        next
          case False
          hence "s + punit.lt (rep_list b) \<prec> t" by simp
          hence "lookup (rep_list p') (s + punit.lt (rep_list b)) =
                  lookup (punit.lower (rep_list p') t) (s + punit.lt (rep_list b))"
            by (simp add: punit.lookup_lower_when)
          also have "... = 0"
          proof (rule ccontr)
            assume "lookup (punit.lower (rep_list p') t) (s + punit.lt (rep_list b)) \<noteq> 0"
            hence "s + punit.lt (rep_list b) \<preceq> punit.lt (punit.lower (rep_list p') t)"
              by (rule punit.lt_max)
            also have "... = punit.lt p''" by (simp only: p''_def)
            finally show False using \<open>punit.lt p'' \<prec> s + punit.lt (rep_list b)\<close> by simp
          qed
          finally show ?thesis .
        qed
        thus "lookup (rep_list (snd (punit.lt p'', p'))) (s + punit.lt (rep_list b)) = 0"
          by (simp only: snd_conv)
      qed
    qed
  qed
qed

corollary sig_trd_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) (sig_trd p)"
  unfolding sig_trd_def
proof (split if_split, intro conjI impI)
  assume "rep_list p = 0"
  show "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p"
    then obtain t where "t \<in> keys (rep_list p)" by (rule is_sig_red_addsE)
    thus False by (simp add: \<open>rep_list p = 0\<close>)
  qed
next
  assume "rep_list p \<noteq> 0"
  show "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) (sig_trd_aux (punit.lt (rep_list p), p))"
  proof (rule sig_trd_aux_irred)
    from \<open>rep_list p \<noteq> 0\<close> have "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
    thus "fst (punit.lt (rep_list p), p) \<in> keys (rep_list (snd (punit.lt (rep_list p), p)))" by simp
  next
    fix b s
    assume "fst (punit.lt (rep_list p), p) \<prec> s + punit.lt (rep_list b)"
    thus "lookup (rep_list (snd (punit.lt (rep_list p), p))) (s + punit.lt (rep_list b)) = 0"
      using punit.lt_max by force
  qed
qed

end

context
  fixes bs :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list"
begin

context
  fixes v :: 't
begin

fun sig_trd_spp_body :: "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b))" where
  "sig_trd_spp_body (p, r) =
    (case find_sig_reducer bs v (punit.lt p) 0 of
        None   \<Rightarrow> (punit.tail p, r + monomial (punit.lc p) (punit.lt p))
      | Some i \<Rightarrow> let b = snd (bs ! i) in
          (punit.tail p - punit.monom_mult (punit.lc p / punit.lc b) (punit.lt p - punit.lt b) (punit.tail b), r))"

definition sig_trd_spp_aux :: "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where sig_trd_spp_aux_def [code del]: "sig_trd_spp_aux = tailrec.fun (\<lambda>x. fst x = 0) snd sig_trd_spp_body"

lemma sig_trd_spp_aux_simps [code]:
  "sig_trd_spp_aux (p, r) = (if p = 0 then r else sig_trd_spp_aux (sig_trd_spp_body (p, r)))"
  by (simp add: sig_trd_spp_aux_def tailrec.simps)

end

fun sig_trd_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))" where
  "sig_trd_spp (v, p) = (v, sig_trd_spp_aux v (p, 0))"

text \<open>We define function @{const sig_trd_spp}, operating on sig-poly-pairs, already here, to have
  its definition in the right context. Lemmas are proved about it below in Section \<open>Sig-Poly-Pairs\<close>.\<close>

end

subsubsection \<open>Koszul Syzygies\<close>

text \<open>A @{emph \<open>Koszul syzygy\<close>} of the list @{term fs} of scalar polynomials is a syzygy of the form
  @{term "(fs ! i) \<odot> (monomial 1 (term_of_pair (0, j))) - (fs ! j) \<odot> (monomial 1 (term_of_pair (0, i)))"},
  for @{prop "i < j"} and @{prop "j < length fs"}.\<close>

primrec Koszul_syz_sigs_aux :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> nat \<Rightarrow> 't list" where
  "Koszul_syz_sigs_aux [] i = []" |
  "Koszul_syz_sigs_aux (b # bs) i =
    map_idx (\<lambda>b' j. ord_term_lin.max (term_of_pair (punit.lt b, j)) (term_of_pair (punit.lt b', i))) bs (Suc i) @
    Koszul_syz_sigs_aux bs (Suc i)"

definition Koszul_syz_sigs :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 't list"
  where "Koszul_syz_sigs bs = filter_min (adds\<^sub>t) (Koszul_syz_sigs_aux bs 0)"

fun new_syz_sigs :: "'t list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat \<Rightarrow> 't list"
  where
    "new_syz_sigs ss bs (Inl (a, b)) = ss" |
    "new_syz_sigs ss bs (Inr j) =
      (if is_pot_ord then
        filter_min_append (adds\<^sub>t) ss (filter_min (adds\<^sub>t) (map (\<lambda>b. term_of_pair (punit.lt (rep_list b), j)) bs))
      else ss)"

fun new_syz_sigs_spp :: "'t list \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat \<Rightarrow> 't list"
  where
    "new_syz_sigs_spp ss bs (Inl (a, b)) = ss" |
    "new_syz_sigs_spp ss bs (Inr j) =
      (if is_pot_ord then
        filter_min_append (adds\<^sub>t) ss (filter_min (adds\<^sub>t) (map (\<lambda>b. term_of_pair (punit.lt (snd b), j)) bs))
      else ss)"

lemma Koszul_syz_sigs_auxI:
  assumes "i < j" and "j < length bs"
  shows "ord_term_lin.max (term_of_pair (punit.lt (bs ! i), k + j)) (term_of_pair (punit.lt (bs ! j), k + i)) \<in>
          set (Koszul_syz_sigs_aux bs k)"
  using assms
proof (induct bs arbitrary: i j k)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons b bs)
  from Cons(2) obtain j0 where j: "j = Suc j0" by (meson lessE)
  from Cons(3) have "j0 < length bs" by (simp add: j)
  let ?A = "(\<lambda>j. ord_term_lin.max (term_of_pair (punit.lt b, Suc (j + k))) (term_of_pair (punit.lt (bs ! j), k))) `
                {0..<length bs}"
  let ?B = "set (Koszul_syz_sigs_aux bs (Suc k))"
  show ?case
  proof (cases i)
    case 0
    from \<open>j0 < length bs\<close> have "j0 \<in> {0..<length bs}" by simp
    hence "ord_term_lin.max (term_of_pair (punit.lt b, Suc (j0 + k)))
                (term_of_pair (punit.lt (bs ! j0), k)) \<in> ?A" by (rule imageI)
    thus ?thesis by (simp add: \<open>i = 0\<close> j set_map_idx ac_simps)
  next
    case (Suc i0)
    from Cons(2) have "i0 < j0" by (simp add: \<open>i = Suc i0\<close> j)
    hence "ord_term_lin.max (term_of_pair (punit.lt (bs ! i0), Suc k + j0))
              (term_of_pair (punit.lt (bs ! j0), Suc k + i0)) \<in> ?B"
      using \<open>j0 < length bs\<close> by (rule Cons(1))
    thus ?thesis by (simp add: \<open>i = Suc i0\<close> j set_map_idx ac_simps)
  qed
qed

lemma Koszul_syz_sigs_auxE:
  assumes "v \<in> set (Koszul_syz_sigs_aux bs k)"
  obtains i j where "i < j" and "j < length bs"
    and "v = ord_term_lin.max (term_of_pair (punit.lt (bs ! i), k + j)) (term_of_pair (punit.lt (bs ! j), k + i))"
  using assms
proof (induct bs arbitrary: k thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons b bs)
  have "v \<in> (\<lambda>j. ord_term_lin.max (term_of_pair (punit.lt b, Suc (j + k))) (term_of_pair (punit.lt (bs ! j), k))) `
                {0..<length bs} \<union> set (Koszul_syz_sigs_aux bs (Suc k))" (is "v \<in> ?A \<union> ?B")
    using Cons(3) by (simp add: set_map_idx)
  thus ?case
  proof
    assume "v \<in> ?A"
    then obtain j where "j \<in> {0..<length bs}"
      and v: "v = ord_term_lin.max (term_of_pair (punit.lt b, Suc (j + k)))
                                    (term_of_pair (punit.lt (bs ! j), k))" ..
    from this(1) have "j < length bs" by simp
    show ?thesis
    proof (rule Cons(2))
      show "0 < Suc j" by simp
    next
      from \<open>j < length bs\<close> show "Suc j < length (b # bs)" by simp
    next
      show "v = ord_term_lin.max (term_of_pair (punit.lt ((b # bs) ! 0), k + Suc j))
                                  (term_of_pair (punit.lt ((b # bs) ! Suc j), k + 0))"
        by (simp add: v ac_simps)
    qed
  next
    assume "v \<in> ?B"
    obtain i j where "i < j" and "j < length bs"
      and v: "v = ord_term_lin.max (term_of_pair (punit.lt (bs ! i), Suc k + j))
                                    (term_of_pair (punit.lt (bs ! j), Suc k + i))"
      by (rule Cons(1), assumption, rule \<open>v \<in> ?B\<close>)
    show ?thesis
    proof (rule Cons(2))
      from \<open>i < j\<close> show "Suc i < Suc j" by simp
    next
      from \<open>j < length bs\<close> show "Suc j < length (b # bs)" by simp
    next
      show "v = ord_term_lin.max (term_of_pair (punit.lt ((b # bs) ! Suc i), k + Suc j))
                                  (term_of_pair (punit.lt ((b # bs) ! Suc j), k + Suc i))"
        by (simp add: v)
    qed
  qed
qed

lemma lt_Koszul_syz_comp:
  assumes "0 \<notin> set fs" and "i < length fs"
  shows "lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j))) = term_of_pair (punit.lt (fs ! i), j)"
proof -
  from assms(2) have "fs ! i \<in> set fs" by (rule nth_mem)
  with assms(1) have "fs ! i \<noteq> 0" by auto
  thus ?thesis by (simp add: lt_mult_scalar_monomial_right splus_def term_simps)
qed

lemma Koszul_syz_nonzero_lt:
  assumes "rep_list a \<noteq> 0" and "rep_list b \<noteq> 0" and "component_of_term (lt a) < component_of_term (lt b)"
  shows "rep_list a \<odot> b - rep_list b \<odot> a \<noteq> 0" (is "?p - ?q \<noteq> 0")
    and "lt (rep_list a \<odot> b - rep_list b \<odot> a) =
          ord_term_lin.max (punit.lt (rep_list a) \<oplus> lt b) (punit.lt (rep_list b) \<oplus> lt a)" (is "_ = ?r")
proof -
  from assms(2) have "b \<noteq> 0" by (auto simp: rep_list_zero)
  with assms(1) have lt_p: "lt ?p = punit.lt (rep_list a) \<oplus> lt b" by (rule lt_mult_scalar)
  from assms(1) have "a \<noteq> 0" by (auto simp: rep_list_zero)
  with assms(2) have lt_q: "lt ?q = punit.lt (rep_list b) \<oplus> lt a" by (rule lt_mult_scalar)
  from assms(3) have "component_of_term (lt ?p) \<noteq> component_of_term (lt ?q)"
    by (simp add: lt_p lt_q component_of_term_splus)
  hence "lt ?p \<noteq> lt ?q" by auto
  hence "lt (?p - ?q) = ord_term_lin.max (lt ?p) (lt ?q)" by (rule lt_minus_distinct_eq_max)
  also have "... = ?r" by (simp only: lt_p lt_q)
  finally show "lt (?p - ?q) = ?r" .
  
  from \<open>lt ?p \<noteq> lt ?q\<close> show "?p - ?q \<noteq> 0" by auto
qed

lemma Koszul_syz_is_syz: "rep_list (rep_list a \<odot> b - rep_list b \<odot> a) = 0"
  by (simp add: rep_list_minus rep_list_mult_scalar)

lemma dgrad_sig_set_closed_Koszul_syz:
  assumes "dickson_grading dgrad" and "a \<in> dgrad_sig_set dgrad" and "b \<in> dgrad_sig_set dgrad"
  shows "rep_list a \<odot> b - rep_list b \<odot> a \<in> dgrad_sig_set dgrad"
proof -
  from assms(2, 3) have 1: "a \<in> dgrad_max_set dgrad" and 2: "b \<in> dgrad_max_set dgrad"
    by (simp_all add: dgrad_sig_set'_def)
  show ?thesis
    by (intro dgrad_sig_set_closed_minus dgrad_sig_set_closed_mult_scalar dgrad_max_2 assms 1 2)
qed

corollary Koszul_syz_is_syz_sig:
  assumes "dickson_grading dgrad" and "a \<in> dgrad_sig_set dgrad" and "b \<in> dgrad_sig_set dgrad"
    and "rep_list a \<noteq> 0" and "rep_list b \<noteq> 0" and "component_of_term (lt a) < component_of_term (lt b)"
  shows "is_syz_sig dgrad (ord_term_lin.max (punit.lt (rep_list a) \<oplus> lt b) (punit.lt (rep_list b) \<oplus> lt a))"
proof (rule is_syz_sigI)
  from assms(4-6) show "rep_list a \<odot> b - rep_list b \<odot> a \<noteq> 0"
    and "lt (rep_list a \<odot> b - rep_list b \<odot> a) =
          ord_term_lin.max (punit.lt (rep_list a) \<oplus> lt b) (punit.lt (rep_list b) \<oplus> lt a)"
    by (rule Koszul_syz_nonzero_lt)+
next
  from assms(1-3) show "rep_list a \<odot> b - rep_list b \<odot> a \<in> dgrad_sig_set dgrad"
    by (rule dgrad_sig_set_closed_Koszul_syz)
qed (fact Koszul_syz_is_syz)

corollary lt_Koszul_syz_in_Koszul_syz_sigs_aux:
  assumes "distinct fs" and "0 \<notin> set fs" and "i < j" and "j < length fs"
  shows "lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i))) \<in>
          set (Koszul_syz_sigs_aux fs 0)" (is "?l \<in> ?K")
proof -
  let ?a = "monomial (1::'b) (term_of_pair (0, i))"
  let ?b = "monomial (1::'b) (term_of_pair (0, j))"
  from assms(3, 4) have "i < length fs" by simp
  with assms(1) have a: "rep_list ?a = fs ! i" by (simp add: rep_list_monomial term_simps)
  from assms(1, 4) have b: "rep_list ?b = fs ! j" by (simp add: rep_list_monomial term_simps)
  have "?l = lt (rep_list ?a \<odot> ?b - rep_list ?b \<odot> ?a)" by (simp only: a b)
  also have "... = ord_term_lin.max (punit.lt (rep_list ?a) \<oplus> lt ?b) (punit.lt (rep_list ?b) \<oplus> lt ?a)"
  proof (rule Koszul_syz_nonzero_lt)
    from \<open>i < length fs\<close> have "fs ! i \<in> set fs" by (rule nth_mem)
    with assms(2) show "rep_list ?a \<noteq> 0" by (auto simp: a)
  next
    from assms(4) have "fs ! j \<in> set fs" by (rule nth_mem)
    with assms(2) show "rep_list ?b \<noteq> 0" by (auto simp: b)
  next
    from assms(3) show "component_of_term (lt ?a) < component_of_term (lt ?b)"
      by (simp add: lt_monomial component_of_term_of_pair)
  qed
  also have "... = ord_term_lin.max (term_of_pair (punit.lt (fs ! i), 0 + j)) (term_of_pair (punit.lt (fs ! j), 0 + i))"
    by (simp add: a b lt_monomial splus_def term_simps)
  also from assms(3, 4) have "... \<in> ?K" by (rule Koszul_syz_sigs_auxI)
  thm Koszul_syz_sigs_auxI[OF assms(3, 4)]
  finally show ?thesis .
qed

corollary lt_Koszul_syz_in_Koszul_syz_sigs:
  assumes "\<not> is_pot_ord" and "distinct fs" and "0 \<notin> set fs" and "i < j" and "j < length fs"
  obtains v where "v \<in> set (Koszul_syz_sigs fs)"
    and "v adds\<^sub>t lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i)))"
proof -
  have "transp (adds\<^sub>t)" by (rule transpI, drule adds_term_trans)
  moreover have "lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i))) \<in>
                  set (Koszul_syz_sigs_aux fs 0)" (is "?l \<in> set ?ks")
    using assms(2-5) by (rule lt_Koszul_syz_in_Koszul_syz_sigs_aux)
  ultimately show ?thesis
  proof (rule filter_min_cases)
    assume "?l \<in> set (filter_min (adds\<^sub>t) ?ks)"
    hence "?l \<in> set (Koszul_syz_sigs fs)" by (simp add: Koszul_syz_sigs_def assms(1))
    thus ?thesis using adds_term_refl ..
  next
    fix v
    assume "v \<in> set (filter_min (adds\<^sub>t) ?ks)"
    hence "v \<in> set (Koszul_syz_sigs fs)" by (simp add: Koszul_syz_sigs_def assms(1))
    moreover assume "v adds\<^sub>t ?l"
    ultimately show ?thesis ..
  qed
qed

lemma lt_Koszul_syz_init:
  assumes "0 \<notin> set fs" and "i < j" and "j < length fs"
  shows "lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i))) =
          ord_term_lin.max (term_of_pair (punit.lt (fs ! i), j)) (term_of_pair (punit.lt (fs ! j), i))"
            (is "lt (?p - ?q) = ?r")
proof -
  from assms(2, 3) have "i < length fs" by simp
  with assms(1) have lt_i: "lt ?p = term_of_pair (punit.lt (fs ! i), j)" by (rule lt_Koszul_syz_comp)
  from assms(1, 3) have lt_j: "lt ?q = term_of_pair (punit.lt (fs ! j), i)" by (rule lt_Koszul_syz_comp)
  from assms(2) have "component_of_term (lt ?p) \<noteq> component_of_term (lt ?q)"
    by (simp add: lt_i lt_j component_of_term_of_pair)
  hence "lt ?p \<noteq> lt ?q" by auto
  hence "lt (?p - ?q) = ord_term_lin.max (lt ?p) (lt ?q)" by (rule lt_minus_distinct_eq_max)
  also have "... = ?r" by (simp only: lt_i lt_j)
  finally show ?thesis .
qed

corollary Koszul_syz_sigs_auxE_lt_Koszul_syz:
  assumes "0 \<notin> set fs" and "v \<in> set (Koszul_syz_sigs_aux fs 0)"
  obtains i j where "i < j" and "j < length fs"
    and "v = lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i)))"
proof -
  from assms(2) obtain i j where "i < j" and "j < length fs"
    and "v = ord_term_lin.max (term_of_pair (punit.lt (fs ! i), 0 + j))
                        (term_of_pair (punit.lt (fs ! j), 0 + i))"
    by (rule Koszul_syz_sigs_auxE)
  with assms(1) have "v = lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) -
                                (fs ! j) \<odot> monomial 1 (term_of_pair (0, i)))"
    by (simp add: lt_Koszul_syz_init)
  with \<open>i < j\<close> \<open>j < length fs\<close> show ?thesis ..
qed

corollary Koszul_syz_sigs_is_syz_sig:
  assumes "dickson_grading dgrad" and "distinct fs" and "0 \<notin> set fs" and "v \<in> set (Koszul_syz_sigs fs)"
  shows "is_syz_sig dgrad v"
proof -
  from assms(4) have "v \<in> set (Koszul_syz_sigs_aux fs 0)"
    using filter_min_subset by (fastforce simp: Koszul_syz_sigs_def)
  with assms(3) obtain i j where "i < j" and "j < length fs"
    and v': "v = lt ((fs ! i) \<odot> monomial 1 (term_of_pair (0, j)) - (fs ! j) \<odot> monomial 1 (term_of_pair (0, i)))"
          (is "v = lt (?p - ?q)")
    by (rule Koszul_syz_sigs_auxE_lt_Koszul_syz)
  let ?a = "monomial (1::'b) (term_of_pair (0, i))"
  let ?b = "monomial (1::'b) (term_of_pair (0, j))"
  from \<open>i < j\<close> \<open>j < length fs\<close> have "i < length fs" by simp
  with assms(2) have a: "rep_list ?a = fs ! i" by (simp add: rep_list_monomial term_simps)
  from assms(2) \<open>j < length fs\<close> have b: "rep_list ?b = fs ! j" by (simp add: rep_list_monomial term_simps)
  note v'
  also have "lt (?p - ?q) = ord_term_lin.max (term_of_pair (punit.lt (fs ! i), j)) (term_of_pair (punit.lt (fs ! j), i))"
    using assms(3) \<open>i < j\<close> \<open>j < length fs\<close> by (rule lt_Koszul_syz_init)
  also have "... = ord_term_lin.max (punit.lt (rep_list ?a) \<oplus> lt ?b) (punit.lt (rep_list ?b) \<oplus> lt ?a)"
    by (simp add: a b lt_monomial splus_def term_simps)
  finally have v: "v = ord_term_lin.max (punit.lt (rep_list ?a) \<oplus> lt ?b) (punit.lt (rep_list ?b) \<oplus> lt ?a)" .
  show ?thesis unfolding v using assms(1)
  proof (rule Koszul_syz_is_syz_sig)
    show "?a \<in> dgrad_sig_set dgrad"
      by (rule dgrad_sig_set_closed_monomial, simp_all add: term_simps dgrad_max_0 \<open>i < length fs\<close>)
  next
    show "?b \<in> dgrad_sig_set dgrad"
      by (rule dgrad_sig_set_closed_monomial, simp_all add: term_simps dgrad_max_0 \<open>j < length fs\<close>)
  next
    from \<open>i < length fs\<close> have "fs ! i \<in> set fs" by (rule nth_mem)
    with assms(3) show "rep_list ?a \<noteq> 0" by (fastforce simp: a)
  next
    from \<open>j < length fs\<close> have "fs ! j \<in> set fs" by (rule nth_mem)
    with assms(3) show "rep_list ?b \<noteq> 0" by (fastforce simp: b)
  next
    from \<open>i < j\<close> show "component_of_term (lt ?a) < component_of_term (lt ?b)"
      by (simp add: lt_monomial component_of_term_of_pair)
  qed
qed

lemma Koszul_syz_sigs_minimal:
  assumes "u \<in> set (Koszul_syz_sigs fs)" and "v \<in> set (Koszul_syz_sigs fs)" and "u adds\<^sub>t v"
  shows "u = v"
proof -
  from assms(1, 2) have "u \<in> set (filter_min (adds\<^sub>t) (Koszul_syz_sigs_aux fs 0))"
    and "v \<in> set (filter_min (adds\<^sub>t) (Koszul_syz_sigs_aux fs 0))" by (simp_all add: Koszul_syz_sigs_def)
  with _ show ?thesis using assms(3)
  proof (rule filter_min_minimal)
    show "transp (adds\<^sub>t)" by (rule transpI, drule adds_term_trans)
  qed
qed

lemma Koszul_syz_sigs_distinct: "distinct (Koszul_syz_sigs fs)"
proof -
  from adds_term_refl have "reflp (adds\<^sub>t)" by (rule reflpI)
  thus ?thesis by (simp add: Koszul_syz_sigs_def filter_min_distinct)
qed

subsubsection \<open>Algorithms\<close>

definition spair_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))"
  where "spair_spp p q = (let t1 = punit.lt (snd p); t2 = punit.lt (snd q); l = lcs t1 t2 in
                          (ord_term_lin.max ((l - t1) \<oplus> fst p) ((l - t2) \<oplus> fst q),
                            punit.monom_mult (1 / punit.lc (snd p)) (l - t1) (snd p) -
                            punit.monom_mult (1 / punit.lc (snd q)) (l - t2) (snd q)))"

definition is_regular_spair_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "is_regular_spair_spp p q \<longleftrightarrow>
                    (snd p \<noteq> 0 \<and> snd q \<noteq> 0 \<and> punit.lt (snd q) \<oplus> fst p \<noteq> punit.lt (snd p) \<oplus> fst q)"

definition spair_sigs :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<times> 't)"
  where "spair_sigs p q =
                  (let t1 = punit.lt (rep_list p); t2 = punit.lt (rep_list q); l = lcs t1 t2 in
                    ((l - t1) \<oplus> lt p, (l - t2) \<oplus> lt q))"

definition spair_sigs_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> 't)"
  where "spair_sigs_spp p q =
                  (let t1 = punit.lt (snd p); t2 = punit.lt (snd q); l = lcs t1 t2 in
                    ((l - t1) \<oplus> fst p, (l - t2) \<oplus> fst q))"

fun poly_of_pair :: "((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where
    "poly_of_pair (Inl (p, q)) = spair p q" |
    "poly_of_pair (Inr j) = monomial 1 (term_of_pair (0, j))"

fun spp_of_pair :: "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))"
  where
    "spp_of_pair (Inl (p, q)) = spair_spp p q" |
    "spp_of_pair (Inr j) = (term_of_pair (0, j), fs ! j)"

fun sig_of_pair :: "((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> 't"
  where
    "sig_of_pair (Inl (p, q)) = (let (u, v) = spair_sigs p q in ord_term_lin.max u v)" |
    "sig_of_pair (Inr j) = term_of_pair (0, j)"

fun sig_of_pair_spp :: "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow> 't"
  where
    "sig_of_pair_spp (Inl (p, q)) = (let (u, v) = spair_sigs_spp p q in ord_term_lin.max u v)" |
    "sig_of_pair_spp (Inr j) = term_of_pair (0, j)"

definition pair_ord :: "((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> bool"
  where "pair_ord x y \<longleftrightarrow> (sig_of_pair x \<preceq>\<^sub>t sig_of_pair y)"

definition pair_ord_spp :: "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow>
                            ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow> bool"
  where "pair_ord_spp x y \<longleftrightarrow> (sig_of_pair_spp x \<preceq>\<^sub>t sig_of_pair_spp y)"

primrec new_spairs :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list" where
  "new_spairs [] p = []" |
  "new_spairs (b # bs) p =
    (if is_regular_spair p b then insort_wrt pair_ord (Inl (p, b)) (new_spairs bs p) else new_spairs bs p)"

primrec new_spairs_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow>
                            ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list" where
  "new_spairs_spp [] p = []" |
  "new_spairs_spp (b # bs) p =
      (if is_regular_spair_spp p b then
        insort_wrt pair_ord_spp (Inl (p, b)) (new_spairs_spp bs p)
      else new_spairs_spp bs p)"

definition add_spairs :: "((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow>
                            ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list"
  where "add_spairs ps bs p = merge_wrt pair_ord (new_spairs bs p) ps"

definition add_spairs_spp :: "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list \<Rightarrow>
                              ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow>
                              ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list"
  where "add_spairs_spp ps bs p = merge_wrt pair_ord_spp (new_spairs_spp bs p) ps"

lemma spair_alt_spair_sigs:
  "spair p q = monom_mult (1 / punit.lc (rep_list p)) (pp_of_term (fst (spair_sigs p q)) - lp p) p -
                monom_mult (1 / punit.lc (rep_list q)) (pp_of_term (snd (spair_sigs p q)) - lp q) q"
  by (simp add: spair_def spair_sigs_def Let_def term_simps)

lemma sig_of_spair:
  assumes "is_regular_spair p q"
  shows "sig_of_pair (Inl (p, q)) = lt (spair p q)"
proof -
  from assms have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
  hence 1: "punit.lc (rep_list p) \<noteq> 0" and "p \<noteq> 0" by (rule punit.lc_not_0, auto simp: rep_list_zero)
  from assms have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
  hence 2: "punit.lc (rep_list q) \<noteq> 0" and "q \<noteq> 0" by (rule punit.lc_not_0, auto simp: rep_list_zero)
  let ?t1 = "punit.lt (rep_list p)"
  let ?t2 = "punit.lt (rep_list q)"
  let ?l = "lcs ?t1 ?t2"
  from assms have "lt (monom_mult (1 / punit.lc (rep_list p)) (?l - ?t1) p) \<noteq>
                   lt (monom_mult (1 / punit.lc (rep_list q)) (?l - ?t2) q)"
    by (rule is_regular_spairD3)
  hence *: "lt (monom_mult (1 / punit.lc (rep_list p)) (pp_of_term (fst (spair_sigs p q)) - lp p) p) \<noteq>
            lt (monom_mult (1 / punit.lc (rep_list q)) (pp_of_term (snd (spair_sigs p q)) - lp q) q)"
    by (simp add: spair_sigs_def Let_def term_simps)
  from 1 2 \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show ?thesis
    by (simp add: spair_alt_spair_sigs lt_monom_mult lt_minus_distinct_eq_max[OF *],
        simp add: spair_sigs_def Let_def term_simps)
qed

lemma sig_of_spair_commute: "sig_of_pair (Inl (p, q)) = sig_of_pair (Inl (q, p))"
  by (simp add: spair_sigs_def Let_def lcs_comm ord_term_lin.max.commute)

lemma in_new_spairsI:
  assumes "b \<in> set bs" and "is_regular_spair p b"
  shows "Inl (p, b) \<in> set (new_spairs bs p)"
  using assms(1)
proof (induct bs)
  case Nil
  thus ?case by simp
next
  case (Cons a bs)
  from Cons(2) have "b = a \<or> b \<in> set bs" by simp
  thus ?case
  proof
    assume "b = a"
    from assms(2) show ?thesis by (simp add: \<open>b = a\<close>)
  next
    assume "b \<in> set bs"
    hence "Inl (p, b) \<in> set (new_spairs bs p)" by (rule Cons(1))
    thus ?thesis by simp
  qed
qed

lemma in_new_spairsD:
  assumes "Inl (a, b) \<in> set (new_spairs bs p)"
  shows "a = p" and "b \<in> set bs" and "is_regular_spair p b"
proof -
  from assms have "a = p \<and> b \<in> set bs \<and> is_regular_spair p b"
  proof (induct bs)
  case Nil
  thus ?case by simp
  next
    case (Cons c bs)
    from Cons(2) have "(is_regular_spair p c \<and> Inl (a, b) = Inl (p, c)) \<or> Inl (a, b) \<in> set (new_spairs bs p)"
      by (simp split: if_split_asm)
    thus ?case
    proof
      assume "is_regular_spair p c \<and> Inl (a, b) = Inl (p, c)"
      hence "is_regular_spair p c" and "a = p" and "b = c" by simp_all
      thus ?thesis by simp
    next
      assume "Inl (a, b) \<in> set (new_spairs bs p)"
      hence "a = p \<and> b \<in> set bs \<and> is_regular_spair p b" by (rule Cons(1))
      thus ?thesis by simp
    qed
  qed
  thus "a = p" and "b \<in> set bs" and "is_regular_spair p b" by simp_all
qed

corollary in_new_spairs_iff:
  "Inl (p, b) \<in> set (new_spairs bs p) \<longleftrightarrow> (b \<in> set bs \<and> is_regular_spair p b)"
  by (auto intro: in_new_spairsI dest: in_new_spairsD)

lemma Inr_not_in_new_spairs: "Inr j \<notin> set (new_spairs bs p)"
  by (induct bs, simp_all)

lemma sum_prodE:
  assumes "\<And>a b. p = Inl (a, b) \<Longrightarrow> thesis" and "\<And>j. p = Inr j \<Longrightarrow> thesis"
  shows thesis
  using _ assms(2)
proof (rule sumE)
  fix x
  assume "p = Inl x"
  moreover obtain a b where "x = (a, b)" by fastforce
  ultimately have "p = Inl (a, b)" by simp
  thus ?thesis by (rule assms(1))
qed

corollary in_new_spairsE:
  assumes "q \<in> set (new_spairs bs p)"
  obtains b where "b \<in> set bs" and "is_regular_spair p b" and "q = Inl (p, b)"
proof (rule sum_prodE)
  fix a b
  assume q: "q = Inl (a, b)"
  from assms have "a = p" and "b \<in> set bs" and "is_regular_spair p b"
    unfolding q by (rule in_new_spairsD)+
  note this(2, 3)
  moreover have "q = Inl (p, b)" by (simp only: q \<open>a = p\<close>)
  ultimately show ?thesis ..
next
  fix j
  assume "q = Inr j"
  with assms show ?thesis by (simp add: Inr_not_in_new_spairs)
qed

lemma new_spairs_sorted: "sorted_wrt pair_ord (new_spairs bs p)"
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons a bs)
  moreover have "transp pair_ord" by (rule transpI, simp add: pair_ord_def)
  moreover have "pair_ord x y \<or> pair_ord y x" for x y by (simp add: pair_ord_def ord_term_lin.linear)
  ultimately show ?case by (simp add: sorted_wrt_insort_wrt)
qed

lemma sorted_add_spairs:
  assumes "sorted_wrt pair_ord ps"
  shows "sorted_wrt pair_ord (add_spairs ps bs p)"
  unfolding add_spairs_def using _ _ new_spairs_sorted assms
proof (rule sorted_merge_wrt)
  show "transp pair_ord" by (rule transpI, simp add: pair_ord_def)
next
  fix x y
  show "pair_ord x y \<or> pair_ord y x" by (simp add: pair_ord_def ord_term_lin.linear)
qed

context
  fixes rword_strict :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"   \<comment>\<open>Must be a @{emph \<open>strict\<close>} rewrite order.\<close>
begin

qualified definition rword :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rword x y \<longleftrightarrow> \<not> rword_strict y x"

definition is_pred_syz :: "'t list \<Rightarrow> 't \<Rightarrow> bool"
  where "is_pred_syz ss u = (\<exists>v\<in>set ss. v adds\<^sub>t u)"

definition is_rewritable :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 't \<Rightarrow> bool"
  where "is_rewritable bs p u = (\<exists>b\<in>set bs. b \<noteq> 0 \<and> lt b adds\<^sub>t u \<and> rword_strict (spp_of p) (spp_of b))"

definition is_rewritable_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> 't \<Rightarrow> bool"
  where "is_rewritable_spp bs p u = (\<exists>b\<in>set bs. fst b adds\<^sub>t u \<and> rword_strict p b)"

fun sig_crit :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 't list \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> bool"
  where
    "sig_crit bs ss (Inl (p, q)) =
      (let (u, v) = spair_sigs p q in
        is_pred_syz ss u \<or> is_pred_syz ss v \<or> is_rewritable bs p u \<or> is_rewritable bs q v)" |
    "sig_crit bs ss (Inr j) = is_pred_syz ss (term_of_pair (0, j))"

fun sig_crit' :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) \<Rightarrow> bool"
  where
    "sig_crit' bs (Inl (p, q)) =
      (let (u, v) = spair_sigs p q in
        is_syz_sig dgrad u \<or> is_syz_sig dgrad v \<or> is_rewritable bs p u \<or> is_rewritable bs q v)" |
    "sig_crit' bs (Inr j) = is_syz_sig dgrad (term_of_pair (0, j))"

fun sig_crit_spp :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> 't list \<Rightarrow> ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow> bool"
  where
    "sig_crit_spp bs ss (Inl (p, q)) =
      (let (u, v) = spair_sigs_spp p q in
        is_pred_syz ss u \<or> is_pred_syz ss v \<or> is_rewritable_spp bs p u \<or> is_rewritable_spp bs q v)" |
    "sig_crit_spp bs ss (Inr j) = is_pred_syz ss (term_of_pair (0, j))"

text \<open>@{const sig_crit} is used in algorithms, @{const sig_crit'} is only needed for proving.\<close>

fun rb_spp_body ::
      "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<times> 't list \<times> ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list) \<times> nat) \<Rightarrow>
       ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<times> 't list \<times> ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list) \<times> nat)"
  where
  "rb_spp_body ((bs, ss, []), z) = ((bs, ss, []), z)" |
  "rb_spp_body ((bs, ss, p # ps), z) =
    (let ss' = new_syz_sigs_spp ss bs p in
      if sig_crit_spp bs ss' p then
          ((bs, ss', ps), z)
       else
          let p' = sig_trd_spp bs (spp_of_pair p) in
          if snd p' = 0 then
            ((bs, fst p' # ss', ps), Suc z)
          else
            ((p' # bs, ss', add_spairs_spp ps bs p'), z))"

definition rb_spp_aux ::
      "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<times> 't list \<times> ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list) \<times> nat) \<Rightarrow>
       ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<times> 't list \<times> ((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) list) \<times> nat)"
  where rb_spp_aux_def [code del]: "rb_spp_aux = tailrec.fun (\<lambda>x. snd (snd (fst x)) = []) (\<lambda>x. x) rb_spp_body"

lemma rb_spp_aux_Nil [code]: "rb_spp_aux ((bs, ss, []), z) = ((bs, ss, []), z)"
  by (simp add: rb_spp_aux_def tailrec.simps)

lemma rb_spp_aux_Cons [code]:
  "rb_spp_aux ((bs, ss, p # ps), z) = rb_spp_aux (rb_spp_body ((bs, ss, p # ps), z))"
  by (simp add: rb_spp_aux_def tailrec.simps)

text \<open>The last parameter / return value of @{const rb_spp_aux}, @{term z}, counts the number of
  zero-reductions. Below we will prove that this number remains $0$ under certain conditions.\<close>

context
  assumes rword_is_strict_rewrite_ord: "is_strict_rewrite_ord rword_strict"
  assumes dgrad: "dickson_grading dgrad"
begin

lemma rword: "is_rewrite_ord rword"
  unfolding rword_def using rword_is_strict_rewrite_ord by (rule is_strict_rewrite_ordD)

lemma sig_crit'_sym: "sig_crit' bs (Inl (p, q)) \<Longrightarrow> sig_crit' bs (Inl (q, p))"
  by (auto simp: spair_sigs_def Let_def lcs_comm)

lemma is_rewritable_ConsD:
  assumes "is_rewritable (b # bs) p u" and "u \<prec>\<^sub>t lt b"
  shows "is_rewritable bs p u"
proof -
  from assms(1) obtain b' where "b' \<in> set (b # bs)" and "b' \<noteq> 0" and "lt b' adds\<^sub>t u"
    and "rword_strict (spp_of p) (spp_of b')" unfolding is_rewritable_def by blast
  from this(3) have "lt b' \<preceq>\<^sub>t u" by (rule ord_adds_term)
  with assms(2) have "b' \<noteq> b" by auto
  with \<open>b' \<in> set (b # bs)\<close> have "b' \<in> set bs" by simp
  with \<open>b' \<noteq> 0\<close> \<open>lt b' adds\<^sub>t u\<close> \<open>rword_strict (spp_of p) (spp_of b')\<close> show ?thesis
    by (auto simp: is_rewritable_def)
qed

lemma sig_crit'_ConsD:
  assumes "sig_crit' (b # bs) p" and "sig_of_pair p \<prec>\<^sub>t lt b"
  shows "sig_crit' bs p"
proof (rule sum_prodE)
  fix x y
  assume p: "p = Inl (x, y)"
  define u where "u = fst (spair_sigs x y)"
  define v where "v = snd (spair_sigs x y)"
  have sigs: "spair_sigs x y = (u, v)" by (simp add: u_def v_def)
  have "u \<preceq>\<^sub>t sig_of_pair p" and "v \<preceq>\<^sub>t sig_of_pair p" by (simp_all add: p sigs)
  hence "u \<prec>\<^sub>t lt b" and "v \<prec>\<^sub>t lt b" using assms(2) by simp_all
  with assms(1) show ?thesis by (auto simp: p sigs dest: is_rewritable_ConsD)
next
  fix j
  assume p: "p = Inr j"
  from assms show ?thesis by (simp add: p)
qed

definition rb_aux_inv1 :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> bool"
  where "rb_aux_inv1 bs =
               (set bs \<subseteq> dgrad_sig_set dgrad \<and> 0 \<notin> rep_list ` set bs \<and>
                sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) bs \<and>
                (\<forall>i<length bs. \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i) bs)) (bs ! i)) \<and>
                (\<forall>i<length bs.
    ((\<exists>j<length fs. lt (bs ! i) = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
            punit.lt (rep_list (bs ! i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
    (\<exists>p\<in>set bs. \<exists>q\<in>set bs. is_regular_spair p q \<and> rep_list (spair p q) \<noteq> 0 \<and>
            lt (bs ! i) = lt (spair p q) \<and> punit.lt (rep_list (bs ! i)) \<preceq> punit.lt (rep_list (spair p q))))) \<and>
                (\<forall>i<length bs. is_RB_upt dgrad rword (set (drop (Suc i) bs)) (lt (bs ! i))))"

fun rb_aux_inv :: "(('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list) \<Rightarrow> bool"
  where "rb_aux_inv (bs, ss, ps) =
          (rb_aux_inv1 bs \<and>
            (\<forall>u\<in>set ss. is_syz_sig dgrad u) \<and>
            (\<forall>p q. Inl (p, q) \<in> set ps \<longrightarrow> (is_regular_spair p q \<and> p \<in> set bs \<and> q \<in> set bs)) \<and>
            (\<forall>j. Inr j \<in> set ps \<longrightarrow> (j < length fs \<and> (\<forall>b\<in>set bs. lt b \<prec>\<^sub>t term_of_pair (0, j))) \<and>
                              length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) ps) \<le> 1) \<and>
            (sorted_wrt pair_ord ps) \<and>
            (\<forall>p\<in>set ps. (\<forall>b1\<in>set bs. \<forall>b2\<in>set bs. is_regular_spair b1 b2 \<longrightarrow>
                          sig_of_pair p \<prec>\<^sub>t lt (spair b1 b2) \<longrightarrow> (Inl (b1, b2) \<in> set ps \<or> Inl (b2, b1) \<in> set ps)) \<and>
                        (\<forall>j<length fs. sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j) \<longrightarrow> Inr j \<in> set ps)) \<and>
            (\<forall>b\<in>set bs. \<forall>p\<in>set ps. lt b \<preceq>\<^sub>t sig_of_pair p) \<and>
            (\<forall>a\<in>set bs. \<forall>b\<in>set bs. is_regular_spair a b \<longrightarrow> Inl (a, b) \<notin> set ps \<longrightarrow> Inl (b, a) \<notin> set ps \<longrightarrow>
                \<not> is_RB_in dgrad rword (set bs) (lt (spair a b)) \<longrightarrow>
                (\<exists>p\<in>set ps. sig_of_pair p = lt (spair a b) \<and> \<not> sig_crit' bs p)) \<and>
            (\<forall>j<length fs. Inr j \<notin> set ps \<longrightarrow> (is_RB_in dgrad rword (set bs) (term_of_pair (0, j)) \<and>
                rep_list (monomial (1::'b) (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs))))"

lemmas [simp del] = rb_aux_inv.simps

lemma rb_aux_inv1_D1: "rb_aux_inv1 bs \<Longrightarrow> set bs \<subseteq> dgrad_sig_set dgrad"
  by (simp add: rb_aux_inv1_def)

lemma rb_aux_inv1_D2: "rb_aux_inv1 bs \<Longrightarrow> 0 \<notin> rep_list ` set bs"
  by (simp add: rb_aux_inv1_def)

lemma rb_aux_inv1_D3: "rb_aux_inv1 bs \<Longrightarrow> sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) bs"
  by (simp add: rb_aux_inv1_def)

lemma rb_aux_inv1_D4:
  "rb_aux_inv1 bs \<Longrightarrow> i < length bs \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i) bs)) (bs ! i)"
  by (simp add: rb_aux_inv1_def)

lemma rb_aux_inv1_D5:
  "rb_aux_inv1 bs \<Longrightarrow> i < length bs \<Longrightarrow> is_RB_upt dgrad rword (set (drop (Suc i) bs)) (lt (bs ! i))"
  by (simp add: rb_aux_inv1_def)

lemma rb_aux_inv1_E:
  assumes "rb_aux_inv1 bs" and "i < length bs"
    and "\<And>j. j < length fs \<Longrightarrow> lt (bs ! i) = lt (monomial (1::'b) (term_of_pair (0, j))) \<Longrightarrow>
            punit.lt (rep_list (bs ! i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j)))) \<Longrightarrow> thesis"
    and "\<And>p q. p \<in> set bs \<Longrightarrow> q \<in> set bs \<Longrightarrow> is_regular_spair p q \<Longrightarrow> rep_list (spair p q) \<noteq> 0 \<Longrightarrow>
            lt (bs ! i) = lt (spair p q) \<Longrightarrow> punit.lt (rep_list (bs ! i)) \<preceq> punit.lt (rep_list (spair p q)) \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding rb_aux_inv1_def by blast

lemmas rb_aux_inv1_D = rb_aux_inv1_D1 rb_aux_inv1_D2 rb_aux_inv1_D3 rb_aux_inv1_D4
                           rb_aux_inv1_D5

lemma rb_aux_inv1_distinct_lt:
  assumes "rb_aux_inv1 bs"
  shows "distinct (map lt bs)"
proof (rule distinct_sorted_wrt_irrefl)
  show "irreflp (\<succ>\<^sub>t)" by (simp add: irreflp_def)
next
  show "transp (\<succ>\<^sub>t)" by (auto simp: transp_def)
next
  from assms show "sorted_wrt (\<succ>\<^sub>t) (map lt bs)"
    unfolding sorted_wrt_map conversep_iff by (rule rb_aux_inv1_D3)
qed

corollary rb_aux_inv1_lt_inj_on:
  assumes "rb_aux_inv1 bs"
  shows "inj_on lt (set bs)"
proof
  fix a b
  assume "a \<in> set bs"
  then obtain i where i: "i < length bs" and a: "a = bs ! i" by (metis in_set_conv_nth)
  assume "b \<in> set bs"
  then obtain j where j: "j < length bs" and b: "b = bs ! j" by (metis in_set_conv_nth)
  assume "lt a = lt b"
  with i j have "(map lt bs) ! i = (map lt bs) ! j" by (simp add: a b)
  moreover from assms have "distinct (map lt bs)" by (rule rb_aux_inv1_distinct_lt)
  moreover from i have "i < length (map lt bs)" by simp
  moreover from j have "j < length (map lt bs)" by simp
  ultimately have "i = j" by (simp only: nth_eq_iff_index_eq)
  thus "a = b" by (simp add: a b)
qed

lemma canon_rewriter_unique:
  assumes "rb_aux_inv1 bs" and "is_canon_rewriter rword (set bs) u a"
    and "is_canon_rewriter rword (set bs) u b"
  shows "a = b"
proof -
  from assms(1) have "inj_on lt (set bs)" by (rule rb_aux_inv1_lt_inj_on)
  moreover from rword(1) assms(2, 3) have "lt a = lt b" by (rule is_rewrite_ord_canon_rewriterD2)
  moreover from assms(2) have "a \<in> set bs" by (rule is_canon_rewriterD1)
  moreover from assms(3) have "b \<in> set bs" by (rule is_canon_rewriterD1)
  ultimately show ?thesis by (rule inj_onD)
qed

lemma rb_aux_inv_D1: "rb_aux_inv (bs, ss, ps) \<Longrightarrow> rb_aux_inv1 bs"
  by (simp add: rb_aux_inv.simps)

lemma rb_aux_inv_D2: "rb_aux_inv (bs, ss, ps) \<Longrightarrow> u \<in> set ss \<Longrightarrow> is_syz_sig dgrad u"
  by (simp add: rb_aux_inv.simps)

lemma rb_aux_inv_D3:
  assumes "rb_aux_inv (bs, ss, ps)" and "Inl (p, q) \<in> set ps"
  shows "p \<in> set bs" and "q \<in> set bs" and "is_regular_spair p q"
  using assms by (simp_all add: rb_aux_inv.simps)

lemma rb_aux_inv_D4:
  assumes "rb_aux_inv (bs, ss, ps)" and "Inr j \<in> set ps"
  shows "j < length fs" and "\<And>b. b \<in> set bs \<Longrightarrow> lt b \<prec>\<^sub>t term_of_pair (0, j)"
    and "length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) ps) \<le> 1"
  using assms by (simp_all add: rb_aux_inv.simps)

lemma rb_aux_inv_D5: "rb_aux_inv (bs, ss, ps) \<Longrightarrow> sorted_wrt pair_ord ps"
  by (simp add: rb_aux_inv.simps)

lemma rb_aux_inv_D6_1:
  assumes "rb_aux_inv (bs, ss, ps)" and "p \<in> set ps" and "b1 \<in> set bs" and "b2 \<in> set bs"
    and "is_regular_spair b1 b2" and "sig_of_pair p \<prec>\<^sub>t lt (spair b1 b2)"
  obtains "Inl (b1, b2) \<in> set ps" | "Inl (b2, b1) \<in> set ps"
  using assms unfolding rb_aux_inv.simps by blast

lemma rb_aux_inv_D6_2:
  "rb_aux_inv (bs, ss, ps) \<Longrightarrow> p \<in> set ps \<Longrightarrow> j < length fs \<Longrightarrow> sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j) \<Longrightarrow>
    Inr j \<in> set ps"
  by (simp add: rb_aux_inv.simps)

lemma rb_aux_inv_D7: "rb_aux_inv (bs, ss, ps) \<Longrightarrow> b \<in> set bs \<Longrightarrow> p \<in> set ps \<Longrightarrow> lt b \<preceq>\<^sub>t sig_of_pair p"
  by (simp add: rb_aux_inv.simps)

lemma rb_aux_inv_D8:
  assumes "rb_aux_inv (bs, ss, ps)" and "a \<in> set bs" and "b \<in> set bs" and "is_regular_spair a b"
    and "Inl (a, b) \<notin> set ps" and "Inl (b, a) \<notin> set ps" and "\<not> is_RB_in dgrad rword (set bs) (lt (spair a b))"
  obtains p where "p \<in> set ps" and "sig_of_pair p = lt (spair a b)" and "\<not> sig_crit' bs p"
  using assms unfolding rb_aux_inv.simps by meson

lemma rb_aux_inv_D9:
  assumes "rb_aux_inv (bs, ss, ps)" and "j < length fs" and "Inr j \<notin> set ps"
  shows "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))"
    and "rep_list (monomial (1::'b) (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
  using assms by (simp_all add: rb_aux_inv.simps)

lemma rb_aux_inv_is_RB_upt:
  assumes "rb_aux_inv (bs, ss, ps)" and "\<And>p. p \<in> set ps \<Longrightarrow> u \<preceq>\<^sub>t sig_of_pair p"
  shows "is_RB_upt dgrad rword (set bs) u"
proof -
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  from dgrad rword(1) show ?thesis
  proof (rule is_RB_upt_finite)
    from inv1 show "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  next
    from inv1 show "inj_on lt (set bs)" by (rule rb_aux_inv1_lt_inj_on)
  next
    show "finite (set bs)" by (fact finite_set)
  next
    fix g1 g2
    assume 1: "g1 \<in> set bs" and 2: "g2 \<in> set bs" and 3: "is_regular_spair g1 g2"
      and 4: "lt (spair g1 g2) \<prec>\<^sub>t u"
    have 5: "p \<notin> set ps" if "sig_of_pair p = lt (spair g1 g2)" for p
    proof
      assume "p \<in> set ps"
      hence "u \<preceq>\<^sub>t sig_of_pair p" by (rule assms(2))
      also have "... \<prec>\<^sub>t u" unfolding that by (fact 4)
      finally show False ..
    qed
    show "is_RB_in dgrad rword (set bs) (lt (spair g1 g2))"
    proof (rule ccontr)
      note assms(1) 1 2 3
      moreover have "Inl (g1, g2) \<notin> set ps" by (rule 5, rule sig_of_spair, fact 3)
      moreover have "Inl (g2, g1) \<notin> set ps"
        by (rule 5, simp only: sig_of_spair_commute, rule sig_of_spair, fact 3)
      moreover assume "\<not> is_RB_in dgrad rword (set bs) (lt (spair g1 g2))"
      ultimately obtain p where "p \<in> set ps" and "sig_of_pair p = lt (spair g1 g2)"
        by (rule rb_aux_inv_D8)
      from this(2) have "p \<notin> set ps" by (rule 5)
      thus False using \<open>p \<in> set ps\<close> ..
    qed
  next
    fix j
    assume 1: "term_of_pair (0, j) \<prec>\<^sub>t u"
    note assms(1)
    moreover assume "j < length fs"
    moreover have "Inr j \<notin> set ps"
    proof
      assume "Inr j \<in> set ps"
      hence "u \<preceq>\<^sub>t sig_of_pair (Inr j)" by (rule assms(2))
      also have "... \<prec>\<^sub>t u" by (simp add: 1)
      finally show False ..
    qed
    ultimately show "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))" by (rule rb_aux_inv_D9)
  qed
qed

lemma rb_aux_inv_is_RB_upt_Cons:
  assumes "rb_aux_inv (bs, ss, p # ps)"
  shows "is_RB_upt dgrad rword (set bs) (sig_of_pair p)"
  using assms
proof (rule rb_aux_inv_is_RB_upt)
  fix q
  assume "q \<in> set (p # ps)"
  hence "q = p \<or> q \<in> set ps" by simp
  thus "sig_of_pair p \<preceq>\<^sub>t sig_of_pair q"
  proof
    assume "q = p"
    thus ?thesis by simp
  next
    assume "q \<in> set ps"
    moreover from assms have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    ultimately show ?thesis by (simp add: pair_ord_def)
  qed
qed

lemma Inr_in_tailD:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "Inr j \<in> set ps"
  shows "sig_of_pair p \<noteq> term_of_pair (0, j)"
proof
  assume eq: "sig_of_pair p = term_of_pair (0, j)"
  from assms(2) have "Inr j \<in> set (p # ps)" by simp
  let ?P = "\<lambda>q. sig_of_pair q = term_of_pair (0, j)"
  from assms(2) obtain i1 where "i1 < length ps" and Inrj: "Inr j = ps ! i1"
    by (metis in_set_conv_nth)
  from assms(1) \<open>Inr j \<in> set (p # ps)\<close> have "length (filter ?P (p # ps)) \<le> 1"
    by (rule rb_aux_inv_D4)
  moreover from \<open>i1 < length ps\<close> have "Suc i1 < length (p # ps)" by simp
  moreover have "0 < length (p # ps)" by simp
  moreover have "?P ((p # ps) ! Suc i1)" by (simp add: Inrj[symmetric])
  moreover have "?P ((p # ps) ! 0)" by (simp add: eq)
  ultimately have "Suc i1 = 0" by (rule length_filter_le_1)
  thus False ..
qed

lemma pair_list_aux:
  assumes "rb_aux_inv (bs, ss, ps)" and "p \<in> set ps"
  shows "sig_of_pair p = lt (poly_of_pair p) \<and> poly_of_pair p \<noteq> 0 \<and> poly_of_pair p \<in> dgrad_sig_set dgrad"
proof (rule sum_prodE)
  fix a b
  assume p: "p = Inl (a, b)"
  from assms(1) have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence bs_sub: "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  from assms have "is_regular_spair a b" unfolding p by (rule rb_aux_inv_D3)
  hence "sig_of_pair p = lt (poly_of_pair p)" and "poly_of_pair p \<noteq> 0"
    unfolding p poly_of_pair.simps by (rule sig_of_spair, rule is_regular_spair_nonzero)
  moreover from dgrad have "poly_of_pair p \<in> dgrad_sig_set dgrad" unfolding p poly_of_pair.simps
  proof (rule dgrad_sig_set_closed_spair)
    from assms have "a \<in> set bs" unfolding p by (rule rb_aux_inv_D3)
    thus "a \<in> dgrad_sig_set dgrad" using bs_sub ..
  next
    from assms have "b \<in> set bs" unfolding p by (rule rb_aux_inv_D3)
    thus "b \<in> dgrad_sig_set dgrad" using bs_sub ..
  qed
  ultimately show ?thesis by simp
next
  fix j
  assume "p = Inr j"
  from assms have "j < length fs" unfolding \<open>p = Inr j\<close> by (rule rb_aux_inv_D4)
  have "monomial 1 (term_of_pair (0, j)) \<in> dgrad_sig_set dgrad"
    by (rule dgrad_sig_set_closed_monomial, simp add: pp_of_term_of_pair dgrad_max_0,
        simp add: component_of_term_of_pair \<open>j < length fs\<close>)
  thus ?thesis by (simp add: \<open>p = Inr j\<close> lt_monomial monomial_0_iff)
qed

corollary pair_list_sig_of_pair:
  "rb_aux_inv (bs, ss, ps) \<Longrightarrow> p \<in> set ps \<Longrightarrow> sig_of_pair p = lt (poly_of_pair p)"
  by (simp add: pair_list_aux)

corollary pair_list_nonzero: "rb_aux_inv (bs, ss, ps) \<Longrightarrow> p \<in> set ps \<Longrightarrow> poly_of_pair p \<noteq> 0"
  by (simp add: pair_list_aux)

corollary pair_list_dgrad_sig_set:
  "rb_aux_inv (bs, ss, ps) \<Longrightarrow> p \<in> set ps \<Longrightarrow> poly_of_pair p \<in> dgrad_sig_set dgrad"
  by (simp add: pair_list_aux)

lemma is_rewritableI_is_canon_rewriter:
  assumes "rb_aux_inv1 bs" and "b \<in> set bs" and "b \<noteq> 0" and "lt b adds\<^sub>t u"
    and "\<not> is_canon_rewriter rword (set bs) u b"
  shows "is_rewritable bs b u"
proof -
  from assms(2-5) obtain b' where "b' \<in> set bs" and "b' \<noteq> 0" and "lt b' adds\<^sub>t u"
    and 1: "\<not> rword (spp_of b') (spp_of b)" by (auto simp: is_canon_rewriter_def)
  show ?thesis unfolding is_rewritable_def
  proof (intro bexI conjI)
    from rword(1) have 2: "rword (spp_of b) (spp_of b')"
    proof (rule is_rewrite_ordD3)
      assume "rword (spp_of b') (spp_of b)"
      with 1 show ?thesis ..
    qed
    from rword(1) 1 have "b \<noteq> b'" by (auto dest: is_rewrite_ordD1)
    have "lt b \<noteq> lt b'"
    proof
      assume "lt b = lt b'"
      with rb_aux_inv1_lt_inj_on[OF assms(1)] have "b = b'" using assms(2) \<open>b' \<in> set bs\<close>
        by (rule inj_onD)
      with \<open>b \<noteq> b'\<close> show False ..
    qed
    hence "fst (spp_of b) \<noteq> fst (spp_of b')" by (simp add: spp_of_def)
    with rword_is_strict_rewrite_ord 2 show "rword_strict (spp_of b) (spp_of b')"
      by (auto simp: rword_def dest: is_strict_rewrite_ord_antisym)
  qed fact+
qed

lemma is_rewritableD_is_canon_rewriter:
  assumes "rb_aux_inv1 bs" and "is_rewritable bs b u"
  shows "\<not> is_canon_rewriter rword (set bs) u b"
proof
  assume "is_canon_rewriter rword (set bs) u b"
  hence "b \<in> set bs" and "b \<noteq> 0" and "lt b adds\<^sub>t u"
    and 1: "\<And>a. a \<in> set bs \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of b)"
    by (rule is_canon_rewriterD)+
  from assms(2) obtain b' where "b' \<in> set bs" and "b' \<noteq> 0" and "lt b' adds\<^sub>t u"
    and 2: "rword_strict (spp_of b) (spp_of b')" unfolding is_rewritable_def by blast
  from this(1, 2, 3) have "rword (spp_of b') (spp_of b)" by (rule 1)
  moreover from rword_is_strict_rewrite_ord 2 have "rword (spp_of b) (spp_of b')"
    unfolding rword_def by (rule is_strict_rewrite_ord_asym)
  ultimately have "fst (spp_of b') = fst (spp_of b)" by (rule is_rewrite_ordD4[OF rword])
  hence "lt b' = lt b" by (simp add: spp_of_def)
  with rb_aux_inv1_lt_inj_on[OF assms(1)] have "b' = b" using \<open>b' \<in> set bs\<close> \<open>b \<in> set bs\<close>
    by (rule inj_onD)
  from rword_is_strict_rewrite_ord have "\<not> rword_strict (spp_of b) (spp_of b')"
    unfolding \<open>b' = b\<close> by (rule is_strict_rewrite_ord_irrefl)
  thus False using 2 ..
qed

lemma lemma_12:
  assumes "rb_aux_inv (bs, ss, ps)" and "is_RB_upt dgrad rword (set bs) u"
    and "dgrad (pp_of_term u) \<le> dgrad_max dgrad" and "is_canon_rewriter rword (set bs) u a"
    and "\<not> is_syz_sig dgrad u" and "is_sig_red (\<prec>\<^sub>t) (=) (set bs) (monom_mult 1 (pp_of_term u - lp a) a)"
  obtains p q where "p \<in> set bs" and "q \<in> set bs" and "is_regular_spair p q" and "lt (spair p q) = u"
    and "\<not> sig_crit' bs (Inl (p, q))"
proof -
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence inj: "inj_on lt (set bs)" by (rule rb_aux_inv1_lt_inj_on)
  from assms(4) have "lt a adds\<^sub>t u" by (rule is_canon_rewriterD3)
  hence "lp a adds pp_of_term u" and comp_a: "component_of_term (lt a) = component_of_term u"
    by (simp_all add: adds_term_def)
  let ?s = "pp_of_term u - lp a"
  let ?a = "monom_mult 1 ?s a"
  from assms(4) have "a \<in> set bs" by (rule is_canon_rewriterD1)
  from assms(6) have "rep_list ?a \<noteq> 0" using is_sig_red_top_addsE by blast
  hence "rep_list a \<noteq> 0" by (auto simp: rep_list_monom_mult)
  hence "a \<noteq> 0" by (auto simp: rep_list_zero)
  hence "lt ?a = ?s \<oplus> lt a" by (simp add: lt_monom_mult)
  also from \<open>lp a adds pp_of_term u\<close> have eq0: "... = u"
    by (simp add: splus_def comp_a adds_minus term_simps)
  finally have "lt ?a = u" .
  note dgrad rword(1)
  moreover from assms(2) have "is_RB_upt dgrad rword (set bs) (lt ?a)" by (simp only: \<open>lt ?a = u\<close>)
  moreover from dgrad have "?a \<in> dgrad_sig_set dgrad"
  proof (rule dgrad_sig_set_closed_monom_mult)
    from dgrad \<open>lp a adds pp_of_term u\<close> have "dgrad (pp_of_term u - lp a) \<le> dgrad (pp_of_term u)"
      by (rule dickson_grading_minus)
    thus "dgrad (pp_of_term u - lp a) \<le> dgrad_max dgrad" using assms(3) by (rule le_trans)
  next
    from inv1 have "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
    with \<open>a \<in> set bs\<close> show "a \<in> dgrad_sig_set dgrad" ..
  qed
  ultimately obtain v b where "v \<prec>\<^sub>t lt ?a" and "dgrad (pp_of_term v) \<le> dgrad_max dgrad"
    and "component_of_term v < length fs" and ns: "\<not> is_syz_sig dgrad v"
    and v: "v = (punit.lt (rep_list ?a) - punit.lt (rep_list b)) \<oplus> lt b"
    and cr: "is_canon_rewriter rword (set bs) v b" and "is_sig_red (\<prec>\<^sub>t) (=) {b} ?a"
    using assms(6) by (rule lemma_11)
  from this(6) have "b \<in> set bs" by (rule is_canon_rewriterD1)
  with \<open>a \<in> set bs\<close> show ?thesis
  proof
    from dgrad rword(1) assms(2) inj assms(5, 4) \<open>b \<in> set bs\<close> \<open>is_sig_red (\<prec>\<^sub>t) (=) {b} ?a\<close> assms(3)
    show "is_regular_spair a b" by (rule lemma_9(3))
  next
    from dgrad rword(1) assms(2) inj assms(5, 4) \<open>b \<in> set bs\<close> \<open>is_sig_red (\<prec>\<^sub>t) (=) {b} ?a\<close> assms(3)
    show "lt (spair a b) = u" by (rule lemma_9(4))
  next
    from \<open>rep_list a \<noteq> 0\<close> have v': "v = (?s + punit.lt (rep_list a) - punit.lt (rep_list b)) \<oplus> lt b"
      by (simp add: v rep_list_monom_mult punit.lt_monom_mult)
    moreover from dgrad rword(1) assms(2) inj assms(5, 4) \<open>b \<in> set bs\<close> \<open>is_sig_red (\<prec>\<^sub>t) (=) {b} ?a\<close> assms(3)
    have "lcs (punit.lt (rep_list a)) (punit.lt (rep_list b)) - punit.lt (rep_list a) = ?s"
      and "lcs (punit.lt (rep_list a)) (punit.lt (rep_list b)) - punit.lt (rep_list b) =
            ?s + punit.lt (rep_list a) - punit.lt (rep_list b)"
      by (rule lemma_9)+
    ultimately have eq1: "spair_sigs a b = (u, v)" by (simp add: spair_sigs_def eq0)
    show "\<not> sig_crit' bs (Inl (a, b))"
    proof (simp add: eq1 assms(5) ns, intro conjI notI)
      assume "is_rewritable bs a u"
      with inv1 have "\<not> is_canon_rewriter rword (set bs) u a" by (rule is_rewritableD_is_canon_rewriter)
      thus False using assms(4) ..
    next
      assume "is_rewritable bs b v"
      with inv1 have "\<not> is_canon_rewriter rword (set bs) v b" by (rule is_rewritableD_is_canon_rewriter)
      thus False using cr ..
    qed
  qed
qed

lemma is_canon_rewriterI_eq_sig:
  assumes "rb_aux_inv1 bs" and "b \<in> set bs"
  shows "is_canon_rewriter rword (set bs) (lt b) b"
proof -
  from assms(2) have "rep_list b \<in> rep_list ` set bs" by (rule imageI)
  moreover from assms(1) have "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
  ultimately have "b \<noteq> 0" by (auto simp: rep_list_zero)
  with assms(2) show ?thesis
  proof (rule is_canon_rewriterI)
    fix a
    assume "a \<in> set bs" and "a \<noteq> 0" and "lt a adds\<^sub>t lt b"
    from assms(2) obtain i where "i < length bs" and b: "b = bs ! i" by (metis in_set_conv_nth)
    from assms(1) this(1) have "is_RB_upt dgrad rword (set (drop (Suc i) bs)) (lt (bs ! i))"
      by (rule rb_aux_inv1_D5)
    with dgrad have "is_sig_GB_upt dgrad (set (drop (Suc i) bs)) (lt (bs ! i))"
      by (rule is_RB_upt_is_sig_GB_upt)
    hence "is_sig_GB_upt dgrad (set (drop (Suc i) bs)) (lt b)" by (simp only: b)
    moreover have "set (drop (Suc i) bs) \<subseteq> set bs" by (rule set_drop_subset)
    moreover from assms(1) have "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
    ultimately have "is_sig_GB_upt dgrad (set bs) (lt b)" by (rule is_sig_GB_upt_mono)
    with rword(1) dgrad show "rword (spp_of a) (spp_of b)"
    proof (rule is_rewrite_ordD5)
      from assms(1) \<open>i < length bs\<close> have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i) bs)) (bs ! i)"
        by (rule rb_aux_inv1_D4)
      hence "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set (drop (Suc i) bs)) b" by (simp add: b is_sig_red_top_tail_cases)
      moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set (take (Suc i) bs)) b"
      proof
        assume "is_sig_red (\<prec>\<^sub>t) (=) (set (take (Suc i) bs)) b"
        then obtain f where f_in: "f \<in> set (take (Suc i) bs)" and "is_sig_red (\<prec>\<^sub>t) (=) {f} b"
          by (rule is_sig_red_singletonI)
        from this(2) have "lt f \<prec>\<^sub>t lt b" by (rule is_sig_red_regularD_lt)
        from \<open>i < length bs\<close> have take_eq: "take (Suc i) bs = (take i bs) @ [b]"
          unfolding b by (rule take_Suc_conv_app_nth)
        from assms(1) have "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) ((take (Suc i) bs) @ (drop (Suc i) bs))"
          unfolding append_take_drop_id by (rule rb_aux_inv1_D3)
        hence 1: "\<And>y. y \<in> set (take i bs) \<Longrightarrow> lt b \<prec>\<^sub>t lt y"
          by (simp add: sorted_wrt_append take_eq del: append_take_drop_id)
        from f_in have "f = b \<or> f \<in> set (take i bs)" by (simp add: take_eq)
        hence "lt b \<preceq>\<^sub>t lt f"
        proof
          assume "f \<in> set (take i bs)"
          hence "lt b \<prec>\<^sub>t lt f" by (rule 1)
          thus ?thesis by simp
        qed simp
        with \<open>lt f \<prec>\<^sub>t lt b\<close> show False by simp
      qed
      ultimately have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set (take (Suc i) bs) \<union> set (drop (Suc i) bs)) b"
        by (simp add: is_sig_red_Un)
      thus "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set bs) b" by (metis append_take_drop_id set_append)
    qed fact+
  qed (simp add: term_simps)
qed

lemma not_sig_crit:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and "b \<in> set bs"
  shows "lt b \<prec>\<^sub>t sig_of_pair p"
proof (rule sum_prodE)
  fix x y
  assume p: "p = Inl (x, y)"
  have "p \<in> set (p # ps)" by simp
  hence "Inl (x, y) \<in> set (p # ps)" by (simp only: p)
  define t1 where "t1 = punit.lt (rep_list x)"
  define t2 where "t2 = punit.lt (rep_list y)"
  define u where "u = fst (spair_sigs x y)"
  define v where "v = snd (spair_sigs x y)"
  have u: "u = (lcs t1 t2 - t1) \<oplus> lt x" by (simp add: u_def spair_sigs_def t1_def t2_def Let_def)
  have v: "v = (lcs t1 t2 - t2) \<oplus> lt y" by (simp add: v_def spair_sigs_def t1_def t2_def Let_def)
  have spair_sigs: "spair_sigs x y = (u, v)" by (simp add: u_def v_def)
  with assms(2) have "\<not> is_rewritable bs x u" and "\<not> is_rewritable bs y v"
    by (simp_all add: p)
  from assms(1) \<open>Inl (x, y) \<in> set (p # ps)\<close> have x_in: "x \<in> set bs" and y_in: "y \<in> set bs"
    and "is_regular_spair x y" by (rule rb_aux_inv_D3)+
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  from inv1 have "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
  with x_in y_in have "rep_list x \<noteq> 0" and "rep_list y \<noteq> 0" by auto
  hence "x \<noteq> 0" and "y \<noteq> 0" by (auto simp: rep_list_zero)
  from inv1 have sorted: "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) bs" by (rule rb_aux_inv1_D3)
  from x_in obtain i1 where "i1 < length bs" and x: "x = bs ! i1" by (metis in_set_conv_nth)
  from y_in obtain i2 where "i2 < length bs" and y: "y = bs ! i2" by (metis in_set_conv_nth)
  have "lt b \<noteq> sig_of_pair p"
  proof
    assume lt_b: "lt b = sig_of_pair p"
    from inv1 have crw: "is_canon_rewriter rword (set bs) (lt b) b" using assms(3)
      by (rule is_canon_rewriterI_eq_sig)
    show False
    proof (rule ord_term_lin.linorder_cases)
      assume "u \<prec>\<^sub>t v"
      hence "lt b = v" by (auto simp: lt_b p spair_sigs ord_term_lin.max_def)
      with crw have crw_b: "is_canon_rewriter rword (set bs) v b" by simp
      from v have "lt y adds\<^sub>t v" by (rule adds_termI)
      hence "is_canon_rewriter rword (set bs) v y"
        using inv1 y_in \<open>y \<noteq> 0\<close> \<open>\<not> is_rewritable bs y v\<close> is_rewritableI_is_canon_rewriter by blast
      with inv1 crw_b have "b = y" by (rule canon_rewriter_unique)
      with \<open>lt b = v\<close> have "lt y = v" by simp
      from inv1 \<open>i2 < length bs\<close> have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i2) bs)) (bs ! i2)"
        by (rule rb_aux_inv1_D4)
      moreover have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i2) bs)) (bs ! i2)"
      proof (rule is_sig_red_singletonD)
        have "is_sig_red (\<prec>\<^sub>t) (=) {x} y"
        proof (rule is_sig_red_top_addsI)
          from \<open>lt y = v\<close> have "(lcs t1 t2 - t2) \<oplus> lt y = lt y" by (simp only: v)
          also have "... = 0 \<oplus> lt y" by (simp only: term_simps)
          finally have "lcs t1 t2 - t2 = 0" by (simp only: splus_right_canc)
          hence "lcs t1 t2 = t2" by (metis (full_types) add.left_neutral adds_minus adds_lcs_2)
          with adds_lcs[of t1 t2] show "punit.lt (rep_list x) adds punit.lt (rep_list y)"
            by (simp only: t1_def t2_def)
        next
          from \<open>u \<prec>\<^sub>t v\<close> show "punit.lt (rep_list y) \<oplus> lt x \<prec>\<^sub>t punit.lt (rep_list x) \<oplus> lt y"
            by (simp add: t1_def t2_def u v term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
        qed (simp|fact)+
        thus "is_sig_red (\<prec>\<^sub>t) (\<preceq>) {x} (bs ! i2)" by (simp add: y is_sig_red_top_tail_cases)
      next
        have "lt x \<preceq>\<^sub>t 0 \<oplus> lt x" by (simp only: term_simps)
        also have "... \<preceq>\<^sub>t u" unfolding u using zero_min by (rule splus_mono_left)
        also have "... \<prec>\<^sub>t v" by fact
        finally have *: "lt (bs ! i1) \<prec>\<^sub>t lt (bs ! i2)" by (simp only: \<open>lt y = v\<close> x y[symmetric])
        have "i2 < i1"
        proof (rule linorder_cases)
          assume "i1 < i2"
          with sorted have "lt (bs ! i2) \<prec>\<^sub>t lt (bs ! i1)" using \<open>i2 < length bs\<close>
            by (rule sorted_wrt_nth_less)
          with * show ?thesis by simp
        next
          assume "i1 = i2"
          with * show ?thesis by simp
        qed
        hence "Suc i2 \<le> i1" by simp
        thus "x \<in> set (drop (Suc i2) bs)" unfolding x using \<open>i1 < length bs\<close> by (rule nth_in_set_dropI)
      qed
      ultimately show ?thesis ..
    next
      assume "v \<prec>\<^sub>t u"
      hence "lt b = u" by (auto simp: lt_b p spair_sigs ord_term_lin.max_def)
      with crw have crw_b: "is_canon_rewriter rword (set bs) u b" by simp
      from u have "lt x adds\<^sub>t u" by (rule adds_termI)
      hence "is_canon_rewriter rword (set bs) u x"
        using inv1 x_in \<open>x \<noteq> 0\<close> \<open>\<not> is_rewritable bs x u\<close> is_rewritableI_is_canon_rewriter by blast
      with inv1 crw_b have "b = x" by (rule canon_rewriter_unique)
      with \<open>lt b = u\<close> have "lt x = u" by simp
      from inv1 \<open>i1 < length bs\<close> have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i1) bs)) (bs ! i1)"
        by (rule rb_aux_inv1_D4)
      moreover have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i1) bs)) (bs ! i1)"
      proof (rule is_sig_red_singletonD)
        have "is_sig_red (\<prec>\<^sub>t) (=) {y} x"
        proof (rule is_sig_red_top_addsI)
          from \<open>lt x = u\<close> have "(lcs t1 t2 - t1) \<oplus> lt x = lt x" by (simp only: u)
          also have "... = 0 \<oplus> lt x" by (simp only: term_simps)
          finally have "lcs t1 t2 - t1 = 0" by (simp only: splus_right_canc)
          hence "lcs t1 t2 = t1" by (metis (full_types) add.left_neutral adds_minus adds_lcs)
          with adds_lcs_2[of t2 t1] show "punit.lt (rep_list y) adds punit.lt (rep_list x)"
            by (simp only: t1_def t2_def)
        next
          from \<open>v \<prec>\<^sub>t u\<close> show "punit.lt (rep_list x) \<oplus> lt y \<prec>\<^sub>t punit.lt (rep_list y) \<oplus> lt x"
            by (simp add: t1_def t2_def u v term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
        qed (simp|fact)+
        thus "is_sig_red (\<prec>\<^sub>t) (\<preceq>) {y} (bs ! i1)" by (simp add: x is_sig_red_top_tail_cases)
      next
        have "lt y \<preceq>\<^sub>t 0 \<oplus> lt y" by (simp only: term_simps)
        also have "... \<preceq>\<^sub>t v" unfolding v using zero_min by (rule splus_mono_left)
        also have "... \<prec>\<^sub>t u" by fact
        finally have *: "lt (bs ! i2) \<prec>\<^sub>t lt (bs ! i1)" by (simp only: \<open>lt x = u\<close> y x[symmetric])
        have "i1 < i2"
        proof (rule linorder_cases)
          assume "i2 < i1"
          with sorted have "lt (bs ! i1) \<prec>\<^sub>t lt (bs ! i2)" using \<open>i1 < length bs\<close>
            by (rule sorted_wrt_nth_less)
          with * show ?thesis by simp
        next
          assume "i2 = i1"
          with * show ?thesis by simp
        qed
        hence "Suc i1 \<le> i2" by simp
        thus "y \<in> set (drop (Suc i1) bs)" unfolding y using \<open>i2 < length bs\<close> by (rule nth_in_set_dropI)
      qed
      ultimately show ?thesis ..
    next
      assume "u = v"
      hence "punit.lt (rep_list x) \<oplus> lt y = punit.lt (rep_list y) \<oplus> lt x"
        by (simp add: t1_def t2_def u v term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
      moreover from \<open>is_regular_spair x y\<close>
      have "punit.lt (rep_list y) \<oplus> lt x \<noteq> punit.lt (rep_list x) \<oplus> lt y" by (rule is_regular_spairD3)
      ultimately show ?thesis by simp
    qed
  qed
  moreover from assms(1, 3) \<open>p \<in> set (p # ps)\<close> have "lt b \<preceq>\<^sub>t sig_of_pair p" by (rule rb_aux_inv_D7)
  ultimately show ?thesis by simp
next
  fix j
  assume p: "p = Inr j"
  have "Inr j \<in> set (p # ps)" by (simp add: p)
  with assms(1) have "lt b \<prec>\<^sub>t term_of_pair (0, j)" using assms(3) by (rule rb_aux_inv_D4)
  thus ?thesis by (simp add: p)
qed

context
  assumes fs_distinct: "distinct fs"
  assumes fs_nonzero: "0 \<notin> set fs"
begin

lemma rep_list_monomial': "rep_list (monomial 1 (term_of_pair (0, j))) = ((fs ! j) when j < length fs)"
  by (simp add: rep_list_monomial fs_distinct term_simps)

lemma new_syz_sigs_is_syz_sig:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "v \<in> set (new_syz_sigs ss bs p)"
  shows "is_syz_sig dgrad v"
proof (rule sum_prodE)
  fix a b
  assume "p = Inl (a, b)"
  with assms(2) have "v \<in> set ss" by simp
  with assms(1) show ?thesis by (rule rb_aux_inv_D2)
next
  fix j
  assume p: "p = Inr j"
  let ?f = "\<lambda>b. term_of_pair (punit.lt (rep_list b), j)"
  let ?a = "monomial (1::'b) (term_of_pair (0, j))"
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  have "Inr j \<in> set (p # ps)" by (simp add: p)
  with assms(1) have "j < length fs" by (rule rb_aux_inv_D4)
  hence a: "rep_list ?a = fs ! j" by (simp add: rep_list_monomial')
  show ?thesis
  proof (cases "is_pot_ord")
    case True
    with assms(2) have "v \<in> set (filter_min_append (adds\<^sub>t) ss (filter_min (adds\<^sub>t) (map ?f bs)))"
      by (simp add: p)
    hence "v \<in> set ss \<union> ?f ` set bs" using filter_min_append_subset filter_min_subset by fastforce
    thus ?thesis
    proof
      assume "v \<in> set ss"
      with assms(1) show ?thesis by (rule rb_aux_inv_D2)
    next
      assume "v \<in> ?f ` set bs"
      then obtain b where "b \<in> set bs" and "v = ?f b" ..
      have comp_b: "component_of_term (lt b) < component_of_term (lt ?a)"
      proof (rule ccontr)
        have *: "pp_of_term (term_of_pair (0, j)) \<preceq> pp_of_term (lt b)"
          by (simp add: pp_of_term_of_pair zero_min)
        assume "\<not> component_of_term (lt b) < component_of_term (lt ?a)"
        hence "component_of_term (term_of_pair (0, j)) \<le> component_of_term (lt b)"
          by (simp add: lt_monomial)
        with * have "term_of_pair (0, j) \<preceq>\<^sub>t lt b" by (rule ord_termI)
        moreover from assms(1) \<open>Inr j \<in> set (p # ps)\<close> \<open>b \<in> set bs\<close> have "lt b \<prec>\<^sub>t term_of_pair (0, j)"
          by (rule rb_aux_inv_D4)
        ultimately show False by simp
      qed
      have "v = punit.lt (rep_list b) \<oplus> lt ?a"
        by (simp add: \<open>v = ?f b\<close> a lt_monomial splus_def term_simps)
      also have "... = ord_term_lin.max (punit.lt (rep_list b) \<oplus> lt ?a) (punit.lt (rep_list ?a) \<oplus> lt b)"
      proof -
        have "component_of_term (punit.lt (rep_list ?a) \<oplus> lt b) = component_of_term (lt b)"
          by (simp only: term_simps)
        also have "... < component_of_term (lt ?a)" by (fact comp_b)
        also have "... = component_of_term (punit.lt (rep_list b) \<oplus> lt ?a)"
          by (simp only: term_simps)
        finally have "component_of_term (punit.lt (rep_list ?a) \<oplus> lt b) <
                      component_of_term (punit.lt (rep_list b) \<oplus> lt ?a)" .
        with True have "punit.lt (rep_list ?a) \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt ?a"
          by (rule is_pot_ordD)
        thus ?thesis by (auto simp: ord_term_lin.max_def)
      qed
      finally have v: "v = ord_term_lin.max (punit.lt (rep_list b) \<oplus> lt ?a) (punit.lt (rep_list ?a) \<oplus> lt b)" .
      show ?thesis unfolding v using dgrad
      proof (rule Koszul_syz_is_syz_sig)
        from inv1 have "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
        with \<open>b \<in> set bs\<close> show "b \<in> dgrad_sig_set dgrad" ..
      next
        show "?a \<in> dgrad_sig_set dgrad"
          by (rule dgrad_sig_set_closed_monomial, simp_all add: term_simps dgrad_max_0 \<open>j < length fs\<close>)
      next
        from inv1 have "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
        with \<open>b \<in> set bs\<close> show "rep_list b \<noteq> 0" by fastforce
      next
        from \<open>j < length fs\<close> have "fs ! j \<in> set fs" by (rule nth_mem)
        with fs_nonzero show "rep_list ?a \<noteq> 0" by (auto simp: a)
      qed (fact comp_b)
    qed
  next
    case False
    with assms(2) have "v \<in> set ss" by (simp add: p)
    with assms(1) show ?thesis by (rule rb_aux_inv_D2)
  qed
qed

lemma new_syz_sigs_minimal:
  assumes "\<And>u' v'. u' \<in> set ss \<Longrightarrow> v' \<in> set ss \<Longrightarrow> u' adds\<^sub>t v' \<Longrightarrow> u' = v'"
  assumes "u \<in> set (new_syz_sigs ss bs p)" and "v \<in> set (new_syz_sigs ss bs p)" and "u adds\<^sub>t v"
  shows "u = v"
proof (rule sum_prodE)
  fix a b
  assume p: "p = Inl (a, b)"
  from assms(2, 3) have "u \<in> set ss" and "v \<in> set ss" by (simp_all add: p)
  thus ?thesis using assms(4) by (rule assms(1))
next
  fix j
  assume p: "p = Inr j"
  show ?thesis
  proof (cases is_pot_ord)
    case True
    have "transp (adds\<^sub>t)" by (rule transpI, drule adds_term_trans)
    define ss' where "ss' = filter_min (adds\<^sub>t) (map (\<lambda>b. term_of_pair (punit.lt (rep_list b), j)) bs)"
    note assms(1)
    moreover have "u' = v'" if "u' \<in> set ss'" and "v' \<in> set ss'" and "u' adds\<^sub>t v'" for u' v'
      using \<open>transp (adds\<^sub>t)\<close> that unfolding ss'_def by (rule filter_min_minimal)
    moreover from True assms(2, 3) have "u \<in> set (filter_min_append (adds\<^sub>t) ss ss')"
      and "v \<in> set (filter_min_append (adds\<^sub>t) ss ss')" by (simp_all add: p ss'_def)
    ultimately show ?thesis using assms(4) by (rule filter_min_append_minimal)
  next
    case False
    with assms(2, 3) have "u \<in> set ss" and "v \<in> set ss" by (simp_all add: p)
    thus ?thesis using assms(4) by (rule assms(1))
  qed
qed

lemma new_syz_sigs_distinct:
  assumes "distinct ss"
  shows "distinct (new_syz_sigs ss bs p)"
proof (rule sum_prodE)
  fix a b
  assume "p = Inl (a, b)"
  with assms show ?thesis by simp
next
  fix j
  assume p: "p = Inr j"
  show ?thesis
  proof (cases is_pot_ord)
    case True
    define ss' where "ss' = filter_min (adds\<^sub>t) (map (\<lambda>b. term_of_pair (punit.lt (rep_list b), j)) bs)"
    from adds_term_refl have "reflp (adds\<^sub>t)" by (rule reflpI)
    moreover note assms
    moreover have "distinct ss'" unfolding ss'_def using \<open>reflp (adds\<^sub>t)\<close> by (rule filter_min_distinct)
    ultimately have "distinct (filter_min_append (adds\<^sub>t) ss ss')" by (rule filter_min_append_distinct)
    thus ?thesis by (simp add: p ss'_def True)
  next
    case False
    with assms show ?thesis by (simp add: p)
  qed
qed

lemma sig_crit'I_sig_crit:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "sig_crit bs (new_syz_sigs ss bs p) p"
  shows "sig_crit' bs p"
proof -
  have rl: "is_syz_sig dgrad u"
    if "is_pred_syz (new_syz_sigs ss bs p) u" and "dgrad (pp_of_term u) \<le> dgrad_max dgrad" for u
  proof -
    from that(1) obtain s where "s \<in> set (new_syz_sigs ss bs p)" and adds: "s adds\<^sub>t u"
      unfolding is_pred_syz_def ..
    from assms(1) this(1) have "is_syz_sig dgrad s" by (rule new_syz_sigs_is_syz_sig)
    with dgrad show ?thesis using adds that(2) by (rule is_syz_sig_adds)
  qed
  from assms(1) have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence bs_sub: "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  show ?thesis
  proof (rule sum_prodE)
    fix a b
    assume p: "p = Inl (a, b)"
    hence "Inl (a, b) \<in> set (p # ps)" by simp
    with assms(1) have "a \<in> set bs" and "b \<in> set bs" by (rule rb_aux_inv_D3)+
    with bs_sub have a_in: "a \<in> dgrad_sig_set dgrad" and b_in: "b \<in> dgrad_sig_set dgrad" by fastforce+
    define t1 where "t1 = punit.lt (rep_list a)"
    define t2 where "t2 = punit.lt (rep_list b)"
    define u where "u = fst (spair_sigs a b)"
    define v where "v = snd (spair_sigs a b)"
    from dgrad a_in have "dgrad t1 \<le> dgrad_max dgrad" unfolding t1_def by (rule dgrad_sig_setD_rep_list_lt)
    moreover from dgrad b_in have "dgrad t2 \<le> dgrad_max dgrad"
      unfolding t2_def by (rule dgrad_sig_setD_rep_list_lt)
    ultimately have "ord_class.max (dgrad t1) (dgrad t2) \<le> dgrad_max dgrad" by simp
    with dickson_grading_lcs[OF dgrad] have "dgrad (lcs t1 t2) \<le> dgrad_max dgrad" by (rule le_trans)
    have u: "u = (lcs t1 t2 - t1) \<oplus> lt a" by (simp add: u_def spair_sigs_def t1_def t2_def Let_def)
    have v: "v = (lcs t1 t2 - t2) \<oplus> lt b" by (simp add: v_def spair_sigs_def t1_def t2_def Let_def)
    have 1: "spair_sigs a b = (u, v)" by (simp add: u_def v_def)
    from assms(2) have "(is_pred_syz (new_syz_sigs ss bs p) u \<or> is_pred_syz (new_syz_sigs ss bs p) v) \<or>
                        (is_rewritable bs a u \<or> is_rewritable bs b v)" by (simp add: p 1)
    thus ?thesis
    proof
      assume "is_pred_syz (new_syz_sigs ss bs p) u \<or> is_pred_syz (new_syz_sigs ss bs p) v"
      thus ?thesis
      proof
        assume "is_pred_syz (new_syz_sigs ss bs p) u"
        moreover have "dgrad (pp_of_term u) \<le> dgrad_max dgrad"
        proof (simp add: u term_simps dickson_gradingD1[OF dgrad], rule)
          from dgrad adds_lcs have "dgrad (lcs t1 t2 - t1) \<le> dgrad (lcs t1 t2)"
            by (rule dickson_grading_minus)
          also have "... \<le> dgrad_max dgrad" by fact
          finally show "dgrad (lcs t1 t2 - t1) \<le> dgrad_max dgrad" .
        next
          from a_in show "dgrad (lp a) \<le> dgrad_max dgrad" by (rule dgrad_sig_setD_lp)
        qed
        ultimately have "is_syz_sig dgrad u" by (rule rl)
        thus ?thesis by (simp add: p 1)
      next
        assume "is_pred_syz (new_syz_sigs ss bs p) v"
        moreover have "dgrad (pp_of_term v) \<le> dgrad_max dgrad"
        proof (simp add: v term_simps dickson_gradingD1[OF dgrad], rule)
          from dgrad adds_lcs_2 have "dgrad (lcs t1 t2 - t2) \<le> dgrad (lcs t1 t2)"
            by (rule dickson_grading_minus)
          also have "... \<le> dgrad_max dgrad" by fact
          finally show "dgrad (lcs t1 t2 - t2) \<le> dgrad_max dgrad" .
        next
          from b_in show "dgrad (lp b) \<le> dgrad_max dgrad" by (rule dgrad_sig_setD_lp)
        qed
        ultimately have "is_syz_sig dgrad v" by (rule rl)
        thus ?thesis by (simp add: p 1)
      qed
    next
      assume "is_rewritable bs a u \<or> is_rewritable bs b v"
      thus ?thesis by (simp add: p 1)
    qed
  next
    fix j
    assume "p = Inr j"
    with assms(2) have "is_pred_syz (new_syz_sigs ss bs p) (term_of_pair (0, j))" by simp
    moreover have "dgrad (pp_of_term (term_of_pair (0, j))) \<le> dgrad_max dgrad"
      by (simp add: pp_of_term_of_pair dgrad_max_0)
    ultimately have "is_syz_sig dgrad (term_of_pair (0, j))" by (rule rl)
    thus ?thesis by (simp add: \<open>p = Inr j\<close>)
  qed
qed

lemma rb_aux_inv_preserved_0:
  assumes "rb_aux_inv (bs, ss, p # ps)"
    and "\<And>s. s \<in> set ss' \<Longrightarrow> is_syz_sig dgrad s"
    and "\<And>a b. a \<in> set bs \<Longrightarrow> b \<in> set bs \<Longrightarrow> is_regular_spair a b \<Longrightarrow> Inl (a, b) \<notin> set ps \<Longrightarrow>
           Inl (b, a) \<notin> set ps \<Longrightarrow> \<not> is_RB_in dgrad rword (set bs) (lt (spair a b)) \<Longrightarrow>
           \<exists>q\<in>set ps. sig_of_pair q = lt (spair a b) \<and> \<not> sig_crit' bs q"
    and "\<And>j. j < length fs \<Longrightarrow> p = Inr j \<Longrightarrow> Inr j \<notin> set ps \<Longrightarrow> is_RB_in dgrad rword (set bs) (term_of_pair (0, j)) \<and>
            rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
  shows "rb_aux_inv (bs, ss', ps)"
proof -
  from assms(1) have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  show ?thesis unfolding rb_aux_inv.simps
  proof (intro conjI ballI allI impI)
    fix s
    assume "s \<in> set ss'"
    thus "is_syz_sig dgrad s" by (rule assms(2))
  next
    fix q1 q2
    assume "Inl (q1, q2) \<in> set ps"
    hence "Inl (q1, q2) \<in> set (p # ps)" by simp
    with assms(1) show "is_regular_spair q1 q2" and "q1 \<in> set bs" and "q2 \<in> set bs"
      by (rule rb_aux_inv_D3)+
  next
    fix j
    assume "Inr j \<in> set ps"
    hence "Inr j \<in> set (p # ps)" by simp
    with assms(1) have "j < length fs" and "length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) (p # ps)) \<le> 1"
      by (rule rb_aux_inv_D4)+
    have "length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) ps) \<le>
          length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) (p # ps))" by simp
    also have "... \<le> 1" by fact
    finally show "length (filter (\<lambda>q. sig_of_pair q = term_of_pair (0, j)) ps) \<le> 1" .
    show "j < length fs" by fact

    fix b
    assume "b \<in> set bs"
    with assms(1) \<open>Inr j \<in> set (p # ps)\<close> show "lt b \<prec>\<^sub>t term_of_pair (0, j)" by (rule rb_aux_inv_D4)
  next
    from assms(1) have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    thus "sorted_wrt pair_ord ps" by simp
  next
    fix q
    assume "q \<in> set ps"
    from assms(1) have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    hence "\<And>p'. p' \<in> set ps \<Longrightarrow> sig_of_pair p \<preceq>\<^sub>t sig_of_pair p'" by (simp add: pair_ord_def)
    with \<open>q \<in> set ps\<close> have 1: "sig_of_pair p \<preceq>\<^sub>t sig_of_pair q" by blast
    {
      fix b1 b2
      note assms(1)
      moreover from \<open>q \<in> set ps\<close> have "q \<in> set (p # ps)" by simp
      moreover assume "b1 \<in> set bs" and "b2 \<in> set bs" and "is_regular_spair b1 b2"
        and 2: "sig_of_pair q \<prec>\<^sub>t lt (spair b1 b2)"
      ultimately show "Inl (b1, b2) \<in> set ps \<or> Inl (b2, b1) \<in> set ps"
      proof (rule rb_aux_inv_D6_1)
        assume "Inl (b1, b2) \<in> set (p # ps)"
        moreover from 1 2 have "sig_of_pair p \<prec>\<^sub>t lt (spair b1 b2)" by simp
        ultimately have "Inl (b1, b2) \<in> set ps"
          by (auto simp: sig_of_spair \<open>is_regular_spair b1 b2\<close> simp del: sig_of_pair.simps)
        thus ?thesis ..
      next
        assume "Inl (b2, b1) \<in> set (p # ps)"
        moreover from 1 2 have "sig_of_pair p \<prec>\<^sub>t lt (spair b1 b2)" by simp
        ultimately have "Inl (b2, b1) \<in> set ps"
          by (auto simp: sig_of_spair \<open>is_regular_spair b1 b2\<close> sig_of_spair_commute simp del: sig_of_pair.simps)
        thus ?thesis ..
      qed
    }
    {
      fix j
      note assms(1)
      moreover from \<open>q \<in> set ps\<close> have "q \<in> set (p # ps)" by simp
      moreover assume "j < length fs" and 2: "sig_of_pair q \<prec>\<^sub>t term_of_pair (0, j)"
      ultimately have "Inr j \<in> set (p # ps)" by (rule rb_aux_inv_D6_2)
      moreover from 1 2 have "sig_of_pair p \<prec>\<^sub>t sig_of_pair (Inr j)" by simp
      ultimately show "Inr j \<in> set ps" by auto
    }
  next
    fix b q
    assume "b \<in> set bs" and "q \<in> set ps"
    hence "b \<in> set bs" and "q \<in> set (p # ps)" by simp_all
    with assms(1) show "lt b \<preceq>\<^sub>t sig_of_pair q" by (rule rb_aux_inv_D7)
  next
    fix j
    assume "j < length fs" and "Inr j \<notin> set ps"
    have "is_RB_in dgrad rword (set bs) (term_of_pair (0, j)) \<and>
            rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
    proof (cases "p = Inr j")
      case True
      with \<open>j < length fs\<close> show ?thesis using \<open>Inr j \<notin> set ps\<close> by (rule assms(4))
    next
      case False
      with \<open>Inr j \<notin> set ps\<close> have "Inr j \<notin> set (p # ps)" by simp
      with assms(1) \<open>j < length fs\<close> rb_aux_inv_D9 show ?thesis by blast
    qed
    thus "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))"
      and "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)" by simp_all
  qed (fact, rule assms(3))
qed

lemma rb_aux_inv_preserved_1:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "sig_crit bs (new_syz_sigs ss bs p) p"
  shows "rb_aux_inv (bs, new_syz_sigs ss bs p, ps)"
proof -
  from assms(1) have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence bs_sub: "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  from assms(1, 2) have "sig_crit' bs p" by (rule sig_crit'I_sig_crit)
  from assms(1) show ?thesis
  proof (rule rb_aux_inv_preserved_0)
    fix s
    assume "s \<in> set (new_syz_sigs ss bs p)"
    with assms(1) show "is_syz_sig dgrad s" by (rule new_syz_sigs_is_syz_sig)
  next
    fix a b
    assume 1: "a \<in> set bs" and 2: "b \<in> set bs" and 3: "is_regular_spair a b" and 4: "Inl (a, b) \<notin> set ps"
      and 5: "Inl (b, a) \<notin> set ps" and 6: "\<not> is_RB_in dgrad rword (set bs) (lt (spair a b))"
    from assms(1, 2) have "sig_crit' bs p" by (rule sig_crit'I_sig_crit)
    show "\<exists>q\<in>set ps. sig_of_pair q = lt (spair a b) \<and> \<not> sig_crit' bs q"
    proof (cases "p = Inl (a, b) \<or> p = Inl (b, a)")
      case True
      hence sig_of_p: "lt (spair a b) = sig_of_pair p"
      proof
        assume p: "p = Inl (a, b)"
        from 3 show ?thesis by (simp only: p sig_of_spair)
      next
        assume p: "p = Inl (b, a)"
        from 3 have "is_regular_spair b a" by (rule is_regular_spair_sym)
        thus ?thesis by (simp only: p sig_of_spair spair_comm[of a] lt_uminus)
      qed
      note assms(1)
      moreover have "is_RB_upt dgrad rword (set bs) (lt (spair a b))" unfolding sig_of_p
        using assms(1) by (rule rb_aux_inv_is_RB_upt_Cons)
      moreover have "dgrad (lp (spair a b)) \<le> dgrad_max dgrad"
      proof (rule dgrad_sig_setD_lp, rule dgrad_sig_set_closed_spair, fact dgrad)
        from \<open>a \<in> set bs\<close> bs_sub show "a \<in> dgrad_sig_set dgrad" ..
      next
        from \<open>b \<in> set bs\<close> bs_sub show "b \<in> dgrad_sig_set dgrad" ..
      qed
      moreover obtain c where crw: "is_canon_rewriter rword (set bs) (lt (spair a b)) c"
      proof (rule ord_term_lin.linorder_cases)
        from 3 have "rep_list b \<noteq> 0" by (rule is_regular_spairD2)
        moreover assume "punit.lt (rep_list b) \<oplus> lt a \<prec>\<^sub>t punit.lt (rep_list a) \<oplus> lt b"
        ultimately have "lt (spair b a) = (lcs (punit.lt (rep_list b)) (punit.lt (rep_list a)) - punit.lt (rep_list b)) \<oplus> lt b"
          by (rule lt_spair)
        hence "lt (spair a b) = (lcs (punit.lt (rep_list b)) (punit.lt (rep_list a)) - punit.lt (rep_list b)) \<oplus> lt b"
          by (simp add: spair_comm[of a])
        hence "lt b adds\<^sub>t lt (spair a b)" by (rule adds_termI)
        from \<open>rep_list b \<noteq> 0\<close> have "b \<noteq> 0" by (auto simp: rep_list_zero)
        show ?thesis by (rule is_rewrite_ord_finite_canon_rewriterE, fact rword, fact finite_set, fact+)
      next
        from 3 have "rep_list a \<noteq> 0" by (rule is_regular_spairD1)
        moreover assume "punit.lt (rep_list a) \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt a"
        ultimately have "lt (spair a b) = (lcs (punit.lt (rep_list a)) (punit.lt (rep_list b)) - punit.lt (rep_list a)) \<oplus> lt a"
          by (rule lt_spair)
        hence "lt a adds\<^sub>t lt (spair a b)" by (rule adds_termI)
        from \<open>rep_list a \<noteq> 0\<close> have "a \<noteq> 0" by (auto simp: rep_list_zero)
        show ?thesis by (rule is_rewrite_ord_finite_canon_rewriterE, fact rword, fact finite_set, fact+)
      next
        from 3 have "punit.lt (rep_list b) \<oplus> lt a \<noteq> punit.lt (rep_list a) \<oplus> lt b"
          by (rule is_regular_spairD3)
        moreover assume "punit.lt (rep_list b) \<oplus> lt a = punit.lt (rep_list a) \<oplus> lt b"
        ultimately show ?thesis ..
      qed
      moreover from 6 have "\<not> is_syz_sig dgrad (lt (spair a b))" by (simp add: is_RB_in_def)
      moreover from 6 crw have "is_sig_red (\<prec>\<^sub>t) (=) (set bs) (monom_mult 1 (lp (spair a b) - lp c) c)"
        by (simp add: is_RB_in_def)
      ultimately obtain x y where 7: "x \<in> set bs" and 8: "y \<in> set bs" and 9: "is_regular_spair x y"
        and 10: "lt (spair x y) = lt (spair a b)" and 11: "\<not> sig_crit' bs (Inl (x, y))"
        by (rule lemma_12)
      from this(5) \<open>sig_crit' bs p\<close> have "Inl (x, y) \<noteq> p" and "Inl (y, x) \<noteq> p"
        by (auto simp only: sig_crit'_sym)
      show ?thesis
      proof (cases "Inl (x, y) \<in> set ps \<or> Inl (y, x) \<in> set ps")
        case True
        thus ?thesis
        proof
          assume "Inl (x, y) \<in> set ps"
          show ?thesis
          proof (intro bexI conjI)
            show "sig_of_pair (Inl (x, y)) = lt (spair a b)" by (simp only: sig_of_spair 9 10)
          qed fact+
        next
          assume "Inl (y, x) \<in> set ps"
          show ?thesis
          proof (intro bexI conjI)
            from 9 have "is_regular_spair y x" by (rule is_regular_spair_sym)
            thus "sig_of_pair (Inl (y, x)) = lt (spair a b)"
              by (simp only: sig_of_spair spair_comm[of y] lt_uminus 10)
          next
            from 11 show "\<not> sig_crit' bs (Inl (y, x))" by (auto simp only: sig_crit'_sym)
          qed fact
        qed
      next
        case False
        note assms(1) 7 8 9
        moreover from False \<open>Inl (x, y) \<noteq> p\<close> \<open>Inl (y, x) \<noteq> p\<close> have "Inl (x, y) \<notin> set (p # ps)"
          and "Inl (y, x) \<notin> set (p # ps)" by auto
        moreover from 6 have "\<not> is_RB_in dgrad rword (set bs) (lt (spair x y))" by (simp add: 10)
        ultimately obtain q where 12: "q \<in> set (p # ps)" and 13: "sig_of_pair q = lt (spair x y)"
          and 14: "\<not> sig_crit' bs q" by (rule rb_aux_inv_D8)
        from 12 14 \<open>sig_crit' bs p\<close> have "q \<in> set ps" by auto
        with 13 14 show ?thesis unfolding 10 by blast
      qed
    next
      case False
      with 4 5 have "Inl (a, b) \<notin> set (p # ps)" and "Inl (b, a) \<notin> set (p # ps)" by auto
      with assms(1) 1 2 3 obtain q where 7: "q \<in> set (p # ps)" and 8: "sig_of_pair q = lt (spair a b)"
        and 9: "\<not> sig_crit' bs q" using 6 by (rule rb_aux_inv_D8)
      from 7 9 \<open>sig_crit' bs p\<close> have "q \<in> set ps" by auto
      with 8 9 show ?thesis by blast
    qed
  next
    fix j
    assume "j < length fs"
    assume p: "p = Inr j"
    with \<open>sig_crit' bs p\<close> have "is_syz_sig dgrad (term_of_pair (0, j))" by simp
    hence "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))" by (rule is_RB_inI2)
    moreover have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
    proof (rule sig_red_zero_idealI, rule syzygy_crit)
      from assms(1) have "is_RB_upt dgrad rword (set bs) (sig_of_pair p)"
        by (rule rb_aux_inv_is_RB_upt_Cons)
      with dgrad have "is_sig_GB_upt dgrad (set bs) (sig_of_pair p)"
        by (rule is_RB_upt_is_sig_GB_upt)
      thus "is_sig_GB_upt dgrad (set bs) (term_of_pair (0, j))" by (simp add: p)
    next
      show "monomial 1 (term_of_pair (0, j)) \<in> dgrad_sig_set dgrad"
        by (rule dgrad_sig_set_closed_monomial, simp_all add: term_simps dgrad_max_0 \<open>j < length fs\<close>)
    next
      show "lt (monomial (1::'b) (term_of_pair (0, j))) = term_of_pair (0, j)" by (simp add: lt_monomial)
    qed (fact dgrad, fact)
    ultimately show "is_RB_in dgrad rword (set bs) (term_of_pair (0, j)) \<and>
                      rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)" ..
  qed
qed

lemma rb_aux_inv_preserved_2:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "rep_list (sig_trd bs (poly_of_pair p)) = 0"
  shows "rb_aux_inv (bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps)"
proof -
  let ?p = "sig_trd bs (poly_of_pair p)"
  have 0: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (poly_of_pair p) ?p"
    by (rule sig_trd_red_rtrancl)
  hence eq: "lt ?p = lt (poly_of_pair p)" by (rule sig_red_regular_rtrancl_lt)
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  have *: "is_syz_sig dgrad (lt (poly_of_pair p))"
  proof (rule is_syz_sigI)
    have "poly_of_pair p \<noteq> 0" by (rule pair_list_nonzero, fact, simp)
    hence "lc (poly_of_pair p) \<noteq> 0" by (rule lc_not_0)
    moreover from 0 have "lc ?p = lc (poly_of_pair p)" by (rule sig_red_regular_rtrancl_lc)
    ultimately have "lc ?p \<noteq> 0" by simp
    thus "?p \<noteq> 0" by (simp add: lc_eq_zero_iff)
  next
    note dgrad(1)
    moreover from inv1 have "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
    moreover have "poly_of_pair p \<in> dgrad_sig_set dgrad" by (rule pair_list_dgrad_sig_set, fact, simp)
    ultimately show "?p \<in> dgrad_sig_set dgrad" using 0 by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  qed (fact eq, fact assms(2))
  hence rb: "is_RB_in dgrad rword (set bs) (lt (poly_of_pair p))" by (rule is_RB_inI2)
  from assms(1) show ?thesis
  proof (rule rb_aux_inv_preserved_0)
    fix s
    assume "s \<in> set (lt ?p # new_syz_sigs ss bs p)"
    hence "s = lt (poly_of_pair p) \<or> s \<in> set (new_syz_sigs ss bs p)" by (simp add: eq)
    thus "is_syz_sig dgrad s"
    proof
      assume "s = lt (poly_of_pair p)"
      with * show ?thesis by simp
    next
      assume "s \<in> set (new_syz_sigs ss bs p)"
      with assms(1) show ?thesis by (rule new_syz_sigs_is_syz_sig)
    qed
  next
    fix a b
    assume 1: "a \<in> set bs" and 2: "b \<in> set bs" and 3: "is_regular_spair a b" and 4: "Inl (a, b) \<notin> set ps"
    and 5: "Inl (b, a) \<notin> set ps" and 6: "\<not> is_RB_in dgrad rword (set bs) (lt (spair a b))"
    have "p \<in> set (p # ps)" by simp
    with assms(1) have sig_of_p: "sig_of_pair p = lt (poly_of_pair p)" by (rule pair_list_sig_of_pair)
    from rb 6 have neq: "lt (poly_of_pair p) \<noteq> lt (spair a b)" by auto
    hence "p \<noteq> Inl (a, b)" and "p \<noteq> Inl (b, a)" by (auto simp: spair_comm[of a])
    with 4 5 have "Inl (a, b) \<notin> set (p # ps)" and "Inl (b, a) \<notin> set (p # ps)" by auto
    with assms(1) 1 2 3 obtain q where 7: "q \<in> set (p # ps)" and 8: "sig_of_pair q = lt (spair a b)"
      and 9: "\<not> sig_crit' bs q" using 6 by (rule rb_aux_inv_D8)
    from this(1, 2) neq have "q \<in> set ps" by (auto simp: sig_of_p)
    thus "\<exists>q\<in>set ps. sig_of_pair q = lt (spair a b) \<and> \<not> sig_crit' bs q" using 8 9 by blast
  next
    fix j
    assume "j < length fs"
    assume p: "p = Inr j"
    from rb have "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))" by (simp add: p lt_monomial)
    moreover have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
    proof (rule sig_red_zero_idealI, rule sig_red_zeroI)
      from 0 show "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) ?p" by (simp add: p)
    qed fact
    ultimately show "is_RB_in dgrad rword (set bs) (term_of_pair (0, j)) \<and>
                      rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)" ..
  qed
qed

lemma rb_aux_inv_preserved_3:
  assumes "rb_aux_inv (bs, ss, p # ps)" and "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
    and "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
  shows "rb_aux_inv ((sig_trd bs (poly_of_pair p)) # bs, new_syz_sigs ss bs p,
                          add_spairs ps bs (sig_trd bs (poly_of_pair p)))"
    and "lt (sig_trd bs (poly_of_pair p)) \<notin> lt ` set bs"
proof -
  have "p \<in> set (p # ps)" by simp
  with assms(1) have sig_of_p: "sig_of_pair p = lt (poly_of_pair p)"
    and p_in: "poly_of_pair p \<in> dgrad_sig_set dgrad"
    by (rule pair_list_sig_of_pair, rule pair_list_dgrad_sig_set)
  define p' where "p' = sig_trd bs (poly_of_pair p)"
  from assms(1) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence bs_sub: "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  have p_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (poly_of_pair p) p'"
    and p'_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p'"
    unfolding p'_def by (rule sig_trd_red_rtrancl, rule sig_trd_irred)
  from dgrad bs_sub p_in p_red have p'_in: "p' \<in> dgrad_sig_set dgrad"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  from p_red have lt_p': "lt p' = lt (poly_of_pair p)" by (rule sig_red_regular_rtrancl_lt)
  have sig_merge: "sig_of_pair p \<preceq>\<^sub>t sig_of_pair q" if "q \<in> set (add_spairs ps bs p')" for q
    using that unfolding add_spairs_def set_merge_wrt
  proof
    assume "q \<in> set (new_spairs bs p')"
    then obtain b0 where "is_regular_spair p' b0" and "q = Inl (p', b0)" by (rule in_new_spairsE)
    hence sig_of_q: "sig_of_pair q = lt (spair p' b0)" by (simp only: sig_of_spair)
    show ?thesis unfolding sig_of_q sig_of_p lt_p'[symmetric] by (rule is_regular_spair_lt_ge_1, fact)
  next
    assume "q \<in> set ps"
    moreover from assms(1) have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    ultimately show ?thesis by (simp add: pair_ord_def)
  qed
  have sig_of_p_less: "sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j)" if "Inr j \<in> set ps" for j
  proof (intro ord_term_lin.le_neq_trans)
    from assms(1) have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    with \<open>Inr j \<in> set ps\<close> show "sig_of_pair p \<preceq>\<^sub>t term_of_pair (0, j)"
      by (auto simp: pair_ord_def)
  next
    from assms(1) that show "sig_of_pair p \<noteq> term_of_pair (0, j)" by (rule Inr_in_tailD)
  qed
  have lt_p_gr: "lt b \<prec>\<^sub>t lt (poly_of_pair p)" if "b \<in> set bs" for b unfolding sig_of_p[symmetric]
    using assms(1, 2) that by (rule not_sig_crit)
  have inv1: "rb_aux_inv1 (p' # bs)" unfolding rb_aux_inv1_def
  proof (intro conjI impI allI)
    from bs_sub p'_in show "set (p' # bs) \<subseteq> dgrad_sig_set dgrad" by simp
  next
    from inv1 have "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
    with assms(3) show "0 \<notin> rep_list ` set (p' # bs)" by (simp add: p'_def)
  next
    from inv1 have "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) bs" by (rule rb_aux_inv1_D3)
    with lt_p_gr show "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) (p' # bs)" by (simp add: lt_p')
  next
    fix i
    assume "i < length (p' # bs)"
    have "(\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i) (p' # bs))) ((p' # bs) ! i)) \<and>
          ((\<exists>j<length fs. lt ((p' # bs) ! i) = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
             punit.lt (rep_list ((p' # bs) ! i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
         (\<exists>p\<in>set (p' # bs). \<exists>q\<in>set (p' # bs). is_regular_spair p q \<and> rep_list (spair p q) \<noteq> 0 \<and>
                lt ((p' # bs) ! i) = lt (spair p q) \<and>
                punit.lt (rep_list ((p' # bs) ! i)) \<preceq> punit.lt (rep_list (spair p q)))) \<and>
          is_RB_upt dgrad rword (set (drop (Suc i) (p' # bs))) (lt ((p' # bs) ! i))"
      (is "?thesis1 \<and> ?thesis2 \<and> ?thesis3")
    proof (cases i)
      case 0
      show ?thesis
      proof (simp add: \<open>i = 0\<close> p'_irred del: bex_simps, rule conjI)
        show "(\<exists>j<length fs. lt p' = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
                  punit.lt (rep_list p') \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
              (\<exists>p\<in>insert p' (set bs). \<exists>q\<in>insert p' (set bs). is_regular_spair p q \<and> rep_list (spair p q) \<noteq> 0 \<and>
                     lt p' = lt (spair p q) \<and> punit.lt (rep_list p') \<preceq> punit.lt (rep_list (spair p q)))"
        proof (rule sum_prodE)
          fix a b
          assume p: "p = Inl (a, b)"
          have "Inl (a, b) \<in> set (p # ps)" by (simp add: p)
          with assms(1) have "a \<in> set bs" and "b \<in> set bs" and "is_regular_spair a b"
            by (rule rb_aux_inv_D3)+
          from p_red have p'_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (spair a b) p'" by (simp add: p)
          hence "(punit.red (rep_list ` set bs))\<^sup>*\<^sup>* (rep_list (spair a b)) (rep_list p')"
            by (rule sig_red_red_rtrancl)
          moreover from assms(3) have "rep_list p' \<noteq> 0" by (simp add: p'_def)
          ultimately have "rep_list (spair a b) \<noteq> 0" by (auto dest: punit.rtrancl_0)
          moreover from p'_red have "lt p' = lt (spair a b)"
            and "punit.lt (rep_list p') \<preceq> punit.lt (rep_list (spair a b))"
            by (rule sig_red_regular_rtrancl_lt, rule sig_red_rtrancl_lt_rep_list)
          ultimately show ?thesis using \<open>a \<in> set bs\<close> \<open>b \<in> set bs\<close> \<open>is_regular_spair a b\<close> by blast
        next
          fix j
          assume "p = Inr j"
          hence "Inr j \<in> set (p # ps)" by simp
          with assms(1) have "j < length fs" by (rule rb_aux_inv_D4)
          from p_red have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
            by (simp add: \<open>p = Inr j\<close>)
          hence "lt p' = lt (monomial (1::'b) (term_of_pair (0, j)))"
            and "punit.lt (rep_list p') \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))"
            by (rule sig_red_regular_rtrancl_lt, rule sig_red_rtrancl_lt_rep_list)
          with \<open>j < length fs\<close> show ?thesis by blast
        qed
      next
        from assms(1) show "is_RB_upt dgrad rword (set bs) (lt p')" unfolding lt_p' sig_of_p[symmetric]
          by (rule rb_aux_inv_is_RB_upt_Cons)
      qed
    next
      case (Suc i')
      with \<open>i < length (p' # bs)\<close> have i': "i' < length bs" by simp
      show ?thesis
      proof (simp add: \<open>i = Suc i'\<close> del: bex_simps, intro conjI)
        from inv1 i' show "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc i') bs)) (bs ! i')"
          by (rule rb_aux_inv1_D4)
      next
        from inv1 i'
        show "(\<exists>j<length fs. lt (bs ! i') = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
                punit.lt (rep_list (bs ! i')) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
            (\<exists>p\<in>insert p' (set bs). \<exists>q\<in>insert p' (set bs). is_regular_spair p q \<and> rep_list (spair p q) \<noteq> 0 \<and>
                lt (bs ! i') = lt (spair p q) \<and> punit.lt (rep_list (bs ! i')) \<preceq> punit.lt (rep_list (spair p q)))"
          by (auto elim!: rb_aux_inv1_E)
      next
        from inv1 i' show "is_RB_upt dgrad rword (set (drop (Suc i') bs)) (lt (bs ! i'))"
          by (rule rb_aux_inv1_D5)
      qed
    qed
    thus ?thesis1 and ?thesis2 and ?thesis3 by simp_all
  qed
  have rb: "is_RB_in dgrad rword (set (p' # bs)) (sig_of_pair p)"
  proof (rule is_RB_inI1)
    have "p' \<in> set (p' # bs)" by simp
    with inv1 have "is_canon_rewriter rword (set (p' # bs)) (lt p') p'"
      by (rule is_canon_rewriterI_eq_sig)
    thus "is_canon_rewriter rword (set (p' # bs)) (sig_of_pair p) p'" by (simp add: lt_p' sig_of_p)
  next
    from p'_irred have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set bs) p'"
      by (simp add: is_sig_red_top_tail_cases)
    with sig_irred_regular_self have "\<not> is_sig_red (\<prec>\<^sub>t) (=) ({p'} \<union> set bs) p'"
      by (simp add: is_sig_red_Un del: Un_insert_left)
    thus "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set (p' # bs)) (monom_mult 1 (pp_of_term (sig_of_pair p) - lp p') p')"
      by (simp add: lt_p' sig_of_p)
  qed
  show "rb_aux_inv (p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p')"
    unfolding rb_aux_inv.simps
  proof (intro conjI ballI allI impI)
    show "rb_aux_inv1 (p' # bs)" by (fact inv1)
  next
    fix s
    assume "s \<in> set (new_syz_sigs ss bs p)"
    with assms(1) show "is_syz_sig dgrad s" by (rule new_syz_sigs_is_syz_sig)
  next
    fix q1 q2
    assume "Inl (q1, q2) \<in> set (add_spairs ps bs p')"
    hence "Inl (q1, q2) \<in> set (new_spairs bs p') \<or> Inl (q1, q2) \<in> set (p # ps)"
      by (auto simp: add_spairs_def set_merge_wrt)
    hence "is_regular_spair q1 q2 \<and> q1 \<in> set (p' # bs) \<and> q2 \<in> set (p' # bs)"
    proof
      assume "Inl (q1, q2) \<in> set (new_spairs bs p')"
      hence "q1 = p'" and "q2 \<in> set bs" and "is_regular_spair p' q2" by (rule in_new_spairsD)+
      thus ?thesis by simp
    next
      assume "Inl (q1, q2) \<in> set (p # ps)"
      with assms(1) have "is_regular_spair q1 q2" and "q1 \<in> set bs" and "q2 \<in> set bs"
        by (rule rb_aux_inv_D3)+
      thus ?thesis by simp
    qed
    thus "is_regular_spair q1 q2" and "q1 \<in> set (p' # bs)" and "q2 \<in> set (p' # bs)" by simp_all
  next
    fix j
    assume "Inr j \<in> set (add_spairs ps bs p')"
    hence "Inr j \<in> set ps" by (simp add: add_spairs_def set_merge_wrt Inr_not_in_new_spairs)
    hence "Inr j \<in> set (p # ps)" by simp
    with assms(1) show "j < length fs" by (rule rb_aux_inv_D4)

    fix b
    assume "b \<in> set (p' # bs)"
    hence "b = p' \<or> b \<in> set bs" by simp
    thus "lt b \<prec>\<^sub>t term_of_pair (0, j)"
    proof
      assume "b = p'"
      hence "lt b = sig_of_pair p" by (simp only: lt_p' sig_of_p)
      also from \<open>Inr j \<in> set ps\<close> have "... \<prec>\<^sub>t term_of_pair (0, j)" by (rule sig_of_p_less)
      finally show ?thesis .
    next
      assume "b \<in> set bs"
      with assms(1) \<open>Inr j \<in> set (p # ps)\<close> show ?thesis by (rule rb_aux_inv_D4)
    qed
  next
    fix j
    assume "Inr j \<in> set (add_spairs ps bs p')"
    hence "Inr j \<in> set ps" by (simp add: add_spairs_def set_merge_wrt Inr_not_in_new_spairs)
    hence "Inr j \<in> set (p # ps)" by simp
    let ?P = "\<lambda>q. sig_of_pair q = term_of_pair (0, j)"
    have "filter ?P (add_spairs ps bs p') = filter ?P ps" unfolding add_spairs_def
    proof (rule filter_merge_wrt_2)
      fix q
      assume "q \<in> set (new_spairs bs p')"
      then obtain b where "b \<in> set bs" and "is_regular_spair p' b" and "q = Inl (p', b)"
        by (rule in_new_spairsE)
      moreover assume "sig_of_pair q = term_of_pair (0, j)"
      ultimately have "lt (spair p' b) = term_of_pair (0, j)"
        by (simp add: sig_of_spair del: sig_of_pair.simps)
      hence eq: "component_of_term (lt (spair p' b)) = j" by (simp add: component_of_term_of_pair)
      have "component_of_term (lt p') < j"
      proof (rule ccontr)
        assume "\<not> component_of_term (lt p') < j"
        hence "component_of_term (term_of_pair (0, j)) \<le> component_of_term (lt p')"
          by (simp add: component_of_term_of_pair)
        moreover have "pp_of_term (term_of_pair (0, j)) \<preceq> pp_of_term (lt p')"
          by (simp add: pp_of_term_of_pair zero_min)
        ultimately have "term_of_pair (0, j) \<preceq>\<^sub>t lt p'" using ord_termI by blast
        moreover have "lt p' \<prec>\<^sub>t term_of_pair (0, j)" unfolding lt_p' sig_of_p[symmetric]
          using \<open>Inr j \<in> set ps\<close> by (rule sig_of_p_less)
        ultimately show False by simp
      qed
      moreover have "component_of_term (lt b) < j"
      proof (rule ccontr)
        assume "\<not> component_of_term (lt b) < j"
        hence "component_of_term (term_of_pair (0, j)) \<le> component_of_term (lt b)"
          by (simp add: component_of_term_of_pair)
        moreover have "pp_of_term (term_of_pair (0, j)) \<preceq> pp_of_term (lt b)"
          by (simp add: pp_of_term_of_pair zero_min)
        ultimately have "term_of_pair (0, j) \<preceq>\<^sub>t lt b" using ord_termI by blast
        moreover from assms(1) \<open>Inr j \<in> set (p # ps)\<close> \<open>b \<in> set bs\<close>
        have "lt b \<prec>\<^sub>t term_of_pair (0, j)" by (rule rb_aux_inv_D4)
        ultimately show False by simp
      qed
      ultimately have "component_of_term (lt (spair p' b)) < j"
        using is_regular_spair_component_lt_cases[OF \<open>is_regular_spair p' b\<close>] by auto
      thus False by (simp add: eq)
    qed
    hence "length (filter ?P (add_spairs ps bs p')) \<le> length (filter ?P (p # ps))"
      by simp
    also from assms(1) \<open>Inr j \<in> set (p # ps)\<close> have "... \<le> 1" by (rule rb_aux_inv_D4)
    finally show "length (filter ?P (add_spairs ps bs p')) \<le> 1" .
  next
    from assms(1) have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
    hence "sorted_wrt pair_ord ps" by simp
    thus "sorted_wrt pair_ord (add_spairs ps bs p')" by (rule sorted_add_spairs)
  next
    fix q b1 b2
    assume 1: "q \<in> set (add_spairs ps bs p')" and 2: "is_regular_spair b1 b2"
      and 3: "sig_of_pair q \<prec>\<^sub>t lt (spair b1 b2)"
    assume "b1 \<in> set (p' # bs)" and "b2 \<in> set (p' # bs)"
    hence "b1 = p' \<or> b1 \<in> set bs" and "b2 = p' \<or> b2 \<in> set bs" by simp_all
    thus "Inl (b1, b2) \<in> set (add_spairs ps bs p') \<or> Inl (b2, b1) \<in> set (add_spairs ps bs p')"
    proof (elim disjE)
      assume "b1 = p'" and "b2 = p'"
      with 2 show ?thesis by (simp add: is_regular_spair_def)
    next
      assume "b1 = p'" and "b2 \<in> set bs"
      from this(2) 2 have "Inl (b1, b2) \<in> set (new_spairs bs p')" unfolding \<open>b1 = p'\<close>
        by (rule in_new_spairsI)
      with 2 show ?thesis by (simp add: sig_of_spair add_spairs_def set_merge_wrt image_Un del: sig_of_pair.simps)
    next
      assume "b2 = p'" and "b1 \<in> set bs"
      note this(2)
      moreover from 2 have "is_regular_spair b2 b1" by (rule is_regular_spair_sym)
      ultimately have "Inl (b2, b1) \<in> set (new_spairs bs p')" unfolding \<open>b2 = p'\<close>
        by (rule in_new_spairsI)
      with 2 show ?thesis
        by (simp add: sig_of_spair_commute sig_of_spair add_spairs_def set_merge_wrt image_Un del: sig_of_pair.simps)
    next
      note assms(1) \<open>p \<in> set (p # ps)\<close>
      moreover assume "b1 \<in> set bs" and "b2 \<in> set bs"
      moreover note 2
      moreover have 4: "sig_of_pair p \<prec>\<^sub>t lt (spair b1 b2)"
        by (rule ord_term_lin.le_less_trans, rule sig_merge, fact 1, fact 3)
      ultimately show ?thesis
      proof (rule rb_aux_inv_D6_1)
        assume "Inl (b1, b2) \<in> set (p # ps)"
        with 4 have "Inl (b1, b2) \<in> set ps"
          by (auto simp: sig_of_spair \<open>is_regular_spair b1 b2\<close> simp del: sig_of_pair.simps)
        thus ?thesis by (simp add: add_spairs_def set_merge_wrt)
      next
        assume "Inl (b2, b1) \<in> set (p # ps)"
        with 4 have "Inl (b2, b1) \<in> set ps"
          by (auto simp: sig_of_spair sig_of_spair_commute \<open>is_regular_spair b1 b2\<close> simp del: sig_of_pair.simps)
        thus ?thesis by (simp add: add_spairs_def set_merge_wrt)
      qed
    qed
  next
    fix q j
    assume "j < length fs"
    assume "q \<in> set (add_spairs ps bs p')"
    hence "sig_of_pair p \<preceq>\<^sub>t sig_of_pair q" by (rule sig_merge)
    also assume "sig_of_pair q \<prec>\<^sub>t term_of_pair (0, j)"
    finally have 1: "sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j)" .
    with assms(1) \<open>p \<in> set (p # ps)\<close> \<open>j < length fs\<close> have "Inr j \<in> set (p # ps)"
      by (rule rb_aux_inv_D6_2)
    with 1 show "Inr j \<in> set (add_spairs ps bs p')" by (auto simp: add_spairs_def set_merge_wrt)
  next
    fix b q
    assume "b \<in> set (p' # bs)" and q_in: "q \<in> set (add_spairs ps bs p')"
    from this(1) have "b = p' \<or> b \<in> set bs" by simp
    hence "lt b \<preceq>\<^sub>t lt p'"
    proof
      note assms(1)
      moreover assume "b \<in> set bs"
      moreover have "p \<in> set (p # ps)" by simp
      ultimately have "lt b \<preceq>\<^sub>t sig_of_pair p" by (rule rb_aux_inv_D7)
      thus ?thesis by (simp only: lt_p' sig_of_p)
    qed simp
    also have "... = sig_of_pair p" by (simp only: sig_of_p lt_p')
    also from q_in have "... \<preceq>\<^sub>t sig_of_pair q" by (rule sig_merge)
    finally show "lt b \<preceq>\<^sub>t sig_of_pair q" .
  next
    fix a b
    assume 1: "a \<in> set (p' # bs)" and 2: "b \<in> set (p' # bs)" and 3: "is_regular_spair a b"
    assume 6: "\<not> is_RB_in dgrad rword (set (p' # bs)) (lt (spair a b))"
    with rb have neq: "lt (spair a b) \<noteq> lt (poly_of_pair p)" by (auto simp: sig_of_p)
    assume "Inl (a, b) \<notin> set (add_spairs ps bs p')"
    hence 40: "Inl (a, b) \<notin> set (new_spairs bs p')" and "Inl (a, b) \<notin> set ps"
      by (simp_all add: add_spairs_def set_merge_wrt)
    from this(2) neq have 4: "Inl (a, b) \<notin> set (p # ps)" by auto
    assume "Inl (b, a) \<notin> set (add_spairs ps bs p')"
    hence 50: "Inl (b, a) \<notin> set (new_spairs bs p')" and "Inl (b, a) \<notin> set ps"
      by (simp_all add: add_spairs_def set_merge_wrt)
    from this(2) neq have 5: "Inl (b, a) \<notin> set (p # ps)" by (auto simp: spair_comm[of a])
    have "a \<noteq> p'"
    proof
      assume "a = p'"
      with 3 have "b \<noteq> p'" by (auto simp: is_regular_spair_def)
      with 2 have "b \<in> set bs" by simp
      hence "Inl (a, b) \<in> set (new_spairs bs p')" using 3 unfolding \<open>a = p'\<close> by (rule in_new_spairsI)
      with 40 show False ..
    qed
    with 1 have "a \<in> set bs" by simp
    have "b \<noteq> p'"
    proof
      assume "b = p'"
      with 3 have "a \<noteq> p'" by (auto simp: is_regular_spair_def)
      with 1 have "a \<in> set bs" by simp
      moreover from 3 have "is_regular_spair b a" by (rule is_regular_spair_sym)
      ultimately have "Inl (b, a) \<in> set (new_spairs bs p')" unfolding \<open>b = p'\<close> by (rule in_new_spairsI)
      with 50 show False ..
    qed
    with 2 have "b \<in> set bs" by simp
    have lt_sp: "lt (spair a b) \<prec>\<^sub>t lt p'"
    proof (rule ord_term_lin.linorder_cases)
      assume "lt (spair a b) = lt p'"
      with neq show ?thesis by (simp add: lt_p')
    next
      assume "lt p' \<prec>\<^sub>t lt (spair a b)"
      hence "sig_of_pair p \<prec>\<^sub>t lt (spair a b)" by (simp only: lt_p' sig_of_p)
      with assms(1) \<open>p \<in> set (p # ps)\<close> \<open>a \<in> set bs\<close> \<open>b \<in> set bs\<close> 3 show ?thesis
      proof (rule rb_aux_inv_D6_1)
        assume "Inl (a, b) \<in> set (p # ps)"
        with 4 show ?thesis ..
      next
        assume "Inl (b, a) \<in> set (p # ps)"
        with 5 show ?thesis ..
      qed
    qed
    have "\<not> is_RB_in dgrad rword (set bs) (lt (spair a b))"
    proof
      assume "is_RB_in dgrad rword (set bs) (lt (spair a b))"
      hence "is_RB_in dgrad rword (set (p' # bs)) (lt (spair a b))" unfolding set_simps using lt_sp
        by (rule is_RB_in_insertI)
      with 6 show False ..
    qed
    with assms(1) \<open>a \<in> set bs\<close> \<open>b \<in> set bs\<close> 3 4 5
    obtain q where "q \<in> set (p # ps)" and 8: "sig_of_pair q = lt (spair a b)" and 9: "\<not> sig_crit' bs q"
      by (rule rb_aux_inv_D8)
    from this(1, 2) lt_sp have "q \<in> set ps" by (auto simp: lt_p' sig_of_p)
    show "\<exists>q\<in>set (add_spairs ps bs p'). sig_of_pair q = lt (spair a b) \<and> \<not> sig_crit' (p' # bs) q"
    proof (intro bexI conjI)
      show "\<not> sig_crit' (p' # bs) q"
      proof
        assume "sig_crit' (p' # bs) q"
        moreover from lt_sp have "sig_of_pair q \<prec>\<^sub>t lt p'" by (simp only: 8)
        ultimately have "sig_crit' bs q" by (rule sig_crit'_ConsD)
        with 9 show False ..
      qed
    next
      from \<open>q \<in> set ps\<close> show "q \<in> set (add_spairs ps bs p')" by (simp add: add_spairs_def set_merge_wrt)
    qed fact
  next
    fix j
    assume "j < length fs"
    assume "Inr j \<notin> set (add_spairs ps bs p')"
    hence "Inr j \<notin> set ps" by (simp add: add_spairs_def set_merge_wrt)

    show "is_RB_in dgrad rword (set (p' # bs)) (term_of_pair (0, j))"
    proof (cases "term_of_pair (0, j) = sig_of_pair p")
      case True
      with rb show ?thesis by simp
    next
      case False
      with \<open>Inr j \<notin> set ps\<close> have "Inr j \<notin> set (p # ps)" by auto
      with assms(1) \<open>j < length fs\<close> have rb': "is_RB_in dgrad rword (set bs) (term_of_pair (0, j))"
        by (rule rb_aux_inv_D9)
      have "term_of_pair (0, j) \<prec>\<^sub>t lt p'"
      proof (rule ord_term_lin.linorder_cases)
        assume "term_of_pair (0, j) = lt p'"
        with False show ?thesis by (simp add: lt_p' sig_of_p)
      next
        assume "lt p' \<prec>\<^sub>t term_of_pair (0, j)"
        hence "sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j)" by (simp only: lt_p' sig_of_p)
        with assms(1) \<open>p \<in> set (p # ps)\<close> \<open>j < length fs\<close> have "Inr j \<in> set (p # ps)"
          by (rule rb_aux_inv_D6_2)
        with \<open>Inr j \<notin> set (p # ps)\<close> show ?thesis ..
      qed
      with rb' show ?thesis unfolding set_simps by (rule is_RB_in_insertI)
    qed

    show "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set (p' # bs))"
    proof (cases "p = Inr j")
      case True
      show ?thesis
      proof (rule sig_red_zero_idealI, rule sig_red_zeroI)
        from p_red have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
          by (simp add: True)
        moreover have "set bs \<subseteq> set (p' # bs)" by fastforce
        ultimately have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
          by (rule sig_red_rtrancl_mono)
        hence "(sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
          by (rule sig_red_rtrancl_sing_regI)
        also have "sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)) p' 0" unfolding sig_red_def
        proof (intro exI bexI)
          from assms(3) have "rep_list p' \<noteq> 0" by (simp add: p'_def)
          show "sig_red_single (\<preceq>\<^sub>t) (\<preceq>) p' 0 p' 0"
          proof (rule sig_red_singleI)
            show "rep_list p' \<noteq> 0" by fact
          next
            from \<open>rep_list p' \<noteq> 0\<close> have "punit.lt (rep_list p') \<in> keys (rep_list p')"
              by (rule punit.lt_in_keys)
            thus "0 + punit.lt (rep_list p') \<in> keys (rep_list p')" by simp
          next
            from \<open>rep_list p' \<noteq> 0\<close> have "punit.lc (rep_list p') \<noteq> 0" by (rule punit.lc_not_0)
            thus "0 = p' - monom_mult (lookup (rep_list p') (0 + punit.lt (rep_list p')) / punit.lc (rep_list p')) 0 p'"
              by (simp add: punit.lc_def[symmetric])
          qed (simp_all add: term_simps)
        qed simp
        finally show "(sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) 0" .
      qed (fact rep_list_zero)
    next
      case False
      with \<open>Inr j \<notin> set ps\<close> have "Inr j \<notin> set (p # ps)" by simp
      with assms(1) \<open>j < length fs\<close>
      have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` set bs)"
        by (rule rb_aux_inv_D9)
      also have "... \<subseteq> ideal (rep_list ` set (p' # bs))" by (rule ideal.span_mono, fastforce)
      finally show ?thesis .
    qed
  qed

  show "lt p' \<notin> lt ` set bs" unfolding lt_p'
  proof
    assume "lt (poly_of_pair p) \<in> lt ` set bs"
    then obtain b where "b \<in> set bs" and "lt (poly_of_pair p) = lt b" ..
    note this(2)
    also from \<open>b \<in> set bs\<close> have "lt b \<prec>\<^sub>t lt (poly_of_pair p)" by (rule lt_p_gr)
    finally show False ..
  qed
qed

lemma rb_aux_inv_init: "rb_aux_inv ([], Koszul_syz_sigs fs, map Inr [0..<length fs])"
proof (simp add: rb_aux_inv.simps rb_aux_inv1_def o_def, intro conjI ballI allI impI)
  fix v
  assume "v \<in> set (Koszul_syz_sigs fs)"
  with dgrad fs_distinct fs_nonzero show "is_syz_sig dgrad v" by (rule Koszul_syz_sigs_is_syz_sig)
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  show "Inl (p, q) \<notin> Inr ` {0..<length fs}" by blast
next
  fix j
  assume "Inr j \<in> Inr ` {0..<length fs}"
  thus "j < length fs" by fastforce
next
  fix j
  have eq: "(term_of_pair (0, i) = term_of_pair (0, j)) \<longleftrightarrow> (j = i)" for i
    by (auto dest: term_of_pair_injective)
  show "length (filter (\<lambda>i. term_of_pair (0, i) = term_of_pair (0, j)) [0..<length fs]) \<le> Suc 0"
    by (simp add: eq)
next
  show "sorted_wrt pair_ord (map Inr [0..<length fs])"
  proof (simp add: sorted_wrt_map pair_ord_def sorted_wrt_upt_iff, intro allI impI)
    fix i j :: nat
    assume "i < j"
    hence "i \<le> j" by simp
    show "term_of_pair (0, i) \<preceq>\<^sub>t term_of_pair (0, j)" by (rule ord_termI, simp_all add: term_simps \<open>i \<le> j\<close>)
  qed
qed

corollary rb_aux_inv_init_fst:
  "rb_aux_inv (fst (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))"
  using rb_aux_inv_init by simp

function (domintros) rb_aux :: "((('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list) \<times> nat) \<Rightarrow>
                                    ((('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list) \<times> nat)"
  where
    "rb_aux ((bs, ss, []), z) = ((bs, ss, []), z)" |
    "rb_aux ((bs, ss, p # ps), z) =
      (let ss' = new_syz_sigs ss bs p in
        if sig_crit bs ss' p then
          rb_aux ((bs, ss', ps), z)
        else
          let p' = sig_trd bs (poly_of_pair p) in
            if rep_list p' = 0 then
              rb_aux ((bs, lt p' # ss', ps), Suc z)
            else
              rb_aux ((p' # bs, ss', add_spairs ps bs p'), z))"
  by pat_completeness auto

definition rb :: "('t \<Rightarrow>\<^sub>0 'b) list \<times> nat"
  where "rb = (let ((bs, _, _), z) = rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), 0) in (bs, z))"

text \<open>@{const rb} is only an auxiliary function used for stating some theorems about rewrite bases
  and their computation in a readable way. Actual computations (of Gr\"obner bases) are performed
  by function \<open>sig_gb\<close>, defined below.
  The second return value of @{const rb} is the number of zero-reductions. It is only needed for
  proving that under certain assumptions, there are no such zero-reductions.\<close>

text \<open>Termination\<close>

qualified definition "rb_aux_term1 \<equiv> {(x, y). \<exists>z. x = z # y}"

qualified definition "rb_aux_term2 \<equiv> {(x, y). (fst x, fst y) \<in> rb_aux_term1 \<or>
                    (fst x = fst y \<and> length (snd (snd x)) < length (snd (snd y)))}"

qualified definition "rb_aux_term \<equiv> rb_aux_term2 \<inter> {(x, y). rb_aux_inv x \<and> rb_aux_inv y}"

lemma wfp_on_rb_aux_term1: "wfp_on (\<lambda>x y. (x, y) \<in> rb_aux_term1) (Collect rb_aux_inv1)"
proof (rule wfp_onI_chain, rule, elim exE)
  fix seq'
  assume "\<forall>i. seq' i \<in> Collect rb_aux_inv1 \<and> (seq' (Suc i), seq' i) \<in> rb_aux_term1"
  hence inv: "rb_aux_inv1 (seq' j)" and cons: "\<exists>b. seq' (Suc j) = b # seq' j" for j
    by (simp_all add: rb_aux_term1_def)
  from this(2) have 1: thesis0 if "\<And>j. i < length (seq' j) \<Longrightarrow> thesis0" for i thesis0
    using that by (rule list_seq_indexE_length)

  define seq where "seq = (\<lambda>i. let j = (SOME k. i < length (seq' k)) in rev (seq' j) ! i)"
  have 2: "seq i = rev (seq' j) ! i" if "i < length (seq' j)" for i j
  proof -
    define k where "k = (SOME k. i < length (seq' k))"
    from that have "i < length (seq' k)" unfolding k_def by (rule someI)
    with cons that have "rev (seq' k) ! i = rev (seq' j) ! i" by (rule list_seq_nth')
    thus ?thesis by (simp add: seq_def k_def[symmetric])
  qed
  have 3: "seq i \<in> set (seq' j)" if "i < length (seq' j)" for i j
  proof -
    from that have "i < length (rev (seq' j))" by simp
    moreover from that have "seq i = rev (seq' j) ! i" by (rule 2)
    ultimately have "seq i \<in> set (rev (seq' j))" by (metis nth_mem)
    thus ?thesis by simp
  qed
  have 4: "seq ` {0..<i} = set (take i (rev (seq' j)))" if "i < length (seq' j)" for i j
  proof -
    from refl have "seq ` {0..<i} = (!) (rev (seq' j)) ` {0..<i}"
    proof (rule image_cong)
      fix i'
      assume "i' \<in> {0..<i}"
      hence "i' < i" by simp
      hence "i' < length (seq' j)" using that by simp
      thus "seq i' = rev (seq' j) ! i'" by (rule 2)
    qed
    also have "... = set (take i (rev (seq' j)))" by (rule nth_image, simp add: that less_imp_le_nat)
    finally show ?thesis .
  qed
  from dgrad show False
  proof (rule rb_termination)
    have "seq i \<in> dgrad_sig_set dgrad" for i
    proof -
      obtain j where "i < length (seq' j)" by (rule 1)
      hence "seq i \<in> set (seq' j)" by (rule 3)
      moreover from inv have "set (seq' j) \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
      ultimately show ?thesis ..
    qed
    thus "range seq \<subseteq> dgrad_sig_set dgrad" by blast
  next
    have "rep_list (seq i) \<noteq> 0" for i
    proof -
      obtain j where "i < length (seq' j)" by (rule 1)
      hence "seq i \<in> set (seq' j)" by (rule 3)
      moreover from inv have "0 \<notin> rep_list ` set (seq' j)" by (rule rb_aux_inv1_D2)
      ultimately show ?thesis by auto
    qed
    thus "0 \<notin> rep_list ` range seq" by fastforce
  next
    fix i1 i2 :: nat
    assume "i1 < i2"
    also obtain j where i2: "i2 < length (seq' j)" by (rule 1)
    finally have i1: "i1 < length (seq' j)" .
    from i1 have s1: "seq i1 = rev (seq' j) ! i1" by (rule 2)
    from i2 have s2: "seq i2 = rev (seq' j) ! i2" by (rule 2)
    from inv have "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) (seq' j)" by (rule rb_aux_inv1_D3)
    hence "sorted_wrt (\<lambda>x y. lt x \<prec>\<^sub>t lt y) (rev (seq' j))" by (simp add: sorted_wrt_rev)
    moreover note \<open>i1 < i2\<close>
    moreover from i2 have "i2 < length (rev (seq' j))" by simp
    ultimately have "lt (rev (seq' j) ! i1) \<prec>\<^sub>t lt (rev (seq' j) ! i2)" by (rule sorted_wrt_nth_less)
    thus "lt (seq i1) \<prec>\<^sub>t lt (seq i2)" by (simp only: s1 s2)
  next
    fix i
    obtain j where i: "i < length (seq' j)" by (rule 1)
    hence eq1: "seq i = rev (seq' j) ! i" and eq2: "seq ` {0..<i} = set (take i (rev (seq' j)))"
      by (rule 2, rule 4)
    let ?i = "length (seq' j) - Suc i"
    from i have "?i < length (seq' j)" by simp
    with inv have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set (drop (Suc ?i) (seq' j))) ((seq' j) ! ?i)"
      by (rule rb_aux_inv1_D4)
    thus "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}) (seq i)"
      using i by (simp add: eq1 eq2 rev_nth take_rev Suc_diff_Suc)
 
    from inv \<open>?i < length (seq' j)\<close>
    show "(\<exists>j<length fs. lt (seq i) = lt (monomial (1::'b) (term_of_pair (0, j))) \<and>
             punit.lt (rep_list (seq i)) \<preceq> punit.lt (rep_list (monomial 1 (term_of_pair (0, j))))) \<or>
         (\<exists>j k. is_regular_spair (seq j) (seq k) \<and> rep_list (spair (seq j) (seq k)) \<noteq> 0 \<and>
                lt (seq i) = lt (spair (seq j) (seq k)) \<and>
                punit.lt (rep_list (seq i)) \<preceq> punit.lt (rep_list (spair (seq j) (seq k))))" (is "?l \<or> ?r")
    proof (rule rb_aux_inv1_E)
      fix j0
      assume "j0 < length fs"
        and "lt (seq' j ! (length (seq' j) - Suc i)) = lt (monomial (1::'b) (term_of_pair (0, j0)))"
        and "punit.lt (rep_list (seq' j ! (length (seq' j) - Suc i))) \<preceq>
             punit.lt (rep_list (monomial 1 (term_of_pair (0, j0))))"
      hence ?l using i by (auto simp: eq1 eq2 rev_nth take_rev Suc_diff_Suc)
      thus ?thesis ..
    next
      fix p q
      assume "p \<in> set (seq' j)"
      then obtain pi where "pi < length (seq' j)" and "p = (seq' j) ! pi" by (metis in_set_conv_nth)
      hence p: "p = seq (length (seq' j) - Suc pi)"
        by (metis "2" \<open>p \<in> set (seq' j)\<close> diff_Suc_less length_pos_if_in_set length_rev rev_nth rev_rev_ident)
      assume "q \<in> set (seq' j)"
      then obtain qi where "qi < length (seq' j)" and "q = (seq' j) ! qi" by (metis in_set_conv_nth)
      hence q: "q = seq (length (seq' j) - Suc qi)"
        by (metis "2" \<open>q \<in> set (seq' j)\<close> diff_Suc_less length_pos_if_in_set length_rev rev_nth rev_rev_ident)
      assume "is_regular_spair p q" and "rep_list (spair p q) \<noteq> 0"
        and "lt (seq' j ! (length (seq' j) - Suc i)) = lt (spair p q)"
        and "punit.lt (rep_list (seq' j ! (length (seq' j) - Suc i))) \<preceq> punit.lt (rep_list (spair p q))"
      hence ?r using i by (auto simp: eq1 eq2 p q rev_nth take_rev Suc_diff_Suc)
      thus ?thesis ..
    qed

    from inv \<open>?i < length (seq' j)\<close>
    have "is_RB_upt dgrad rword (set (drop (Suc ?i) (seq' j))) (lt ((seq' j) ! ?i))"
      by (rule rb_aux_inv1_D5)
    with dgrad have "is_sig_GB_upt dgrad (set (drop (Suc ?i) (seq' j))) (lt ((seq' j) ! ?i))"
      by (rule is_RB_upt_is_sig_GB_upt)
    thus "is_sig_GB_upt dgrad (seq ` {0..<i}) (lt (seq i))"
      using i by (simp add: eq1 eq2 rev_nth take_rev Suc_diff_Suc)
  qed
qed

lemma wfp_on_rb_aux_term2: "wfp_on (\<lambda>x y. (x, y) \<in> rb_aux_term2) (Collect rb_aux_inv)"
proof (rule wfp_onI_min)
  fix x Q
  assume "x \<in> Q" and Q_sub: "Q \<subseteq> Collect rb_aux_inv"
  from this(1) have "fst x \<in> fst ` Q" by (rule imageI)
  have "fst ` Q \<subseteq> Collect rb_aux_inv1"
  proof
    fix y
    assume "y \<in> fst ` Q"
    then obtain z where "z \<in> Q" and y: "y = fst z" by fastforce
    obtain bs ss ps where z: "z = (bs, ss, ps)" by (rule rb_aux_inv.cases)
    from \<open>z \<in> Q\<close> Q_sub have "rb_aux_inv z" by blast
    thus "y \<in> Collect rb_aux_inv1" by (simp add: y z rb_aux_inv.simps)
  qed
  with wfp_on_rb_aux_term1 \<open>fst x \<in> fst ` Q\<close> obtain z' where "z' \<in> fst ` Q"
    and z'_min: "\<And>y. (y, z') \<in> rb_aux_term1 \<Longrightarrow> y \<notin> fst ` Q" by (rule wfp_onE_min) blast
  from this(1) obtain z0 where "z0 \<in> Q" and z': "z' = fst z0" by fastforce
  define Q0 where "Q0 = {z. z \<in> Q \<and> fst z = fst z0}"
  from \<open>z0 \<in> Q\<close> have "z0 \<in> Q0" by (simp add: Q0_def)
  hence "length (snd (snd z0)) \<in> length ` snd ` snd ` Q0" by (intro imageI)
  with wf_less obtain n where n1: "n \<in> length ` snd ` snd ` Q0"
    and n2: "\<And>n'. n' < n \<Longrightarrow> n' \<notin> length ` snd ` snd ` Q0" by (rule wfE_min, blast)
  from n1 obtain z where "z \<in> Q0" and n3: "n = length (snd (snd z))" by fastforce
  have z_min: "y \<notin> Q0" if "length (snd (snd y)) < length (snd (snd z))" for y
  proof
    assume "y \<in> Q0"
    hence "length (snd (snd y)) \<in> length ` snd ` snd ` Q0" by (intro imageI)
    with n2 have "\<not> length (snd (snd y)) < length (snd (snd z))" unfolding n3[symmetric] by blast
    thus False using that ..
  qed
  show "\<exists>z\<in>Q. \<forall>y\<in>Collect rb_aux_inv. (y, z) \<in> rb_aux_term2 \<longrightarrow> y \<notin> Q"
  proof (intro bexI ballI impI)
    fix y
    assume "y \<in> Collect rb_aux_inv"
    assume "(y, z) \<in> rb_aux_term2"
    hence "(fst y, fst z) \<in> rb_aux_term1 \<or> (fst y = fst z \<and> length (snd (snd y)) < length (snd (snd z)))"
      by (simp add: rb_aux_term2_def)
    thus "y \<notin> Q"
    proof
      assume "(fst y, fst z) \<in> rb_aux_term1"
      moreover from \<open>z \<in> Q0\<close> have "fst z = fst z0" by (simp add: Q0_def)
      ultimately have "(fst y, z') \<in> rb_aux_term1" by (simp add: rb_aux_term1_def z')
      hence "fst y \<notin> fst ` Q" by (rule z'_min)
      thus ?thesis by blast
    next
      assume "fst y = fst z \<and> length (snd (snd y)) < length (snd (snd z))"
      hence "fst y = fst z" and "length (snd (snd y)) < length (snd (snd z))" by simp_all
      from this(2) have "y \<notin> Q0" by (rule z_min)
      moreover from \<open>z \<in> Q0\<close> have "fst y = fst z0" by (simp add: Q0_def \<open>fst y = fst z\<close>)
      ultimately show ?thesis by (simp add: Q0_def)
    qed
  next
    from \<open>z \<in> Q0\<close> show "z \<in> Q" by (simp add: Q0_def)
  qed
qed

corollary wf_rb_aux_term: "wf rb_aux_term"
proof (rule wfI_min)
  fix x::"('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list" and Q
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> rb_aux_term \<longrightarrow> y \<notin> Q"
  proof (cases "rb_aux_inv x")
    case True
    let ?Q = "Q \<inter> Collect rb_aux_inv"
    note wfp_on_rb_aux_term2
    moreover from \<open>x \<in> Q\<close> True have "x \<in> ?Q" by simp
    moreover have "?Q \<subseteq> Collect rb_aux_inv" by simp
    ultimately obtain z where "z \<in> ?Q" and z_min: "\<And>y. (y, z) \<in> rb_aux_term2 \<Longrightarrow> y \<notin> ?Q"
      by (rule wfp_onE_min) blast
    show ?thesis
    proof (intro bexI allI impI)
      fix y
      assume "(y, z) \<in> rb_aux_term"
      hence "(y, z) \<in> rb_aux_term2" and "rb_aux_inv y" by (simp_all add: rb_aux_term_def)
      from this(1) have "y \<notin> ?Q" by (rule z_min)
      with \<open>rb_aux_inv y\<close> show "y \<notin> Q" by simp
    next
      from \<open>z \<in> ?Q\<close> show "z \<in> Q" by simp
    qed
  next
    case False
    show ?thesis
    proof (intro bexI allI impI)
      fix y
      assume "(y, x) \<in> rb_aux_term"
      hence "rb_aux_inv x" by (simp add: rb_aux_term_def)
      with False show "y \<notin> Q" ..
    qed fact
  qed
qed

lemma rb_aux_domI:
  assumes "rb_aux_inv (fst args)"
  shows "rb_aux_dom args"
proof -
  let ?rel = "rb_aux_term <*lex*> ({}::(nat \<times> nat) set)"
  from wf_rb_aux_term wf_empty have "wf ?rel" ..
  thus ?thesis using assms
  proof (induct args)
    case (less args)
    obtain bs ss ps0 z where args: "args = ((bs, ss, ps0), z)" using prod.exhaust by metis
    show ?case
    proof (cases ps0)
      case Nil
      show ?thesis unfolding args Nil by (rule rb_aux.domintros)
    next
      case (Cons p ps)
      from less(1) have 1: "\<And>y. (y, ((bs, ss, p # ps), z)) \<in> ?rel \<Longrightarrow> rb_aux_inv (fst y) \<Longrightarrow> rb_aux_dom y"
        by (simp only: args Cons)
      from less(2) have 2: "rb_aux_inv (bs, ss, p # ps)" by (simp only: args Cons fst_conv)
      show ?thesis unfolding args Cons
      proof (rule rb_aux.domintros)
        assume "sig_crit bs (new_syz_sigs ss bs p) p"
        with 2 have a: "rb_aux_inv (bs, (new_syz_sigs ss bs p), ps)" by (rule rb_aux_inv_preserved_1)
        with 2 have "((bs, (new_syz_sigs ss bs p), ps), bs, ss, p # ps) \<in> rb_aux_term"
          by (simp add: rb_aux_term_def rb_aux_term2_def)
        hence "(((bs, (new_syz_sigs ss bs p), ps), z), (bs, ss, p # ps), z) \<in> ?rel" by simp
        moreover from a have "rb_aux_inv (fst ((bs, (new_syz_sigs ss bs p), ps), z))"
          by (simp only: fst_conv)
        ultimately show "rb_aux_dom ((bs, (new_syz_sigs ss bs p), ps), z)" by (rule 1)
      next
        assume "rep_list (sig_trd bs (poly_of_pair p)) = 0"
        with 2 have a: "rb_aux_inv (bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps)"
          by (rule rb_aux_inv_preserved_2)
        with 2 have "((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), bs, ss, p # ps) \<in>
                      rb_aux_term"
          by (simp add: rb_aux_term_def rb_aux_term2_def)
        hence "(((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z), (bs, ss, p # ps), z) \<in>
                      ?rel" by simp
        moreover from a have "rb_aux_inv (fst ((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z))"
          by (simp only: fst_conv)
        ultimately show "rb_aux_dom ((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z)"
          by (rule 1)
      next
        let ?args = "(sig_trd bs (poly_of_pair p) # bs, new_syz_sigs ss bs p, add_spairs ps bs (sig_trd bs (poly_of_pair p)))"
        assume "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
        with 2 have a: "rb_aux_inv ?args" by (rule rb_aux_inv_preserved_3)
        with 2 have "(?args, bs, ss, p # ps) \<in> rb_aux_term"
          by (simp add: rb_aux_term_def rb_aux_term2_def rb_aux_term1_def)
        hence "((?args, z), (bs, ss, p # ps), z) \<in> ?rel" by simp
        moreover from a have "rb_aux_inv (fst (?args, z))" by (simp only: fst_conv)
        ultimately show "rb_aux_dom (?args, z)" by (rule 1)
      qed
    qed
  qed
qed

text \<open>Invariant\<close>

lemma rb_aux_inv_invariant:
  assumes "rb_aux_inv (fst args)"
  shows "rb_aux_inv (fst (rb_aux args))"
proof -
  from assms have "rb_aux_dom args" by (rule rb_aux_domI)
  thus ?thesis using assms
  proof (induct args rule: rb_aux.pinduct)
    case (1 bs ss z)
    thus ?case by (simp only: rb_aux.psimps(1))
  next
    case (2 bs ss p ps z)
    from 2(5) have *: "rb_aux_inv (bs, ss, p # ps)" by (simp only: fst_conv)
    show ?case
    proof (simp add: rb_aux.psimps(2)[OF 2(1)] Let_def, intro conjI impI)
      assume a: "sig_crit bs (new_syz_sigs ss bs p) p"
      with * have "rb_aux_inv (bs, new_syz_sigs ss bs p, ps)"
        by (rule rb_aux_inv_preserved_1)
      hence "rb_aux_inv (fst ((bs, new_syz_sigs ss bs p, ps), z))" by (simp only: fst_conv)
      with refl a show "rb_aux_inv (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)))" by (rule 2(2))
      thus "rb_aux_inv (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)))" .
    next
      assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
      assume b: "rep_list (sig_trd bs (poly_of_pair p)) = 0"
      with * have "rb_aux_inv (bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps)"
        by (rule rb_aux_inv_preserved_2)
      hence "rb_aux_inv (fst ((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z))"
        by (simp only: fst_conv)
      with refl a refl b
      show "rb_aux_inv (fst (rb_aux ((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z)))"
        by (rule 2(3))
    next
      let ?args = "(sig_trd bs (poly_of_pair p) # bs, new_syz_sigs ss bs p,
                       add_spairs ps bs (sig_trd bs (poly_of_pair p)))"
      assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and b: "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
      with * have "rb_aux_inv ?args" by (rule rb_aux_inv_preserved_3)
      hence "rb_aux_inv (fst (?args, z))" by (simp only: fst_conv)
      with refl a refl b
      show "rb_aux_inv (fst (rb_aux (?args, z)))"
        by (rule 2(4))
    qed
  qed
qed

lemma rb_aux_inv_last_Nil:
  assumes "rb_aux_dom args"
  shows "snd (snd (fst (rb_aux args))) = []"
  using assms
proof (induct args rule: rb_aux.pinduct)
  case (1 bs ss z)
  thus ?case by (simp add: rb_aux.psimps(1))
next
  case (2 bs ss p ps z)
  show ?case
  proof (simp add: rb_aux.psimps(2)[OF 2(1)] Let_def, intro conjI impI)
    assume "sig_crit bs (new_syz_sigs ss bs p) p"
    with refl show "snd (snd (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)))) = []"
      and "snd (snd (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)))) = []"
      by (rule 2(2))+
  next
    assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and b: "rep_list (sig_trd bs (poly_of_pair p)) = 0"
    from refl a refl b
    show "snd (snd (fst (rb_aux ((bs, lt (sig_trd bs (poly_of_pair p)) # new_syz_sigs ss bs p, ps), Suc z)))) = []"
      by (rule 2(3))
  next
    assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and b: "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
    from refl a refl b
    show "snd (snd (fst (rb_aux ((sig_trd bs (poly_of_pair p) # bs, new_syz_sigs ss bs p,
                                add_spairs ps bs (sig_trd bs (poly_of_pair p))), z)))) = []"
      by (rule 2(4))
  qed
qed

corollary rb_aux_shape:
  assumes "rb_aux_dom args"
  obtains bs ss z where "rb_aux args = ((bs, ss, []), z)"
proof -
  obtain bs ss ps z where "rb_aux args = ((bs, ss, ps), z)" using prod.exhaust by metis
  moreover from assms have "snd (snd (fst (rb_aux args))) = []" by (rule rb_aux_inv_last_Nil)
  ultimately have "rb_aux args = ((bs, ss, []), z)" by simp
  thus ?thesis ..
qed

lemma rb_aux_is_RB_upt:
  "is_RB_upt dgrad rword (set (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))) u"
proof -
  let ?args = "(([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)"
  from rb_aux_inv_init_fst have "rb_aux_dom ?args" by (rule rb_aux_domI)
  then obtain bs ss z' where eq: "rb_aux ?args = ((bs, ss, []), z')" by (rule rb_aux_shape)
  moreover from rb_aux_inv_init_fst have "rb_aux_inv (fst (rb_aux ?args))"
    by (rule rb_aux_inv_invariant)
  ultimately have "rb_aux_inv (bs, ss, [])" by simp
  have "is_RB_upt dgrad rword (set bs) u" by (rule rb_aux_inv_is_RB_upt, fact, simp)
  thus ?thesis by (simp add: eq)
qed

corollary rb_is_RB_upt: "is_RB_upt dgrad rword (set (fst rb)) u"
  using rb_aux_is_RB_upt[of 0 u] by (auto simp add: rb_def split: prod.split)

corollary rb_aux_is_sig_GB_upt:
  "is_sig_GB_upt dgrad (set (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))) u"
  using dgrad rb_aux_is_RB_upt by (rule is_RB_upt_is_sig_GB_upt)

corollary rb_aux_is_sig_GB_in:
  "is_sig_GB_in dgrad (set (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))) u"
proof -
  let ?u = "term_of_pair (pp_of_term u, Suc (component_of_term u))"
  have "u \<prec>\<^sub>t ?u"
  proof (rule ord_term_lin.le_neq_trans)
    show "u \<preceq>\<^sub>t ?u" by (rule ord_termI, simp_all add: term_simps)
  next
    show "u \<noteq> ?u"
    proof
      assume "u = ?u"
      hence "component_of_term u = component_of_term ?u" by simp
      thus False by (simp add: term_simps)
    qed
  qed
  with rb_aux_is_sig_GB_upt show ?thesis by (rule is_sig_GB_uptD2)
qed

corollary rb_aux_is_Groebner_basis:
  assumes "hom_grading dgrad"
  shows "punit.is_Groebner_basis (set (map rep_list (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))))"
proof -
  let ?args = "(([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)"
  from rb_aux_inv_init_fst have "rb_aux_dom ?args" by (rule rb_aux_domI)
  then obtain bs ss z' where eq: "rb_aux ?args = ((bs, ss, []), z')" by (rule rb_aux_shape)
  moreover from rb_aux_inv_init_fst have "rb_aux_inv (fst (rb_aux ?args))"
    by (rule rb_aux_inv_invariant)
  ultimately have "rb_aux_inv (bs, ss, [])" by simp
  hence "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  hence "set (fst (fst (rb_aux ?args))) \<subseteq> dgrad_max_set dgrad" by (simp add: eq dgrad_sig_set'_def)
  with dgrad assms have "punit.is_Groebner_basis (rep_list ` set (fst (fst (rb_aux ?args))))"
    using rb_aux_is_sig_GB_in by (rule is_sig_GB_is_Groebner_basis)
  thus ?thesis by simp
qed

lemma ideal_rb_aux:
  "ideal (set (map rep_list (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))))) =
   ideal (set fs)" (is "ideal ?l = ideal ?r")
proof
  show "ideal ?l \<subseteq> ideal ?r" by (rule ideal.span_subset_spanI, auto simp: rep_list_in_ideal)
next
  show "ideal ?r \<subseteq> ideal ?l"
  proof (rule ideal.span_subset_spanI, rule subsetI)
    fix f
    assume "f \<in> set fs"
    then obtain j where "j < length fs" and f: "f = fs ! j" by (metis in_set_conv_nth)
    let ?args = "(([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)"
    from rb_aux_inv_init_fst have "rb_aux_dom ?args" by (rule rb_aux_domI)
    then obtain bs ss z' where eq: "rb_aux ?args = ((bs, ss, []), z')" by (rule rb_aux_shape)
    moreover from rb_aux_inv_init_fst have "rb_aux_inv (fst (rb_aux ?args))"
      by (rule rb_aux_inv_invariant)
    ultimately have "rb_aux_inv (bs, ss, [])" by simp
    moreover note \<open>j < length fs\<close>
    moreover have "Inr j \<notin> set []" by simp
    ultimately have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal ?l"
      unfolding eq set_map fst_conv by (rule rb_aux_inv_D9)
    thus "f \<in> ideal ?l" by (simp add: rep_list_monomial' \<open>j < length fs\<close> f)
  qed
qed

corollary ideal_rb: "ideal (rep_list ` set (fst rb)) = ideal (set fs)"
proof -
  have "ideal (rep_list ` set (fst rb)) =
        ideal (set (map rep_list (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), 0))))))"
    by (auto simp: rb_def split: prod.splits)
  also have "... = ideal (set fs)" by (fact ideal_rb_aux)
  finally show ?thesis .
qed

lemma
  shows dgrad_max_set_closed_rb_aux:
    "set (map rep_list (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))) \<subseteq>
      punit_dgrad_max_set dgrad" (is ?thesis1)
  and rb_aux_nonzero:
    "0 \<notin> set (map rep_list (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))))"
      (is ?thesis2)
proof -
  let ?args = "(([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)"
  from rb_aux_inv_init_fst have "rb_aux_dom ?args" by (rule rb_aux_domI)
  then obtain bs ss z' where eq: "rb_aux ?args = ((bs, ss, []), z')" by (rule rb_aux_shape)
  moreover from rb_aux_inv_init_fst have "rb_aux_inv (fst (rb_aux ?args))"
    by (rule rb_aux_inv_invariant)
  ultimately have "rb_aux_inv (bs, ss, [])" by simp
  hence "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence "set bs \<subseteq> dgrad_sig_set dgrad" and *: "0 \<notin> rep_list ` set bs"
    by (rule rb_aux_inv1_D1, rule rb_aux_inv1_D2)
  from this(1) have "set bs \<subseteq> dgrad_max_set dgrad" by (simp add: dgrad_sig_set'_def)
  with dgrad show ?thesis1 by (simp add: eq dgrad_max_3)
  from * show ?thesis2 by (simp add: eq)
qed

subsubsection \<open>Minimality of the Computed Basis\<close>

lemma rb_aux_top_irred':
  assumes "rword_strict = rw_rat_strict" and "rb_aux_inv (bs, ss, p # ps)"
    and "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
  shows "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set bs) (sig_trd bs (poly_of_pair p))"
proof -
  have "rword = rw_rat" by (intro ext, simp only: rword_def rw_rat_alt, simp add: assms(1))

  have lt_p: "sig_of_pair p = lt (poly_of_pair p)" by (rule pair_list_sig_of_pair, fact, simp)
  define p' where "p' = sig_trd bs (poly_of_pair p)"
  have red_p: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (poly_of_pair p) p'"
    unfolding p'_def by (rule sig_trd_red_rtrancl)
  hence lt_p': "lt p' = sig_of_pair p"
    and lt_p'': "punit.lt (rep_list p') \<preceq> punit.lt (rep_list (poly_of_pair p))"
    unfolding lt_p by (rule sig_red_regular_rtrancl_lt, rule sig_red_rtrancl_lt_rep_list)
  have "\<not> is_sig_red (=) (=) (set bs) p'"
  proof
    assume "is_sig_red (=) (=) (set bs) p'"
    then obtain b where "b \<in> set bs" and "rep_list b \<noteq> 0" and "rep_list p' \<noteq> 0"
      and 1: "punit.lt (rep_list b) adds punit.lt (rep_list p')"
      and 2: "punit.lt (rep_list p') \<oplus> lt b = punit.lt (rep_list b) \<oplus> lt p'"
      by (rule is_sig_red_top_addsE)
    note this(3)
    moreover from red_p have "(punit.red (rep_list ` set bs))\<^sup>*\<^sup>* (rep_list (poly_of_pair p)) (rep_list p')"
      by (rule sig_red_red_rtrancl)
    ultimately have "rep_list (poly_of_pair p) \<noteq> 0" by (auto simp: punit.rtrancl_0)

    define x where "x = punit.lt (rep_list p') - punit.lt (rep_list b)"
    from 1 2 have x1: "x \<oplus> lt b = lt p'" by (simp add: term_is_le_rel_minus x_def)
    from this[symmetric] have "lt b adds\<^sub>t sig_of_pair p" unfolding lt_p' by (rule adds_termI)
    from 1 have x2: "x + punit.lt (rep_list b) = punit.lt (rep_list p')" by (simp add: x_def adds_minus)
    from \<open>rep_list b \<noteq> 0\<close> have "b \<noteq> 0" by (auto simp: rep_list_zero)

    show False
    proof (rule sum_prodE)
      fix a0 b0
      assume p: "p = Inl (a0, b0)"
      hence "Inl (a0, b0) \<in> set (p # ps)" by simp
      with assms(2) have reg: "is_regular_spair a0 b0" and "a0 \<in> set bs" and "b0 \<in> set bs"
        by (rule rb_aux_inv_D3)+
      from assms(2) have inv1: "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
      hence "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
      with \<open>a0 \<in> set bs\<close> \<open>b0 \<in> set bs\<close> have "rep_list a0 \<noteq> 0" and "rep_list b0 \<noteq> 0" by fastforce+
      hence "a0 \<noteq> 0" and "b0 \<noteq> 0" by (auto simp: rep_list_zero)

      let ?t1 = "punit.lt (rep_list a0)"
      let ?t2 = "punit.lt (rep_list b0)"
      let ?l = "lcs ?t1 ?t2"
      from \<open>rep_list (poly_of_pair p) \<noteq> 0\<close> have "punit.spoly (rep_list a0) (rep_list b0) \<noteq> 0"
        by (simp add: p rep_list_spair)
      with \<open>rep_list a0 \<noteq> 0\<close> \<open>rep_list b0 \<noteq> 0\<close>
      have "punit.lt (punit.spoly (rep_list a0) (rep_list b0)) \<prec> ?l"
        by (rule punit.lt_spoly_less_lcs[simplified])

      obtain b' where 3: "is_canon_rewriter rword (set bs) (sig_of_pair p) b'"
        and 4: "punit.lt (rep_list (poly_of_pair p)) \<prec>
                      (pp_of_term (sig_of_pair p) - lp b') + punit.lt (rep_list b')"
      proof (cases "(?l - ?t1) \<oplus> lt a0 \<preceq>\<^sub>t (?l - ?t2) \<oplus> lt b0")
        case True
        have "sig_of_pair p = lt (spair a0 b0)" unfolding lt_p by (simp add: p)
        also from reg have "... = (?l - ?t2) \<oplus> lt b0"
          by (simp add: True is_regular_spair_lt ord_term_lin.max_def)
        finally have eq1: "sig_of_pair p = (?l - ?t2) \<oplus> lt b0" .
        hence "lt b0 adds\<^sub>t sig_of_pair p" by (rule adds_termI)
        moreover from assms(3) have "\<not> is_rewritable bs b0 ((?l - ?t2) \<oplus> lt b0)"
          by (simp add: p spair_sigs_def Let_def)
        ultimately have "is_canon_rewriter rword (set bs) (sig_of_pair p) b0"
          unfolding eq1[symmetric] using inv1 \<open>b0 \<in> set bs\<close> \<open>b0 \<noteq> 0\<close> is_rewritableI_is_canon_rewriter
          by blast
        thus ?thesis
        proof
          have "punit.lt (rep_list (poly_of_pair p)) = punit.lt (punit.spoly (rep_list a0) (rep_list b0))"
            by (simp add: p rep_list_spair)
          also have "... \<prec> ?l" by fact
          also have "... = (?l - ?t2) + ?t2" by (simp only: adds_minus adds_lcs_2)
          also have "... = (pp_of_term (sig_of_pair p) - lp b0) + ?t2"
            by (simp only: eq1 pp_of_term_splus add_diff_cancel_right')
          finally show "punit.lt (rep_list (poly_of_pair p)) \<prec> pp_of_term (sig_of_pair p) - lp b0 + ?t2" .
        qed
      next
        case False
        have "sig_of_pair p = lt (spair a0 b0)" unfolding lt_p by (simp add: p)
        also from reg have "... = (?l - ?t1) \<oplus> lt a0"
          by (simp add: False is_regular_spair_lt ord_term_lin.max_def)
        finally have eq1: "sig_of_pair p = (?l - ?t1) \<oplus> lt a0" .
        hence "lt a0 adds\<^sub>t sig_of_pair p" by (rule adds_termI)
        moreover from assms(3) have "\<not> is_rewritable bs a0 ((?l - ?t1) \<oplus> lt a0)"
          by (simp add: p spair_sigs_def Let_def)
        ultimately have "is_canon_rewriter rword (set bs) (sig_of_pair p) a0"
          unfolding eq1[symmetric] using inv1 \<open>a0 \<in> set bs\<close> \<open>a0 \<noteq> 0\<close> is_rewritableI_is_canon_rewriter
          by blast
        thus ?thesis
        proof
          have "punit.lt (rep_list (poly_of_pair p)) = punit.lt (punit.spoly (rep_list a0) (rep_list b0))"
            by (simp add: p rep_list_spair)
          also have "... \<prec> ?l" by fact
          also have "... = (?l - ?t1) + ?t1" by (simp only: adds_minus adds_lcs)
          also have "... = (pp_of_term (sig_of_pair p) - lp a0) + ?t1"
            by (simp only: eq1 pp_of_term_splus add_diff_cancel_right')
          finally show "punit.lt (rep_list (poly_of_pair p)) \<prec> pp_of_term (sig_of_pair p) - lp a0 + ?t1" .
        qed
      qed

      define y where "y = pp_of_term (sig_of_pair p) - lp b'"
      from lt_p'' 4 have y2: "punit.lt (rep_list p') \<prec> y + punit.lt (rep_list b')"
        unfolding y_def by (rule ordered_powerprod_lin.le_less_trans)
      from 3 have "lt b' adds\<^sub>t sig_of_pair p" by (rule is_canon_rewriterD3)
      hence "lp b' adds lp p'" and "component_of_term (lt b') = component_of_term (lt p')"
        by (simp_all add: adds_term_def lt_p')
      hence y1: "y \<oplus> lt b' = lt p'" by (simp add: y_def splus_def lt_p' adds_minus term_simps)
      from 3 \<open>b \<in> set bs\<close> \<open>b \<noteq> 0\<close> \<open>lt b adds\<^sub>t sig_of_pair p\<close>
      have "rword (spp_of b) (spp_of b')" by (rule is_canon_rewriterD)
      hence "punit.lt (rep_list b') \<oplus> lt b \<preceq>\<^sub>t punit.lt (rep_list b) \<oplus> lt b'"
        by (auto simp: \<open>rword = rw_rat\<close> rw_rat_def Let_def spp_of_def)
      hence "(x + y) \<oplus> (punit.lt (rep_list b') \<oplus> lt b) \<preceq>\<^sub>t (x + y) \<oplus> (punit.lt (rep_list b) \<oplus> lt b')"
        by (rule splus_mono)
      hence "(y + punit.lt (rep_list b')) \<oplus> (x \<oplus> lt b) \<preceq>\<^sub>t (x + punit.lt (rep_list b)) \<oplus> (y \<oplus> lt b')"
        by (simp add: ac_simps)
      hence "(y + punit.lt (rep_list b')) \<oplus> lt p' \<preceq>\<^sub>t punit.lt (rep_list p') \<oplus> lt p'"
        by (simp only: x1 x2 y1)
      hence "y + punit.lt (rep_list b') \<preceq> punit.lt (rep_list p')" by (rule ord_term_canc_left)
      with y2 show ?thesis by simp
    next
      fix j
      assume p: "p = Inr j"
      hence "lt p' = term_of_pair (0, j)" by (simp add: lt_p')
      with x1 term_of_pair_pair[of "lt b"] have "lt b = term_of_pair (0, j)"
        by (auto simp: splus_def dest!: term_of_pair_injective plus_eq_zero_2)
      moreover have "lt b \<prec>\<^sub>t term_of_pair (0, j)" by (rule rb_aux_inv_D4, fact, simp add: p, fact)
      ultimately show ?thesis by simp
    qed
  qed
  moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (set bs) p'"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (=) (set bs) p'"
    hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs) p'" by (simp add: is_sig_red_top_tail_cases)
    with sig_trd_irred show False unfolding p'_def ..
  qed
  ultimately show ?thesis by (simp add: p'_def is_sig_red_sing_reg_cases)
qed

lemma rb_aux_top_irred:
  assumes "rword_strict = rw_rat_strict" and "rb_aux_inv (fst args)" and "b \<in> set (fst (fst (rb_aux args)))"
    and "\<And>b0. b0 \<in> set (fst (fst args)) \<Longrightarrow> \<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst args)) - {b0}) b0"
  shows "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst (rb_aux args))) - {b}) b"
proof -
  from assms(2) have "rb_aux_dom args" by (rule rb_aux_domI)
  thus ?thesis using assms(2, 3, 4)
  proof (induct args rule: rb_aux.pinduct)
    case (1 bs ss z)
    let ?nil = "[]::((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list"
    from 1(3) have "b \<in> set (fst (fst ((bs, ss, ?nil), z)))" by (simp add: rb_aux.psimps(1)[OF 1(1)])
    hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, ss, ?nil), z))) - {b}) b" by (rule 1(4))
    thus ?case by (simp add: rb_aux.psimps(1)[OF 1(1)])
  next
    case (2 bs ss p ps z)
    from 2(5) have *: "rb_aux_inv (bs, ss, p # ps)" by (simp only: fst_conv)
    define p' where "p' = sig_trd bs (poly_of_pair p)"
    from 2(6) show ?case
    proof (simp add: rb_aux.psimps(2)[OF 2(1)] Let_def p'_def[symmetric] split: if_splits)
      note refl
      moreover assume "sig_crit bs (new_syz_sigs ss bs p) p"
      moreover from * this have "rb_aux_inv (fst ((bs, new_syz_sigs ss bs p, ps), z))"
        unfolding fst_conv by (rule rb_aux_inv_preserved_1)
      moreover assume "b \<in> set (fst (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z))))"
      ultimately show "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)))) - {b}) b"
      proof (rule 2(2))
        fix b0
        assume "b0 \<in> set (fst (fst ((bs, new_syz_sigs ss bs p, ps), z)))"
        hence "b0 \<in> set (fst (fst ((bs, ss, p # ps), z)))" by simp
        hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, ss, p # ps), z))) - {b0}) b0" by (rule 2(7))
        thus "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, new_syz_sigs ss bs p, ps), z))) - {b0}) b0"
          by simp
      qed
    next
      note refl
      moreover assume "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
      moreover note refl
      moreover assume "rep_list p' = 0"
      moreover from * this have "rb_aux_inv (fst ((bs, lt p' # new_syz_sigs ss bs p, ps), Suc z))"
        unfolding p'_def fst_conv by (rule rb_aux_inv_preserved_2)
      moreover assume "b \<in> set (fst (fst (rb_aux ((bs, lt p' # new_syz_sigs ss bs p, ps), Suc z))))"
      ultimately show "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst (rb_aux ((bs,
                                                        lt p' # new_syz_sigs ss bs p, ps), Suc z)))) - {b}) b"
      proof (rule 2(3)[simplified p'_def[symmetric]])
        fix b0
        assume "b0 \<in> set (fst (fst ((bs, lt p' # new_syz_sigs ss bs p, ps), Suc z)))"
        hence "b0 \<in> set (fst (fst ((bs, ss, p # ps), z)))" by simp
        hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, ss, p # ps), z))) - {b0}) b0" by (rule 2(7))
        thus "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, lt p' # new_syz_sigs ss bs p, ps), Suc z))) - {b0}) b0"
          by simp
      qed
    next
      note refl
      moreover assume "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
      moreover note refl
      moreover assume "rep_list p' \<noteq> 0"
      moreover from * \<open>\<not> sig_crit bs (new_syz_sigs ss bs p) p\<close> this
      have inv: "rb_aux_inv (fst ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z))"
        unfolding p'_def fst_conv by (rule rb_aux_inv_preserved_3)
      moreover assume "b \<in> set (fst (fst (rb_aux ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z))))"
      ultimately show "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst (rb_aux ((p' # bs,
                                              new_syz_sigs ss bs p, add_spairs ps bs p'), z)))) - {b}) b"
      proof (rule 2(4)[simplified p'_def[symmetric]])
        fix b0
        assume "b0 \<in> set (fst (fst ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z)))"
        hence "b0 = p' \<or> b0 \<in> set bs" by simp
        hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (({p'} - {b0}) \<union> (set bs - {b0})) b0"
        proof
          assume "b0 = p'"
          have "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set bs - {b0}) p'"
          proof
            assume "is_sig_red (\<preceq>\<^sub>t) (=) (set bs - {b0}) p'"
            moreover have "set bs - {b0} \<subseteq> set bs" by fastforce
            ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) (set bs) p'" by (rule is_sig_red_mono)
            moreover have "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set bs) p'" unfolding p'_def
              using assms(1) * \<open>\<not> sig_crit bs (new_syz_sigs ss bs p) p\<close> by (rule rb_aux_top_irred')
            ultimately show False by simp
          qed
          thus ?thesis by (simp add: \<open>b0 = p'\<close>)
        next
          assume "b0 \<in> set bs"
          hence "b0 \<in> set (fst (fst ((bs, ss, p # ps), z)))" by simp
          hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((bs, ss, p # ps), z))) - {b0}) b0" by (rule 2(7))
          hence "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set bs - {b0}) b0" by simp
          moreover have "\<not> is_sig_red (\<preceq>\<^sub>t) (=) ({p'} - {b0}) b0"
          proof
            assume "is_sig_red (\<preceq>\<^sub>t) (=) ({p'} - {b0}) b0"
            moreover have "{p'} - {b0} \<subseteq> {p'}" by fastforce
            ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) {p'} b0" by (rule is_sig_red_mono)
            hence "lt p' \<preceq>\<^sub>t lt b0" by (rule is_sig_redD_lt)

            from inv have "rb_aux_inv (p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p')"
              by (simp only: fst_conv)
            hence "rb_aux_inv1 (p' # bs)" by (rule rb_aux_inv_D1)
            hence "sorted_wrt (\<lambda>x y. lt y \<prec>\<^sub>t lt x) (p' # bs)" by (rule rb_aux_inv1_D3)
            with \<open>b0 \<in> set bs\<close> have "lt b0 \<prec>\<^sub>t lt p'" by simp
            with \<open>lt p' \<preceq>\<^sub>t lt b0\<close> show False by simp
          qed
          ultimately show ?thesis by (simp add: is_sig_red_Un)
        qed
        thus "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z))) - {b0}) b0"
          by (simp add: Un_Diff[symmetric])
      qed
    qed
  qed
qed

corollary rb_aux_is_min_sig_GB:
  assumes "rword_strict = rw_rat_strict"
  shows "is_min_sig_GB dgrad (set (fst (fst (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))))"
    (is "is_min_sig_GB _ (set (fst (fst (rb_aux ?args))))")
  unfolding is_min_sig_GB_def
proof (intro conjI allI ballI impI)
  from rb_aux_inv_init_fst have inv: "rb_aux_inv (fst (rb_aux ?args))"
    and "rb_aux_dom ?args"
    by (rule rb_aux_inv_invariant, rule rb_aux_domI)
  from this(2) obtain bs ss z' where eq: "rb_aux ?args = ((bs, ss, []), z')"
    by (rule rb_aux_shape)
  from inv have "rb_aux_inv (bs, ss, [])" by (simp only: eq fst_conv)
  hence "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
  thus "set (fst (fst (rb_aux ?args))) \<subseteq> dgrad_sig_set dgrad" by (simp add: eq)
next
  fix u
  show "is_sig_GB_in dgrad (set (fst (fst (rb_aux ?args)))) u" by (fact rb_aux_is_sig_GB_in)
next
  fix g
  assume "g \<in> set (fst (fst (rb_aux ?args)))"
  with assms(1) rb_aux_inv_init_fst
  show "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (set (fst (fst (rb_aux ?args))) - {g}) g"
    by (rule rb_aux_top_irred) simp
qed

corollary rb_is_min_sig_GB:
  assumes "rword_strict = rw_rat_strict"
  shows "is_min_sig_GB dgrad (set (fst rb))"
  using rb_aux_is_min_sig_GB[OF assms, of 0] by (auto simp: rb_def split: prod.split)

subsubsection \<open>No Zero-Reductions\<close>

fun rb_aux_inv2 :: "(('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> ((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list) \<Rightarrow> bool"
  where "rb_aux_inv2 (bs, ss, ps) =
          (rb_aux_inv (bs, ss, ps) \<and>
           (\<forall>j<length fs. Inr j \<notin> set ps \<longrightarrow>
               (fs ! j \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) bs)) \<and>
               (\<forall>b\<in>set bs. component_of_term (lt b) < j \<longrightarrow>
                  (\<exists>s\<in>set ss. s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j))))))"

lemma rb_aux_inv2_D1: "rb_aux_inv2 args \<Longrightarrow> rb_aux_inv args"
  by (metis prod.exhaust rb_aux_inv2.simps)

lemma rb_aux_inv2_D2:
  "rb_aux_inv2 (bs, ss, ps) \<Longrightarrow> j < length fs \<Longrightarrow> Inr j \<notin> set ps \<Longrightarrow>
    fs ! j \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) bs))"
  by simp

lemma rb_aux_inv2_E:
  assumes "rb_aux_inv2 (bs, ss, ps)" and "j < length fs" and "Inr j \<notin> set ps" and "b \<in> set bs"
    and "component_of_term (lt b) < j"
  obtains s where "s \<in> set ss" and "s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
  using assms by auto

context
  assumes pot: "is_pot_ord"
begin

lemma sig_red_zero_filter:
  assumes "sig_red_zero (\<preceq>\<^sub>t) (set bs) r" and "component_of_term (lt r) < j"
  shows "sig_red_zero (\<preceq>\<^sub>t) (set (filter (\<lambda>b. component_of_term (lt b) < j) bs)) r"
proof -
  have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
  with assms(1) have "sig_red_zero (\<preceq>\<^sub>t) {b\<in>set bs. lt b \<preceq>\<^sub>t lt r} r" by (rule sig_red_zero_subset)
  moreover have "{b\<in>set bs. lt b \<preceq>\<^sub>t lt r} \<subseteq> set (filter (\<lambda>b. component_of_term (lt b) < j) bs)"
  proof
    fix b
    assume "b \<in> {b\<in>set bs. lt b \<preceq>\<^sub>t lt r}"
    hence "b \<in> set bs" and "lt b \<preceq>\<^sub>t lt r" by simp_all
    from pot this(2) have "component_of_term (lt b) \<le> component_of_term (lt r)" by (rule is_pot_ordD2)
    also have "... < j" by (fact assms(2))
    finally have "component_of_term (lt b) < j" .
    with \<open>b \<in> set bs\<close> show "b \<in> set (filter (\<lambda>b. component_of_term (lt b) < j) bs)" by simp
  qed
  ultimately show ?thesis by (rule sig_red_zero_mono)
qed

lemma rb_aux_inv2_preserved_0:
  assumes "rb_aux_inv2 (bs, ss, p # ps)" and "j < length fs" and "Inr j \<notin> set ps"
    and "b \<in> set bs" and "component_of_term (lt b) < j"
  shows "\<exists>s\<in>set (new_syz_sigs ss bs p). s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
proof (rule sum_prodE)
  fix x y
  assume p: "p = Inl (x, y)"
  with assms(3) have "Inr j \<notin> set (p # ps)" by simp
  with assms(1, 2) obtain s where "s \<in> set ss" and *: "s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
    using assms(4, 5) by (rule rb_aux_inv2_E)
  from this(1) have "s \<in> set (new_syz_sigs ss bs p)" by (simp add: p)
  with * show ?thesis ..
next
  fix i
  assume p: "p = Inr i"
  have trans: "transp (adds\<^sub>t)" by (rule transpI, drule adds_term_trans)
  from adds_term_refl have refl: "reflp (adds\<^sub>t)" by (rule reflpI)
  let ?v = "term_of_pair (punit.lt (rep_list b), j)"
  let ?f = "\<lambda>b. term_of_pair (punit.lt (rep_list b), i)"
  define ss' where "ss' = filter_min (adds\<^sub>t) (map ?f bs)"
  have eq: "new_syz_sigs ss bs p = filter_min_append (adds\<^sub>t) ss ss'" by (simp add: p ss'_def pot)
  show ?thesis
  proof (cases "i = j")
    case True
    from \<open>b \<in> set bs\<close> have "?v \<in> ?f ` set bs" unfolding \<open>i = j\<close> by (rule imageI)
    hence "?v \<in> set ss \<union> set (map ?f bs)" by simp
    thus ?thesis
    proof
      assume "?v \<in> set ss"
      hence "?v \<in> set ss \<union> set ss'" by simp
      with trans refl obtain s where "s \<in> set (new_syz_sigs ss bs p)" and "s adds\<^sub>t ?v"
        unfolding eq by (rule filter_min_append_relE)
      thus ?thesis ..
    next
      assume "?v \<in> set (map ?f bs)"
      with trans refl obtain s where "s \<in> set ss'" and "s adds\<^sub>t ?v"
        unfolding ss'_def by (rule filter_min_relE)
      from this(1) have "s \<in> set ss \<union> set ss'" by simp
      with trans refl obtain s' where s': "s' \<in> set (new_syz_sigs ss bs p)" and "s' adds\<^sub>t s"
        unfolding eq by (rule filter_min_append_relE)
      from this(2) \<open>s adds\<^sub>t ?v\<close> have "s' adds\<^sub>t ?v" by (rule adds_term_trans)
      with s' show ?thesis ..
    qed
  next
    case False
    with assms(3) have "Inr j \<notin> set (p # ps)" by (simp add: p)
    with assms(1, 2) obtain s where "s \<in> set ss" and "s adds\<^sub>t ?v"
      using assms(4, 5) by (rule rb_aux_inv2_E)
    from this(1) have "s \<in> set ss \<union> set (map ?f bs)" by simp
    thus ?thesis
    proof
      assume "s \<in> set ss"
      hence "s \<in> set ss \<union> set ss'" by simp
      with trans refl obtain s' where s': "s' \<in> set (new_syz_sigs ss bs p)" and "s' adds\<^sub>t s"
        unfolding eq by (rule filter_min_append_relE)
      from this(2) \<open>s adds\<^sub>t ?v\<close> have "s' adds\<^sub>t ?v" by (rule adds_term_trans)
      with s' show ?thesis ..
    next
      assume "s \<in> set (map ?f bs)"
      with trans refl obtain s' where "s' \<in> set ss'" and "s' adds\<^sub>t s"
        unfolding ss'_def by (rule filter_min_relE)
      from this(1) have "s' \<in> set ss \<union> set ss'" by simp
      with trans refl obtain s'' where s'': "s'' \<in> set (new_syz_sigs ss bs p)" and "s'' adds\<^sub>t s'"
        unfolding eq by (rule filter_min_append_relE)
      from this(2) \<open>s' adds\<^sub>t s\<close> have "s'' adds\<^sub>t s" by (rule adds_term_trans)
      hence "s'' adds\<^sub>t ?v" using \<open>s adds\<^sub>t ?v\<close> by (rule adds_term_trans)
      with s'' show ?thesis ..
    qed
  qed
qed

lemma rb_aux_inv2_preserved_1:
  assumes "rb_aux_inv2 (bs, ss, p # ps)" and "sig_crit bs (new_syz_sigs ss bs p) p"
  shows "rb_aux_inv2 (bs, new_syz_sigs ss bs p, ps)"
  unfolding rb_aux_inv2.simps
proof (intro allI conjI impI ballI)
  from assms(1) have inv: "rb_aux_inv (bs, ss, p # ps)" by (rule rb_aux_inv2_D1)
  thus "rb_aux_inv (bs, new_syz_sigs ss bs p, ps)"
    using assms(2) by (rule rb_aux_inv_preserved_1)

  fix j
  assume "j < length fs" and "Inr j \<notin> set ps"
  show "fs ! j \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) bs))"
  proof (cases "p = Inr j")
    case True
    with assms(2) have "is_pred_syz (new_syz_sigs ss bs p) (term_of_pair (0, j))" by simp
    let ?X = "set (filter (\<lambda>b. component_of_term (lt b) < Suc j) bs)"
    have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` ?X)"
    proof (rule sig_red_zero_idealI)
      have "sig_red_zero (\<prec>\<^sub>t) (set bs) (monomial 1 (term_of_pair (0, j)))"
      proof (rule syzygy_crit)
        from inv have "is_RB_upt dgrad rword (set bs) (sig_of_pair p)"
          by (rule rb_aux_inv_is_RB_upt_Cons)
        with dgrad have "is_sig_GB_upt dgrad (set bs) (sig_of_pair p)"
          by (rule is_RB_upt_is_sig_GB_upt)
        thus "is_sig_GB_upt dgrad (set bs) (term_of_pair (0, j))" by (simp add: \<open>p = Inr j\<close>)
      next
        show "monomial 1 (term_of_pair (0, j)) \<in> dgrad_sig_set dgrad"
          by (rule dgrad_sig_set_closed_monomial, simp_all add: term_simps dgrad_max_0 \<open>j < length fs\<close>)
      next
        show "lt (monomial (1::'b) (term_of_pair (0, j))) = term_of_pair (0, j)" by (simp add: lt_monomial)
      next
        from inv assms(2) have "sig_crit' bs p" by (rule sig_crit'I_sig_crit)
        thus "is_syz_sig dgrad (term_of_pair (0, j))" by (simp add: \<open>p = Inr j\<close>)
      qed (fact dgrad)
      hence "sig_red_zero (\<preceq>\<^sub>t) (set bs) (monomial 1 (term_of_pair (0, j)))"
        by (rule sig_red_zero_sing_regI)
      moreover have "component_of_term (lt (monomial (1::'b) (term_of_pair (0, j)))) < Suc j"
        by (simp add: lt_monomial component_of_term_of_pair)
      ultimately show "sig_red_zero (\<preceq>\<^sub>t) ?X (monomial 1 (term_of_pair (0, j)))"
        by (rule sig_red_zero_filter)
    qed
    thus ?thesis by (simp add: rep_list_monomial' \<open>j < length fs\<close>)
  next
    case False
    with \<open>Inr j \<notin> set ps\<close> have "Inr j \<notin> set (p # ps)" by simp
    with assms(1) \<open>j < length fs\<close> show ?thesis by (rule rb_aux_inv2_D2)
  qed
next
  fix j b
  assume "j < length fs" and "Inr j \<notin> set ps" and "b \<in> set bs" and "component_of_term (lt b) < j"
  with assms(1) show "\<exists>s\<in>set (new_syz_sigs ss bs p). s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
    by (rule rb_aux_inv2_preserved_0)
qed

lemma rb_aux_inv2_preserved_3:
  assumes "rb_aux_inv2 (bs, ss, p # ps)" and "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
    and "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
  shows "rb_aux_inv2 (sig_trd bs (poly_of_pair p) # bs, new_syz_sigs ss bs p,
                          add_spairs ps bs (sig_trd bs (poly_of_pair p)))"
proof -
  from assms(1) have inv: "rb_aux_inv (bs, ss, p # ps)" by (rule rb_aux_inv2_D1)
  define p' where "p' = sig_trd bs (poly_of_pair p)"
  from sig_trd_red_rtrancl[of bs "poly_of_pair p"] have "lt p' = lt (poly_of_pair p)"
    unfolding p'_def by (rule sig_red_regular_rtrancl_lt)
  also have "... = sig_of_pair p" by (rule sym, rule pair_list_sig_of_pair, fact inv, simp)
  finally have lt_p': "lt p' = sig_of_pair p" .
  show ?thesis unfolding rb_aux_inv2.simps p'_def[symmetric]
  proof (intro allI conjI impI ballI)
    show "rb_aux_inv (p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p')"
      unfolding p'_def using inv assms(2, 3) by (rule rb_aux_inv_preserved_3)
  next
    fix j
    assume "j < length fs" and *: "Inr j \<notin> set (add_spairs ps bs p')"
    show "fs ! j \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) (p' # bs)))"
    proof (cases "p = Inr j")
      case True
      let ?X = "set (filter (\<lambda>b. component_of_term (lt b) < Suc j) (p' # bs))"
      have "rep_list (monomial 1 (term_of_pair (0, j))) \<in> ideal (rep_list ` ?X)"
      proof (rule sig_red_zero_idealI)
        have "sig_red_zero (\<preceq>\<^sub>t) (set (p' # bs)) (monomial 1 (term_of_pair (0, j)))"
        proof (rule sig_red_zeroI)
          have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
            using sig_trd_red_rtrancl[of bs "poly_of_pair p"] by (simp add: True p'_def)
          moreover have "set bs \<subseteq> set (p' # bs)" by fastforce
          ultimately have "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
            by (rule sig_red_rtrancl_mono)
          hence "(sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) p'"
            by (rule sig_red_rtrancl_sing_regI)
          also have "sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)) p' 0" unfolding sig_red_def
          proof (intro exI bexI)
            from assms(3) have "rep_list p' \<noteq> 0" by (simp add: p'_def)
            show "sig_red_single (\<preceq>\<^sub>t) (\<preceq>) p' 0 p' 0"
            proof (rule sig_red_singleI)
              show "rep_list p' \<noteq> 0" by fact
            next
              from \<open>rep_list p' \<noteq> 0\<close> have "punit.lt (rep_list p') \<in> keys (rep_list p')"
                by (rule punit.lt_in_keys)
              thus "0 + punit.lt (rep_list p') \<in> keys (rep_list p')" by simp
            next
              from \<open>rep_list p' \<noteq> 0\<close> have "punit.lc (rep_list p') \<noteq> 0" by (rule punit.lc_not_0)
              thus "0 = p' - monom_mult (lookup (rep_list p') (0 + punit.lt (rep_list p')) / punit.lc (rep_list p')) 0 p'"
                by (simp add: punit.lc_def[symmetric])
            qed (simp_all add: term_simps)
          qed simp
          finally show "(sig_red (\<preceq>\<^sub>t) (\<preceq>) (set (p' # bs)))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) 0" .
        qed (fact rep_list_zero)
        moreover have "component_of_term (lt (monomial (1::'b) (term_of_pair (0, j)))) < Suc j"
          by (simp add: lt_monomial component_of_term_of_pair)
        ultimately show "sig_red_zero (\<preceq>\<^sub>t) ?X (monomial 1 (term_of_pair (0, j)))"
          by (rule sig_red_zero_filter)
      qed
      thus ?thesis by (simp add: rep_list_monomial' \<open>j < length fs\<close>)
    next
      case False
      from * have "Inr j \<notin> set ps" by (simp add: add_spairs_def set_merge_wrt)
      hence "Inr j \<notin> set (p # ps)" using False by simp
      with assms(1) \<open>j < length fs\<close>
      have "fs ! j \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) bs))"
        by (rule rb_aux_inv2_D2)
      also have "... \<subseteq> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc j) (p' # bs)))"
        by (intro ideal.span_mono image_mono, fastforce)
      finally show ?thesis .
    qed
  next
    fix j and b::"'t \<Rightarrow>\<^sub>0 'b"
    assume "j < length fs" and *: "component_of_term (lt b) < j"
    assume "Inr j \<notin> set (add_spairs ps bs p')"
    hence "Inr j \<notin> set ps" by (simp add: add_spairs_def set_merge_wrt)
    assume "b \<in> set (p' # bs)"
    hence "b = p' \<or> b \<in> set bs" by simp
    thus "\<exists>s\<in>set (new_syz_sigs ss bs p). s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
    proof
      assume "b = p'"
      with * have "component_of_term (sig_of_pair p) < component_of_term (term_of_pair (0, j))"
        by (simp only: lt_p' component_of_term_of_pair)
      with pot have **: "sig_of_pair p \<prec>\<^sub>t term_of_pair (0, j)" by (rule is_pot_ordD)
      have "p \<in> set (p # ps)" by simp
      with inv have "Inr j \<in> set (p # ps)" using \<open>j < length fs\<close> ** by (rule rb_aux_inv_D6_2)
      with \<open>Inr j \<notin> set ps\<close> have "p = Inr j" by simp
      with ** show ?thesis by simp
    next
      assume "b \<in> set bs"
      with assms(1) \<open>j < length fs\<close> \<open>Inr j \<notin> set ps\<close> show ?thesis
        using * by (rule rb_aux_inv2_preserved_0)
    qed
  qed
qed

lemma rb_aux_inv2_ideal_subset:
  assumes "rb_aux_inv2 (bs, ss, ps)" and "\<And>p0. p0 \<in> set ps \<Longrightarrow> j \<le> component_of_term (sig_of_pair p0)"
  shows "ideal (set (take j fs)) \<subseteq> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < j) bs))"
          (is "ideal ?B \<subseteq> ideal ?A")
proof (intro ideal.span_subset_spanI subsetI)
  fix f
  assume "f \<in> ?B"
  then obtain i where "i < length (take j fs)" and "f = (take j fs) ! i"
    by (metis in_set_conv_nth)
  hence "i < length fs" and "i < j" and f: "f = fs ! i" by auto
  from this(2) have "Suc i \<le> j" by simp
  have "f \<in> ideal (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < Suc i) bs))"
    unfolding f using assms(1) \<open>i < length fs\<close>
  proof (rule rb_aux_inv2_D2)
    show "Inr i \<notin> set ps"
    proof
      assume "Inr i \<in> set ps"
      hence "j \<le> component_of_term (sig_of_pair (Inr i))" by (rule assms(2))
      hence "j \<le> i" by (simp add: component_of_term_of_pair)
      with \<open>i < j\<close> show False by simp
    qed
  qed
  also have "... \<subseteq> ideal ?A"
    by (intro ideal.span_mono image_mono, auto dest: order_less_le_trans[OF _ \<open>Suc i \<le> j\<close>])
  finally show "f \<in> ideal ?A" .
qed

lemma rb_aux_inv_is_Groebner_basis:
  assumes "hom_grading dgrad" and "rb_aux_inv (bs, ss, ps)"
    and "\<And>p0. p0 \<in> set ps \<Longrightarrow> j \<le> component_of_term (sig_of_pair p0)"
  shows "punit.is_Groebner_basis (rep_list ` set (filter (\<lambda>b. component_of_term (lt b) < j) bs))"
          (is "punit.is_Groebner_basis (rep_list ` set ?bs)")
  using dgrad assms(1)
proof (rule is_sig_GB_upt_is_Groebner_basis)
  show "set ?bs \<subseteq> dgrad_sig_set' j dgrad"
  proof
    fix b
    assume "b \<in> set ?bs"
    hence "b \<in> set bs" and "component_of_term (lt b) < j" by simp_all
    show "b \<in> dgrad_sig_set' j dgrad" unfolding dgrad_sig_set'_def
    proof
      from assms(2) have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
      hence "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)
      with \<open>b \<in> set bs\<close> have "b \<in> dgrad_sig_set dgrad" ..
      thus "b \<in> dgrad_max_set dgrad" by (simp add: dgrad_sig_set'_def)
    next
      show "b \<in> sig_inv_set' j"
      proof (rule sig_inv_setI')
        fix v
        assume "v \<in> keys b"
        hence "v \<preceq>\<^sub>t lt b" by (rule lt_max_keys)
        with pot have "component_of_term v \<le> component_of_term (lt b)" by (rule is_pot_ordD2)
        also have "... < j" by fact
        finally show "component_of_term v < j" .
      qed
    qed
  qed
next
  fix u
  assume u: "component_of_term u < j"
  from dgrad have "is_sig_GB_upt dgrad (set bs) (term_of_pair (0, j))"
  proof (rule is_RB_upt_is_sig_GB_upt)
    from assms(2) show "is_RB_upt dgrad rword (set bs) (term_of_pair (0, j))"
    proof (rule rb_aux_inv_is_RB_upt)
      fix p
      assume "p \<in> set ps"
      hence "j \<le> component_of_term (sig_of_pair p)" by (rule assms(3))
      with pot show "term_of_pair (0, j) \<preceq>\<^sub>t sig_of_pair p"
        by (auto simp: is_pot_ord term_simps zero_min)
    qed
  qed
  moreover from pot have "u \<prec>\<^sub>t term_of_pair (0, j)"
    by (rule is_pot_ordD) (simp only: u component_of_term_of_pair)
  ultimately have 1: "is_sig_GB_in dgrad (set bs) u" by (rule is_sig_GB_uptD2)
  show "is_sig_GB_in dgrad (set ?bs) u"
  proof (rule is_sig_GB_inI)
    fix r :: "'t \<Rightarrow>\<^sub>0 'b"
    assume "lt r = u"
    assume "r \<in> dgrad_sig_set dgrad"
    with 1 have "sig_red_zero (\<preceq>\<^sub>t) (set bs) r" using \<open>lt r = u\<close> by (rule is_sig_GB_inD)
    moreover from u have "component_of_term (lt r) < j" by (simp only: \<open>lt r = u\<close>)
    ultimately show "sig_red_zero (\<preceq>\<^sub>t) (set ?bs) r" by (rule sig_red_zero_filter)
  qed
qed

lemma rb_aux_inv2_no_zero_red:
  assumes "hom_grading dgrad" and "is_regular_sequence fs" and "rb_aux_inv2 (bs, ss, p # ps)"
    and "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
  shows "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
proof
  from assms(3) have inv: "rb_aux_inv (bs, ss, p # ps)" by (rule rb_aux_inv2_D1)
  moreover have "p \<in> set (p # ps)" by simp
  ultimately have sig_p: "sig_of_pair p = lt (poly_of_pair p)" and "poly_of_pair p \<noteq> 0"
    and p_in: "poly_of_pair p \<in> dgrad_sig_set dgrad"
    by (rule pair_list_sig_of_pair, rule pair_list_nonzero, rule pair_list_dgrad_sig_set)
  from this(2) have "lc (poly_of_pair p) \<noteq> 0" by (rule lc_not_0)
  from inv have "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
  hence bs_sub: "set bs \<subseteq> dgrad_sig_set dgrad" by (rule rb_aux_inv1_D1)

  define p' where "p' = sig_trd bs (poly_of_pair p)"
  define j where "j = component_of_term (lt p')"
  define q where "q = lookup (vectorize_poly p') j"
  let ?bs = "filter (\<lambda>b. component_of_term (lt b) < j) bs"
  let ?fs = "take (Suc j) fs"

  have "p' \<in> dgrad_sig_set dgrad" unfolding p'_def using dgrad bs_sub p_in sig_trd_red_rtrancl
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  hence "p' \<in> sig_inv_set" by (simp add: dgrad_sig_set'_def)

  have lt_p': "lt p' = lt (poly_of_pair p)" and "lc p' = lc (poly_of_pair p)"
    unfolding p'_def using sig_trd_red_rtrancl
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  from this(2) \<open>lc (poly_of_pair p) \<noteq> 0\<close> have "p' \<noteq> 0" by (simp add: lc_eq_zero_iff[symmetric])
  hence "lt p' \<in> keys p'" by (rule lt_in_keys)
  hence "j \<in> keys (vectorize_poly p')" by (simp add: keys_vectorize_poly j_def)
  hence "q \<noteq> 0" by (simp add: q_def in_keys_iff)

  from \<open>p' \<in> sig_inv_set\<close> \<open>lt p' \<in> keys p'\<close> have "j < length fs"
    unfolding j_def by (rule sig_inv_setD')
  with le_refl have "fs ! j \<in> set (drop j fs)" by (rule nth_in_set_dropI)
  with fs_distinct le_refl have 0: "fs ! j \<notin> set (take j fs)"
    by (auto dest: set_take_disj_set_drop_if_distinct)

  have 1: "j \<le> component_of_term (sig_of_pair p0)" if "p0 \<in> set (p # ps)" for p0
  proof -
    from that have "p0 = p \<or> p0 \<in> set ps" by simp
    thus ?thesis
    proof
      assume "p0 = p"
      thus ?thesis by (simp add: j_def lt_p' sig_p)
    next
      assume "p0 \<in> set ps"
      from inv have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
      hence "Ball (set ps) (pair_ord p)" by simp
      hence "pair_ord p p0" using \<open>p0 \<in> set ps\<close> ..
      hence "lt p' \<preceq>\<^sub>t sig_of_pair p0" by (simp add: pair_ord_def lt_p' sig_p)
      thus ?thesis using pot by (auto simp add: is_pot_ord j_def term_simps)
    qed
  qed
  with assms(1) inv have gb: "punit.is_Groebner_basis (rep_list ` set ?bs)"
    by (rule rb_aux_inv_is_Groebner_basis)

  have "p' \<in> sig_inv_set' (Suc j)"
  proof (rule sig_inv_setI')
    fix v
    assume "v \<in> keys p'"
    hence "v \<preceq>\<^sub>t lt p'" by (rule lt_max_keys)
    with pot have "component_of_term v \<le> j" unfolding j_def by (rule is_pot_ordD2)
    thus "component_of_term v < Suc j" by simp
  qed
  hence 2: "keys (vectorize_poly p') \<subseteq> {0..<Suc j}" by (rule sig_inv_setD)
  moreover assume "rep_list p' = 0"
  ultimately have "0 = (\<Sum>k\<in>keys (pm_of_idx_pm ?fs (vectorize_poly p')).
                              lookup (pm_of_idx_pm ?fs (vectorize_poly p')) k * k)"
    by (simp add: rep_list_def ideal.rep_def pm_of_idx_pm_take)
  also have "... = (\<Sum>k\<in>set ?fs. lookup (pm_of_idx_pm ?fs (vectorize_poly p')) k * k)"
    using finite_set keys_pm_of_idx_pm_subset by (rule sum.mono_neutral_left) (simp add: in_keys_iff)

  also from 2 have "... = (\<Sum>k\<in>set ?fs. lookup (pm_of_idx_pm fs (vectorize_poly p')) k * k)"
    by (simp only: pm_of_idx_pm_take)
  also have "... = lookup (pm_of_idx_pm fs (vectorize_poly p')) (fs ! j) * fs ! j +
                    (\<Sum>k\<in>set (take j fs). lookup (pm_of_idx_pm fs (vectorize_poly p')) k * k)"
    using \<open>j < length fs\<close> by (simp add: take_Suc_conv_app_nth q_def sum.insert[OF finite_set 0])
  also have "... = q * fs ! j + (\<Sum>k\<in>set (take j fs). lookup (pm_of_idx_pm fs (vectorize_poly p')) k * k)"
    using fs_distinct \<open>j < length fs\<close> by (simp only: lookup_pm_of_idx_pm_distinct q_def)
  finally have "- (q * fs ! j) =
                          (\<Sum>k\<in>set (take j fs). lookup (pm_of_idx_pm fs (vectorize_poly p')) k * k)"
    by (simp add: add_eq_0_iff)
  hence "- (q * fs ! j) \<in> ideal (set (take j fs))" by (simp add: ideal.sum_in_spanI)
  hence "- (- (q * fs ! j)) \<in> ideal (set (take j fs))" by (rule ideal.span_neg)
  hence "q * fs ! j \<in> ideal (set (take j fs))" by simp
  with assms(2) \<open>j < length fs\<close> have "q \<in> ideal (set (take j fs))" by (rule is_regular_sequenceD)
  also from assms(3) 1 have "... \<subseteq> ideal (rep_list ` set ?bs)"
    by (rule rb_aux_inv2_ideal_subset)
  finally have "q \<in> ideal (rep_list ` set ?bs)" .
  with gb obtain g where "g \<in> rep_list ` set ?bs" and "g \<noteq> 0" and "punit.lt g adds punit.lt q"
    using \<open>q \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
  from this(1) obtain b where "b \<in> set bs" and "component_of_term (lt b) < j" and g: "g = rep_list b"
    by auto
  from assms(3) \<open>j < length fs\<close> _ this(1, 2)
  have "\<exists>s\<in>set (new_syz_sigs ss bs p). s adds\<^sub>t term_of_pair (punit.lt (rep_list b), j)"
  proof (rule rb_aux_inv2_preserved_0)
    show "Inr j \<notin> set ps"
    proof
      assume "Inr j \<in> set ps"
      with inv have "sig_of_pair p \<noteq> term_of_pair (0, j)" by (rule Inr_in_tailD)
      hence "lt p' \<noteq> term_of_pair (0, j)" by (simp add: lt_p' sig_p)
      from inv have "sorted_wrt pair_ord (p # ps)" by (rule rb_aux_inv_D5)
      hence "Ball (set ps) (pair_ord p)" by simp
      hence "pair_ord p (Inr j)" using \<open>Inr j \<in> set ps\<close> ..
      hence "lt p' \<preceq>\<^sub>t term_of_pair (0, j)" by (simp add: pair_ord_def lt_p' sig_p)
      hence "lp p' \<preceq> 0" using pot by (simp add: is_pot_ord j_def term_simps)
      hence "lp p' = 0" using zero_min by (rule ordered_powerprod_lin.antisym)
      hence "lt p' = term_of_pair (0, j)" by (metis j_def term_of_pair_pair)
      with \<open>lt p' \<noteq> term_of_pair (0, j)\<close> show False ..
    qed
  qed
  then obtain s where s_in: "s \<in> set (new_syz_sigs ss bs p)" and "s adds\<^sub>t term_of_pair (punit.lt g, j)"
    unfolding g ..
  from this(2) \<open>punit.lt g adds punit.lt q\<close> have "s adds\<^sub>t term_of_pair (punit.lt q, j)"
    by (metis adds_minus_splus adds_term_splus component_of_term_of_pair pp_of_term_of_pair)
  also have "... = lt p'" by (simp only: q_def j_def lt_lookup_vectorize term_simps)
  finally have "s adds\<^sub>t sig_of_pair p" by (simp only: lt_p' sig_p)
  with s_in have pred: "is_pred_syz (new_syz_sigs ss bs p) (sig_of_pair p)"
    by (auto simp: is_pred_syz_def)
  have "sig_crit bs (new_syz_sigs ss bs p) p"
  proof (rule sum_prodE)
    fix x y
    assume "p = Inl (x, y)"
    thus ?thesis using pred by (auto simp: ord_term_lin.max_def split: if_splits)
  next
    fix i
    assume "p = Inr i"
    thus ?thesis using pred by simp
  qed
  with assms(4) show False ..
qed

corollary rb_aux_no_zero_red':
  assumes "hom_grading dgrad" and "is_regular_sequence fs" and "rb_aux_inv2 (fst args)"
  shows "snd (rb_aux args) = snd args"
proof -
  from assms(3) have "rb_aux_inv (fst args)" by (rule rb_aux_inv2_D1)
  hence "rb_aux_dom args" by (rule rb_aux_domI)
  thus ?thesis using assms(3)
  proof (induct args rule: rb_aux.pinduct)
    case (1 bs ss z)
    show ?case by (simp only: rb_aux.psimps(1)[OF 1(1)])
  next
    case (2 bs ss p ps z)
    from 2(5) have *: "rb_aux_inv2 (bs, ss, p # ps)" by (simp only: fst_conv)
    show ?case
    proof (simp add: rb_aux.psimps(2)[OF 2(1)] Let_def, intro conjI impI)
      note refl
      moreover assume "sig_crit bs (new_syz_sigs ss bs p) p"
      moreover from * this have "rb_aux_inv2 (fst ((bs, new_syz_sigs ss bs p, ps), z))"
        unfolding fst_conv by (rule rb_aux_inv2_preserved_1)
      ultimately have "snd (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) =
                        snd ((bs, new_syz_sigs ss bs p, ps), z)" by (rule 2(2))
      thus "snd (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) = z" by (simp only: snd_conv)
      thus "snd (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) = z" .
    next
      assume "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
      with assms(1, 2) * have "rep_list (sig_trd bs (poly_of_pair p)) \<noteq> 0"
        by (rule rb_aux_inv2_no_zero_red)
      moreover assume "rep_list (sig_trd bs (poly_of_pair p)) = 0"
      ultimately show "snd (rb_aux ((bs, lt (sig_trd bs (poly_of_pair p)) #
                          new_syz_sigs ss bs p, ps), Suc z)) = z" ..
    next
      define p' where "p' = sig_trd bs (poly_of_pair p)"
      note refl
      moreover assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p"
      moreover note p'_def
      moreover assume b: "rep_list p' \<noteq> 0"
      moreover have "rb_aux_inv2 (fst ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z))"
        using * a b unfolding fst_conv p'_def by (rule rb_aux_inv2_preserved_3)
      ultimately have "snd (rb_aux ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z)) =
            snd ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z)"
        by (rule 2(4))
      thus "snd (rb_aux ((p' # bs, new_syz_sigs ss bs p, add_spairs ps bs p'), z)) = z"
        by (simp only: snd_conv)
    qed
  qed
qed

corollary rb_aux_no_zero_red:
  assumes "hom_grading dgrad" and "is_regular_sequence fs"
  shows "snd (rb_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)) = z"
proof -
  let ?args = "(([]::('t \<Rightarrow>\<^sub>0 'b) list, Koszul_syz_sigs fs,
                  (map Inr [0..<length fs])::((('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) + nat) list), z)"
  from rb_aux_inv_init have "rb_aux_inv2 (fst ?args)" by simp
  with assms have "snd (rb_aux ?args) = snd ?args" by (rule rb_aux_no_zero_red')
  thus ?thesis by (simp only: snd_conv)
qed

corollary rb_no_zero_red:
  assumes "hom_grading dgrad" and "is_regular_sequence fs"
  shows "snd rb = 0"
  using rb_aux_no_zero_red[OF assms, of 0] by (auto simp: rb_def split: prod.split)

end

subsection \<open>Sig-Poly-Pairs\<close>

text \<open>We now prove that the algorithms defined for sig-poly-pairs (i.\,e. those whose names end with
  \<open>_spp\<close>) behave exactly as those defined for module elements. More precisely, if \<open>A\<close> is some
  algorithm defined for module elements, we prove something like
  @{prop "spp_of (A x) = A_spp (spp_of x)"}.\<close>

fun spp_inv_pair :: "((('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))) + nat) \<Rightarrow> bool" where
  "spp_inv_pair (Inl (p, q)) = (spp_inv p \<and> spp_inv q)" |
  "spp_inv_pair (Inr j) = True"

fun app_pair :: "('x \<Rightarrow> 'y) \<Rightarrow> (('x \<times> 'x) + nat) \<Rightarrow> (('y \<times> 'y) + nat)" where
  "app_pair f (Inl (p, q)) = Inl (f p, f q)" |
  "app_pair f (Inr j) = Inr j"

fun app_args :: "('x \<Rightarrow> 'y) \<Rightarrow> (('x list \<times> 'z \<times> ((('x \<times> 'x) + nat) list)) \<times> nat) \<Rightarrow>
                     (('y list \<times> 'z \<times> ((('y \<times> 'y) + nat) list)) \<times> nat)" where
  "app_args f ((as, bs, cs), n) = ((map f as, bs, map (app_pair f) cs), n)"

lemma app_pair_spp_of_vec_of:
  assumes "spp_inv_pair p"
  shows "app_pair spp_of (app_pair vec_of p) = p"
proof (rule sum_prodE)
  fix a b
  assume p: "p = Inl (a, b)"
  from assms have "spp_inv a" and "spp_inv b" by (simp_all add: p)
  thus ?thesis by (simp add: p spp_of_vec_of)
qed simp

lemma map_app_pair_spp_of_vec_of:
  assumes "list_all spp_inv_pair ps"
  shows "map (app_pair spp_of \<circ> app_pair vec_of) ps = ps"
proof (rule map_idI)
  fix p
  assume "p \<in> set ps"
  with assms have "spp_inv_pair p" by (simp add: list_all_def)
  hence "app_pair spp_of (app_pair vec_of p) = p" by (rule app_pair_spp_of_vec_of)
  thus "(app_pair spp_of \<circ> app_pair vec_of) p = p" by simp
qed

lemma snd_app_args: "snd (app_args f args) = snd args"
  by (metis prod.exhaust app_args.simps snd_conv)

lemma new_syz_sigs_alt_spp:
  "new_syz_sigs ss bs p = new_syz_sigs_spp ss (map spp_of bs) (app_pair spp_of p)"
proof (rule sum_prodE)
  fix a b
  assume "p = Inl (a, b)"
  thus ?thesis by simp
next
  fix j
  assume "p = Inr j"
  thus ?thesis by (simp add: comp_def spp_of_def)
qed

lemma is_rewritable_alt_spp:
  assumes "0 \<notin> set bs"
  shows "is_rewritable bs p u = is_rewritable_spp (map spp_of bs) (spp_of p) u"
proof -
  from assms have "b \<in> set bs \<Longrightarrow> b \<noteq> 0" for b by blast
  thus ?thesis by (auto simp: is_rewritable_def is_rewritable_spp_def fst_spp_of)
qed

lemma spair_sigs_alt_spp: "spair_sigs p q = spair_sigs_spp (spp_of p) (spp_of q)"
  by (simp add: spair_sigs_def spair_sigs_spp_def Let_def fst_spp_of snd_spp_of)

lemma sig_crit_alt_spp:
  assumes "0 \<notin> set bs"
  shows "sig_crit bs ss p = sig_crit_spp (map spp_of bs) ss (app_pair spp_of p)"
proof (rule sum_prodE)
  fix a b
  assume p: "p = Inl (a, b)"
  from assms show ?thesis by (simp add: p spair_sigs_alt_spp is_rewritable_alt_spp)
qed simp

lemma spair_alt_spp:
  assumes "is_regular_spair p q"
  shows "spp_of (spair p q) = spair_spp (spp_of p) (spp_of q)"
proof -
  let ?t1 = "punit.lt (rep_list p)"
  let ?t2 = "punit.lt (rep_list q)"
  let ?l = "lcs ?t1 ?t2"
  from assms have p: "rep_list p \<noteq> 0" and q: "rep_list q \<noteq> 0"
    by (rule is_regular_spairD1, rule is_regular_spairD2)
  hence "p \<noteq> 0" and "q \<noteq> 0" and 1: "punit.lc (rep_list p) \<noteq> 0" and 2: "punit.lc (rep_list q) \<noteq> 0"
    by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
  from assms have "lt (monom_mult (1 / punit.lc (rep_list p)) (?l - ?t1) p) \<noteq>
                    lt (monom_mult (1 / punit.lc (rep_list q)) (?l - ?t2) q)" (is "?u \<noteq> ?v")
    by (rule is_regular_spairD3)
  hence "lt (monom_mult (1 / punit.lc (rep_list p)) (?l - ?t1) p - monom_mult (1 / punit.lc (rep_list q)) (?l - ?t2) q) =
          ord_term_lin.max ?u ?v" by (rule lt_minus_distinct_eq_max)
  moreover from \<open>p \<noteq> 0\<close> 1 have "?u = (?l - ?t1) \<oplus> fst (spp_of p)" by (simp add: lt_monom_mult fst_spp_of)
  moreover from \<open>q \<noteq> 0\<close> 2 have "?v = (?l - ?t2) \<oplus> fst (spp_of q)" by (simp add: lt_monom_mult fst_spp_of)
  ultimately show ?thesis
    by (simp add: spair_spp_def spair_def Let_def spp_of_def rep_list_minus rep_list_monom_mult)
qed

lemma sig_trd_spp_body_alt_Some:
  assumes "find_sig_reducer (map spp_of bs) v (punit.lt p) 0 = Some i"
  shows "sig_trd_spp_body (map spp_of bs) v (p, r) =
          (punit.lower (p - local.punit.monom_mult (punit.lc p / punit.lc (rep_list (bs ! i)))
                  (punit.lt p - punit.lt (rep_list (bs ! i))) (rep_list (bs ! i))) (punit.lt p), r)"
      (is ?thesis1)
    and "sig_trd_spp_body (map spp_of bs) v (p, r) =
          (p - local.punit.monom_mult (punit.lc p / punit.lc (rep_list (bs ! i)))
                  (punit.lt p - punit.lt (rep_list (bs ! i))) (rep_list (bs ! i)), r)"
      (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2"
  proof (cases "p = 0")
    case True
    show ?thesis by (simp add: assms, simp add: True)
  next
    case False
    from assms have "i < length bs" by (rule find_sig_reducer_SomeD)
    hence eq1: "snd (map spp_of bs ! i) = rep_list (bs ! i)" by (simp add: snd_spp_of)
    from assms have "rep_list (bs ! i) \<noteq> 0" and "punit.lt (rep_list (bs ! i)) adds punit.lt p"
      by (rule find_sig_reducer_SomeD)+
    hence nz: "rep_list (bs ! i) \<noteq> 0" and adds: "punit.lt (rep_list (bs ! i)) adds punit.lt p"
      by (simp_all add: snd_spp_of)
    from nz have "punit.lc (rep_list (bs ! i)) \<noteq> 0" by (rule punit.lc_not_0)
    moreover from False have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
    ultimately have eq2: "punit.lt (punit.monom_mult (punit.lc p / punit.lc (rep_list (bs ! i)))
                        (punit.lt p - punit.lt (rep_list (bs ! i))) (rep_list (bs ! i))) = punit.lt p"
      (is "punit.lt ?p = _") using nz adds by (simp add: lp_monom_mult adds_minus)
    have ?thesis1 by (simp add: assms Let_def eq1 punit.lower_minus punit.tail_monom_mult[symmetric],
                      simp add: punit.tail_def eq2)
    moreover have ?thesis2
    proof (simp add: \<open>?thesis1\<close> punit.lower_id_iff disj_commute[of "p = ?p"] del: sig_trd_spp_body.simps)
      show "punit.lt (p - ?p) \<prec> punit.lt p \<or> p = ?p"
      proof (rule disjCI)
        assume "p \<noteq> ?p"
        hence "p - ?p \<noteq> 0" by simp
        moreover note eq2
        moreover from \<open>punit.lc (rep_list (bs ! i)) \<noteq> 0\<close> have "punit.lc ?p = punit.lc p" by simp
        ultimately show "punit.lt (p - ?p) \<prec> punit.lt p" by (rule punit.lt_minus_lessI)
      qed
    qed
    ultimately show ?thesis ..
  qed
  thus ?thesis1 and ?thesis2 by blast+
qed

lemma sig_trd_aux_alt_spp:
  assumes "fst args \<in> keys (rep_list (snd args))"
  shows "rep_list (sig_trd_aux bs args) =
              sig_trd_spp_aux (map spp_of bs) (lt (snd args))
                (rep_list (snd args) - punit.higher (rep_list (snd args)) (fst args),
                 punit.higher (rep_list (snd args)) (fst args))"
proof -
  from assms have "sig_trd_aux_dom bs args" by (rule sig_trd_aux_domI)
  thus ?thesis using assms
  proof (induct args rule: sig_trd_aux.pinduct)
    case (1 t p)
    define p' where "p' = (case find_sig_reducer (map spp_of bs) (lt p) t 0 of
                              None \<Rightarrow> p
                            | Some i \<Rightarrow> p -
                                monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                                 (t - punit.lt (rep_list (bs ! i))) (bs ! i))"
    define p'' where "p'' = punit.lower (rep_list p') t"
    from 1(3) have t_in: "t \<in> keys (rep_list p)" by simp
    hence "t \<in> keys (rep_list p - punit.higher (rep_list p) t)" (is "_ \<in> keys ?p")
      by (simp add: punit.keys_minus_higher)
    hence "?p \<noteq> 0" by auto
    hence eq1: "sig_trd_spp_aux bs0 v0 (?p, r0) = sig_trd_spp_aux bs0 v0 (sig_trd_spp_body bs0 v0 (?p, r0))"
      for bs0 v0 r0 by (simp add: sig_trd_spp_aux_simps del: sig_trd_spp_body.simps)
    from t_in have lt_p: "punit.lt ?p = t" and lc_p: "punit.lc ?p = lookup (rep_list p) t"
      and tail_p: "punit.tail ?p = punit.lower (rep_list p) t"
      by (rule punit.lt_minus_higher, rule punit.lc_minus_higher, rule punit.tail_minus_higher)
    have "lt p' = lt p \<and> punit.higher (rep_list p') t = punit.higher (rep_list p) t \<and>
          (\<forall>i. find_sig_reducer (map spp_of bs) (lt p) t 0 = Some i \<longrightarrow> lookup (rep_list p') t = 0)"
      (is "?A \<and> ?B \<and> ?C")
    proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
      case None
      thus ?thesis by (simp add: p'_def)
    next
      case (Some i)
      hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                            (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
      from Some have "punit.lt (rep_list (bs ! i)) adds t" by (rule find_sig_reducer_SomeD)
      hence eq: "t - punit.lt (rep_list (bs ! i)) + punit.lt (rep_list (bs ! i)) = t" by (rule adds_minus)
      from t_in Some have *: "sig_red_single (\<prec>\<^sub>t) (\<preceq>) p p' (bs ! i) (t - punit.lt (rep_list (bs ! i)))"
        unfolding p' by (rule find_sig_reducer_SomeD_red_single)
      hence **: "punit.red_single (rep_list p) (rep_list p') (rep_list (bs ! i)) (t - punit.lt (rep_list (bs ! i)))"
        by (rule sig_red_single_red_single)
      from * have ?A by (rule sig_red_single_regular_lt)
      moreover from punit.red_single_higher[OF **] have ?B by (simp add: eq)
      moreover have ?C
      proof (intro allI impI)
        from punit.red_single_lookup[OF **] show "lookup (rep_list p') t = 0" by (simp add: eq)
      qed
      ultimately show ?thesis by (intro conjI)
    qed
    hence lt_p': "lt p' = lt p" and higher_p': "punit.higher (rep_list p') t = punit.higher (rep_list p) t"
      and lookup_p': "\<And>i. find_sig_reducer (map spp_of bs) (lt p) t 0 = Some i \<Longrightarrow> lookup (rep_list p') t = 0"
      by blast+
    show ?case
    proof (simp add: sig_trd_aux.psimps[OF 1(1)] Let_def p'_def[symmetric] p''_def[symmetric], intro conjI impI)
      assume "p'' = 0"
      hence p'_decomp: "punit.higher (rep_list p) t + monomial (lookup (rep_list p') t) t = rep_list p'"
        using punit.higher_lower_decomp[of "rep_list p'" t] by (simp add: p''_def higher_p')
      show "rep_list p' = sig_trd_spp_aux (map spp_of bs) (lt p) (?p, punit.higher (rep_list p) t)"
      proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
        case None
        hence p': "p' = p" by (simp add: p'_def)
        from \<open>p'' = 0\<close> have eq2: "punit.tail ?p = 0" by (simp add: tail_p p''_def p')
        from p'_decomp show ?thesis by (simp add: p' eq1 lt_p lc_p None eq2 sig_trd_spp_aux_simps)
      next
        case (Some i)
        hence p': "p' = p - monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                            (t - punit.lt (rep_list (bs ! i))) (bs ! i)" by (simp add: p'_def)
        from \<open>p'' = 0\<close> have eq2: "punit.lower (rep_list p - punit.higher (rep_list p) t -
                punit.monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                  (t - punit.lt (rep_list (bs ! i))) (rep_list (bs ! i)))
                t = 0"
          by (simp add: p''_def p' rep_list_minus rep_list_monom_mult punit.lower_minus punit.lower_higher_zeroI)
        from Some have "lookup (rep_list p') t = 0" by (rule lookup_p')
        with p'_decomp have eq3: "rep_list p' = punit.higher (rep_list p) t" by simp
        show ?thesis by (simp add: sig_trd_spp_body_alt_Some(1) eq1 eq2 lt_p lc_p Some del: sig_trd_spp_body.simps,
                         simp add: sig_trd_spp_aux_simps eq3)
      qed
    next
      assume "p'' \<noteq> 0"
      hence "punit.lt p'' \<prec> t" unfolding p''_def by (rule punit.lt_lower_less)
      have higher_p'_2: "punit.higher (rep_list p') (punit.lt p'') =
                          punit.higher (rep_list p) t + monomial (lookup (rep_list p') t) t"
      proof (simp add: higher_p'[symmetric], rule poly_mapping_eqI)
        fix s
        show "lookup (punit.higher (rep_list p') (punit.lt p'')) s =
              lookup (punit.higher (rep_list p') t + monomial (lookup (rep_list p') t) t) s"
        proof (rule ordered_powerprod_lin.linorder_cases)
          assume "t \<prec> s"
          moreover from \<open>punit.lt p'' \<prec> t\<close> this have "punit.lt p'' \<prec> s"
            by (rule ordered_powerprod_lin.less_trans)
          ultimately show ?thesis by (simp add: lookup_add punit.lookup_higher_when lookup_single)
        next
          assume "t = s"
          with \<open>punit.lt p'' \<prec> t\<close> show ?thesis by (simp add: lookup_add punit.lookup_higher_when)
        next
          assume "s \<prec> t"
          show ?thesis
          proof (cases "punit.lt p'' \<prec> s")
            case True
            hence "lookup (punit.higher (rep_list p') (punit.lt p'')) s = lookup (rep_list p') s"
              by (simp add: punit.lookup_higher_when)
            also from \<open>s \<prec> t\<close> have "... = lookup p'' s" by (simp add: p''_def punit.lookup_lower_when)
            also from True have "... = 0" using punit.lt_le_iff by auto
            finally show ?thesis using \<open>s \<prec> t\<close>
              by (simp add: lookup_add lookup_single punit.lookup_higher_when)
          next
            case False
            with \<open>s \<prec> t\<close> show ?thesis by (simp add: lookup_add punit.lookup_higher_when lookup_single)
          qed
        qed
      qed
      have "rep_list (sig_trd_aux bs (punit.lt p'', p')) =
              sig_trd_spp_aux (map spp_of bs) (lt (snd (punit.lt p'', p')))
               (rep_list (snd (punit.lt p'', p')) -
                punit.higher (rep_list (snd (punit.lt p'', p'))) (fst (punit.lt p'', p')),
                punit.higher (rep_list (snd (punit.lt p'', p'))) (fst (punit.lt p'', p')))"
        using p'_def p''_def \<open>p'' \<noteq> 0\<close>
      proof (rule 1(2))
        from \<open>p'' \<noteq> 0\<close> have "punit.lt p'' \<in> keys p''" by (rule punit.lt_in_keys)
        also have "... \<subseteq> keys (rep_list p')" by (auto simp: p''_def punit.keys_lower)
        finally show "fst (punit.lt p'', p') \<in> keys (rep_list (snd (punit.lt p'', p')))" by simp
      qed
      also have "... = sig_trd_spp_aux (map spp_of bs) (lt p)
                         (rep_list p' - punit.higher (rep_list p') (punit.lt p''),
                          punit.higher (rep_list p') (punit.lt p''))"
        by (simp only: lt_p' fst_conv snd_conv)
      also have "... = sig_trd_spp_aux (map spp_of bs) (lt p) (?p, punit.higher (rep_list p) t)"
      proof (cases "find_sig_reducer (map spp_of bs) (lt p) t 0")
        case None
        hence p': "p' = p" by (simp add: p'_def)
        have "rep_list p - (punit.higher (rep_list p) t + monomial (lookup (rep_list p) t) t) =
              punit.lower (rep_list p) t"
          using punit.higher_lower_decomp[of "rep_list p" t] by (simp add: diff_eq_eq ac_simps)
        with higher_p'_2 show ?thesis by (simp add: eq1 lt_p lc_p tail_p p' None)
      next
        case (Some i)
        hence p': "rep_list p - punit.monom_mult (lookup (rep_list p) t / punit.lc (rep_list (bs ! i)))
                          (t - punit.lt (rep_list (bs ! i))) (rep_list (bs ! i)) = rep_list p'"
          by (simp add: p'_def rep_list_minus rep_list_monom_mult)
        from Some have "lookup (rep_list p') t = 0" by (rule lookup_p')
        with higher_p'_2 show ?thesis
          by (simp add: sig_trd_spp_body_alt_Some(2) eq1 lt_p lc_p tail_p Some
              diff_right_commute[of "rep_list p" "punit.higher (rep_list p) t"] p' del: sig_trd_spp_body.simps)
      qed
      finally show "rep_list (sig_trd_aux bs (punit.lt p'', p')) =
                     sig_trd_spp_aux (map spp_of bs) (lt p) (?p, punit.higher (rep_list p) t)" .
    qed
  qed
qed

lemma sig_trd_alt_spp: "spp_of (sig_trd bs p) = sig_trd_spp (map spp_of bs) (spp_of p)"
  unfolding sig_trd_def
proof (split if_split, intro conjI impI)
  assume "rep_list p = 0"
  thus "spp_of p = sig_trd_spp (map spp_of bs) (spp_of p)" by (simp add: spp_of_def sig_trd_spp_aux_simps)
next
  let ?args = "(punit.lt (rep_list p), p)"
  assume "rep_list p \<noteq> 0"
  hence a: "fst ?args \<in> keys (rep_list (snd ?args))" by (simp add: punit.lt_in_keys)
  hence "(sig_red (\<prec>\<^sub>t) (\<preceq>) (set bs))\<^sup>*\<^sup>* (snd ?args) (sig_trd_aux bs ?args)"
    by (rule sig_trd_aux_red_rtrancl)
  hence eq1: "lt (sig_trd_aux bs ?args) = lt (snd ?args)" by (rule sig_red_regular_rtrancl_lt)
  have eq2: "punit.higher (rep_list p) (punit.lt (rep_list p)) = 0"
    by (auto simp: punit.higher_eq_zero_iff punit.lt_max simp flip: not_in_keys_iff_lookup_eq_zero
            dest: punit.lt_max_keys)
  show "spp_of (sig_trd_aux bs (punit.lt (rep_list p), p)) = sig_trd_spp (map spp_of bs) (spp_of p)"
    by (simp add: spp_of_def eq1 eq2 sig_trd_aux_alt_spp[OF a])
qed

lemma is_regular_spair_alt_spp: "is_regular_spair p q \<longleftrightarrow> is_regular_spair_spp (spp_of p) (spp_of q)"
  by (auto simp: is_regular_spair_spp_def fst_spp_of snd_spp_of intro: is_regular_spairI
          dest: is_regular_spairD1 is_regular_spairD2 is_regular_spairD3)

lemma sig_of_spair_alt_spp: "sig_of_pair p = sig_of_pair_spp (app_pair spp_of p)"
proof (rule sum_prodE)
  fix a b
  assume p: "p = Inl (a, b)"
  show ?thesis by (simp add: p spair_sigs_def spair_sigs_spp_def spp_of_def)
qed simp

lemma pair_ord_alt_spp: "pair_ord x y \<longleftrightarrow> pair_ord_spp (app_pair spp_of x) (app_pair spp_of y)"
  by (simp add: pair_ord_spp_def pair_ord_def sig_of_spair_alt_spp)

lemma new_spairs_alt_spp:
  "map (app_pair spp_of) (new_spairs bs p) = new_spairs_spp (map spp_of bs) (spp_of p)"
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have "map (app_pair spp_of) (insort_wrt pair_ord (Inl (p, b)) (new_spairs bs p)) =
        insort_wrt pair_ord_spp (app_pair spp_of (Inl (p, b))) (map (app_pair spp_of) (new_spairs bs p))"
    by (rule map_insort_wrt, rule pair_ord_alt_spp[symmetric])
  thus ?case by (simp add: is_regular_spair_alt_spp Cons)
qed

lemma add_spairs_alt_spp:
  assumes "\<And>x. x \<in> set bs \<Longrightarrow> Inl (spp_of p, spp_of x) \<notin> app_pair spp_of ` set ps"
  shows "map (app_pair spp_of) (add_spairs ps bs p) =
          add_spairs_spp (map (app_pair spp_of) ps) (map spp_of bs) (spp_of p)"
proof -
  have "map (app_pair spp_of) (merge_wrt pair_ord (new_spairs bs p) ps) =
        merge_wrt pair_ord_spp (map (app_pair spp_of) (new_spairs bs p)) (map (app_pair spp_of) ps)"
  proof (rule map_merge_wrt, rule ccontr)
    assume "app_pair spp_of ` set (new_spairs bs p) \<inter> app_pair spp_of ` set ps \<noteq> {}"
    then obtain q' where "q' \<in> app_pair spp_of ` set (new_spairs bs p)"
      and q'_in: "q' \<in> app_pair spp_of ` set ps" by blast
    from this(1) obtain q where "q \<in> set (new_spairs bs p)" and q': "q' = app_pair spp_of q" ..
    from this(1) obtain x where x_in: "x \<in> set bs" and q: "q = Inl (p, x)"
      by (rule in_new_spairsE)
    have q': "q' = Inl (spp_of p, spp_of x)" by (simp add: q q')
    have "q' \<notin> app_pair spp_of ` set ps" unfolding q' using x_in by (rule assms)
    thus False using q'_in ..
  qed (simp only: pair_ord_alt_spp)
  thus ?thesis by (simp add: add_spairs_def add_spairs_spp_def new_spairs_alt_spp)
qed

lemma rb_aux_invD_app_args:
  assumes "rb_aux_inv (fst (app_args vec_of ((bs, ss, ps), z)))"
  shows "list_all spp_inv bs" and "list_all spp_inv_pair ps"
proof -
  from assms(1) have inv: "rb_aux_inv (map vec_of bs, ss, map (app_pair vec_of) ps)" by simp
  hence "rb_aux_inv1 (map vec_of bs)" by (rule rb_aux_inv_D1)
  hence "0 \<notin> rep_list ` set (map vec_of bs)" by (rule rb_aux_inv1_D2)
  hence "0 \<notin> vec_of ` set bs" using rep_list_zero by fastforce
  hence 1: "b \<in> set bs \<Longrightarrow> spp_inv b" for b by (auto simp: spp_inv_alt)
  thus "list_all spp_inv bs" by (simp add: list_all_def)

  have 2: "x \<in> set bs" if "vec_of x \<in> set (map vec_of bs)" for x
  proof -
    from that have "vec_of x \<in> vec_of ` set bs" by simp
    then obtain y where "y \<in> set bs" and eq: "vec_of x = vec_of y" ..
    from this(1) have "spp_inv y" by (rule 1)
    moreover have "vec_of y = vec_of x" by (simp only: eq)
    ultimately have "y = x" by (rule vec_of_inj)
    with \<open>y \<in> set bs\<close> show ?thesis by simp
  qed

  show "list_all spp_inv_pair ps" unfolding list_all_def
  proof (rule ballI)
    fix p
    assume "p \<in> set ps"
    show "spp_inv_pair p"
    proof (rule sum_prodE)
      fix a b
      assume p: "p = Inl (a, b)"
      from \<open>p \<in> set ps\<close> have "Inl (a, b) \<in> set ps" by (simp only: p)
      hence "app_pair vec_of (Inl (a, b)) \<in> app_pair vec_of ` set ps" by (rule imageI)
      hence "Inl (vec_of a, vec_of b) \<in> set (map (app_pair vec_of) ps)" by simp
      with inv have "vec_of a \<in> set (map vec_of bs)" and "vec_of b \<in> set (map vec_of bs)"
        by (rule rb_aux_inv_D3)+
      have "spp_inv a" by (rule 1, rule 2, fact)
      moreover have "spp_inv b" by (rule 1, rule 2, fact)
      ultimately show ?thesis by (simp add: p)
    qed simp
  qed
qed

lemma app_args_spp_of_vec_of:
  assumes "rb_aux_inv (fst (app_args vec_of args))"
  shows "app_args spp_of (app_args vec_of args) = args"
proof -
  obtain bs ss ps z where args: "args = ((bs, ss, ps), z)" using prod.exhaust by metis
  from assms have "list_all spp_inv bs" and *: "list_all spp_inv_pair ps" unfolding args
    by (rule rb_aux_invD_app_args)+
  from this(1) have "map (spp_of \<circ> vec_of) bs = bs" by (rule map_spp_of_vec_of)
  moreover from * have "map (app_pair spp_of \<circ> app_pair vec_of) ps = ps"
    by (rule map_app_pair_spp_of_vec_of)
  ultimately show ?thesis by (simp add: args)
qed

lemma poly_of_pair_alt_spp:
  assumes "distinct fs" and "rb_aux_inv (bs, ss, p # ps)"
  shows "spp_of (poly_of_pair p) = spp_of_pair (app_pair spp_of p)"
proof -
  show ?thesis
  proof (rule sum_prodE)
    fix a b
    assume p: "p = Inl (a, b)"
    hence "Inl (a, b) \<in> set (p # ps)" by simp
    with assms(2) have "is_regular_spair a b" by (rule rb_aux_inv_D3)
    thus ?thesis by (simp add: p spair_alt_spp)
  next
    fix j
    assume p: "p = Inr j"
    hence "Inr j \<in> set (p # ps)" by simp
    with assms(2) have "j < length fs" by (rule rb_aux_inv_D4)
    thus ?thesis by (simp add: p spp_of_def lt_monomial rep_list_monomial[OF assms(1)] term_simps)
  qed
qed

lemma rb_aux_alt_spp:
  assumes "rb_aux_inv (fst args)"
  shows "app_args spp_of (rb_aux args) = rb_spp_aux (app_args spp_of args)"
proof -
  from assms have "rb_aux_dom args" by (rule rb_aux_domI)
  thus ?thesis using assms
  proof (induct args rule: rb_aux.pinduct)
    case (1 bs ss z)
    show ?case by (simp add: rb_aux.psimps(1)[OF 1(1)] rb_spp_aux_Nil)
  next
    case (2 bs ss p ps z)
    let ?q = "sig_trd bs (poly_of_pair p)"

    from 2(5) have *: "rb_aux_inv (bs, ss, p # ps)" by (simp only: fst_conv)
    hence "rb_aux_inv1 bs" by (rule rb_aux_inv_D1)
    hence "0 \<notin> rep_list ` set bs" by (rule rb_aux_inv1_D2)
    hence "0 \<notin> set bs" by (force simp: rep_list_zero)
    hence eq1: "sig_crit_spp (map spp_of bs) ss' (app_pair spp_of p) \<longleftrightarrow> sig_crit bs ss' p" for ss'
      by (simp add: sig_crit_alt_spp)
    from fs_distinct * have eq2: "sig_trd_spp (map spp_of bs) (spp_of_pair (app_pair spp_of p)) = spp_of ?q"
      by (simp only: sig_trd_alt_spp poly_of_pair_alt_spp)

    show ?case
    proof (simp add: rb_aux.psimps(2)[OF 2(1)] Let_def, intro conjI impI)
      note refl
      moreover assume a: "sig_crit bs (new_syz_sigs ss bs p) p"
      moreover from * this have "rb_aux_inv (fst ((bs, new_syz_sigs ss bs p, ps), z))"
        unfolding fst_conv by (rule rb_aux_inv_preserved_1)
      ultimately have "app_args spp_of (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) =
                        rb_spp_aux (app_args spp_of ((bs, new_syz_sigs ss bs p, ps), z))"
        by (rule 2(2))
      also have "... = rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)"
        by (simp add: rb_spp_aux_Cons eq1 a new_syz_sigs_alt_spp[symmetric])
      finally show "app_args spp_of (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) =
            rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)" .
      thus "app_args spp_of (rb_aux ((bs, new_syz_sigs ss bs p, ps), z)) =
            rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)" .
    next
      assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and b: "rep_list ?q = 0"
      from * b have "rb_aux_inv (fst ((bs, lt ?q # new_syz_sigs ss bs p, ps), Suc z))"
        unfolding fst_conv by (rule rb_aux_inv_preserved_2)
      with refl a refl b have "app_args spp_of (rb_aux ((bs, lt ?q # new_syz_sigs ss bs p, ps), Suc z)) =
                               rb_spp_aux (app_args spp_of ((bs, lt ?q # new_syz_sigs ss bs p, ps), Suc z))"
        by (rule 2(3))
      also have "... = rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)"
        by (simp add: rb_spp_aux_Cons eq1 a Let_def eq2 snd_spp_of b fst_spp_of new_syz_sigs_alt_spp[symmetric])
      finally show "app_args spp_of (rb_aux ((bs, lt ?q # new_syz_sigs ss bs p, ps), Suc z)) =
                    rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)" .
    next
      assume a: "\<not> sig_crit bs (new_syz_sigs ss bs p) p" and b: "rep_list ?q \<noteq> 0"

      have "Inl (spp_of ?q, spp_of x) \<notin> app_pair spp_of ` set ps" for x
      proof
        assume "Inl (spp_of ?q, spp_of x) \<in> app_pair spp_of ` set ps"
        then obtain y where "y \<in> set ps" and eq0: "Inl (spp_of ?q, spp_of x) = app_pair spp_of y" ..
        obtain a b where y: "y = Inl (a, b)" and "spp_of ?q = spp_of a"
        proof (rule sum_prodE)
          fix a b
          assume "y = Inl (a, b)"
          moreover from eq0 have "spp_of ?q = spp_of a" by (simp add: \<open>y = Inl (a, b)\<close>)
          ultimately show ?thesis ..
        next
          fix j
          assume "y = Inr j"
          with eq0 show ?thesis by simp
        qed
        from this(2) have "lt ?q = lt a" by (simp add: spp_of_def)
        from \<open>y \<in> set ps\<close> have "y \<in> set (p # ps)" by simp
        with * have "a \<in> set bs" unfolding y by (rule rb_aux_inv_D3(1))
        hence "lt ?q \<in> lt ` set bs" unfolding \<open>lt ?q = lt a\<close> by (rule imageI)
        moreover from * a b have "lt ?q \<notin> lt ` set bs" by (rule rb_aux_inv_preserved_3)
        ultimately show False by simp
      qed
      hence eq3: "add_spairs_spp (map (app_pair spp_of) ps) (map spp_of bs) (spp_of ?q) =
                  map (app_pair spp_of) (add_spairs ps bs ?q)" by (simp add: add_spairs_alt_spp)

      from * a b have "rb_aux_inv (fst ((?q # bs, new_syz_sigs ss bs p, add_spairs ps bs ?q), z))"
        unfolding fst_conv by (rule rb_aux_inv_preserved_3)
      with refl a refl b
      have "app_args spp_of (rb_aux ((?q # bs, new_syz_sigs ss bs p, add_spairs ps bs ?q), z)) =
            rb_spp_aux (app_args spp_of ((?q # bs, new_syz_sigs ss bs p, add_spairs ps bs ?q), z))"
        by (rule 2(4))
      also have "... = rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)"
        by (simp add: rb_spp_aux_Cons eq1 a Let_def eq2 fst_spp_of snd_spp_of b eq3 new_syz_sigs_alt_spp[symmetric])
      finally show "app_args spp_of (rb_aux ((?q # bs, new_syz_sigs ss bs p, add_spairs ps bs ?q), z)) =
                     rb_spp_aux ((map spp_of bs, ss, app_pair spp_of p # map (app_pair spp_of) ps), z)" .
    qed
  qed
qed

corollary rb_spp_aux_alt:
  "rb_aux_inv (fst (app_args vec_of args)) \<Longrightarrow>
    rb_spp_aux args = app_args spp_of (rb_aux (app_args vec_of args))"
  by (simp only: rb_aux_alt_spp app_args_spp_of_vec_of)

corollary rb_spp_aux:
  "hom_grading dgrad \<Longrightarrow>
    punit.is_Groebner_basis (set (map snd (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))))"
          (is "_ \<Longrightarrow> ?thesis1")
  "ideal (set (map snd (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))))) = ideal (set fs)"
          (is "?thesis2")
  "set (map snd (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z))))) \<subseteq> punit_dgrad_max_set dgrad"
          (is "?thesis3")
  "0 \<notin> set (map snd (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))))"
          (is "?thesis4")
  "hom_grading dgrad \<Longrightarrow> is_pot_ord \<Longrightarrow> is_regular_sequence fs \<Longrightarrow>
    snd (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)) = z"
          (is "_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?thesis5")
  "rword_strict = rw_rat_strict \<Longrightarrow> p \<in> set (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))) \<Longrightarrow>
    q \<in> set (fst (fst (rb_spp_aux (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)))) \<Longrightarrow> p \<noteq> q \<Longrightarrow>
    punit.lt (snd p) adds punit.lt (snd q) \<Longrightarrow> punit.lt (snd p) \<oplus> fst q \<prec>\<^sub>t punit.lt (snd q) \<oplus> fst p"
proof -
  let ?args = "(([], Koszul_syz_sigs fs, map Inr [0..<length fs]), z)"
  have eq0: "app_pair vec_of \<circ> Inr = Inr" by (intro ext, simp)
  have eq1: "fst (fst (app_args spp_of a)) = map spp_of (fst (fst a))" for a::"(_ \<times> ('t list) \<times> _) \<times> _"
  proof -
    obtain bs ss ps z where "a = ((bs, ss, ps), z)" using prod.exhaust by metis
    thus ?thesis by simp
  qed
  have eq2: "snd \<circ> spp_of = rep_list" by (intro ext, simp add: snd_spp_of)
  have "rb_aux_inv (fst (app_args vec_of ?args))" by (simp add: eq0 rb_aux_inv_init)
  hence eq3: "rb_spp_aux ?args = app_args spp_of (rb_aux (app_args vec_of ?args))"
    by (rule rb_spp_aux_alt)

  {
    assume "hom_grading dgrad"
    with rb_aux_is_Groebner_basis show ?thesis1 by (simp add: eq0 eq1 eq2 eq3 del: set_map)
  }

  from ideal_rb_aux show ?thesis2 by (simp add: eq0 eq1 eq2 eq3 del: set_map)

  from dgrad_max_set_closed_rb_aux show ?thesis3 by (simp add: eq0 eq1 eq2 eq3 del: set_map)

  from rb_aux_nonzero show ?thesis4 by (simp add: eq0 eq1 eq2 eq3 del: set_map)

  {
    assume "is_pot_ord" and "hom_grading dgrad" and "is_regular_sequence fs"
    hence "snd (rb_aux ?args) = z" by (rule rb_aux_no_zero_red)
    thus ?thesis5 by (simp add: snd_app_args eq0 eq3)
  }

  {
    from rb_aux_nonzero have "0 \<notin> rep_list ` set (fst (fst (rb_aux ?args)))"
      (is "0 \<notin> rep_list ` ?G") by simp
    assume "rword_strict = rw_rat_strict"
    hence "is_min_sig_GB dgrad ?G" by (rule rb_aux_is_min_sig_GB)
    hence rl: "\<And>g. g \<in> ?G \<Longrightarrow> \<not> is_sig_red (\<preceq>\<^sub>t) (=) (?G - {g}) g" by (simp add: is_min_sig_GB_def)
    assume "p \<in> set (fst (fst (rb_spp_aux ?args)))"
    also have "... = spp_of ` ?G" by (simp add: eq0 eq1 eq3)
    finally obtain p' where "p' \<in> ?G" and p: "p = spp_of p'" ..
    assume "q \<in> set (fst (fst (rb_spp_aux ?args)))"
    also have "... = spp_of ` ?G" by (simp add: eq0 eq1 eq3)
    finally obtain q' where "q' \<in> ?G" and q: "q = spp_of q'" ..
    from this(1) have 1: "\<not> is_sig_red (\<preceq>\<^sub>t) (=) (?G - {q'}) q'" by (rule rl)
    assume "p \<noteq> q" and "punit.lt (snd p) adds punit.lt (snd q)"
    hence "p' \<noteq> q'" and adds: "punit.lt (rep_list p') adds punit.lt (rep_list q')"
      by (auto simp: p q snd_spp_of)
    show "punit.lt (snd p) \<oplus> fst q \<prec>\<^sub>t punit.lt (snd q) \<oplus> fst p"
    proof (rule ccontr)
      assume "\<not> punit.lt (snd p) \<oplus> fst q \<prec>\<^sub>t punit.lt (snd q) \<oplus> fst p"
      hence le: "punit.lt (rep_list q') \<oplus> lt p' \<preceq>\<^sub>t punit.lt (rep_list p') \<oplus> lt q'"
        by (simp add: p q spp_of_def)
      from \<open>p' \<noteq> q'\<close> \<open>p' \<in> ?G\<close> have "p' \<in> ?G - {q'}" by simp
      moreover from \<open>p' \<in> ?G\<close> \<open>0 \<notin> rep_list ` ?G\<close> have "rep_list p' \<noteq> 0" by fastforce
      moreover from \<open>q' \<in> ?G\<close> \<open>0 \<notin> rep_list ` ?G\<close> have "rep_list q' \<noteq> 0" by fastforce
      moreover note adds
      moreover have "ord_term_lin.is_le_rel (\<preceq>\<^sub>t)" by simp
      ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) (?G - {q'}) q'" using le by (rule is_sig_red_top_addsI)
      with 1 show False ..
    qed
  }
qed

end

end

end

end

end

definition gb_sig_z ::
    "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b::field)) list \<times> nat)"
  where "gb_sig_z rword_strict fs0 =
              (let fs = rev (remdups (rev (removeAll 0 fs0)));
                   res = rb_spp_aux fs rword_strict (([], Koszul_syz_sigs fs, map Inr [0..<length fs]), 0) in
                  (fst (fst res), snd res))"

text \<open>The second return value of @{const gb_sig_z} is the total number of zero-reductions.\<close>

definition gb_sig :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "gb_sig rword_strict fs0 = map snd (fst (gb_sig_z rword_strict fs0))"

theorem
  assumes "\<And>fs. is_strict_rewrite_ord fs rword_strict"
  shows gb_sig_isGB: "punit.is_Groebner_basis (set (gb_sig rword_strict fs))" (is ?thesis1)
    and gb_sig_ideal: "ideal (set (gb_sig rword_strict fs)) = ideal (set fs)" (is ?thesis2)
    and dgrad_p_set_closed_gb_sig:
        "dickson_grading d \<Longrightarrow> set fs \<subseteq> punit.dgrad_p_set d m \<Longrightarrow> set (gb_sig rword_strict fs) \<subseteq> punit.dgrad_p_set d m"
          (is "_ \<Longrightarrow> _ \<Longrightarrow> ?thesis3")
    and gb_sig_nonzero: "0 \<notin> set (gb_sig rword_strict fs)" (is ?thesis4)
    and gb_sig_no_zero_red: "is_pot_ord \<Longrightarrow> is_regular_sequence fs \<Longrightarrow> snd (gb_sig_z rword_strict fs) = 0"
proof -
  from ex_hgrad obtain d0::"'a \<Rightarrow> nat" where "dickson_grading d0 \<and> hom_grading d0" ..
  hence dg: "dickson_grading d0" and hg: "hom_grading d0" by simp_all
  define fs1 where "fs1 = rev (remdups (rev (removeAll 0 fs)))"
  note assms dg
  moreover have "distinct fs1" and "0 \<notin> set fs1" by (simp_all add: fs1_def)
  ultimately have "ideal (set (gb_sig rword_strict fs)) = ideal (set fs1)" and ?thesis4
    unfolding gb_sig_def gb_sig_z_def fst_conv fs1_def Let_def by (rule rb_spp_aux)+
  thus ?thesis2 and ?thesis4 by (simp_all add: fs1_def ideal.span_Diff_zero)

  from assms dg \<open>distinct fs1\<close> \<open>0 \<notin> set fs1\<close> hg show ?thesis1
    unfolding gb_sig_def gb_sig_z_def fst_conv fs1_def Let_def by (rule rb_spp_aux)

  {
    assume dg: "dickson_grading d" and *: "set fs \<subseteq> punit.dgrad_p_set d m"
    show ?thesis3
    proof (cases "set fs \<subseteq> {0}")
      case True
      hence "removeAll 0 fs = []"
        by (metis (no_types, lifting) Diff_iff ex_in_conv set_empty2 set_removeAll subset_singleton_iff)
      thus ?thesis by (simp add: gb_sig_def gb_sig_z_def Let_def rb_spp_aux_Nil)
    next
      case False
      have "set fs1 \<subseteq> set fs" by (fastforce simp: fs1_def)
      hence "Keys (set fs1) \<subseteq> Keys (set fs)" by (rule Keys_mono)
      hence "d ` Keys (set fs1) \<subseteq> d ` Keys (set fs)" by (rule image_mono)
      hence "insert (d 0) (d ` Keys (set fs1)) \<subseteq> insert (d 0) (d ` Keys (set fs))" by (rule insert_mono)
      moreover have "insert (d 0) (d ` Keys (set fs1)) \<noteq> {}" by simp
      moreover have "finite (insert (d 0) (d ` Keys (set fs)))"
        by (simp add: finite_Keys)
      ultimately have le: "Max (insert (d 0) (d ` Keys (set fs1))) \<le>
                            Max (insert (d 0) (d ` Keys (set fs)))" by (rule Max_mono)
      from assms dg have "set (gb_sig rword_strict fs) \<subseteq> punit_dgrad_max_set (TYPE('b)) fs1 d"
        using \<open>distinct fs1\<close> \<open>0 \<notin> set fs1\<close>
        unfolding gb_sig_def gb_sig_z_def fst_conv fs1_def Let_def by (rule rb_spp_aux)
      also have "punit_dgrad_max_set (TYPE('b)) fs1 d \<subseteq> punit_dgrad_max_set (TYPE('b)) fs d"
        by (rule punit.dgrad_p_set_subset, simp add: dgrad_max_def le)
      also from dg * False have "... \<subseteq> punit.dgrad_p_set d m"
        by (rule punit_dgrad_max_set_subset_dgrad_p_set)
      finally show ?thesis .
    qed
  }

  {
    assume "is_regular_sequence fs"
    note assms dg \<open>distinct fs1\<close> \<open>0 \<notin> set fs1\<close> hg
    moreover assume "is_pot_ord"
    moreover from \<open>is_regular_sequence fs\<close> have "is_regular_sequence fs1" unfolding fs1_def
      by (intro is_regular_sequence_remdups is_regular_sequence_removeAll_zero)
    ultimately show "snd (gb_sig_z rword_strict fs) = 0"
      unfolding gb_sig_def gb_sig_z_def snd_conv fs1_def Let_def by (rule rb_spp_aux)
  }
qed

theorem gb_sig_z_is_min_sig_GB:
  assumes "p \<in> set (fst (gb_sig_z rw_rat_strict fs))" and "q \<in> set (fst (gb_sig_z rw_rat_strict fs))"
    and "p \<noteq> q" and "punit.lt (snd p) adds punit.lt (snd q)"
  shows "punit.lt (snd p) \<oplus> fst q \<prec>\<^sub>t punit.lt (snd q) \<oplus> fst p"
proof -
  define fs1 where "fs1 = rev (remdups (rev (removeAll 0 fs)))"
  from ex_hgrad obtain d0::"'a \<Rightarrow> nat" where "dickson_grading d0 \<and> hom_grading d0" ..
  hence "dickson_grading d0" ..
  note rw_rat_strict_is_strict_rewrite_ord this
  moreover have "distinct fs1" and "0 \<notin> set fs1" by (simp_all add: fs1_def)
  moreover note refl assms
  ultimately show ?thesis unfolding gb_sig_z_def fst_conv fs1_def Let_def by (rule rb_spp_aux)
qed

text \<open>Summarizing, these are the four main results proved in this theory:
  \<^item> @{thm gb_sig_isGB},
  \<^item> @{thm gb_sig_ideal},
  \<^item> @{thm gb_sig_no_zero_red}, and
  \<^item> @{thm gb_sig_z_is_min_sig_GB}.\<close>

end (* qpm_inf_term *)

end (* theory *)
