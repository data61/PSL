(* Author: Alexander Maletzky *)

section \<open>Quasi-Poly-Mapping Power-Products\<close>

theory Quasi_PM_Power_Products
  imports MPoly_Type_Class_Ordered
begin

text \<open>In this theory we introduce a subclass of @{class graded_dickson_powerprod} that approximates
  polynomial mappings even closer. We need this class for signature-based Gr\"obner basis algorithms.\<close>

definition (in monoid_add) hom_grading_fun :: "('a \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "hom_grading_fun d f \<longleftrightarrow> (\<forall>n. (\<forall>s t. f n (s + t) = f n s + f n t) \<and>
          (\<forall>t. d (f n t) \<le> n \<and> (d t \<le> n \<longrightarrow> f n t = t)))"

definition (in monoid_add) hom_grading :: "('a \<Rightarrow> nat) \<Rightarrow> bool"
  where "hom_grading d \<longleftrightarrow> (\<exists>f. hom_grading_fun d f)"

definition (in monoid_add) decr_grading :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where "decr_grading d = (SOME f. hom_grading_fun d f)"

lemma decr_grading:
  assumes "hom_grading d"
  shows "hom_grading_fun d (decr_grading d)"
proof -
  from assms obtain f where "hom_grading_fun d f" unfolding hom_grading_def ..
  thus ?thesis unfolding decr_grading_def by (metis someI)
qed

lemma decr_grading_plus:
  "hom_grading d \<Longrightarrow> decr_grading d n (s + t) = decr_grading d n s + decr_grading d n t"
  using decr_grading unfolding hom_grading_fun_def by blast

lemma decr_grading_zero:
  assumes "hom_grading d"
  shows "decr_grading d n 0 = (0::'a::cancel_comm_monoid_add)"
proof -
  have "decr_grading d n 0 = decr_grading d n (0 + 0)" by simp
  also from assms have "... = decr_grading d n 0 + decr_grading d n 0" by (rule decr_grading_plus)
  finally show ?thesis by simp
qed

lemma decr_grading_le: "hom_grading d \<Longrightarrow> d (decr_grading d n t) \<le> n"
  using decr_grading unfolding hom_grading_fun_def by blast

lemma decr_grading_idI: "hom_grading d \<Longrightarrow> d t \<le> n \<Longrightarrow> decr_grading d n t = t"
  using decr_grading unfolding hom_grading_fun_def by blast

class quasi_pm_powerprod = ulcs_powerprod +
  assumes ex_hgrad: "\<exists>d::'a \<Rightarrow> nat. dickson_grading d \<and> hom_grading d"
begin

subclass graded_dickson_powerprod
proof
  from ex_hgrad show "\<exists>d. dickson_grading d" by blast
qed

end (* quasi_pm_powerprod *)

lemma hom_grading_varnum:
  "hom_grading ((varnum X)::('x::countable \<Rightarrow>\<^sub>0 'b::add_wellorder) \<Rightarrow> nat)"
proof -
  define f where "f = (\<lambda>n t. (except t (- (X \<union> {x. elem_index x < n})))::'x \<Rightarrow>\<^sub>0 'b)"
  show ?thesis unfolding hom_grading_def hom_grading_fun_def
  proof (intro exI allI conjI impI)
    fix n s t
    show "f n (s + t) = f n s + f n t" by (simp only: f_def except_plus)
  next
    fix n t
    show "varnum X (f n t) \<le> n" by (auto simp: varnum_le_iff keys_except f_def)
  next
    fix n t
    show "varnum X t \<le> n \<Longrightarrow> f n t = t" by (auto simp: f_def except_id_iff varnum_le_iff)
  qed
qed

instance poly_mapping :: (countable, add_wellorder) quasi_pm_powerprod
  by (standard, intro exI conjI, fact dickson_grading_varnum_empty, fact hom_grading_varnum)

context term_powerprod
begin

definition decr_grading_term :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 't \<Rightarrow> 't"
  where "decr_grading_term d n v = term_of_pair (decr_grading d n (pp_of_term v), component_of_term v)"

definition decr_grading_p :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
  where "decr_grading_p d n p = (\<Sum>v\<in>keys p. monomial (lookup p v) (decr_grading_term d n v))"

lemma decr_grading_term_splus:
  "hom_grading d \<Longrightarrow> decr_grading_term d n (t \<oplus> v) = decr_grading d n t \<oplus> decr_grading_term d n v"
  by (simp add: decr_grading_term_def term_simps decr_grading_plus splus_def)

lemma decr_grading_term_le: "hom_grading d \<Longrightarrow> d (pp_of_term (decr_grading_term d n v)) \<le> n"
  by (simp add: decr_grading_term_def term_simps decr_grading_le)

lemma decr_grading_term_idI: "hom_grading d \<Longrightarrow> d (pp_of_term v) \<le> n \<Longrightarrow> decr_grading_term d n v = v"
  by (simp add: decr_grading_term_def term_simps decr_grading_idI)

lemma punit_decr_grading_term: "punit.decr_grading_term = decr_grading"
  by (intro ext, simp add: punit.decr_grading_term_def)

lemma decr_grading_p_zero: "decr_grading_p d n 0 = 0"
  by (simp add: decr_grading_p_def)

lemma decr_grading_p_monomial: "decr_grading_p d n (monomial c v) = monomial c (decr_grading_term d n v)"
  by (simp add: decr_grading_p_def)

lemma decr_grading_p_plus:
  "decr_grading_p d n (p + q) = (decr_grading_p d n p) + (decr_grading_p d n q)"
proof -
  from finite_keys finite_keys have fin: "finite (keys p \<union> keys q)" by (rule finite_UnI)
  hence eq1: "(\<Sum>v\<in>keys p \<union> keys q. monomial (lookup p v) (decr_grading_term d n v)) =
              (\<Sum>v\<in>keys p. monomial (lookup p v) (decr_grading_term d n v))"
  proof (rule sum.mono_neutral_right)
    show "\<forall>v\<in>keys p \<union> keys q - keys p. monomial (lookup p v) (decr_grading_term d n v) = 0"
      by (simp add: in_keys_iff)
  qed simp
  from fin have eq2: "(\<Sum>v\<in>keys p \<union> keys q. monomial (lookup q v) (decr_grading_term d n v)) =
              (\<Sum>v\<in>keys q. monomial (lookup q v) (decr_grading_term d n v))"
  proof (rule sum.mono_neutral_right)
    show "\<forall>v\<in>keys p \<union> keys q - keys q. monomial (lookup q v) (decr_grading_term d n v) = 0"
      by (simp add: in_keys_iff)
  qed simp
  from fin Poly_Mapping.keys_add
  have "decr_grading_p d n (p + q) =
                (\<Sum>v\<in>keys p \<union> keys q. monomial (lookup (p + q) v) (decr_grading_term d n v))"
    unfolding decr_grading_p_def
  proof (rule sum.mono_neutral_left)
    show "\<forall>v\<in>keys p \<union> keys q - keys (p + q). monomial (lookup (p + q) v) (decr_grading_term d n v) = 0"
      by (simp add: in_keys_iff)
  qed
  also have "... = (\<Sum>v\<in>keys p \<union> keys q. monomial (lookup p v) (decr_grading_term d n v)) +
                   (\<Sum>v\<in>keys p \<union> keys q. monomial (lookup q v) (decr_grading_term d n v))"
    by (simp only: lookup_add single_add sum.distrib)
  also have "... = (decr_grading_p d n p) + (decr_grading_p d n q)"
    by (simp only: eq1 eq2 decr_grading_p_def)
  finally show ?thesis .
qed

corollary decr_grading_p_sum: "decr_grading_p d n (sum f A) = (\<Sum>a\<in>A. decr_grading_p d n (f a))"
  using decr_grading_p_zero decr_grading_p_plus by (rule fun_sum_commute)

lemma decr_grading_p_monom_mult:
  assumes "hom_grading d"
  shows "decr_grading_p d n (monom_mult c t p) = monom_mult c (decr_grading d n t) (decr_grading_p d n p)"
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by (simp add: decr_grading_p_zero)
next
  case (2 p a s)
  from assms show ?case
    by (simp add: monom_mult_dist_right decr_grading_p_plus 2(3) monom_mult_monomial
        decr_grading_p_monomial decr_grading_term_splus)
qed

lemma decr_grading_p_mult_scalar:
  assumes "hom_grading d"
  shows "decr_grading_p d n (p \<odot> q) = punit.decr_grading_p d n p \<odot> decr_grading_p d n q"
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by (simp add: punit.decr_grading_p_zero decr_grading_p_zero)
next
  case (2 p a s)
  from assms show ?case
    by (simp add: mult_scalar_distrib_right decr_grading_p_plus punit.decr_grading_p_plus 2(3)
        punit.decr_grading_p_monomial mult_scalar_monomial decr_grading_p_monom_mult punit_decr_grading_term)
qed

lemma decr_grading_p_keys_subset: "keys (decr_grading_p d n p) \<subseteq> decr_grading_term d n ` keys p"
proof
  fix v
  assume "v \<in> keys (decr_grading_p d n p)"
  also have "... \<subseteq> (\<Union>u\<in>keys p. keys (monomial (lookup p u) (decr_grading_term d n u)))"
    unfolding decr_grading_p_def by (fact keys_sum_subset)
  finally obtain u where "u \<in> keys p" and "v \<in> keys (monomial (lookup p u) (decr_grading_term d n u))" ..
  from this(2) have eq: "v = decr_grading_term d n u" by (simp split: if_split_asm)
  show "v \<in> decr_grading_term d n ` keys p" unfolding eq using \<open>u \<in> keys p\<close> by (rule imageI)
qed

lemma decr_grading_p_idI':
  assumes "hom_grading d" and "\<And>v. v \<in> keys p \<Longrightarrow> d (pp_of_term v) \<le> n"
  shows "decr_grading_p d n p = p"
proof -
  have "decr_grading_p d n p = (\<Sum>v \<in> keys p. monomial (lookup p v) v)" unfolding decr_grading_p_def
    using refl
  proof (rule sum.cong)
    fix v
    assume "v \<in> keys p"
    hence "d (pp_of_term v) \<le> n" by (rule assms(2))
    with assms(1) have "decr_grading_term d n v = v" by (rule decr_grading_term_idI)
    thus "monomial (lookup p v) (decr_grading_term d n v) = monomial (lookup p v) v" by simp
  qed
  also have "... = p" by (fact poly_mapping_sum_monomials)
  finally show ?thesis .
qed

end (* term_powerprod *)

context gd_term
begin

lemma decr_grading_p_idI:
  assumes "hom_grading d" and "p \<in> dgrad_p_set d m"
  shows "decr_grading_p d m p = p"
proof -
  from assms(2) have "\<And>v. v \<in> keys p \<Longrightarrow> d (pp_of_term v) \<le> m"
    by (auto simp: dgrad_p_set_def dgrad_set_def)
  with assms(1) show ?thesis by (rule decr_grading_p_idI')
qed

lemma decr_grading_p_dgrad_p_setI:
  assumes "hom_grading d"
  shows "decr_grading_p d m p \<in> dgrad_p_set d m"
proof (rule dgrad_p_setI)
  fix v
  assume "v \<in> keys (decr_grading_p d m p)"
  hence "v \<in> decr_grading_term d m ` keys p" using decr_grading_p_keys_subset ..
  then obtain u where "v = decr_grading_term d m u" ..
  with assms show "d (pp_of_term v) \<le> m" by (simp add: decr_grading_term_le)
qed

lemma (in gd_term) in_pmdlE_dgrad_p_set:
  assumes "hom_grading d" and "B \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "p \<in> pmdl B"
  obtains A q where "finite A" and "A \<subseteq> B" and "\<And>b. q b \<in> punit.dgrad_p_set d m"
    and "p = (\<Sum>b\<in>A. q b \<odot> b)"
proof -
  from assms(4) obtain A q0 where "finite A" and "A \<subseteq> B" and p: "p = (\<Sum>b\<in>A. q0 b \<odot> b)"
    by (rule pmdl.spanE)
  define q where "q = (\<lambda>b. punit.decr_grading_p d m (q0 b))"
  from \<open>finite A\<close> \<open>A \<subseteq> B\<close> show ?thesis
  proof
    fix b
    show "q b \<in> punit.dgrad_p_set d m" unfolding q_def using assms(1) by (rule punit.decr_grading_p_dgrad_p_setI)
  next
    from assms(1, 3) have "p = decr_grading_p d m p" by (simp only: decr_grading_p_idI)
    also from assms(1) have "... = (\<Sum>b\<in>A. q b \<odot> (decr_grading_p d m b))"
      by (simp add: p q_def decr_grading_p_sum decr_grading_p_mult_scalar)
    also from refl have "... = (\<Sum>b\<in>A. q b \<odot> b)"
    proof (rule sum.cong)
      fix b
      assume "b \<in> A"
      hence "b \<in> B" using \<open>A \<subseteq> B\<close> ..
      hence "b \<in> dgrad_p_set d m" using assms(2) ..
      with assms(1) have "decr_grading_p d m b = b" by (rule decr_grading_p_idI)
      thus "q b \<odot> decr_grading_p d m b = q b \<odot> b" by simp
    qed
    finally show "p = (\<Sum>b\<in>A. q b \<odot> b)" .
  qed
qed

end (* gd_term *)

end (* theory *)
