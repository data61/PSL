section\<open>Shifting the origin for integration of periodic functions\<close>

theory Periodic
  imports "HOL-Analysis.Analysis" 
begin

lemma has_bochner_integral_null [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "N \<in> null_sets lebesgue"
  shows "has_bochner_integral (lebesgue_on N) f 0"
  unfolding has_bochner_integral_iff
proof
  show "integrable (lebesgue_on N) f"
  proof (subst integrable_restrict_space)
    show "N \<inter> space lebesgue \<in> sets lebesgue"
      using assms by force
    show "integrable lebesgue (\<lambda>x. indicat_real N x *\<^sub>R f x)"
    proof (rule integrable_cong_AE_imp)
      show "integrable lebesgue (\<lambda>x. 0)"
        by simp
      show *: "AE x in lebesgue. 0 = indicat_real N x *\<^sub>R f x"
        using assms
        by (simp add: indicator_def completion.null_sets_iff_AE eventually_mono)
      show "(\<lambda>x. indicat_real N x *\<^sub>R f x) \<in> borel_measurable lebesgue"
        by (auto intro: borel_measurable_AE [OF _ *])
    qed
  qed
  show "integral\<^sup>L (lebesgue_on N) f = 0"
  proof (rule integral_eq_zero_AE)
    show "AE x in lebesgue_on N. f x = 0"
      by (rule AE_I' [where N=N]) (auto simp: assms null_setsD2 null_sets_restrict_space)
  qed
qed

lemma has_bochner_integral_null_eq[simp]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "N \<in> null_sets lebesgue"
  shows "has_bochner_integral (lebesgue_on N) f i \<longleftrightarrow> i = 0"
  using assms has_bochner_integral_eq by blast

lemma periodic_integer_multiple:
   "(\<forall>x. f(x + a) = f x) \<longleftrightarrow> (\<forall>x. \<forall>n \<in> \<int>. f(x + n * a) = f x)" (is "?lhs = ?rhs")
proof
  assume L [rule_format]: ?lhs
  have nat: "f(x + of_nat n * a) = f x" for x n
  proof (induction n)
    case (Suc n)
    with L [of "x + of_nat n * a"] show ?case
      by (simp add: algebra_simps)
  qed auto
  have "f(x + of_int z * a) = f x" for x z
  proof (cases "z \<ge> 0")
    case True
    then show ?thesis
      by (metis nat of_nat_nat)
  next
    case False
    then show ?thesis
      using nat [of "x + of_int z * a" "nat (-z)"] by auto
  qed
  then show ?rhs
    by (auto simp: Ints_def)
qed (use Ints_1 in fastforce)

lemma has_integral_offset:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "has_bochner_integral (lebesgue_on {a..b}) f i"
  shows "has_bochner_integral (lebesgue_on {a-c..b-c}) (\<lambda>x. f(x + c)) i"
proof -
  have eq: "indicat_real {a..b} (x + c) = indicat_real {a-c..b-c} x" for x
    by (auto simp: indicator_def)
  have "has_bochner_integral lebesgue (\<lambda>x. indicator {a..b} x *\<^sub>R f x) i"
    using assms  by (auto simp: has_bochner_integral_restrict_space)
  then have "has_bochner_integral lebesgue (\<lambda>x. indicat_real {a-c..b-c} x *\<^sub>R f(x + c)) i"
    using has_bochner_integral_lebesgue_real_affine_iff [of 1 "(\<lambda>x. indicator {a..b} x *\<^sub>R f x)" i c]
    by (simp add: add_ac eq)
  then show ?thesis
    using assms by (auto simp: has_bochner_integral_restrict_space)
qed


lemma has_integral_periodic_offset_lemma:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes periodic: "\<And>x. f(x + (b-a)) = f x" and f: "has_bochner_integral (lebesgue_on {a..a+c}) f i"
  shows "has_bochner_integral (lebesgue_on {b..b+c}) f i"
proof -
  have "f(x + a-b) = f x" for x
    using periodic [of "x + (a-b)"] by (simp add: algebra_simps)
  then show ?thesis
    using has_integral_offset [OF f, of "a-b"]
    by (auto simp: algebra_simps)
qed


lemma has_integral_periodic_offset_pos:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "has_bochner_integral (lebesgue_on {a..b}) f i" and periodic: "\<And>x. f(x + (b-a)) = f x"
      and c: "c \<ge> 0" "a + c \<le> b"
  shows "has_bochner_integral (lebesgue_on {a..b}) (\<lambda>x. f(x + c)) i"
proof -
  have "{a..a + c} \<subseteq> {a..b}"
    by (simp add: assms(4))
  then have 1: "has_bochner_integral (lebesgue_on {a..a+c}) f(integral\<^sup>L (lebesgue_on {a..a+c}) f)"
    by (meson integrable_subinterval f has_bochner_integral_iff)
  then have 3: "has_bochner_integral (lebesgue_on {b..b+c}) f(integral\<^sup>L (lebesgue_on {a..a+c}) f)"
    using has_integral_periodic_offset_lemma periodic by blast
  have "{a + c..b} \<subseteq> {a..b}"
    by (simp add: c)
  then have 2: "has_bochner_integral (lebesgue_on {a+c..b}) f(integral\<^sup>L (lebesgue_on {a+c..b}) f)"
    by (meson integrable_subinterval f has_bochner_integral_integrable integrable.intros)
  have "integral\<^sup>L (lebesgue_on {a + c..b}) f + integral\<^sup>L (lebesgue_on {a..a + c}) f = i"
    by (metis integral_combine add.commute c f has_bochner_integral_iff le_add_same_cancel1)
  then have "has_bochner_integral (lebesgue_on {a+c..b+c}) f i"
    using has_bochner_integral_combine [OF _ _ 2 3] 1 2 by (simp add: c)
  then show ?thesis
    by (metis add_diff_cancel_right' has_integral_offset)
qed


lemma has_integral_periodic_offset_weak:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "has_bochner_integral (lebesgue_on {a..b}) f i" and periodic: "\<And>x. f(x + (b-a)) = f x" and c: "\<bar>c\<bar> \<le> b-a"
  shows "has_bochner_integral (lebesgue_on {a..b}) (\<lambda>x. f(x + c)) i"
proof (cases "c \<ge> 0")
  case True
  then show ?thesis
    using c f has_integral_periodic_offset_pos periodic by auto
next
  case False
  have per': "f(- (x + (- a - - b))) = f(- x)" for x
    using periodic [of "(a-b)-x"] by simp
  have f': "has_bochner_integral (lebesgue_on {- b..- a}) (\<lambda>x. f(- x)) i"
    using f by blast
  show ?thesis
    using has_integral_periodic_offset_pos [of "-b" "-a" "\<lambda>x. f(-x)" i "-c", OF f' per'] c  False
    by (simp flip: has_bochner_integral_reflect_real [of b a])
qed

lemma has_integral_periodic_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "has_bochner_integral (lebesgue_on {a..b}) f i" and periodic: "\<And>x. f(x + (b-a)) = f x"
  shows "has_bochner_integral (lebesgue_on {a..b}) (\<lambda>x. f(x + c)) i"
proof -
  consider "b \<le> a" | "a < b" by linarith
  then show ?thesis
  proof cases
    case 1
    then have "{a..b} \<in> null_sets lebesgue"
      using less_eq_real_def by auto
    with f show ?thesis
      by auto
  next
    case 2
    define fba where "fba \<equiv> \<lambda>x. f(x + (b-a) * frac(c / (b-a)))"
    have eq: "fba x = f(x + c)"
      if "x \<in> {a..b}" for x
    proof -
      have "f(x + n * (b-a)) = f x" if "n \<in> \<int>" for n x
        using periodic periodic_integer_multiple that by blast
      then have "f((x + c) + - floor (c / (b - a)) * (b - a)) = f(x + c)"
        using Ints_of_int by blast
      moreover have "((x + c) + -floor (c / (b - a)) * (b - a)) = (x + (b - a) * frac (c / (b - a)))"
        using 2 by (simp add: field_simps frac_def)
      ultimately show ?thesis
        unfolding fba_def by metis
    qed
    have *: "has_bochner_integral (lebesgue_on {a..b}) fba i"
      unfolding fba_def
    proof (rule has_integral_periodic_offset_weak [OF f])
      show "f(x + (b - a)) = f x" for x
        by fact
      have "\<bar>frac (c / (b - a))\<bar> \<le> 1"
        using frac_unique_iff less_eq_real_def by auto
      then show "\<bar>(b - a) * frac (c / (b - a))\<bar> \<le> b - a"
        using "2" by auto
    qed
    then show ?thesis
    proof (rule has_bochner_integralI_AE [OF _ _ AE_I2])
      have "fba \<in> borel_measurable (lebesgue_on {a..b})"
        using "*" borel_measurable_has_bochner_integral by blast
      then show "(\<lambda>x. f(x + c)) \<in> borel_measurable (lebesgue_on {a..b})"
        by (subst measurable_lebesgue_cong [OF eq, symmetric])
    qed (auto simp: eq)
  qed
qed

lemma integrable_periodic_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "integrable (lebesgue_on {a..b}) f" and periodic: "\<And>x. f(x + (b-a)) = f x"
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. f(x + c))"
  using f has_integral_periodic_offset periodic
  by (simp add: has_bochner_integral_iff)

lemma absolutely_integrable_periodic_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {a..b}" and periodic: "\<And>x. f(x + (b-a)) = f x"
  shows "(\<lambda>x. f(x + c)) absolutely_integrable_on {a..b}" "(\<lambda>x. f(c + x)) absolutely_integrable_on {a..b}"
  using assms integrable_periodic_offset [of a b "f"]
  by (auto simp: integrable_restrict_space set_integrable_def add.commute [of c])

lemma integral_periodic_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes periodic: "\<And>x. f(x + (b-a)) = f x"
  shows "integral\<^sup>L (lebesgue_on {a..b}) (\<lambda>x. f(x + c)) = integral\<^sup>L (lebesgue_on {a..b}) f"
proof (cases "integrable (lebesgue_on {a..b}) f")
  case True
  then show ?thesis
    using has_integral_periodic_offset periodic
    by (simp add: has_bochner_integral_iff)
next
  case False
  then have "\<not> integrable (lebesgue_on {a..b}) (\<lambda>x. f(x + c))"
    using periodic[of "_+c"]
    by (auto simp: algebra_simps intro: dest: integrable_periodic_offset [where c = "-c"])
  then have "integral\<^sup>L (lebesgue_on {a..b}) f = 0" "integral\<^sup>L (lebesgue_on {a..b}) (\<lambda>x. f(x + c)) = 0"
    using False not_integrable_integral_eq by blast+
  then show ?thesis
    by simp
qed

end
