(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Additions to Isabelle's Main Theories\<close>

theory Additions_to_Main
imports "HOL-Library.Multiset"
begin

subsection \<open>Addition to Finite-Set Theory\<close>

lemma bound_domain_and_range_impl_finitely_many_functions:
  "finite {f::nat\<Rightarrow>nat. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>m. f i = 0)}"
proof (induct m)
  case 0
  have eq: "{f. (\<forall>i. f i \<le> n) \<and> (\<forall>i. f i = 0)} = {(\<lambda>_. 0)}" by auto
  from this show ?case by auto (subst eq; auto)
next
  case (Suc m)
  let ?S = "(\<lambda>(y, f). f(m := y)) ` ({0..n} \<times> {f. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>m. f i = 0)})"
  {
    fix g
    assume "\<forall>i. g i \<le> n" "\<forall>i\<ge>Suc m. g i = 0"
    from this have "g \<in> ?S"
      by (auto intro: image_eqI[where x="(g m, g(m:=0))"])
  }
  from this have "{f. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>Suc m. f i = 0)} = ?S" by auto
  from this Suc show ?case by simp
qed

subsection \<open>Addition to Set-Interval Theory\<close>

lemma sum_atMost_remove_nat:
  assumes "k \<le> (n :: nat)"
  shows "(\<Sum>i\<le>n. f i) = f k + (\<Sum>i\<in>{..n}-{k}. f i)"
using assms by (auto simp add: sum.remove[where x=k])

subsection \<open>Additions to Multiset Theory\<close>

lemma set_mset_Abs_multiset:
  assumes "f \<in> multiset"
  shows "set_mset (Abs_multiset f) = {x. f x > 0}"
using assms unfolding set_mset_def by simp

lemma sum_mset_sum_count:
  "sum_mset M = (\<Sum>i\<in>set_mset M. count M i * i)"
proof (induct M)
  show "sum_mset {#} = (\<Sum>i\<in>set_mset {#}. count {#} i * i)" by simp
next
  fix M x
  assume hyp: "sum_mset M = (\<Sum>i\<in>set_mset M. count M i * i)"
  show "sum_mset (add_mset x M) = (\<Sum>i\<in>set_mset (add_mset x M). count (add_mset x M) i * i)"
  proof (cases "x \<in># M")
    assume a: "\<not> x \<in># M"
    from this have "count M x = 0" by (meson count_inI)
    from \<open>\<not> x \<in># M\<close> this hyp show ?thesis
      by (auto intro!: sum.cong)
  next
    assume "x \<in># M"
    have "sum_mset (add_mset x M) = (\<Sum>i\<in>set_mset M. count M i * i) + x"
      using hyp by simp
    also have "\<dots> = (\<Sum>i\<in>set_mset M - {x}. count M i * i) + count M x * x + x"
      using \<open>x \<in># M\<close> by (simp add: sum.remove[of _ x])
    also have "\<dots> = count (add_mset x M) x * x + (\<Sum>i\<in>set_mset (add_mset x M) - {x}. count (add_mset x M) i * i)"
      by simp
    also have "\<dots> = (\<Sum>i\<in>set_mset (add_mset x M). count (add_mset x M) i * i)"
      using \<open>x \<in># M\<close> by (simp add: sum.remove[of _ x])
    finally show ?thesis .
  qed
qed

lemma sum_mset_eq_sum_on_supersets:
  assumes "finite A" "set_mset M \<subseteq> A"
  shows "(\<Sum>i\<in>set_mset M. count M i * i) = (\<Sum>i\<in>A. count M i * i)"
proof -
  note \<open>finite A\<close> \<open>set_mset M \<subseteq> A\<close>
  moreover have "\<forall>i\<in>A - set_mset M. count M i * i = 0"
    using count_inI by fastforce
  ultimately show ?thesis
    by (auto intro: sum.mono_neutral_cong_left)
qed

end
