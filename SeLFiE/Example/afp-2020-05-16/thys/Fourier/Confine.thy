section\<open>Confining a series to a set\<close>

theory Confine
  imports Complex_Main
begin

definition confine :: "('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "confine f A = (\<lambda>x. if x \<in> A then f x else 0)"

lemma confine_UNIV [simp]: "confine f UNIV = f"
  by (simp add: confine_def)

lemma sum_confine_eq_Int:
  assumes "finite I"
  shows "sum (confine f A) I = (\<Sum>i \<in> I \<inter> A. f i)"
proof -
  have "sum f(I \<inter> A) = (\<Sum>a\<in>I. if a \<in> A then f a else 0)"
    using assms sum.inter_restrict by blast
  then show ?thesis
    by (auto simp: confine_def)
qed

lemma sums_confine_add:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "confine f N sums a" "confine g N sums b"
  shows "confine (\<lambda>i. f i + g i) N sums (a+b)"
proof -
  have "\<And>n. (if n \<in> N then f n + g n else 0) = (if n \<in> N then f n else 0) + (if n \<in> N then g n else 0)"
    by simp
  then show ?thesis
    using sums_add [of "confine f N" a "confine g N" b] assms
    by (simp add: confine_def)
qed

lemma sums_confine_minus:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "confine f N sums a \<Longrightarrow> confine (uminus \<circ> f) N sums (-a)"
     using sums_minus [of "confine f N" a]
     by (simp add: confine_def if_distrib [of uminus] cong: if_cong)

lemma sums_confine_mult:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_algebra"
  shows "confine f N sums a \<Longrightarrow> confine (\<lambda>n. c * f n) N sums (c * a)"
     using sums_mult [of "confine f N" a c]
     by (simp add: confine_def if_distrib [of "(*)c"] cong: if_cong)

lemma sums_confine_divide:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_field"
  shows "confine f N sums a \<Longrightarrow> confine (\<lambda>n. f n / c) N sums (a/c)"
     using sums_divide [of "confine f N" a c]
     by (simp add: confine_def if_distrib [of "\<lambda>x. x/c"] cong: if_cong)

lemma sums_confine_divide_iff:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_field"
  assumes "c \<noteq> 0"
  shows "confine (\<lambda>n. f n / c) N sums (a/c) \<longleftrightarrow> confine f N sums a"
proof
  show "confine f N sums a"
    if "confine (\<lambda>n. f n / c) N sums (a / c)"
    using sums_confine_mult [OF that, of c] assms by simp
qed (auto simp: sums_confine_divide)

lemma sums_confine:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "confine f N sums l \<longleftrightarrow> ((\<lambda>n. \<Sum>i \<in> {..<n} \<inter> N. f i) \<longlonglongrightarrow> l)"
  by (simp add: sums_def atLeast0LessThan confine_def sum.inter_restrict)

lemma sums_confine_le:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "confine f N sums l \<longleftrightarrow> ((\<lambda>n. \<Sum>i \<in> {..n} \<inter> N. f i) \<longlonglongrightarrow> l)"
  by (simp add: sums_def_le atLeast0AtMost confine_def sum.inter_restrict)

end
