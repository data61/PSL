(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Stewart's Theorem and Apollonius' Theorem\<close>

theory Stewart_Apollonius
imports
  Triangle.Triangle
begin

subsection \<open>Stewart's Theorem\<close>

theorem Stewart:
  fixes A B C D :: "'a::euclidean_space"
  assumes "between (B, C) D"
  assumes "a = dist B C"
  assumes "b = dist A C"
  assumes "c = dist B A"
  assumes "d = dist A D"
  assumes "m = dist B D"
  assumes "n = dist C D"
  shows "b\<^sup>2 * m + c\<^sup>2 * n = a * (d\<^sup>2 + m * n)"
proof (cases)
  assume "B \<noteq> D \<and> C \<noteq> D"
  let ?\<theta> = "angle B D A"
  let ?\<theta>' = "angle A D C"
  from \<open>B \<noteq> D \<and> C \<noteq> D\<close> \<open>between _ _\<close> have cos: "cos ?\<theta>' = - cos ?\<theta>"
    by (auto simp add: angle_inverse[of B C D] angle_commute[of A D C])
  from \<open>between _ _\<close> have "m + n = a"
    unfolding \<open>a = _\<close> \<open>m = _\<close> \<open>n = _\<close>
    by (metis (no_types) between dist_commute)
  have "c\<^sup>2 = m\<^sup>2 + d\<^sup>2 - 2 * d * m * cos ?\<theta>"
    unfolding \<open>c = _\<close> \<open>m = _\<close> \<open>d = _\<close>
    by (simp add: cosine_law_triangle[of B A D] dist_commute[of D A] dist_commute[of D B])
  moreover have "b\<^sup>2 = n\<^sup>2 + d\<^sup>2 + 2 * d * n * cos ?\<theta>"
    unfolding \<open>b = _\<close> \<open>n = _\<close> \<open>d = _\<close>
    by (simp add: cosine_law_triangle[of A C D] cos dist_commute[of D A] dist_commute[of D C])
  ultimately have "b\<^sup>2 * m + c\<^sup>2 * n = n * m\<^sup>2 + n\<^sup>2 * m + (m + n) * d\<^sup>2" by algebra
  also have "\<dots> = (m + n) * (m * n + d\<^sup>2)" by algebra
  also from \<open>m + n = a\<close> have "\<dots> = a * (d\<^sup>2 + m * n)" by simp
  finally show ?thesis .
next
  assume "\<not> (B \<noteq> D \<and> C \<noteq> D)"
  from this assms show ?thesis by (auto simp add: dist_commute)
qed

text \<open>
Here is an equivalent formulation that is probably more suitable for further use
in other geometry theories in Isabelle.
\<close>

theorem Stewart':
  fixes A B C D :: "'a::euclidean_space"
  assumes "between (B, C) D"
  shows "(dist A C)\<^sup>2 * dist B D + (dist B A)\<^sup>2 * dist C D = dist B C * ((dist A D)\<^sup>2 + dist B D * dist C D)"
using assms by (auto intro: Stewart)

subsection \<open>Apollonius' Theorem\<close>

text \<open>
Apollonius' theorem is a simple specialisation of Stewart's theorem,
but historically predated Stewart's theorem by many centuries.
\<close>

lemma Apollonius:
  fixes A B C :: "'a::euclidean_space"
  assumes "B \<noteq> C"
  assumes "b = dist A C"
  assumes "c = dist B A"
  assumes "d = dist A (midpoint B C)"
  assumes "m = dist B (midpoint B C)"
  shows "b\<^sup>2 + c\<^sup>2 = 2 * (m\<^sup>2 + d\<^sup>2)"
proof -
  from \<open>B \<noteq> C\<close> have "m \<noteq> 0"
    unfolding \<open>m = _\<close> using midpoint_eq_endpoint(1) by fastforce
  have "between (B, C) (midpoint B C)"
    by (simp add: between_midpoint)
  moreover have "dist C (midpoint B C) = dist B (midpoint B C)"
    by (simp add: dist_midpoint)
  moreover have "dist B C = 2 * dist B (midpoint B C)"
    by (simp add: dist_midpoint)
  moreover note assms(2-5)
  ultimately have "b\<^sup>2 * m + c\<^sup>2 * m = (2 * m) * (m\<^sup>2 + d\<^sup>2)"
    by (auto dest!: Stewart[where a="2 * m"] simp add: power2_eq_square)
  from this have "m * (b\<^sup>2 + c\<^sup>2) = m * (2 * (m\<^sup>2 + d\<^sup>2))"
    by (simp add: distrib_left semiring_normalization_rules(7))
  from this \<open>m \<noteq> 0\<close> show ?thesis by auto
qed

text \<open>
Here is the equivalent formulation that is probably more suitable for further use
in other geometry theories in Isabelle.
\<close>

lemma Apollonius':
  fixes A B C :: "'a::euclidean_space"
  assumes "B \<noteq> C"
  shows "(dist A C)\<^sup>2 + (dist B A)\<^sup>2 = 2 * ((dist B (midpoint B C))\<^sup>2 + (dist A (midpoint B C))\<^sup>2)"
using assms by (rule Apollonius) auto

end
