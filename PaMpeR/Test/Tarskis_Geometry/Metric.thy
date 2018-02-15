(*  Title:       Metric and semimetric spaces
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "Metric and semimetric spaces"

theory Metric
imports "HOL-Analysis.Euclidean_Space"
begin

locale semimetric =
  fixes dist :: "'p \<Rightarrow> 'p \<Rightarrow> real"
  assumes nonneg [simp]: "dist x y \<ge> 0"
  and eq_0 [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
  and symm: "dist x y = dist y x"
begin
  lemma refl [simp]: "dist x x = 0"
    by simp
end

locale metric =
  fixes dist :: "'p \<Rightarrow> 'p \<Rightarrow> real"
  assumes [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
  and triangle: "dist x z \<le> dist y x + dist y z"

sublocale metric < semimetric
proof
  { fix w
    have "dist w w = 0" by simp }
  note [simp] = this
  fix x y
  show "0 \<le> dist x y"
  proof -
    from triangle [of y y x] show "0 \<le> dist x y" by simp
  qed
  show "dist x y = 0 \<longleftrightarrow> x = y" by simp
  show "dist x y = dist y x"
  proof -
    { fix w z
      have "dist w z \<le> dist z w"
      proof -
        from triangle [of w z z] show "dist w z \<le> dist z w" by simp
      qed }
    hence "dist x y \<le> dist y x" and "dist y x \<le> dist x y" by simp+
    thus "dist x y = dist y x" by simp
  qed
qed

definition norm_dist :: "('a::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> real" where
[simp]: "norm_dist x y \<equiv> norm (x - y)"

interpretation norm_metric: metric norm_dist
proof
  fix x y
  show "norm_dist x y = 0 \<longleftrightarrow> x = y" by simp
  fix z
  from norm_triangle_ineq [of "x - y" "y - z"] have
    "norm (x - z) \<le> norm (x - y) + norm (y - z)" by simp
  with norm_minus_commute [of x y] show
    "norm_dist x z \<le> norm_dist y x + norm_dist y z" by simp
qed

end
