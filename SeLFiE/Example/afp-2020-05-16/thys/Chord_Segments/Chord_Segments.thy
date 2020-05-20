(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Intersecting Chord Theorem\<close>

theory Chord_Segments
imports Triangle.Triangle
begin

subsection \<open>Preliminaries\<close>

lemma betweenE_if_dist_leq:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "dist A X \<le> dist B X"
  obtains u where "1 / 2 \<le> u" "u \<le> 1" and "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
proof (cases "A = B")
  assume "A \<noteq> B"
  from \<open>between (A, B) X\<close> obtain u where u: "u \<ge> 0" "u \<le> 1" and X: "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    by (metis add.commute betweenE between_commute)
  from X have "X = B + u *\<^sub>R (A - B)" and "X = A + (u - 1) *\<^sub>R (A - B)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)+
  from \<open>X = B + u *\<^sub>R (A - B)\<close> have dist_B: "dist B X = norm (u *\<^sub>R (A - B))"
    by (auto simp add: dist_norm)
  from \<open>X = A + (u - 1) *\<^sub>R (A - B)\<close> have dist_A: "dist A X = norm ((u - 1) *\<^sub>R (A - B))"
    by (auto simp add: dist_norm)
  from \<open>A \<noteq> B\<close> have "norm (A - B) > 0" by auto
  from this \<open>dist A X \<le> dist B X\<close> have "u \<ge> 1 / 2"
    using dist_A dist_B by simp
  from this \<open>u \<le> 1\<close> X that show thesis by blast
next
  assume "A = B"
  define u :: real where "u = 1"
  from \<open>between (A, B) X\<close> \<open>A = B\<close> have "1 / 2 \<le> u" "u \<le> 1" "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    unfolding u_def by auto
  with that show thesis by blast
qed

lemma dist_geq_iff_midpoint_in_between:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  shows "dist A X \<le> dist B X \<longleftrightarrow> between (X, B) (midpoint A B)"
proof
  assume "dist A X \<le> dist B X"
  from \<open>between (A, B) X\<close> this obtain u
    where u: "1 / 2 \<le> u" "u \<le> 1" and X: "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    using betweenE_if_dist_leq by blast
  have M: "midpoint A B = (1 / 2) *\<^sub>R A + (1 / 2) *\<^sub>R B"
    unfolding midpoint_def by (simp add: scaleR_add_right)
  from \<open>1 / 2 \<le> u\<close> have 1: "midpoint A B = (1 / (2 * u)) *\<^sub>R X + (1 - (1 / (2 * u))) *\<^sub>R B"
  proof -
    have "(2 - u * 2) / (2 * u) = 1 / u - u / u"
      using u(1) by (simp add: diff_divide_distrib)
    also have "\<dots> = 1 / u - 1" using u(1) by auto
    finally have "(2 - u * 2) / (2 * u) = 1 / u - 1" .
    from \<open>1 / 2 \<le> u\<close> this show ?thesis
      using X M by (simp add: scaleR_add_right scaleR_add_left[symmetric])
  qed
  moreover from u have 2: "(1 / (2 * u)) \<ge> 0" "(1 / (2 * u)) \<le> 1" by auto
  ultimately show "between (X, B) (midpoint A B)"
    using betweenI [of concl: B X]  by (metis add.commute between_commute)
next
  assume "between (X, B) (midpoint A B)"
  then have "between (A, midpoint A B) X"
    using \<open>between (A, B) X\<close> between_midpoint(1) between_swap by blast
  then have "dist A X \<le> dist A (midpoint A B)"
    using between zero_le_dist by force
  also have "dist A (midpoint A B) \<le> dist B (midpoint A B)"
    by (simp add: dist_midpoint)
  also from \<open>between (X, B) (midpoint A B)\<close> have "dist B (midpoint A B) \<le> dist B X"
    using between zero_le_dist by (metis add.commute dist_commute le_add_same_cancel1)
  finally show "dist A X \<le> dist B X" .
qed

subsection \<open>Properties of Chord Segments\<close>

lemma chord_property:
  fixes S C :: "'a :: euclidean_space"
  assumes "dist C S = dist C T"
  assumes "between (S, T) X"
  shows "dist S X * dist X T = (dist C S) ^ 2 - (dist C X) ^ 2"
proof -
  define M where "M = midpoint S T"
  have "between (S, T) M"
    unfolding M_def by (simp add: between_midpoint(1))
  have "dist T M = dist S M"
    unfolding M_def by (simp add: dist_midpoint)

  have distances: "max (dist S X) (dist X T) = (dist S M) + (dist X M) \<and>
    min (dist S X) (dist X T) = (dist S M) - (dist X M)"
  proof cases
    assume "dist S X \<le> dist X T"
    then have "between (X, T) M"
      using \<open>between (S, T) X\<close> M_def
      by (simp add: dist_geq_iff_midpoint_in_between dist_commute)
    then have "between (S, M) X"
      using \<open>between (S, T) X\<close> \<open>between (S, T) M\<close> between_swap by blast
    from \<open>between (X, T) M\<close> have "dist X T = dist X M + dist M T"
      using between by auto
    moreover from \<open>between (S, M) X\<close> have "dist S X = dist S M - dist M X"
      using between dist_commute by force
    ultimately show ?thesis
      using \<open>dist S X \<le> dist X T\<close> \<open>dist T M = dist S M\<close>
      by (simp add: add.commute dist_commute max_def min_def)
  next
    assume "\<not> (dist S X \<le> dist X T)"
    then have "dist T X \<le> dist S X" by (simp add: dist_commute)
    then have "between (S, X) M"
      using \<open>between (S, T) X\<close> M_def
      by (simp add: dist_geq_iff_midpoint_in_between midpoint_sym between_commute)
    then have "between (T, M) X"
      using \<open>between (S, T) X\<close> \<open>between (S, T) M\<close> between_swap between_commute by metis
    from \<open>between (S, X) M\<close> have "dist S X = dist S M + dist M X"
      using between by auto
    moreover from \<open>between (T, M) X\<close> have "dist T X = dist T M - dist M X"
      using between dist_commute by force
    ultimately show ?thesis
      using \<open>\<not> dist S X \<le> dist X T\<close> \<open>dist T M = dist S M\<close>
      by (metis dist_commute max_def min_def)
  qed

  have "orthogonal (C - M) (S - M)"
    using \<open>dist C S = dist C T\<close> M_def
    by (auto simp add: isosceles_triangle_orthogonal_on_midpoint)
  have "orthogonal (C - M) (X - M)"
  proof -
    have "between (S, T) M"
      using M_def between_midpoint(1) by blast
    obtain c where "(X - M) = c *\<^sub>R (S - M)"
    proof (cases "S = M")
      assume "S \<noteq> M"
      then obtain c where "(X - M) = c *\<^sub>R (S - M)"
        using between_implies_scaled_diff [OF \<open>between (S, T) X\<close> \<open>between (S, T) M\<close>] by metis
      from this that show thesis by blast
    next
      assume "S = M"
      from this \<open>between (S, T) X\<close> have "X = M"
        by (simp add: midpoint_between M_def)
      from \<open>X = M\<close> \<open>S = M\<close> have "(X - M) = 0 *\<^sub>R (S - M)" by simp
      from this that show thesis by blast
    qed
    from this \<open>orthogonal (C - M) (S - M)\<close> show ?thesis
      by (auto intro: orthogonal_clauses(2))
  qed
  from \<open>orthogonal (C - M) (S - M)\<close> \<open>orthogonal (C - M) (X - M)\<close> have
    "(dist S M) ^ 2 + (dist M C) ^ 2 = (dist C S) ^ 2"
    "(dist X M) ^ 2 + (dist M C) ^ 2 = (dist C X) ^ 2"
    by (auto simp only: Pythagoras)
  then have geometric_observation:
    "(dist S M) ^ 2 = (dist C S) ^ 2 - (dist M C) ^ 2"
    "(dist X M) ^ 2 = (dist C X) ^ 2 - (dist M C) ^ 2"
    by auto

  have "dist S X * dist X T = max (dist S X) (dist X T) * min (dist S X) (dist X T)"
    by (auto split: split_max)
  also have "\<dots> = ((dist S M) + (dist X M)) * ((dist S M) - (dist X M))"
    using distances by simp
  also have "\<dots> = (dist S M) ^ 2 - (dist X M) ^ 2"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> = ((dist C S) ^ 2 - (dist M C) ^ 2) - ((dist C X) ^ 2 - (dist M C) ^ 2)"
    using geometric_observation by simp
  also have "\<dots> = (dist C S) ^ 2 - (dist C X) ^ 2" by simp
  finally show ?thesis .
qed

theorem product_of_chord_segments:
  fixes S\<^sub>1 T\<^sub>1 S\<^sub>2 T\<^sub>2 X C :: "'a :: euclidean_space"
  assumes "between (S\<^sub>1, T\<^sub>1) X" "between (S\<^sub>2, T\<^sub>2) X"
  assumes "dist C S\<^sub>1 = r" "dist C T\<^sub>1 = r"
  assumes "dist C S\<^sub>2 = r" "dist C T\<^sub>2 = r"
  shows "dist S\<^sub>1 X * dist X T\<^sub>1 = dist S\<^sub>2 X * dist X T\<^sub>2"
proof -
  from \<open>dist C S\<^sub>1 = r\<close> \<open>dist C T\<^sub>1 = r\<close> \<open>between (S\<^sub>1, T\<^sub>1) X\<close>
  have "dist S\<^sub>1 X * dist X T\<^sub>1 = r ^ 2 - (dist C X) ^ 2"
    by (subst chord_property) auto
  also from \<open>dist C S\<^sub>2 = r\<close> \<open>dist C T\<^sub>2 = r\<close> \<open>between (S\<^sub>2, T\<^sub>2) X\<close>
  have "\<dots> = dist S\<^sub>2 X * dist X T\<^sub>2"
    by (subst chord_property) auto
  finally show ?thesis .
qed

end
