section \<open>Sum of Vector Sets\<close>

text \<open>We use Isabelle's Set-Algebra theory to be able to write V + W for sets of vectors V and W,
 and prove some obvious properties about them.\<close>
theory Sum_Vec_Set
  imports
    Missing_Matrix
    "HOL-Library.Set_Algebras"
begin


lemma add_0_right_vecset:
  assumes "(A :: 'a :: monoid_add vec set) \<subseteq> carrier_vec n"
  shows "A + {0\<^sub>v n} = A"
  unfolding set_plus_def using assms by force

lemma add_0_left_vecset:
  assumes "(A :: 'a :: monoid_add vec set) \<subseteq> carrier_vec n"
  shows "{0\<^sub>v n} + A = A"
  unfolding set_plus_def using assms by force

lemma assoc_add_vecset:
  assumes "(A :: 'a :: semigroup_add vec set) \<subseteq> carrier_vec n"
    and "B \<subseteq> carrier_vec n"
    and "C \<subseteq> carrier_vec n"
  shows "A + (B + C) = (A + B) + C"
proof -
  {
    fix x
    assume "x \<in> A + (B + C)"
    then obtain a b c where "x = a + (b + c)" and *: "a \<in> A" "b \<in> B" "c \<in> C"
      unfolding set_plus_def by auto
    with assms have "x = (a + b) + c" using assoc_add_vec[of a n b c] by force
    with * have "x \<in> (A + B) + C" by auto
  }
  moreover
  {
    fix x
    assume "x \<in> (A + B) + C"
    then obtain a b c where "x = (a + b) + c" and *: "a \<in> A" "b \<in> B" "c \<in> C"
      unfolding set_plus_def by auto
    with assms have "x = a + (b + c)" using assoc_add_vec[of a n b c] by force
    with * have "x \<in> A + (B + C)" by auto
  }
  ultimately show ?thesis by blast
qed

lemma sum_carrier_vec[intro]: "A \<subseteq> carrier_vec n \<Longrightarrow> B \<subseteq> carrier_vec n \<Longrightarrow> A + B \<subseteq> carrier_vec n"
  unfolding set_plus_def by force

lemma comm_add_vecset:
  assumes "(A :: 'a :: ab_semigroup_add vec set) \<subseteq> carrier_vec n"
    and "B \<subseteq> carrier_vec n"
  shows "A + B = B + A"
  unfolding set_plus_def using comm_add_vec assms by blast


end