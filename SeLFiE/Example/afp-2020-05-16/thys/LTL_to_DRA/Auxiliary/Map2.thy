(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary Map Facts\<close>

theory Map2
  imports Main
begin 

lemma map_of_tabulate:  
  "map_of (map (\<lambda>x. (x, f x)) xs) x \<noteq> None \<longleftrightarrow> x \<in> set xs"
  by (induct xs) auto

lemma map_of_tabulate_simp:
  "map_of (map (\<lambda>x. (x, f x)) xs) x = (if x \<in> set xs then Some (f x) else None)"
  by (metis (mono_tags, lifting) comp_eq_dest_lhs map_of_map_restrict restrict_map_def)

lemma dom_map_update:
  "dom (m (k \<mapsto> v)) = dom m \<union> {k}"
  by simp

lemma map_equal:
  "dom m = dom m' \<Longrightarrow> (\<And>x. x \<in> dom m \<Longrightarrow> m x = m' x) \<Longrightarrow> m = m'"
  by fastforce

lemma map_reduce:
  assumes "dom m = {a} \<union> B"
  shows "\<exists>m'. dom m' = B \<and> (\<forall>x \<in> B. m x = m' x)"
proof (cases "a \<in> B")
  case True
    thus ?thesis
      using assms by (metis insert_absorb insert_is_Un)
next
  case False
    with assms have "dom (m (a := None)) = B \<and> (\<forall>x\<in>B. m x = (m (a := None)) x)"
      by simp
    thus ?thesis
      by blast
qed

end
