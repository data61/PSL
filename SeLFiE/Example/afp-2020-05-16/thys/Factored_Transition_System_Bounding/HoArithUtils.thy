theory HoArithUtils
  imports Main
begin

lemma general_theorem: 
  fixes P f and l :: nat
  assumes "(\<forall>p. P p \<and> f p > l \<longrightarrow> (\<exists>p'. P p' \<and> f p' < f p))"
  shows "(\<forall>p. P p \<longrightarrow> (\<exists>p'. P p' \<and> f p' \<le> l))"
proof-
  have "\<forall>p. (n = f p) \<and> P p \<longrightarrow> (\<exists>p'. P p' \<and> f p' \<le> l)" for n
    apply(rule Nat.nat_less_induct[where ?P = "%n. \<forall>p. (n = f p) \<and> P p \<longrightarrow> (\<exists>p'. P p' \<and> f p' \<le> l)"])
    by (metis assms not_less)
  then show ?thesis by auto
qed

end