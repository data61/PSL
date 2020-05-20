theory Pick imports Main
begin

definition "pick X \<equiv> SOME x. x \<in> X"

lemma pick[simp]: "x \<in> X \<Longrightarrow> pick X \<in> X"
unfolding pick_def by (metis someI_ex)

lemma pick_NE[simp]: "X \<noteq> {} \<Longrightarrow> pick X \<in> X" by auto


end