theory TopoS_Util
imports Main
begin

lemma finite_ne_subset_induct [case_names singleton insert, consumes 2]:
  assumes "finite F" and "F \<noteq> {}" and "F \<subseteq> A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> P {x}"
    and "\<And>x F. finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
using assms
proof induct
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by cases auto
qed


(*lemma from afp collections Misc*)
lemma set_union_code:
  "set xs \<union> set ys = set (xs @ ys)"
  by auto

end
