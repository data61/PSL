theory Tangle_Relation
imports  Main
begin



lemma symmetry1: assumes "symp R" 
shows "\<forall>x y. (x, y) \<in> {(x, y). R x y}\<^sup>* \<longrightarrow> (y, x) \<in> {(x, y). R x y}\<^sup>*" 
proof-
have  "R x y \<longrightarrow>  R y x" by (metis assms sympD)
then have " (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, x) \<in> {(x, y). R x y}" by auto
then have 2:"\<forall> x y. (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, x) \<in> {(x, y). R x y}"
 by (metis (full_types) assms mem_Collect_eq split_conv sympE)
then have "sym {(x, y). R x y}" unfolding sym_def by auto
then have 3: "sym (rtrancl {(x, y). R x y})" using sym_rtrancl by auto
then show ?thesis by (metis symE)
qed

lemma symmetry2: assumes "\<forall>x y. (x, y) \<in> {(x, y). R x y}\<^sup>* \<longrightarrow> (y, x) \<in> {(x, y). R x y}\<^sup>* "
shows "symp R^**" 
unfolding symp_def Enum.rtranclp_rtrancl_eq assms by (metis assms)

lemma symmetry3: assumes "symp R" shows "symp R^**" using assms symmetry1 symmetry2 by metis

lemma symm_trans: assumes "symp R" shows "symp R^++" by (metis assms rtranclpD symmetry3 symp_def tranclp_into_rtranclp)

end
