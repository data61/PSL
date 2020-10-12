theory Pf_Add
imports Automatic_Refinement.Misc "HOL-Library.Monad_Syntax"
begin

lemma fun_ordI:
  assumes "\<And>x. ord (f x) (g x)"
  shows "fun_ord ord f g"
  using assms unfolding fun_ord_def by auto

lemma fun_ordD:
  assumes "fun_ord ord f g"
  shows "ord (f x) (g x)"
  using assms unfolding fun_ord_def by auto

lemma mono_fun_fun_cnv:
  assumes "\<And>d. monotone (fun_ord ordA) ordB (\<lambda>x. F x d)"
  shows "monotone (fun_ord ordA) (fun_ord ordB) F"
  apply rule
  apply (rule fun_ordI)
  using assms
  by (blast dest: monotoneD)

lemma fun_lub_Sup[simp]: "fun_lub Sup = Sup"
  unfolding fun_lub_def[abs_def]
  by (clarsimp intro!: ext; metis image_def)

lemma fun_ord_le[simp]: "fun_ord (\<le>) = (\<le>)"
  unfolding fun_ord_def[abs_def]
  by (auto intro!: ext simp: le_fun_def)

end
