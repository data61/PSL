theory General_Rewriting
imports Terms_Extras
begin

locale rewriting =
  fixes R :: "'a::term \<Rightarrow> 'a \<Rightarrow> bool"
  assumes R_fun: "R t t' \<Longrightarrow> R (app t u) (app t' u)"
  assumes R_arg: "R u u' \<Longrightarrow> R (app t u) (app t u')"
begin

lemma rt_fun:
  "R\<^sup>*\<^sup>* t t' \<Longrightarrow> R\<^sup>*\<^sup>* (app t u) (app t' u)"
by (induct rule: rtranclp.induct) (auto intro: rtranclp.rtrancl_into_rtrancl R_fun)

lemma rt_arg:
  "R\<^sup>*\<^sup>* u u' \<Longrightarrow> R\<^sup>*\<^sup>* (app t u) (app t u')"
by (induct rule: rtranclp.induct) (auto intro: rtranclp.rtrancl_into_rtrancl R_arg)

lemma rt_comb:
  "R\<^sup>*\<^sup>* t\<^sub>1 u\<^sub>1 \<Longrightarrow> R\<^sup>*\<^sup>* t\<^sub>2 u\<^sub>2 \<Longrightarrow> R\<^sup>*\<^sup>* (app t\<^sub>1 t\<^sub>2) (app u\<^sub>1 u\<^sub>2)"
by (metis rt_fun rt_arg rtranclp_trans)

lemma rt_list_comb:
  assumes "list_all2 R\<^sup>*\<^sup>* ts us" "R\<^sup>*\<^sup>* t u"
  shows "R\<^sup>*\<^sup>* (list_comb t ts) (list_comb u us)"
using assms
by (induction ts us arbitrary: t u rule: list.rel_induct) (auto intro: rt_comb)

end

end