(*  Title:      JinjaThreads/J/WWellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Weak well-formedness of Jinja programs\<close>

theory WWellForm
imports
  "../Common/WellForm"
  Expr
begin

definition
  wwf_J_mdecl :: "'addr J_prog \<Rightarrow> cname \<Rightarrow> 'addr J_mb mdecl \<Rightarrow> bool"
where
  "wwf_J_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns"

lemma wwf_J_mdecl[simp]:
  "wwf_J_mdecl P C (M,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns)"
(*<*)by(simp add:wwf_J_mdecl_def)(*>*)

abbreviation wwf_J_prog :: "'addr J_prog \<Rightarrow> bool"
where "wwf_J_prog == wf_prog wwf_J_mdecl"

end
