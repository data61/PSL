(*  Title:       CoreC++

    Author:      Tobias Nipkow
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Weak well-formedness of CoreC++ programs\<close>

theory WWellForm imports WellForm Expr begin


definition wwf_mdecl :: "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> bool" where
  "wwf_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns"

lemma wwf_mdecl[simp]:
  "wwf_mdecl P C (M,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns)"
by(simp add:wwf_mdecl_def)


abbreviation
  wwf_prog :: "prog \<Rightarrow> bool" where
  "wwf_prog == wf_prog wwf_mdecl"

end
