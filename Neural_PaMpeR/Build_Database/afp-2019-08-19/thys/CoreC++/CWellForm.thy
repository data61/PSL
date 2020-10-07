(*  Title:       CoreC++

    Author:      Tobias Nipkow, Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Well-formedness Constraints\<close>

theory CWellForm imports WellForm WWellForm WellTypeRT DefAss begin


definition wf_C_mdecl :: "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> bool" where
  "wf_C_mdecl P C \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>"

lemma wf_C_mdecl[simp]:
  "wf_C_mdecl P C (M,Ts,T,pns,body) \<equiv>
  (length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>)"
by(simp add:wf_C_mdecl_def)



abbreviation
  wf_C_prog :: "prog \<Rightarrow> bool" where
  "wf_C_prog ==  wf_prog wf_C_mdecl"

lemma wf_C_prog_wf_C_mdecl:
  "\<lbrakk> wf_C_prog P; (C,Bs,fs,ms) \<in> set P; m \<in> set ms \<rbrakk>
  \<Longrightarrow> wf_C_mdecl P C m"

apply (simp add: wf_prog_def)
apply (simp add: wf_cdecl_def)
apply (erule conjE)+
apply (drule bspec, assumption)
apply simp
apply (erule conjE)+
apply (drule bspec, assumption)
apply (simp add: wf_mdecl_def split_beta)
done



lemma wf_mdecl_wwf_mdecl: "wf_C_mdecl P C Md \<Longrightarrow> wwf_mdecl P C Md"
by(fastforce simp:wwf_mdecl_def dest!:WT_fv)


lemma wf_prog_wwf_prog: "wf_C_prog P \<Longrightarrow> wwf_prog P"

apply(simp add:wf_prog_def wf_cdecl_def wf_mdecl_def)
apply(fast intro:wf_mdecl_wwf_mdecl)
done



end
