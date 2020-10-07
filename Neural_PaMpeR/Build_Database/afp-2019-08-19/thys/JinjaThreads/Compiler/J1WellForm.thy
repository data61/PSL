(*  Title:      JinjaThreads/Compiler/J1WellForm.thy
    Author:     Andreas Lochbihler, Tobias Nipkow
*)

section \<open>Well-Formedness of Intermediate Language\<close>

theory J1WellForm imports
  "../J/DefAss"
  J1WellType
begin

subsection\<open>Well-formedness\<close>

definition wf_J1_mdecl :: "'addr J1_prog \<Rightarrow> cname \<Rightarrow> 'addr expr1 mdecl \<Rightarrow> bool"
where
  "wf_J1_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,body).
    (\<exists>T'. P,Class C#Ts \<turnstile>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
    \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1) \<and> syncvars body"

lemma wf_J1_mdecl[simp]:
  "wf_J1_mdecl P C (M,Ts,T,body) \<equiv>
    ((\<exists>T'. P,Class C#Ts \<turnstile>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1)) \<and> syncvars body"
by (simp add:wf_J1_mdecl_def)

abbreviation wf_J1_prog :: "'addr J1_prog \<Rightarrow> bool"
where "wf_J1_prog == wf_prog wf_J1_mdecl"

end
