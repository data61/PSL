(*  Title:      JinjaThreads/J/JWellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Well-formedness Constraints\<close>

theory JWellForm
imports
  WWellForm
  WellType
  DefAss
begin

definition wf_J_mdecl :: "'addr J_prog \<Rightarrow> cname \<Rightarrow> 'addr J_mb mdecl \<Rightarrow> bool"
where
  "wf_J_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>"

lemma wf_J_mdecl[simp]:
  "wf_J_mdecl P C (M,Ts,T,pns,body) \<equiv>
  (length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  (\<exists>T'. P,[this\<mapsto>Class C,pns[\<mapsto>]Ts] \<turnstile> body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>)"
(*<*)by(simp add:wf_J_mdecl_def)(*>*)


abbreviation wf_J_prog :: "'addr J_prog \<Rightarrow> bool"
where "wf_J_prog == wf_prog wf_J_mdecl"

lemma wf_mdecl_wwf_mdecl: "wf_J_mdecl P C Md \<Longrightarrow> wwf_J_mdecl P C Md"
(*<*)
apply(clarsimp simp add: wwf_J_mdecl_def)
apply(frule WT_fv)
apply(auto)
done

lemma wf_prog_wwf_prog: "wf_J_prog P \<Longrightarrow> wwf_J_prog P"
by(erule wf_prog_lift)(erule wf_mdecl_wwf_mdecl)

subsection \<open>Code generation\<close>

definition typeable_with :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool"
where [simp]: "typeable_with P E e T \<longleftrightarrow> (\<exists>T'. P,E \<turnstile> e ::' T' \<and> P \<turnstile> T' \<le> T)"

definition wf_J_mdecl' :: "'addr J_prog \<Rightarrow> cname \<Rightarrow> 'addr J_mb mdecl \<Rightarrow> bool"
where
  "wf_J_mdecl' P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and>
  distinct pns \<and>
  this \<notin> set pns \<and>
  typeable_with P [this\<mapsto>Class C,pns[\<mapsto>]Ts] body T \<and>
  \<D> body \<lfloor>{this} \<union> set pns\<rfloor>"

definition wf_J_prog' :: "'addr J_prog \<Rightarrow> bool"
where "wf_J_prog' = wf_prog wf_J_mdecl'"

lemma wf_J_prog_wf_J_prog':
  "wf_J_prog P \<Longrightarrow> wf_J_prog' P"
unfolding wf_J_prog'_def
apply(erule wf_prog_lift)
apply(clarsimp simp add: wf_J_mdecl'_def)
apply(drule (1) WT_into_WT_code)
apply(auto simp add: ran_def map_upds_def dest!: map_of_SomeD set_zip_rightD)
done

lemma wf_J_prog'_wf_J_prog:
  "wf_J_prog' P \<Longrightarrow> wf_J_prog P"
unfolding wf_J_prog'_def
apply(erule wf_prog_lift)
apply(clarsimp simp add: wf_J_mdecl'_def)
apply(drule (1) WT_code_into_WT)
apply(auto simp add: ran_def map_upds_def dest!: map_of_SomeD set_zip_rightD)
done

lemma wf_J_prog_eq_wf_J_prog' [code_unfold]:
  "wf_J_prog = wf_J_prog'"
by(blast intro: ext wf_J_prog'_wf_J_prog wf_J_prog_wf_J_prog' del: equalityI)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  typeable_with 
.

text \<open>Formal code generation test\<close>
ML_val \<open>@{code wf_J_prog'}\<close>

end
