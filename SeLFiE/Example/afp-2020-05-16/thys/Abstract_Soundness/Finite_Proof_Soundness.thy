(*<*)
theory Finite_Proof_Soundness
imports Abstract_Completeness.Abstract_Completeness
begin
(*>*)

section \<open>Abstract Soundness\<close>

locale Soundness = RuleSystem_Defs eff rules for
  eff :: "'rule \<Rightarrow> 'sequent \<Rightarrow> 'sequent fset \<Rightarrow> bool"
  and rules :: "'rule stream" +
  fixes "structure" :: "'structure set"
    and sat :: "'structure \<Rightarrow> 'sequent \<Rightarrow> bool"
  assumes local_soundness:
    "\<And>r s sl.
      \<lbrakk>r \<in> R; eff r s sl; \<And>s'. s' |\<in>| sl \<Longrightarrow> \<forall>S \<in> structure. sat S s'\<rbrakk>
      \<Longrightarrow>
      \<forall>S \<in> structure. sat S s"
begin

abbreviation "ssat s \<equiv> \<forall>S \<in> structure. sat S s"

lemma epath_shift:
  assumes "epath (srs @- steps)"
  shows "epath steps"
  using assms by (induction srs arbitrary: steps) (auto elim: epath.cases)

theorem soundness:
  assumes f: "tfinite t" and w: "wf t"
  shows "ssat (fst (root t))"
  using f w proof (induction t rule: tfinite.induct)
  case (tfinite t)
  show ?case
    by (rule local_soundness[of "snd (root t)" _ "fimage (fst o root) (cont t)"], insert tfinite)
      (fastforce elim!: wf.cases)+
qed

end (* context Soundness *)

(*<*)
end
(*>*)
