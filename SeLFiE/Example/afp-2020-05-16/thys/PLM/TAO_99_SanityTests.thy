(*<*)
theory TAO_99_SanityTests
imports TAO_7_Axioms
begin
(*>*)

section\<open>Sanity Tests\<close>
text\<open>\label{TAO_SanityTests}\<close>

locale SanityTests
begin
  interpretation MetaSolver.
  interpretation Semantics.

subsection\<open>Consistency\<close>
text\<open>\label{TAO_SanityTests_Consistency}\<close>

  lemma "True"
    nitpick[expect=genuine, user_axioms, satisfy]
    by auto

subsection\<open>Intensionality\<close>
text\<open>\label{TAO_SanityTests_Intensionality}\<close>

  lemma "[(\<^bold>\<lambda>y. (q \<^bold>\<or> \<^bold>\<not>q)) \<^bold>= (\<^bold>\<lambda>y. (p \<^bold>\<or> \<^bold>\<not>p)) in v]"
    unfolding identity_\<Pi>\<^sub>1_def conn_defs
    apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
    nitpick[expect = genuine, user_axioms=true, card i = 2,
            card j = 2, card \<omega> = 1, card \<sigma> = 1,
            sat_solver = MiniSat_JNI, verbose, show_all]
    oops \<comment> \<open>Countermodel by Nitpick\<close>
  lemma "[(\<^bold>\<lambda>y. (p \<^bold>\<or> q)) \<^bold>= (\<^bold>\<lambda>y. (q \<^bold>\<or> p)) in v]"
    unfolding identity_\<Pi>\<^sub>1_def
    apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
    nitpick[expect = genuine, user_axioms=true,
            sat_solver = MiniSat_JNI, card i = 2,
            card j = 2, card \<sigma> = 1, card \<omega> = 1,
            card \<upsilon> = 2, verbose, show_all]
    oops \<comment> \<open>Countermodel by Nitpick\<close>

subsection\<open>Concreteness coindices with Object Domains\<close>
text\<open>\label{TAO_SanityTests_Concreteness}\<close>

  lemma OrdCheck:
    "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow>
     (proper x) \<and> (case (rep x) of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    apply (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
    using \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> by fastforce
  lemma AbsCheck:
    "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow>
     (proper x) \<and> (case (rep x) of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    apply (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
    using no_\<alpha>\<omega> by blast

subsection\<open>Justification for Meta-Logical Axioms\<close>
text\<open>\label{TAO_SanityTests_MetaAxioms}\<close>

text\<open>
\begin{remark}
  OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all ordinary objects are
   possibly concrete".
\end{remark}
\<close>
  lemma OrdAxiomCheck:
    "OrdinaryObjectsPossiblyConcrete \<longleftrightarrow>
      (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v]
       \<longleftrightarrow> (case x of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    unfolding Concrete_def
    apply (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
    using \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> by fastforce

text\<open>
\begin{remark}
  OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all abstract objects are
  necessarily not concrete".
\end{remark}
\<close>

  lemma AbsAxiomCheck:
    "OrdinaryObjectsPossiblyConcrete \<longleftrightarrow>
      (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v]
       \<longleftrightarrow> (case x of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    apply (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
    using \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> no_\<alpha>\<omega> by fastforce
  
text\<open>
\begin{remark}
  PossiblyContingentObjectExistsAxiom is equivalent to the corresponding statement
  in the embedded logic.
\end{remark}
\<close>

  lemma PossiblyContingentObjectExistsCheck:
    "PossiblyContingentObjectExists \<longleftrightarrow> [\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
     apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
     by (metis \<nu>.simps(5) \<nu>\<upsilon>_def \<upsilon>.simps(1) no_\<sigma>\<omega> \<upsilon>.exhaust)

text\<open>
\begin{remark}
  PossiblyNoContingentObjectExistsAxiom is equivalent to the corresponding statement
  in the embedded logic.
\end{remark}
\<close>

  lemma PossiblyNoContingentObjectExistsCheck:
    "PossiblyNoContingentObjectExists \<longleftrightarrow> [\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>))) in v]"
    apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    using \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> by blast

subsection\<open>Relations in the Meta-Logic\<close>
text\<open>\label{TAO_SanityTests_MetaRelations}\<close>

text\<open>
\begin{remark}
  Material equality in the embedded logic corresponds to
  equality in the actual state in the meta-logic.
\end{remark}
\<close>

  lemma mat_eq_is_eq_dj:
    "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v] \<longleftrightarrow>
     ((\<lambda> x . (eval\<Pi>\<^sub>1 F) x dj) = (\<lambda> x . (eval\<Pi>\<^sub>1 G) x dj))"
  proof
    assume 1: "[\<^bold>\<forall>x. \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
    {
      fix v
      fix y
      obtain x where y_def: "y = \<nu>\<upsilon> x"
        by (meson \<nu>\<upsilon>_surj surj_def)
      have "(\<exists>r o\<^sub>1. Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 \<in> ex1 r v) =
            (\<exists>r o\<^sub>1. Some r = d\<^sub>1 G \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 \<in> ex1 r v)"
            using 1 apply - by meta_solver
      moreover obtain r where r_def: "Some r = d\<^sub>1 F"
        unfolding d\<^sub>1_def by auto
      moreover obtain s where s_def: "Some s = d\<^sub>1 G"
        unfolding d\<^sub>1_def by auto
      moreover have "Some x = d\<^sub>\<kappa> (x\<^sup>P)"
        using d\<^sub>\<kappa>_proper by simp
      ultimately have "(x \<in> ex1 r v) = (x \<in> ex1 s v)"
        by (metis option.inject)
      hence "(eval\<Pi>\<^sub>1 F) y dj v = (eval\<Pi>\<^sub>1 G) y dj v"
        using r_def s_def y_def by (simp add: d\<^sub>1.rep_eq ex1_def)
    }
    thus "(\<lambda>x. eval\<Pi>\<^sub>1 F x dj) = (\<lambda>x. eval\<Pi>\<^sub>1 G x dj)"
      by auto
  next
    assume 1: "(\<lambda>x. eval\<Pi>\<^sub>1 F x dj) = (\<lambda>x. eval\<Pi>\<^sub>1 G x dj)"
    {
      fix y v
      obtain x where x_def: "x = \<nu>\<upsilon> y"
        by simp
      hence "eval\<Pi>\<^sub>1 F x dj = eval\<Pi>\<^sub>1 G x dj"
        using 1 by metis
      moreover obtain r where r_def: "Some r = d\<^sub>1 F"
        unfolding d\<^sub>1_def by auto
      moreover obtain s where s_def: "Some s = d\<^sub>1 G"
        unfolding d\<^sub>1_def by auto
      ultimately have "(y \<in> ex1 r v) = (y \<in> ex1 s v)"
        by (simp add: d\<^sub>1.rep_eq ex1_def \<nu>\<upsilon>_surj x_def)
      hence "[\<lparr>F,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,y\<^sup>P\<rparr> in v]"
        apply - apply meta_solver
        using r_def s_def by (metis Semantics.d\<^sub>\<kappa>_proper option.inject)
    }
    thus "[\<^bold>\<forall>x. \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
      using T6 T8 by fast
  qed

text\<open>
\begin{remark}
  Materially equivalent relations are equal in the embedded logic
  if and only if they also coincide in all other states.
\end{remark}
\<close>

  lemma mat_eq_is_eq_if_eq_forall_j:
    assumes "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
    shows "[F \<^bold>= G in v] \<longleftrightarrow>
           (\<forall> s . s \<noteq> dj \<longrightarrow> (\<forall> x . (eval\<Pi>\<^sub>1 F) x s = (eval\<Pi>\<^sub>1 G) x s))"
    proof
      interpret MetaSolver .
      assume "[F \<^bold>= G in v]"
      hence "F = G"
        apply - unfolding identity_\<Pi>\<^sub>1_def by meta_solver
      thus "\<forall>s. s \<noteq> dj \<longrightarrow> (\<forall>x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s)"
        by auto
    next
      interpret MetaSolver .
      assume "\<forall>s. s \<noteq> dj \<longrightarrow> (\<forall>x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s)"
      moreover have "((\<lambda> x . (eval\<Pi>\<^sub>1 F) x dj) = (\<lambda> x . (eval\<Pi>\<^sub>1 G) x dj))"
        using assms mat_eq_is_eq_dj by auto
      ultimately have "\<forall>s x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s"
        by metis
      hence "eval\<Pi>\<^sub>1 F = eval\<Pi>\<^sub>1 G"
        by blast
      hence "F = G"
        by (metis eval\<Pi>\<^sub>1_inverse)
      thus "[F \<^bold>= G in v]"
        unfolding identity_\<Pi>\<^sub>1_def using Eq\<^sub>1I by auto
    qed

text\<open>
\begin{remark}
  Under the assumption that all properties behave in all states like in the actual state
  the defined equality degenerates to material equality.
\end{remark}
\<close>

  lemma assumes "\<forall> F x s . (eval\<Pi>\<^sub>1 F) x s = (eval\<Pi>\<^sub>1 F) x dj"
    shows "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v] \<longleftrightarrow> [F \<^bold>= G in v]"
    by (metis (no_types) MetaSolver.Eq\<^sub>1S assms identity_\<Pi>\<^sub>1_def
                         mat_eq_is_eq_dj mat_eq_is_eq_if_eq_forall_j)

subsection\<open>Lambda Expressions\<close>
text\<open>\label{TAO_SanityTests_MetaLambda}\<close>

  lemma lambda_interpret_1:
  assumes "[a \<^bold>= b in v]"
  shows "(\<^bold>\<lambda>x. \<lparr>R,x\<^sup>P,a\<rparr>) = (\<^bold>\<lambda>x . \<lparr>R,x\<^sup>P, b\<rparr>)"
  proof -
    have "a = b"
      using MetaSolver.Eq\<kappa>S Semantics.d\<^sub>\<kappa>_inject assms
            identity_\<kappa>_def by auto
    thus ?thesis by simp
  qed

  lemma lambda_interpret_2:
  assumes "[a \<^bold>= (\<^bold>\<iota>y. \<lparr>G,y\<^sup>P\<rparr>) in v]"
  shows "(\<^bold>\<lambda>x. \<lparr>R,x\<^sup>P,a\<rparr>) = (\<^bold>\<lambda>x . \<lparr>R,x\<^sup>P, \<^bold>\<iota>y. \<lparr>G,y\<^sup>P\<rparr>\<rparr>)"
  proof -
    have "a = (\<^bold>\<iota>y. \<lparr>G,y\<^sup>P\<rparr>)"
      using MetaSolver.Eq\<kappa>S Semantics.d\<^sub>\<kappa>_inject assms
            identity_\<kappa>_def by auto
    thus ?thesis by simp
  qed

end

(*<*)
end
(*>*)
