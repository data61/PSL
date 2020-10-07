(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Congruence
  imports Weak_Cong_Struct_Cong Bisim_Subst
begin

context env begin

definition weakCongruence :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<doteq>\<^sub>c _" [70, 70] 65)
where 
  "P \<doteq>\<^sub>c Q \<equiv> \<forall>\<Psi> \<sigma>. wellFormedSubst \<sigma> \<longrightarrow> \<Psi> \<rhd> P[<\<sigma>>] \<doteq> Q[<\<sigma>>]"

lemma weakCongE:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "P \<doteq>\<^sub>c Q"
  "wellFormedSubst \<sigma>"

  shows "\<Psi> \<rhd> P[<\<sigma>>] \<doteq> Q[<\<sigma>>]"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongI[case_names cWeakPsiCong]:
  fixes P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<And>\<Psi> \<sigma>. wellFormedSubst \<sigma> \<Longrightarrow> \<Psi> \<rhd> P[<\<sigma>>] \<doteq> Q[<\<sigma>>]"

  shows "P \<doteq>\<^sub>c Q"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongClosed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"
  
  assumes "P \<doteq>\<^sub>c Q"

  shows "(p \<bullet> P) \<doteq>\<^sub>c (p \<bullet> Q)"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  note \<open>P \<doteq>\<^sub>c Q\<close>
  moreover from \<open>wellFormedSubst \<sigma>\<close> have "wellFormedSubst (rev p \<bullet> \<sigma>)" by simp
  ultimately have "((rev p) \<bullet> \<Psi>) \<rhd> P[<(rev p \<bullet> \<sigma>)>] \<doteq>  Q[<(rev p \<bullet> \<sigma>)>]"
    by(rule weakCongE)
  thus ?case by(drule_tac p=p in weakPsiCongClosed) (simp add: eqvts)
qed

lemma weakCongReflexive:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"

  shows "P \<doteq>\<^sub>c P"
by(auto intro: weakCongI weakPsiCongReflexive)

lemma weakCongSym:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"

  assumes "P \<doteq>\<^sub>c Q"

  shows "Q \<doteq>\<^sub>c P"
using assms
by(auto simp add: weakCongruence_def weakPsiCongSym)

lemma weakCongTransitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<doteq> Q"
  and     "\<Psi> \<rhd> Q \<doteq> R"

  shows "\<Psi> \<rhd> P \<doteq> R"
using assms
by(auto intro: weakCongI weakPsiCongTransitive dest: weakCongE)

lemma weakCongWeakBisim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<doteq>\<^sub>c Q"

  shows "\<Psi> \<rhd> P \<approx> Q"
using assms
apply(drule_tac \<sigma>="[]" in weakCongE)
by(auto dest: weakPsiCongE)

lemma weakCongWeakPsiCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<doteq>\<^sub>c Q"

  shows "\<Psi> \<rhd> P \<doteq> Q"
using assms
by(drule_tac weakCongE[where \<Psi>=\<Psi> and \<sigma>="[]"]) auto

lemma strongBisimWeakCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<sim>\<^sub>s Q"

  shows "P \<doteq>\<^sub>c Q"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  from assms \<open>wellFormedSubst \<sigma>\<close> have "P[<\<sigma>>] \<sim> Q[<\<sigma>>]"
    by(rule closeSubstE)
  hence "\<Psi> \<rhd> P[<\<sigma>>] \<sim> Q[<\<sigma>>]" by(metis bisimE(3) statEqBisim Identity Commutativity)
  thus ?case by(rule strongBisimWeakPsiCong)
qed

lemma structCongWeakCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<doteq>\<^sub>c Q"
using assms
by(metis strongBisimWeakCong structCongBisimSubst)

lemma weakCongUnfold:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "P \<doteq>\<^sub>c Q"
  and     "wellFormedSubst \<sigma>"

  shows "P[<\<sigma>>] \<doteq>\<^sub>c Q[<\<sigma>>]"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>')
  with \<open>wellFormedSubst \<sigma>\<close> \<open>wellFormedSubst \<sigma>'\<close> have "wellFormedSubst(\<sigma>@\<sigma>')" by simp
  with \<open>P \<doteq>\<^sub>c Q\<close> have "\<Psi> \<rhd> P[<(\<sigma>@\<sigma>')>] \<doteq> Q[<(\<sigma>@\<sigma>')>]"
    by(rule weakCongE)
  thus "\<Psi> \<rhd> P[<\<sigma>>][<\<sigma>'>] \<doteq> Q[<\<sigma>>][<\<sigma>'>]"
    by simp
qed

lemma weakCongOutputPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a
  
  assumes "P \<doteq>\<^sub>c Q"

  shows "M\<langle>N\<rangle>.P \<doteq>\<^sub>c M\<langle>N\<rangle>.Q"
using assms
by(fastforce intro: weakCongI weakCongE weakPsiCongOutputPres)

lemma weakCongInputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "P \<doteq>\<^sub>c Q"
  and     "distinct xvec"

  shows "M\<lparr>\<lambda>*xvec N\<rparr>.P \<doteq>\<^sub>c M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  obtain p where "(p \<bullet> xvec) \<sharp>* \<sigma>"
             and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* N"
             and S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
      by(rule_tac c="(\<sigma>, P, Q, \<Psi>, N)" in name_list_avoiding) auto
    
  from \<open>P \<doteq>\<^sub>c Q\<close> have "(p \<bullet> P) \<doteq>\<^sub>c (p \<bullet> Q)"
    by(rule weakCongClosed)
  {
    fix Tvec :: "'a list"
    from \<open>(p \<bullet> P) \<doteq>\<^sub>c (p \<bullet> Q)\<close> \<open>wellFormedSubst \<sigma>\<close> have "(p \<bullet> P)[<\<sigma>>] \<doteq>\<^sub>c (p \<bullet> Q)[<\<sigma>>]"
      by(rule weakCongUnfold)
    moreover assume "length xvec = length Tvec" and "distinct xvec"
    ultimately have "\<Psi> \<rhd> ((p \<bullet> P)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec] \<doteq> ((p \<bullet> Q)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec]" 
      by(drule_tac weakCongE[where \<sigma>="[((p \<bullet> xvec), Tvec)]"]) auto
    hence "\<Psi> \<rhd> ((p \<bullet> P)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec] \<approx> ((p \<bullet> Q)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec]"
      by(rule weakPsiCongE)
  }

  with \<open>(p \<bullet> xvec) \<sharp>* \<sigma>\<close> \<open>distinct xvec\<close>
  have "\<Psi> \<rhd> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P))[<\<sigma>>] \<doteq> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q))[<\<sigma>>]"
    by(force intro: weakPsiCongInputPres)
  moreover from \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) = M\<lparr>\<lambda>*xvec N\<rparr>.P" 
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  moreover from \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q) = M\<lparr>\<lambda>*xvec N\<rparr>.Q"
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  ultimately show ?case by force
qed

lemma weakCongCasePresAux:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"
  
  assumes C1: "\<And>\<phi> P. (\<phi>, P) mem CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> P \<doteq>\<^sub>c Q"
  and     C2: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> P \<doteq>\<^sub>c Q"

  shows "Cases CsP \<doteq>\<^sub>c Cases CsQ"
proof -
  {
    fix \<Psi> :: 'b
    fix \<sigma> :: "(name list \<times> 'a list) list"

    assume "wellFormedSubst \<sigma>"
    have "\<Psi> \<rhd> Cases(caseListSeqSubst CsP \<sigma>) \<doteq> Cases(caseListSeqSubst CsQ \<sigma>)"
    proof(rule weakPsiCongCasePres)
      fix \<phi> P
      assume "(\<phi>, P) mem (caseListSeqSubst CsP \<sigma>)"
      then obtain \<phi>' P' where "(\<phi>', P') mem CsP" and "\<phi> = substCond.seqSubst \<phi>' \<sigma>" and PeqP': "P = (P'[<\<sigma>>])"
        by(induct CsP) force+
      from \<open>(\<phi>', P') mem CsP\<close> obtain Q' where "(\<phi>', Q') mem CsQ" and "guarded Q'" and "P' \<doteq>\<^sub>c Q'" by(blast dest: C1)
      from \<open>(\<phi>', Q') mem CsQ\<close> \<open>\<phi> = substCond.seqSubst \<phi>' \<sigma>\<close> obtain Q where "(\<phi>, Q) mem (caseListSeqSubst CsQ \<sigma>)" and "Q = Q'[<\<sigma>>]"
        by(induct CsQ) auto
      with PeqP' \<open>guarded Q'\<close> \<open>P' \<doteq>\<^sub>c Q'\<close> \<open>wellFormedSubst \<sigma>\<close> show "\<exists>Q. (\<phi>, Q) mem (caseListSeqSubst CsQ \<sigma>) \<and> guarded Q \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"
        by(blast dest: weakCongE guardedSeqSubst)
    next
      fix \<phi> Q
      assume "(\<phi>, Q) mem (caseListSeqSubst CsQ \<sigma>)"
      then obtain \<phi>' Q' where "(\<phi>', Q') mem CsQ" and "\<phi> = substCond.seqSubst \<phi>' \<sigma>" and QeqQ': "Q = Q'[<\<sigma>>]"
        by(induct CsQ) force+
      from \<open>(\<phi>', Q') mem CsQ\<close> obtain P' where "(\<phi>', P') mem CsP" and "guarded P'" and "P' \<doteq>\<^sub>c Q'" by(blast dest: C2)
      from \<open>(\<phi>', P') mem CsP\<close> \<open>\<phi> = substCond.seqSubst \<phi>' \<sigma>\<close> obtain P where "(\<phi>, P) mem (caseListSeqSubst CsP \<sigma>)" and "P = P'[<\<sigma>>]"
        by(induct CsP) auto
      with QeqQ' \<open>guarded P'\<close> \<open>P' \<doteq>\<^sub>c Q'\<close> \<open>wellFormedSubst \<sigma>\<close>
      show "\<exists>P. (\<phi>, P) mem (caseListSeqSubst CsP \<sigma>) \<and> guarded P \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"
        by(blast dest: weakCongE guardedSeqSubst)
    qed
  }
  thus ?thesis
    by(rule_tac weakCongI) auto
qed

lemma weakCongParPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"
  
  assumes "P \<doteq>\<^sub>c Q"

  shows "P \<parallel> R \<doteq>\<^sub>c Q \<parallel> R"
using assms
by(fastforce intro: weakCongI weakCongE weakPsiCongParPres)

lemma weakCongResPres:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name

  assumes "P \<doteq>\<^sub>c Q"

  shows "\<lparr>\<nu>x\<rparr>P \<doteq>\<^sub>c \<lparr>\<nu>x\<rparr>Q"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  obtain y::name where "y \<sharp> (\<Psi>::'b)" and "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<sigma>"
    by(generate_fresh "name") (auto simp add: fresh_prod)

  from \<open>P \<doteq>\<^sub>c Q\<close> have "([(x, y)] \<bullet> P) \<doteq>\<^sub>c ([(x, y)] \<bullet> Q)" by(rule weakCongClosed)
  hence "\<Psi> \<rhd> ([(x, y)] \<bullet> P)[<\<sigma>>] \<doteq> ([(x, y)] \<bullet> Q)[<\<sigma>>]" using \<open>wellFormedSubst \<sigma>\<close>
    by(rule weakCongE)
  hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P)[<\<sigma>>]) \<doteq> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)[<\<sigma>>])" using \<open>y \<sharp> \<Psi>\<close>
    by(rule weakPsiCongResPres)
  with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close>  \<open>y \<sharp> \<sigma>\<close>
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>P)[<\<sigma>>] \<doteq> (\<lparr>\<nu>x\<rparr>Q)[<\<sigma>>]"
    by(simp add: alphaRes)
qed

lemma weakCongBangPres:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
 
  assumes "P \<doteq>\<^sub>c Q"
  and     "guarded P"
  and     "guarded Q"

  shows "!P \<doteq>\<^sub>c !Q"
using assms
by(fastforce intro: weakCongI weakCongE weakPsiCongBangPres  guardedSeqSubst)

end

end



