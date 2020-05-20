(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Close_Subst
  imports Agent
begin

context substPsi
begin

definition closeSubst :: "('b::fs_name \<times> ('a::fs_name, 'b, 'c::fs_name) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
where "closeSubst Rel \<equiv> {(\<Psi>, P, Q) | \<Psi> P Q. (\<forall>\<sigma>. wellFormedSubst \<sigma> \<longrightarrow> (\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel)}"

lemma closeSubstI:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<And>\<sigma>. wellFormedSubst \<sigma> \<Longrightarrow> (\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel"

  shows "(\<Psi>, P, Q) \<in> closeSubst Rel"
using assms
by(unfold closeSubst_def) auto

lemma closeSubstE:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "(\<Psi>, P, Q) \<in> closeSubst Rel"
  and     "wellFormedSubst \<sigma>"

  shows "(\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel"
using assms
by(unfold closeSubst_def) auto

lemma closeSubstClosed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"

  assumes "eqvt Rel"
  and     "(\<Psi>, P, Q) \<in> closeSubst Rel"

  shows "(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> closeSubst Rel"
proof(rule closeSubstI)
  fix \<sigma>
  assume "wellFormedSubst(\<sigma>::(name list \<times> 'a list) list)"
  with \<open>(\<Psi>, P, Q) \<in> closeSubst Rel\<close> \<open>wellFormedSubst \<sigma>\<close>
  have "(\<Psi>, P[<(rev p \<bullet> \<sigma>)>], Q[<(rev p \<bullet> \<sigma>)>]) \<in> Rel"
    by(rule_tac closeSubstE) auto
  hence "(p \<bullet> \<Psi>, p \<bullet> (P[<(rev p \<bullet> \<sigma>)>]), p \<bullet> (Q[<(rev p \<bullet> \<sigma>)>])) \<in> Rel"
    by(drule_tac p=p in eqvtI[OF \<open>eqvt Rel\<close>]) (simp add: eqvts)
  thus "(p \<bullet> \<Psi>, (p \<bullet> P)[<\<sigma>>], (p \<bullet> Q)[<\<sigma>>]) \<in> Rel"
    by(simp del: seqSubs_def add: eqvts)
qed

lemma closeSubstEqvt:
  assumes "eqvt Rel"

  shows "eqvt(closeSubst Rel)"
proof(auto simp add: eqvt_def)
  fix \<Psi> P Q p
  assume "(\<Psi>, P, Q) \<in> closeSubst Rel"
  thus "((p::name prm) \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> closeSubst Rel"
    by(drule_tac p=p in closeSubstClosed[OF \<open>eqvt Rel\<close>]) (simp add: eqvts)
qed

lemma closeSubstUnfold:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "(\<Psi>, P, Q) \<in> closeSubst Rel"
  and     "wellFormedSubst \<sigma>"

  shows "(\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> closeSubst Rel"
proof(rule closeSubstI)
  fix \<sigma>'::"(name list \<times> 'a list) list"
  assume "wellFormedSubst \<sigma>'"
  with \<open>wellFormedSubst \<sigma>\<close> have "wellFormedSubst(\<sigma>@\<sigma>')" by simp
  with \<open>(\<Psi>, P, Q) \<in> closeSubst Rel\<close> have "(\<Psi>, P[<(\<sigma>@\<sigma>')>], Q[<(\<sigma>@\<sigma>')>]) \<in> Rel"
    by(rule closeSubstE)
  thus "(\<Psi>, P[<\<sigma>>][<\<sigma>'>], Q[<\<sigma>>][<\<sigma>'>]) \<in> Rel"
    by simp
qed

end

end
  

  


