(*File: Reachability.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Operational judgement that extends MultiStep by
           entering subframes. Necessary for the interpretation
           of invariants.            
*)
(*<*)
theory Reachability imports Language begin
(*>*)

subsection\<open>Reachability relation\<close> 

text\<open>The second auxiliary operational judgement is required for the
interpretation of invariants and method invariants. Invariants are
expected to be satisfied in all heap components of (future) states
that occur either in the same frame as the current state or a subframe
thereof. Likewise, method invariants are expected to be satisfied by
all heap components of states observed during the execution of a
method, including subframes. None of the previous three operational
judgements allows us to express these interpretations, as \<open>Step\<close>
injects the execution of an invoked method as a single step. Thus,
states occurring in subframes cannot be related to states occurring in
the parent frame using these judgements. This motivates the
introduction of predicates relating states $s$ and $t$ whenever the
latter can be reach from the former, i.e.~whenever $t$ occurs as a
successor of $s$ in the same frame as $s$ or one of its
subframes. Again, we first define a relation that includes an explicit
derivation height index.\<close>

inductive_set
  Reachable::"(Mbody \<times> Label \<times> State \<times> nat \<times> State) set" 
where
Reachable_zero: "\<lbrakk>k=0; t=s\<rbrakk> \<Longrightarrow> (M,l,s,k,t):Reachable"
|
Reachable_step: 
  "\<lbrakk> (M,l,s,n,ll,r):Step; (M,ll,r,m,t):Reachable; k=Suc m+n\<rbrakk>
  \<Longrightarrow> (M,l,s,k,t) : Reachable"
|
Reachable_invS: 
  "\<lbrakk> mbody_is C m (par,code,l0); get_ins M l = Some (invokeS C m);
      s = (ops,S,h); (ops,par,R,ops1):Frame;
     ((par,code,l0), l0, ([],R,h), n, t):Reachable; k=Suc n\<rbrakk>
  \<Longrightarrow> (M,l,s,k,t) : Reachable"

text\<open>The following properties of are useful to notice.\<close>
(*<*)
lemma ZeroHeightReachableElimAux[rule_format]:
  "(M, l, s, k, r) \<in> Reachable \<Longrightarrow> 0=k \<longrightarrow> r=s"
by (erule Reachable.induct, simp_all) 
(*>*) 
lemma ZeroHeightReachableElim: "(M,l,s,0,r) \<in> Reachable \<Longrightarrow> r=s"
(*<*)
by (erule ZeroHeightReachableElimAux, simp)
(*>*)

lemma ReachableSplit[rule_format]:
  "(M, l,s, k, t) \<in> Reachable \<Longrightarrow> 
    1 \<le> k \<longrightarrow> 
   ((\<exists> n m r ll. (M,l,s,n,ll,r):Step \<and> 
                 (M,ll,r,m,t):Reachable \<and> Suc m +n =k) \<or>
    (\<exists> n ops S h c m par R ops1 code l0. 
          s=(ops,S,h) \<and> get_ins M l = Some (invokeS c m) \<and> 
          mbody_is c m (par,code,l0) \<and> (ops,par,R,ops1):Frame \<and> 
          ((par,code,l0), l0, ([],R,h), n, t):Reachable \<and> Suc n = k))"
(*<*)
apply (erule Reachable.induct, simp_all)
apply clarsimp
  apply (case_tac m, clarsimp) 
    apply (drule ZeroHeightReachableElim[simplified], clarsimp) 
      apply (rule, rule,rule, rule,rule, rule, rule, assumption) 
      apply (rule,rule Reachable_zero) apply simp apply simp apply simp
  apply clarsimp
    apply (rule, rule,rule, rule,rule, rule,rule,assumption) apply (rule,assumption)
    apply simp
apply (rule disjI2)
apply fast
done
(*>*)

lemma Reachable_returnElim[rule_format]:
"(M,l,s,k,t) \<in> Reachable \<Longrightarrow> get_ins M l = Some vreturn \<longrightarrow> t=s"
(*<*)
apply (erule Reachable.induct)
apply clarsimp
apply clarsimp apply (drule RetElim1) apply simp apply clarsimp
apply clarsimp
done
(*>*)

text\<open>Similar to the operational semantics, we define a variation of
the reachability relation that hides the index.\<close>

definition Reach::"Mbody \<Rightarrow> Label \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
where "Reach M l s t = (\<exists> k . (M,l,s,k,t):Reachable)"

(*<*)  
end
(*>*)
