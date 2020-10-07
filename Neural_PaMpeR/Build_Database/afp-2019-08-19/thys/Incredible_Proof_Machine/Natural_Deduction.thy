theory Natural_Deduction
imports
  Abstract_Completeness.Abstract_Completeness
  Abstract_Rules
  Entailment
begin

text \<open>Our formalization of natural deduction builds on @{theory Abstract_Completeness.Abstract_Completeness} and refines and
concretizes the structure given there as follows
 \<^item> The judgements are entailments consisting of a finite set of assumptions and a conclusion, which
   are abstract formulas in the sense of @{theory Incredible_Proof_Machine.Abstract_Formula}.
 \<^item> The abstract rules given in @{theory Incredible_Proof_Machine.Abstract_Rules} are used to decide the validity of a
   step in the derivation.
\<close>

text \<open>A single setep in the derivation can either be the axiom rule, the cut rule, or one
of the given rules in @{theory Incredible_Proof_Machine.Abstract_Rules}.\<close>

datatype 'rule NatRule = Axiom | NatRule 'rule | Cut


text \<open>The following locale is still abstract in the set of rules (\<open>nat_rule\<close>), but implements
the bookkeeping logic for assumptions, the @{term Axiom} rule and the @{term Cut} rule.\<close>

locale ND_Rules_Inst =
  Abstract_Formulas freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP
   for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form" +

  fixes nat_rule :: "'rule \<Rightarrow> 'form \<Rightarrow> ('form, 'var) antecedent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  text \<open>
  \<^item> An application of the @{term Axiom} rule is valid if the conclusion is among the assumptions.
  \<^item> An application of a @{term NatRule} is more complicated. This requires some natural number
    \<open>a\<close> to rename local variables, and some instantiation \<open>s\<close>. It checks that
     \<^item> none of the local variables occur in the context of the judgement.
     \<^item> none of the local variables occur in the instantiation.
    Together, this implements the usual freshness side-conditions.
    Furthermore, for every antecedent of the rule, the (correctly renamed and instantiated)
    hypotheses need to be added to the context.
  \<^item> The @{term Cut} rule is again easy.
  \<close>
  inductive eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
    "con |\<in>| \<Gamma>
    \<Longrightarrow> eff Axiom (\<Gamma> \<turnstile> con) {||}"
   |"nat_rule rule c ants
    \<Longrightarrow> (\<And> ant f. ant |\<in>| ants \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenLC a ` (a_fresh ant) \<inter> lconsts f = {})
    \<Longrightarrow> (\<And> ant. ant |\<in>| ants \<Longrightarrow> freshenLC a ` (a_fresh ant) \<inter> subst_lconsts s = {})
    \<Longrightarrow> eff (NatRule rule)
        (\<Gamma> \<turnstile> subst s (freshen a c))
        ((\<lambda>ant. ((\<lambda>p. subst s (freshen a p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen a (a_conc ant)))) |`| ants) "
   |"eff Cut (\<Gamma> \<turnstile> c') {| (\<Gamma> \<turnstile> c')|}"

  inductive_simps eff_Cut_simps[simp]: "eff Cut (\<Gamma> \<turnstile> c) S"

  sublocale RuleSystem_Defs where
    eff = eff and rules = "Cut ## Axiom ## smap NatRule rules".
end

text \<open>Now we instantiate the above locale. We duplicate each abstract rule (which can have multiple
consequents) for each consequent, as the natural deduction formulation can only handle a single
consequent per rule\<close>

context Abstract_Task 
begin           
  inductive natEff_Inst where
    "c \<in> set (consequent r) \<Longrightarrow> natEff_Inst (r,c) c (f_antecedent r)"

  definition n_rules where
    "n_rules = flat (smap (\<lambda>r. map (\<lambda>c. (r,c)) (consequent r)) rules)"
  
  sublocale ND_Rules_Inst _ _ _ _ _ _ _ _ natEff_Inst n_rules ..
 
  text \<open>A task is solved if for every conclusion, there is a well-formed and finite tree that proves
  this conclusion, using only assumptions given in the task.\<close>
  
  definition solved where
    "solved \<longleftrightarrow> (\<forall> c. c |\<in>| conc_forms \<longrightarrow> (\<exists> \<Gamma> t. fst (root t) = (\<Gamma> \<turnstile> c) \<and> \<Gamma> |\<subseteq>| ass_forms \<and> wf t \<and> tfinite t))"
end

end
