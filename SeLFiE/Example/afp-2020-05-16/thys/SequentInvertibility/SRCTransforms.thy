(*<*)
(* Author : Peter Chapman *)
(* License: LGPL *)
section "Rule Set Transformations"
 
theory SRCTransforms
imports "HOL-Library.Multiset"
begin

datatype 'a form = At "nat"
                 | Compound "'a" "'a form list"
                 | ff

datatype 'a sequent = Sequent "('a form) multiset" "('a form) multiset" (" (_) \<Rightarrow>* (_)" [6,6] 5)

abbreviation multiset_abbrev ("\<LM> _  \<RM>" [75]75) where
   "\<LM> A \<RM> \<equiv> {# A #}"

abbreviation multiset_empty ("\<Empt>" 75) where
  "\<Empt> \<equiv> {#}"

(* We have that any step in a rule, be it a primitive rule or an instance of a rule in a derivation
   can be represented as a list of premisses and a conclusion.  We need a list since a list is finite
   by definition *)
type_synonym 'a rule = "'a sequent list * 'a sequent"

type_synonym 'a deriv = "'a sequent * nat"

abbreviation
multiset_plus (infixl "\<oplus>" 80) where
   "(\<Gamma> :: 'a multiset) \<oplus> (A :: 'a) \<equiv> \<Gamma> + \<LM>A\<RM>"
abbreviation
multiset_minus (infixl "\<ominus>" 80) where
   "(\<Gamma> :: 'a multiset) \<ominus>  (A :: 'a) \<equiv> \<Gamma> - \<LM>A\<RM>" 

consts
  (* extend a sequent by adding another one.  A form of weakening.  Is this overkill by adding a sequent? *)
  extend :: "'a sequent \<Rightarrow> 'a sequent \<Rightarrow> 'a sequent"
  extendRule :: "'a sequent \<Rightarrow> 'a rule \<Rightarrow> 'a rule"

  (* Unique conclusion Property *)
  uniqueConclusion :: "'a rule set \<Rightarrow> bool"

  (* Invertible definitions *)
  invertible :: "'a rule \<Rightarrow> 'a rule set \<Rightarrow> bool"
  invertible_set :: "'a rule set \<Rightarrow> bool"

  (* functions to get at components of sequents *)
primrec antec :: "'a sequent \<Rightarrow> 'a form multiset" where "antec (Sequent ant suc) = ant"
primrec succ :: "'a sequent \<Rightarrow> 'a form multiset" where "succ (Sequent ant suc) = suc"
primrec mset :: "'a sequent \<Rightarrow> 'a form multiset" where "mset (Sequent ant suc) = ant + suc"
primrec seq_size :: "'a sequent \<Rightarrow> nat" where "seq_size (Sequent ant suc) = size ant + size suc"

(* Extend a sequent, and then a rule by adding seq to all premisses and the conclusion *)
overloading
  extend \<equiv> extend
  extendRule \<equiv> extendRule
  uniqueConclusion \<equiv> uniqueConclusion
begin

definition extend
  where "extend forms seq \<equiv> (antec forms + antec seq) \<Rightarrow>* (succ forms + succ seq)"

definition extendRule
  where "extendRule forms R \<equiv> (map (extend forms) (fst R), extend forms (snd R))"

(* The unique conclusion property.  A set of rules has unique conclusion property if for any pair of rules,
   the conclusions being the same means the rules are the same*)
definition uniqueConclusion :: "'a rule set \<Rightarrow> bool"
  where "uniqueConclusion R \<equiv> \<forall> r1 \<in> R. \<forall> r2 \<in> R. (snd r1 = snd r2) \<longrightarrow> (r1 =r2)"

end

primrec max_list :: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (n # ns) = max n (max_list ns)"

(* The depth of a formula.  Will be useful in later files. *)
fun depth :: "'a form \<Rightarrow> nat"
where
   "depth (At i) = 0"
|  "depth (Compound f fs) = (max_list (map depth fs)) + 1"
|  "depth (ff) = 0"

(* The formulation of various rule sets *)

(* Ax is the set containing all identity RULES and LBot *)
inductive_set "Ax" where
   id[intro]: "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) \<in> Ax"
|  Lbot[intro]: "([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<in> Ax"

(* upRules is the set of all rules which have a single conclusion.  This is akin to each rule having a 
   single principal formula.  We don't want rules to have no premisses, hence the restriction
   that ps \<noteq> [] *)
inductive_set "upRules" where
   I[intro]: "\<lbrakk> mset c \<equiv> \<LM> Compound R Fs \<RM> ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules"

inductive_set extRules :: "'a rule set \<Rightarrow> 'a rule set"  ("_*")
  for R :: "'a rule set" 
  where
   I[intro]: "r \<in> R \<Longrightarrow> extendRule seq r \<in> R*"

(* A formulation of what it means to be a principal formula for a rule.  Note that we have to build up from
   single conclusion rules.   *)

inductive leftPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up[intro]: "C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)  \<Longrightarrow> 
                   leftPrincipal (Ps,C) (Compound F Fs)"


inductive rightPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up[intro]: "C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<Longrightarrow> rightPrincipal (Ps,C) (Compound F Fs)"


(* What it means to be a derivable sequent.  Can have this as a predicate or as a set.
   The two formation rules say that the supplied premisses are derivable, and the second says
   that if all the premisses of some rule are derivable, then so is the conclusion.  *)

inductive_set derivable :: "'a rule set \<Rightarrow> 'a deriv set"
  for R :: "'a rule set"
  where
   base[intro]: "\<lbrakk>([],C) \<in> R\<rbrakk> \<Longrightarrow> (C,0) \<in> derivable R"
|  step[intro]: "\<lbrakk> r \<in> R ; (fst r)\<noteq>[] ; \<forall> p \<in> set (fst r). \<exists> n \<le> m. (p,n) \<in> derivable R \<rbrakk> 
                       \<Longrightarrow> (snd r,m + 1) \<in> derivable R"


(* When we don't care about height! *)
inductive_set derivable' :: "'a rule set \<Rightarrow> 'a sequent set"
   for R :: "'a rule set"
   where
    base[intro]: "\<lbrakk> ([],C) \<in> R \<rbrakk> \<Longrightarrow> C \<in> derivable' R"
|   step[intro]: "\<lbrakk> r \<in> R ; (fst r) \<noteq> [] ; \<forall> p \<in> set (fst r). p \<in> derivable' R \<rbrakk>
                       \<Longrightarrow> (snd r) \<in> derivable' R"

lemma deriv_to_deriv[simp]:
assumes "(C,n) \<in> derivable R"
shows "C \<in> derivable' R"
using assms by (induct) auto

lemma deriv_to_deriv2:
assumes "C \<in> derivable' R"
shows "\<exists> n. (C,n) \<in> derivable R"
using assms
proof (induct)
  case (base C)
  then have "(C,0) \<in> derivable R" by auto
  then show ?case by blast
next
  case (step r)
  then obtain ps c where "r = (ps,c)" and "ps \<noteq> []" by (cases r) auto
  then have aa: "\<forall> p \<in> set ps. \<exists> n. (p,n) \<in> derivable R" using step(3) by auto
  then have "\<exists> m. \<forall> p \<in> set ps. \<exists> n\<le>m. (p,n) \<in> derivable R"
  proof (induct ps)
    case Nil
    then show ?case  by auto
  next
    case (Cons a as)
    then have "\<exists> m. \<forall> p \<in> set as. \<exists> n\<le>m. (p,n) \<in> derivable R" by auto
    then obtain m where "\<forall> p \<in> set as. \<exists> n\<le>m. (p,n) \<in> derivable R" by auto
    moreover from \<open>\<forall> p \<in> set (a # as). \<exists> n. (p,n) \<in> derivable R\<close> have
      "\<exists> n. (a,n) \<in> derivable R" by auto
    then obtain m' where "(a,m') \<in> derivable R" by blast
    ultimately have "\<forall> p \<in> set (a # as). \<exists> n\<le>(max m m'). (p,n) \<in> derivable R"
      apply (auto simp add:Ball_def)
      apply (rule_tac x=m' in exI) apply simp
      apply (drule_tac x=x in spec) apply auto
      apply (rule_tac x=n in exI) apply auto done
    then show ?case by blast
  qed
  then obtain m where "\<forall> p \<in> set ps. \<exists> n\<le>m. (p,n) \<in> derivable R" by blast
  with \<open>r = (ps,c)\<close> and \<open>r \<in> R\<close> have "(c,m+1) \<in> derivable R" using \<open>ps \<noteq> []\<close> and
    derivable.step[where r="(ps,c)" and R=R and m=m] by auto
  then show ?case using \<open>r = (ps,c)\<close> by auto
qed

(* definition of invertible rule and invertible set of rules.  It's a bit nasty, but all it really says is
   If a rule is in the given set, and if any extension of that rule is derivable at n, then the
   premisses of the extended rule are derivable at height at most n.  *)
overloading
  invertible \<equiv> invertible
  invertible_set \<equiv> invertible_set
begin

definition invertible
  where "invertible r R \<equiv>
    \<forall> n S. (r \<in> R \<and> (snd (extendRule S r),n) \<in> derivable R*) \<longrightarrow>
    (\<forall> p \<in> set (fst (extendRule S r)). \<exists> m \<le> n. (p,m) \<in> derivable R*)"

definition invertible_set
  where "invertible_set R \<equiv> \<forall> (ps,c) \<in> R. invertible (ps,c) R"

end


(* Characterisation of a sequent *)
lemma characteriseSeq:
shows "\<exists> A B. (C :: 'a sequent) = (A \<Rightarrow>* B)"
apply (rule_tac x="antec C" in exI, rule_tac x="succ C" in exI) by (cases C) (auto)


(* Helper function for later *)
lemma nonEmptySet:
shows "A \<noteq> [] \<longrightarrow> (\<exists> a. a \<in> set A)"
by (auto simp add:neq_Nil_conv)

(* Lemma which comes in helpful ALL THE TIME *)
lemma midMultiset:
  assumes "\<Gamma> \<oplus> A = \<Gamma>' \<oplus> B" and "A \<noteq> B"
  shows "\<exists> \<Gamma>''. \<Gamma> = \<Gamma>'' \<oplus> B \<and> \<Gamma>' = \<Gamma>'' \<oplus> A"
proof-
  from assms have "A \<in># \<Gamma>'"
      proof-
      from assms have "set_mset (\<Gamma> \<oplus> A) = set_mset (\<Gamma>' \<oplus> B)" by auto
      then have "set_mset \<Gamma> \<union> {A} = set_mset \<Gamma>' \<union> {B}" by auto
      then have "set_mset \<Gamma> \<union> {A} \<subseteq> set_mset \<Gamma>' \<union> {B}" by simp
      then have "A \<in> set_mset \<Gamma>'" using assms by auto
      thus "A \<in># \<Gamma>'" by simp
      qed
  then have "\<Gamma>' \<ominus> A \<oplus> A = \<Gamma>'" by (auto simp add:multiset_eq_iff)
  then have "\<exists> \<Gamma>''. \<Gamma>' = \<Gamma>'' \<oplus> A" apply (rule_tac x="\<Gamma>' \<ominus> A" in exI) by auto
  then obtain \<Gamma>'' where eq1:"\<Gamma>' = \<Gamma>'' \<oplus> A" by blast
  from \<open>\<Gamma> \<oplus> A = \<Gamma>' \<oplus> B\<close> eq1 have "\<Gamma> \<oplus> A = \<Gamma>'' \<oplus> A \<oplus> B" by auto
  then have "\<Gamma> = \<Gamma>'' \<oplus> B" by auto
  thus ?thesis using eq1 by blast
qed

(* Lemma which says that if we have extended an identity rule, then the propositional variable is
   contained in the extended multisets *)
lemma extendID:
assumes "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "At i \<in># \<Gamma> \<and> At i \<in># \<Delta>"
using assms
proof-
  from assms have "\<exists> \<Gamma>' \<Delta>'. \<Gamma> = \<Gamma>' \<oplus> At i \<and> \<Delta> = \<Delta>' \<oplus> At i" 
    using extend_def[where forms=S and seq="\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>"]
    by (rule_tac x="antec S" in exI,rule_tac x="succ S" in exI) auto
  then show ?thesis by auto
qed

lemma extendFalsum:
assumes "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "ff \<in># \<Gamma>"
proof-
  from assms have "\<exists> \<Gamma>'. \<Gamma> = \<Gamma>' \<oplus> ff" 
    using extend_def[where forms=S and seq="\<LM>ff \<RM> \<Rightarrow>* \<Empt>"]
    by (rule_tac x="antec S" in exI) auto
  then show ?thesis by auto
qed


(* Lemma that says if a propositional variable is in both the antecedent and succedent of a sequent,
   then it is derivable from idupRules *)
lemma containID:
assumes a:"At i \<in># \<Gamma> \<and> At i \<in># \<Delta>"
    and b:"Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable R*"
proof-
  from a have "\<Gamma> = \<Gamma> \<ominus> At i \<oplus> At i \<and> \<Delta> = \<Delta> \<ominus> At i \<oplus> At i" by auto
  then have "extend ((\<Gamma> \<ominus> At i) \<Rightarrow>* (\<Delta> \<ominus> At i)) (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)" 
    using extend_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i" and seq="\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>"]
    by auto
  moreover
  have "([],\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) \<in> R" using b by auto
  ultimately
  have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> R*" 
    using extRules.I[where R=R and r="([],  \<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)" and seq="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i"] 
      and extendRule_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i" and R="([],  \<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"] by auto
  then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed

lemma containFalsum:
assumes a: "ff \<in># \<Gamma>"
   and  b: "Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable R*"
proof-
  from a have "\<Gamma> = \<Gamma> \<ominus> ff \<oplus> ff" by auto
  then have "extend (\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>) (\<LM>ff\<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)"
    using extend_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and seq="\<LM>ff\<RM> \<Rightarrow>* \<Empt>"] by auto 
  moreover
  have "([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>) \<in> R" using b by auto
  ultimately have "([],\<Gamma> \<Rightarrow>* \<Delta>) \<in> R*"
    using extRules.I[where R=R and r="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)" and seq="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>"] 
      and extendRule_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* \<Delta>" and R="([],  \<LM>ff\<RM> \<Rightarrow>* \<Empt>)"] by auto
  then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* \<Delta>"] by auto
qed 

(* Lemma which says that if r is an identity rule, then r is of the form
   ([], P \<Rightarrow>* P) *)
lemma characteriseAx:
shows "r \<in> Ax \<Longrightarrow> r = ([],\<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<or> (\<exists> i. r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>))"
  apply (cases r) by (rule Ax.cases) auto

(* A lemma about the last rule used in a derivation, i.e. that one exists *)
lemma characteriseLast:
assumes "(C,m+1) \<in> derivable R"
shows "\<exists> Ps. Ps \<noteq> [] \<and>
             (Ps,C) \<in> R \<and> 
             (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)"
using assms
by (cases) auto


(* Lemma which says that if rule is an upRule, then the succedent is either empty, or a single formula *)
lemma succ_upRule:
assumes "(Ps,\<Phi> \<Rightarrow>* \<Psi>) \<in> upRules"
shows "\<Psi> = \<Empt> \<or> (\<exists> A. \<Psi> = \<LM>A\<RM>)"
using assms 
proof (cases)
    case (I R Rs)
    then show "\<Psi> = \<Empt> \<or> (\<exists> A. \<Psi> = \<LM>A\<RM>)" using mset.simps[where ant=\<Phi> and suc=\<Psi>] 
         and union_is_single[where M=\<Phi> and N=\<Psi> and a="Compound R Rs"] by (simp,elim disjE) (auto)
qed

(* Equivalent, but the antecedent *)
lemma antec_upRule:
assumes "(Ps,\<Phi> \<Rightarrow>* \<Psi>) \<in> upRules"
shows "\<Phi> = \<Empt> \<or> (\<exists> A. \<Phi> = \<LM>A\<RM>)"
using assms 
proof (cases)
    case (I R Rs)
    then show "\<Phi> = \<Empt> \<or> (\<exists> A. \<Phi> = \<LM>A\<RM>)" using mset.simps[where ant=\<Phi> and suc=\<Psi>] 
         and union_is_single[where M=\<Phi> and N=\<Psi> and a="Compound R Rs"] by (simp,elim disjE) (auto)
qed

lemma upRule_Size:
assumes "r \<in> upRules"
shows "seq_size (snd r) = 1"
using assms
proof-
    obtain Ps C where "r = (Ps,C)" by (cases r)
    then have "(Ps,C) \<in> upRules" using assms by simp
    then show ?thesis
       proof (cases)
          case (I R Rs)
          obtain G H where "C = (G \<Rightarrow>* H)" by (cases C) (auto)
          then have "G + H = \<LM>Compound R Rs\<RM>" using mset.simps and \<open>mset C \<equiv> \<LM>Compound R Rs\<RM>\<close> by auto
          then have "size (G+H) = 1" by auto 
          then have "size G + size H = 1" by auto
          then have "seq_size C = 1" using seq_size.simps[where ant=G and suc=H] and \<open>C = (G \<Rightarrow>* H)\<close> by auto
          moreover have "snd r = C" using \<open>r = (Ps,C)\<close> by simp
          ultimately show "seq_size (snd r) = 1" by simp
       qed
qed

lemma upRuleCharacterise:
assumes "(Ps,C) \<in> upRules"
shows "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)"
using assms
proof (cases)
  case (I F Fs)
  then obtain \<Gamma> \<Delta> where "C = (\<Gamma> \<Rightarrow>* \<Delta>)" using characteriseSeq[where C=C] by auto
  then have "(Ps,\<Gamma> \<Rightarrow>* \<Delta>) \<in> upRules" using assms by simp
  then show "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" 
    using \<open>mset C \<equiv> \<LM>Compound F Fs\<RM>\<close> and \<open>C = (\<Gamma> \<Rightarrow>* \<Delta>)\<close>
      and mset.simps[where ant=\<Gamma> and suc=\<Delta>] and union_is_single[where M=\<Gamma> and N=\<Delta> and a="Compound F Fs"]
    by auto
qed

lemma extendEmpty:
shows "extend (\<Empt> \<Rightarrow>* \<Empt>) C = C"
apply (auto simp add:extend_def) by (cases C) auto

lemma extendContain:
assumes "r = (ps,c)"
    and "(Ps,C) = extendRule S r"
    and "p \<in> set ps"
shows "extend S p \<in> set Ps"
proof-
from \<open>p \<in> set ps\<close> have "extend S p \<in> set (map (extend S) ps)" by auto
moreover from \<open>(Ps,C) = extendRule S r\<close> and \<open>r = (ps,c)\<close> have "map (extend S) ps = Ps" by (simp add:extendRule_def) 
ultimately show ?thesis by auto
qed

lemma nonPrincipalID:
fixes A :: "'a form"
assumes "r \<in> Ax"
shows "\<not> rightPrincipal r A \<and> \<not> leftPrincipal r A"
proof-
from assms obtain i where r1:"r = ([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<or> r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i\<RM>)" 
     using characteriseAx[where r=r] by auto
{ assume "rightPrincipal r A" then obtain Ps where r2:"r = (Ps, \<Empt> \<Rightarrow>* \<LM> A \<RM>)" by (cases r) auto
  with r1 have "False" by simp
}
then have "\<not> rightPrincipal r A" by auto
moreover
{ assume "leftPrincipal r A" then obtain Ps' F Fs where r3:"r = (Ps', \<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" by (cases r) auto
  with r1 have "False" by auto
}
then have "\<not> leftPrincipal r A" by auto
ultimately show ?thesis by simp
qed

lemma extendCommute:
shows "(extend S) (extend R c) = (extend R) (extend S c)"
by (auto simp add:extend_def union_ac)

lemma mapCommute:
shows "map (extend S) (map (extend R) c) = map (extend R) (map (extend S) c)"
by (induct_tac c) (auto simp add:extendCommute)

lemma extendAssoc:
shows "(extend S) (extend R c) = extend (extend S R) c" 
by (auto simp add:extend_def union_ac)

lemma mapAssoc:
shows "map (extend S) (map (extend R) c) = map (extend (extend S R)) c"
by (induct_tac c) (auto simp add:extendAssoc)

lemma extended_Ax_prems_empty:
assumes "r \<in> Ax"
shows "fst (extendRule S r) = []"
using assms apply (cases r) by (rule Ax.cases) (auto simp add:extendRule_def)

inductive lastRule :: "'a deriv \<Rightarrow> 'a rule \<Rightarrow> 'a rule set \<Rightarrow> bool"
  where
  base[intro]: "\<lbrakk> r \<in> Ax; Ax \<subseteq> R ; snd (extendRule S r) = (\<Gamma> \<Rightarrow>* \<Delta>)\<rbrakk>
                 \<Longrightarrow> lastRule (\<Gamma> \<Rightarrow>* \<Delta>,0) r R"
|    I[intro]:  "\<lbrakk> r\<in>R ; r \<notin> Ax ; snd (extendRule S r) = (\<Gamma> \<Rightarrow>* \<Delta>) ; 
                \<forall> p \<in> set (fst (extendRule S r)). \<exists> m\<le>n. (p,m) \<in> derivable R* \<rbrakk> 
                 \<Longrightarrow> lastRule (\<Gamma> \<Rightarrow>* \<Delta>,n+1) r R" 

lemma obv:
fixes a :: "('a * 'b)"
shows "a = (fst a, snd a)" by auto

lemma getLast:
assumes "lastRule (\<Gamma> \<Rightarrow>* \<Delta>,n+1) r R"
shows "\<exists> S Ps. extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>) \<and> (\<forall> p \<in> set Ps. \<exists> m\<le>n. (p,m) \<in> derivable R*) \<and> r \<in> R \<and> r \<notin> Ax"
proof-
  from assms show ?thesis apply (rule lastRule.cases) apply simp apply simp
  apply (rule_tac x=S in exI) apply (rule_tac x="fst (extendRule S r)" in exI) apply simp
  apply auto
  apply (subgoal_tac "extendRule S (a,b) = (fst (extendRule S (a,b)),snd (extendRule S (a,b)))")
  apply simp by (rule obv)
qed

lemma getAx:
assumes "lastRule (\<Gamma> \<Rightarrow>* \<Delta>,0) r R"
shows "r \<in> Ax \<and> (\<exists> S. extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta>))"
proof-
  from assms have "r \<in> Ax \<and> (\<exists> S. snd (extendRule S r) = (\<Gamma> \<Rightarrow>* \<Delta>))"
       by (rule lastRule.cases) auto
  then obtain S where "r \<in> Ax" and "snd (extendRule S r) = (\<Gamma> \<Rightarrow>* \<Delta>)" by auto
  from \<open>r \<in> Ax\<close> have "fst r = []" apply (cases r) by (rule Ax.cases) auto
  then have "fst (extendRule S r) = []" by (auto simp add:extendRule_def)
  with \<open>snd (extendRule S r) = (\<Gamma> \<Rightarrow>* \<Delta>)\<close> and \<open>r \<in> Ax\<close> show ?thesis apply auto
       apply (rule_tac x=S in exI) 
       apply (subgoal_tac "extendRule S r = (fst (extendRule S r),snd (extendRule S r))") apply simp
       by (rule obv)
qed


(* Has the usual set-up: takes a subset of the upRules, combines with all the axioms, blah blah *)


(* Constructing the rule set we will use.  It contains all axioms, but only a subset
   of the possible logical rules. *)
lemma ruleSet:
assumes "R' \<subseteq> upRules"
    and "R = Ax \<union> R'"
    and "(Ps,C) \<in> R*"
shows "\<exists> S r. extendRule S r = (Ps,C) \<and> (r \<in> R' \<or> r \<in> Ax)"
proof-
from \<open>(Ps,C) \<in> R*\<close> have "\<exists> S r. extendRule S r = (Ps,C) \<and> r \<in> R" by (cases) auto
then obtain S r where "(Ps,C) = extendRule S r" and "r \<in> R" apply auto 
                by (drule_tac x=S in meta_spec,drule_tac x=a in meta_spec, drule_tac x=b in meta_spec) auto
moreover from \<open>r \<in> R\<close> and \<open>R = Ax \<union> R'\<close> have "r \<in> Ax \<or> r \<in> R'" by blast
ultimately show ?thesis by (rule_tac x=S in exI,rule_tac x=r in exI) (auto)
qed

lemma dpWeak:
assumes a:"(\<Gamma> \<Rightarrow>* \<Delta>,n) \<in> derivable R*"
   and  b: "R' \<subseteq> upRules"
   and  c: "R = Ax \<union> R'" 
shows "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n) \<in> derivable R*"
using a
proof (induct n arbitrary: \<Gamma> \<Delta> rule:nat_less_induct)
case (1 n \<Gamma> \<Delta>)
then have IH: "\<forall>m<n. \<forall> \<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta>, m) \<in> derivable R* \<longrightarrow> ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m) \<in> derivable R*" 
      and a': "( \<Gamma> \<Rightarrow>* \<Delta>, n) \<in> derivable R*" by auto
show ?case
proof (cases n)
case 0
 then have "(\<Gamma> \<Rightarrow>* \<Delta>,0) \<in> derivable R*" using a' by simp
 then have "([], \<Gamma> \<Rightarrow>* \<Delta>) \<in> R*" by (cases) auto
 then obtain  r S where "r \<in> R" and split:"extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta>)" 
      by (rule extRules.cases) auto
 then obtain c where "r = ([],c)" by (cases r) (auto simp add:extendRule_def)
 with \<open>r \<in> R\<close> have "r \<in> Ax \<or> r \<in> upRules" using b c by auto
 with \<open>r = ([],c)\<close> have "r \<in> Ax" by (auto) (rule upRules.cases,auto)                                 
 with \<open>r = ([],c)\<close> obtain i where "c = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>) \<or> c = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
      using characteriseAx[where r=r] by auto
 moreover
    {assume "c = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>)"
     then have "extend S (\<LM>At i\<RM> \<Rightarrow>*\<LM>At i\<RM>) = (\<Gamma> \<Rightarrow>* \<Delta>)" using split and \<open>r = ([],c)\<close>
          by (auto simp add:extendRule_def)
     then have "At i \<in># \<Gamma> \<and> At i \<in># \<Delta>" using extendID by auto
     then have "At i \<in># \<Gamma> + \<Gamma>' \<and> At i \<in># \<Delta> + \<Delta>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" 
          using c and containID[where \<Gamma>="\<Gamma>+\<Gamma>'" and \<Delta>="\<Delta>+\<Delta>'" and R=R and i=i] by auto
    }
 moreover
    {assume "c = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
     then have "extend S (\<LM>ff\<RM> \<Rightarrow>*\<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta>)" using split and \<open>r = ([],c)\<close>
          by (auto simp add:extendRule_def)
     then have "ff \<in># \<Gamma>" using extendFalsum by auto
     then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" 
          using c and containFalsum[where \<Gamma>="\<Gamma>+\<Gamma>'" and \<Delta>="\<Delta>+\<Delta>'" and R=R] by auto
    }
 ultimately show "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n) \<in> derivable R*" using \<open>n=0\<close> by auto
next
case (Suc n')
 then have "(\<Gamma> \<Rightarrow>* \<Delta>, n'+1) \<in> derivable R*" using a' by simp
 then obtain Ps where f:"Ps \<noteq> []"
                  and g:"(Ps, \<Gamma> \<Rightarrow>* \<Delta>) \<in> R*" 
                  and h:"\<forall> p \<in> set Ps. \<exists> m\<le>n'. (p,m) \<in> derivable R*" 
      using characteriseLast[where C="\<Gamma> \<Rightarrow>* \<Delta>" and m=n' and R="R*"] by auto
 from g c obtain S r where "r \<in> R" and "(r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>)" by (cases) auto
 with b have as: "(r \<in> Ax \<or> r \<in> upRules) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta>)" by auto
 then have eq:"map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps = fst (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
       using mapCommute[where S="\<Gamma>'\<Rightarrow>*\<Delta>'" and R=S and c="fst r"]
       by (auto simp add:extendRule_def extend_def mapAssoc simp del: map_map)
 from as have eq2: "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') = snd (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)"
       by (auto simp add:extendRule_def extend_def union_ac)
 from as f have "fst r \<noteq> []" by (auto simp add:extendRule_def map_is_Nil_conv)
 with as have "r \<in> upRules" apply (cases r,auto) by (rule Ax.cases) auto
 have "\<forall> p' \<in> set (map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps). \<exists> m\<le>n'. (p',m) \<in> derivable R*"
      proof-
      {fix p
       assume "p \<in> set (map (extend (\<Gamma>' \<Rightarrow>* \<Delta>')) Ps)"
       then obtain p' where t:"p' \<in> set Ps \<and> p = extend (\<Gamma>' \<Rightarrow>* \<Delta>') p'" by auto
       with h obtain m where "m\<le>n'" and "(p',m) \<in> derivable R*" by auto
       moreover obtain \<Phi> \<Psi> where eq:"p' = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases p') auto 
       then have "p = (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')" using t by (auto simp add:extend_def union_ac)
       ultimately have "(p,m) \<in> derivable R*" using IH and \<open>n = Suc n'\<close> and eq
            apply- by (drule_tac x=m in spec) simp
       then have "\<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>m\<le>n'\<close> by auto
       }
       then show ?thesis by auto
       qed
 then have "\<forall> p' \<in> set (fst (extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r)).
            \<exists> m\<le>n'. (p',m) \<in> derivable R*" using eq by auto
 moreover have "extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r \<in> R*" 
          using \<open>r \<in> upRules\<close> and \<open>r \<in> R\<close> by auto
 ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',n'+1) \<in> derivable R*"
          using derivable.step[where r="extendRule (extend S (\<Gamma>' \<Rightarrow>* \<Delta>')) r" and R="R*" and m="n'"]
          and \<open>fst r \<noteq> []\<close> and eq2 by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
 then show "( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', n) \<in> derivable R*" using \<open>n = Suc n'\<close> by auto
 qed
qed
(*>*)
text\<open>
\section{Manipulating Rule Sets \label{isaSRC}}
The removal of superfluous and redundant rules \cite{AL01} will not be harmful to invertibility: removing rules means that the conditions of earlier sections are more likely to be fulfilled.  Here, we formalise the results that the removal of such rules from a calculus $\mathcal{L}$ will create a new calculus $\mathcal{L}'$ which is equivalent.  In other words, if a sequent is derivable in $\mathcal{L}$, then it is derivable in $\mathcal{L}'$.
The results formalised in this section are for \SC multisuccedent calculi.

When dealing with lists of premisses, a rule $R$ with premisses $P$ will be redundant given a rule $R'$ with premisses $P'$ if there exists some $p$ such that $P = p \# P'$.  There are other ways in which a rule could be redundant; say if $P = Q @ P'$, or if $P = P' @ Q$, and so on.  The order of the premisses is not really important, since the formalisation operates on the finite set based upon the list.  The more general ``append'' lemma could be proved from the lemma we give; we prove the inductive step case in the proof of such an append lemma.  This is a height preserving transformation.  Some of the proof is shown:
\<close>

lemma removeRedundant:
assumes (*<*)a:(*>*) "r1 = (p#ps,c) \<and> r1 \<in> upRules"
and     (*<*)b:(*>*) "r2 = (ps,c) \<and> r2 \<in> upRules"
and     (*<*)c:(*>*) "R1 \<subseteq> upRules \<and> R = Ax \<union> R1"
and     (*<*)d:(*>*) "(T,n) \<in> derivable (R \<union> {r1} \<union> {r2})*"
shows   "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*"
 (*<*)
using assms (*>*)
proof (induct n (*<*)arbitrary: T (*>*)rule:nat_less_induct)
 (*<*)case (1 n T)
    then have IH: " \<forall>m<n. \<forall> x. (r1 = (p # ps, c) \<and> r1 \<in> upRules \<longrightarrow>
                         r2 = (ps, c) \<and> r2 \<in> upRules \<longrightarrow>
                         R1 \<subseteq> upRules \<and> R = Ax \<union> R1 \<longrightarrow> 
                         (x, m) \<in> derivable (R \<union> {r1} \<union> {r2})* \<longrightarrow> 
                         (\<exists> m'\<le>m. (x, m') \<in> derivable (R \<union> {r2})*))" and
             prm: "(T,n) \<in> derivable (R \<union> {r1} \<union> {r2})*" by auto
    show ?case
 proof (cases n) (*>*)
 case 0
  (*<*) with prm (*>*) have "(T,0) \<in> derivable (R \<union> {r1} \<union> {r2})*" by simp
   then have "([],T) \<in> (R \<union> {r1} \<union> {r2})*" by (cases) auto
   then obtain S r where ext: "extendRule S r = ([],T)" and 
        "r \<in> (R \<union> {r1} \<union> {r2})" by (rule extRules.cases) auto
   then have "r \<in> R \<or> r = r1 \<or> r = r2" using c by auto
txt\<open>\noindent It cannot be the case that $r=r_{1}$ or $r=r_{2}$, since those are \SC rules, whereas anything with an empty set of premisses
must be an axiom.  Since $\mathcal{R}$ contains the set of axioms, so will $\mathcal{R} \cup r_{2}$:\<close>
 (*<*)   moreover from ext obtain d where "r = ([],d)" by (cases r) (auto simp add:extendRule_def) 
   ultimately have "r \<in> R \<or> r = r2" using c a ext by (auto simp add:extendRule_def) (*>*)
   then have "r \<in> (R \<union> {r2})" using c by auto
 (*<*)  then have "([],T) \<in> (R \<union> {r2})*" using \<open>extendRule S r = ([],T)\<close> 
          and extRules.I[where r=r and R="R \<union> {r2}" and seq=S] by auto (*>*)
  then have "(T,0) \<in> derivable (R \<union> {r2})*" by auto
  then show "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*" using \<open>n=0\<close> by auto
next
 case (Suc n')
 (*<*) with prm (*>*)have "(T,n'+1) \<in> derivable (R \<union> {r1} \<union> {r2})*" by simp
  then obtain Ps where e: "Ps \<noteq> []"
         and   f: "(Ps,T) \<in> (R \<union> {r1} \<union> {r2})*"
         and   g: "\<forall> P \<in> set Ps. \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r1} \<union> {r2})*"
        (*<*) using characteriseLast[where C=T and m=n' and R="(R \<union> {r1} \<union> {r2})*"](*>*) by auto
  have g': "\<forall> P \<in> set Ps. \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r2})*"
  (*<*)       proof-
              {fix P
               assume "P \<in> set Ps"
               with g obtain m where "(P,m) \<in> derivable (R \<union> {r1} \<union> {r2})*" and "m\<le>n'" by auto
               with IH have "\<exists> m'\<le>m. (P,m') \<in> derivable (R \<union> {r2})*" using a b c and \<open>n = Suc n'\<close>
                    by auto
               then have "\<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r2})*" using \<open>m\<le>n'\<close> apply auto 
                    by (rule_tac x=m' in exI) auto
              } 
              then show ?thesis by auto
         qed  (*>*)             
   from f obtain S r where ext: "extendRule S r = (Ps,T)"
        and "r \<in> (R \<union> {r1} \<union> {r2})" by (rule extRules.cases) auto
    then have "r \<in> (R \<union> {r2}) \<or> r = r1" by auto
txt\<open>\noindent Either $r$ is in the new rule set or $r$ is the redundant rule.  In the former case, there is nothing to do:\<close>
 (*<*)moreover
    {(*>*) assume "r \<in> (R \<union> {r2})"
     then have "(Ps,T) \<in> (R \<union> {r2})*" (*<*)using ext and extRules.I[where r=r and R="R \<union> {r2}" and seq=S](*>*) by auto
     with g' have "(T,n) \<in> derivable (R \<union> {r2})*" using \<open>n = Suc n'\<close> (*<*)and e and
       derivable.step[where r="(Ps,T)" and R="(R \<union> {r2})*" and m=n'](*>*) by auto
   (*<*) }
 moreover 
    { (*>*)
txt\<open>\noindent In the latter case, the last inference was redundant.  Therefore the premisses, which are derivable at a lower height than the conclusion, 
contain the premisses of $r_{2}$ (these premisses are \texttt{extend S ps}).  This completes the proof:\<close>
     assume "r = r1" 
     with ext have "map (extend S) (p # ps) = Ps" using a by (auto(*<*) simp add:extendRule_def(*>*))
     then have "\<forall> P \<in> set (map (extend S) (p#ps)). 
                   \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r2})*"
         using g' by simp
     then have h: "\<forall> P \<in> set (map (extend S) ps). 
                      \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r2})*" by auto

 (*<*)    have "extendRule S r2 = (map (extend S) ps, T)" using b and a and ext and \<open>r = r1\<close> 
           by (auto simp add:extendRule_def)
     then have i: "(map (extend S) ps,T) \<in> (R \<union> {r2})*" using extRules.I(*<*)[where r=r2 and R="(R \<union> {r2})" and seq=S](*>*)
               by auto
    have "ps = [] \<or> ps \<noteq> []" by blast
   moreover
       {assume "ps = []"
         with i have "([],T) \<in> (R \<union> {r2})*" by auto
         then have "(T,0) \<in> derivable (R \<union> {r2})*" by auto
         then have "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*" by auto
       }
       moreover
          {assume "ps \<noteq> []"
           then have "map (extend S) ps \<noteq> []" by auto
            with i and h have "(T,n'+1) \<in> derivable (R \<union> {r2})*" 
                  using derivable.step[where r="(map (extend S) ps,T)" and R="(R \<union> {r2})*" and m=n'] by auto
           with \<open>n = Suc n'\<close> have "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*" by auto
           }
       ultimately have "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*" by blast
     }
  ultimately show "\<exists> m\<le>n. (T,m) \<in> derivable (R \<union> {r2})*" by blast
  qed
qed(*>*)
text\<open>
\noindent Recall that to remove superfluous rules, we must know that Cut is admissible in the original calculus \cite{AL01}.  Again, we add the two distinguished premisses at the head of the premiss list; general results about permutation of lists will achieve a more general result.  Since one uses Cut in the proof, this will in general not be height-preserving:
\<close>

lemma removeSuperfluous:
assumes (*<*)a:(*>*) "r1 = ((\<Empt> \<Rightarrow>* \<LM>A\<RM>) # ((\<LM>A\<RM> \<Rightarrow>* \<Empt>) # ps),c) \<and> r1 \<in> upRules"
and     (*<*)b:(*>*) "R1 \<subseteq> upRules \<and> R = Ax \<union> R1"
and     "(T,n) \<in> derivable (R \<union> {r1})*"
and     CA: "\<forall> \<Gamma> \<Delta> A. ((\<Gamma> \<Rightarrow>* \<Delta> \<oplus> A) \<in> derivable' R* \<longrightarrow> 
             (\<Gamma> \<oplus> A \<Rightarrow>* \<Delta>) \<in> derivable' R*) \<longrightarrow>
             (\<Gamma> \<Rightarrow>* \<Delta>) \<in> derivable' R*"
shows   "T \<in> derivable' R*"
(*<*)
using assms
proof (induct n arbitrary: T rule: nat_less_induct)
  case (1 n T)
  then have IH: "\<forall>m<n. r1 = (( \<Empt> \<Rightarrow>* \<LM>A\<RM>) # ( \<LM>A\<RM> \<Rightarrow>* \<Empt>) # ps, c) \<and> r1 \<in> upRules \<longrightarrow>
    R1 \<subseteq> upRules \<and> R = Ax \<union> R1 \<longrightarrow>
    (\<forall> T. (T, m) \<in> derivable (R \<union> {r1})* \<longrightarrow>
    (\<forall> \<Gamma> \<Delta> B.
    ((\<Gamma> \<Rightarrow>* \<Delta> \<oplus> B) \<in> derivable' R* \<longrightarrow> (\<Gamma> \<oplus> B \<Rightarrow>* \<Delta>) \<in> derivable' R*) \<longrightarrow> 
    (\<Gamma> \<Rightarrow>* \<Delta>) \<in> derivable' R*) \<longrightarrow>
    T \<in> derivable' R*)" by blast
  from 1 have prm: "(T,n) \<in> derivable (R \<union> {r1})*" by blast
  show ?case
  proof (cases n)
    case 0
    with prm have "(T,0) \<in> derivable (R \<union> {r1})*" by simp
    then have "([],T) \<in> (R \<union> {r1})*" by (rule derivable.cases) auto
    then obtain S r where ext: "extendRule S r = ([],T)" and "r \<in> (R \<union> {r1})" by (rule extRules.cases) auto
    then have "r \<in> R \<or> r = r1" by auto
    with a have "r \<in> R" using ext by (auto simp add:extendRule_def)
    then have "([],T) \<in> R*" using ext and extRules.I[where r=r and R=R and seq=S] by auto
    then show "T \<in> derivable' R*" by auto
  next
    case (Suc n')
    with prm have prm': "(T,n'+1) \<in> derivable (R \<union> {r1})*" by auto
    then obtain Ps where ne: "Ps \<noteq> []"
      and   ex: "(Ps,T) \<in> (R \<union> {r1})*"
      and   "\<forall> P \<in> set Ps. \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r1})*"
      using characteriseLast[where C=T and m=n' and R="(R \<union> {r1})*"] by auto
    with IH have e: "\<forall> P \<in> set Ps. P \<in> derivable' R*" using a b and prm' and \<open>n = Suc n'\<close>
      apply (auto simp only:Ball_def) apply (drule_tac x=x in spec) apply auto
      apply (drule_tac x=m in spec) apply auto apply (drule_tac x=x in spec) apply simp
      apply (insert CA[simplified]) apply (subgoal_tac "R = Ax \<union> R1") apply blast apply (insert b) by blast
    from ex obtain S r where ext: "extendRule S r = (Ps,T)" and "r \<in> (R \<union> {r1})" by (rule extRules.cases) auto
    then have "r \<in> R \<or> r = r1" by blast
    moreover
    {assume "r \<in> R"
      with ext have "(Ps,T) \<in> R*" using extRules.I[where r=r and R=R and seq=S] by auto
      with e have "T \<in> derivable' R*" using ne and
        derivable'.step[where r="(Ps,T)" and R="R*"] by auto
    }
    moreover
    {assume "r = r1"
      with e and a and ext have "(extend S (\<LM>A\<RM> \<Rightarrow>* \<Empt>)) \<in> derivable' R*"
        and  "(extend S (\<Empt> \<Rightarrow>* \<LM>A\<RM>)) \<in> derivable' R*"
        by (auto simp add:extendRule_def)
      then have "S \<in> derivable' R*" using CA apply-
        apply (drule_tac x="antec S" in spec) apply (drule_tac x="succ S" in spec) apply (drule_tac x=A in spec)
        apply (simp add:extend_def) by (cases S) auto
      then obtain s where "(S,s) \<in> derivable R*" using deriv_to_deriv2 by auto
      then have "(extend S c,s) \<in> derivable R*" 
        using dpWeak[where R=R and R'=R1 and \<Gamma>="antec S" and \<Delta>="succ S"
          and \<Gamma>'="antec c" and \<Delta>'="succ c" and n=s] and b
        apply (auto simp add:extend_def union_ac) by (cases S) auto
      with ext have "(T,s) \<in> derivable R*" using \<open>r = r1\<close> and a by (auto simp add:extendRule_def)
      then have "T \<in> derivable' R*" by auto
    }
    ultimately show "T \<in> derivable' R*" by blast
  qed
qed
(*>*)

text\<open>
\noindent \textit{Combinable rules} can also be removed.  We encapsulate the combinable criterion by saying that if $(p \# P,T)$ and $(q \# P, T)$ are rules in a calculus, then we get an equivalent calculus by replacing these two rules by $((\textrm{extend } p \ q) \# P, T)$.  Since the \texttt{extend} function is commutative, the order of $p$ and $q$ in the new rule is not important.  This transformation is height preserving:
\<close>

lemma removeCombinable:
assumes a: "r1 = (p # ps,c) \<and> r1 \<in> upRules"
and     b: "r2 = (q # ps,c) \<and> r2 \<in> upRules"
and     c: "r3 = (extend p q # ps, c) \<and> r3 \<in> upRules"
and     d: "R1 \<subseteq> upRules \<and> R = Ax \<union> R1"
and     "(T,n) \<in> derivable (R \<union> {r1} \<union> {r2})*"
shows   "(T,n) \<in> derivable (R \<union> {r3})*"
(*<*)
using assms
proof (induct n arbitrary:T rule:nat_less_induct)
case (1 n T)
    then have IH: "\<forall>m<n. \<forall> T. (r1 = (p # ps, c) \<and> r1 \<in> upRules \<longrightarrow>
                               r2 = (q # ps, c) \<and> r2 \<in> upRules \<longrightarrow>
                               r3 = (extend p q # ps, c) \<and> r3 \<in> upRules \<longrightarrow>
                               R1 \<subseteq> upRules \<and> R = Ax \<union> R1 \<longrightarrow> 
                              (T, m) \<in> derivable (R \<union> {r1} \<union> {r2})* \<longrightarrow> 
                              (T, m) \<in> derivable (R \<union> {r3})*)" and
             prm: "(T, n) \<in> derivable (R \<union> {r1} \<union> {r2})*" by auto
    show ?case
    proof (cases n)
    case 0
        with prm have "(T,0) \<in> derivable (R \<union> {r1} \<union> {r2})*" by simp
        then have "([],T) \<in> (R \<union> {r1} \<union> {r2})*" by (rule derivable.cases) auto
        then obtain S r where ext: "extendRule S r = ([],T)" and "r \<in> (R \<union> {r1} \<union> {r2})" by (rule extRules.cases) auto
        then have "r \<in> R \<or> r = r1 \<or> r = r2" by blast
        with ext and a and b have "r \<in> R" by (auto simp add:extendRule_def)
        then have "r \<in> (R \<union> {r3})" by simp
        with ext have "([],T) \<in> (R \<union> {r3})*" using extRules.I[where r=r and R="R \<union> {r3}" and seq=S] by auto
        then have "(T,0) \<in> derivable (R \<union> {r3})*" by auto
        then show "(T,n) \<in> derivable (R \<union> {r3})*" using \<open>n=0\<close> by auto
    next
    case (Suc n')
        with prm have prm': "(T,n'+1) \<in> derivable (R \<union> {r1} \<union> {r2})*" by simp
        then obtain Ps where ne: "Ps \<noteq> []"
                       and   ex: "(Ps,T) \<in> (R \<union> {r1} \<union> {r2})*"
                       and   "\<forall> P \<in> set Ps. \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r1} \<union> {r2})*"
             using characteriseLast[where C=T and m=n' and R="(R \<union> {r1} \<union> {r2})*"] by auto
        with IH have e: "\<forall> P \<in> set Ps. \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*" using a b c d and prm' and \<open>n = Suc n'\<close>
             apply (auto simp add:Ball_def) by (drule_tac x=x in spec) auto
        from ex obtain S r where ext: "extendRule S r = (Ps,T)" and "r \<in> (R \<union> {r1} \<union> {r2})" by (rule extRules.cases) auto
        then have "r \<in> R \<or> r = r1 \<or> r = r2" by blast
        moreover
           {assume "r \<in> R"
            then have "r \<in> (R \<union> {r3})" by simp
            with ext have "(Ps,T) \<in> (R \<union> {r3})*" using extRules.I[where r=r and R="R \<union> {r3}" and seq=S] by auto
            with e have "(T,n'+1) \<in> derivable (R \<union> {r3})*" using ne and
                 derivable.step[where r="(Ps,T)" and R="(R \<union> {r3})*" and m=n'] by auto
           }
        moreover
           {assume "r = r1"
            with e and a and ext have "\<exists> m\<le>n'. (extend S p,m) \<in> derivable (R \<union> {r3})*"
                 by (auto simp add:extendRule_def)
            then have "\<exists> m\<le>n'. (extend S (extend q p),m) \<in> derivable (R \<union> {r3})*" 
                 using dpWeak[where R="R \<union> {r3}" and R'="R1 \<union> {r3}" and \<Gamma>="antec S + antec p" and \<Delta>="succ S + succ p"
                              and \<Gamma>'="antec q" and \<Delta>'="succ q"] and d c by (auto simp add:extend_def union_ac)
            moreover from e and ext and \<open>r = r1\<close> and a
                 have "\<forall> P \<in> set (map (extend S) ps). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 by (auto simp add:extendRule_def)
            ultimately have "\<forall> P \<in> set (map (extend S) (extend q p # ps)). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 by auto
            moreover have "extend q p = extend p q" by (auto simp add:extend_def union_ac)
            ultimately have pm: "\<forall> P \<in> set (fst (extendRule S r3)). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 using c by (auto simp add:extendRule_def)
            from ext and a and c and \<open>r = r1\<close> have con: "snd (extendRule S r3) = T" by (auto simp add:extendRule_def)
            have "r3 \<in> (R \<union> {r3})" by simp
            then have "extendRule S r3 \<in> (R \<union> {r3})*" by auto
            with pm and con and c have "(T,n'+1) \<in> derivable (R \<union> {r3})*"
                 using derivable.step[where r="extendRule S r3" and R="(R \<union> {r3})*" and m=n']
                 by (auto simp add:extendRule_def)
           }
        moreover
           {assume "r = r2"
            with e and b and ext have "\<exists> m\<le>n'. (extend S q,m) \<in> derivable (R \<union> {r3})*"
                 by (auto simp add:extendRule_def)
            then have "\<exists> m\<le>n'. (extend S (extend p q),m) \<in> derivable (R \<union> {r3})*" 
                 using dpWeak[where R="R \<union> {r3}" and R'="R1 \<union> {r3}" and \<Gamma>="antec S + antec q" and \<Delta>="succ S + succ q"
                              and \<Gamma>'="antec p" and \<Delta>'="succ p"] and d c by (auto simp add:extend_def union_ac)
            moreover from e and ext and \<open>r = r2\<close> and b
                 have "\<forall> P \<in> set (map (extend S) ps). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 by (auto simp add:extendRule_def)
            ultimately have "\<forall> P \<in> set (map (extend S) (extend p q # ps)). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 by auto
            then have pm: "\<forall> P \<in> set (fst (extendRule S r3)). \<exists> m\<le>n'. (P,m) \<in> derivable (R \<union> {r3})*"
                 using c by (auto simp add:extendRule_def)
            from ext and b and c and \<open>r = r2\<close> have con: "snd (extendRule S r3) = T" by (auto simp add:extendRule_def)
            have "r3 \<in> (R \<union> {r3})" by simp
            then have "extendRule S r3 \<in> (R \<union> {r3})*" by auto
            with pm and con and c have "(T,n'+1) \<in> derivable (R \<union> {r3})*"
                 using derivable.step[where r="extendRule S r3" and R="(R \<union> {r3})*" and m=n']
                 by (auto simp add:extendRule_def)
           }
        ultimately show "(T,n) \<in> derivable (R \<union> {r3})*" using \<open>n = Suc n'\<close> by auto
    qed
qed
(*>*)
text\<open>
\section{Conclusions}

Only a portion of the formalisation was shown; a variety of intermediate lemmata were not made explicit.  This was necessary, for the \textit{Isabelle} theory files run to almost 8000 lines.  However, these files do not have to be replicated for each new calculus.  It takes very little effort to define a new calculus.  Furthermore, proving invertibility is now a quick process; less than 25 lines of proof in most cases.  
\<close>
(*<*)
end(*>*)
