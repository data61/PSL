(*<*)
(*  Author : Peter Chapman *)
(* License: LGPL *)
section "Single Succedent"

theory SingleSuccedent
imports "HOL-Library.Multiset"
begin

(* Has the empty formula O, which will mean we can have empty right-hand sides *)
(*>*)

text\<open>
\section{Single Succedent Calculi \label{isasingle}}
We must be careful when restricting sequents to single succedents.  If we have sequents as a pair of multisets, where the second is restricted to having size at most 1, then how does one extend the active part of $\implies{L}{}$ from \textbf{G3ip}?  The left premiss will be $\implies{A}{B} \Rightarrow A$, and the extension will be $\Gamma \Rightarrow C$.  The \texttt{extend} function must be able to correctly choose to discard the $C$.  

Rather than taking this route, we instead restrict to single formulae in the succedents of sequents.  This raises its own problems, since now how does one represent the empty succedent?  We introduce a dummy formula \texttt{Em}, which will stand for the empty formula:
\<close>

datatype 'a form = At "nat"
                        | Compound "'a" "'a form list"
                        | ff
                        | Em
(*<*)
abbreviation multiset_abbrev ("\<LM> _  \<RM>" [75]75) where
   "\<LM> A \<RM> \<equiv> {# A #}"

abbreviation multiset_empty ("\<Empt>" 75) where
  "\<Empt> \<equiv> {#}"

datatype 'a sequent = Sequent "('a form) multiset" "('a form)" (" (_) \<Rightarrow>* (_)" [6,6] 5)

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
primrec succ :: "'a sequent \<Rightarrow> 'a form" where "succ (Sequent ant suc) = suc"
primrec mset :: "'a sequent \<Rightarrow> 'a form multiset" where "mset (Sequent ant suc) = ant \<oplus> suc"
primrec seq_size :: "'a sequent \<Rightarrow> nat" where "seq_size (Sequent ant suc) = size ant + size suc"

(* Extend a sequent, and then a rule by adding seq to all premisses and the conclusion *)

(*>*)
text\<open>
\noindent When we come to extend a sequent, say $\Gamma \Rightarrow C$, with another sequent, say $\Gamma' \Rightarrow C'$, we only ``overwrite'' the succedent if $C$ is the empty formula:
\<close>
overloading
  extend \<equiv> extend
  extendRule \<equiv> extendRule
begin

definition extend
  where "extend forms seq \<equiv>
    if (succ seq = Em) 
    then (antec forms + antec seq) \<Rightarrow>* (succ forms) 
    else (antec forms + antec seq \<Rightarrow>* succ seq)"

definition extendRule
  where "extendRule forms R \<equiv> (map (extend forms) (fst R), extend forms (snd R))"

end

(*<*)
(* The formulation of various rule sets *)

(* Ax is the set containing all identity RULES and LBot *)
inductive_set "Ax" where
   id[intro]: "([], \<LM> At i \<RM> \<Rightarrow>* At i) \<in> Ax"
|  Lbot[intro]: "([], \<LM> ff \<RM> \<Rightarrow>* Em) \<in> Ax"

(* upRules is the set of all rules which have a single conclusion.  This is akin to each rule having a 
   single principal formula.  We don't want rules to have no premisses, hence the restriction
   that ps \<noteq> [] *)
inductive_set "upRules" where
   L[intro]: "\<lbrakk> c \<equiv> (\<LM> Compound R Fs \<RM> \<Rightarrow>* Em) ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules"
|  R[intro]: "\<lbrakk> c \<equiv> (\<Empt> \<Rightarrow>* Compound F Fs) ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules" 

inductive_set extRules :: "'a rule set \<Rightarrow> 'a rule set"  ("_*")
  for R :: "'a rule set" 
  where
   I[intro]: "r \<in> R \<Longrightarrow> extendRule seq r \<in> R*"

(* A formulation of what it means to be a principal formula for a rule.  Note that we have to build up from
   single conclusion rules.   *)

inductive leftPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up[intro]: "C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* Em)  \<Longrightarrow> 
                   leftPrincipal (Ps,C) (Compound F Fs)"


inductive rightPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up[intro]: "C = (\<Empt> \<Rightarrow>* Compound F Fs) \<Longrightarrow> rightPrincipal (Ps,C) (Compound F Fs)"


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
    ultimately have "\<forall> p \<in> set (a # as). \<exists> n\<le>(max m m'). (p,n) \<in> derivable R" apply (auto simp add:Ball_def)
      apply (rule_tac x=m' in exI) apply simp
      apply (drule_tac x=x in spec) apply auto by (rule_tac x=n in exI) auto
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
assumes "extend S (\<LM> At i \<RM> \<Rightarrow>* At i) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "At i \<in># \<Gamma>"
using assms
proof-
  from assms have "\<exists> \<Gamma>'. \<Gamma> = \<Gamma>' \<oplus> At i" 
     using extend_def[where forms=S and seq="\<LM> At i \<RM> \<Rightarrow>* At i"]
     by (rule_tac x="antec S" in exI) auto
  then show ?thesis by auto
qed

lemma extendFalsum:
assumes "extend S (\<LM> ff \<RM> \<Rightarrow>* Em) = (\<Gamma> \<Rightarrow>* \<Delta>)"
shows "ff \<in># \<Gamma>"
proof-
  from assms have "\<exists> \<Gamma>'. \<Gamma> = \<Gamma>' \<oplus> ff" 
     using extend_def[where forms=S and seq="\<LM>ff \<RM> \<Rightarrow>* Em"]
     by (rule_tac x="antec S" in exI) auto
  then show ?thesis by auto
qed


(* Lemma that says if a propositional variable is in both the antecedent and succedent of a sequent,
   then it is derivable from idupRules *)
lemma containID:
assumes a:"At i \<in># \<Gamma>"
    and b:"Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* At i,0) \<in> derivable R*"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> At i \<oplus> At i" by auto
then have "extend ((\<Gamma> \<ominus> At i) \<Rightarrow>* Em) (\<LM> At i \<RM> \<Rightarrow>* At i) = (\<Gamma> \<Rightarrow>* At i)" 
     using extend_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* Em" and seq="\<LM>At i\<RM> \<Rightarrow>* At i"] by auto
moreover
have "([],\<LM> At i \<RM> \<Rightarrow>* At i) \<in> R" using b by auto
ultimately
have "([],\<Gamma> \<Rightarrow>* At i) \<in> R*" 
     using extRules.I[where R=R and r="([],  \<LM>At i\<RM> \<Rightarrow>* At i)" and seq="\<Gamma> \<ominus> At i \<Rightarrow>* Em"] 
       and extendRule_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* Em" and R="([],  \<LM>At i\<RM> \<Rightarrow>* At i)"] by auto
then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* At i"] by auto
qed

lemma containFalsum:
assumes a: "ff \<in># \<Gamma>"
   and  b: "Ax \<subseteq> R"
shows "(\<Gamma> \<Rightarrow>* C,0) \<in> derivable R*"
proof-
from a have "\<Gamma> = \<Gamma> \<ominus> ff \<oplus> ff" by auto
then have "extend (\<Gamma> \<ominus> ff \<Rightarrow>* C) (\<LM>ff\<RM> \<Rightarrow>* Em) = (\<Gamma> \<Rightarrow>* C)"
     using extend_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* C" and seq="\<LM>ff\<RM> \<Rightarrow>* Em"] by auto 
moreover
have "([],\<LM>ff\<RM> \<Rightarrow>* Em) \<in> R" using b by auto
ultimately have "([],\<Gamma> \<Rightarrow>* C) \<in> R*"
     using extRules.I[where R=R and r="([],  \<LM>ff\<RM> \<Rightarrow>* Em)" and seq="\<Gamma> \<ominus> ff \<Rightarrow>* C"] 
       and extendRule_def[where forms="\<Gamma> \<ominus> ff \<Rightarrow>* C" and R="([],  \<LM>ff\<RM> \<Rightarrow>* Em)"] by auto
then show ?thesis using derivable.base[where R="R*" and C="\<Gamma> \<Rightarrow>* C"] by auto
qed 

(* Lemma which says that if r is an identity rule, then r is of the form
   ([], P \<Rightarrow>* P) *)
lemma characteriseAx:
shows "r \<in> Ax \<Longrightarrow> r = ([],\<LM> ff \<RM> \<Rightarrow>* Em) \<or> (\<exists> i. r = ([], \<LM> At i \<RM> \<Rightarrow>* At i))"
apply (cases r) by (rule Ax.cases) auto

(* A lemma about the last rule used in a derivation, i.e. that one exists *)
lemma characteriseLast:
assumes "(C,m+1) \<in> derivable R"
shows "\<exists> Ps. Ps \<noteq> [] \<and>
             (Ps,C) \<in> R \<and> 
             (\<forall> p \<in> set Ps. \<exists> n\<le>m. (p,n) \<in> derivable R)"
using assms
by (cases) auto




lemma upRuleCharacterise:
assumes "(Ps,C) \<in> upRules"
shows "\<exists> F Fs. C = (\<Empt> \<Rightarrow>* Compound F Fs) \<or> C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* Em)"
using assms by (cases) auto


lemma extendEmpty:
shows "extend (\<Empt> \<Rightarrow>* Em) C = C"
apply (auto simp add:extend_def) apply (cases C) apply auto by (cases C) auto

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
from assms obtain i where r1:"r = ([], \<LM> ff \<RM> \<Rightarrow>* Em) \<or> r = ([], \<LM> At i \<RM> \<Rightarrow>* At i)" 
     using characteriseAx[where r=r] by auto
{ assume "rightPrincipal r A" then obtain Ps where r2:"r = (Ps, \<Empt> \<Rightarrow>* A)" by (cases r) auto
  with r1 have "False" by simp
}
then have "\<not> rightPrincipal r A" by auto
moreover
{ assume "leftPrincipal r A" then obtain Ps' F Fs where r3:"r = (Ps', \<LM>Compound F Fs\<RM> \<Rightarrow>* Em)" by (cases r) auto
  with r1 have "False" by auto
}
then have "\<not> leftPrincipal r A" by auto
ultimately show ?thesis by simp
qed

lemma extended_Ax_prems_empty:
assumes "r \<in> Ax"
shows "fst (extendRule S r) = []"
using assms apply (cases r) by (rule Ax.cases) (auto simp add:extendRule_def)



(* ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
                THIS IS NOW
                SingleWeakening.thy
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   --------------------------------------------------- *)


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
assumes a:"(\<Gamma> \<Rightarrow>* E,n) \<in> derivable R*"
   and  b: "R' \<subseteq> upRules"
   and  c: "R = Ax \<union> R'" 
shows "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,n) \<in> derivable R*"
using a
proof (induct n arbitrary: \<Gamma> E rule:nat_less_induct)
case (1 n \<Gamma> E)
then have IH: "\<forall>m<n. \<forall> \<Gamma> E. ( \<Gamma> \<Rightarrow>* E, m) \<in> derivable R* \<longrightarrow> ( \<Gamma> + \<Gamma>' \<Rightarrow>* E, m) \<in> derivable R*" 
      and a': "( \<Gamma> \<Rightarrow>* E, n) \<in> derivable R*" by auto
show ?case
proof (cases n)
case 0
 then have "(\<Gamma> \<Rightarrow>* E,0) \<in> derivable R*" using a' by simp
 then have "([], \<Gamma> \<Rightarrow>* E) \<in> R*" by (cases) auto
 then obtain  r S where "r \<in> R" and split:"extendRule S r = ([],\<Gamma> \<Rightarrow>* E)" 
      by (rule extRules.cases) auto
 then obtain c where "r = ([],c)" by (cases r) (auto simp add:extendRule_def)
 with \<open>r \<in> R\<close> have "r \<in> Ax \<or> r \<in> upRules" using b c by auto
 with \<open>r = ([],c)\<close> have "r \<in> Ax" by (auto) (rule upRules.cases,auto)                                 
 with \<open>r = ([],c)\<close> obtain i where "c = (\<LM>At i\<RM> \<Rightarrow>* At i) \<or> c = (\<LM>ff\<RM> \<Rightarrow>* Em)"
      using characteriseAx[where r=r] by auto
 moreover
    {assume "c = (\<LM>At i\<RM> \<Rightarrow>* At i)"
     then have "extend S (\<LM>At i\<RM> \<Rightarrow>* At i) = (\<Gamma> \<Rightarrow>* At i)" and "At i = E" using split and \<open>r = ([],c)\<close>
          by (auto simp add:extendRule_def extend_def)
     then have "At i \<in># \<Gamma>" using extendID by auto
     then have "At i \<in># \<Gamma> + \<Gamma>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,0) \<in> derivable R*" 
          using c and containID[where \<Gamma>="\<Gamma>+\<Gamma>'" and R=R and i=i] and \<open>At i = E\<close> by auto
    }
 moreover
    {assume "c = (\<LM>ff\<RM> \<Rightarrow>* Em)"
     then have "extend S (\<LM>ff\<RM> \<Rightarrow>* Em) = (\<Gamma> \<Rightarrow>* E)" using split and \<open>r = ([],c)\<close>
          by (auto simp add:extendRule_def extend_def)
     then have "ff \<in># \<Gamma>" using extendFalsum by auto
     then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
     then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,0) \<in> derivable R*" 
          using c and containFalsum[where \<Gamma>="\<Gamma>+\<Gamma>'" and R=R] by auto
    }
 ultimately show "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,n) \<in> derivable R*" using \<open>n=0\<close> by auto
next
case (Suc n')
 then have "(\<Gamma> \<Rightarrow>* E, n'+1) \<in> derivable R*" using a' by simp
 then obtain Ps where f:"Ps \<noteq> []"
                  and g:"(Ps, \<Gamma> \<Rightarrow>* E) \<in> R*" 
                  and h:"\<forall> p \<in> set Ps. \<exists> m\<le>n'. (p,m) \<in> derivable R*" 
      using characteriseLast[where C="\<Gamma> \<Rightarrow>* E" and m=n' and R="R*"] by auto
 from g c obtain S r where "r \<in> R" and "(r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* E)" by (cases) auto
 with b have as: "(r \<in> Ax \<or> r \<in> upRules) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* E)" by auto
 from as f have "fst r \<noteq> []" by (auto simp add:extendRule_def map_is_Nil_conv)
 with as have "r \<in> upRules" apply (cases r,auto) by (rule Ax.cases) auto
 moreover obtain ps c where "r = (ps,c)" by (cases r) auto
 ultimately have "(ps,c) \<in> upRules" by simp
 obtain \<Gamma>1 \<delta> where "S = (\<Gamma>1 \<Rightarrow>* \<delta>)" by (cases S) auto
 with h as \<open>r = (ps,c)\<close> have pms: "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 \<Rightarrow>* \<delta>) p,m) \<in> derivable R*"
      by(auto simp add:extendRule_def)
 have "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*"
      proof-
      {fix p
       assume "p \<in> set ps"
       with pms obtain m where "m\<le>n'" and aa: "(extend (\<Gamma>1 \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" by auto
       moreover obtain \<Gamma>2 \<delta>' where eq:"p = (\<Gamma>2 \<Rightarrow>* \<delta>')" by (cases p) auto
       have "\<delta>' = Em \<or> \<delta>' \<noteq> Em" by blast
       moreover
          {assume "\<delta>' = Em"
           then have "extend (\<Gamma>1 \<Rightarrow>* \<delta>) p = (\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>)" using eq by (auto simp add:extend_def)
           then have "(\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>,m) \<in> derivable R*" using aa by auto
           then have "(\<Gamma>1 + \<Gamma>2 + \<Gamma>' \<Rightarrow>* \<delta>, m) \<in> derivable R*" using IH and \<open>n = Suc n'\<close> and \<open>m\<le>n'\<close>
                apply- apply (drule_tac x=m in spec) by auto
           then have "(extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" using eq and \<open>\<delta>' = Em\<close>
                by (auto simp add:extend_def union_ac)
          }
       moreover
          {assume "\<delta>' \<noteq> Em"
           then have "extend (\<Gamma>1 \<Rightarrow>* \<delta>) p = (\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>')" using eq by (auto simp add:extend_def)
           then have "(\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>',m) \<in> derivable R*" using aa by auto
           then have "(\<Gamma>1 + \<Gamma>2 + \<Gamma>' \<Rightarrow>* \<delta>', m) \<in> derivable R*" using IH and \<open>n = Suc n'\<close> and \<open>m\<le>n'\<close>
                apply- apply (drule_tac x=m in spec) by auto
           then have "(extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" using eq and \<open>\<delta>' \<noteq> Em\<close>
                by (auto simp add:extend_def union_ac)
          }
       ultimately have "(extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" by blast
       then have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close> by auto
       }
       then show ?thesis by auto
       qed
 then have "\<forall> p \<in> set (fst (extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r)).
            \<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
 moreover have "extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r \<in> R*" 
          using \<open>r \<in> upRules\<close> and \<open>r \<in> R\<close> by auto
 moreover from \<open>S = (\<Gamma>1 \<Rightarrow>* \<delta>)\<close> and as have "extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) (snd r) = (\<Gamma> + \<Gamma>' \<Rightarrow>* E)"
          by (auto simp add:extendRule_def extend_def union_ac)
 ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,n'+1) \<in> derivable R*"
          using derivable.step[where r="extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r" and R="R*" and m="n'"]
          and \<open>fst r \<noteq> []\<close> by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
 then show "( \<Gamma> + \<Gamma>' \<Rightarrow>* E, n) \<in> derivable R*" using \<open>n = Suc n'\<close> by auto
 qed
qed

(*>*)
text\<open>
\noindent Given this, it is possible to have right weakening, where we overwrite the empty formula if it appears as the succedent of the root of a derivation:
\<close>
lemma dpWeakR:
assumes (*<*)a:(*>*)"(\<Gamma> \<Rightarrow>* Em,n) \<in> derivable R*"
and  (*<*)b:(*>*) "R' \<subseteq> upRules"
and  (*<*)c:(*>*) "R = Ax \<union> R'" 
shows "(\<Gamma> \<Rightarrow>* C,n) \<in> derivable R*"   \<comment> \<open>Proof omitted\<close>
(*<*)
using a
proof (induct n arbitrary: \<Gamma> rule:nat_less_induct)
case (1 n \<Gamma>)
then have IH: "\<forall>m<n. \<forall> \<Gamma>. ( \<Gamma> \<Rightarrow>* Em, m) \<in> derivable R* \<longrightarrow> ( \<Gamma> \<Rightarrow>* C, m) \<in> derivable R*" 
      and a': "( \<Gamma> \<Rightarrow>* Em, n) \<in> derivable R*" by auto
show ?case
proof (cases n)
case 0
 then have "(\<Gamma> \<Rightarrow>* Em,0) \<in> derivable R*" using a' by simp
 then have "([], \<Gamma> \<Rightarrow>* Em) \<in> R*" by (cases) auto
 then obtain  r S where "r \<in> R" and split:"extendRule S r = ([],\<Gamma> \<Rightarrow>* Em)" 
      by (rule extRules.cases) auto
 then obtain c where "r = ([],c)" by (cases r) (auto simp add:extendRule_def)
 with \<open>r \<in> R\<close> have "r \<in> Ax \<or> r \<in> upRules" using b c by auto
 with \<open>r = ([],c)\<close> have "r \<in> Ax" by (auto) (rule upRules.cases,auto)                                 
 with \<open>r = ([],c)\<close> obtain i where "c = (\<LM>At i\<RM> \<Rightarrow>* At i) \<or> c = (\<LM>ff\<RM> \<Rightarrow>* Em)"
      using characteriseAx[where r=r] by auto
 moreover
    {assume "c = (\<LM>At i\<RM> \<Rightarrow>* At i)"
     with split and \<open>r = ([],c)\<close> have "(\<Gamma> \<Rightarrow>* C,0) \<in> derivable R*" by (auto simp add:extendRule_def extend_def)
    }
 moreover
    {assume "c = (\<LM>ff\<RM> \<Rightarrow>* Em)"
     then have "extend S (\<LM>ff\<RM> \<Rightarrow>* Em) = (\<Gamma> \<Rightarrow>* Em)" using split and \<open>r = ([],c)\<close>
          by (auto simp add:extendRule_def extend_def)
     then have "ff \<in># \<Gamma>" using extendFalsum by auto
     then have "(\<Gamma> \<Rightarrow>* C,0) \<in> derivable R*" 
          using c and containFalsum[where \<Gamma>=\<Gamma> and R=R] by auto
    }
 ultimately show "(\<Gamma> \<Rightarrow>* C,n) \<in> derivable R*" using \<open>n=0\<close> by auto
next
case (Suc n')
 then have "(\<Gamma> \<Rightarrow>* Em, n'+1) \<in> derivable R*" using a' by simp
 then obtain Ps where f:"Ps \<noteq> []"
                  and g:"(Ps, \<Gamma> \<Rightarrow>* Em) \<in> R*" 
                  and h:"\<forall> p \<in> set Ps. \<exists> m\<le>n'. (p,m) \<in> derivable R*" 
      using characteriseLast[where C="\<Gamma> \<Rightarrow>* Em" and m=n' and R="R*"] by auto
 from g c obtain S r where "r \<in> R" and split: "(r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* Em)" by (cases) auto
 with b have as: "(r \<in> Ax \<or> r \<in> upRules) \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* Em)" by auto
 from as f have "fst r \<noteq> []" by (auto simp add:extendRule_def map_is_Nil_conv)
 with as have "r \<in> upRules" apply (cases r,auto) by (rule Ax.cases) auto
 moreover obtain ps c where "r = (ps,c)" by (cases r) auto
 ultimately have "(ps,c) \<in> upRules" by simp
 then obtain F Fs where "c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* Em) \<or> c = (\<Empt> \<Rightarrow>* Compound F Fs)" by (rule upRules.cases) auto
 moreover
    {assume "c = (\<Empt> \<Rightarrow>* Compound F Fs)"
     with \<open>r = (ps,c)\<close> and split have "(\<Gamma> \<Rightarrow>* C,n'+1) \<in> derivable R*" by (auto simp add:extendRule_def extend_def)
    }
 moreover
    {assume "c = (\<LM> Compound F Fs \<RM> \<Rightarrow>* Em)"
     moreover obtain \<Gamma>1 \<delta> where "S = (\<Gamma>1 \<Rightarrow>* \<delta>)" by (cases S) auto
     ultimately have "\<delta> = Em" using split and \<open>r= (ps,c)\<close> by (auto simp add:extendRule_def extend_def)
     then have "S = (\<Gamma>1 \<Rightarrow>* Em)" using \<open>S = (\<Gamma>1 \<Rightarrow>* \<delta>)\<close> by simp
     with h as \<open>r = (ps,c)\<close> have pms: "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 \<Rightarrow>* Em) p,m) \<in> derivable R*"
          by(auto simp add:extendRule_def)
     have "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1  \<Rightarrow>* C) p,m) \<in> derivable R*"
          proof-
          {fix p
           assume "p \<in> set ps"
           with pms obtain m where "m\<le>n'" and aa: "(extend (\<Gamma>1 \<Rightarrow>* Em) p,m) \<in> derivable R*" by auto
           moreover obtain \<Gamma>2 \<delta>' where eq:"p = (\<Gamma>2 \<Rightarrow>* \<delta>')" by (cases p) auto
           have "\<delta>' = Em \<or> \<delta>' \<noteq> Em" by blast
           moreover
              {assume "\<delta>' = Em"
               then have "extend (\<Gamma>1 \<Rightarrow>* Em) p = (\<Gamma>1 + \<Gamma>2 \<Rightarrow>* Em)" using eq by (auto simp add:extend_def)
               then have "(\<Gamma>1 + \<Gamma>2 \<Rightarrow>* Em,m) \<in> derivable R*" using aa by auto
               then have "(\<Gamma>1 + \<Gamma>2 \<Rightarrow>* C, m) \<in> derivable R*" using IH and \<open>n = Suc n'\<close> and \<open>m\<le>n'\<close>
                    apply- apply (drule_tac x=m in spec) by auto
               then have "(extend (\<Gamma>1  \<Rightarrow>* C) p,m) \<in> derivable R*" using eq and \<open>\<delta>' = Em\<close>
                    by (auto simp add:extend_def union_ac)
              }
           moreover
              {assume "\<delta>' \<noteq> Em"
               then have "extend (\<Gamma>1 \<Rightarrow>* Em) p = (\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>')" using eq by (auto simp add:extend_def)
               then have "(\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>',m) \<in> derivable R*" using aa by auto
               moreover have "extend (\<Gamma>1 \<Rightarrow>* C) p = (\<Gamma>1 + \<Gamma>2 \<Rightarrow>* \<delta>')" using eq and \<open>\<delta>' \<noteq> Em\<close> by (auto simp add:extend_def)
               ultimately have "(extend (\<Gamma>1 \<Rightarrow>* C) p,m) \<in> derivable R*" by simp
              }
           ultimately have "(extend (\<Gamma>1  \<Rightarrow>* C) p,m) \<in> derivable R*" by blast
           then have "\<exists> m\<le>n'. (extend (\<Gamma>1  \<Rightarrow>* C) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close> by auto
           }
           then show ?thesis by auto
           qed
     then have "\<forall> p \<in> set (fst (extendRule (\<Gamma>1  \<Rightarrow>* C) r)).
                \<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
     moreover have "extendRule (\<Gamma>1  \<Rightarrow>* C) r \<in> R*" 
              using \<open>r \<in> upRules\<close> and \<open>r \<in> R\<close> by auto
     moreover from \<open>S = (\<Gamma>1 \<Rightarrow>* Em)\<close> and as have "extend (\<Gamma>1  \<Rightarrow>* C) (snd r) = (\<Gamma> \<Rightarrow>* C)"
              by (auto simp add:extendRule_def extend_def union_ac)
     ultimately have "(\<Gamma> \<Rightarrow>* C,n'+1) \<in> derivable R*"
              using derivable.step[where r="extendRule (\<Gamma>1 \<Rightarrow>* C) r" and R="R*" and m="n'"]
              and \<open>fst r \<noteq> []\<close> by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
    }
 ultimately show "( \<Gamma> \<Rightarrow>* C, n) \<in> derivable R*" using \<open>n = Suc n'\<close> by auto
 qed
qed



(* ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
                THIS IS NOW
                SingleInvertible.thy
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   --------------------------------------------------- *)
(*>*)
text\<open>
\noindent Of course, if $C = Em$, then the above lemma is trivial.  The burden is on the user not to ``use'' the empty formula as a normal formula.  An invertibility lemma can then be formalised:
\<close>

lemma rightInvertible:
(*<*)fixes \<Gamma> :: "'a form multiset"(*>*)

assumes (*<*)rules:(*>*) "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
and   (*<*)a:(*>*) "(\<Gamma> \<Rightarrow>* Compound F Fs,n) \<in> derivable R*"
and   (*<*)b:(*>*) "\<forall> r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* E) \<in> set (fst r')"
and (*<*)nonEm:(*>*) "E \<noteq> Em"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*"

(*<*)
using assms
proof (induct n arbitrary:\<Gamma> rule:nat_less_induct)
 case (1 n \<Gamma>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma>. ( \<Gamma> \<Rightarrow>* Compound F Fs, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* E) \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* E, m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<Rightarrow>* Compound F Fs,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* E) \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<Rightarrow>* Compound F Fs,0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<Rightarrow>* Compound F Fs) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<Rightarrow>* Compound F Fs) \<and> (r \<in> Ax \<or> r \<in> R')"
          using rules and ruleSet[where R'=R' and R=R and Ps="[]" and C="\<Gamma> \<Rightarrow>* Compound F Fs"] by auto
     then obtain r S where "extendRule S r = ([],\<Gamma> \<Rightarrow>* Compound F Fs)" and "r \<in> Ax \<or> r \<in> R'" by auto
      moreover
      {assume "r \<in> Ax"
       then have "r = ([], \<LM> ff \<RM> \<Rightarrow>* Em)" 
            using characteriseAx[where r=r] and \<open>extendRule S r = ([],\<Gamma> \<Rightarrow>* Compound F Fs)\<close> 
            by (auto simp add:extendRule_def extend_def)
       with \<open>extendRule S r = ([],\<Gamma> \<Rightarrow>* Compound F Fs)\<close>
            have "extend S (\<LM> ff \<RM> \<Rightarrow>* Em) = (\<Gamma> \<Rightarrow>* Compound F Fs)"
            using extendRule_def[where R="([],\<LM>ff\<RM>\<Rightarrow>* Em)" and forms=S] by auto
       then have "ff \<in># \<Gamma>" using extendFalsum[where S=S and \<Gamma>=\<Gamma> and \<Delta>="Compound F Fs"] by auto
       then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
       then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,0) \<in> derivable R*" using rules
            and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and R=R] by auto
       then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,0) \<in> derivable R*" by blast
      }
      moreover
      {assume "r \<in> R'"
       then have "r \<in> upRules" using rules by auto
       then have "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)"
            proof-
            obtain x y where "r = (x,y)" by (cases r)
            with \<open>r \<in> upRules\<close> have "(x,y) \<in> upRules" by simp
            then obtain Ps where "(Ps :: 'a sequent list) \<noteq> []" and "x=Ps" by (cases) (auto)
            with \<open>r = (x,y)\<close> have "r = (Ps, y)" by simp
            then show "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)" using \<open>Ps \<noteq> []\<close> by blast
            qed
       then obtain Ps C where "Ps \<noteq> []" and "r = (Ps,C)" by auto
       moreover from \<open>extendRule S r = ([], \<Gamma> \<Rightarrow>* Compound F Fs)\<close> have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then obtain S where "r = ([],S)" by blast
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,0) \<in> derivable R*" using rules by simp
       }
       ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*" using \<open>n=0\<close> by blast
 next
     case (Suc n')
     then have "(\<Gamma> \<Rightarrow>* Compound F Fs,n'+1) \<in> derivable R*" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<Rightarrow>* Compound F Fs) \<in> R*" and 
                          "Ps \<noteq> []" and 
                          derv: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
          using characteriseLast[where C="\<Gamma> \<Rightarrow>* Compound F Fs" and m=n' and R="R*"] by auto
     then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* Compound F Fs)"
          using rules and ruleSet[where R'=R' and R=R and Ps=Ps and C="\<Gamma> \<Rightarrow>* Compound F Fs"] by auto
     then obtain r S where "r \<in> Ax \<or> r \<in> R'" and ext: "extendRule S r = (Ps, \<Gamma> \<Rightarrow>* Compound F Fs)" by auto
     moreover
        {assume "r \<in> Ax"
         then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
         moreover obtain x y where "r = (x,y)" by (cases r)
         then have "x \<noteq> []" using \<open>Ps \<noteq> []\<close> and ext
                            and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] by auto
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*"
              using \<open>r=(x,y)\<close> by auto
        }
     moreover
        {assume "r \<in> R'"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> upRules" using rules and \<open>r \<in> R'\<close> by auto
         then have "\<exists> T Ts. c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em) \<or> c = (\<Empt> \<Rightarrow>* Compound T Ts)" using \<open>r=(ps,c)\<close>
              and upRuleCharacterise[where Ps=ps and C=c] by auto
         then obtain T Ts where "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em) \<or> c = (\<Empt> \<Rightarrow>* Compound T Ts)" by blast
         moreover
            {assume "c = (\<Empt> \<Rightarrow>* Compound T Ts)"
             with ext have "Compound T Ts = Compound F Fs"
                  using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def extend_def)
             then have "rightPrincipal r (Compound F Fs)" using \<open>c = (\<Empt> \<Rightarrow>* Compound T Ts)\<close> and \<open>r = (ps,c)\<close>
                  by auto
             then have "(\<Gamma>' \<Rightarrow>* E) \<in> set ps" using b' and \<open>r = (ps,c)\<close> and \<open>r \<in> R'\<close> and rules
                  by auto
             then have "extend S (\<Gamma>' \<Rightarrow>* E) \<in> set Ps" using \<open>extendRule S r = (Ps,\<Gamma> \<Rightarrow>* Compound F Fs)\<close>
                  and \<open>r = (ps,c)\<close> by (simp add:extendContain)
             moreover from \<open>rightPrincipal r (Compound F Fs)\<close> have "c = (\<Empt> \<Rightarrow>* Compound F Fs)" 
                  using \<open>r = (ps,c)\<close> by (cases) auto
             with ext have "antec S = \<Gamma>"
                  using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def extend_def)
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E) \<in> set Ps" using nonEm by (simp add:extend_def)
             then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*"
                  using \<open>\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*\<close> by auto
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*" using \<open>n = Suc n'\<close>
                  by (auto,rule_tac x=m in exI) (simp)
            }
         moreover
            {assume "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)"
             with ext and \<open>r = (ps,c)\<close>
                  have "Compound T Ts \<in># \<Gamma>" by (auto simp add:extendRule_def extend_def)
             then have "\<exists> \<Gamma>1. \<Gamma> = \<Gamma>1 \<oplus> Compound T Ts"
                  by (rule_tac x="\<Gamma> \<ominus> Compound T Ts" in exI) (auto simp add:multiset_eq_iff)
             then obtain \<Gamma>1 where "\<Gamma> = \<Gamma>1 \<oplus> Compound T Ts" by auto
             moreover from \<open>c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)\<close> and \<open>r = (ps,c)\<close> and ext
                  have "succ S = Compound F Fs"
                  by (auto simp add:extendRule_def extend_def)
             ultimately have "S = (\<Gamma>1 \<Rightarrow>* Compound F Fs)" using ext
                  and \<open>r = (ps,c)\<close> and \<open>c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)\<close> apply (auto simp add:extendRule_def extend_def)
                  by (cases S) auto
             with derv have pms: "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 \<Rightarrow>* Compound F Fs) p,m) \<in> derivable R*" using ext
                  and \<open>r= (ps,c)\<close> by (auto simp add:extendRule_def)
             have "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) p,m) \<in> derivable R*"
                 proof-
                 {fix p
                  assume "p \<in> set ps"
                  obtain \<Gamma>i \<delta>i where p: "p = (\<Gamma>i \<Rightarrow>* \<delta>i)" by (cases p) auto
                  have "\<delta>i = Em \<or> \<delta>i \<noteq> Em" by blast
                  moreover
                     {assume "\<delta>i = Em"
                      then have "extend (\<Gamma>1 \<Rightarrow>* Compound F Fs) p = (\<Gamma>1 + \<Gamma>i \<Rightarrow>* Compound F Fs)" using p
                           by (auto simp add:extend_def)
                      with pms obtain m where "m \<le>n'" and "(\<Gamma>1 + \<Gamma>i \<Rightarrow>* Compound F Fs,m) \<in> derivable R*"
                           using \<open>p \<in> set ps\<close> by auto
                      with IH and \<open>n = Suc n'\<close> and b' have "\<exists> m'\<le>m. (\<Gamma>1 + \<Gamma>i + \<Gamma>' \<Rightarrow>* E,m') \<in> derivable R*"
                           by auto
                      then have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                           and p and \<open>\<delta>i = Em\<close> apply (auto simp add:extend_def union_ac) 
                           by (rule_tac x="m'" in exI) auto
                     }
                  moreover
                     {assume "\<delta>i \<noteq> Em"
                      then have "extend (\<Gamma>1 \<Rightarrow>* Compound F Fs) p = (\<Gamma>1 + \<Gamma>i \<Rightarrow>* \<delta>i)" using p
                           by (auto simp add:extend_def)
                      with pms obtain m where "m\<le>n'" and "(\<Gamma>1 + \<Gamma>i \<Rightarrow>* \<delta>i,m) \<in> derivable R*"
                           using \<open>p \<in> set ps\<close> by auto
                      then have "(\<Gamma>1 + \<Gamma>i + \<Gamma>' \<Rightarrow>* \<delta>i,m) \<in> derivable R*" using rules 
                           and dpWeak[where \<Gamma>="\<Gamma>1 + \<Gamma>i" and E="\<delta>i" and n=m and R=R and R'=R'] by auto
                      then have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                           and p and \<open>\<delta>i \<noteq> Em\<close> by (auto simp add:extend_def union_ac)
                     } 
                  ultimately have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) p, m) \<in> derivable R*" by blast
                 }
                 thus ?thesis by auto
                 qed
             then have "\<forall> p \<in> set (fst (extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) r)).
                          \<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
             moreover have "extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) r \<in> R*" using \<open>r \<in> R'\<close> and rules by auto
             moreover from \<open>S = (\<Gamma>1 \<Rightarrow>* Compound F Fs)\<close> and ext and \<open>c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)\<close>
                 and \<open>\<Gamma> = \<Gamma>1 \<oplus> Compound T Ts\<close> and \<open>r = (ps,c)\<close>
                 have "extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) (snd r) = (\<Gamma> + \<Gamma>' \<Rightarrow>* E)" by (auto simp add:extend_def union_ac)
             moreover from ext and \<open>r = (ps,c)\<close> and \<open>Ps \<noteq> []\<close> have "fst r \<noteq> []" by (auto simp add:extendRule_def)
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* E,n'+1) \<in> derivable R*" using
                 derivable.step[where r="extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* E) r" and m="n'" and R="R*"] 
                 by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*" using \<open>n = Suc n'\<close> by auto
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*" by blast         
        }
      ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* E,m) \<in> derivable R*" by blast
   qed
qed
(*>*)

lemma leftInvertible:
(*<*)fixes \<Gamma> :: "'a form multiset"(*>*)

assumes (*<*)rules:(*>*) "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
and   (*<*)a:(*>*) "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>,n) \<in> derivable R*"
and   (*<*)b:(*>*) "\<forall> r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* Em) \<in> set (fst r')"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*"
 (*<*)
using assms
proof (induct n arbitrary:\<Gamma> \<delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<delta>. ( \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* Em) \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>, m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* Em) \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>, 0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>) \<and> (r \<in> Ax \<or> r \<in> R')"
          using rules and ruleSet[where R'=R' and R=R and Ps="[]" and C="\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>"] by auto
     then obtain r S where "extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)" and "r \<in> Ax \<or> r \<in> R'" by auto
     moreover
      {assume "r \<in> Ax"
       then obtain i where "r = ([], \<LM> ff \<RM> \<Rightarrow>* Em) \<or> r = ([], \<LM>At i\<RM> \<Rightarrow>* At i)" 
            using characteriseAx[where r=r] and \<open>extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close> 
            by (auto simp add:extendRule_def extend_def)
       moreover
          {assume "r = ([], \<LM>ff\<RM> \<Rightarrow>* Em)"
           with \<open>extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close>
                have "extend S (\<LM> ff \<RM> \<Rightarrow>* Em) = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)"
                using extendRule_def[where R="([],\<LM>ff\<RM>\<Rightarrow>* Em)" and forms=S] by auto
           then have "ff \<in># \<Gamma> \<oplus> Compound F Fs" 
                using extendFalsum[where S=S and \<Gamma>="\<Gamma>\<oplus> Compound F Fs" and \<Delta>=\<delta>] by auto
           then have "ff \<in># \<Gamma>" by auto
           then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
           then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,0) \<in> derivable R*" using rules
                and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and R=R] by auto
          }
       moreover
          {assume "r = ([], \<LM>At i\<RM> \<Rightarrow>* At i)"
           with \<open>extendRule S r = ([], \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close>
                have "extend S (\<LM> At i\<RM> \<Rightarrow>* At i) = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)"
                using extendRule_def[where R="([], \<LM>At i \<RM> \<Rightarrow>* At i)" and forms=S] by auto
           then have "At i \<in># \<Gamma> \<oplus> Compound F Fs" and eq: "\<delta> = At i"
                using extendID[where S=S and \<Gamma>="\<Gamma> \<oplus> Compound F Fs" and \<Delta>=\<delta> and i=i] by (auto simp add:extend_def)
           then have "At i \<in># \<Gamma>" by auto
           then have "At i \<in># \<Gamma> + \<Gamma>'" by auto
           with eq have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,0) \<in> derivable R*" using rules
                and containID[where i=i and \<Gamma>="\<Gamma> + \<Gamma>'" and R=R] by auto
          }
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>, 0) \<in> derivable R*" by blast
      }
   moreover
      {assume "r \<in> R'"
       then have "r \<in> upRules" using rules by auto
       then have "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)"
            proof-
            obtain x y where "r = (x,y)" by (cases r)
            with \<open>r \<in> upRules\<close> have "(x,y) \<in> upRules" by simp
            then obtain Ps where "(Ps :: 'a sequent list) \<noteq> []" and "x=Ps" by (cases) (auto)
            with \<open>r = (x,y)\<close> have "r = (Ps, y)" by simp
            then show "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)" using \<open>Ps \<noteq> []\<close> by blast
            qed
       then obtain Ps C where "Ps \<noteq> []" and "r = (Ps,C)" by auto
       moreover from \<open>extendRule S r = ([], \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close> have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then obtain S where "r = ([],S)" by blast
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,0) \<in> derivable R*" using rules by simp
       }
    ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*" using \<open>n=0\<close> by blast
 next
     case (Suc n')
     then have "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>,n'+1) \<in> derivable R*" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>) \<in> R*" and 
                          "Ps \<noteq> []" and 
                          derv: "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
          using characteriseLast[where C="\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>" and m=n' and R="R*"] by auto
     then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)"
          using rules and ruleSet[where R'=R' and R=R and Ps=Ps and C="\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>"] by auto
     then obtain r S where "r \<in> Ax \<or> r \<in> R'" and ext: "extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)" by auto
     moreover
        {assume "r \<in> Ax"
         then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
         moreover obtain x y where "r = (x,y)" by (cases r)
         then have "x \<noteq> []" using \<open>Ps \<noteq> []\<close> and ext
                            and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] by auto
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*"
              using \<open>r=(x,y)\<close> by auto
        }
     moreover
        {assume "r \<in> R'"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> upRules" using rules and \<open>r \<in> R'\<close> by auto
         then have "\<exists> T Ts. c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em) \<or> c = (\<Empt> \<Rightarrow>* Compound T Ts)" using \<open>r=(ps,c)\<close>
              and upRuleCharacterise[where Ps=ps and C=c] by auto
         then obtain T Ts where "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em) \<or> c = (\<Empt> \<Rightarrow>* Compound T Ts)" by blast
         moreover
            {assume "c = (\<Empt> \<Rightarrow>* Compound T Ts)"
             with ext have "antec S = \<Gamma> \<oplus> Compound F Fs" and del: "Compound T Ts = \<delta>"
                  using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def extend_def)
             then obtain \<delta>' where "S = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>')" by (cases S) auto
             with derv have pms: "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>') p,m) \<in> derivable R*"
                  using ext and \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
             have "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') p,m) \<in> derivable R*"
                 proof-
                 {fix p
                  assume "p \<in> set ps"
                  obtain \<Gamma>i \<delta>i where p: "p = (\<Gamma>i \<Rightarrow>* \<delta>i)" by (cases p) auto
                  have "\<delta>i = Em \<or> \<delta>i \<noteq> Em" by blast
                  moreover
                     {assume "\<delta>i = Em"
                      then have "extend (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>') p = (\<Gamma> + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>')" using p
                           by (auto simp add:extend_def union_ac)
                      with pms obtain m where "m \<le>n'" and "(\<Gamma> + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>',m) \<in> derivable R*"
                           using \<open>p \<in> set ps\<close> by auto
                      with IH and \<open>n = Suc n'\<close> and b' have "\<exists> m'\<le>m. (\<Gamma> + \<Gamma>i + \<Gamma>' \<Rightarrow>* \<delta>',m') \<in> derivable R*"
                           by auto
                      then have "\<exists> m\<le>n'. (extend (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                           and p and \<open>\<delta>i = Em\<close> apply (auto simp add:extend_def union_ac) 
                           by (rule_tac x="m'" in exI) auto
                     }
                  moreover
                     {assume "\<delta>i \<noteq> Em"
                      then have "extend (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>') p = (\<Gamma> + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>i)" using p
                           by (auto simp add:extend_def union_ac)
                      with pms obtain m where "m\<le>n'" and "(\<Gamma> + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>i,m) \<in> derivable R*"
                           using \<open>p \<in> set ps\<close> by auto
                      then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>i + \<Gamma>' \<Rightarrow>* \<delta>i,m) \<in> derivable R*" using \<open>n = Suc n'\<close> and b'
                           and IH
                           apply auto apply (drule_tac x=m in spec) apply auto
                           apply (drule_tac x="\<Gamma> + \<Gamma>i" in spec) apply (drule_tac x=\<delta>i in spec) 
                           apply (auto simp add:union_ac) apply (rule_tac x="m'" in exI) by auto
                      then have "\<exists> m\<le>n'. (extend (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                           and p and \<open>\<delta>i \<noteq> Em\<close> by (auto simp add:extend_def union_ac)
                     } 
                  ultimately have "\<exists> m\<le>n'. (extend (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') p, m) \<in> derivable R*" by blast
                 }
                 thus ?thesis by auto
                 qed
             then have "\<forall> p \<in> set (fst (extendRule (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') r)).
                          \<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
             moreover have "extendRule (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') r \<in> R*" using \<open>r \<in> R'\<close> and rules by auto
             moreover from \<open>S = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>')\<close> and ext and \<open>c = (\<Empt> \<Rightarrow>* Compound T Ts)\<close>
                 and \<open>r = (ps,c)\<close>
                 have "extend (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') (snd r) = (\<Gamma> + \<Gamma>' \<Rightarrow>* Compound T Ts)" by (auto simp add:extend_def union_ac)
             moreover from ext and \<open>r = (ps,c)\<close> and \<open>Ps \<noteq> []\<close> have "fst r \<noteq> []" by (auto simp add:extendRule_def)
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* Compound T Ts ,n'+1) \<in> derivable R*" using
                 derivable.step[where r="extendRule (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>') r" and m="n'" and R="R*"] 
                 by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*" using \<open>n = Suc n'\<close> and del by auto
            }
         moreover
            {assume r: "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)"
             have "Compound F Fs = Compound T Ts \<or> Compound F Fs \<noteq> Compound T Ts" by blast
             moreover
                {assume "Compound F Fs = Compound T Ts"
                 then have "leftPrincipal r (Compound F Fs)" using r and \<open>r = (ps,c)\<close> by auto
                 then have "(\<Gamma>' \<Rightarrow>* Em) \<in> set ps" using b' and \<open>r = (ps,c)\<close> and \<open>r \<in> R'\<close> and rules
                      by auto
                 then have "extend S (\<Gamma>' \<Rightarrow>* Em) \<in> set Ps" using \<open>extendRule S r = (Ps,\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close>
                      and \<open>r = (ps,c)\<close> by (simp add:extendContain)
                 moreover from r and \<open>Compound F Fs = Compound T Ts\<close> have "c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* Em)" by auto
                 with ext have "S = (\<Gamma> \<Rightarrow>* \<delta>)"
                      using \<open>r = (ps,c)\<close> apply (auto simp add:extendRule_def extend_def) by (cases S) auto
                 ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>) \<in> set Ps" by (simp add:extend_def)
                 then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*"
                      using \<open>\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*\<close> by auto
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta> ,m) \<in> derivable R*" using \<open>n = Suc n'\<close>
                      by (auto,rule_tac x=m in exI) (simp)
                }
             moreover
                {assume "Compound F Fs \<noteq> Compound T Ts"
                 obtain \<Gamma>'' \<delta>' where "S = (\<Gamma>'' \<Rightarrow>* \<delta>')" by (cases S) auto
                 with ext and r and \<open>r = (ps,c)\<close> have "\<delta> = \<delta>'" by (auto simp add:extendRule_def extend_def)
                 then have "S = (\<Gamma>'' \<Rightarrow>* \<delta>)" using \<open>S = (\<Gamma>'' \<Rightarrow>* \<delta>')\<close> by simp
                 with r and \<open>r = (ps,c)\<close> and ext have "\<Gamma> \<oplus> Compound F Fs = \<Gamma>'' \<oplus> Compound T Ts"
                      by (auto simp add:extendRule_def extend_def)
                 with \<open>Compound F Fs \<noteq> Compound T Ts\<close> obtain \<Gamma>1 where
                      gam1: "\<Gamma> = \<Gamma>1 \<oplus> Compound T Ts" and
                      gam2: "\<Gamma>'' = \<Gamma>1 \<oplus> Compound F Fs"
                      using midMultiset[where \<Gamma>=\<Gamma> and \<Gamma>'=\<Gamma>'' and A="Compound F Fs" and B="Compound T Ts"] by auto
                 with \<open>S = (\<Gamma>'' \<Rightarrow>* \<delta>)\<close> have "S = (\<Gamma>1 \<oplus> Compound F Fs \<Rightarrow>* \<delta>)" by simp
                 with derv have pms: "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 \<oplus> Compound F Fs \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" 
                      using ext and \<open>r= (ps,c)\<close> by (auto simp add:extendRule_def)
                 have "\<forall> p \<in> set ps. \<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*"
                     proof-
                     {fix p
                      assume "p \<in> set ps"
                      obtain \<Gamma>i \<delta>i where p: "p = (\<Gamma>i \<Rightarrow>* \<delta>i)" by (cases p) auto
                      have "\<delta>i = Em \<or> \<delta>i \<noteq> Em" by blast
                      moreover
                         {assume "\<delta>i = Em"
                          then have "extend (\<Gamma>1 \<oplus> Compound F Fs \<Rightarrow>* \<delta>) p = (\<Gamma>1 + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>)" using p
                               by (auto simp add:extend_def union_ac)
                          with pms obtain m where "m \<le>n'" and "(\<Gamma>1 + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>,m) \<in> derivable R*"
                               using \<open>p \<in> set ps\<close> by auto
                          with IH and \<open>n = Suc n'\<close> and b' have "\<exists> m'\<le>m. (\<Gamma>1 + \<Gamma>i + \<Gamma>' \<Rightarrow>* \<delta>,m') \<in> derivable R*"
                               by auto
                          then have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                               and p and \<open>\<delta>i = Em\<close> apply (auto simp add:extend_def union_ac) 
                               by (rule_tac x="m'" in exI) auto
                         }
                      moreover
                         {assume "\<delta>i \<noteq> Em"
                          then have "extend (\<Gamma>1 \<oplus> Compound F Fs \<Rightarrow>* \<delta>) p = (\<Gamma>1 + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>i)" using p
                               by (auto simp add:extend_def union_ac)
                          with pms obtain m where "m\<le>n'" and "(\<Gamma>1 + \<Gamma>i \<oplus> Compound F Fs \<Rightarrow>* \<delta>i,m) \<in> derivable R*"
                               using \<open>p \<in> set ps\<close> by auto
                          with IH and \<open>n = Suc n'\<close> and b' have "\<exists> m'\<le>m. (\<Gamma>1 + \<Gamma>i + \<Gamma>' \<Rightarrow>* \<delta>i,m') \<in> derivable R*"
                               by auto
                          then have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p,m) \<in> derivable R*" using \<open>m\<le>n'\<close>
                               and p and \<open>\<delta>i \<noteq> Em\<close> and \<open>n = Suc n'\<close> apply (auto simp add:extend_def union_ac)
                               apply (rule_tac x=m' in exI) by auto
                         } 
                      ultimately have "\<exists> m\<le>n'. (extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) p, m) \<in> derivable R*" by blast
                     }
                     thus ?thesis by auto
                     qed
                 then have "\<forall> p \<in> set (fst (extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r)).
                              \<exists> m\<le>n'. (p,m) \<in> derivable R*" using \<open>r = (ps,c)\<close> by (auto simp add:extendRule_def)
                 moreover have "extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r \<in> R*" using \<open>r \<in> R'\<close> and rules by auto
                 moreover from \<open>S = (\<Gamma>1 \<oplus> Compound F Fs \<Rightarrow>* \<delta>)\<close> and ext and \<open>c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* Em)\<close>
                     and gam1 and \<open>r = (ps,c)\<close>
                     have "extend (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) (snd r) = (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>)" by (auto simp add:extend_def union_ac)
                 moreover from ext and \<open>r = (ps,c)\<close> and \<open>Ps \<noteq> []\<close> have "fst r \<noteq> []" by (auto simp add:extendRule_def)
                 ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,n'+1) \<in> derivable R*" using
                     derivable.step[where r="extendRule (\<Gamma>1 + \<Gamma>' \<Rightarrow>* \<delta>) r" and m="n'" and R="R*"] 
                     by (cases r) (auto simp add:map_is_Nil_conv extendRule_def)
                 then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>,m) \<in> derivable R*" using \<open>n = Suc n'\<close> by auto
                }
            ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>, m) \<in> derivable R*" by blast
           }
       ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>, m) \<in> derivable R*" by blast
      }
   ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<delta>, m) \<in> derivable R*" by blast
   qed
qed
    


(* ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
                THIS IS NOW
                G3ip.thy
   ---------------------------------------------------
   ---------------------------------------------------
   ---------------------------------------------------
   --------------------------------------------------- *)



datatype cdi = con | dis | imp

type_synonym cdi_form = "cdi form"

abbreviation con_form (infixl "\<and>*" 80) where
   "p \<and>* q \<equiv> Compound con [p,q]"

abbreviation dis_form (infixl "\<or>*" 80) where
   "p \<or>* q \<equiv> Compound dis [p,q]"

abbreviation imp_form (infixl "\<supset>" 80) where
   "p \<supset> q  \<equiv> Compound imp [p,q]"
(*>*)
text\<open>
\noindent \textbf{G3ip} can be expressed in this formalism: 
\<close>
inductive_set "g3ip"
where
   conL(*<*)[intro](*>*):  "([\<LM> A \<RM> + \<LM> B \<RM> \<Rightarrow>* Em], \<LM> A \<and>* B \<RM> \<Rightarrow>* Em) \<in> g3ip"
|  conR(*<*)[intro](*>*):  "([\<Empt> \<Rightarrow>* A, \<Empt> \<Rightarrow>* B], \<Empt> \<Rightarrow>* (A \<and>* B)) \<in> g3ip"
|  disL(*<*)[intro](*>*):  "([\<LM> A \<RM> \<Rightarrow>* Em, \<LM> B \<RM> \<Rightarrow>* Em], \<LM> A \<or>* B\<RM> \<Rightarrow>* Em) \<in> g3ip"
|  disR1(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* A], \<Empt> \<Rightarrow>* (A \<or>* B)) \<in> g3ip"
|  disR2(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* B], \<Empt> \<Rightarrow>* (A \<or>* B)) \<in> g3ip"
|  impL(*<*)[intro](*>*):  "([\<LM> A \<supset> B \<RM> \<Rightarrow>* A, \<LM> B \<RM> \<Rightarrow>* Em], \<LM> (A \<supset> B) \<RM> \<Rightarrow>* Em) \<in> g3ip"
|  impR(*<*)[intro](*>*):  "([\<LM> A \<RM> \<Rightarrow>* B], \<Empt> \<Rightarrow>* (A \<supset> B)) \<in> g3ip"

(*<*)
lemma g3ip_upRules:
shows "g3ip \<subseteq> upRules"
proof-
  {fix r
   assume "r \<in> g3ip"
   then have "r \<in> upRules" apply (cases r) by (rule g3ip.cases) auto
  }
  then show "g3ip \<subseteq> upRules" by auto
qed
(*>*)

text\<open>\noindent As expected, $\implies{R}{}$ can be shown invertible:\<close>

lemma impRInvert:
assumes "(\<Gamma> \<Rightarrow>* (A \<supset> B), n) \<in> derivable (Ax \<union> g3ip)*" and "B \<noteq> Em"
shows "\<exists> m\<le>n. (\<Gamma> \<oplus> A \<Rightarrow>* B, m) \<in> derivable (Ax \<union> g3ip)*"
proof-
  have "\<forall> r \<in> (Ax \<union> g3ip). rightPrincipal r (A \<supset> B) \<longrightarrow> 
                           (\<LM>A\<RM> \<Rightarrow>* B) \<in> set (fst r)"
  proof-  \<comment> \<open>Showing that $A \Rightarrow B$ is a premiss of every rule with $\implies{A}{B}$ principal\<close> 
   {fix r
    assume "r \<in> (Ax \<union> g3ip)"
    moreover assume "rightPrincipal r (A \<supset> B)"
    ultimately have "r \<in> g3ip" (*<*)apply auto apply (rule rightPrincipal.cases) apply auto (*>*)by(*<*) (rule Ax.cases) (*>*) auto  \<comment> \<open>If $\implies{A}{B}$ was principal, then $r \notin Ax$\<close>
    from \<open>rightPrincipal r (A \<supset> B)\<close> have "snd r = (\<Empt> \<Rightarrow>* (A \<supset> B))" by(*<*) (rule rightPrincipal.cases)(*>*) auto
    with \<open>r \<in> g3ip\<close> and \<open>rightPrincipal r (A \<supset> B)\<close> 
        have "r = ([\<LM>A\<RM> \<Rightarrow>* B], \<Empt> \<Rightarrow>* (A\<supset>B))" (*<*) apply (cases r)(*>*) by (rule g3ip.cases) auto
    then have "(\<LM>A\<RM> \<Rightarrow>* B) \<in> set (fst r)" by auto
   }
   thus ?thesis by auto
   qed
  with assms (*<*)and g3ip_upRules(*>*) show ?thesis using rightInvertible(*<*)[where R'="g3ip" and R="Ax \<union> g3ip" and \<Gamma>=\<Gamma> and n=n
                            and \<Gamma>'="\<LM>A\<RM>" and E=B and F="imp" and Fs="[A,B]"](*>*) by auto
qed

(*<*)
end
(*>*)
