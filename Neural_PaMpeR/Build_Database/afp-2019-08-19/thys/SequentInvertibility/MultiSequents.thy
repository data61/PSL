(* Author : Peter Chapman *)
(* License: LGPL *)
(*<*)
section "Multisuccedent Sequents"

theory MultiSequents
imports "HOL-Library.Multiset"
begin
(*>*)

text\<open>
\section{Introduction}
In this paper, we give an overview of some results about invertibility in sequent calculi.  The framework is outlined in \S\ref{isadefs}.  The results are mainly concerned with multisuccedent calculi that have a single principal formula.  We will use, as our running example throughout, the calculus \textbf{G3cp}.  In \S\ref{isasingle}, we look at the formalisation of single-succedent calculi; in \S\ref{isafirstorder}, the formalisation in \textit{Nominal Isabelle} for first-order calculi is shown; in \S\ref{isamodal} the results for modal logic are examined.  We return to multisuccedent calculi in \S\ref{isaSRC} to look at manipulating rule sets.


\section{Formalising the Framework \label{isadefs}}

\subsection{Formulae and Sequents \label{isaformulae}}
A \textit{formula} is either a propositional variable, the constant $\bot$, or a connective applied to a list of formulae.  We thus have a type variable indexing formulae, where the type variable will be a set of connectives.  In the usual way, we index propositional variables by use of natural numbers.  So, formulae are given by the datatype:
\<close>

datatype 'a form = At "nat"
                        | Compound "'a" "'a form list"
                        | ff

text\<open>
\noindent For \textbf{G3cp}, we define the datatype $Gp$, and give the following abbreviations:
\<close>


(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)
(* Try a small example with conjunction and disjunction *)
datatype Gp = con | dis | imp
type_synonym Gp_form = "Gp form"

abbreviation con_form (infixl "\<and>*" 80) where
   "p \<and>* q \<equiv> Compound con [p,q]"

abbreviation dis_form (infixl "\<or>*" 80) where
   "p \<or>* q \<equiv> Compound dis [p,q]"

abbreviation imp_form (infixl "\<supset>" 80) where
   "p \<supset> q  \<equiv> Compound imp [p,q]"
(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE ENDS
   --------------------------------------------
   -------------------------------------------- *)
(*<*)
abbreviation multiset_abbrev ("\<LM> _  \<RM>" [75]75) where
   "\<LM> A \<RM> \<equiv> {# A #}"

abbreviation multiset_empty ("\<Empt>" 75) where
  "\<Empt> \<equiv> {#}"

datatype 'a sequent = Sequent "('a form) multiset" "('a form) multiset" (" (_) \<Rightarrow>* (_)" [6,6] 5)

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
(*>*)

text\<open>
\noindent A \textit{sequent} is a pair of multisets of formulae.  Sequents are indexed by the connectives used to index the formulae.  To add a single formula to a multiset of formulae, we use the symbol $\oplus$, whereas to join two multisets, we use the symbol $+$.

\subsection{Rules and Rule Sets \label{isarules}}
A \textit{rule} is a list of sequents (called the premisses) paired with a sequent (called the conclusion).  The two \textit{rule sets} used for multisuccedent calculi are the axioms, and the \SC rules (i.e. rules having one principal formula).  Both are defined as inductive sets.  There are two clauses for axioms, corresponding to $L\bot$ and normal axioms:

\<close>
inductive_set "Ax" where
   id(*<*)[intro](*>*): "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) \<in> Ax"
|  Lbot(*<*)[intro](*>*): "([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>) \<in> Ax"

text\<open>
\noindent The set of \SC rules, on the other hand, must not have empty premisses, and must have a single, compound formula in its conclusion.  The function \texttt{mset} takes a sequent, and returns the multiset obtained by adding the antecedent and the succedent together:
\<close>

(* upRules is the set of all rules which have a single conclusion.  This is akin to each rule having a 
   single principal formula.  We don't want rules to have no premisses, hence the restriction
   that ps \<noteq> [] *)
inductive_set "upRules" where
   I(*<*)[intro](*>*): "\<lbrakk> mset c \<equiv> \<LM> Compound R Fs \<RM> ; ps \<noteq> [] \<rbrakk> \<Longrightarrow> (ps,c) \<in> upRules"

text\<open>
\noindent For \textbf{G3cp}, we have the following six rules, which we then show are a subset of the set of \SC rules:
\<close>

(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)

inductive_set "g3cp"
where
    conL(*<*)[intro](*>*): "([\<LM> A \<RM> + \<LM> B \<RM> \<Rightarrow>* \<Empt>], \<LM> A \<and>* B \<RM> \<Rightarrow>* \<Empt>) \<in> g3cp"
|   conR(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* \<LM> A \<RM>, \<Empt> \<Rightarrow>* \<LM> B \<RM>], \<Empt> \<Rightarrow>* \<LM> A \<and>* B \<RM>) \<in> g3cp"
|   disL(*<*)[intro](*>*): "([\<LM> A \<RM> \<Rightarrow>* \<Empt>, \<LM> B \<RM> \<Rightarrow>* \<Empt>], \<LM> A \<or>* B\<RM> \<Rightarrow>* \<Empt>) \<in> g3cp"
|   disR(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* \<LM> A \<RM> + \<LM> B \<RM>], \<Empt> \<Rightarrow>* \<LM> A \<or>* B \<RM>) \<in> g3cp"
|   impL(*<*)[intro](*>*): "([\<Empt> \<Rightarrow>* \<LM> A \<RM>, \<LM> B \<RM> \<Rightarrow>* \<Empt>], \<LM> A \<supset> B \<RM> \<Rightarrow>* \<Empt>) \<in> g3cp"
|   impR(*<*)[intro](*>*): "([\<LM> A \<RM> \<Rightarrow>* \<LM> B \<RM>], \<Empt> \<Rightarrow>* \<LM> A \<supset> B \<RM>) \<in> g3cp"

lemma g3cp_upRules:
shows "g3cp \<subseteq> upRules"
proof-
 {
  fix ps c
  assume "(ps,c) \<in> g3cp"
  then have "(ps,c) \<in> upRules" by (induct) auto
 }
thus "g3cp \<subseteq> upRules" by auto
qed


(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE ENDS
   --------------------------------------------
   -------------------------------------------- *)

text\<open>
\noindent We have thus given the \textit{active} parts of the \textbf{G3cp} calculus.  We now need to extend these active parts with \textit{passive} parts.

Given a sequent $C$, we extend it with another sequent $S$ by adding the two antecedents and the two succedents.  To extend an active part $(Ps,C)$ with a sequent $S$, we extend every $P \in Ps$ and $C$ with $S$:
\<close>

(* Extend a sequent, and then a rule by adding seq to all premisses and the conclusion *)
overloading
  extend \<equiv> extend
  extendRule \<equiv> extendRule
begin

definition extend
  where "extend forms seq \<equiv> (antec forms + antec seq) \<Rightarrow>* (succ forms + succ seq)"

definition extendRule
  where "extendRule forms R \<equiv> (map (extend forms) (fst R), extend forms (snd R))"

end

text\<open>
\noindent Given a rule set $\mathcal{R}$, the \textit{extension} of $\mathcal{R}$, called $\mathcal{R}^{\star}$, is then defined as another inductive set:
\<close>

inductive_set extRules :: "'a rule set \<Rightarrow> 'a rule set"  ("_*")
  for R :: "'a rule set" 
  where I(*<*)[intro](*>*): "r \<in> R \<Longrightarrow> extendRule seq r \<in> R*"

text\<open>
\noindent The rules of \textbf{G3cp} all have unique conclusions.  This is easily formalised:
\<close>


(* The unique conclusion property.  A set of rules has unique conclusion property if for any pair of rules,
   the conclusions being the same means the rules are the same*)
overloading uniqueConclusion \<equiv> uniqueConclusion
begin

definition uniqueConclusion :: "'a rule set \<Rightarrow> bool"
  where "uniqueConclusion R \<equiv> \<forall> r1 \<in> R. \<forall> r2 \<in> R. (snd r1 = snd r2) \<longrightarrow> (r1 = r2)"

end

(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)
lemma g3cp_uc:
shows "uniqueConclusion g3cp"
apply (auto simp add:uniqueConclusion_def Ball_def)
apply (rule g3cp.cases) apply auto by (rotate_tac 1,rule g3cp.cases,auto)+
(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE ENDS
   --------------------------------------------
   -------------------------------------------- *)
(*<*)
(* A formulation of what it means to be a principal formula for a rule.  Note that we have to build up from
   single conclusion rules.   *)

inductive leftPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up[intro]: "C = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)  \<Longrightarrow> 
                   leftPrincipal (Ps,C) (Compound F Fs)"

(*>*)

text\<open>
\subsection{Principal Rules and Derivations \label{isaderv}}
A formula $A$ is \textit{left principal} for an active part $R$ iff the conclusion of $R$ is of the form $A \Rightarrow \emptyset$.  The definition of \textit{right principal} is then obvious.  We have an inductive predicate to check these things:
\<close>

inductive rightPrincipal :: "'a rule \<Rightarrow> 'a form \<Rightarrow> bool"
  where
  up(*<*)[intro](*>*): "C = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<Longrightarrow> 
                        rightPrincipal (Ps,C) (Compound F Fs)"

text\<open>
\noindent As an example, we show that if $A\wedge B$ is principal for an active part in \textbf{G3cp}, then $\emptyset \Rightarrow A$ is a premiss of that active part:
\<close>

(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)

lemma principal_means_premiss:
assumes a: "rightPrincipal r (A \<and>* B)"
and     b: "r \<in> g3cp"
shows      "(\<Empt> \<Rightarrow>* \<LM> A \<RM>) \<in> set (fst r)"
proof-
    from a and b obtain Ps where req: "r = (Ps, \<Empt> \<Rightarrow>* \<LM> A\<and>*B \<RM>)" 
         by (cases r) auto
    with b have "Ps = [\<Empt> \<Rightarrow>* \<LM> A \<RM>, \<Empt> \<Rightarrow>* \<LM> B \<RM>]"
         apply (cases r) by (rule g3cp.cases) auto
    with req show "(\<Empt> \<Rightarrow>* \<LM> A \<RM>) \<in> set (fst r)" by auto
qed



(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE ENDS
   --------------------------------------------
   -------------------------------------------- *)



(* What it means to be a derivable sequent.  Can have this as a predicate or as a set.
   The two formation rules say that the supplied premisses are derivable, and the second says
   that if all the premisses of some rule are derivable, then so is the conclusion.  *)

text\<open>
\noindent A sequent is \textit{derivable} at height $0$ if it is the conclusion of a rule with no premisses.  If a rule has $m$ premisses, and the maximum height of the derivation of any of the premisses is $n$, then the conclusion will be derivable at height $n+1$.  We encode this as pairs of sequents and natural numbers.  A sequent $S$ is derivable at a height $n$ in a rule system $\mathcal{R}$ iff $(S,n)$ belongs to the inductive set \texttt{derivable} $\mathcal{R}$:
\<close>

inductive_set derivable :: "'a rule set \<Rightarrow> 'a deriv set"
  for R :: "'a rule set"
  where
   base(*<*)[intro](*>*): "\<lbrakk>([],C) \<in> R\<rbrakk> \<Longrightarrow> (C,0) \<in> derivable R"
|  step(*<*)[intro](*>*):  "\<lbrakk> r \<in> R ; (fst r)\<noteq>[] ; \<forall> p \<in> set (fst r). \<exists> n \<le> m. (p,n) \<in> derivable R \<rbrakk> 
                       \<Longrightarrow> (snd r,m + 1) \<in> derivable R"

text\<open>
\noindent In some instances, we do not care about the height of a derivation, rather that the root is derivable.  For this, we have the additional definition of \texttt{derivable'}, which is a set of sequents:
\<close>

(* When we don't care about height! *)
inductive_set derivable' :: "'a rule set \<Rightarrow> 'a sequent set"
   for R :: "'a rule set"
   where
    base(*<*)[intro](*>*): "\<lbrakk> ([],C) \<in> R \<rbrakk> \<Longrightarrow> C \<in> derivable' R"
|   step(*<*)[intro](*>*):  "\<lbrakk> r \<in> R ; (fst r) \<noteq> [] ; \<forall> p \<in> set (fst r). p \<in> derivable' R \<rbrakk>
                       \<Longrightarrow> (snd r) \<in> derivable' R"

text\<open>
\noindent It is desirable to switch between the two notions.  Shifting from derivable at a height to derivable is simple: we delete the information about height.  The converse is more complicated and involves an induction on the length of the premiss list:
\<close>

lemma deriv_to_deriv(*<*)[simp](*>*):
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
  with step(3) have aa: "\<forall> p \<in> set ps. \<exists> n. (p,n) \<in> derivable R" by auto
  then have "\<exists> m. \<forall> p \<in> set ps. \<exists> n\<le>m. (p,n) \<in> derivable R"
  proof (induct ps) \<comment> \<open>induction on the list\<close>
    case Nil
    then show ?case by auto
  next
    case (Cons a as)
    then have "\<exists> m. \<forall> p \<in> set as. \<exists> n\<le>m. (p,n) \<in> derivable R" by auto
    then obtain m where "\<forall> p \<in> set as. \<exists> n\<le>m. (p,n) \<in> derivable R" by auto
    moreover from \<open>\<forall> p \<in> set (a # as). \<exists> n. (p,n) \<in> derivable R\<close> have
      "\<exists> n. (a,n) \<in> derivable R" by auto
    then obtain m' where "(a,m') \<in> derivable R" by blast
    ultimately have "\<forall> p \<in> set (a # as). \<exists> n\<le>(max m m'). (p,n) \<in> derivable R" 

(*<*)
      apply (auto simp add:Ball_def)
      apply (rule_tac x=m' in exI) apply simp
      apply (drule_tac x=x in spec) apply auto(*>*) by (*<*)(rule_tac x=n in exI)(*>*) auto \<comment> \<open>max returns the maximum of two integers\<close>
    then show ?case by blast
  qed
  then obtain m where "\<forall> p \<in> set ps. \<exists> n\<le>m. (p,n) \<in> derivable R" by blast
  with \<open>r = (ps,c)\<close> and \<open>r \<in> R\<close> have "(c,m+1) \<in> derivable R" using \<open>ps \<noteq> []\<close> and
    derivable.step[where r="(ps,c)" and R=R and m=m] by auto
  then show ?case using \<open>r = (ps,c)\<close> by auto
qed
(*<*)
(* definition of invertible rule and invertible set of rules.  It's a bit nasty, but all it really says is
   If a rule is in the given set, and if any extension of that rule is derivable at n, then the
   premisses of the extended rule are derivable at height at most n.  *)





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
     using extend_def[where forms="\<Gamma> \<ominus> At i \<Rightarrow>* \<Delta> \<ominus> At i" and seq="\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>"] by auto
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


(* -------------------------------------------
   -------------------------------------------
       THIS IS NOW INVERTIBLERULESPOLY.THY
   -------------------------------------------
   ------------------------------------------- *)

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
(*>*)

text\<open>
\section{Formalising the Results \label{isaproofs}}
A variety of ``helper'' lemmata are used in the proofs, but they are not shown.  The proof tactics themselves are hidden in the following proof, except where they are interesting.  Indeed, only the interesting parts of the proof are shown at all.  The main result of this section is that a rule is invertible if the premisses appear as premisses of \textit{every} rule with the same principal formula.  The proof is interspersed with comments.
\<close>

lemma rightInvertible:
fixes \<Gamma> \<Delta> :: "'a form multiset"
assumes rules: "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
  and   a: "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs,n) \<in> derivable R*"
  and   b: "\<forall> r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> 
            (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
using assms
txt\<open>
\noindent The height of derivations is decided by the length of the longest branch.  Thus, we need to use
strong induction: i.e. $\forall m\leq n.\ \textrm{If } P(m) \textrm{ then } P(n+1)$.
\<close>
proof (induct n arbitrary:\<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs, m) \<in> derivable R* \<longrightarrow>
                   (\<forall>r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> 
                   ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
                   (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. rightPrincipal r' (Compound F Fs) \<longrightarrow> 
                        (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)   \<comment> \<open>Case analysis on $n$\<close>
     case 0
 (*<*)    then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs,0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs) \<and> (r \<in> Ax \<or> r \<in> R')"
          using rules and ruleSet[where R'=R' and R=R and Ps="[]" and C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs"] by auto(*>*)
     then obtain r S where "extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)" 
                   and "r \<in> Ax \<or> r \<in> R'" by auto  \<comment> \<open>At height 0, the premisses are empty\<close>
      moreover
      {assume "r \<in> Ax"
       then obtain i where "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = r \<or> 
                             r = ([], \<LM> ff \<RM> \<Rightarrow>* \<Empt>)" 
            using characteriseAx[where r=r] by auto
          moreover \<comment> \<open>Case split on the kind of axiom used\<close>
          {assume "r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>)"
 (*<*)         with \<open>extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close>
                have "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)"
                using extendRule_def[where R="([],\<LM>At i\<RM>\<Rightarrow>*\<LM>At i\<RM>)" and forms=S] by auto (*>*)
          then have "At i \<in># \<Gamma> \<and> At i \<in># \<Delta>" (*<*)using extendID[where S=S and i=i and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> Compound F Fs"](*>*) by auto
           then have "At i \<in># \<Gamma> + \<Gamma>' \<and> At i \<in># \<Delta> + \<Delta>'" by auto
           then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules (*<*)
                and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R](*>*) by auto
          }
          moreover
          {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
 (*<*)          with \<open>extendRule S r = ([],\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close>
                have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)"
                using extendRule_def[where R="([],\<LM>ff\<RM>\<Rightarrow>*\<Empt>)" and forms=S] by auto (*>*)
          then have "ff \<in># \<Gamma>" (*<*)using extendFalsum[where S=S and \<Gamma>=\<Gamma> and \<Delta>="\<Delta> \<oplus> Compound F Fs"](*>*)  by auto
           then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
           then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules (*<*)
                and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R](*>*) by auto
          }
          ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" by blast
      }
      moreover
      {assume "r \<in> R'" \<comment> \<open>This leads to a contradiction\<close>
 (*<*)      then have "r \<in> upRules" using rules by auto
       then have "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)"
            proof-
            obtain x y where "r = (x,y)" by (cases r)
            with \<open>r \<in> upRules\<close> have "(x,y) \<in> upRules" by simp
            then obtain Ps where "(Ps :: 'a sequent list) \<noteq> []" and "x=Ps" by (cases) (auto)
            with \<open>r = (x,y)\<close> have "r = (Ps, y)" by simp
            then show "\<exists> Ps C. Ps \<noteq> [] \<and> r = (Ps,C)" using \<open>Ps \<noteq> []\<close> by blast
            qed (*>*)
      then obtain Ps C where "Ps \<noteq> []" and "r = (Ps,C)" by auto
       moreover (*<*) from \<open>extendRule S r = ([], \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close> have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then(*>*) obtain S where "r = ([],S)" by blast   \<comment> \<open>Contradiction\<close>
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules by simp
       }
       ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" (*<*)using \<open>n=0\<close> (*>*) by blast
(*<*)next (*>*)
txt\<open>\noindent In the case where $n = n' + 1$ for some $n'$, we know the premisses are empty,
and every premiss is derivable at a height lower than $n'$:\<close>
  case (Suc n')
  then have "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs,n'+1) \<in> derivable R*" using a' by simp
  then obtain Ps where "(Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs) \<in> R*" and 
                       "Ps \<noteq> []" and 
                       "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*" (*<*)
       using characteriseLast[where C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs" and m=n' and R="R*"](*>*) by auto
 (*<*)    then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)"
          using rules and ruleSet[where R'=R' and R=R and Ps=Ps and C="\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs"] by auto (*>*)
  then obtain r S where "r \<in> Ax \<or> r \<in> R'"  
                  and "extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)" by auto
  moreover
     {assume "r \<in> Ax"   \<comment> \<open>Gives a contradiction\<close>
      then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
      moreover obtain x y where "r = (x,y)" by (cases r)
      then have "x \<noteq> []" using \<open>Ps \<noteq> []\<close>
                    and \<open>extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close> (*<*)
                          and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] (*>*)by auto
      ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" (*<*)
              using \<open>r=(x,y)\<close>(*>*)  by auto
     }
  moreover
     {assume "r \<in> R'"
      obtain ps c where "r = (ps,c)" by (cases r) auto
  (*<*)       then have "r \<in> upRules" using rules and \<open>r \<in> R'\<close> by auto (*>*)
      have "(rightPrincipal r (Compound F Fs)) \<or> 
                \<not>(rightPrincipal r (Compound F Fs))" 
      by blast  \<comment> \<open>The formula is principal, or not\<close>
    (*<*)  moreover (*>*)
txt\<open>\noindent If the formula is principal, then $\Gamma' \Rightarrow \Delta'$ is amongst the premisses of $r$:\<close>
  {assume "rightPrincipal r (Compound F Fs)"
   then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' (*<*)and \<open>r = (ps,c)\<close> and \<open>r \<in> R'\<close> and rules(*>*)
        by auto
   then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" 
        using \<open>extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close>
      (*<*)  and \<open>r = (ps,c)\<close>(*>*) by (simp(*<*) add:extendContain(*>*))
   moreover (*<*)from \<open>rightPrincipal r (Compound F Fs)\<close> have "c = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)" 
        using \<open>r = (ps,c)\<close> by (cases) auto
   with \<open>extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close>(*>*) have "S = (\<Gamma> \<Rightarrow>* \<Delta>)" (*<*)
        using \<open>r = (ps,c)\<close> apply (auto simp add:extendRule_def extend_def)(*>*) by (cases S) auto
   ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
   then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
       using \<open>\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*\<close> by auto
   then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" (*<*)using \<open>n = Suc n'\<close>(*>*) by (auto(*<*),rule_tac x=m in exI) (simp(*>*))
  }
(*<*) moreover (*>*)
txt\<open>\noindent If the formula is not principal, then it must appear in the premisses.  The first two lines give a characterisation of the extension and conclusion, respectively.  Then, we apply the induction hypothesis
at the lower height of the premisses:\<close>
  {assume "\<not> rightPrincipal r (Compound F Fs)"
   obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)   
   then obtain G H where "c = (G \<Rightarrow>* H)" by (cases c) (auto)  
   then have "\<LM> Compound F Fs \<RM> \<noteq> H"   \<comment> \<open>Proof omitted\<close>
 (*<*)                 proof-
                  from \<open>r = (ps,c)\<close> and \<open>r \<in> upRules\<close>
                     obtain T Ts where  "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                     using upRuleCharacterise[where Ps=ps and C=c] by auto
                  moreover
                     {assume "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
                      then have "rightPrincipal r (Compound T Ts)" using \<open>r = (ps,c)\<close> by auto
                      with \<open>\<not> rightPrincipal r (Compound F Fs)\<close> have "Compound T Ts \<noteq> Compound F Fs" by auto
                      then have "\<LM>Compound F Fs\<RM> \<noteq> H" using \<open>c = (G \<Rightarrow>* H)\<close> and \<open>c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)\<close> by auto
                     }
                  moreover
                     {assume "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                      then have "\<LM>Compound F Fs\<RM> \<noteq> H" using \<open>c = (G \<Rightarrow>* H)\<close> by auto
                     }
                  ultimately show "\<LM>Compound F Fs\<RM> \<noteq> H" by blast
                  qed 
             moreover have "succ S + succ (snd r) = (\<Delta> \<oplus> Compound F Fs)" 
                         using \<open>extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close>
                         and extendRule_def[where forms=S and R=r]
                         and extend_def[where forms=S and seq="snd r"] by auto
   then (*>*) have "\<Psi> + H = \<Delta> \<oplus> Compound F Fs" 
        using \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close> and \<open>r = (ps,c)\<close> and \<open>c = (G \<Rightarrow>* H)\<close> by auto
   moreover from \<open>r = (ps,c)\<close> and \<open>c = (G \<Rightarrow>* H)\<close> (*<*)and \<open>r \<in> upRules\<close> (*>*)
   
   have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)"(*<*)
            using succ_upRule[where Ps=ps and \<Phi>=G and \<Psi>=H](*>*) by auto
   ultimately have "Compound F Fs \<in># \<Psi>"   \<comment> \<open>Proof omitted\<close>
 (*<*)                proof-
                 have "H = \<Empt> \<or> (\<exists> A. H = \<LM>A\<RM>)" by fact
                 moreover
                    {assume "H = \<Empt>"
                     then have "\<Psi> = \<Delta> \<oplus> Compound F Fs" using \<open>\<Psi> + H = \<Delta> \<oplus> Compound F Fs\<close> by auto
                     then have "Compound F Fs \<in># \<Psi>" by auto
                    }
                 moreover
                    {assume "\<exists> A. H = \<LM>A\<RM>"
                     then obtain A where "H = \<LM>A\<RM>" by auto
                     then have "\<Psi> \<oplus> A = \<Delta> \<oplus> Compound F Fs" using \<open>\<Psi> + H = \<Delta> \<oplus> Compound F Fs\<close> by auto
                     then have "set_mset (\<Psi> \<oplus> A) = set_mset (\<Delta> \<oplus> Compound F Fs)" by auto
                     then have "set_mset \<Psi> \<union> {A} = set_mset \<Delta> \<union> {Compound F Fs}" by auto
                     moreover from \<open>H = \<LM>A\<RM>\<close> and \<open>\<LM>Compound F Fs\<RM> \<noteq> H\<close> have "Compound F Fs \<noteq> A" by auto
                     ultimately have "Compound F Fs \<in> set_mset \<Psi>" by auto
                     then have "Compound F Fs \<in># \<Psi>" by auto
                    }
                 ultimately show "Compound F Fs \<in># \<Psi>" by blast
                 qed (*>*)
  then have "\<exists> \<Psi>1. \<Psi> = \<Psi>1 \<oplus> Compound F Fs" by (*<*)(rule_tac x="\<Psi> \<ominus> Compound F Fs" in exI)(*>*) (auto(*<*) simp add:multiset_eq_iff(*>*))
  then obtain \<Psi>1 where "S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs)"(*<*) using \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close>(*>*) by auto
 (*<*)           have "Ps = map (extend S) ps" 
                 using \<open>extendRule S r = (Ps,\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close> 
                 and extendRule_def[where forms=S and R=r] and \<open>r = (ps,c)\<close> by auto
            then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
  then (*>*) have "\<forall> p \<in> set Ps. (Compound F Fs \<in># succ p)"  \<comment> \<open>Appears in every premiss\<close>
                 (*<*)     using \<open>Compound F Fs \<in># \<Psi>\<close> and \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close> apply (auto simp add:Ball_def) (*>*)
         by (*<*)(drule_tac x=x in spec)(*>*) (auto(*<*) simp add:extend_def(*>*))
  (*<*)          then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs)" using characteriseSeq
                      apply (auto simp add:Ball_def) apply (drule_tac x=x in spec,simp) 
                      apply (rule_tac x="antec x" in exI,rule_tac x="succ x \<ominus> Compound F Fs" in exI) 
                      by (drule_tac x=x in meta_spec) (auto simp add:multiset_eq_iff)
            moreover have "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by fact
            ultimately have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs,n) \<in> derivable R*
                                                     \<and> p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs)"
                 by (auto simp add:Ball_def) (*>*)
 then have (*<*)a2:(*>*) "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> 
                                   (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable R* \<and>
                                   p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs)" using (*<*)\<open>n = Suc n'\<close> and b' and (*>*)IH(*<*)
                 apply (auto simp add:Ball_def) apply (drule_tac x=x in spec) apply simp
                 apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                 apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                 apply (simp) apply (elim exE)(*>*) by(*<*) (rule_tac x=m' in exI)(*>*) (arith) 
txt\<open>\noindent  To this set of new premisses, we apply a new instance of $r$, with a different extension:\<close>           
  obtain Ps' where eq: "Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps" by auto
  (*<*)          have "length Ps = length Ps'" using \<open>Ps' = map (extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>')) ps\<close>
                                            and \<open>Ps = map (extend S) ps\<close> by auto
            then have "Ps' \<noteq> []" using \<open>Ps \<noteq> []\<close> by auto
            from \<open>r \<in> R'\<close> have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r \<in> R*" using rules by auto
            moreover have "extendRule (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
                 using \<open>S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs)\<close> and \<open>extendRule S r = (Ps, \<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)\<close> 
                 and \<open>r = (ps,c)\<close> and eq
                 by (auto simp add:extendRule_def extend_def)
  ultimately(*>*) have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*" by simp
  (*<*)          have c1:"\<forall> p \<in> set ps. extend S p \<in> set Ps" using \<open>Ps = map (extend S) ps\<close> by (simp add:Ball_def)           
            have c2:"\<forall> p \<in> set ps. extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p \<in> set Ps'" using eq
                 by (simp add:Ball_def)
            then have eq2:"\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq
                 by (auto simp add: extend_def) 
            have d1:"\<forall> p \<in> set Ps. \<exists> p' \<in> set ps. p = extend S p'" using \<open>Ps = map (extend S) ps\<close>
                 by (auto simp add:Ball_def Bex_def)
            then have "\<forall> p \<in> set Ps. \<exists> p'. p' \<in> set Ps'" using c2 
                 by (auto simp add:Ball_def Bex_def)
            moreover have d2: "\<forall> p \<in> set Ps'. \<exists> p' \<in> set ps. p = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p'" using eq
                 by (auto simp add:Ball_def Bex_def)
            then have "\<forall> p \<in> set Ps'. \<exists> p'. p' \<in> set Ps" using c1
                 by (auto simp add:Ball_def Bex_def) 
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) \<in> set Ps \<longrightarrow> 
                            (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) \<in> set Ps"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs) p = (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs)"
                      using \<open>Ps = map (extend S) ps\<close> and \<open>S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs)\<close> and a1 and d1
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x=" \<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs" in spec)
                           by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs) p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain A B where "p = (A \<Rightarrow>* B)" by (cases p) 
                 then have "(A \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs) (A \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' = \<Phi> + A" and suc: "\<Psi>' \<oplus> Compound F Fs = \<Psi>1 \<oplus> Compound F Fs + B" 
                      using extend_def[where forms="\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs" and seq="A \<Rightarrow>* B"] by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + \<Gamma>') + A" by (auto simp add:union_ac)
                 moreover
                 from suc have "\<Psi>' = \<Psi>1 + B" by auto
                 then have "\<Psi>' + \<Delta>' = (\<Psi>1 + \<Delta>') + B" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (A \<Rightarrow>* B)" 
                      using extend_def[where forms="\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>'" and seq="A \<Rightarrow>* B"] by auto
                 moreover have "extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (A \<Rightarrow>* B) \<in> set Ps'" using \<open>p = (A \<Rightarrow>* B)\<close> and t and c2 by auto
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                 }
                 thus ?thesis by blast
               qed
            moreover
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) \<in> set Ps"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')"
                      using eq and eq2 and d2
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec)
                           by (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain A B where "p = (A \<Rightarrow>* B)" by (cases p) 
                 then have "(A \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>') (A \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' + \<Gamma>' = \<Phi> + \<Gamma>' + A" and suc: "\<Psi>' + \<Delta>' = \<Psi>1 + \<Delta>' + B" 
                      using extend_def[where forms="\<Phi> + \<Gamma>' \<Rightarrow>* \<Psi>1 + \<Delta>'" and seq="A \<Rightarrow>* B"] by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi> + A) + \<Gamma>'" by (auto simp add:union_ac)
                 then have "\<Phi>' = \<Phi> + A" by simp
                 moreover
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi>1 + B) + \<Delta>'" by (auto simp add:union_ac)
                 then have "\<Psi>' = \<Psi>1 + B" by simp
                 then have "\<Psi>' \<oplus> Compound F Fs = (\<Psi>1 \<oplus> Compound F Fs) + B" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) = extend (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs) (A \<Rightarrow>* B)" 
                      using extend_def[where forms="\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs" and seq="A\<Rightarrow>*B"] by auto
                 moreover have "extend (\<Phi>  \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs) (A \<Rightarrow>* B) \<in> set Ps" using \<open>p = (A \<Rightarrow>* B)\<close> and t and c1
                      and \<open>S = (\<Phi> \<Rightarrow>* \<Psi>1 \<oplus> Compound F Fs)\<close> by auto
                 ultimately have "(\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) \<in> set Ps" by simp
                 }
                 thus ?thesis by blast
               qed
            ultimately
            have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs) \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
            then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable R*
                                                \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
                 apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=x in spec) apply simp
                 apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
                 by (drule_tac x="\<Phi>' \<Rightarrow>* \<Psi>' \<oplus> Compound F Fs" in spec) (simp) (*>*)
  then have "\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by auto
  then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" 
    using (*<*)\<open>n = Suc n'\<close> and \<open>Ps' \<noteq> []\<close>
    and(*>*) \<open>(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*\<close> (*<*)
       and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="R*"](*>*)
 by (auto(*<*) simp add:Ball_def Bex_def(*>*))
  (*<*)          }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast         
        }(*>*)
 txt\<open>\noindent All of the cases are now complete.\<close>
 ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
 (*<*)  qed (*>*)
qed
(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)
text\<open>
As an example, we show the left premiss of $R\wedge$ in \textbf{G3cp} is derivable at a height not greater than that of the conclusion.  The two results used in the proof (\texttt{principal-means-premiss} and \texttt{rightInvertible}) are those we have previously shown:
\<close>

lemma conRInvert:
assumes "(\<Gamma> \<Rightarrow>* \<Delta> \<oplus> (A \<and>* B),n) \<in> derivable (g3cp \<union> Ax)*"
shows "\<exists> m\<le>n. (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> A,m) \<in> derivable (g3cp \<union> Ax)*"
proof-
have "\<forall> r \<in> g3cp. rightPrincipal r (A \<and>* B) \<longrightarrow> (\<Empt> \<Rightarrow>* \<LM> A \<RM>) \<in> set (fst r)"
     using principal_means_premiss by auto
with assms show ?thesis using rightInvertible(*<*)[where R'="g3cp" and \<Gamma>'="\<Empt>" and \<Delta>'="\<LM> A \<RM>" 
                           and R="g3cp \<union> Ax"](*>*) by (auto(*<*) simp add:Un_commute Ball_def nonPrincipalID g3cp_upRules(*>*))
qed
(* --------------------------------------------
   --------------------------------------------
             G3cp EXAMPLE ENDS
   --------------------------------------------
   -------------------------------------------- *)

text\<open>
\noindent  We can obviously show the equivalent proof for left rules, too:
\<close>

lemma leftInvertible:
fixes \<Gamma> \<Delta> :: "'a form multiset"
assumes rules: "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
  and   a: "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>,n) \<in> derivable R*"
  and   b: "\<forall> r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
shows "\<exists> m\<le>n. (\<Gamma> +\<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
(*<*)
using assms
proof (induct n arbitrary:\<Gamma> \<Delta> rule:nat_less_induct)
 case (1 n \<Gamma> \<Delta>)
 then have IH:"\<forall>m<n. \<forall>\<Gamma> \<Delta>. ( \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>, m) \<in> derivable R* \<longrightarrow>
              (\<forall>r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> ( \<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')) \<longrightarrow>
              (\<exists>m'\<le>m. ( \<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>', m') \<in> derivable R*)" 
     and a': "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>,n) \<in> derivable R*" 
     and b': "\<forall> r' \<in> R. leftPrincipal r' (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')"
       by auto
 show ?case
 proof (cases n)
     case 0
     then have "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>,0) \<in> derivable R*" using a' by simp
     then have "([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>) \<in> R*" by (cases) (auto)
     then have "\<exists> r S. extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>) \<and> (r \<in> Ax \<or> r \<in> R')"
          using rules and ruleSet[where Ps="[]" and C="\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>" and R'=R' and R=R] by (auto)
     then obtain r S where "extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)" and "r \<in> Ax \<or> r \<in> R'" by auto
      moreover
      {assume "r \<in> Ax"
       then obtain i where "([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = r \<or> r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
            using characteriseAx[where r=r] by auto
          moreover
          {assume "r = ([], \<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>)"
           with \<open>extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close>
                have "extend S (\<LM> At i \<RM> \<Rightarrow>* \<LM> At i \<RM>) = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)"
                using extendRule_def[where R="([],\<LM>At i\<RM>\<Rightarrow>*\<LM>At i\<RM>)" and forms=S] by auto
           then have "At i \<in># \<Gamma> \<and> At i \<in># \<Delta>" using extendID[where S=S and i=i and \<Gamma>="\<Gamma> \<oplus> Compound F Fs" and \<Delta>=\<Delta>] by auto
           then have "At i \<in># \<Gamma> + \<Gamma>' \<and> At i \<in># \<Delta> + \<Delta>'" by auto
           then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                and containID[where \<Gamma>="\<Gamma> + \<Gamma>'" and i=i and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
          }
          moreover
          {assume "r = ([],\<LM>ff\<RM> \<Rightarrow>* \<Empt>)"
           with \<open>extendRule S r = ([],\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close>
                have "extend S (\<LM> ff \<RM> \<Rightarrow>* \<Empt>) = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)"
                using extendRule_def[where R="([],\<LM>ff\<RM>\<Rightarrow>*\<Empt>)" and forms=S] by auto
           then have "ff \<in># \<Gamma>" using extendFalsum[where S=S and \<Gamma>="\<Gamma>\<oplus>Compound F Fs" and \<Delta>=\<Delta>] by auto
           then have "ff \<in># \<Gamma> + \<Gamma>'" by auto
           then have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" using rules
                and containFalsum[where \<Gamma>="\<Gamma> + \<Gamma>'" and \<Delta>="\<Delta> + \<Delta>'" and R=R] by auto
          }
          ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" by blast       
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
       moreover from \<open>extendRule S r = ([], \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close> have "\<exists> S. r = ([],S)"
            using extendRule_def[where forms=S and R=r] by (cases r) (auto)
       then obtain S where "r = ([],S)" by blast
       ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',0) \<in> derivable R*" by simp
       }
       ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using \<open>n=0\<close> by blast
 next
     case (Suc n')
     then have "(\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>,n'+1) \<in> derivable R*" using a' by simp
     then obtain Ps where "(Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>) \<in> R*" and 
                          "Ps \<noteq> []" and 
                          "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*"
          using characteriseLast[where C="\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>" and m=n' and R="R*"] by auto
     then have "\<exists> r S. (r \<in> Ax \<or> r \<in> R') \<and> extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)"
          using rules ruleSet[where R'=R' and R=R and Ps=Ps and C="\<Gamma>\<oplus> Compound F Fs \<Rightarrow>* \<Delta>"] by auto
     then obtain r S where "r \<in> Ax \<or> r \<in> R'" and "extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)" by auto
     moreover
        {assume "r \<in> Ax"
         then have "fst r = []" apply (cases r) by (rule Ax.cases) auto
         moreover obtain x y where "r = (x,y)" by (cases r)
         then have "x \<noteq> []" using \<open>Ps \<noteq> []\<close> and \<open>extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close>
                            and extendRule_def[where forms=S and R=r]
                            and extend_def[where forms=S and seq="snd r"] by auto
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
              using \<open>r=(x,y)\<close> by auto
        }
     moreover
        {assume "r \<in> R'"
         obtain ps c where "r = (ps,c)" by (cases r) auto
         then have "r \<in> upRules" using rules and \<open>r \<in> R'\<close> by auto
         have "(leftPrincipal r (Compound F Fs)) \<or> \<not>(leftPrincipal r (Compound F Fs))" by blast
         moreover
            {assume "leftPrincipal r (Compound F Fs)"
             then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set ps" using b' and \<open>r = (ps,c)\<close> and \<open>r \<in> R'\<close> and rules
                  by auto
             then have "extend S (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set Ps" using \<open>extendRule S r = (Ps,\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close>
                  and \<open>r = (ps,c)\<close> by (simp add:extendContain)
             moreover from \<open>leftPrincipal r (Compound F Fs)\<close> have "c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)"
                  using  \<open>r = (ps,c)\<close> by (cases) auto
             with \<open>extendRule S r = (Ps,\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close> have "S = (\<Gamma> \<Rightarrow>* \<Delta>)"
                  using \<open>r = (ps,c)\<close> apply (auto simp add:extendRule_def extend_def) by (cases S) auto
             ultimately have "(\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> set Ps" by (simp add:extend_def)
             then have "\<exists> m\<le>n'. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*"
                  using \<open>\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*\<close> by auto
             then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using \<open>n = Suc n'\<close>
                  by (auto,rule_tac x=m in exI) (simp)
            }
         moreover
            {assume "\<not> leftPrincipal r (Compound F Fs)"
             obtain \<Phi> \<Psi> where "S = (\<Phi> \<Rightarrow>* \<Psi>)" by (cases S) (auto)
             then obtain G H where "c = (G \<Rightarrow>* H)" by (cases c) (auto)
             then have "\<LM> Compound F Fs \<RM> \<noteq> G" 
                  proof-
                  from \<open>r = (ps,c)\<close> and \<open>r \<in> upRules\<close>
                     obtain T Ts where  "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>) \<or> c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                     using upRuleCharacterise[where Ps=ps and C=c] by auto
                  moreover
                     {assume "c = (\<Empt> \<Rightarrow>* \<LM>Compound T Ts\<RM>)"
                      then have "\<LM>Compound F Fs\<RM> \<noteq> G" using \<open>c = (G \<Rightarrow>* H)\<close> by auto   
                     }
                  moreover
                     {assume "c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)"
                      then have "leftPrincipal r (Compound T Ts)" using \<open>r = (ps,c)\<close> by auto
                      with \<open>\<not> leftPrincipal r (Compound F Fs)\<close> have "Compound T Ts \<noteq> Compound F Fs" by auto
                      then have "\<LM>Compound F Fs\<RM> \<noteq> G" using \<open>c = (G \<Rightarrow>* H)\<close> and \<open>c = (\<LM>Compound T Ts\<RM> \<Rightarrow>* \<Empt>)\<close> by auto
                     }
                  ultimately show "\<LM>Compound F Fs\<RM> \<noteq> G" by blast
                  qed
             moreover have "antec S + antec (snd r) = (\<Gamma> \<oplus> Compound F Fs)" 
                         using \<open>extendRule S r = (Ps,\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close>
                         and extendRule_def[where forms=S and R=r]
                         and extend_def[where forms=S and seq="snd r"] by auto
             then have "\<Phi> + G = \<Gamma> \<oplus> Compound F Fs" using \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close> and \<open>r = (ps,c)\<close> and \<open>c = (G \<Rightarrow>* H)\<close> by auto
             moreover from \<open>r = (ps,c)\<close> and \<open>c = (G\<Rightarrow>* H)\<close> and \<open>r \<in> upRules\<close> have "G = \<Empt> \<or> (\<exists> A. G = \<LM>A\<RM>)"
                      using antec_upRule[where Ps=ps and \<Phi>=G and \<Psi>=H] by auto
             ultimately have "Compound F Fs \<in># \<Phi>"
                 proof-
                 have "G = \<Empt> \<or> (\<exists> A. G = \<LM>A\<RM>)" by fact
                 moreover
                    {assume "G = \<Empt>"
                     then have "\<Phi> = \<Gamma> \<oplus> Compound F Fs" using \<open>\<Phi> + G = \<Gamma> \<oplus> Compound F Fs\<close> by auto
                     then have "Compound F Fs \<in># \<Phi>" by auto
                    }
                 moreover
                    {assume "\<exists> A. G = \<LM>A\<RM>"
                     then obtain A where "G = \<LM>A\<RM>" by auto
                     then have "\<Phi> \<oplus> A = \<Gamma> \<oplus> Compound F Fs" using \<open>\<Phi> + G = \<Gamma> \<oplus> Compound F Fs\<close> by auto
                     then have "set_mset (\<Phi> \<oplus> A) = set_mset (\<Gamma> \<oplus> Compound F Fs)" by auto
                     then have "set_mset \<Phi> \<union> {A} = set_mset \<Gamma> \<union> {Compound F Fs}" by auto
                     moreover from \<open>G = \<LM>A\<RM>\<close> and \<open>\<LM>Compound F Fs\<RM> \<noteq> G\<close> have "Compound F Fs \<noteq> A" by auto
                     ultimately have "Compound F Fs \<in> set_mset \<Phi>" by auto
                     then have "Compound F Fs \<in># \<Phi>" by auto
                    }
                 ultimately show "Compound F Fs \<in># \<Phi>" by blast
                 qed
            then have "\<exists> \<Phi>1. \<Phi> = \<Phi>1 \<oplus> Compound F Fs" 
                 by (rule_tac x="\<Phi> \<ominus> Compound F Fs" in exI) (auto simp add:multiset_eq_iff)
            then obtain \<Phi>1 where "S = (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>)" using \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close> by auto
            have "Ps = map (extend S) ps" 
                 using \<open>extendRule S r = (Ps,\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close> 
                 and extendRule_def[where forms=S and R=r] and \<open>r = (ps,c)\<close> by auto
            then have "\<forall> p \<in> set Ps. (\<exists> p'. p = extend S p')" using ex_map_conv[where ys=Ps and f="extend S"] by auto
            then have "\<forall> p \<in> set Ps. (Compound F Fs \<in># antec p)" 
                      using \<open>Compound F Fs \<in># \<Phi>\<close> and \<open>S = (\<Phi> \<Rightarrow>* \<Psi>)\<close> apply (auto simp add:Ball_def) 
                      by (drule_tac x=x in spec) (auto simp add:extend_def)
            then have a1:"\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>')" using characteriseSeq
                      apply (auto simp add:Ball_def) apply (drule_tac x=x in spec,simp) 
                      apply (rule_tac x="antec x \<ominus> Compound F Fs" in exI,rule_tac x="succ x" in exI) 
                      by (drule_tac x=x in meta_spec) (auto simp add:multiset_eq_iff)
            moreover have "\<forall> p \<in> set Ps. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by fact
            ultimately have "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>',n) \<in> derivable R*
                                                     \<and> p = (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>')"
                 by (auto simp add:Ball_def)
            then have a2: "\<forall> p \<in> set Ps. \<exists> \<Phi>' \<Psi>' m. m\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',m) \<in> derivable R*
                                                   \<and> p = (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>')"
                 using \<open>n = Suc n'\<close> and b' and IH
                 apply (auto simp add:Ball_def) apply (drule_tac x=x in spec) apply simp
                 apply (elim exE conjE) apply (drule_tac x=n in spec) apply simp
                 apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)
                 apply (simp) apply (elim exE) by (rule_tac x=m' in exI) (arith)
            obtain Ps' where eq: "Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps" by auto
            have "length Ps = length Ps'" using \<open>Ps' = map (extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>')) ps\<close>
                                            and \<open>Ps = map (extend S) ps\<close> by auto
            then have "Ps' \<noteq> []" using \<open>Ps \<noteq> []\<close> by auto
            from \<open>r \<in> R'\<close> have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r \<in> R*" using rules by auto
            moreover have "extendRule (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') r = (Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')"
                 using \<open>S = (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>)\<close> and \<open>extendRule S r = (Ps, \<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)\<close> 
                 and \<open>r = (ps,c)\<close> and eq
                 by (auto simp add:extendRule_def extend_def)
            ultimately have "(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*" by simp
            have c1:"\<forall> p \<in> set ps. extend S p \<in> set Ps" using \<open>Ps = map (extend S) ps\<close> by (simp add:Ball_def)           
            have c2:"\<forall> p \<in> set ps. extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p \<in> set Ps'" using eq
                 by (simp add:Ball_def)
            then have eq2:"\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>'. p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq
                 by (auto simp add: extend_def)
            have d1:"\<forall> p \<in> set Ps. \<exists> p' \<in> set ps. p = extend S p'" using \<open>Ps = map (extend S) ps\<close>
                 by (auto simp add:Ball_def Bex_def)
            then have "\<forall> p \<in> set Ps. \<exists> p'. p' \<in> set Ps'" using c2 
                 by (auto simp add:Ball_def Bex_def)
            moreover have d2: "\<forall> p \<in> set Ps'. \<exists> p' \<in> set ps. p = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p'" using eq
                 by (auto simp add:Ball_def Bex_def)
            then have "\<forall> p \<in> set Ps'. \<exists> p'. p' \<in> set Ps" using c1
                 by (auto simp add:Ball_def Bex_def)
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') \<in> set Ps \<longrightarrow> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') \<in> set Ps"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>) p = (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>')"
                      using \<open>Ps = map (extend S) ps\<close> and \<open>S = (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>)\<close> and a1 and d1
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x="\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>'" in spec)
                           by (drule_tac x="\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>'" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>) p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain A B where "p = (A \<Rightarrow>* B)" by (cases p) 
                 then have "(A \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>) (A \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' \<oplus> Compound F Fs = \<Phi>1 \<oplus> Compound F Fs + A" and suc: "\<Psi>' = \<Psi> + B"
                      using extend_def[where forms="\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>" and seq="A\<Rightarrow>*B"] by auto
                 from ant have "\<Phi>' = \<Phi>1 + A" by auto
                 then have "\<Phi>' + \<Gamma>' = (\<Phi>1 + \<Gamma>') + A" by (auto simp add:union_ac)
                 moreover
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi> + \<Delta>') + B" by (auto simp add:union_ac)
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (A \<Rightarrow>* B)" 
                      using extend_def[where forms="\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>'" and seq="A \<Rightarrow>* B"] by auto
                 moreover have "extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (A \<Rightarrow>* B) \<in> set Ps'" using \<open>p = (A \<Rightarrow>* B)\<close> and t and c2 by auto
                 ultimately have "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'" by simp
                 }
                 thus ?thesis by blast
               qed
            moreover
            have "\<forall> \<Phi>' \<Psi>'. (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps' \<longrightarrow> (\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') \<in> set Ps"
               proof-
                 {fix \<Phi>' \<Psi>'
                 assume "(\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps'"  
                 then have "\<exists> p \<in> set ps. extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')"
                      using eq and eq2 and d2
                           apply (simp only:Ball_def Bex_def) apply (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec)
                           by (drule_tac x="\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>'" in spec) (auto)
                 then obtain p where t:"p \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') p"
                      apply auto by (drule_tac x=p in meta_spec) (simp)
                 then obtain A B where "p = (A \<Rightarrow>* B)" by (cases p) 
                 then have "(A \<Rightarrow>* B) \<in> set ps \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') = extend (\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>') (A \<Rightarrow>* B)"
                      using t by auto
                 then have ant: "\<Phi>' + \<Gamma>' = \<Phi>1 + \<Gamma>' + A" and suc: "\<Psi>' + \<Delta>' = \<Psi> + \<Delta>' + B" 
                      using extend_def[where forms="\<Phi>1 + \<Gamma>' \<Rightarrow>* \<Psi> + \<Delta>'" and seq="A \<Rightarrow>* B"] by auto
                 from ant have "\<Phi>' + \<Gamma>' = (\<Phi>1 + A) + \<Gamma>'" by (auto simp add:union_ac)
                 then have "\<Phi>' = \<Phi>1 + A" by simp
                 then have "\<Phi>' \<oplus> Compound F Fs = (\<Phi>1 \<oplus> Compound F Fs) + A" by (auto simp add:union_ac)
                 moreover
                 from suc have "\<Psi>' + \<Delta>' = (\<Psi> + B) + \<Delta>'" by (auto simp add:union_ac)
                 then have "\<Psi>' = \<Psi> + B" by simp
                 ultimately have "(\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') = extend (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>) (A \<Rightarrow>* B)" 
                      using extend_def[where forms="\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>" and seq="A\<Rightarrow>*B"] by auto
                 moreover have "extend (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>) (A \<Rightarrow>* B) \<in> set Ps" using \<open>p = (A \<Rightarrow>* B)\<close> and t and c1
                      and \<open>S = (\<Phi>1 \<oplus> Compound F Fs \<Rightarrow>* \<Psi>)\<close> by auto
                 ultimately have "(\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') \<in> set Ps" by simp
                 }
                 thus ?thesis by blast
               qed
            ultimately
            have "\<forall> \<Phi>' \<Psi>'. ((\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>') \<in> set Ps) = ((\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>') \<in> set Ps')" by auto
            then have "\<forall> p \<in> set Ps'. \<exists> \<Phi>' \<Psi>' n. n\<le>n' \<and> (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>',n) \<in> derivable R*
                                                \<and> p = (\<Phi>' + \<Gamma>' \<Rightarrow>* \<Psi>' + \<Delta>')" using eq2 and a2
                 apply (simp add:Ball_def) apply (intro allI impI) apply (drule_tac x=x in spec) apply simp
                 apply (elim exE) apply (drule_tac x=\<Phi>' in spec,drule_tac x=\<Psi>' in spec)  
                 by (drule_tac x="\<Phi>' \<oplus> Compound F Fs \<Rightarrow>* \<Psi>'" in spec) (simp)
            then have all:"\<forall> p \<in> set Ps'. \<exists> n\<le>n'. (p,n) \<in> derivable R*" by auto
            then have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" using \<open>n = Suc n'\<close>
                 and \<open>(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>') \<in> R*\<close> and \<open>Ps' \<noteq> []\<close>
                 and derivable.step[where r="(Ps',\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" and R="R*"]
                 by (auto simp add:Ball_def Bex_def)
            }
         ultimately have "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast         
        }
      ultimately show "\<exists> m\<le>n. (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>',m) \<in> derivable R*" by blast
  qed
qed



lemma invertibleRule:
assumes rules: "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
   and UC:     "uniqueConclusion R'"
   and IN:     "(Ps,C) \<in> R*"
   and der:    "(C,n) \<in> derivable R*"
shows "\<forall> p \<in> set Ps. \<exists> m\<le>n. (p,m) \<in> derivable R*"
proof-
  from IN have "\<exists> r' S. (r' \<in> Ax \<or> r' \<in>  R') \<and> (Ps,C) = extendRule S r'" 
    using rules and ruleSet[where R'=R' and R=R and Ps=Ps and C=C]
    apply (auto) apply (rule_tac x=a in exI,rule_tac x=b in exI) apply simp apply (rule_tac x=S in exI) apply (simp)
    apply (rule_tac x=a in exI,rule_tac x=b in exI) apply simp by (rule_tac x=S in exI) simp
  then obtain r' S where "r' \<in> Ax \<or> r' \<in> R'" and "(Ps,C) = extendRule S r'" by blast
  then obtain \<Gamma> \<Delta> where gam1:"S = (\<Gamma> \<Rightarrow>* \<Delta>)" by (cases S) auto
  have "r' \<in> Ax \<or> r' \<in> R'" by fact
  moreover
  {assume "r' \<in> Ax"
    then have "Ps = []" using characteriseAx[where r=r'] and \<open>(Ps,C) = extendRule S r'\<close> 
      and extendRule_def[where forms=S and R=r'] by auto
    then have "\<forall> p \<in> set Ps. \<exists> m\<le>n. (p,m) \<in> derivable R*" by (auto simp add:Ball_def)
  }
  moreover
  {assume "r' \<in> R'"
    {fix P
      assume "P \<in> set Ps"
      from \<open>r' \<in> R'\<close> have "r' \<in> upRules" using rules by auto
      then obtain ps c where "r' = (ps,c)" by (cases r') (auto)
      then have "\<exists> p \<in> set ps. P = extend S p" using \<open>P \<in> set Ps\<close> and \<open>(Ps,C) = extendRule S r'\<close>
        by (auto simp add:extendRule_def extend_def)
      then obtain p where "p \<in> set ps" and "P = extend S p" by auto
      then obtain \<Gamma>' \<Delta>' where "p = (\<Gamma>' \<Rightarrow>* \<Delta>')" using characteriseSeq[where C=p] by auto
      then have P: "P = (\<Gamma> + \<Gamma>' \<Rightarrow>* \<Delta> + \<Delta>')" using gam1 and \<open>P = extend S p\<close> by (auto simp add:extend_def)    
      then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')" using \<open>p \<in> set ps\<close> and \<open>r' = (ps,c)\<close> and \<open>p = (\<Gamma>' \<Rightarrow>* \<Delta>')\<close> by auto
      from \<open>r'=(ps,c)\<close> have "\<exists> F Fs. c = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" 
        using \<open>r' \<in> upRules\<close> and upRuleCharacterise[where Ps=ps and C=c] by auto
      then obtain F Fs where "c = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>) \<or> c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" by auto
      moreover
      {assume "c = (\<Empt> \<Rightarrow>* \<LM> Compound F Fs \<RM>)"          
        with \<open>c= (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)\<close> and \<open>(Ps,C) = extendRule S r'\<close> and \<open>r' = (ps,c)\<close> and gam1
        have gam2:"C = (\<Gamma> \<Rightarrow>* \<Delta> \<oplus> Compound F Fs)"
          using extendRule_def[where forms=S and R=r'] and extend_def[where forms=S and seq=c]
          by simp
        with \<open>c = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)\<close> have "rightPrincipal r' (Compound F Fs)"  
          using \<open>r' = (ps,c)\<close> by auto
        then have a1:"\<forall> r \<in> R'. rightPrincipal r (Compound F Fs) \<longrightarrow> r = r'" using \<open>uniqueConclusion R'\<close>
        proof-
          {fix r
            assume "r \<in> R'" then have "r \<in> upRules" using \<open>R' \<subseteq> upRules \<and> R = Ax \<union> R'\<close> by auto
            assume "rightPrincipal r (Compound F Fs)"
            obtain ps' c' where "r = (ps',c')" by (cases r) auto
            with \<open>rightPrincipal r (Compound F Fs)\<close> have "c' = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)"
              by (cases) auto
            then have "c' = c" using \<open>c = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)\<close> by simp
            then have "r = r'" using \<open>uniqueConclusion R'\<close> and \<open>r \<in> R'\<close> and \<open>r' \<in> R'\<close>
              and \<open>r'=(ps,c)\<close> and \<open>r = (ps',c')\<close>
              by (simp add:uniqueConclusion_def Ball_def)
          }
          thus ?thesis by (auto simp add:Ball_def)
        qed
        with \<open>p \<in> set ps\<close> and \<open>r' = (ps,c)\<close> and \<open>(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')\<close>
        have b1:"\<forall> r \<in> R'. rightPrincipal r (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r)" by blast
        have "\<forall> r \<in> R. rightPrincipal r (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r)"
        proof-               
          {fix t
            assume "t \<in> R" and "rightPrincipal t (Compound F Fs)"
            then obtain pss d where "t = (pss,d)" by (cases t) auto
            with \<open>rightPrincipal t (Compound F Fs)\<close> have rP:"d = (\<Empt> \<Rightarrow>* \<LM>Compound F Fs\<RM>)" by (cases) auto
            from \<open>t \<in> R\<close> have split:"t \<in> Ax \<or> t \<in> R'" using rules by auto
            moreover
            {assume "t \<in> Ax"
              then obtain i where "d = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>) \<or> d = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
                using characteriseAx[where r=t] and \<open>t = (pss,d)\<close> by auto
              then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" using rP by auto
            }
            moreover
            {assume "t \<in> R'"
              with \<open>rightPrincipal t (Compound F Fs)\<close> have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" using b1 and \<open>t \<in> R'\<close> by auto
            }
            ultimately have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" by blast
          }
          then show ?thesis by auto
        qed
        then have "\<exists> m\<le>n. (P,m) \<in> derivable R*" using rules and gam1 and gam2 and P
          and rightInvertible[where R'=R' and R=R and F=F and Fs=Fs and n=n and \<Gamma>=\<Gamma> and \<Gamma>'=\<Gamma>' and \<Delta>=\<Delta> and \<Delta>'=\<Delta>']
          and IN and der by auto 
      }
      moreover
      {assume "c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)"          
        with \<open>c= (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)\<close> and \<open>(Ps,C) = extendRule S r'\<close> and \<open>r' = (ps,c)\<close> and gam1
        have gam3:"C = (\<Gamma> \<oplus> Compound F Fs \<Rightarrow>* \<Delta>)"
          using extendRule_def[where forms=S and R=r'] and extend_def[where forms=S and seq=c]
          by simp
        with \<open>c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)\<close> have "leftPrincipal r' (Compound F Fs)" 
          using \<open>r' = (ps,c)\<close> and \<open>r' \<in> R'\<close> by auto
        then have a1:"\<forall> r \<in> R'. leftPrincipal r (Compound F Fs) \<longrightarrow> r = r'" using \<open>uniqueConclusion R'\<close>
        proof-
          {fix r
            assume "r \<in> R'" then have "r \<in> upRules" using \<open>R' \<subseteq> upRules \<and> R = Ax \<union> R'\<close> by auto
            assume "leftPrincipal r (Compound F Fs)"
            obtain ps' c' where "r = (ps',c')" by (cases r) auto
            with \<open>leftPrincipal r (Compound F Fs)\<close> have "c' = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)" by (cases) auto
            then have "c' = c" using \<open>c = (\<LM>Compound F Fs\<RM> \<Rightarrow>* \<Empt>)\<close> by simp
            then have "r = r'" using \<open>uniqueConclusion R'\<close> and \<open>r \<in> R'\<close> and \<open>r' \<in> R'\<close>
              and \<open>r'=(ps,c)\<close> and \<open>r = (ps',c')\<close>
              by (simp add:uniqueConclusion_def Ball_def)
          }
          thus ?thesis by (auto simp add:Ball_def)
        qed
        with \<open>p \<in> set ps\<close> and \<open>r' = (ps,c)\<close> and \<open>(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r')\<close>
        have b1:"\<forall> r \<in> R'. leftPrincipal r (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r)" by blast
        have "\<forall> r \<in> R. leftPrincipal r (Compound F Fs) \<longrightarrow> (\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst r)"
        proof-               
          {fix t
            assume "t \<in> R" and "leftPrincipal t (Compound F Fs)"
            then obtain pss d where "t = (pss,d)" by (cases t) auto
            with \<open>leftPrincipal t (Compound F Fs)\<close> have rP:"antec d = \<LM>Compound F Fs\<RM>" by (cases) auto
            from \<open>t \<in> R\<close> have split:"t \<in> Ax \<or> t \<in> R'" using rules by (cases) auto
            moreover
            {assume "t \<in> Ax"
              then obtain i where "d = (\<LM>At i\<RM> \<Rightarrow>* \<LM>At i\<RM>) \<or> d = (\<LM>ff\<RM> \<Rightarrow>* \<Empt>)" 
                using characteriseAx[where r=t] and \<open>t = (pss,d)\<close> by auto
              then have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" using rP by auto
            }
            moreover
            {assume "t \<in> R'"
              with \<open>leftPrincipal t (Compound F Fs)\<close> have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" using b1 and \<open>t \<in> R'\<close> by auto
            }
            ultimately have "(\<Gamma>' \<Rightarrow>* \<Delta>') \<in> set (fst t)" by blast
          }
          then show ?thesis by auto
        qed
        then have "\<exists> m\<le>n. (P,m) \<in> derivable R*" using rules and gam1 and gam3 and P
          and leftInvertible[where R'=R' and R=R and F=F and Fs=Fs and n=n and \<Gamma>=\<Gamma> and \<Gamma>'=\<Gamma>' and \<Delta>=\<Delta> and \<Delta>'=\<Delta>']
          and IN and der by auto
      }
      ultimately have "\<exists> m\<le>n. (P,m) \<in> derivable R*" by blast
    }
    then have "\<forall> p \<in> set Ps. \<exists> m\<le>n. (p,m) \<in> derivable R*" by auto
  }
  ultimately show "\<forall> p \<in> set Ps. \<exists> m\<le>n. (p,m) \<in> derivable R*" by blast
qed

(*>*)

text\<open>
A rule is invertible iff every premiss is derivable at a height lower than that of the conclusion.  A set of rules is invertible iff every rule is invertible.  These definitions are easily formalised:\<close>

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

text\<open>
\noindent A set of multisuccedent \SC rules is invertible if each rule has a different conclusion.  \textbf{G3cp} has the unique conclusion property (as shown in \S\ref{isarules}).  Thus, \textbf{G3cp} is an invertible set of rules:
\<close>

lemma unique_to_invertible:
assumes (*<*)a:(*>*) "R' \<subseteq> upRules \<and> R = Ax \<union> R'"
   and  "uniqueConclusion R'"
shows "invertible_set R"
(*<*)
using assms invertibleRule
  apply (auto simp add:invertible_set_def invertible_def)
  apply (drule_tac x=R' in meta_spec) apply (drule_tac x=R in meta_spec)
  apply (drule_tac x="fst (extendRule S (a,b))" in meta_spec)
  apply (drule_tac x="snd (extendRule S (a,b))" in meta_spec)
  apply (drule_tac x=n in meta_spec)
  apply (simp add:a extRules.intros)
  apply (drule_tac x=R' in meta_spec) apply (drule_tac x=R in meta_spec)
  apply (drule_tac x="fst (extendRule S (a,b))" in meta_spec)
  apply (drule_tac x="snd (extendRule S (a,b))" in meta_spec)
  apply (drule_tac x=n in meta_spec)
by (simp add:a extRules.intros)
(*>*)
(* --------------------------------------------
   --------------------------------------------
               G3cp EXAMPLE
   --------------------------------------------
   -------------------------------------------- *)

lemma g3cp_invertible:
shows "invertible_set (Ax \<union> g3cp)"
using g3cp_uc and g3cp_upRules
   and unique_to_invertible[where R'="g3cp" and R="Ax \<union> g3cp"] 
by auto

text\<open>
\subsection{Conclusions}
For \SC multisuccedent calculi, the theoretical results have been formalised.  Moreover, the running example demonstrates that it is straightforward to implement such calculi and reason about them.  Indeed, it will be this class of calculi for which we will prove more results in \S\ref{isaSRC}.
\<close>
(*<*)
end
(*>*)
