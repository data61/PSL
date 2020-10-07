subsection\<open>Semantics\<close>
theory Sema
imports Formulas
begin

type_synonym 'a valuation = "'a \<Rightarrow> bool"
text\<open>The implicit statement here is that an assignment or valuation is always defined on all atoms (because HOL is a total logic).
Thus, there are no unsuitable assignments.\<close>

primrec formula_semantics :: "'a valuation \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
"\<A> \<Turnstile> Atom k = \<A> k" |
"_ \<Turnstile> \<bottom> = False" |
"\<A> \<Turnstile> Not F = (\<not> \<A> \<Turnstile> F)" |
"\<A> \<Turnstile> And F G = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)" |
"\<A> \<Turnstile> Or F G = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)" |
"\<A> \<Turnstile> Imp F G = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"

abbreviation valid ("\<Turnstile> _" 51) where
"\<Turnstile> F \<equiv> \<forall>A. A \<Turnstile> F"

lemma irrelevant_atom[simp]: "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F; simp)
lemma relevant_atoms_same_semantics: "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  by(induction F; simp)

context begin
text\<open>Just a definition more similar to~\cite[p. 5]{schoening1987logik}.
Unfortunately, using this as the main definition would get in the way of automated reasoning all the time.\<close>
private primrec formula_semantics_alt where
"formula_semantics_alt \<A> (Atom k) = \<A> k" |
"formula_semantics_alt \<A> (Bot) = False" |
"formula_semantics_alt \<A> (Not a) = (if formula_semantics_alt \<A> a then False else True)" |
"formula_semantics_alt \<A> (And a b) = (if formula_semantics_alt \<A> a then formula_semantics_alt \<A> b else False)" |
"formula_semantics_alt \<A> (Or a b) = (if formula_semantics_alt \<A> a then True else formula_semantics_alt \<A> b)" |
"formula_semantics_alt \<A> (Imp a b) = (if formula_semantics_alt \<A> a then formula_semantics_alt \<A> b else True)"
private lemma "formula_semantics_alt \<A> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F; simp)

text\<open>If you fancy a definition more similar to~\cite[p. 39]{gallier2015logic},
this is probably the closest you can go without going incredibly ugly.\<close>
private primrec formula_semantics_tt where
"formula_semantics_tt \<A> (Atom k) = \<A> k" |
"formula_semantics_tt \<A> (Bot) = False" |
"formula_semantics_tt \<A> (Not a) = (case formula_semantics_tt \<A> a of True \<Rightarrow> False | False \<Rightarrow> True)" |
"formula_semantics_tt \<A> (And a b) = (case (formula_semantics_tt \<A> a, formula_semantics_tt \<A> b) of
  (False, False) \<Rightarrow> False
| (False, True) \<Rightarrow> False
| (True, False) \<Rightarrow> False
| (True, True) \<Rightarrow> True)" |
"formula_semantics_tt \<A> (Or a b) = (case (formula_semantics_tt \<A> a, formula_semantics_tt \<A> b) of
  (False, False) \<Rightarrow> False
| (False, True) \<Rightarrow> True
| (True, False) \<Rightarrow> True
| (True, True) \<Rightarrow> True)" |
"formula_semantics_tt \<A> (Imp a b) = (case (formula_semantics_tt \<A> a, formula_semantics_tt \<A> b) of
  (False, False) \<Rightarrow> True
| (False, True) \<Rightarrow> True
| (True, False) \<Rightarrow> False
| (True, True) \<Rightarrow> True)"
private lemma "A \<Turnstile> F \<longleftrightarrow> formula_semantics_tt A F"
  by(induction F; simp split: prod.splits bool.splits)
end

definition entailment :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>/ _)" (* \TTurnstile *) [53,53] 53) where
"\<Gamma> \<TTurnstile> F \<equiv> (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> F)))"
text\<open>We write entailment differently than semantics (\<open>\<Turnstile>\<close> vs. \<open>\<TTurnstile>\<close>).
For humans, it is usually pretty clear what is meant in a specific situation, 
but it often needs to be decided from context that Isabelle/HOL does not have.\<close>
  
text\<open>Some helpers for the derived connectives\<close>
lemma top_semantics[simp,intro!]: "A \<Turnstile> \<top>" unfolding Top_def by simp
lemma BigAnd_semantics[simp]: "A \<Turnstile> \<^bold>\<And>F \<longleftrightarrow> (\<forall>f \<in> set F. A \<Turnstile> f)" by(induction F; simp)
lemma BigOr_semantics[simp]: "A \<Turnstile> \<^bold>\<Or>F \<longleftrightarrow> (\<exists>f \<in> set F. A \<Turnstile> f)" by(induction F; simp)
    
text\<open>Definitions for sets of formulae, used for compactness and model existence.\<close>

definition "sat S \<equiv> \<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"
definition "fin_sat S \<equiv> (\<forall>s \<subseteq> S. finite s \<longrightarrow> sat s)"
  
lemma entail_sat: "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" (* btw. *)
  unfolding sat_def entailment_def by simp

lemma pn_atoms_updates: "p \<notin> snd (pn_atoms F) \<Longrightarrow> n \<notin> fst (pn_atoms F) \<Longrightarrow>
  ((M \<Turnstile> F \<longrightarrow> (M(p := True) \<Turnstile> F \<and> M(n := False) \<Turnstile> F))) \<and> ((\<not>(M \<Turnstile> F)) \<longrightarrow> \<not>(M(n := True) \<Turnstile> F) \<and> \<not>(M(p := False) \<Turnstile> F))"
proof(induction F arbitrary: n p)
  case (Imp F G)
  from Imp.prems have prems:
     "p \<notin> fst (pn_atoms F)" "p \<notin> snd (pn_atoms G)"
     "n \<notin> snd (pn_atoms F)" "n \<notin> fst (pn_atoms G)"
    by(simp_all add: prod_unions_def split: prod.splits)
  have IH1: "M \<Turnstile> F \<Longrightarrow> M(n := True) \<Turnstile> F" " M \<Turnstile> F \<Longrightarrow> M(p := False) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(p := True) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(n := False) \<Turnstile> F"
    using Imp.IH(1)[OF prems(3) prems(1)] by blast+
  have IH2: "M \<Turnstile> G \<Longrightarrow> M(p := True) \<Turnstile> G" "M \<Turnstile> G \<Longrightarrow> M(n := False) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(n := True) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(p := False) \<Turnstile> G" 
    using Imp.IH(2)[OF prems(2) prems(4)] by blast+
   show ?case proof(intro conjI; intro impI)
     assume "M \<Turnstile> F \<^bold>\<rightarrow> G"
     then consider "\<not> M \<Turnstile> F" | "M \<Turnstile>G" by auto
     thus "M(p := True) \<Turnstile> F \<^bold>\<rightarrow> G \<and> M(n := False) \<Turnstile> F \<^bold>\<rightarrow> G" using IH1(3,4) IH2(1,2) by cases simp_all
   next
     assume "\<not>(M \<Turnstile> F \<^bold>\<rightarrow> G)"
     hence "M \<Turnstile> F" "\<not>M \<Turnstile> G" by simp_all
     thus "\<not> M(n := True) \<Turnstile> F \<^bold>\<rightarrow> G \<and> \<not> M(p := False) \<Turnstile> F \<^bold>\<rightarrow> G" using IH1(1,2) IH2(3,4) by simp
   qed
 next
  case (And F G)
  from And.prems have prems:
     "p \<notin> snd (pn_atoms F)" "p \<notin> snd (pn_atoms G)"
     "n \<notin> fst (pn_atoms F)" "n \<notin> fst (pn_atoms G)"
    by(simp_all add: prod_unions_def split: prod.splits)
  have IH1: "M \<Turnstile> F \<Longrightarrow> M(p := True) \<Turnstile> F" " M \<Turnstile> F \<Longrightarrow> M(n := False) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(n := True) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(p := False) \<Turnstile> F"
    using And.IH(1)[OF prems(1) prems(3)] by blast+
  have IH2: "M \<Turnstile> G \<Longrightarrow> M(p := True) \<Turnstile> G" "M \<Turnstile> G \<Longrightarrow> M(n := False) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(n := True) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(p := False) \<Turnstile> G" 
    using And.IH(2)[OF prems(2) prems(4)] by blast+
  show ?case proof(intro conjI; intro impI)
    assume "\<not>M \<Turnstile> F \<^bold>\<and> G"
    then consider "\<not> M \<Turnstile> F" | "\<not> M \<Turnstile>G" by auto
    thus "\<not> M(n := True) \<Turnstile> F \<^bold>\<and> G \<and> \<not> M(p := False) \<Turnstile> F \<^bold>\<and> G" using IH1 IH2 by cases simp_all
  next
    assume "M \<Turnstile> F \<^bold>\<and> G"
    hence "M \<Turnstile> F" "M \<Turnstile> G" by simp_all
    thus "M(p := True) \<Turnstile> F \<^bold>\<and> G \<and> M(n := False) \<Turnstile> F \<^bold>\<and> G " using IH1 IH2 by simp
  qed
next
  case (Or F G)
  from Or.prems have prems:
     "p \<notin> snd (pn_atoms F)" "p \<notin> snd (pn_atoms G)"
     "n \<notin> fst (pn_atoms F)" "n \<notin> fst (pn_atoms G)"
    by(simp_all add: prod_unions_def split: prod.splits)
  have IH1: "M \<Turnstile> F \<Longrightarrow> M(p := True) \<Turnstile> F" " M \<Turnstile> F \<Longrightarrow> M(n := False) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(n := True) \<Turnstile> F" "\<not> M \<Turnstile> F \<Longrightarrow> \<not> M(p := False) \<Turnstile> F"
    using Or.IH(1)[OF prems(1) prems(3)] by blast+
  have IH2: "M \<Turnstile> G \<Longrightarrow> M(p := True) \<Turnstile> G" "M \<Turnstile> G \<Longrightarrow> M(n := False) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(n := True) \<Turnstile> G" "\<not> M \<Turnstile> G \<Longrightarrow> \<not> M(p := False) \<Turnstile> G" 
    using Or.IH(2)[OF prems(2) prems(4)] by blast+
  show ?case proof(intro conjI; intro impI)
    assume "M \<Turnstile> F \<^bold>\<or> G"
    then consider "M \<Turnstile> F" | "M \<Turnstile>G" by auto
    thus "M(p := True) \<Turnstile> F \<^bold>\<or> G \<and> M(n := False) \<Turnstile> F \<^bold>\<or> G" using IH1 IH2 by cases simp_all
  next
    assume "\<not>M \<Turnstile> F \<^bold>\<or> G"
    hence "\<not>M \<Turnstile> F" "\<not>M \<Turnstile> G" by simp_all
    thus "\<not>M(n := True) \<Turnstile> F \<^bold>\<or> G \<and> \<not>M(p := False) \<Turnstile> F \<^bold>\<or> G " using IH1 IH2 by simp
  qed
qed simp_all
  
lemma const_simplifier_correct: "\<A> \<Turnstile> simplify_consts F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F) (auto simp add: Let_def isstop_def Top_def split: formula.splits) 
 
end
