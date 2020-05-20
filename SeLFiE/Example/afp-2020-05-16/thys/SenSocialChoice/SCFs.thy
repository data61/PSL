(*
 * Social Choice Functions (SCFs).
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced July 2006.
 * License: BSD
 *)

(*<*)
theory SCFs

imports RPRs

begin
(*>*)

(* **************************************** *)

subsection\<open>Choice Sets, Choice Functions\<close>

text\<open>A \emph{choice set} is the subset of @{term "A"} where every element
of that subset is (weakly) preferred to every other element of @{term "A"}
with respect to a given RPR. A \emph{choice function} yields a non-empty
choice set whenever @{term "A"} is non-empty.\<close>

definition choiceSet :: "'a set \<Rightarrow> 'a RPR \<Rightarrow> 'a set" where
  "choiceSet A r \<equiv> { x \<in> A . \<forall>y \<in> A. x \<^bsub>r\<^esub>\<preceq> y }"

definition choiceFn :: "'a set \<Rightarrow> 'a RPR \<Rightarrow> bool" where
  "choiceFn A r \<equiv> \<forall>A' \<subseteq> A. A' \<noteq> {} \<longrightarrow> choiceSet A' r \<noteq> {}"

lemma choiceSetI[intro]:
  "\<lbrakk> x \<in> A; \<And>y. y \<in> A \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<rbrakk> \<Longrightarrow> x \<in> choiceSet A r"
  unfolding choiceSet_def by simp

lemma choiceFnI[intro]:
  "(\<And>A'. \<lbrakk> A' \<subseteq> A; A' \<noteq> {} \<rbrakk> \<Longrightarrow> choiceSet A' r \<noteq> {}) \<Longrightarrow> choiceFn A r"
  unfolding choiceFn_def by simp

text\<open>If a complete and reflexive relation is also \emph{quasi-transitive}
it will yield a choice function.\<close>

definition quasi_trans :: "'a RPR \<Rightarrow> bool" where
  "quasi_trans r \<equiv> \<forall>x y z. x \<^bsub>r\<^esub>\<prec> y \<and> y \<^bsub>r\<^esub>\<prec> z \<longrightarrow> x \<^bsub>r\<^esub>\<prec> z"

lemma quasi_transI[intro]:
  "(\<And>x y z. \<lbrakk> x \<^bsub>r\<^esub>\<prec> y; y \<^bsub>r\<^esub>\<prec> z \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> z) \<Longrightarrow> quasi_trans r"
  unfolding quasi_trans_def by blast

lemma quasi_transD: "\<lbrakk> x \<^bsub>r\<^esub>\<prec> y; y \<^bsub>r\<^esub>\<prec> z; quasi_trans r \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> z"
  unfolding quasi_trans_def by blast

lemma trans_imp_quasi_trans: "trans r \<Longrightarrow> quasi_trans r"
  by (rule quasi_transI, unfold strict_pref_def trans_def, blast)

lemma r_c_qt_imp_cf:
  assumes finiteA: "finite A"
      and c: "complete A r"
      and qt: "quasi_trans r"
      and r: "refl_on A r"
  shows "choiceFn A r"
proof
  fix B assume B: "B \<subseteq> A" "B \<noteq> {}"
  with finite_subset finiteA have finiteB: "finite B" by auto
  from finiteB B show "choiceSet B r \<noteq> {}"
  proof(induct rule: finite_subset_induct')
    case empty with B show ?case by auto
  next
    case (insert a B)
    hence finiteB: "finite B"
        and aA: "a \<in> A"
        and AB: "B \<subseteq> A"
        and aB: "a \<notin> B"
        and cF: "B \<noteq> {} \<Longrightarrow> choiceSet B r \<noteq> {}" by - blast
    show ?case
    proof(cases "B = {}")
      case True with aA r show ?thesis
        unfolding choiceSet_def by blast
    next
      case False
      with cF obtain b where bCF: "b \<in> choiceSet B r" by blast
      from AB aA bCF complete_refl_on[OF c r]
      have "a \<^bsub>r\<^esub>\<prec> b \<or> b \<^bsub>r\<^esub>\<preceq> a" unfolding choiceSet_def strict_pref_def by blast
      thus ?thesis
      proof
        assume ab: "b \<^bsub>r\<^esub>\<preceq> a"
        with bCF show ?thesis unfolding choiceSet_def by auto
      next
        assume ab: "a \<^bsub>r\<^esub>\<prec> b"
        have "a \<in> choiceSet (insert a B) r"
        proof(rule ccontr)
          assume aCF: "a \<notin> choiceSet (insert a B) r"
          from aB have "\<And>b. b \<in> B \<Longrightarrow> a \<noteq> b" by auto
          with aCF aA AB c r obtain b' where B: "b' \<in> B" "b' \<^bsub>r\<^esub>\<prec> a"
            unfolding choiceSet_def complete_def strict_pref_def by blast
          with ab qt have "b' \<^bsub>r\<^esub>\<prec> b" by (blast dest: quasi_transD)
          with bCF B show False unfolding choiceSet_def strict_pref_def by blast
        qed
        thus ?thesis by auto
      qed
    qed
  qed
qed

lemma rpr_choiceFn: "\<lbrakk> finite A; rpr A r \<rbrakk> \<Longrightarrow> choiceFn A r"
  unfolding rpr_def by (blast dest: trans_imp_quasi_trans r_c_qt_imp_cf)

(* **************************************** *)

subsection\<open>Social Choice Functions (SCFs)\<close>

text \<open>A \emph{social choice function} (SCF), also called a
\emph{collective choice rule} by Sen \cite[p28]{Sen:70a}, is a function that
somehow aggregates society's opinions, expressed as a profile, into a
preference relation.\<close>

type_synonym ('a, 'i) SCF = "('a, 'i) Profile \<Rightarrow> 'a RPR"

text \<open>The least we require of an SCF is that it be \emph{complete} and
some function of the profile. The latter condition is usually implied by
other conditions, such as @{term "iia"}.\<close>

definition
  SCF :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> ('a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool) \<Rightarrow> bool"
where
  "SCF scf A Is Pcond \<equiv> (\<forall>P. Pcond A Is P \<longrightarrow> (complete A (scf P)))"

lemma SCFI[intro]:
  assumes c: "\<And>P. Pcond A Is P \<Longrightarrow> complete A (scf P)"
  shows "SCF scf A Is Pcond"
  unfolding SCF_def using assms by blast

lemma SCF_completeD[dest]: "\<lbrakk> SCF scf A Is Pcond; Pcond A Is P \<rbrakk> \<Longrightarrow> complete A (scf P)"
  unfolding SCF_def by blast

(* **************************************** *)

subsection\<open>Social Welfare Functions (SWFs)\<close>

text \<open>A \emph{Social Welfare Function} (SWF) is an SCF that expresses the
society's opinion as a single RPR.

In some situations it might make sense to restrict the allowable
profiles.\<close>

definition
  SWF :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> ('a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool) \<Rightarrow> bool"
where
  "SWF swf A Is Pcond \<equiv> (\<forall>P. Pcond A Is P \<longrightarrow> rpr A (swf P))"

lemma SWF_rpr[dest]: "\<lbrakk> SWF swf A Is Pcond; Pcond A Is P \<rbrakk> \<Longrightarrow> rpr A (swf P)"
  unfolding SWF_def by simp

(* **************************************** *)

subsection\<open>General Properties of an SCF\<close>

text\<open>An SCF has a \emph{universal domain} if it works for all profiles.\<close>

definition universal_domain :: "'a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool" where
  "universal_domain A Is P \<equiv> profile A Is P"

declare universal_domain_def[simp]

text\<open>An SCF is \emph{weakly Pareto-optimal} if, whenever everyone strictly
prefers @{term "x"} to @{term "y"}, the SCF does too.\<close>

definition
  weak_pareto :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> ('a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool) \<Rightarrow> bool"
where
  "weak_pareto scf A Is Pcond \<equiv>
     (\<forall>P x y. Pcond A Is P \<and> x \<in> A \<and> y \<in> A \<and> (\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y) \<longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y)"

lemma weak_paretoI[intro]:
  "(\<And>P x y. \<lbrakk>Pcond A Is P; x \<in> A; y \<in> A; \<And>i. i\<in>Is \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y\<rbrakk> \<Longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y)
  \<Longrightarrow> weak_pareto scf A Is Pcond"
  unfolding weak_pareto_def by simp

lemma weak_paretoD:
  "\<lbrakk> weak_pareto scf A Is Pcond; Pcond A Is P; x \<in> A; y \<in> A;
     (\<And>i. i \<in> Is \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y) \<rbrakk> \<Longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y"
  unfolding weak_pareto_def by simp

text\<open>

An SCF satisfies \emph{independence of irrelevant alternatives} if, for two
preference profiles @{term "P"} and @{term "P'"} where for all individuals
@{term "i"}, alternatives @{term "x"} and @{term "y"} drawn from set @{term
"S"} have the same order in @{term "P i"} and @{term "P' i"}, then
alternatives @{term "x"} and @{term "y"} have the same order in @{term "scf
P"} and @{term "scf P'"}.

\<close>

definition iia :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "iia scf S Is \<equiv>
    (\<forall>P P' x y. profile S Is P \<and> profile S Is P'
      \<and> x \<in> S \<and> y \<in> S
      \<and> (\<forall>i \<in> Is. ((x \<^bsub>(P i)\<^esub>\<preceq> y) \<longleftrightarrow> (x \<^bsub>(P' i)\<^esub>\<preceq> y)) \<and> ((y \<^bsub>(P i)\<^esub>\<preceq> x) \<longleftrightarrow> (y \<^bsub>(P' i)\<^esub>\<preceq> x)))
         \<longrightarrow> ((x \<^bsub>(scf P)\<^esub>\<preceq> y) \<longleftrightarrow> (x \<^bsub>(scf P')\<^esub>\<preceq> y)))"

lemma iiaI[intro]:
  "(\<And>P P' x y.
    \<lbrakk> profile S Is P; profile S Is P';
      x \<in> S; y \<in> S;
      \<And>i. i \<in> Is \<Longrightarrow> ((x \<^bsub>(P i)\<^esub>\<preceq> y) \<longleftrightarrow> (x \<^bsub>(P' i)\<^esub>\<preceq> y)) \<and> ((y \<^bsub>(P i)\<^esub>\<preceq> x) \<longleftrightarrow> (y \<^bsub>(P' i)\<^esub>\<preceq> x))
    \<rbrakk> \<Longrightarrow> ((x \<^bsub>(swf P)\<^esub>\<preceq> y) \<longleftrightarrow> (x \<^bsub>(swf P')\<^esub>\<preceq> y)))
  \<Longrightarrow> iia swf S Is"
  unfolding iia_def by simp

lemma iiaE:
  "\<lbrakk> iia swf S Is;
     {x,y} \<subseteq> S;
     a \<in> {x, y}; b \<in> {x, y};
     \<And>i a b. \<lbrakk> a \<in> {x, y}; b \<in> {x, y}; i \<in> Is \<rbrakk> \<Longrightarrow> (a \<^bsub>(P' i)\<^esub>\<preceq> b) \<longleftrightarrow> (a \<^bsub>(P i)\<^esub>\<preceq> b);
     profile S Is P; profile S Is P' \<rbrakk>
  \<Longrightarrow> (a \<^bsub>(swf P)\<^esub>\<preceq> b) \<longleftrightarrow> (a \<^bsub>(swf P')\<^esub>\<preceq> b)"
  unfolding iia_def by (simp, blast)

(* **************************************** *)

subsection\<open>Decisiveness and Semi-decisiveness\<close>

text\<open>This notion is the key to Arrow's Theorem, and hinges on the use of
strict preference \cite[p42]{Sen:70a}.\<close>

text\<open>A coalition @{term "C"} of agents is \emph{semi-decisive} for @{term
"x"} over @{term "y"} if, whenever the coalition prefers @{term "x"} to
@{term "y"} and all other agents prefer the converse, the coalition
prevails.\<close>

definition semidecisive :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "semidecisive scf A Is C x y \<equiv>
    C \<subseteq> Is \<and> (\<forall>P. profile A Is P \<and> (\<forall>i \<in> C. x \<^bsub>(P i)\<^esub>\<prec> y) \<and> (\<forall>i \<in> Is - C. y \<^bsub>(P i)\<^esub>\<prec> x)
      \<longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y)"

lemma semidecisiveI[intro]:
  "\<lbrakk> C \<subseteq> Is;
    \<And>P. \<lbrakk> profile A Is P; \<And>i. i \<in> C \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y; \<And>i. i \<in> Is - C \<Longrightarrow> y \<^bsub>(P i)\<^esub>\<prec> x \<rbrakk>
     \<Longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> semidecisive scf A Is C x y"
  unfolding semidecisive_def by simp

lemma semidecisive_coalitionD[dest]: "semidecisive scf A Is C x y \<Longrightarrow> C \<subseteq> Is"
  unfolding semidecisive_def by simp

lemma sd_refl: "\<lbrakk> C \<subseteq> Is; C \<noteq> {} \<rbrakk> \<Longrightarrow> semidecisive scf A Is C x x"
  unfolding semidecisive_def strict_pref_def by blast

text\<open>A coalition @{term "C"} is \emph{decisive} for @{term "x"} over
@{term "y"} if, whenever the coalition prefers @{term "x"} to @{term "y"},
the coalition prevails.\<close>

definition decisive :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "decisive scf A Is C x y \<equiv>
    C \<subseteq> Is \<and> (\<forall>P. profile A Is P \<and> (\<forall>i \<in> C. x \<^bsub>(P i)\<^esub>\<prec> y) \<longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y)"

lemma decisiveI[intro]:
  "\<lbrakk> C \<subseteq> Is; \<And>P. \<lbrakk> profile A Is P; \<And>i. i \<in> C \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<^bsub>(scf P)\<^esub>\<prec> y \<rbrakk>
    \<Longrightarrow> decisive scf A Is C x y"
  unfolding decisive_def by simp

lemma d_imp_sd: "decisive scf A Is C x y \<Longrightarrow> semidecisive scf A Is C x y"
  unfolding decisive_def by (rule semidecisiveI, blast+)

lemma decisive_coalitionD[dest]: "decisive scf A Is C x y \<Longrightarrow> C \<subseteq> Is"
  unfolding decisive_def by simp

text \<open>Anyone is trivially decisive for @{term "x"} against @{term "x"}.\<close>

lemma d_refl: "\<lbrakk> C \<subseteq> Is; C \<noteq> {} \<rbrakk> \<Longrightarrow> decisive scf A Is C x x"
  unfolding decisive_def strict_pref_def by simp

text\<open>Agent @{term "j"} is a \emph{dictator} if her preferences always
prevail. This is the same as saying that she is decisive for all @{term "x"}
and @{term "y"}.\<close>

definition dictator :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> 'i \<Rightarrow> bool" where
  "dictator scf A Is j \<equiv> j \<in> Is \<and> (\<forall>x \<in> A. \<forall>y \<in> A. decisive scf A Is {j} x y)"

lemma dictatorI[intro]:
  "\<lbrakk> j \<in> Is; \<And>x y. \<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> decisive scf A Is {j} x y \<rbrakk> \<Longrightarrow> dictator scf A Is j"
  unfolding dictator_def by simp

lemma dictator_individual[dest]: "dictator scf A Is j \<Longrightarrow> j \<in> Is"
  unfolding dictator_def by simp

(*<*)
end
(*>*)
