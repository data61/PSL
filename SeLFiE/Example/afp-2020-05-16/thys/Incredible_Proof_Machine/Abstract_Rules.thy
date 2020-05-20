theory Abstract_Rules
imports
  Abstract_Formula
begin

text \<open>
Next, we can define a logic, by giving a set of rules.

In order to connect to the AFP entry Abstract Completeness, the set of rules is a stream; the only
relevant effect of this is that the set is guaranteed to be non-empty and at most countable. This
has no further significance in our development.

Each antecedent of a rule consists of
 \<^item> a set of fresh variables
 \<^item> a set of hypotheses that may be used in proving the conclusion of the antecedent and
 \<^item> the conclusion of the antecedent.

Our rules allow for multiple conclusions (but must have at least one).

In order to prove the completeness (but incidentally not to prove correctness) of the incredible
proof graphs, there are some extra conditions about the fresh variables in a rule. 
 \<^item> These need to be disjoint for different antecedents.
 \<^item> They need to list all local variables occurring in either the hypothesis and the conclusion.
 \<^item> The conclusions of a rule must not contain any local variables.
\<close>


datatype ('form, 'var) antecedent =
  Antecedent (a_hyps: "'form fset") (a_conc: "'form") (a_fresh: "'var set")

abbreviation plain_ant :: "'form \<Rightarrow> ('form, 'var) antecedent"
  where "plain_ant f \<equiv> Antecedent {||} f {}"

locale Abstract_Rules =
  Abstract_Formulas freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP
  for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  and renameLCs  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  and lconsts :: "'form \<Rightarrow> 'var set"
  and closed :: "'form \<Rightarrow> bool"
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
  and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
  and anyP :: "'form" +

  fixes antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
    and consequent :: "'rule \<Rightarrow> 'form list"
    and rules :: "'rule stream"

  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"

  assumes no_local_consts_in_consequences: "\<forall>xs\<in>sset rules. \<Union>(lconsts ` (set (consequent xs))) = {}"
  assumes no_multiple_local_consts:
    "\<And> r i i' . r \<in> sset rules \<Longrightarrow>
                 i < length (antecedent r) \<Longrightarrow>
                 i' < length (antecedent r) \<Longrightarrow>
                 a_fresh (antecedent r ! i) \<inter> a_fresh (antecedent r ! i') = {} \<or> i = i'"
  assumes all_local_consts_listed:
    "\<And> r p. r \<in> sset rules \<Longrightarrow> p \<in> set (antecedent r) \<Longrightarrow>
        lconsts (a_conc p) \<union> (\<Union>(lconsts ` fset (a_hyps p))) \<subseteq> a_fresh p "
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent fset"
    where "f_antecedent r = fset_from_list (antecedent r)"
  definition "f_consequent r = fset_from_list (consequent r)"
end

text \<open>
Finally, an abstract task specifies what a specific proof should prove. In particular, it gives
a set of assumptions that may be used, and lists the conclusions that need to be proven.

Both assumptions and conclusions are closed expressions that may not be changed by substitutions. 
\<close>

locale Abstract_Task =
  Abstract_Rules freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP  antecedent consequent rules
  for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
    and renameLCs  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
    and lconsts :: "'form \<Rightarrow> 'var set"
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"
    and antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
    and consequent :: "'rule \<Rightarrow> 'form list" 
    and rules :: "'rule stream" +

  fixes assumptions :: "'form list"
  fixes conclusions :: "'form list"
  assumes assumptions_closed: "\<And> a. a \<in> set assumptions \<Longrightarrow> closed a"
  assumes conclusions_closed: "\<And> c. c \<in> set conclusions \<Longrightarrow> closed c"
begin
  definition ass_forms where "ass_forms = fset_from_list assumptions"
  definition conc_forms where "conc_forms = fset_from_list  conclusions"

  lemma mem_ass_forms[simp]: "a |\<in>| ass_forms \<longleftrightarrow> a \<in> set assumptions"
    by (auto simp add: ass_forms_def)
  
  lemma mem_conc_forms[simp]: "a |\<in>| conc_forms \<longleftrightarrow> a \<in> set conclusions"
    by (auto simp add: conc_forms_def)

  lemma subst_freshen_assumptions[simp]:
    assumes "pf \<in> set assumptions"
    shows "subst s (freshen a pf) = pf "
      using assms assumptions_closed 
      by (simp add: closed_no_lconsts freshen_def rename_closed subst_closed)

  lemma subst_freshen_conclusions[simp]:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) = pf "
      using assms conclusions_closed 
      by (simp add: closed_no_lconsts freshen_def rename_closed subst_closed)

  lemma subst_freshen_in_ass_formsI:
    assumes "pf \<in> set assumptions"
    shows "subst s (freshen a pf) |\<in>| ass_forms"
      using assms by simp

  lemma subst_freshen_in_conc_formsI:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) |\<in>| conc_forms"
      using assms by simp
end


end
