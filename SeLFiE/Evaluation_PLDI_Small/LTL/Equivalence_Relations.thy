(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Equivalence Relations for LTL formulas\<close>

theory Equivalence_Relations
imports
  LTL
begin

subsection \<open>Language Equivalence\<close>

definition ltl_lang_equiv :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>\<^sub>L" 75)
where
  "\<phi> \<sim>\<^sub>L \<psi> \<equiv> \<forall>w. w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi>"

lemma ltl_lang_equiv_equivp:
  "equivp (\<sim>\<^sub>L)"
  unfolding ltl_lang_equiv_def
  by (simp add: equivpI reflp_def symp_def transp_def)

lemma ltl_lang_equiv_and_true[simp]:
  "\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L true\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>L true\<^sub>n \<and> \<phi>\<^sub>2 \<sim>\<^sub>L true\<^sub>n"
  unfolding ltl_lang_equiv_def by auto

lemma ltl_lang_equiv_and_false[intro, simp]:
  "\<phi>\<^sub>1 \<sim>\<^sub>L false\<^sub>n \<Longrightarrow> \<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L false\<^sub>n"
  "\<phi>\<^sub>2 \<sim>\<^sub>L false\<^sub>n \<Longrightarrow> \<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L false\<^sub>n"
  unfolding ltl_lang_equiv_def by auto

lemma ltl_lang_equiv_or_false[simp]:
  "\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L false\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>L false\<^sub>n \<and> \<phi>\<^sub>2 \<sim>\<^sub>L false\<^sub>n"
  unfolding ltl_lang_equiv_def by auto

lemma ltl_lang_equiv_or_const[intro, simp]:
  "\<phi>\<^sub>1 \<sim>\<^sub>L true\<^sub>n \<Longrightarrow> \<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L true\<^sub>n"
  "\<phi>\<^sub>2 \<sim>\<^sub>L true\<^sub>n \<Longrightarrow> \<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>L true\<^sub>n"
  unfolding ltl_lang_equiv_def by auto


subsection \<open>Propositional Equivalence\<close>

fun ltl_prop_entailment :: "'a ltln set \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>P" 80)
where
  "\<A> \<Turnstile>\<^sub>P true\<^sub>n = True"
| "\<A> \<Turnstile>\<^sub>P false\<^sub>n = False"
| "\<A> \<Turnstile>\<^sub>P \<phi> and\<^sub>n \<psi> = (\<A> \<Turnstile>\<^sub>P \<phi> \<and> \<A> \<Turnstile>\<^sub>P \<psi>)"
| "\<A> \<Turnstile>\<^sub>P \<phi> or\<^sub>n \<psi> = (\<A> \<Turnstile>\<^sub>P \<phi> \<or> \<A> \<Turnstile>\<^sub>P \<psi>)"
| "\<A> \<Turnstile>\<^sub>P \<phi> = (\<phi> \<in> \<A>)"

lemma ltl_prop_entailment_monotonI[intro]:
  "S \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> S' \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

lemma ltl_models_equiv_prop_entailment:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> {\<psi>. w \<Turnstile>\<^sub>n \<psi>} \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

definition ltl_prop_equiv :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>\<^sub>P" 75)
where
  "\<phi> \<sim>\<^sub>P \<psi> \<equiv> \<forall>\<A>. \<A> \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> \<A> \<Turnstile>\<^sub>P \<psi>"

definition ltl_prop_implies :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<longrightarrow>\<^sub>P" 75)
where
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<equiv> \<forall>\<A>. \<A> \<Turnstile>\<^sub>P \<phi> \<longrightarrow> \<A> \<Turnstile>\<^sub>P \<psi>"

lemma ltl_prop_implies_equiv:
  "\<phi> \<sim>\<^sub>P \<psi> \<longleftrightarrow> (\<phi> \<longrightarrow>\<^sub>P \<psi> \<and> \<psi> \<longrightarrow>\<^sub>P \<phi>)"
  unfolding ltl_prop_equiv_def ltl_prop_implies_def by meson

lemma ltl_prop_equiv_equivp:
  "equivp (\<sim>\<^sub>P)"
  by (simp add: ltl_prop_equiv_def equivpI reflp_def symp_def transp_def)

lemma ltl_prop_equiv_trans[trans]:
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> \<psi> \<sim>\<^sub>P \<chi> \<Longrightarrow> \<phi> \<sim>\<^sub>P \<chi>"
  by (simp add: ltl_prop_equiv_def)

lemma ltl_prop_equiv_true:
  "\<phi> \<sim>\<^sub>P true\<^sub>n \<longleftrightarrow> {} \<Turnstile>\<^sub>P \<phi>"
  using bot.extremum ltl_prop_entailment.simps(1) ltl_prop_equiv_def by blast

lemma ltl_prop_equiv_false:
  "\<phi> \<sim>\<^sub>P false\<^sub>n \<longleftrightarrow> \<not> UNIV \<Turnstile>\<^sub>P \<phi>"
  by (meson ltl_prop_entailment.simps(2) ltl_prop_entailment_monotonI ltl_prop_equiv_def top_greatest)

lemma ltl_prop_equiv_true_implies_true:
  "x \<sim>\<^sub>P true\<^sub>n \<Longrightarrow> x \<longrightarrow>\<^sub>P y \<Longrightarrow> y \<sim>\<^sub>P true\<^sub>n"
  by (simp add: ltl_prop_equiv_def ltl_prop_implies_def)

lemma ltl_prop_equiv_false_implied_by_false:
  "y \<sim>\<^sub>P false\<^sub>n \<Longrightarrow> x \<longrightarrow>\<^sub>P y \<Longrightarrow> x \<sim>\<^sub>P false\<^sub>n"
  by (simp add: ltl_prop_equiv_def ltl_prop_implies_def)

lemma ltl_prop_implication_implies_ltl_implication:
  "w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> \<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<psi>"
  using ltl_models_equiv_prop_entailment ltl_prop_implies_def by blast

lemma ltl_prop_equiv_implies_ltl_lang_equiv:
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>L \<psi>"
  using ltl_lang_equiv_def ltl_prop_implication_implies_ltl_implication ltl_prop_implies_equiv by blast

lemma ltl_prop_equiv_lt_ltl_lang_equiv[simp]:
  "(\<sim>\<^sub>P) \<le> (\<sim>\<^sub>L)"
  using ltl_prop_equiv_implies_ltl_lang_equiv by blast


subsection \<open>Constants Equivalence\<close>

datatype tvl = Yes | No | Maybe

definition eval_and :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl"
where
  "eval_and \<phi> \<psi> =
    (case (\<phi>, \<psi>) of
      (Yes, Yes) \<Rightarrow> Yes
    | (No, _) \<Rightarrow> No
    | (_, No) \<Rightarrow> No
    | _ \<Rightarrow> Maybe)"

definition eval_or :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl"
where
  "eval_or \<phi> \<psi> =
    (case (\<phi>, \<psi>) of
      (No, No) \<Rightarrow> No
    | (Yes, _) \<Rightarrow> Yes
    | (_, Yes) \<Rightarrow> Yes
    | _ \<Rightarrow> Maybe)"

fun eval :: "'a ltln \<Rightarrow> tvl"
where
  "eval true\<^sub>n = Yes"
| "eval false\<^sub>n = No"
| "eval (\<phi> and\<^sub>n \<psi>) = eval_and (eval \<phi>) (eval \<psi>)"
| "eval (\<phi> or\<^sub>n \<psi>) = eval_or (eval \<phi>) (eval \<psi>)"
| "eval \<phi> = Maybe"

lemma eval_and_const[simp]:
  "eval_and \<phi> \<psi> = No \<longleftrightarrow> \<phi> = No \<or> \<psi> = No"
  "eval_and \<phi> \<psi> = Yes \<longleftrightarrow> \<phi> = Yes \<and> \<psi> = Yes"
  unfolding eval_and_def
  by (cases \<phi>; cases \<psi>, auto)+

lemma eval_or_const[simp]:
  "eval_or \<phi> \<psi> = Yes \<longleftrightarrow> \<phi> = Yes \<or> \<psi> = Yes"
  "eval_or \<phi> \<psi> = No \<longleftrightarrow> \<phi> = No \<and> \<psi> = No"
  unfolding eval_or_def
  by (cases \<phi>; cases \<psi>, auto)+

lemma eval_prop_entailment:
  "eval \<phi> = Yes \<longleftrightarrow> {} \<Turnstile>\<^sub>P \<phi>"
  "eval \<phi> = No \<longleftrightarrow> \<not> UNIV \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

definition ltl_const_equiv :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>\<^sub>C" 75)
where
  "\<phi> \<sim>\<^sub>C \<psi> \<equiv> \<phi> = \<psi> \<or> (eval \<phi> = eval \<psi> \<and> eval \<psi> \<noteq> Maybe)"

lemma ltl_const_equiv_equivp:
  "equivp (\<sim>\<^sub>C)"
  unfolding ltl_const_equiv_def
  by (intro equivpI reflpI sympI transpI) auto

lemma ltl_const_equiv_const:
  "\<phi> \<sim>\<^sub>C true\<^sub>n \<longleftrightarrow> eval \<phi> = Yes"
  "\<phi> \<sim>\<^sub>C false\<^sub>n \<longleftrightarrow> eval \<phi> = No"
  unfolding ltl_const_equiv_def by force+

lemma ltl_const_equiv_and_const[simp]:
  "\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>C true\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>C true\<^sub>n \<and> \<phi>\<^sub>2 \<sim>\<^sub>C true\<^sub>n"
  "\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>C false\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>C false\<^sub>n \<or> \<phi>\<^sub>2 \<sim>\<^sub>C false\<^sub>n"
  unfolding ltl_const_equiv_const by force+

lemma ltl_const_equiv_or_const[simp]:
  "\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>C true\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>C true\<^sub>n \<or> \<phi>\<^sub>2 \<sim>\<^sub>C true\<^sub>n"
  "\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<sim>\<^sub>C false\<^sub>n \<longleftrightarrow> \<phi>\<^sub>1 \<sim>\<^sub>C false\<^sub>n \<and> \<phi>\<^sub>2 \<sim>\<^sub>C false\<^sub>n"
  unfolding ltl_const_equiv_const by force+

lemma ltl_const_equiv_other[simp]:
  "\<phi> \<sim>\<^sub>C prop\<^sub>n(a) \<longleftrightarrow> \<phi> = prop\<^sub>n(a)"
  "\<phi> \<sim>\<^sub>C nprop\<^sub>n(a) \<longleftrightarrow> \<phi> = nprop\<^sub>n(a)"
  "\<phi> \<sim>\<^sub>C X\<^sub>n \<psi> \<longleftrightarrow> \<phi> = X\<^sub>n \<psi>"
  "\<phi> \<sim>\<^sub>C \<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2 \<longleftrightarrow> \<phi> = \<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2"
  "\<phi> \<sim>\<^sub>C \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<longleftrightarrow> \<phi> = \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2"
  "\<phi> \<sim>\<^sub>C \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<longleftrightarrow> \<phi> = \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2"
  "\<phi> \<sim>\<^sub>C \<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2 \<longleftrightarrow> \<phi> = \<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2"
  using ltl_const_equiv_def by fastforce+

lemma ltl_const_equiv_no_const_singleton:
  "eval \<psi> = Maybe \<Longrightarrow> \<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> \<phi> = \<psi>"
  unfolding ltl_const_equiv_def by fastforce

lemma ltl_const_equiv_implies_prop_equiv:
  "\<phi> \<sim>\<^sub>C true\<^sub>n \<longleftrightarrow> \<phi> \<sim>\<^sub>P true\<^sub>n"
  "\<phi> \<sim>\<^sub>C false\<^sub>n \<longleftrightarrow> \<phi> \<sim>\<^sub>P false\<^sub>n"
  unfolding ltl_const_equiv_const eval_prop_entailment ltl_prop_equiv_def
  by auto

lemma ltl_const_equiv_no_const_prop_equiv:
  "eval \<psi> = Maybe \<Longrightarrow> \<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>P \<psi>"
  using ltl_const_equiv_no_const_singleton equivp_reflp[OF ltl_prop_equiv_equivp]
  by blast

lemma ltl_const_equiv_implies_ltl_prop_equiv:
  "\<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>P \<psi>"
proof (induction \<psi>)
  case (And_ltln \<psi>1 \<psi>2)

  show ?case
  proof (cases "eval (\<psi>1 and\<^sub>n \<psi>2)")
    case Yes

    then have "\<phi> \<sim>\<^sub>C true\<^sub>n"
      by (meson And_ltln.prems equivp_transp ltl_const_equiv_const(1) ltl_const_equiv_equivp)
    then show ?thesis
      by (metis (full_types) Yes ltl_const_equiv_const(1) ltl_const_equiv_implies_prop_equiv(1) ltl_prop_equiv_trans ltl_prop_implies_equiv)
  next
    case No

    then have "\<phi> \<sim>\<^sub>C false\<^sub>n"
      by (meson And_ltln.prems equivp_transp ltl_const_equiv_const(2) ltl_const_equiv_equivp)
    then show ?thesis
      by (metis (full_types) No ltl_const_equiv_const(2) ltl_const_equiv_implies_prop_equiv(2) ltl_prop_equiv_trans ltl_prop_implies_equiv)
  next
    case Maybe

    then show ?thesis
      using And_ltln.prems ltl_const_equiv_no_const_prop_equiv by force
  qed
next
  case (Or_ltln \<psi>1 \<psi>2)

  then show ?case
  proof (cases "eval (\<psi>1 or\<^sub>n \<psi>2)")
    case Yes

    then have "\<phi> \<sim>\<^sub>C true\<^sub>n"
      by (meson Or_ltln.prems equivp_transp ltl_const_equiv_const(1) ltl_const_equiv_equivp)
    then show ?thesis
      by (metis (full_types) Yes ltl_const_equiv_const(1) ltl_const_equiv_implies_prop_equiv(1) ltl_prop_equiv_trans ltl_prop_implies_equiv)
  next
    case No

    then have "\<phi> \<sim>\<^sub>C false\<^sub>n"
      by (meson Or_ltln.prems equivp_transp ltl_const_equiv_const(2) ltl_const_equiv_equivp)
    then show ?thesis
      by (metis (full_types) No ltl_const_equiv_const(2) ltl_const_equiv_implies_prop_equiv(2) ltl_prop_equiv_trans ltl_prop_implies_equiv)
  next
    case Maybe

    then show ?thesis
      using Or_ltln.prems ltl_const_equiv_no_const_prop_equiv by force
  qed
qed (simp_all add: ltl_const_equiv_implies_prop_equiv equivp_reflp[OF ltl_prop_equiv_equivp])

lemma ltl_const_equiv_lt_ltl_prop_equiv[simp]:
  "(\<sim>\<^sub>C) \<le> (\<sim>\<^sub>P)"
  using ltl_const_equiv_implies_ltl_prop_equiv by blast


subsection \<open>Quotient types\<close>

quotient_type 'a ltln\<^sub>L = "'a ltln" / "(\<sim>\<^sub>L)"
  by (rule ltl_lang_equiv_equivp)

instantiation ltln\<^sub>L :: (type) equal
begin

lift_definition ltln\<^sub>L_eq_test :: "'a ltln\<^sub>L \<Rightarrow> 'a ltln\<^sub>L \<Rightarrow> bool" is "\<lambda>x y. x \<sim>\<^sub>L y"
  by (metis ltln\<^sub>L.abs_eq_iff)

definition
  eq\<^sub>L: "equal_class.equal \<equiv> ltln\<^sub>L_eq_test"

instance
  by (standard; simp add: eq\<^sub>L ltln\<^sub>L_eq_test.rep_eq, metis Quotient_ltln\<^sub>L Quotient_rel_rep)

end


quotient_type 'a ltln\<^sub>P = "'a ltln" / "(\<sim>\<^sub>P)"
  by (rule ltl_prop_equiv_equivp)

instantiation ltln\<^sub>P :: (type) equal
begin

lift_definition ltln\<^sub>P_eq_test :: "'a ltln\<^sub>P \<Rightarrow> 'a ltln\<^sub>P \<Rightarrow> bool" is "\<lambda>x y. x \<sim>\<^sub>P y"
  by (metis ltln\<^sub>P.abs_eq_iff)

definition
  eq\<^sub>P: "equal_class.equal \<equiv> ltln\<^sub>P_eq_test"

instance
  by (standard; simp add: eq\<^sub>P ltln\<^sub>P_eq_test.rep_eq, metis Quotient_ltln\<^sub>P Quotient_rel_rep)

end


quotient_type 'a ltln\<^sub>C = "'a ltln" / "(\<sim>\<^sub>C)"
  by (rule ltl_const_equiv_equivp)

instantiation ltln\<^sub>C :: (type) equal
begin

lift_definition ltln\<^sub>C_eq_test :: "'a ltln\<^sub>C \<Rightarrow> 'a ltln\<^sub>C \<Rightarrow> bool" is "\<lambda>x y. x \<sim>\<^sub>C y"
  by (metis ltln\<^sub>C.abs_eq_iff)

definition
  eq\<^sub>C: "equal_class.equal \<equiv> ltln\<^sub>C_eq_test"

instance
  by (standard; simp add: eq\<^sub>C ltln\<^sub>C_eq_test.rep_eq, metis Quotient_ltln\<^sub>C Quotient_rel_rep)

end



subsection \<open>Cardinality of propositional quotient sets\<close>

definition sat_models :: "'a ltln\<^sub>P \<Rightarrow> 'a ltln set set"
where
  "sat_models \<phi> = {\<A>. \<A> \<Turnstile>\<^sub>P rep_ltln\<^sub>P \<phi>}"

lemma Rep_Abs_prop_entailment[simp]:
  "\<A> \<Turnstile>\<^sub>P rep_ltln\<^sub>P (abs_ltln\<^sub>P \<phi>) = \<A> \<Turnstile>\<^sub>P \<phi>"
  by (metis Quotient3_ltln\<^sub>P Quotient3_rep_abs ltl_prop_equiv_def)

lemma sat_models_Abs:
  "\<A> \<in> sat_models (abs_ltln\<^sub>P \<phi>) = \<A> \<Turnstile>\<^sub>P \<phi>"
  by (simp add: sat_models_def)

lemma sat_models_inj:
  "inj sat_models"
proof (rule injI)
  fix \<phi> \<psi> :: "'a ltln\<^sub>P"
  assume "sat_models \<phi> = sat_models \<psi>"

  then have "rep_ltln\<^sub>P \<phi> \<sim>\<^sub>P rep_ltln\<^sub>P \<psi>"
    unfolding sat_models_def ltl_prop_equiv_def by force

  then show "\<phi> = \<psi>"
    by (meson Quotient3_ltln\<^sub>P Quotient3_rel_rep)
qed


fun prop_atoms :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "prop_atoms true\<^sub>n = {}"
| "prop_atoms false\<^sub>n = {}"
| "prop_atoms (\<phi> and\<^sub>n \<psi>) = prop_atoms \<phi> \<union> prop_atoms \<psi>"
| "prop_atoms (\<phi> or\<^sub>n \<psi>) = prop_atoms \<phi> \<union> prop_atoms \<psi>"
| "prop_atoms \<phi> = {\<phi>}"

fun nested_prop_atoms :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "nested_prop_atoms true\<^sub>n = {}"
| "nested_prop_atoms false\<^sub>n = {}"
| "nested_prop_atoms (\<phi> and\<^sub>n \<psi>) = nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms (\<phi> or\<^sub>n \<psi>) = nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms (X\<^sub>n \<phi>) = {X\<^sub>n \<phi>} \<union> nested_prop_atoms \<phi>"
| "nested_prop_atoms (\<phi> U\<^sub>n \<psi>) = {\<phi> U\<^sub>n \<psi>} \<union> nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms (\<phi> R\<^sub>n \<psi>) = {\<phi> R\<^sub>n \<psi>} \<union> nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms (\<phi> W\<^sub>n \<psi>) = {\<phi> W\<^sub>n \<psi>} \<union> nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms (\<phi> M\<^sub>n \<psi>) = {\<phi> M\<^sub>n \<psi>} \<union> nested_prop_atoms \<phi> \<union> nested_prop_atoms \<psi>"
| "nested_prop_atoms \<phi> = {\<phi>}"

lemma prop_atoms_nested_prop_atoms:
  "prop_atoms \<phi> \<subseteq> nested_prop_atoms \<phi>"
  by (induction \<phi>) auto

lemma prop_atoms_subfrmlsn:
  "prop_atoms \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma nested_prop_atoms_subfrmlsn:
  "nested_prop_atoms \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma prop_atoms_notin[simp]:
  "true\<^sub>n \<notin> prop_atoms \<phi>"
  "false\<^sub>n \<notin> prop_atoms \<phi>"
  "\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<notin> prop_atoms \<phi>"
  "\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<notin> prop_atoms \<phi>"
  by (induction \<phi>) auto

lemma nested_prop_atoms_notin[simp]:
  "true\<^sub>n \<notin> nested_prop_atoms \<phi>"
  "false\<^sub>n \<notin> nested_prop_atoms \<phi>"
  "\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2 \<notin> nested_prop_atoms \<phi>"
  "\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2 \<notin> nested_prop_atoms \<phi>"
  by (induction \<phi>) auto

lemma prop_atoms_finite:
  "finite (prop_atoms \<phi>)"
  by (induction \<phi>) auto

lemma nested_prop_atoms_finite:
  "finite (nested_prop_atoms \<phi>)"
  by (induction \<phi>) auto

lemma prop_atoms_entailment_iff:
  "\<phi> \<in> prop_atoms \<psi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> \<phi> \<in> \<A>"
  by (induction \<phi>) auto

lemma prop_atoms_entailment_inter:
  "prop_atoms \<phi> \<subseteq> P \<Longrightarrow> (\<A> \<inter> P) \<Turnstile>\<^sub>P \<phi> = \<A> \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

lemma nested_prop_atoms_entailment_inter:
  "nested_prop_atoms \<phi> \<subseteq> P \<Longrightarrow> (\<A> \<inter> P) \<Turnstile>\<^sub>P \<phi> = \<A> \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

lemma sat_models_inter_inj_helper:
  assumes
    "prop_atoms \<phi> \<subseteq> P"
  and
    "prop_atoms \<psi> \<subseteq> P"
  and
    "sat_models (abs_ltln\<^sub>P \<phi>) \<inter> Pow P = sat_models (abs_ltln\<^sub>P \<psi>) \<inter> Pow P"
  shows
    "\<phi> \<sim>\<^sub>P \<psi>"
proof -
  from assms have "\<forall>\<A>. (\<A> \<inter> P) \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> (\<A> \<inter> P) \<Turnstile>\<^sub>P \<psi>"
    by (auto simp: sat_models_Abs)

  with assms show "\<phi> \<sim>\<^sub>P \<psi>"
    by (simp add: prop_atoms_entailment_inter ltl_prop_equiv_def)
qed

lemma sat_models_inter_inj:
  "inj_on (\<lambda>\<phi>. sat_models \<phi> \<inter> Pow P) {abs_ltln\<^sub>P \<phi> |\<phi>. prop_atoms \<phi> \<subseteq> P}"
  by (auto simp: inj_on_def sat_models_inter_inj_helper ltln\<^sub>P.abs_eq_iff)

lemma sat_models_pow_pow:
  "{sat_models (abs_ltln\<^sub>P \<phi>) \<inter> Pow P | \<phi>. prop_atoms \<phi> \<subseteq> P} \<subseteq> Pow (Pow P)"
  by (auto simp: sat_models_def)

lemma sat_models_finite:
  "finite P \<Longrightarrow> finite {sat_models (abs_ltln\<^sub>P \<phi>) \<inter> Pow P | \<phi>. prop_atoms \<phi> \<subseteq> P}"
  using sat_models_pow_pow finite_subset by fastforce

lemma sat_models_card:
  "finite P \<Longrightarrow> card ({sat_models (abs_ltln\<^sub>P \<phi>) \<inter> Pow P | \<phi>. prop_atoms \<phi> \<subseteq> P}) \<le> 2 ^ 2 ^ card P"
  by (metis (mono_tags, lifting) sat_models_pow_pow Pow_def card_Pow card_mono finite_Collect_subsets)


lemma image_filter:
  "f ` {g a | a. P a} = {f (g a) | a. P a}"
  by blast

lemma prop_equiv_finite:
  "finite P \<Longrightarrow> finite {abs_ltln\<^sub>P \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> P}"
  by (auto simp: image_filter sat_models_finite finite_imageD[OF _ sat_models_inter_inj])

lemma prop_equiv_card:
  "finite P \<Longrightarrow> card {abs_ltln\<^sub>P \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> P} \<le> 2 ^ 2 ^ card P"
  by (auto simp: image_filter sat_models_card card_image[OF sat_models_inter_inj, symmetric])


lemma prop_equiv_subset:
  "{abs_ltln\<^sub>P \<psi> |\<psi>. nested_prop_atoms \<psi> \<subseteq> P} \<subseteq> {abs_ltln\<^sub>P \<psi> |\<psi>. prop_atoms \<psi> \<subseteq> P}"
  using prop_atoms_nested_prop_atoms by blast

lemma prop_equiv_finite':
  "finite P \<Longrightarrow> finite {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> P}"
  using prop_equiv_finite prop_equiv_subset finite_subset by fast

lemma prop_equiv_card':
  "finite P \<Longrightarrow> card {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> P} \<le> 2 ^ 2 ^ card P"
  by (metis (mono_tags, lifting) prop_equiv_card prop_equiv_subset prop_equiv_finite card_mono le_trans)



subsection \<open>Substitution\<close>

fun subst :: "'a ltln \<Rightarrow> ('a ltln \<rightharpoonup> 'a ltln) \<Rightarrow> 'a ltln"
where
  "subst true\<^sub>n m = true\<^sub>n"
| "subst false\<^sub>n m = false\<^sub>n"
| "subst (\<phi> and\<^sub>n \<psi>) m = subst \<phi> m and\<^sub>n subst \<psi> m"
| "subst (\<phi> or\<^sub>n \<psi>) m = subst \<phi> m or\<^sub>n subst \<psi> m"
| "subst \<phi> m = (case m \<phi> of Some \<psi> \<Rightarrow> \<psi> | None \<Rightarrow> \<phi>)"

text \<open>Based on Uwe Schoening's Translation Lemma (Logic for CS, p. 54)\<close>

lemma ltl_prop_equiv_subst_S:
  "S \<Turnstile>\<^sub>P subst \<phi> m = ((S - dom m) \<union> {\<chi> | \<chi> \<chi>'. \<chi> \<in> dom m \<and> m \<chi> = Some \<chi>' \<and> S \<Turnstile>\<^sub>P \<chi>'}) \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) (auto split: option.split)

lemma subst_respects_ltl_prop_entailment:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> subst \<phi> m \<longrightarrow>\<^sub>P subst \<psi> m"
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> subst \<phi> m \<sim>\<^sub>P subst \<psi> m"
  unfolding ltl_prop_equiv_def ltl_prop_implies_def ltl_prop_equiv_subst_S by blast+


lemma eval_subst:
  "eval \<phi> = Yes \<Longrightarrow> eval (subst \<phi> m) = Yes"
  "eval \<phi> = No \<Longrightarrow> eval (subst \<phi> m) = No"
  by (meson empty_subsetI eval_prop_entailment ltl_prop_entailment_monotonI ltl_prop_equiv_subst_S subset_UNIV)+

lemma subst_respects_ltl_const_entailment:
  "\<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> subst \<phi> m \<sim>\<^sub>C subst \<psi> m"
  unfolding ltl_const_equiv_def
  by (cases "eval \<psi>") (metis eval_subst(1), metis eval_subst(2), blast)



subsection \<open>Order of Equivalence Relations\<close>

locale ltl_equivalence =
  fixes
    eq :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>" 75)
  assumes
    eq_equivp: "equivp (\<sim>)"
  and
    ge_const_equiv: "(\<sim>\<^sub>C) \<le> (\<sim>)"
  and
    le_lang_equiv: "(\<sim>) \<le> (\<sim>\<^sub>L)"
begin

lemma eq_implies_ltl_equiv:
  "\<phi> \<sim> \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> = w \<Turnstile>\<^sub>n \<psi>"
  using le_lang_equiv ltl_lang_equiv_def by blast

lemma const_implies_eq:
  "\<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> \<phi> \<sim> \<psi>"
  using ge_const_equiv by blast

lemma eq_implies_lang:
  "\<phi> \<sim> \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>L \<psi>"
  using le_lang_equiv by blast

lemma eq_refl[simp]:
  "\<phi> \<sim> \<phi>"
  by (meson eq_equivp equivp_reflp)

lemma eq_sym[sym]:
  "\<phi> \<sim> \<psi> \<Longrightarrow> \<psi> \<sim> \<phi>"
  by (meson eq_equivp equivp_symp)

lemma eq_trans[trans]:
  "\<phi> \<sim> \<psi> \<Longrightarrow> \<psi> \<sim> \<chi> \<Longrightarrow> \<phi> \<sim> \<chi>"
  by (meson eq_equivp equivp_transp)

end

interpretation ltl_lang_equivalence: ltl_equivalence "(\<sim>\<^sub>L)"
  using ltl_lang_equiv_equivp ltl_const_equiv_lt_ltl_prop_equiv ltl_prop_equiv_lt_ltl_lang_equiv
  by unfold_locales blast+

interpretation ltl_prop_equivalence: ltl_equivalence "(\<sim>\<^sub>P)"
  using ltl_prop_equiv_equivp ltl_const_equiv_lt_ltl_prop_equiv ltl_prop_equiv_lt_ltl_lang_equiv
  by unfold_locales blast+

interpretation ltl_const_equivalence: ltl_equivalence "(\<sim>\<^sub>C)"
  using ltl_const_equiv_equivp ltl_const_equiv_lt_ltl_prop_equiv ltl_prop_equiv_lt_ltl_lang_equiv
  by unfold_locales blast+

end
