(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>LTL Code Equations\<close>

theory LTL_Impl
  imports Main 
    "../LTL_FGXU" 
    Boolean_Expression_Checkers.Boolean_Expression_Checkers 
    Boolean_Expression_Checkers.Boolean_Expression_Checkers_AList_Mapping
begin

subsection \<open>Subformulae\<close>

fun G_list :: "'a ltl \<Rightarrow>'a ltl list"
where 
  "G_list (\<phi> and \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list (\<phi> or \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list (F \<phi>) = G_list \<phi>"
| "G_list (G \<phi>) = List.insert (G \<phi>) (G_list \<phi>)"
| "G_list (X \<phi>) = G_list \<phi>"
| "G_list (\<phi> U \<psi>) = List.union (G_list \<phi>) (G_list \<psi>)"
| "G_list \<phi> = []"

lemma G_eq_G_list:
  "\<^bold>G \<phi> = set (G_list \<phi>)"
  by (induction \<phi>) auto

lemma G_list_distinct:
  "distinct (G_list \<phi>)"
  by (induction \<phi>) auto

subsection \<open>Propositional Equivalence\<close>

fun ifex_of_ltl :: "'a ltl \<Rightarrow> 'a ltl ifex" 
where
  "ifex_of_ltl true = Trueif"
| "ifex_of_ltl false = Falseif"
| "ifex_of_ltl (\<phi> and \<psi>) = normif Mapping.empty (ifex_of_ltl \<phi>) (ifex_of_ltl \<psi>) Falseif"
| "ifex_of_ltl (\<phi> or \<psi>) = normif Mapping.empty (ifex_of_ltl \<phi>) Trueif (ifex_of_ltl \<psi>)"
| "ifex_of_ltl \<phi> = IF \<phi> Trueif Falseif"

lemma val_ifex: 
  "val_ifex (ifex_of_ltl b) s = (\<Turnstile>\<^sub>P) {x. s x} b"
  by (induction b) (simp add: agree_Nil val_normif)+

lemma reduced_ifex: 
  "reduced (ifex_of_ltl b) {}"
  by (induction b) (simp; metis keys_empty reduced_normif)+

lemma ifex_of_ltl_reduced_bdt_checker: 
  "reduced_bdt_checkers ifex_of_ltl (\<lambda>y s. {x. s x} \<Turnstile>\<^sub>P y)"
  by (unfold reduced_bdt_checkers_def; insert val_ifex reduced_ifex; blast)

lemma [code]: 
  "(\<phi> \<equiv>\<^sub>P \<psi>) = equiv_test ifex_of_ltl \<phi> \<psi>"
  by (simp add: ltl_prop_equiv_def reduced_bdt_checkers.equiv_test[OF ifex_of_ltl_reduced_bdt_checker]; fastforce) 

lemma [code]: 
  "(\<phi> \<longrightarrow>\<^sub>P \<psi>) = impl_test ifex_of_ltl \<phi> \<psi>"
  by (simp add: ltl_prop_implies_def reduced_bdt_checkers.impl_test[OF ifex_of_ltl_reduced_bdt_checker]; force)

\<comment> \<open>Check Code Export\<close> 
export_code "(\<equiv>\<^sub>P)" "(\<longrightarrow>\<^sub>P)" checking

subsection \<open>Remove Constants\<close>

fun remove_constants\<^sub>P :: "'a ltl \<Rightarrow> 'a ltl"
where
  "remove_constants\<^sub>P (\<phi> and \<psi>) = (
    case (remove_constants\<^sub>P \<phi>) of
        false \<Rightarrow> false
      | true \<Rightarrow> remove_constants\<^sub>P \<psi>
      | \<phi>' \<Rightarrow> (case remove_constants\<^sub>P \<psi> of 
          false \<Rightarrow> false 
        | true \<Rightarrow> \<phi>' 
        | \<psi>' \<Rightarrow> \<phi>' and \<psi>'))"
| "remove_constants\<^sub>P (\<phi> or \<psi>) = (
    case (remove_constants\<^sub>P \<phi>) of
        true \<Rightarrow> true
      | false \<Rightarrow> remove_constants\<^sub>P \<psi>
      | \<phi>' \<Rightarrow> (case remove_constants\<^sub>P \<psi> of 
          true \<Rightarrow> true 
        | false \<Rightarrow> \<phi>' 
        | \<psi>' \<Rightarrow> \<phi>' or \<psi>'))"
| "remove_constants\<^sub>P \<phi> = \<phi>"

lemma remove_constants_correct: 
  "S \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> S \<Turnstile>\<^sub>P remove_constants\<^sub>P \<phi>"
  by (induction \<phi> arbitrary: S) (auto split: ltl.split)

subsection \<open>And/Or Constructors\<close>  

fun in_and
where
  "in_and x (y and z) = (in_and x y \<or> in_and x z)"
| "in_and x y = (x = y)"

fun in_or
where
  "in_or x (y or z) = (in_or x y \<or> in_or x z)"
| "in_or x y = (x = y)"
 
lemma in_entailment: 
  "in_and x y \<Longrightarrow> S \<Turnstile>\<^sub>P y \<Longrightarrow> S \<Turnstile>\<^sub>P x"
  "in_or x y \<Longrightarrow> S \<Turnstile>\<^sub>P x \<Longrightarrow> S \<Turnstile>\<^sub>P y"
  by (induction y) auto

definition mk_and
where
  "mk_and f x y = (case f x of false \<Rightarrow> false | true \<Rightarrow> f y 
    | x' \<Rightarrow> (case f y of false \<Rightarrow> false | true \<Rightarrow> x' 
    | y' \<Rightarrow> if in_and x' y' then y' else if in_and y' x' then x' else x' and y'))"

definition mk_and' 
where
  "mk_and' x y \<equiv> case y of false \<Rightarrow> false | true \<Rightarrow> x | _ \<Rightarrow> x and y"

definition mk_or 
where
  "mk_or f x y = (case f x of true \<Rightarrow> true | false \<Rightarrow> f y 
    | x' \<Rightarrow> (case f y of true \<Rightarrow> true | false \<Rightarrow> x' 
    | y' \<Rightarrow> if in_or x' y' then y' else if in_or y' x' then x' else x' or y'))"

definition mk_or'
where
  "mk_or' x y \<equiv> case y of true \<Rightarrow> true | false \<Rightarrow> x | _ \<Rightarrow> x or y"

lemma mk_and_correct: 
  "S \<Turnstile>\<^sub>P mk_and f x y \<longleftrightarrow> S \<Turnstile>\<^sub>P f x and f y"
proof -
  have X: "\<And>x' y'. S \<Turnstile>\<^sub>P (if in_and x' y' then y' else if in_and y' x' then x' else x' and y')
    \<longleftrightarrow> S \<Turnstile>\<^sub>P x' and y'"
    using in_entailment by auto
  show ?thesis
    unfolding mk_and_def ltl.split X by (cases "f x"; cases "f y"; simp) 
qed

lemma mk_and'_correct: 
  "S \<Turnstile>\<^sub>P mk_and' x y \<longleftrightarrow> S \<Turnstile>\<^sub>P x and y"
  unfolding mk_and'_def by (cases y; simp) 

lemma mk_or_correct: 
  "S \<Turnstile>\<^sub>P mk_or f x y \<longleftrightarrow> S \<Turnstile>\<^sub>P f x or f y"
proof -
  have X: "\<And>x' y'. S \<Turnstile>\<^sub>P (if in_or x' y' then y' else if in_or y' x' then x' else x' or y')
    \<longleftrightarrow> S \<Turnstile>\<^sub>P x' or y'"
    using in_entailment by auto
  show ?thesis
    unfolding mk_or_def ltl.split X by (cases "f x"; cases "f y"; simp) 
qed

lemma mk_or'_correct: 
  "S \<Turnstile>\<^sub>P mk_or' x y \<longleftrightarrow> S \<Turnstile>\<^sub>P x or y"
  unfolding mk_or'_def by (cases y; simp) 

end
