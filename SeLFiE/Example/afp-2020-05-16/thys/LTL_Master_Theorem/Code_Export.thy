(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Code export to Standard ML\<close>

theory Code_Export
imports
  "LTL_to_DRA/DRA_Instantiation"
  LTL.Code_Equations
  "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>Hashing Sets\<close>

global_interpretation comp_fun_commute "plus o cube o hashcode :: ('a :: hashable) \<Rightarrow> hashcode \<Rightarrow> hashcode"
  by unfold_locales (auto simp: cube_def)

lemma [code]:
  "hashcode (set xs) = fold (plus o cube o hashcode) (remdups xs) (uint32_of_nat (length (remdups xs)))"
  by (simp add: fold_set_fold_remdups length_remdups_card_conv)

lemma [code]:
  "hashcode (abs_ltln\<^sub>P \<phi>) = hashcode (min_dnf \<phi>)"
  by simp

lemma min_dnf_rep_abs[simp]:
  "min_dnf (Unf (rep_ltln\<^sub>Q (abs_ltln\<^sub>Q \<phi>))) = min_dnf (Unf \<phi>)"
  using Quotient3_ltln\<^sub>Q ltl_prop_equiv_min_dnf ltl_prop_unfold_equiv_def rep_abs_rsp by fastforce

lemma [code]:
  "hashcode (abs_ltln\<^sub>Q \<phi>) = hashcode (min_dnf (Unf \<phi>))"
  by simp


subsection \<open>LTL to DRA\<close>

declare ltl_to_dra\<^sub>P.af_letter\<^sub>F_lifted_semantics [code]
declare ltl_to_dra\<^sub>P.af_letter\<^sub>G_lifted_semantics [code]
declare ltl_to_dra\<^sub>P.af_letter\<^sub>\<nu>_lifted_semantics [code]

declare ltl_to_dra\<^sub>Q.af_letter\<^sub>F_lifted_semantics [code]
declare ltl_to_dra\<^sub>Q.af_letter\<^sub>G_lifted_semantics [code]
declare ltl_to_dra\<^sub>Q.af_letter\<^sub>\<nu>_lifted_semantics [code]

definition atoms_ltlc_list_literals :: "String.literal ltlc \<Rightarrow> String.literal list"
where
  "atoms_ltlc_list_literals = atoms_ltlc_list"

definition ltlc_to_draei_literals :: "equiv \<Rightarrow> String.literal ltlc \<Rightarrow> (String.literal set, nat) draei"
where
  "ltlc_to_draei_literals = ltlc_to_draei"

definition sort_transitions :: "(nat \<times> String.literal set \<times> nat) list \<Rightarrow> (nat \<times> String.literal set \<times> nat) list"
where
  "sort_transitions = sort_key fst"

export_code True_ltlc Iff_ltlc ltlc_to_draei_literals Prop PropUnfold
  alphabetei initialei transitionei conditionei
  integer_of_nat atoms_ltlc_list_literals sort_transitions set
  in SML module_name LTL file_prefix LTL_to_DRA



subsection \<open>LTL to NBA\<close>

(* TODO *)



subsection \<open>LTL to LDBA\<close>

(* TODO *)



end
