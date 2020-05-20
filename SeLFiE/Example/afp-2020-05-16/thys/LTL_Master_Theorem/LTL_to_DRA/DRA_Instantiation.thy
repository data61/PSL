(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Instantiation of the LTL to DRA construction\<close>

theory DRA_Instantiation
imports
  DRA_Implementation
  LTL.Equivalence_Relations
  LTL.Disjunctive_Normal_Form
  "../Logical_Characterization/Extra_Equivalence_Relations"
  "HOL-Library.Log_Nat"
  Deriving.Derive
begin

subsection \<open>Hash Functions for Quotient Types\<close>

derive hashable ltln

definition "cube a = a * a * a"


instantiation set :: (hashable) hashable
begin

definition [simp]: "hashcode (x :: 'a set) = Finite_Set.fold (plus o cube o hashcode) (uint32_of_nat (card x)) x"
definition "def_hashmap_size = (\<lambda>_ :: 'a set itself. 2 * def_hashmap_size TYPE('a))"

instance
proof
  from def_hashmap_size[where ?'a = "'a"]
  show "1 < def_hashmap_size TYPE('a set)"
    by (simp add: def_hashmap_size_set_def)
qed

end


instantiation fset :: (hashable) hashable
begin

definition [simp]: "hashcode (x :: 'a fset) = hashcode (fset x)"
definition "def_hashmap_size = (\<lambda>_ :: 'a fset itself. 2 * def_hashmap_size TYPE('a))"

instance
proof
  from def_hashmap_size[where ?'a = "'a"]
  show "1 < def_hashmap_size TYPE('a fset)"
    by (simp add: def_hashmap_size_fset_def)
qed

end


instantiation ltln\<^sub>P:: (hashable) hashable
begin

definition [simp]: "hashcode (\<phi> :: 'a ltln\<^sub>P) = hashcode (min_dnf (rep_ltln\<^sub>P \<phi>))"
definition "def_hashmap_size = (\<lambda>_ :: 'a ltln\<^sub>P itself. def_hashmap_size TYPE('a ltln))"

instance
proof
  from def_hashmap_size[where ?'a = "'a"]
  show "1 < def_hashmap_size TYPE('a ltln\<^sub>P)"
    by (simp add: def_hashmap_size_ltln\<^sub>P_def def_hashmap_size_ltln_def)
qed

end


instantiation ltln\<^sub>Q :: (hashable) hashable
begin

definition [simp]: "hashcode (\<phi> :: 'a ltln\<^sub>Q) = hashcode (min_dnf (Unf (rep_ltln\<^sub>Q \<phi>)))"
definition "def_hashmap_size = (\<lambda>_ :: 'a ltln\<^sub>Q itself. def_hashmap_size TYPE('a ltln))"

instance
proof
  from def_hashmap_size[where ?'a = "'a"]
  show "1 < def_hashmap_size TYPE('a ltln\<^sub>Q)"
    by (simp add: def_hashmap_size_ltln\<^sub>Q_def def_hashmap_size_ltln_def)
qed

end


subsection \<open>Interpretations with Equivalence Relations\<close>

text \<open>
  We instantiate the construction locale with propositional equivalence
  and obtain a function converting a formula into an abstract automaton.
\<close>

global_interpretation ltl_to_dra\<^sub>P: dra_implementation "(\<sim>\<^sub>P)" id rep_ltln\<^sub>P abs_ltln\<^sub>P
  defines ltl_to_dra\<^sub>P = ltl_to_dra\<^sub>P.ltl_to_dra
    and ltl_to_dra_restricted\<^sub>P = ltl_to_dra\<^sub>P.ltl_to_dra_restricted
    and ltl_to_dra_alphabet\<^sub>P = ltl_to_dra\<^sub>P.ltl_to_dra_alphabet
    and \<AA>'\<^sub>P = ltl_to_dra\<^sub>P.\<AA>'
    and \<AA>\<^sub>1\<^sub>P = ltl_to_dra\<^sub>P.\<AA>\<^sub>1
    and \<AA>\<^sub>2\<^sub>P = ltl_to_dra\<^sub>P.\<AA>\<^sub>2
    and \<AA>\<^sub>3\<^sub>P = ltl_to_dra\<^sub>P.\<AA>\<^sub>3
    and \<AA>\<^sub>\<nu>_FG\<^sub>P = ltl_to_dra\<^sub>P.\<AA>\<^sub>\<nu>_FG
    and \<AA>\<^sub>\<mu>_GF\<^sub>P = ltl_to_dra\<^sub>P.\<AA>\<^sub>\<mu>_GF
    and af_letter\<^sub>G\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>G
    and af_letter\<^sub>F\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>F
    and af_letter\<^sub>G_lifted\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>G_lifted
    and af_letter\<^sub>F_lifted\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>F_lifted
    and af_letter\<^sub>\<nu>_lifted\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>\<nu>_lifted
    and \<CC>\<^sub>P = ltl_to_dra\<^sub>P.\<CC>
    and af_letter\<^sub>\<nu>\<^sub>P = ltl_to_dra\<^sub>P.af_letter\<^sub>\<nu>
    and ltln_to_draei\<^sub>P = ltl_to_dra\<^sub>P.ltln_to_draei
    and ltlc_to_draei\<^sub>P = ltl_to_dra\<^sub>P.ltlc_to_draei
  by unfold_locales (meson Quotient_abs_rep Quotient_ltln\<^sub>P, simp_all add: Quotient_abs_rep Quotient_ltln\<^sub>P ltln\<^sub>P.abs_eq_iff prop_equiv_card prop_equiv_finite)

thm ltl_to_dra\<^sub>P.ltl_to_dra_language
thm ltl_to_dra\<^sub>P.ltl_to_dra_size
thm ltl_to_dra\<^sub>P.final_correctness

text \<open>
  Similarly, we instantiate the locale with a different equivalence relation and obtain another
  constant for translation of LTL to deterministic Rabin automata.
\<close>

global_interpretation ltl_to_dra\<^sub>Q: dra_implementation "(\<sim>\<^sub>Q)" Unf rep_ltln\<^sub>Q abs_ltln\<^sub>Q
  defines ltl_to_dra\<^sub>Q = ltl_to_dra\<^sub>Q.ltl_to_dra
    and ltl_to_dra_restricted\<^sub>Q = ltl_to_dra\<^sub>Q.ltl_to_dra_restricted
    and ltl_to_dra_alphabet\<^sub>Q = ltl_to_dra\<^sub>Q.ltl_to_dra_alphabet
    and \<AA>'\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>'
    and \<AA>\<^sub>1\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>\<^sub>1
    and \<AA>\<^sub>2\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>\<^sub>2
    and \<AA>\<^sub>3\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>\<^sub>3
    and \<AA>\<^sub>\<nu>_FG\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>\<^sub>\<nu>_FG
    and \<AA>\<^sub>\<mu>_GF\<^sub>Q = ltl_to_dra\<^sub>Q.\<AA>\<^sub>\<mu>_GF
    and af_letter\<^sub>G\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>G
    and af_letter\<^sub>F\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>F
    and af_letter\<^sub>G_lifted\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>G_lifted
    and af_letter\<^sub>F_lifted\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>F_lifted
    and af_letter\<^sub>\<nu>_lifted\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>\<nu>_lifted
    and \<CC>\<^sub>Q = ltl_to_dra\<^sub>Q.\<CC>
    and af_letter\<^sub>\<nu>\<^sub>Q = ltl_to_dra\<^sub>Q.af_letter\<^sub>\<nu>
    and ltln_to_draei\<^sub>Q = ltl_to_dra\<^sub>Q.ltln_to_draei
    and ltlc_to_draei\<^sub>Q = ltl_to_dra\<^sub>Q.ltlc_to_draei
  by unfold_locales (meson Quotient_abs_rep Quotient_ltln\<^sub>Q, simp_all add: Quotient_abs_rep Quotient_ltln\<^sub>Q ltln\<^sub>Q.abs_eq_iff nested_prop_atoms_Unf prop_unfold_equiv_finite prop_unfold_equiv_card)

thm ltl_to_dra\<^sub>Q.ltl_to_dra_language
thm ltl_to_dra\<^sub>Q.ltl_to_dra_size
thm ltl_to_dra\<^sub>Q.final_correctness


text \<open>
  We allow the user to choose one of the two equivalence relations.
\<close>

datatype equiv = Prop | PropUnfold

fun ltlc_to_draei :: "equiv \<Rightarrow> ('a :: hashable) ltlc \<Rightarrow> ('a set, nat) draei"
where
  "ltlc_to_draei Prop = ltlc_to_draei\<^sub>P"
| "ltlc_to_draei PropUnfold = ltlc_to_draei\<^sub>Q"

end
