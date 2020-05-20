(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Implementation of the DRA Construction\<close>

theory DRA_Implementation
imports
  DRA_Construction
  LTL.Rewriting
  Transition_Systems_and_Automata.DRA_Translate
begin

subsection \<open>Generating the Explicit Automaton\<close>

text \<open>
  We convert the implicit automaton to its explicit representation
  and afterwards proof the final correctness theorem and the overall
  size bound.
\<close>

definition dra_to_drai :: "('a, 'b) dra \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) drai"
where
  "dra_to_drai \<AA> \<Sigma> = drai \<Sigma> (initial \<AA>) (transition \<AA>) (condition \<AA>)"

lemma dra_to_drai_language:
  "set \<Sigma> = alphabet \<AA> \<Longrightarrow> language (drai_dra (dra_to_drai \<AA> \<Sigma>)) = language \<AA>"
  by (simp add: dra_to_drai_def drai_dra_def)

definition drai_to_draei :: "nat \<Rightarrow> ('a, 'b :: hashable) drai \<Rightarrow> ('a, nat) draei"
where
  "drai_to_draei hms = to_draei_impl (=) bounded_hashcode_nat hms"


lemma dra_to_drai_rel:
  assumes
    "(\<Sigma>, alphabet A) \<in> \<langle>Id\<rangle> list_set_rel"
  shows
    "(dra_to_drai A \<Sigma>, A) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
proof -
  have "(A, A) \<in> \<langle>Id, Id\<rangle>dra_rel"
    by simp

  then have "(dra_to_drai A \<Sigma>, dra (alphabet A) (initial A) (transition A) (condition A)) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
    unfolding dra_to_drai_def using assms by parametricity

  then show ?thesis
    by simp
qed

lemma draei_language_rel:
  fixes
    A :: "('label, 'state :: hashable) dra"
  assumes
    "(\<Sigma>, alphabet A) \<in> \<langle>Id\<rangle> list_set_rel"
  and
    "finite (DRA.nodes A)"
  and
    "is_valid_def_hm_size TYPE('state) hms"
  shows
    "DRA.language (drae_dra (draei_drae (drai_to_draei hms (dra_to_drai A \<Sigma>)))) = DRA.language A"
proof -
  have "(dra_to_drai A \<Sigma>, A) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
    using dra_to_drai_rel assms by fast

  then have "(drai_to_draei hms (dra_to_drai A \<Sigma>), to_draei A) \<in> \<langle>Id_on (dra.alphabet A), rel (dra_to_drai A \<Sigma>) A (=) bounded_hashcode_nat hms\<rangle> draei_dra_rel"
    unfolding drai_to_draei_def
    using to_draei_impl_refine[unfolded autoref_tag_defs]
    by parametricity (simp_all add: assms is_bounded_hashcode_def bounded_hashcode_nat_bounds)

  then have "(DRA.language ((drae_dra \<circ> draei_drae) (drai_to_draei hms (dra_to_drai A \<Sigma>))), DRA.language (id (to_draei A))) \<in> \<langle>\<langle>Id_on (dra.alphabet A)\<rangle> stream_rel\<rangle> set_rel"
    by parametricity

  then show ?thesis
    by (simp add: to_draei_def)
qed


subsection \<open>Defining the Alphabet\<close>

fun atoms_ltlc_list :: "'a ltlc \<Rightarrow> 'a list"
where
  "atoms_ltlc_list true\<^sub>c = []"
| "atoms_ltlc_list false\<^sub>c = []"
| "atoms_ltlc_list prop\<^sub>c(q) = [q]"
| "atoms_ltlc_list (not\<^sub>c \<phi>) = atoms_ltlc_list \<phi>"
| "atoms_ltlc_list (\<phi> and\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (\<phi> or\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (\<phi> implies\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (X\<^sub>c \<phi>) = atoms_ltlc_list \<phi>"
| "atoms_ltlc_list (F\<^sub>c \<phi>) = atoms_ltlc_list \<phi>"
| "atoms_ltlc_list (G\<^sub>c \<phi>) = atoms_ltlc_list \<phi>"
| "atoms_ltlc_list (\<phi> U\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (\<phi> R\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (\<phi> W\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"
| "atoms_ltlc_list (\<phi> M\<^sub>c \<psi>) = List.union (atoms_ltlc_list \<phi>) (atoms_ltlc_list \<psi>)"

lemma atoms_ltlc_list_set:
  "set (atoms_ltlc_list \<phi>) = atoms_ltlc \<phi>"
  by (induction \<phi>) simp_all

lemma atoms_ltlc_list_distinct:
  "distinct (atoms_ltlc_list \<phi>)"
  by (induction \<phi>) simp_all

definition ltl_alphabet :: "'a list \<Rightarrow> 'a set list"
where
  "ltl_alphabet AP = map set (subseqs AP)"


subsection \<open>The Final Constant\<close>

text \<open>
  We require the quotient type to be hashable in order to efficiently explore the automaton.
\<close>

locale dra_implementation = dra_construction_size _ _ _ Abs
  for
    Abs :: "'a ltln \<Rightarrow> 'ltlq :: hashable"
begin

definition ltln_to_draei :: "'a list \<Rightarrow> 'a ltln \<Rightarrow> ('a set, nat) draei"
where
  "ltln_to_draei AP \<phi> = drai_to_draei (Suc (size \<phi>)) (dra_to_drai (ltl_to_dra_alphabet \<phi> (set AP)) (ltl_alphabet AP))"

definition ltlc_to_draei :: "'a ltlc \<Rightarrow> ('a set, nat) draei"
where
  "ltlc_to_draei \<phi> = ltln_to_draei (atoms_ltlc_list \<phi>) (simplify Slow (ltlc_to_ltln \<phi>))"


lemma ltl_to_dra_alphabet_rel:
  "distinct AP \<Longrightarrow> (ltl_alphabet AP, alphabet (ltl_to_dra_alphabet \<psi> (set AP))) \<in> \<langle>Id\<rangle> list_set_rel"
  unfolding ltl_to_dra_alphabet_alphabet ltl_alphabet_def
  by (simp add: list_set_rel_def in_br_conv subseqs_powset distinct_set_subseqs)

lemma ltlc_to_ltln_simplify_atoms:
  "atoms_ltln (simplify Slow (ltlc_to_ltln \<phi>)) \<subseteq> atoms_ltlc \<phi>"
  using ltlc_to_ltln_atoms simplify_atoms by fast

lemma valid_def_hm_size:
  "is_valid_def_hm_size TYPE('state) (Suc (size \<phi>))" for \<phi> :: "'a ltln"
  unfolding is_valid_def_hm_size_def
  using ltln.size_neq by auto

theorem final_correctness:
  "to_omega ` language (drae_dra (draei_drae (ltlc_to_draei \<phi>)))
    = language_ltlc \<phi> \<inter> {w. range w \<subseteq> Pow (atoms_ltlc \<phi>)}"
  unfolding ltlc_to_draei_def ltln_to_draei_def
  unfolding draei_language_rel[OF ltl_to_dra_alphabet_rel[OF atoms_ltlc_list_distinct] ltl_to_dra_alphabet_nodes_finite valid_def_hm_size]
  unfolding atoms_ltlc_list_set
  unfolding ltl_to_dra_alphabet_language[OF ltlc_to_ltln_simplify_atoms]
  unfolding ltlc_to_ltln_atoms language_ltln_def language_ltlc_def ltlc_to_ltln_semantics simplify_correct ..

end

end
