(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Implementation of the DRA Construction\<close>

theory DRA_Implementation
imports
  DRA_Instantiation
  LTL.Rewriting
  Transition_Systems_and_Automata.DRA_Translate
begin

text \<open>We convert the implicit automaton to its explicit representation
      and afterwards proof the final correctness theorem and the overall
      size bound.\<close>

subsection \<open>Generating the Explicit Automaton\<close>

definition dra_to_drai :: "('a, 'b) dra \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) drai"
where
  "dra_to_drai \<AA> \<Sigma> = drai \<Sigma> (initial \<AA>) (succ \<AA>) (accepting \<AA>)"

lemma dra_to_drai_language:
  "set \<Sigma> = alphabet \<AA> \<Longrightarrow> language (drai_dra (dra_to_drai \<AA> \<Sigma>)) = language \<AA>"
  by (simp add: dra_to_drai_def drai_dra_def)

definition drai_to_draei :: "('a, 'b) drai \<Rightarrow> ('a, nat) draei"
where
  "drai_to_draei = to_draei_impl (=) bot 2"

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

definition ltl_alphabet :: "'a ltlc \<Rightarrow> 'a set list"
where
  "ltl_alphabet \<phi> = map set (subseqs (atoms_ltlc_list \<phi>))"

definition ltlc_to_draei :: "'a ltlc \<Rightarrow> ('a set, nat) draei"
where
  "ltlc_to_draei \<phi> = drai_to_draei (dra_to_drai (ltl_to_dra_alphabet (simplify Slow (ltlc_to_ltln \<phi>)) (atoms_ltlc \<phi>)) (ltl_alphabet \<phi>))"



subsection \<open>Final Proof of Correctness\<close>

lemma dra_to_drai_rel:
  assumes
    "(\<Sigma>, alphabet A) \<in> \<langle>Id\<rangle> list_set_rel"
  shows
    "(dra_to_drai A \<Sigma>, A) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
proof -
  have "(A, A) \<in> \<langle>Id, Id\<rangle>dra_rel"
    by simp

  then have "(dra_to_drai A \<Sigma>, dra (alphabet A) (initial A) (succ A) (accepting A)) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
    unfolding dra_to_drai_def using assms by parametricity

  then show ?thesis
    by simp
qed

lemma draei_language:
  assumes 1:
    "(\<Sigma>, alphabet A) \<in> \<langle>Id\<rangle> list_set_rel"
  and
    "finite (DRA.nodes A)"
  shows
    "DRA.language (drae_dra (draei_drae (drai_to_draei (dra_to_drai A \<Sigma>)))) = DRA.language A"
proof -
  have "(dra_to_drai A \<Sigma>, A) \<in> \<langle>Id, Id\<rangle>drai_dra_rel"
    using dra_to_drai_rel 1 by fast

  then have "(drai_to_draei (dra_to_drai A \<Sigma>), to_draei A) \<in> \<langle>Id_on (dra.alphabet A), rel (dra_to_drai A \<Sigma>) A (=) bot 2\<rangle> draei_dra_rel"
    unfolding drai_to_draei_def
    using to_draei_impl_refine[unfolded autoref_tag_defs]
    apply parametricity
    by (simp_all add: assms is_bounded_hashcode_def bot_nat_def is_valid_def_hm_size_def)

  then have "(DRA.language ((drae_dra \<circ> draei_drae) (drai_to_draei (dra_to_drai A \<Sigma>))), DRA.language (id (to_draei A))) \<in> \<langle>\<langle>Id_on (dra.alphabet A)\<rangle> stream_rel\<rangle> set_rel"
    by parametricity

  then show ?thesis
    by (simp add: to_draei_def)
qed


lemma ltl_to_dra_alphabet_rel:
  "(ltl_alphabet \<phi>, alphabet (ltl_to_dra_alphabet \<psi> (atoms_ltlc \<phi>))) \<in> \<langle>Id\<rangle> list_set_rel"
  unfolding ltl_to_dra.ltl_to_dra_alphabet_alphabet ltl_alphabet_def
  by (simp add: list_set_rel_def atoms_ltlc_list_set atoms_ltlc_list_distinct in_br_conv subseqs_powset distinct_set_subseqs)

lemma ltl_to_dra_alphabet_nodes_finite:
  "finite (DRA.nodes (ltl_to_dra_alphabet \<phi> Ap))"
  using ltl_to_dra.ltl_to_dra_alphabet_nodes ltl_to_dra_nodes_finite finite_subset by fast

lemma ltlc_to_ltln_simplify_atoms:
  "atoms_ltln (simplify Slow (ltlc_to_ltln \<phi>)) \<subseteq> atoms_ltlc \<phi>"
  using ltlc_to_ltln_atoms simplify_atoms by fast

theorem final_correctness:
  "to_omega ` language (drae_dra (draei_drae (ltlc_to_draei \<phi>)))
    = language_ltlc \<phi> \<inter> {w. range w \<subseteq> Pow (atoms_ltlc \<phi>)}"
  unfolding ltlc_to_draei_def
  unfolding draei_language[OF ltl_to_dra_alphabet_rel ltl_to_dra_alphabet_nodes_finite]
  unfolding ltl_to_dra.ltl_to_dra_alphabet_language[OF ltlc_to_ltln_simplify_atoms]
  unfolding ltlc_to_ltln_atoms language_ltln_def language_ltlc_def ltlc_to_ltln_semantics simplify_correct ..

end
