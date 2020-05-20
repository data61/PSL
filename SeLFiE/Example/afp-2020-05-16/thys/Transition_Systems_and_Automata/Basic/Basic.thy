section \<open>Basics\<close>

theory Basic
imports Main
begin

  subsection \<open>Miscellaneous\<close>

  abbreviation (input) "const x \<equiv> \<lambda> _. x"

  lemmas [simp] = map_prod.id map_prod.comp[symmetric]
  lemma prod_UNIV[iff]: "A \<times> B = UNIV \<longleftrightarrow> A = UNIV \<and> B = UNIV" by auto
  lemma prod_singleton:
    "fst ` A = {x} \<Longrightarrow> A = fst ` A \<times> snd ` A"
    "snd ` A = {y} \<Longrightarrow> A = fst ` A \<times> snd ` A"
    by force+

  lemma infinite_subset[trans]: "infinite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> infinite B" using infinite_super by this
  lemma finite_subset[trans]: "A \<subseteq> B \<Longrightarrow> finite B \<Longrightarrow> finite A" using finite_subset by this

  declare infinite_coinduct[case_names infinite, coinduct pred: infinite]
  lemma infinite_psubset_coinduct[case_names infinite, consumes 1]:
    assumes "R A"
    assumes "\<And> A. R A \<Longrightarrow> \<exists> B \<subset> A. R B"
    shows "infinite A"
  proof
    show "False" if "finite A" using that assms by (induct rule: finite_psubset_induct) (auto)
  qed

  (* TODO: why are there two copies of this theorem? *)
  thm inj_on_subset subset_inj_on

  lemma inj_inj_on[dest]: "inj f \<Longrightarrow> inj_on f S" using inj_on_subset by auto

end
