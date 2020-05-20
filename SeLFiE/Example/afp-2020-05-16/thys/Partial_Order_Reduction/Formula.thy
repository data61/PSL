section \<open>LTL Formulae\<close>

theory Formula
imports
  "Basics/Stuttering"
  Stuttering_Equivalence.PLTL
begin

  locale formula =
    fixes \<phi> :: "'a pltl"
  begin

    definition language :: "'a stream set"
      where "language \<equiv> {w. snth w \<Turnstile>\<^sub>p \<phi>}"
  
    lemma language_entails[iff]: "w \<in> language \<longleftrightarrow> snth w \<Turnstile>\<^sub>p \<phi>" unfolding language_def by simp

  end

  locale formula_next_free =
    formula \<phi>
    for \<phi> :: "'a pltl"
    +
    assumes next_free: "next_free \<phi>"
  begin

    lemma stutter_equivalent_entails[dest]: "u \<approx> v \<Longrightarrow> u \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> v \<Turnstile>\<^sub>p \<phi>"
      using next_free_stutter_invariant next_free by blast

  end

end
