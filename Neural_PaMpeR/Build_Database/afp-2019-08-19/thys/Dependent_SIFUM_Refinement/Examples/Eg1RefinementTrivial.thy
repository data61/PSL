theory Eg1RefinementTrivial
imports Eg1
        "../CompositionalRefinement"
        Dependent_SIFUM_Type_Systems.TypeSystem
begin

sublocale sifum_example \<subseteq>
    sifum_refinement_same_mem dma \<C>_vars \<C> eval\<^sub>w eval\<^sub>w
      by(unfold_locales)

context sifum_example begin

text \<open>This predicate can be used to express arbitrary relational invariants for
  compiler-specific features, but for this trivial case the vacuous one is fine.
\<close>
definition P_true :: "('a \<times> 'a) set"
where
  "P_true  \<equiv> UNIV"

lemma Id_secure_refinement:
  "secure_refinement R Id P_true"
  unfolding secure_refinement_def
  proof(safe)
    show "closed_others Id"
    unfolding closed_others_def Id_def by blast
  next
    show "preserves_modes_mem Id"
    unfolding preserves_modes_mem_def Id_def by blast
  next
    fix c\<^sub>1\<^sub>A mds mem\<^sub>1 c\<^sub>1\<^sub>C c\<^sub>1\<^sub>C' mds' mem\<^sub>1'
    assume step: "(\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C) \<in> eval\<^sub>w"
    show
      "\<exists>n c\<^sub>1\<^sub>A'.
          neval \<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C n \<langle>c\<^sub>1\<^sub>A', mds', mem\<^sub>1'\<rangle>\<^sub>C \<and>
          (\<langle>c\<^sub>1\<^sub>A', mds', mem\<^sub>1'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C) \<in> Id \<and>
          (\<forall>c\<^sub>2\<^sub>A mem\<^sub>2 c\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2'.
              (\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> R \<and>
              (\<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> Id \<and>
              (\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> P_true \<and>
              neval \<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C n \<langle>c\<^sub>2\<^sub>A', mds', mem\<^sub>2'\<rangle>\<^sub>C \<longrightarrow>
              (\<exists>c\<^sub>2\<^sub>C'.
                  (\<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C)
                  \<in> eval\<^sub>w \<and>
                  (\<langle>c\<^sub>2\<^sub>A', mds', mem\<^sub>2'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C) \<in> Id \<and>
                  (\<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C) \<in> P_true))"
    proof -
      let ?n = "Suc 0"
      let ?c\<^sub>1\<^sub>A' = c\<^sub>1\<^sub>C'
      from step have "neval \<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C ?n \<langle>?c\<^sub>1\<^sub>A', mds', mem\<^sub>1'\<rangle>\<^sub>C"
        by simp
      moreover have "(\<langle>?c\<^sub>1\<^sub>A', mds', mem\<^sub>1'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C) \<in> Id"
        by simp
      moreover have "(\<forall>c\<^sub>2\<^sub>A mem\<^sub>2 c\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2'.
              (\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> R \<and>
              (\<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> Id \<and>
              (\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> P_true \<and>
              neval \<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<rangle>\<^sub>C ?n \<langle>c\<^sub>2\<^sub>A', mds', mem\<^sub>2'\<rangle>\<^sub>C \<longrightarrow>
              (\<exists>c\<^sub>2\<^sub>C'.
                  (\<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C)
                  \<in> eval\<^sub>w \<and>
                  (\<langle>c\<^sub>2\<^sub>A', mds', mem\<^sub>2'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C) \<in> Id \<and>
                  (\<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C) \<in> P_true))"
        using step
        unfolding P_true_def
        by clarsimp
      ultimately show ?thesis by blast
    qed
  next
    show "closed_glob_consistent P_true"
      by(auto simp: closed_glob_consistent_def P_true_def)
  qed

text \<open>
  This doesn't really mean much, but shows the lemmas in action.
  (I suspect that @{term "R\<^sub>C_of R Id"} is equivalent to @{term R}. But who cares?)
\<close>
lemma "strong_low_bisim_mm (gen_refine.R\<^sub>C_of (\<R> \<Gamma> \<S> P) Id P_true)"
  apply(rule R\<^sub>C_of_strong_low_bisim_mm)
   apply(rule \<R>_bisim)
  apply(rule Id_secure_refinement)
  unfolding P_true_def sym_def apply blast
  done

end

end
