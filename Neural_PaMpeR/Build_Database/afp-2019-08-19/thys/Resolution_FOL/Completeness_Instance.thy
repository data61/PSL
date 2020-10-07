section \<open>Instance of completeness theorem\<close>

theory Completeness_Instance imports Unification_Theorem Completeness begin

interpretation unification using unification by unfold_locales auto

thm lifting

lemma lift:
  assumes fin: "finite C \<and> finite D"
  assumes apart: "vars\<^sub>l\<^sub>s C \<inter> vars\<^sub>l\<^sub>s D = {}"
  assumes inst\<^sub>1: "instance_of\<^sub>l\<^sub>s C' C"
  assumes inst\<^sub>2: "instance_of\<^sub>l\<^sub>s D' D"
  assumes appl: "applicable C' D' L' M' \<sigma>"
  shows "\<exists>L M \<tau>. applicable C D L M \<tau> \<and>
                   instance_of\<^sub>l\<^sub>s (resolution C' D' L' M' \<sigma>) (resolution C D L M \<tau>)"
using assms lifting by metis

thm completeness

theorem complete:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::hterm fun_denot) (G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
using assms completeness by -

thm completeness_countable

theorem complete_countable:
  assumes inf_uni: "infinite (UNIV :: ('u :: countable) set)"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::'u fun_denot) (G::'u pred_denot). \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
using assms completeness_countable by -

thm completeness_nat

theorem complete_nat:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::nat fun_denot) (G::nat pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
using assms completeness_nat by -

end
