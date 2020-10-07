theory Acceptance_Refine
imports "Acceptance" "Refine"
begin

  abbreviation (input) "pred_rel A \<equiv> A \<rightarrow> bool_rel"
  abbreviation (input) "rabin_rel A \<equiv> pred_rel A \<times>\<^sub>r pred_rel A"

  lemma rabin_param[param]: "(rabin, rabin) \<in> rabin_rel A \<rightarrow> pred_rel (\<langle>A\<rangle> stream_rel)"
    unfolding rabin_def by parametricity
  lemma gen_param[param]: "(gen, gen) \<in> (A \<rightarrow> pred_rel B) \<rightarrow> (\<langle>A\<rangle> list_rel \<rightarrow> pred_rel B)"
    unfolding gen_def by parametricity
  lemma cogen_param[param]: "(cogen, cogen) \<in> (A \<rightarrow> pred_rel B) \<rightarrow> (\<langle>A\<rangle> list_rel \<rightarrow> pred_rel B)"
    unfolding cogen_def by parametricity

end