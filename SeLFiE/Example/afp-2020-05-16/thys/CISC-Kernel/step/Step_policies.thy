subsection \<open>Formulation of a subject-subject communication policy and an information flow 
policy, and showing both can be derived from subject-object configuration data\<close>

theory Step_policies
  imports Step_configuration
begin

subsubsection \<open>Specification\label{sect:policy_specification}\<close>

text \<open>In order to use CISK, we need an information flow policy @{term ifp}
  relation. 
  We also express a static subject-subject @{term sp_spec_subj_obj} and subject-object @{term sp_spec_subj_subj} access control policy
  for the implementation of the model. The following locale summarizes
  all properties we need.\<close>

locale policy_axioms =
  fixes sp_spec_subj_obj :: "'a \<Rightarrow> obj_id_t \<Rightarrow> mode_t \<Rightarrow> bool"
    and sp_spec_subj_subj :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and ifp :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

  assumes sp_spec_file_provider: "\<forall> p1 p2 f m1 m2 .
     sp_spec_subj_obj p1 (FILEP f) m1 \<and>
     sp_spec_subj_obj p2 (FILEP f) m2 \<longrightarrow> sp_spec_subj_subj p1 p2"

  and sp_spec_no_wronly_pages:
    "\<forall> p x . sp_spec_subj_obj p (PAGE x) WRITE \<longrightarrow> sp_spec_subj_obj p (PAGE x) READ"

  and ifp_reflexive:
    "\<forall> p . ifp p p"

  and ifp_compatible_with_sp_spec:
    "\<forall> a b . sp_spec_subj_subj a b \<longrightarrow> ifp a b \<and> ifp b a"

  and ifp_compatible_with_ipc:
    "\<forall> a b c x . (sp_spec_subj_subj a b
                  \<and> sp_spec_subj_obj b (PAGE x) WRITE  \<and> sp_spec_subj_obj c (PAGE x) READ)
                 \<longrightarrow> ifp a c"
begin (* empty *) end

subsubsection \<open>Derivation\<close>

text \<open>The configuration data only consists of a subject-object policy. 
We derive the subject-subject policy and the information flow policy from the configuration data and prove that properties we specified in Section~\ref{sect:policy_specification} are satisfied.\<close>

locale abstract_policy_derivation =
  fixes configuration_subj_obj :: "'a \<Rightarrow> obj_id_t \<Rightarrow> mode_t \<Rightarrow> bool"
begin

  definition "sp_spec_subj_obj a x m \<equiv>
    configuration_subj_obj a x m \<or> (\<exists> y . x = PAGE y \<and> m = READ \<and> configuration_subj_obj a x WRITE)"

  definition "sp_spec_subj_subj a b \<equiv>
    \<exists> f m1 m2 . sp_spec_subj_obj a (FILEP f) m1 \<and> sp_spec_subj_obj b (FILEP f) m2"

  definition "ifp a b \<equiv>
     sp_spec_subj_subj a b
   \<or> sp_spec_subj_subj b a
   \<or> (\<exists> c y . sp_spec_subj_subj a c
            \<and> sp_spec_subj_obj c (PAGE y) WRITE
            \<and> sp_spec_subj_obj b (PAGE y) READ)
   \<or> (a = b)"

text \<open>Show that the policies specified in Section~\ref{sect:policy_specification} can be derived from the configuration and their definitions.\<close>

  lemma correct:
    shows "policy_axioms sp_spec_subj_obj sp_spec_subj_subj ifp"
  proof (unfold_locales)
    show sp_spec_file_provider:
      "\<forall> p1 p2 f m1 m2 .
           sp_spec_subj_obj p1 (FILEP f) m1 \<and>
           sp_spec_subj_obj p2 (FILEP f) m2 \<longrightarrow> sp_spec_subj_subj p1 p2"
      unfolding sp_spec_subj_subj_def by auto
    show sp_spec_no_wronly_pages:
      "\<forall> p x . sp_spec_subj_obj p (PAGE x) WRITE \<longrightarrow> sp_spec_subj_obj p (PAGE x) READ"
      unfolding sp_spec_subj_obj_def by auto
    show ifp_reflexive:
      "\<forall> p . ifp p p"
      unfolding ifp_def by auto
    show ifp_compatible_with_sp_spec:
      "\<forall> a b . sp_spec_subj_subj a b \<longrightarrow> ifp a b \<and> ifp b a"
      unfolding ifp_def by auto
    show ifp_compatible_with_ipc:
      "\<forall> a b c x . (sp_spec_subj_subj a b
                  \<and> sp_spec_subj_obj b (PAGE x) WRITE  \<and> sp_spec_subj_obj c (PAGE x) READ)
                 \<longrightarrow> ifp a c"
      unfolding ifp_def by auto
  qed
end

type_synonym sp_subj_subj_t = "partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool"
type_synonym sp_subj_obj_t = "partition_id_t \<Rightarrow> obj_id_t \<Rightarrow> mode_t \<Rightarrow> bool"

interpretation Policy: abstract_policy_derivation "configured_subj_obj".
interpretation Policy_properties: policy_axioms Policy.sp_spec_subj_obj Policy.sp_spec_subj_subj Policy.ifp
  using Policy.correct by auto

lemma example_how_to_use_properties_in_proofs:
  shows "\<forall> p . Policy.ifp p p"
  using Policy_properties.ifp_reflexive by auto

end
