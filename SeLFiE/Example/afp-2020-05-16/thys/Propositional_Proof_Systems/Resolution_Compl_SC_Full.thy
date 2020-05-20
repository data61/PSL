theory Resolution_Compl_SC_Full
imports LSC_Resolution Resolution SC_Sema Compactness
begin

theorem Resolution_complete:
  fixes S :: "'a :: countable formula set"
  assumes val: "S \<TTurnstile> F"
  shows "\<Union>((cnf \<circ> nnf) ` ({\<^bold>\<not>F} \<union> S)) \<turnstile> \<box>"
  (* look: S may be infinite. *)
proof -
  let ?mun = "\<lambda>s. \<Union>((cnf \<circ> nnf) ` s)"
  (* note: there's an alternate version of this proof with CSC_Resolution_pre and the CNF_Semantics *)
  from compact_entailment[OF val] obtain S'' where fin: "finite S''" and su: "S'' \<subseteq> S" and val': " S'' \<TTurnstile> F" by blast
  from fin obtain S' where S: "S'' = set_mset S'" using finite_set_mset_mset_set by blast
  have cnf: "\<forall>F \<in> set_mset (image_mset (cnf_form_of \<circ> nnf) (\<^bold>\<not> F, S')). is_cnf F" by(simp add: cnf_form_of_is is_nnf_nnf)
  note entailment_def[simp]
  from val' have "S'' \<TTurnstile> \<^bold>\<not>(\<^bold>\<not>F)" by simp
  hence "S' \<Rightarrow> {#\<^bold>\<not>(\<^bold>\<not>F)#}"
    unfolding SC_sound_complete sequent_intuitonistic_semantics S .
  hence "\<^bold>\<not>F, S' \<Rightarrow> {#}" by (simp add: NotR_inv)
  hence "image_mset nnf (\<^bold>\<not>F, S') \<Rightarrow> {#}" using LSC_NNF SC_LSC by blast
  hence "image_mset nnf (\<^bold>\<not>F, S') \<Rightarrow>\<^sub>n" by (simp add: SC_LSC is_nnf_nnf)
  with LSC_Resolution have "\<Union>(cnf ` nnf ` set_mset (image_mset nnf (\<^bold>\<not> F, S'))) \<turnstile> \<box>"  .
  hence "?mun ({\<^bold>\<not> F} \<union> S'') \<turnstile> \<box>" 
    unfolding set_image_mset image_comp comp_def S is_nnf_nnf_id[OF is_nnf_nnf] by simp
  from Resolution_weaken[OF this, of "?mun S"] show ?thesis using su by (metis UN_Un Un_left_commute sup.order_iff)
qed

end
