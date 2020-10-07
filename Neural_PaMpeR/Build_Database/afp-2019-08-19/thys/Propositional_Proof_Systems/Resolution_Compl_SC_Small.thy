theory Resolution_Compl_SC_Small
imports LSC_Resolution Resolution SC_Sema CNF_Formulas_Sema
begin

(* if you think that cnf transformation of LSC and Compactness are funky, this is the proof for you. *)
lemma Resolution_complete':
  assumes fin: "finite S"
  assumes val: "S \<TTurnstile> F"
  shows "\<Union>((cnf \<circ> nnf) ` ({\<^bold>\<not>F} \<union> S)) \<turnstile> \<box>"
proof -
  from fin obtain S' where S: "S = set_mset S'" using finite_set_mset_mset_set by blast
  have cnf: "\<forall>F \<in> set_mset (image_mset (cnf_form_of \<circ> nnf) (\<^bold>\<not> F, S')). is_cnf F" by(simp add: cnf_form_of_is is_nnf_nnf)
  note entailment_def[simp]
  from val
  have "S \<TTurnstile> \<^bold>\<not>(\<^bold>\<not>F)" by simp
  hence "S \<TTurnstile> \<^bold>\<not>(nnf (\<^bold>\<not>F))" by (simp add: nnf_semantics)
  hence "S \<TTurnstile> \<^bold>\<not>(cnf_form_of (nnf (\<^bold>\<not>F)))" by (simp add: cnf_form_semantics[OF is_nnf_nnf])
  hence "set_mset (image_mset nnf S') \<TTurnstile> \<^bold>\<not>(cnf_form_of (nnf (\<^bold>\<not>F)))" using S by (simp add: nnf_semantics)
  hence "set_mset (image_mset (cnf_form_of \<circ> nnf) S') \<TTurnstile> \<^bold>\<not>(cnf_form_of (nnf (\<^bold>\<not>F)))" by (simp add: cnf_form_semantics[OF is_nnf_nnf])
  hence "image_mset (cnf_form_of \<circ> nnf) S' \<Rightarrow> {#\<^bold>\<not>(cnf_form_of (nnf (\<^bold>\<not>F)))#}"
    unfolding SC_sound_complete sequent_intuitonistic_semantics .
  hence "image_mset (cnf_form_of \<circ> nnf) (\<^bold>\<not>F, S') \<Rightarrow> {#}" using NotR_inv by simp
  hence "image_mset (cnf_form_of \<circ> nnf) (\<^bold>\<not>F, S') \<Rightarrow>\<^sub>n" by (simp add: SC_LSC is_nnf_nnf nnf_cnf_form)
  with CSC_Resolution_pre have "\<Union>(cnf ` set_mset (image_mset (cnf_form_of \<circ> nnf) (\<^bold>\<not> F, S'))) \<turnstile> \<box>"  using cnf .
  thus ?thesis using cnf_cnf[where 'a='a, OF is_nnf_nnf] 
               unfolding set_image_mset image_comp comp_def S by simp
qed

corollary Resolution_complete_single:
  assumes "\<Turnstile> F"
  shows "cnf (nnf (\<^bold>\<not>F)) \<turnstile> \<box>"
  using assms Resolution_complete'[OF finite.emptyI, of F] 
  unfolding entailment_def comp_def by simp
(* the interesting thing that I want to state with this lemma (although much weaker than Resolution_complete (yes, the one from the other file without the '))
   is that you can prove all these things relatively easily. You don't need complicated things like compactness or that CNF transformation.
   (I did not feel like separating "that CNF transformation" into different files, so you'll either have to believe me
    or stare at the used lemmas and simp sets, etc. very intensely. *)

end
