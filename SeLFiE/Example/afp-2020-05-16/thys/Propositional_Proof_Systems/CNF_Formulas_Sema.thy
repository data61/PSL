theory CNF_Formulas_Sema
imports CNF_Sema CNF_Formulas Sema
begin

lemma nnf_semantics: "\<A> \<Turnstile> nnf F \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F rule: nnf.induct; simp)
  
lemma cnf_semantics: "is_nnf F \<Longrightarrow> cnf_semantics \<A> (cnf F) \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F rule: cnf.induct; simp add: cnf_semantics_def clause_semantics_def ball_Un; metis Un_iff)
  (* surprisingly, the solvers are smarter if this one is done on mutlisets.*)

lemma cnf_form_semantics: 
  fixes F :: "'a formula"
  assumes nnf: "is_nnf F"
  shows "\<A> \<Turnstile> cnf_form_of F \<longleftrightarrow> \<A> \<Turnstile> F"
proof -
  define cnf_semantics_list
    where "cnf_semantics_list \<A> S \<longleftrightarrow> (\<forall>s \<in> set S. \<exists>l \<in> set s. lit_semantics \<A> (l :: 'a literal))"
    for \<A> S
  have tcn: "cnf F = set (map set (cnf_lists F))" using nnf
    by(induction F rule: cnf.induct) (auto simp add: image_UN image_comp comp_def )
  have "\<A> \<Turnstile> F \<longleftrightarrow> cnf_semantics \<A> (cnf F)" using cnf_semantics[OF nnf] by simp
  also have "\<dots> = cnf_semantics \<A> (set (map set (cnf_lists F)))" unfolding tcn ..
  also have "\<dots> = cnf_semantics_list \<A> (cnf_lists F)"
    unfolding cnf_semantics_def clause_semantics_def cnf_semantics_list_def by fastforce
  also have "\<dots> = \<A> \<Turnstile> (cnf_form_of F)" using nnf
    by(induction F rule: cnf_lists.induct;
       simp add: cnf_semantics_list_def cnf_form_of_defs  ball_Un bex_Un)
  finally show ?thesis by simp
qed
  
corollary "\<exists>G. \<A> \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> G \<and> is_cnf G"
  using cnf_form_of_is cnf_form_semantics is_nnf_nnf nnf_semantics by blast

end
