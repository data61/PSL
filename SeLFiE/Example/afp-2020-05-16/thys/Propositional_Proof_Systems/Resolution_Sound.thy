theory Resolution_Sound
imports Resolution CNF_Formulas_Sema
begin

(* there is one theory where we show Resolution completeness entirely without the relation to 
normal formulas. We haven't done the same for soundness, because we do not want too many theory files. *)

lemma Resolution_insert: "S \<turnstile> R \<Longrightarrow> cnf_semantics \<A> S \<Longrightarrow> cnf_semantics \<A> {R}"
by(induction  rule: Resolution.induct;
   clarsimp simp add: cnf_semantics_def clause_semantics_def lit_semantics_cases split: literal.splits;
   blast)

(* Schöning's resolution lemma. We don't use it. *)
lemma "S \<turnstile> R \<Longrightarrow> cnf_semantics \<A> S \<longleftrightarrow> cnf_semantics \<A> (R \<triangleright> S)"
  using Resolution_insert cnf_semantics_def by (metis insert_iff)

corollary Resolution_cnf_sound: assumes "S \<turnstile> \<box>" shows "\<not> cnf_semantics \<A> S"
proof(rule notI)
  assume "cnf_semantics \<A> S"
  with Resolution_insert assms have "cnf_semantics \<A> {\<box>}" .
  thus False by(simp add: cnf_semantics_def clause_semantics_def)
qed

corollary Resolution_sound: 
  assumes rp: "cnf (nnf F) \<turnstile> \<box>"
  shows "\<not> \<A> \<Turnstile> F"
proof -
  from Resolution_cnf_sound rp have "\<not> cnf_semantics \<A> (cnf (nnf F))" .
  hence "\<not>\<A> \<Turnstile> nnf F" unfolding cnf_semantics[OF is_nnf_nnf] .
  thus ?thesis unfolding nnf_semantics .
qed

end
