theory ArityEtaExpansionSafe
imports EtaExpansionSafe ArityStack ArityEtaExpansion
begin

lemma Aeta_expand_safe:
  assumes "Astack S \<sqsubseteq> a"
  shows "(\<Gamma>, Aeta_expand a e, S) \<Rightarrow>\<^sup>* (\<Gamma>, e, S)"
proof-
  have "arg_prefix S = Rep_Arity (Astack S)"
    by (induction S arbitrary: a rule: arg_prefix.induct) (auto simp add: Arity.zero_Arity.rep_eq[symmetric])
  also
 from assms
  have "Rep_Arity a \<le> Rep_Arity (Astack S)" by (metis below_Arity.rep_eq)
  finally
  show ?thesis 
    by transfer (rule eta_expansion_safe')
qed


end
