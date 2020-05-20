theory ArityEtaExpansion
imports EtaExpansion "Arity-Nominal" TransformTools
begin

lift_definition Aeta_expand :: "Arity \<Rightarrow> exp \<Rightarrow> exp" is "eta_expand".

lemma Aeta_expand_eqvt[eqvt]: "\<pi> \<bullet> Aeta_expand a e = Aeta_expand (\<pi> \<bullet> a) (\<pi> \<bullet> e)"
  apply (cases a)
  apply simp
  apply transfer
  apply simp
  done

lemma Aeta_expand_0[simp]: "Aeta_expand 0 e = e"
  by transfer simp

lemma Aeta_expand_inc[simp]: "Aeta_expand (inc\<cdot>n) e = (Lam [fresh_var e]. Aeta_expand n (App e (fresh_var e)))"
  apply (simp add: inc_def)
  by transfer simp

lemma subst_Aeta_expand:
  "(Aeta_expand n e)[x::=y] = Aeta_expand n e[x::=y]"
  by transfer (rule subst_eta_expand)

lemma isLam_Aeta_expand: "isLam e \<Longrightarrow> isLam (Aeta_expand a e)"
  by transfer (rule isLam_eta_expand)

lemma isVal_Aeta_expand: "isVal e \<Longrightarrow> isVal (Aeta_expand a e)"
  by transfer (rule isVal_eta_expand)

lemma Aeta_expand_fresh[simp]: "a \<sharp> Aeta_expand n e = a \<sharp> e" by transfer simp
lemma Aeta_expand_fresh_star[simp]: "a \<sharp>* Aeta_expand n e = a \<sharp>* e" by (auto simp add: fresh_star_def)

interpretation supp_bounded_transform Aeta_expand
  apply standard
  using Aeta_expand_fresh
  apply (auto simp add: fresh_def)
  done

end
