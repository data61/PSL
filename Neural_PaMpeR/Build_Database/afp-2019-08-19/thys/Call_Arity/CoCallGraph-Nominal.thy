theory "CoCallGraph-Nominal"
imports CoCallGraph "Launchbury.Nominal-HOLCF"
begin

instantiation CoCalls :: pt
begin
  lift_definition permute_CoCalls :: "perm \<Rightarrow> CoCalls \<Rightarrow> CoCalls" is "permute"
    by (auto intro!: symI elim: symE simp add: mem_permute_set)
instance
  apply standard
  apply (transfer, simp)+
  done
end

instance CoCalls :: cont_pt
  apply standard
  apply (rule contI2)
  apply (rule monofunI)
  apply transfer
  apply (metis (full_types) True_eqvt subset_eqvt)
  apply (thin_tac "chain _")+
  apply transfer
  apply simp
  done

lemmas lub_eqvt[OF exists_lub, simp, eqvt]

lemma cc_restr_perm:
  fixes G :: CoCalls
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "cc_restr S (p \<bullet> G) = cc_restr S G"
  using assms
  apply -
  apply transfer
  apply (auto simp add: mem_permute_set)
  apply (subst (asm) perm_supp_eq, simp add: supp_minus_perm, metis (full_types) fresh_def fresh_star_def supp_set_elem_finite)+
  apply assumption
  apply (subst perm_supp_eq, simp add: supp_minus_perm, metis (full_types) fresh_def fresh_star_def supp_set_elem_finite)+
  apply assumption
  done



lemma inCC_eqvt[eqvt]: "\<pi> \<bullet> (x--y\<in>G) = (\<pi>\<bullet>x)--(\<pi>\<bullet>y)\<in>(\<pi>\<bullet>G)"
  by transfer auto
lemma cc_restr_eqvt[eqvt]: "\<pi> \<bullet> cc_restr S G = cc_restr (\<pi> \<bullet> S) (\<pi> \<bullet> G)"
  by transfer (perm_simp, rule)
lemma ccProd_eqvt[eqvt]: "\<pi> \<bullet> ccProd S S' = ccProd (\<pi> \<bullet> S) (\<pi> \<bullet>  S')" 
  by transfer (perm_simp, rule)
lemma ccSquare_eqvt[eqvt]: "\<pi> \<bullet> ccSquare S = ccSquare (\<pi> \<bullet> S)"
  unfolding ccSquare_def
  by perm_simp rule
lemma ccNeighbors_eqvt[eqvt]: "\<pi> \<bullet> ccNeighbors S G = ccNeighbors (\<pi> \<bullet> S) (\<pi> \<bullet> G)"
  by transfer (perm_simp, rule)


end
