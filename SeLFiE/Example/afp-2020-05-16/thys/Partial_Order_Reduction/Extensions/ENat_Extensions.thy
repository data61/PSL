section \<open>Extended Natural Numbers\<close>

theory ENat_Extensions
imports
  Coinductive.Coinductive_Nat
begin

  declare eSuc_enat[simp]
  declare iadd_Suc[simp] iadd_Suc_right[simp]
  declare enat_0[simp] enat_1[simp] one_eSuc[simp]
  declare enat_0_iff[iff] enat_1_iff[iff]
  declare Suc_ile_eq[iff]

  lemma enat_Suc0[simp]: "enat (Suc 0) = eSuc 0" by (metis One_nat_def one_eSuc one_enat_def)

  lemma le_epred[iff]: "l < epred k \<longleftrightarrow> eSuc l < k"
    by (metis eSuc_le_iff epred_eSuc epred_le_epredI less_le_not_le not_le)

  lemma eq_infI[intro]:
    assumes "\<And> n. enat n \<le> m"
    shows "m = \<infinity>"
    using assms by (metis enat_less_imp_le enat_ord_simps(5) less_le_not_le)

end