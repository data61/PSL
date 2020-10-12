section \<open>Miscellaneous Lemmas\<close>
theory Dijkstra_Misc
imports Main
begin
  inductive_set least_map for f S where
    "\<lbrakk> x\<in>S; \<forall>x'\<in>S. f x \<le> f x' \<rbrakk> \<Longrightarrow> x \<in> least_map f S"

  lemma least_map_subset: "least_map f S \<subseteq> S"
    by (auto elim: least_map.cases)

  lemmas least_map_elemD = subsetD[OF least_map_subset]

  lemma least_map_leD:
    assumes "x \<in> least_map f S"
    assumes "y\<in>S"
    shows "f x \<le> f y"
    using assms
    by (auto elim: least_map.cases)

  lemma least_map_empty[simp]: "least_map f {} = {}"
    by (auto elim: least_map.cases)

  lemma least_map_singleton[simp]: "least_map (f::'a\<Rightarrow>'b::order) {x} = {x}"
    by (auto elim: least_map.cases intro!: least_map.intros simp: refl)

  lemma least_map_insert_min:
    fixes f::"'a\<Rightarrow>'b::order"
    assumes "\<forall>y\<in>S. f x \<le> f y"
    shows "x \<in> least_map f (insert x S)"
    using assms by (auto intro: least_map.intros)

  lemma least_map_insert_nmin: 
    "\<lbrakk> x\<in>least_map f S; f x \<le> f a \<rbrakk> \<Longrightarrow> x\<in>least_map f (insert a S)"
    by (auto elim: least_map.cases intro: least_map.intros)


context semilattice_inf
begin
  lemmas [simp] = inf_absorb1 inf_absorb2

  lemma inf_absorb_less[simp]:
    "a < b \<Longrightarrow> inf a b = a"
    "a < b \<Longrightarrow> inf b a = a"
    apply (metis le_iff_inf less_imp_le)
    by (metis inf_commute le_iff_inf less_imp_le)
end







end
