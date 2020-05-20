theory Quasi_Order
imports Main
begin

locale quasi_order =
fixes qle :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 60)
assumes qle_refl[iff]: "x \<preceq> x"
and qle_trans: "x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
begin

definition in_qle :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infix "\<in>\<^sub>\<preceq>" 60) where
 "x \<in>\<^sub>\<preceq> M \<equiv> \<exists>y \<in> M. x \<preceq> y"

definition subseteq_qle :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<subseteq>\<^sub>\<preceq>" 60) where
 "M \<subseteq>\<^sub>\<preceq> N \<equiv> \<forall>x \<in> M. x \<in>\<^sub>\<preceq> N"

definition seteq_qle :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "=\<^sub>\<preceq>" 60) where
 "M =\<^sub>\<preceq> N  \<equiv>  M \<subseteq>\<^sub>\<preceq> N \<and> N \<subseteq>\<^sub>\<preceq> M"

lemmas "defs" = in_qle_def subseteq_qle_def seteq_qle_def

lemma subseteq_qle_refl[simp]: "M \<subseteq>\<^sub>\<preceq> M"
by(auto simp add: subseteq_qle_def in_qle_def)

lemma subseteq_qle_trans: "A \<subseteq>\<^sub>\<preceq> B \<Longrightarrow> B \<subseteq>\<^sub>\<preceq> C \<Longrightarrow> A \<subseteq>\<^sub>\<preceq> C"
by (simp add: subseteq_qle_def in_qle_def) (metis qle_trans)

lemma empty_subseteq_qle[simp]: "{} \<subseteq>\<^sub>\<preceq> A"
by (simp add: subseteq_qle_def)

lemma subseteq_qleI2: "(\<And>x. x \<in> M \<Longrightarrow> \<exists>y \<in> N. x \<preceq> y) \<Longrightarrow> M \<subseteq>\<^sub>\<preceq> N"
by (auto simp add: subseteq_qle_def in_qle_def)

lemma subseteq_qleD2: "M \<subseteq>\<^sub>\<preceq> N \<Longrightarrow> x \<in> M \<Longrightarrow> \<exists>y \<in> N. x \<preceq> y"
by (auto simp add: subseteq_qle_def in_qle_def)

lemma seteq_qle_refl[iff]: "A =\<^sub>\<preceq> A"
by (simp add: seteq_qle_def)

lemma seteq_qle_trans: "A =\<^sub>\<preceq> B \<Longrightarrow> B =\<^sub>\<preceq> C \<Longrightarrow> A =\<^sub>\<preceq> C"
by (simp add: seteq_qle_def) (metis subseteq_qle_trans)

end

end
