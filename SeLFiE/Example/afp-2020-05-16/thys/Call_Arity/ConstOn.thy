theory ConstOn
imports Main
begin

definition const_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
  where "const_on f S x = (\<forall> y \<in> S . f y = x)"

lemma const_onI[intro]: "(\<And>y. y \<in> S \<Longrightarrow> f y = x) \<Longrightarrow> const_on f S x"
  by (simp add: const_on_def)

lemma const_onD[dest]: "const_on f S x \<Longrightarrow> y \<in> S \<Longrightarrow> f y = x"
  by (simp add: const_on_def)

(*
lemma const_onE[elim]: "const_on f S r ==> x : S ==> r = r' ==> f x = r'" 
*)

lemma const_on_insert[simp]: "const_on f (insert x S) y \<longleftrightarrow> const_on f S y \<and> f x = y"
   by auto

lemma const_on_union[simp]: "const_on f (S \<union> S') y \<longleftrightarrow> const_on f S y \<and> const_on f S' y"
  by auto

lemma const_on_subset[elim]: "const_on f S y \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> const_on f S' y"
  by auto


end
