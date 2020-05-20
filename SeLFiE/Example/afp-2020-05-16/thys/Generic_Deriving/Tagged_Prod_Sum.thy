chapter \<open>Tagged Sum-of-Products Representation\<close>
text \<open>
This theory sets up a version of the sum-of-products representation that includes constructor and 
selector names. For an example of a type class that uses this representation see Derive\_Show.
\<close>

theory Tagged_Prod_Sum
imports Main
begin

context begin

qualified datatype ('a, 'b) prod = Prod "string option" "string option" 'a 'b
qualified datatype ('a, 'b) sum = Inl "string option" 'a | Inr "string option" 'b

qualified definition fst where "fst p = (case p of (Prod _ _ a _) \<Rightarrow> a)"
qualified definition snd where "snd p = (case p of (Prod _ _ _ b) \<Rightarrow> b)"
qualified definition sel_name_fst where "sel_name_fst p = (case p of (Prod s _ _ _) \<Rightarrow> s)"
qualified definition sel_name_snd where "sel_name_snd p = (case p of (Prod _ s _ _) \<Rightarrow> s)"

qualified definition constr_name where "constr_name x = (case x of (Inl s _) \<Rightarrow> s | (Inr s _) \<Rightarrow> s)" 

end

lemma measure_tagged_fst[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda> p. f (Tagged_Prod_Sum.fst p))"
  by (rule is_measure_trivial)

lemma measure_tagged_snd[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda> p. f (Tagged_Prod_Sum.snd p))"
  by (rule is_measure_trivial)

lemma size_tagged_prod_simp: 
  "Tagged_Prod_Sum.prod.size_prod f g p = f (Tagged_Prod_Sum.fst p) + g (Tagged_Prod_Sum.snd p) + Suc 0"
  apply (induct p)
  by (simp add: Tagged_Prod_Sum.fst_def Tagged_Prod_Sum.snd_def) 

lemma size_tagged_sum_simp: 
  "Tagged_Prod_Sum.sum.size_sum f g x = (case x of Tagged_Prod_Sum.Inl _ a \<Rightarrow> f a + Suc 0 | Tagged_Prod_Sum.Inr _ b \<Rightarrow> g b + Suc 0)"
  apply (induct x)
  by auto

lemma size_tagged_prod_measure: 
  "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (Tagged_Prod_Sum.prod.size_prod f g)"
by (rule is_measure_trivial)

lemma size_tagged_sum_measure: 
  "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (Tagged_Prod_Sum.sum.size_sum f g)"
by (rule is_measure_trivial)

end