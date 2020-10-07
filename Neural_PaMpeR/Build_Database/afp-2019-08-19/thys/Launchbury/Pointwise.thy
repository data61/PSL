theory Pointwise imports Main begin

text \<open>
Lifting a relation to a function.
\<close>

definition pointwise where "pointwise P m m' = (\<forall> x. P (m x) (m' x))"

lemma pointwiseI[intro]: "(\<And> x. P (m x) (m' x)) \<Longrightarrow> pointwise P m m'" unfolding pointwise_def by blast

end
