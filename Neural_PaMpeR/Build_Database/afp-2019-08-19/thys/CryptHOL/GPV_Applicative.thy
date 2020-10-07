theory GPV_Applicative imports
  Generative_Probabilistic_Value
  SPMF_Applicative
begin

subsection \<open>Applicative instance for @{typ "(_, 'out, 'in) gpv"}\<close>

definition ap_gpv :: "('a \<Rightarrow> 'b, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> ('b, 'out, 'in) gpv"
where "ap_gpv f x = bind_gpv f (\<lambda>f'. bind_gpv x (\<lambda>x'. Done (f' x')))"

adhoc_overloading Applicative.ap ap_gpv

abbreviation (input) pure_gpv :: "'a \<Rightarrow> ('a, 'out, 'in) gpv"
where "pure_gpv \<equiv> Done"

context includes applicative_syntax begin

lemma ap_gpv_id: "pure_gpv (\<lambda>x. x) \<diamondop> x = x"
by(simp add: ap_gpv_def)

lemma ap_gpv_comp: "pure_gpv (\<circ>) \<diamondop> u \<diamondop> v \<diamondop> w = u \<diamondop> (v \<diamondop> w)"
by(simp add: ap_gpv_def bind_gpv_assoc)

lemma ap_gpv_homo: "pure_gpv f \<diamondop> pure_gpv x = pure_gpv (f x)"
by(simp add: ap_gpv_def)

lemma ap_gpv_interchange: "u \<diamondop> pure_gpv x = pure_gpv (\<lambda>f. f x) \<diamondop> u"
by(simp add: ap_gpv_def)

applicative gpv
for
  pure: pure_gpv
  ap: ap_gpv
by(rule ap_gpv_id ap_gpv_comp[unfolded o_def[abs_def]] ap_gpv_homo ap_gpv_interchange)+

lemma map_conv_ap_gpv: "map_gpv f (\<lambda>x. x) gpv = pure_gpv f \<diamondop> gpv"
by(simp add: ap_gpv_def map_gpv_conv_bind)

lemma exec_gpv_ap:
  "exec_gpv callee (f \<diamondop> x) \<sigma> = 
   exec_gpv callee f \<sigma> \<bind> (\<lambda>(f', \<sigma>'). pure_spmf (\<lambda>(x', \<sigma>''). (f' x', \<sigma>'')) \<diamondop> exec_gpv callee x \<sigma>')"
by(simp add: ap_gpv_def exec_gpv_bind ap_spmf_conv_bind split_def)

lemma exec_gpv_ap_pure [simp]:
  "exec_gpv callee (pure_gpv f \<diamondop> x) \<sigma> = pure_spmf (apfst f) \<diamondop> exec_gpv callee x \<sigma>"
by(simp add: exec_gpv_ap apfst_def map_prod_def)

end

end
