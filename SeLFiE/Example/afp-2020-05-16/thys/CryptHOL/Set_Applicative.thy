theory Set_Applicative imports
  Applicative_Lifting.Applicative_Set
begin

subsection \<open>Applicative instance for @{typ "'a set"}\<close>

lemma ap_set_conv_bind: "ap_set f x = Set.bind f (\<lambda>f. Set.bind x (\<lambda>x. {f x}))"
by(auto simp add: ap_set_def bind_UNION)

context includes applicative_syntax begin

lemma in_ap_setI: "\<lbrakk> f' \<in> f; x' \<in> x \<rbrakk> \<Longrightarrow> f' x' \<in> f \<diamondop> x"
by(auto simp add: ap_set_def)

lemma in_ap_setE [elim!]:
  "\<lbrakk> x \<in> f \<diamondop> y; \<And>f' y'. \<lbrakk> x = f' y'; f' \<in> f; y' \<in> y \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: ap_set_def)

lemma in_ap_pure_set [iff]: "x \<in> {f} \<diamondop> y \<longleftrightarrow> (\<exists>y'\<in>y. x = f y')"
unfolding ap_set_def by auto

end

end
