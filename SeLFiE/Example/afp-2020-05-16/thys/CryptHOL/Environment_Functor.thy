theory Environment_Functor imports
  Applicative_Lifting.Applicative_Environment
begin

subsection \<open>The environment functor\<close>

type_synonym ('i, 'a) envir = "'i \<Rightarrow> 'a"

lemma const_apply [simp]: "const x i = x"
by(simp add: const_def)

context includes applicative_syntax begin

lemma ap_envir_apply [simp]: "(f \<diamondop> x) i = f i (x i)"
by(simp add: apf_def)

definition all_envir :: "('i, bool) envir \<Rightarrow> bool"
where "all_envir p \<longleftrightarrow> (\<forall>x. p x)"

lemma all_envirI [Pure.intro!, intro!]: "(\<And>x. p x) \<Longrightarrow> all_envir p"
by(simp add: all_envir_def)

lemma all_envirE [Pure.elim 2, elim]: "all_envir p \<Longrightarrow> (p x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
by(simp add: all_envir_def)

lemma all_envirD: "all_envir p \<Longrightarrow> p x"
by(simp add: all_envir_def)


definition pred_envir :: "('a \<Rightarrow> bool) \<Rightarrow> ('i, 'a) envir \<Rightarrow> bool"
where "pred_envir p f = all_envir (const p \<diamondop> f)"

lemma pred_envir_conv: "pred_envir p f \<longleftrightarrow> (\<forall>x. p (f x))"
by(auto simp add: pred_envir_def)

lemma pred_envirI [Pure.intro!, intro!]: "(\<And>x. p (f x)) \<Longrightarrow> pred_envir p f"
by(auto simp add: pred_envir_def)

lemma pred_envirD: "pred_envir p f \<Longrightarrow> p (f x)"
by(auto simp add: pred_envir_def)

lemma pred_envirE [Pure.elim 2, elim]: "pred_envir p f \<Longrightarrow> (p (f x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
by(simp add: pred_envir_conv)

lemma pred_envir_mono: "\<lbrakk> pred_envir p f; \<And>x. p (f x) \<Longrightarrow> q (g x) \<rbrakk> \<Longrightarrow> pred_envir q g"
by blast

definition rel_envir :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('i, 'a) envir \<Rightarrow> ('i, 'b) envir \<Rightarrow> bool"
where "rel_envir p f g \<longleftrightarrow> all_envir (const p \<diamondop> f \<diamondop> g)"

lemma rel_envir_conv: "rel_envir p f g \<longleftrightarrow> (\<forall>x. p (f x) (g x))"
by(auto simp add: rel_envir_def)

lemma rel_envir_conv_rel_fun: "rel_envir = rel_fun (=)"
by(simp add: rel_envir_conv rel_fun_def fun_eq_iff)

lemma rel_envirI [Pure.intro!, intro!]: "(\<And>x. p (f x) (g x)) \<Longrightarrow> rel_envir p f g"
by(auto simp add: rel_envir_def)

lemma rel_envirD: "rel_envir p f g \<Longrightarrow> p (f x) (g x)"
by(auto simp add: rel_envir_def)

lemma rel_envirE [Pure.elim 2, elim]: "rel_envir p f g \<Longrightarrow> (p (f x) (g x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
by(simp add: rel_envir_conv)

lemma rel_envir_mono: "\<lbrakk> rel_envir p f g; \<And>x. p (f x) (g x) \<Longrightarrow> q (f' x) (g' x) \<rbrakk> \<Longrightarrow> rel_envir q f' g'"
by blast

lemma rel_envir_mono1: "\<lbrakk> pred_envir p f; \<And>x. p (f x) \<Longrightarrow> q (f' x) (g' x) \<rbrakk> \<Longrightarrow> rel_envir q f' g'"
by blast

lemma pred_envir_mono2: "\<lbrakk> rel_envir p f g; \<And>x. p (f x) (g x) \<Longrightarrow> q (f' x) \<rbrakk> \<Longrightarrow> pred_envir q f'"
by blast

end

end
