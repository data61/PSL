(*  Title:      Containers/Closure_set.thy
    Author:     Andreas Lochbihler, KIT *)

theory Closure_Set imports Equal begin

section \<open>Sets implemented as Closures\<close>

context equal_base begin

definition fun_upd :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
where fun_upd_apply: "fun_upd f a b a' = (if equal a a' then b else f a')"

end

lemmas [code] = equal_base.fun_upd_apply
lemmas [simp] = equal_base.fun_upd_apply

lemma fun_upd_conv_fun_upd: "equal_base.fun_upd (=) = fun_upd"
by(simp add: fun_eq_iff)

end
