section\<open>Boolean functions\<close>
theory Bool_Func
imports Main
begin
text\<open>
  The end result of our implementation is verified against these functions:
\<close>
type_synonym 'a boolfunc = "('a \<Rightarrow> bool) \<Rightarrow> bool"

text\<open>if-then-else on boolean functions.\<close>
definition "bf_ite i t e \<equiv> (\<lambda>l. if i l then t l else e l)"
text\<open>if-then-else is interesting because we can, together with constant true and false, represent all binary boolean functions using maximally two applications of it.\<close>
abbreviation "bf_True \<equiv> (\<lambda>l. True)"
abbreviation "bf_False \<equiv> (\<lambda>l. False)"
text\<open>A quick demonstration:\<close>
definition "bf_and a b \<equiv> bf_ite a b bf_False"
lemma "(bf_and a b) as \<longleftrightarrow> a as \<and> b as" unfolding bf_and_def  bf_ite_def  by meson 
definition "bf_not b \<equiv> bf_ite b bf_False bf_True"
lemma bf_not_alt: "bf_not a as \<longleftrightarrow> \<not>a as" unfolding bf_not_def bf_ite_def by meson
text\<open>For convenience, we want a few functions more:\<close>
definition "bf_or a b \<equiv> bf_ite a bf_True b"
definition "bf_lit v \<equiv> (\<lambda>l. l v)"
definition "bf_if v t e \<equiv> bf_ite (bf_lit v) t e"
lemma bf_if_alt: "bf_if v t e = (\<lambda>l. if l v then t l else e l)" unfolding bf_if_def bf_ite_def bf_lit_def ..
definition "bf_nand a b = bf_not (bf_and a b)"
definition "bf_nor a b = bf_not (bf_or a b)"
definition "bf_biimp a b = (bf_ite a b (bf_not b))"
lemma bf_biimp_alt: "bf_biimp a b = (\<lambda>l. a l \<longleftrightarrow> b l)" unfolding bf_biimp_def bf_not_def bf_ite_def by(simp add: fun_eq_iff)
definition "bf_xor a b = bf_not (bf_biimp a b)"
lemma bf_xor_alt: "bf_xor a b = (bf_ite a (bf_not b) b)" (* two application version *) 
  unfolding bf_xor_def bf_biimp_def bf_not_def
  unfolding bf_ite_def
  by simp
text\<open>All of these are implemented and had their implementation verified.\<close>

definition "bf_imp a b = bf_ite a b bf_True"
lemma bf_imp_alt: "bf_imp a b = bf_or (bf_not a) b" unfolding bf_or_def bf_not_def bf_imp_def unfolding bf_ite_def unfolding fun_eq_iff by simp

lemma [dest!,elim!]: "bf_False = bf_True \<Longrightarrow> False" "bf_True = bf_False \<Longrightarrow> False" unfolding fun_eq_iff by simp_all (* Occurs here and there as goal for sep_auto *)

lemmas [simp] = bf_and_def bf_or_def bf_nand_def bf_biimp_def bf_xor_alt bf_nor_def bf_not_def 

subsection\<open>Shannon decomposition\<close>
text\<open>
  A restriction of a boolean function on a variable is creating the boolean function that evaluates as if that variable was set to a fixed value:
\<close>
definition "bf_restrict (i::'a) (val::bool) (f::'a boolfunc) \<equiv> (\<lambda>v. f (v(i:=val)))"

text \<open>
  Restrictions are useful, because they remove variables from the set of significant variables:
\<close>
definition "bf_vars bf = {v. \<exists>as. bf_restrict v True bf as \<noteq> bf_restrict v False bf as}"
lemma "var \<notin> bf_vars (bf_restrict var val ex)"
unfolding bf_vars_def bf_restrict_def by(simp)

text\<open>
  We can decompose calculating if-then-else into computing if-then-else of two triples of functions with one variable restricted to true / false.
  Given that the functions have finite arity, we can use this to construct a recursive definition.
\<close>
lemma brace90shannon: "bf_ite F G H ass =
  bf_ite (\<lambda>l. l i) 
         (bf_ite (bf_restrict i True F) (bf_restrict i True G) (bf_restrict i True H))
         (bf_ite (bf_restrict i False F) (bf_restrict i False G) (bf_restrict i False H)) ass"
unfolding bf_ite_def bf_restrict_def by (auto simp add: fun_upd_idem)


end
