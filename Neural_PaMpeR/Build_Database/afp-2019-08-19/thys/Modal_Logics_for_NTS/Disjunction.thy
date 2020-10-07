theory Disjunction
imports
  Formula
  Validity
begin

section \<open>Disjunction\<close>

definition Disj :: "('idx,'pred::fs,'act::bn) formula set['idx] \<Rightarrow> ('idx,'pred,'act) formula" where
  "Disj xset = Not (Conj (map_bset Not xset))"

lemma finite_supp_map_bset_Not [simp]:
  assumes "finite (supp xset)"
  shows "finite (supp (map_bset Not xset))"
proof -
  have "eqvt map_bset" and "eqvt Not"
    by (simp add: eqvtI)+
  then have "supp (map_bset Not) = {}"
    using supp_fun_eqvt supp_fun_app_eqvt by blast
  then have "supp (map_bset Not xset) \<subseteq> supp xset"
    using supp_fun_app by blast
  with assms show "finite (supp (map_bset Not xset))"
    by (metis finite_subset)
qed

lemma Disj_eqvt [simp]:
  assumes "finite (supp xset)"
  shows "p \<bullet> Disj xset = Disj (p \<bullet> xset)"
using assms unfolding Disj_def by simp

lemma Disj_eq_iff [simp]:
  assumes "finite (supp xset1)" and "finite (supp xset2)"
  shows "Disj xset1 = Disj xset2 \<longleftrightarrow> xset1 = xset2"
using assms unfolding Disj_def by (metis Conj_eq_iff Not_eq_iff bset.inj_map_strong finite_supp_map_bset_Not)

context nominal_ts
begin

  lemma valid_Disj [simp]:
    assumes "finite (supp xset)"
    shows "P \<Turnstile> Disj xset \<longleftrightarrow> (\<exists>x\<in>set_bset xset. P \<Turnstile> x)"
  using assms by (simp add: Disj_def map_bset.rep_eq)

end

end
