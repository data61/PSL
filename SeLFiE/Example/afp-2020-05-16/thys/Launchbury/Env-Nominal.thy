theory "Env-Nominal"
  imports Env "Nominal-Utils" "Nominal-HOLCF"
begin

subsubsection \<open>Equivariance lemmas\<close>

lemma edom_perm:
  fixes f :: "'a::pt \<Rightarrow> 'b::{pcpo_pt}"
  shows "edom (\<pi> \<bullet> f) = \<pi> \<bullet> (edom f)"
  by (simp add: edom_def)

lemmas edom_perm_rev[simp,eqvt] = edom_perm[symmetric]

lemma mem_edom_perm[simp]:
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt}"
  shows "xa \<in> edom (p \<bullet> \<rho>) \<longleftrightarrow> - p \<bullet> xa \<in> edom \<rho>" 
  by (metis (mono_tags) edom_perm_rev mem_Collect_eq permute_set_eq)

lemma env_restr_eqvt[eqvt]:
  fixes m :: "'a::pt \<Rightarrow> 'b::{cont_pt,pcpo}"
  shows "\<pi> \<bullet> m f|` d = (\<pi> \<bullet> m) f|` (\<pi> \<bullet> d)"
  by (auto simp add: env_restr_def)

lemma env_delete_eqvt[eqvt]:
  fixes m :: "'a::pt \<Rightarrow> 'b::{cont_pt,pcpo}"
  shows "\<pi> \<bullet> env_delete x m = env_delete (\<pi> \<bullet> x) (\<pi> \<bullet> m)"
  by (auto simp add: env_delete_def)

lemma esing_eqvt[eqvt]: "\<pi> \<bullet> (esing x) = esing (\<pi> \<bullet> x)"
  unfolding esing_def
  apply perm_simp
  apply (simp add: Abs_cfun_eqvt)
  done

subsubsection \<open>Permutation and restriction\<close>

lemma env_restr_perm:
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "(p \<bullet> \<rho>) f|` S = \<rho> f|` S"
using assms
apply -
apply (rule ext)
apply (case_tac "x \<in> S")
apply (simp)
apply (subst permute_fun_def)
apply (simp add: permute_pure)
apply (subst perm_supp_eq)
apply (auto simp add:perm_supp_eq supp_minus_perm fresh_star_def fresh_def supp_set_elem_finite)
done

lemma env_restr_perm':
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "p \<bullet> (\<rho> f|` S) = \<rho> f|` S"
  by (simp add: perm_supp_eq[OF assms(1)]  env_restr_perm[OF assms])

lemma env_restr_flip:
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` S = \<rho> f|` S"
  using assms
  apply -
  apply rule
  apply (auto  simp add: permute_flip_at env_restr_def split:if_splits)
  by (metis eqvt_lambda flip_at_base_simps(3) minus_flip permute_pure unpermute_def)

lemma env_restr_flip':
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "(x' \<leftrightarrow> x) \<bullet> (\<rho> f|` S) = \<rho> f|` S"
  by (simp add: flip_set_both_not_in[OF assms]  env_restr_flip[OF assms])



subsubsection \<open>Pure codomains\<close>
(*
lemma edom_fv_pure:
  fixes f :: "('a::at_base \<Rightarrow> 'b::{pcpo,pure})"
  assumes "finite (edom f)"
  shows  "fv f = edom f"
using assms
proof (induction "edom f" arbitrary: f)
  case empty
  hence "f = \<bottom>" unfolding edom_def by auto
  thus ?case by (auto simp add: fv_def fresh_def supp_def)
next
  case (insert x S)
  have "f = (env_delete x f)(x := f x)" by auto

  from `insert x S = edom f`  and `x \<notin> S`
  have "S = edom (env_delete x f)" by auto
  hence "fv (env_delete x f) = edom (env_delete x f)" by (rule insert)
*)

lemma edom_fv_pure:
  fixes f :: "('a::at_base \<Rightarrow> 'b::{pcpo,pure})"
  assumes "finite (edom f)"
  shows  "fv f \<subseteq> edom f"
using assms
proof (induction "edom f" arbitrary: f)
  case empty
  hence "f = \<bottom>" unfolding edom_def by auto
  thus ?case by (auto simp add: fv_def fresh_def supp_def)
next
  case (insert x S)
  have "f = (env_delete x f)(x := f x)" by auto
  hence "fv f \<subseteq> fv (env_delete x f) \<union> fv x \<union> fv (f x)"
    using eqvt_fresh_cong3[where f = fun_upd and x = "env_delete x f" and y = x and z = "f x", OF fun_upd_eqvt]
    apply (auto simp add: fv_def fresh_def)
    by (metis fresh_def pure_fresh)
  also

  from \<open>insert x S = edom f\<close>  and \<open>x \<notin> S\<close>
  have "S = edom (env_delete x f)" by auto
  hence "fv (env_delete x f) \<subseteq> edom (env_delete x f)" by (rule insert)
  also
  have "fv (f x) = {}" by (rule fv_pure)
  also
  from \<open>insert x S = edom f\<close> have "x \<in> edom f" by auto
  hence "edom (env_delete x f) \<union> fv x \<union> {} \<subseteq> edom f" by auto
  finally
  show ?case by this (intro Un_mono subset_refl)
qed

(*
lemma domA_fresh_pure:
  fixes \<Gamma> :: "('a::at_base \<times> 'b::pure) list"
  shows  "x \<in> domA \<Gamma> \<longleftrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  unfolding domA_fv_pure[symmetric]
  by (auto simp add: fv_def fresh_def)
*)

end
