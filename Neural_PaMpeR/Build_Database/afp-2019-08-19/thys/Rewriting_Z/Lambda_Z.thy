(*
 * Title:      Z  
 * Author:     Bertram Felgenhauer (2016)
 * Author:     Julian Nagele (2016)
 * Author:     Vincent van Oostrom (2016)
 * Author:     Christian Sternagel (2016)
 * Maintainer: Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>
 * Maintainer: Juilan Nagele <julian.nagele@uibk.ac.at>
 * Maintainer: Christian Sternagel <c.sternagel@gmail.com>
 * License:    BSD
 *)

section \<open>Lambda Calculus has the Church-Rosser property\<close>

theory Lambda_Z
imports
  Nominal2.Nominal2
  "HOL-Eisbach.Eisbach"
  Z
begin

atom_decl name

nominal_datatype "term" =
  Var name
| App "term" "term"
| Abs x::name t::"term" binds x in t

subsection \<open>Ad-hoc methods for nominal-functions over lambda terms\<close>

ML \<open>
fun graph_aux_tac ctxt =
  SUBGOAL (fn (subgoal, i) =>
    (case subgoal of
      Const (@{const_name Trueprop}, _) $ (Const (@{const_name eqvt}, _) $ Free (f, _)) =>
        full_simp_tac (
          ctxt addsimps [@{thm eqvt_def}, Proof_Context.get_thm ctxt (f ^ "_def")]) i
    | _ => no_tac))
\<close>

method_setup eqvt_graph_aux =
  \<open>Scan.succeed (fn ctxt : Proof.context => SIMPLE_METHOD' (graph_aux_tac ctxt))\<close>
  "show equivariance of auxilliary graph construction for nominal functions"

method without_alpha_lst methods m =
  (match termI in H [simproc del: alpha_lst]: _ \<Rightarrow> \<open>m\<close>)

method Abs_lst =
  (match premises in
    "atom ?x \<sharp> c" and P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" for c :: "'a::fs" \<Rightarrow>
      \<open>rule Abs_lst1_fcb2' [where c = c, OF P]\<close>
  \<bar> P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" \<Rightarrow> \<open>rule Abs_lst1_fcb2' [where c = "()", OF P]\<close>)

method pat_comp_aux =
  (match premises in
    "x = (_ :: term) \<Longrightarrow> _" for x \<Rightarrow> \<open>rule term.strong_exhaust [where y = x and c = x]\<close>
  \<bar> "x = (Var _, _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "fst x" and c = x]\<close>
  \<bar> "x = (_, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd x" and c = x]\<close>
  \<bar> "x = (_, _, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd (snd x)" and c = x]\<close>)

method pat_comp = (pat_comp_aux; force simp: fresh_star_def fresh_Pair_elim)

method freshness uses fresh =
  (match conclusion in
    "_ \<sharp> _" \<Rightarrow> \<open>simp add: fresh_Unit fresh_Pair fresh\<close>
  \<bar> "_ \<sharp>* _" \<Rightarrow> \<open>simp add: fresh_star_def fresh_Unit fresh_Pair fresh\<close>)

method solve_eqvt_at =
  (simp add: eqvt_at_def; simp add: perm_supp_eq fresh_star_Pair)+

method nf uses fresh = without_alpha_lst \<open>
  eqvt_graph_aux, rule TrueI, pat_comp, auto, Abs_lst,
  auto simp: Abs_fresh_iff pure_fresh perm_supp_eq,
  (freshness fresh: fresh)+,
  solve_eqvt_at?\<close>


subsection \<open>Substitutions\<close>

nominal_function subst
where
  "subst x s (Var y) = (if x = y then s else Var y)"
| "subst x s (App t u) = App (subst x s t) (subst x s u)"
| "atom y \<sharp> (x, s) \<Longrightarrow> subst x s (Abs y t) = Abs y (subst x s t)"
by nf
nominal_termination (eqvt) by lexicographic_order

lemma fresh_subst:
  "atom z \<sharp> s \<Longrightarrow> z = y \<or> atom z \<sharp> t \<Longrightarrow> atom z \<sharp> subst y s t"
by (nominal_induct t avoiding: z y s rule: term.strong_induct) auto

lemma fresh_subst_id [simp]:
  "atom x \<sharp> t \<Longrightarrow> subst x s t = t"
by (nominal_induct t avoiding: x s rule: term.strong_induct) (auto simp: fresh_at_base)

text \<open>The substitution lemma.\<close>
lemma subst_subst:
  assumes "x \<noteq> y" and "atom x \<sharp> u"
  shows "subst y u (subst x s t) = subst x (subst y u s) (subst y u t)"
using assms by (nominal_induct t avoiding: x y u s rule: term.strong_induct) (auto simp: fresh_subst)

inductive_set Beta ("{\<rightarrow>\<^sub>\<beta>}")
where
  root: "atom x \<sharp> t \<Longrightarrow> (App (Abs x s) t, subst x t s) \<in> {\<rightarrow>\<^sub>\<beta>}"
| Appl: "(s, t) \<in> {\<rightarrow>\<^sub>\<beta>} \<Longrightarrow> (App s u, App t u) \<in> {\<rightarrow>\<^sub>\<beta>}"
| Appr: "(s, t) \<in> {\<rightarrow>\<^sub>\<beta>} \<Longrightarrow> (App u s, App u t) \<in> {\<rightarrow>\<^sub>\<beta>}"
| Abs: "(s, t) \<in> {\<rightarrow>\<^sub>\<beta>} \<Longrightarrow> (Abs x s, Abs x t) \<in> {\<rightarrow>\<^sub>\<beta>}"

abbreviation beta ("(_/ \<rightarrow>\<^sub>\<beta> _)" [56, 56] 55)
where
  "s \<rightarrow>\<^sub>\<beta> t \<equiv> (s, t) \<in> {\<rightarrow>\<^sub>\<beta>}"

equivariance Betap
lemmas Beta_eqvt = Betap.eqvt [to_set]

nominal_inductive Betap
  avoids Abs: x
       | root: x
by (simp_all add: fresh_star_def fresh_subst)

lemmas Beta_strong_induct = Betap.strong_induct [to_set]

abbreviation betas (infix "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)
where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<equiv> (s, t) \<in> {\<rightarrow>\<^sub>\<beta>}\<^sup>*"

nominal_function app_beta :: "term \<Rightarrow> term \<Rightarrow> term"
where
  "atom x \<sharp> u \<Longrightarrow> app_beta (Abs x s') u = subst x u s'"
| "app_beta (Var x) u = App (Var x) u"
| "app_beta (App s t) u = App (App s t) u"
by (nf fresh: fresh_subst)
nominal_termination (eqvt) by lexicographic_order

nominal_function bullet :: "term \<Rightarrow> term" ("_\<^sup>\<bullet>" [1000] 1000)
where
  "(Var x)\<^sup>\<bullet> = Var x"
| "(Abs x t)\<^sup>\<bullet> = Abs x t\<^sup>\<bullet>"
| "(App s t)\<^sup>\<bullet> = app_beta s\<^sup>\<bullet> t\<^sup>\<bullet>"
by nf
nominal_termination (eqvt) by lexicographic_order

lemma app_beta_exhaust [case_names Redex no_Redex]:
  fixes c :: "'a :: fs"
  assumes "\<And>x s'. atom x \<sharp> c \<Longrightarrow> s = Abs x s' \<Longrightarrow> thesis"
    and "(\<And>t. app_beta s t = App s t) \<Longrightarrow> thesis"
  shows "thesis"
by (cases s rule: term.strong_exhaust [of _ _ c]) (auto simp: fresh_star_def fresh_Pair intro: assms)

lemma App_Betas:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* t" and "u \<rightarrow>\<^sub>\<beta>\<^sup>* v"
  shows "App s u \<rightarrow>\<^sub>\<beta>\<^sup>* App t v"
using assms(1)
proof (induct)
  case base
  show ?case using assms(2) by (induct) (auto intro: Beta.intros rtrancl_into_rtrancl)
qed (auto intro: Beta.intros rtrancl_into_rtrancl)

lemma Abs_Betas:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* t"
  shows "Abs x s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs x t"
using assms by (induct) (auto intro: Beta.intros rtrancl_into_rtrancl)

lemma self:
  "t \<rightarrow>\<^sub>\<beta>\<^sup>* t\<^sup>\<bullet>"
proof (nominal_induct t rule: term.strong_induct)
  case (App t u)
  then show ?case
    by (cases "t\<^sup>\<bullet>" rule: app_beta_exhaust[of "u\<^sup>\<bullet>"])
       (auto intro: App_Betas Beta.intros rtrancl_into_rtrancl)
qed (auto intro: Abs_Betas)

lemma fresh_atom_bullet:
  "atom (x::name) \<sharp> t \<Longrightarrow> atom x \<sharp> t\<^sup>\<bullet>"
proof (nominal_induct t avoiding: x rule: term.strong_induct)
  case (App t u)
  then show ?case by (cases "t\<^sup>\<bullet>" rule: app_beta_exhaust[of "u\<^sup>\<bullet>"]) (auto intro: fresh_subst)
qed auto

lemma subst_Beta:
  assumes "t \<rightarrow>\<^sub>\<beta> t'"
  shows "subst x s t \<rightarrow>\<^sub>\<beta> subst x s t'"
using assms
proof (nominal_induct avoiding: x s rule: Beta_strong_induct)
  case (root y t u)
  then show ?case by (auto simp: subst_subst fresh_subst intro: Beta.root)
qed (auto intro: Beta.intros)

lemma Beta_in_subst:
  assumes "s \<rightarrow>\<^sub>\<beta> s'"
  shows "subst x s t \<rightarrow>\<^sub>\<beta>\<^sup>* subst x s' t"
using assms
by (nominal_induct t avoiding: x s s' rule: term.strong_induct)
   (auto intro: App_Betas Abs_Betas)

lemma subst_Betas:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* s'" and "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  shows "subst x s t \<rightarrow>\<^sub>\<beta>\<^sup>* subst x s' t'"
using assms(1)
proof (induct)
  case base
  from assms(2) show ?case by (induct) (auto simp: subst_Beta intro: rtrancl_into_rtrancl)
next
  case (step u v)
  from Beta_in_subst [OF this(2), of x t'] and this(3) show ?case by auto
qed

lemma Beta_fresh:
  fixes x :: name
  assumes "s \<rightarrow>\<^sub>\<beta> t" and "atom x \<sharp> s"
  shows "atom x \<sharp> t"
using assms by (nominal_induct rule: Beta_strong_induct) (auto simp: fresh_subst)

lemma Abs_BetaD:
  assumes "Abs x s \<rightarrow>\<^sub>\<beta> t"
  shows "\<exists>u. t = Abs x u \<and> s \<rightarrow>\<^sub>\<beta> u"
using assms
proof (nominal_induct "Abs x s" t avoiding: s rule: Beta_strong_induct)
  case (Abs u v y)
  then show ?case
    by (auto simp: Abs1_eq_iff Beta_fresh fresh_permute_left intro!: exI [of _ "(y \<leftrightarrow> x) \<bullet> v"])
       (metis Abs1_eq_iff(3) Beta_eqvt flip_commute)
qed

lemma Abs_BetaE:
  assumes "Abs x s \<rightarrow>\<^sub>\<beta> t"
  obtains u where "t = Abs x u" and "s \<rightarrow>\<^sub>\<beta> u"
using assms by (blast dest: Abs_BetaD)

lemma Abs_BetasE:
  assumes "Abs x s \<rightarrow>\<^sub>\<beta>\<^sup>* t"
  obtains u where "t = Abs x u" and "s \<rightarrow>\<^sub>\<beta>\<^sup>* u"
using assms by (induct "Abs x s" t) (auto elim: Abs_BetaE intro: rtrancl_into_rtrancl)

lemma bullet_App:
  "(App s\<^sup>\<bullet> t\<^sup>\<bullet>, (App s t)\<^sup>\<bullet>) \<in> {\<rightarrow>\<^sub>\<beta>}\<^sup>="
by (cases "s\<^sup>\<bullet>" rule: term.strong_exhaust[of _ _ "t\<^sup>\<bullet>"])
   (auto simp: fresh_star_def intro: Beta.root)

lemma rhs:
  "subst x s\<^sup>\<bullet> t\<^sup>\<bullet> \<rightarrow>\<^sub>\<beta>\<^sup>* (subst x s t)\<^sup>\<bullet>"
proof (nominal_induct t avoiding: x s rule: term.strong_induct)
  case (App t\<^sub>1 t\<^sub>2)
  show ?case
  proof (cases "t\<^sub>1\<^sup>\<bullet>" rule: app_beta_exhaust[of "(x, t\<^sub>2, s)"])
    case (Redex y u)
    then have "Abs y (subst x s\<^sup>\<bullet> u) \<rightarrow>\<^sub>\<beta>\<^sup>* (subst x s t\<^sub>1)\<^sup>\<bullet>"
      using App(1) [of x s] by (simp add: fresh_star_def fresh_atom_bullet)
    with Abs_BetasE obtain v where "(subst x s t\<^sub>1)\<^sup>\<bullet> = Abs y v" and " subst x s\<^sup>\<bullet> u \<rightarrow>\<^sub>\<beta>\<^sup>* v" by blast
    then show ?thesis using subst_subst and subst_Betas and App(2) and Redex
      by (simp add: fresh_atom_bullet fresh_subst)
  next
    case (no_Redex)
    then have "subst x s\<^sup>\<bullet> ((App t\<^sub>1 t\<^sub>2)\<^sup>\<bullet>) \<rightarrow>\<^sub>\<beta>\<^sup>* App ((subst x s t\<^sub>1)\<^sup>\<bullet>) ((subst x s t\<^sub>2)\<^sup>\<bullet>)"
      using App by (auto intro: App_Betas)
    then show ?thesis using bullet_App by (force intro: rtrancl_into_rtrancl)
  qed
qed (force dest: fresh_atom_bullet intro: Abs_Betas)+

lemma Betas_fresh:
  fixes x :: name
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* t" and "atom x \<sharp> s"
  shows "atom x \<sharp> t"
using assms by (induct) (auto dest: Beta_fresh)

lemma Var_BetaD:
  assumes "Var x \<rightarrow>\<^sub>\<beta> t"
  shows False
using assms by (induct "Var x" t)

lemma Var_BetasD:
  assumes "Var x \<rightarrow>\<^sub>\<beta>\<^sup>* t"
  shows "t = Var x"
using assms by (induct) (auto dest: Var_BetaD)

lemma app_beta_Betas:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* s'" and "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  shows "app_beta s t \<rightarrow>\<^sub>\<beta>\<^sup>* app_beta s' t'"
using assms
proof (cases s rule: term.strong_exhaust [of _ _ t])
  case (App s\<^sub>1 s\<^sub>2)
  with assms show ?thesis
    by (cases s' rule: app_beta_exhaust [of t']) (auto intro: root rtrancl_into_rtrancl App_Betas)
qed (auto simp: fresh_star_def Betas_fresh subst_Betas elim: Abs_BetasE intro: App_Betas dest!: Var_BetasD)

lemma lambda_Z:
  assumes "s \<rightarrow>\<^sub>\<beta> t"
  shows "t \<rightarrow>\<^sub>\<beta>\<^sup>* s\<^sup>\<bullet> \<and> s\<^sup>\<bullet> \<rightarrow>\<^sub>\<beta>\<^sup>* t\<^sup>\<bullet>"
using assms
proof (nominal_induct rule: Beta_strong_induct)
  case (Appl s t u)
  then have "App t u \<rightarrow>\<^sub>\<beta>\<^sup>* App s\<^sup>\<bullet> u\<^sup>\<bullet>" using self by (auto intro: App_Betas)
  also have "App s\<^sup>\<bullet> u\<^sup>\<bullet> \<rightarrow>\<^sub>\<beta>\<^sup>* (App s u)\<^sup>\<bullet>" using bullet_App by force
  finally show ?case using Appl by (auto intro: App_Betas app_beta_Betas)
next
  case (Appr s t u)
  then have "App u t \<rightarrow>\<^sub>\<beta>\<^sup>* App u\<^sup>\<bullet> s\<^sup>\<bullet>" using self by (auto intro: App_Betas)
  also have "App u\<^sup>\<bullet> s\<^sup>\<bullet> \<rightarrow>\<^sub>\<beta>\<^sup>* (App u s)\<^sup>\<bullet>" using bullet_App by force
  finally show ?case using Appr by (auto intro: App_Betas app_beta_Betas)
qed (auto intro: Abs_Betas subst_Betas rhs simp: self fresh_atom_bullet)

interpretation lambda_z: z_property bullet Beta
by (standard) (fact lambda_Z)

end
