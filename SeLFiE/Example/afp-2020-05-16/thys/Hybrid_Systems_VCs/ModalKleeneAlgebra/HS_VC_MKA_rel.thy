(*  Title:       Verification components with relational MKA 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with relational MKA \<close>

text \<open> We show that relations form an antidomain Kleene algebra (hence a modal Kleene 
algebra). We use its forward box operator to derive rules in the algebra for weakest 
liberal preconditions (wlps) of hybrid programs. Finally, we derive our three methods 
for verifying correctness specifications for the continuous dynamics of HS in this setting. \<close>

theory HS_VC_MKA_rel
  imports "../HS_ODEs" "KAD.Modal_Kleene_Algebra"

begin


subsection \<open> Modal Kleene algebra preparation \<close> 

context dioid_one_zero (* by Victor Gomes, Georg Struth *)
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ n) \<cdot> z \<le> y"
  by(induct n, auto, metis mult.assoc mult_isol order_trans)

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {
    fix n
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using \<open>z + y \<cdot> x \<le> y\<close> by auto
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by auto
  }
  thus ?case
    by (metis Suc)
qed

end

context antidomain_kleene_algebra
begin

lemma fbox_frame: "d p \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d q \<le> |x] t \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d t)"    
  using dual.mult_isol_var fbox_add1 fbox_demodalisation3 fbox_simp by auto

lemma plus_inv: "i \<le> |x] i \<Longrightarrow> j \<le> |x] j \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  by (metis ads_d_def dka.dsr5 fbox_simp fbox_subdist join.sup_mono order_trans)

lemma mult_inv: "d i \<le> |x] d i \<Longrightarrow> d j \<le> |x] d j \<Longrightarrow> (d i \<cdot> d j) \<le> |x] (d i \<cdot> d j)"
  using fbox_demodalisation3 fbox_frame fbox_simp by auto

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure addual.ars_r_def fbox_def fbox_mult by auto

lemma fbox_stari: "d p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |x\<^sup>\<star>] q"
  by (meson dual_order.trans fbox_iso fbox_star_induct_var)

declare fbox_mult [simp]

definition cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) 
  where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

lemma fbox_cond_var [simp]: "|if p then x else y fi] q = (ad p + |x] q) \<cdot> (d p + |y] q)"  
  using cond_def a_closure' ads_d_def ans_d_def fbox_add2 fbox_export1 by auto

definition loopi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma fbox_loopi: "d p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |loop x inv i] q"
  unfolding loopi_def using fbox_stari by blast

end


subsection \<open> Relational model \<close> (* by Victor Gomes, Georg Struth *)

interpretation rel_dioid: dioid_one_zero "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)"
  by (unfold_locales, auto)

lemma power_is_relpow: "rel_dioid.power X n = X ^^ n"
proof (induct n)
  case 0 show ?case
    by (metis rel_dioid.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_dioid.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>n. rel_dioid.power X n)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>n. X O rel_dioid.power Y n)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>n. (rel_dioid.power X n) O Y)"
by (metis rel_star_def relcomp_UNION_distrib2)

interpretation rel_ka: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_dioid.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_dioid.power_inductr)
qed

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ad R = {(x,x) | x. \<not> (\<exists>y. (x,y) \<in> R)}"

interpretation rel_aka: antidomain_kleene_algebra rel_ad "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
  by  unfold_locales (auto simp: rel_ad_def)


subsection \<open> Store and weakest preconditions \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and antidomain_semiringl.ads_d ("d")

notation Id ("skip")
     and relcomp (infixl ";" 70)
     and zero_class.zero ("0")
     and rel_aka.fbox ("wp")

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("(1\<lceil>_\<rceil>)") where
  "\<lceil>P\<rceil> = {(s,s) |s. P s}"

lemma p2r_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> ; \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "rel_ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  "rel_aka.ads_d \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  unfolding p2r_def rel_ad_def rel_aka.ads_d_def by auto

lemma wp_rel: "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
  unfolding rel_aka.fbox_def p2r_def rel_ad_def by auto

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = {(s, vec_upd s x (e s))| s. True}" 

lemma wp_assign [simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)\<rceil>"
  unfolding wp_rel vec_upd_def assign_def by (auto simp: fun_upd_def)

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF P THEN X ELSE Y \<equiv> rel_aka.cond \<lceil>P\<rceil> X Y"

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP R INV I \<equiv> rel_aka.loopi R \<lceil>I\<rceil>"

lemma wp_loopI: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp R \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (LOOP R INV I) \<lceil>Q\<rceil>"
  using rel_aka.fbox_loopi[of "\<lceil>P\<rceil>"] by auto


subsection \<open> Verification of hybrid programs \<close>

text \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> 'b rel" ("EVOL")
  where "EVOL \<phi> G T = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G T}"

lemma wp_g_dyn[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "wp (EVOL \<phi> G T) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding wp_rel g_evol_def g_orbit_eq by auto

text \<open>Verification by providing solutions\<close>

definition g_ode :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

lemma wp_g_orbital: "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>X\<in>Sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq wp_rel ivp_sols_def g_ode_def by auto

context local_flow
begin

lemma wp_g_ode: "wp (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  unfolding wp_g_orbital 
  apply(clarsimp, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE)
  using in_ivp_sols 
     apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma fbox_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> wp (x\<acute>=f & G on {0..t} S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  unfolding wp_g_orbital 
  apply(clarsimp, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE, force)
  using in_ivp_sols_ivl 
    apply(force simp: closed_segment_eq_real_ivl)
  using in_ivp_sols_ivl 
   apply(force simp: ivp_sols_def)
  apply(subgoal_tac "\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. X \<tau> = \<phi> \<tau> s)", simp, clarsimp)
  apply(subst eq_solution_ivl, simp_all add: ivp_sols_def)
     apply(rule has_vderiv_on_subset, force, force simp: closed_segment_eq_real_ivl)
    apply(force simp: closed_segment_eq_real_ivl)
  using interval_time init_time 
   apply (meson is_interval_1 order_trans) 
  using init_time by force

lemma wp_orbit: "wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s))\<rceil>"
  unfolding orbit_def wp_g_ode g_ode_def[symmetric] by auto

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma wp_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>H\<rceil>"
  unfolding wp_g_orbital using assms by auto

lemma wp_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  apply(rule rel_aka.fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv[simp]: "(\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_orbital by(auto simp: p2r_def)

lemma diff_inv_guard_ignore:
  assumes "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. True) on T S @ t\<^sub>0) \<lceil>I\<rceil>"
  shows "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>"
  using assms unfolding wp_diff_inv diff_invariant_eq by auto

context local_flow
begin

lemma wp_diff_inv_eq: "diff_invariant I f T S 0 (\<lambda>s. True) = 
  (\<lceil>\<lambda>s. s \<in> S \<longrightarrow> I s\<rceil> = wp (x\<acute>= f & (\<lambda>s. True) on T S @ 0) \<lceil>\<lambda>s. s \<in> S \<longrightarrow> I s\<rceil>)"
  unfolding wp_diff_inv[symmetric] wp_g_orbital
  using init_time 
  apply(clarsimp simp: ivp_sols_def)
  apply(safe, force, force)
   apply(subst ivp(2)[symmetric], simp)
   apply(erule_tac x="\<lambda>t. \<phi> t s" in allE)
  using in_domain has_vderiv_on_domain ivp(2) init_time by auto

lemma diff_inv_eq_inv_set:
  "diff_invariant I f T S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by (auto simp: p2r_def)

end

lemma wp_g_odei: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def 
  apply(rule_tac b="wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" in order.trans)
   apply(rule_tac I="I" in wp_g_orbital_inv, simp_all)
  apply(subst wp_g_orbital_guard, simp)
  by (rule rel_aka.fbox_iso, simp)


subsection \<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. \<forall>t\<in>T. (\<P> (\<lambda>t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_ode[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_ode, auto)

lemma diff_weak_axiom: 
  "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_orbital image_def by force

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: g_orbital_eq g_ode_def)

lemma wp_g_evol_IdD:
  assumes "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
    and "\<forall>\<tau>\<in>(down T t). (s, x \<tau>) \<in> (x\<acute>= f & G on T S @ t\<^sub>0)"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> g_orbital f G T S t\<^sub>0 s" 
    using assms(2) unfolding g_ode_def by blast
  also have "\<forall>y. y \<in> (g_orbital f G T S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_rel g_ode_def by(auto simp: p2r_def)
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule subset_antisym)
  show "(x\<acute>=f & G on T S @ t\<^sub>0) \<subseteq> (x\<acute>=f & \<lambda>s. G s \<and> C s on T S @ t\<^sub>0)"
  proof(clarsimp simp: g_ode_def)
    fix s and s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"(\<P> X (down T \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using wp_g_evol_IdD[OF assms(3)] unfolding g_ode_def by blast
    thus "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> by fastforce
  qed
next show "(x\<acute>=f & \<lambda>s. G s \<and> C s on T S @ t\<^sub>0) \<subseteq> (x\<acute>=f & G on T S @ t\<^sub>0)"  
    by (auto simp: g_orbital_eq g_ode_def)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_rel, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_rel) (auto simp: g_ode_def)
qed

text \<open>The rules of dL\<close>

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = \<lceil>\<lambda>x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  by (subst diff_solve_axiom[of UNIV]) auto

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) by simp

lemma DW: "wp (x\<acute>= f & G) \<lceil>Q\<rceil> = wp (x\<acute>= f & G) \<lceil>\<lambda>s. G s \<longrightarrow> Q s\<rceil>"
  by (rule diff_weak_axiom)
  
lemma dW: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  by (rule diff_weak_rule)

lemma DC:
  assumes "wp (x\<acute>= f & G) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>= f & G) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  apply (rule diff_cut_axiom) 
  using assms by auto

lemma dC:
  assumes "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>C\<rceil>"
    and "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f UNIV UNIV 0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule wp_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding wp_diff_inv using assms(2) .

end