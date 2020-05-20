(*  Title:       Verification components with MKA and non-deterministic functions
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with MKA and non-deterministic functions\<close>

text \<open> We show that non-deterministic endofunctions form an antidomain Kleene algebra 
(hence a modal Kleene algebra). We use MKA's forward box operator to derive rules for weakest 
liberal preconditions (wlps) of hybrid programs. Finally, we derive our three methods 
for verifying correctness specifications for the continuous dynamics of HS. \<close>

theory HS_VC_MKA_ndfun
  imports 
    "../HS_ODEs"
    "Transformer_Semantics.Kleisli_Quantale" 
    "KAD.Modal_Kleene_Algebra"

begin


subsection \<open> Modal Kleene algebra preparation \<close>

context antidomain_kleene_algebra
begin

lemma fbox_frame: "d p \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d q \<le> |x] t \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d t)"    
  using dual.mult_isol_var fbox_add1 fbox_demodalisation3 fbox_simp by auto

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure addual.ars_r_def fbox_def fbox_mult by auto

lemma plus_inv: "i \<le> |x] i \<Longrightarrow> j \<le> |x] j \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  by (metis ads_d_def dka.dsr5 fbox_simp fbox_subdist join.sup_mono order_trans)

lemma mult_inv: "d i \<le> |x] d i \<Longrightarrow> d j \<le> |x] d j \<Longrightarrow> (d i \<cdot> d j) \<le> |x] (d i \<cdot> d j)"
  using fbox_demodalisation3 fbox_frame fbox_simp by auto

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


subsection \<open> Non-deterministic functions \<close>

text\<open> Our semantics now corresponds to nondeterministic functions @{typ "'a nd_fun"}. Below we prove
some auxiliary lemmas for them and show that they form an antidomain kleene algebra. The proof just 
extends the results on the Transformer\_Semantics.Kleisli\_Quantale theory.\<close>


notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)
     and fbox ("wp")

declare Abs_nd_fun_inverse [simp]

lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject 
   apply blast
  by(rule ext, simp)

lemma nd_fun_eq_iff: "(f = g) = (\<forall>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x)"
  by (auto simp: nd_fun_ext)

instantiation nd_fun :: (type) antidomain_kleene_algebra
begin

definition "ad f = (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>"

definition "0 = \<zeta>\<^sup>\<bullet>"

definition "star_nd_fun f = qstar f" for f::"'a nd_fun"

definition "f + g = ((f\<^sub>\<bullet>) \<squnion> (g\<^sub>\<bullet>))\<^sup>\<bullet>"

named_theorems nd_fun_aka "antidomain kleene algebra properties for nondeterministic functions."

lemma nd_fun_plus_assoc[nd_fun_aka]: "x + y + z = x + (y + z)"
  and nd_fun_plus_comm[nd_fun_aka]: "x + y = y + x"
  and nd_fun_plus_idem[nd_fun_aka]: "x + x = x" for x::"'a nd_fun"
  unfolding plus_nd_fun_def by (simp add: ksup_assoc, simp_all add: ksup_comm)

lemma nd_fun_distr[nd_fun_aka]: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_aka]: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z" for x::"'a nd_fun"
  unfolding plus_nd_fun_def times_nd_fun_def by (simp_all add: kcomp_distr kcomp_distl)

lemma nd_fun_plus_zerol[nd_fun_aka]: "0 + x = x" 
  and nd_fun_mult_zerol[nd_fun_aka]: "0 \<cdot> x = 0"
  and nd_fun_mult_zeror[nd_fun_aka]: "x \<cdot> 0 = 0" for x::"'a nd_fun"
  unfolding plus_nd_fun_def zero_nd_fun_def times_nd_fun_def by auto

lemma nd_fun_leq[nd_fun_aka]: "(x \<le> y) = (x + y = y)"
  and nd_fun_less[nd_fun_aka]: "(x < y) = (x + y = y \<and> x \<noteq> y)"
  and nd_fun_leq_add[nd_fun_aka]: "z \<cdot> x \<le> z \<cdot> (x + y)" for x::"'a nd_fun"
  unfolding less_eq_nd_fun_def less_nd_fun_def plus_nd_fun_def times_nd_fun_def sup_fun_def
  by (unfold nd_fun_eq_iff le_fun_def, auto simp: kcomp_def)

lemma nd_fun_ad_zero[nd_fun_aka]: "ad x \<cdot> x = 0"
  and nd_fun_ad[nd_fun_aka]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and nd_fun_ad_one[nd_fun_aka]: "ad (ad x) + ad x = 1" for x::"'a nd_fun"
  unfolding antidomain_op_nd_fun_def times_nd_fun_def plus_nd_fun_def zero_nd_fun_def 
  by (auto simp: nd_fun_eq_iff kcomp_def one_nd_fun_def)

lemma nd_star_one[nd_fun_aka]: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_aka]: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_aka]: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y" for x::"'a nd_fun"
  unfolding plus_nd_fun_def star_nd_fun_def
    apply(simp_all add: fun_star_inductl sup_nd_fun.rep_eq fun_star_inductr)
  by (metis order_refl sup_nd_fun.rep_eq uwqlka.conway.dagger_unfoldl_eq)

instance
  apply intro_classes
  using nd_fun_aka by simp_all

end

subsection \<open> Store and weakest preconditions \<close>

text\<open> Now that we know that nondeterministic functions form an Antidomain Kleene Algebra, we give
 a lifting operation from predicates to @{typ "'a nd_fun"} and use it to compute weakest liberal
preconditions.\<close>

\<comment> \<open>We start by deleting some notation and introducing some new.\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Relation.relcomp (infixl ";" 75)
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and antidomain_semiringl.ads_d ("d")

abbreviation p2ndf :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

lemma p2ndf_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> \<cdot> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> + \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  "d \<lceil>P\<rceil> = \<lceil>P\<rceil>" "\<lceil>P\<rceil> \<le> \<eta>\<^sup>\<bullet>"
  unfolding less_eq_nd_fun_def times_nd_fun_def plus_nd_fun_def ads_d_def 
  by (auto simp: nd_fun_eq_iff kcomp_def le_fun_def antidomain_op_nd_fun_def)

lemma wp_nd_fun: "wp F \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<forall>s'. s' \<in> ((F\<^sub>\<bullet>) s) \<longrightarrow> P s'\<rceil>"
  apply(simp add: fbox_def antidomain_op_nd_fun_def)
  by(rule nd_fun_ext, auto simp: Rep_comp_hom kcomp_prop)

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})\<^sup>\<bullet>" 

abbreviation seq_comp :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" (infixl ";" 75)
  where "f ; g \<equiv> f \<cdot> g"

lemma wp_assign[simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)\<rceil>"
  unfolding wp_nd_fun nd_fun_eq_iff vec_upd_def assign_def by auto

abbreviation skip :: "'a nd_fun"
  where "skip \<equiv> 1"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF P THEN X ELSE Y \<equiv> cond \<lceil>P\<rceil> X Y"

abbreviation loopi_sugar :: "'a nd_fun \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP R INV I \<equiv> loopi R \<lceil>I\<rceil>"

lemma wp_loopI: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp R \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (LOOP R INV I) \<lceil>Q\<rceil>"
  using fbox_loopi[of "\<lceil>P\<rceil>"] by auto


subsection \<open> Verification of hybrid programs \<close>


text  \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> 'b nd_fun" ("EVOL")
  where "EVOL \<phi> G T = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G T)\<^sup>\<bullet>"

lemma wp_g_dyn[simp]: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "wp (EVOL \<phi> G T) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding wp_nd_fun g_evol_def g_orbit_eq by (auto simp: fun_eq_iff)


text \<open>Verification by providing solutions\<close>

definition g_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a nd_fun" ("(1x\<acute>= _ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) \<equiv> (\<lambda> s. g_orbital f G T S t\<^sub>0 s)\<^sup>\<bullet>"

lemma wp_g_orbital: "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>= 
  \<lceil>\<lambda> s. \<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq(1) wp_nd_fun g_ode_def by (auto simp: fun_eq_iff)

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

lemma wp_orbit: "wp (\<gamma>\<^sup>\<phi>\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s))\<rceil>"
  unfolding orbit_def wp_g_ode g_ode_def[symmetric] by auto

end


text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
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
  apply(rule fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv[simp]: "(\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_orbital by(auto simp: fun_eq_iff)

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
  unfolding diff_inv_eq_inv_set orbit_def by auto

end

lemma wp_g_odei: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow>
  \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def 
  apply(rule_tac b="wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" in order.trans)
   apply(rule_tac I="I" in wp_g_orbital_inv, simp_all)
  apply(subst wp_g_orbital_guard, simp)
  by (rule fbox_iso, simp)

subsection \<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_ode[where f="\<lambda>s. c" and \<phi>="(\<lambda> t s. s + t *\<^sub>R c)"])
  using line_is_local_flow[OF assms] by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_ode, auto)

lemma diff_weak_axiom: 
  "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_orbital image_def by force

lemma diff_weak_rule: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  by (subst wp_g_orbital) (auto simp: g_ode_def)

lemma wp_g_orbit_IdD:
  assumes "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
    and "\<forall>\<tau>\<in>(down T t). x \<tau> \<in> g_orbital f G T S t\<^sub>0 s"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> g_orbital f G T S t\<^sub>0 s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f G T S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_nd_fun g_ode_def 
    by (subst (asm) nd_fun_eq_iff) auto
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym)
  fix s show "((x\<acute>= f & G on T S @ t\<^sub>0)\<^sub>\<bullet>) s \<subseteq> ((x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0)\<^sub>\<bullet>) s"
  proof(clarsimp simp: g_ode_def)
    fix s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"(\<P> X (down T \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using wp_g_orbit_IdD[OF assms(3)] by blast
    thus "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> by fastforce
  qed
next 
  fix s show "((x\<acute>= f & \<lambda>s. G s \<and> C s on T S @ t\<^sub>0)\<^sub>\<bullet>) s \<subseteq> ((x\<acute>= f & G on T S @ t\<^sub>0)\<^sub>\<bullet>) s" 
    by (auto simp: g_orbital_eq g_ode_def)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(simp add: wp_nd_fun g_orbital_eq g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_nd_fun, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_nd_fun) (auto simp: g_ode_def)
qed

text \<open>The rules of dL\<close>

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = \<lceil>\<lambda>x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  by (subst diff_solve_axiom[of UNIV]) (auto simp: fun_eq_iff)

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
  assumes "wp (x\<acute>= f & G) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
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