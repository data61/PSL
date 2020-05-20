(*  Title:       Verification components with predicate transformers
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with predicate transformers \<close>

text \<open> We use the categorical forward box operator @{text fb\<^sub>\<F>} to compute weakest liberal 
preconditions (wlps) of hybrid programs. Then we repeat the three methods for verifying 
correctness specifications of the continuous dynamics of a HS. \<close>

theory HS_VC_PT
  imports "../HS_ODEs" "Transformer_Semantics.Kleisli_Quantale"
                        
begin

\<comment> \<open>We start by deleting some notation and introducing some new.\<close>

no_notation bres (infixr "\<rightarrow>" 60)
        and dagger ("_\<^sup>\<dagger>" [101] 100)
        and "Relation.relcomp" (infixl ";" 75) 
        and eta ("\<eta>")
        and kcomp (infixl "\<circ>\<^sub>K" 75)

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation eta ("skip")
     and kcomp (infixl ";" 75)
     and g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")


subsection \<open>Verification of regular programs\<close>

text \<open>Properties of the forward box operator. \<close>

lemma "fb\<^sub>\<F> F S = {s. F s \<subseteq> S}"
  unfolding ffb_def map_dual_def klift_def kop_def dual_set_def
  by(auto simp: Compl_eq_Diff_UNIV fun_eq_iff f2r_def converse_def r2f_def)

lemma ffb_eq: "fb\<^sub>\<F> F S = {s. \<forall>s'. s' \<in> F s \<longrightarrow> s' \<in> S}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

lemma ffb_iso: "P \<le> Q \<Longrightarrow> fb\<^sub>\<F> F P \<le> fb\<^sub>\<F> F Q"
  unfolding ffb_eq by auto

lemma ffb_invariants: 
  assumes "{s. I s} \<le> fb\<^sub>\<F> F {s. I s}" and "{s. J s} \<le> fb\<^sub>\<F> F {s. J s}"
  shows "{s. I s \<and> J s} \<le> fb\<^sub>\<F> F {s. I s \<and> J s}"
    and "{s. I s \<or> J s} \<le> fb\<^sub>\<F> F {s. I s \<or> J s}"
  using assms unfolding ffb_eq by auto

text \<open>The weakest liberal precondition (wlp) of the ``skip'' program is the identity. \<close>

lemma ffb_skip[simp]: "fb\<^sub>\<F> skip S = S"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

text \<open>Next, we introduce assignments and their wlps.\<close>

definition vec_upd :: "('a^'n) \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'a^'n"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'n \<Rightarrow> ('a^'n \<Rightarrow> 'a) \<Rightarrow> ('a^'n) \<Rightarrow> ('a^'n) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> (x ::= e) Q = {s. (\<chi> j. ((($) s)(x := (e s))) j) \<in> Q}"
  unfolding vec_upd_def assign_def by (subst ffb_eq) simp

text \<open>The wlp of program composition is just the composition of the wlps.\<close>

lemma ffb_kcomp[simp]: "fb\<^sub>\<F> (G ; F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by(auto simp: kcomp_def)

lemma hoare_kcomp:
  assumes "P \<le> fb\<^sub>\<F> F R" "R \<le> fb\<^sub>\<F> G Q"
  shows "P \<le> fb\<^sub>\<F> (F ; G) Q"
  apply(subst ffb_kcomp) 
  by (rule order.trans[OF assms(1)]) (rule ffb_iso[OF assms(2)])

text \<open>We also have an implementation of the conditional operator and its wlp.\<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where 
  "IF P THEN X ELSE Y = (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else[simp]:
  "fb\<^sub>\<F> (IF T THEN X ELSE Y) Q = {s. T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q} \<inter> {s. \<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q}"
  unfolding ffb_eq ifthenelse_def by auto

lemma hoare_if_then_else:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y) Q"
  using assms 
  apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

text\<open> We also deal with finite iteration. \<close>

lemma kpower_inv: "I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  apply simp
  by(auto simp: kcomp_prop) 

lemma kstar_inv: "I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (kstar F) I"
  unfolding kstar_def ffb_eq apply clarsimp
  using kpower_inv by blast

lemma ffb_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> fb\<^sub>\<F> F I"
  shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using assms(3) kstar_inv by blast
  hence "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  also have "fb\<^sub>\<F> (kstar F) I \<le> fb\<^sub>\<F> (kstar F) Q"
    by (rule ffb_iso[OF assms(2)])
  finally show ?thesis .
qed

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP F INV I \<equiv> (kstar F)"

lemma ffb_loopI: "P \<le> {s. I s}  \<Longrightarrow> {s. I s} \<le> Q \<Longrightarrow> {s. I s} \<le> fb\<^sub>\<F> F {s. I s} \<Longrightarrow> P \<le> fb\<^sub>\<F> (LOOP F INV I) Q"
  unfolding loopi_def using ffb_kstarI[of "P"] by simp


subsection \<open>Verification of hybrid programs\<close>

text \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "EVOL \<phi> G T = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G T)"

lemma fbox_g_evol[simp]: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "fb\<^sub>\<F> (EVOL \<phi> G T) Q = {s. (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}"
  unfolding g_evol_def g_orbit_eq ffb_eq by auto

text \<open>Verification by providing solutions\<close>

lemma ffb_g_orbital: "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q = 
  {s. \<forall>X\<in>Sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> (X t) \<in> Q}"
  unfolding ffb_eq g_orbital_eq subset_eq by (auto simp: fun_eq_iff)

context local_flow
begin

lemma ffb_g_ode: "fb\<^sub>\<F> (x\<acute>= f & G on T S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}" (is "_ = ?wlp")
  unfolding ffb_g_orbital 
  apply(safe, clarsimp)
    apply(erule_tac x="\<lambda>t. \<phi> t x" in ballE)
  using in_ivp_sols 
     apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> x", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma ffb_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> fb\<^sub>\<F> (x\<acute>=f & G on {0..t} S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}"
  unfolding ffb_g_orbital 
  apply(clarsimp, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t x" in ballE, force)
  using in_ivp_sols_ivl 
    apply(force simp: closed_segment_eq_real_ivl)
  using in_ivp_sols_ivl 
   apply(force simp: ivp_sols_def)
  apply(subgoal_tac "\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. X \<tau> = \<phi> \<tau> x)", simp, clarsimp)
  apply(subst eq_solution_ivl, simp_all add: ivp_sols_def)
     apply(rule has_vderiv_on_subset, force, force simp: closed_segment_eq_real_ivl)
    apply(force simp: closed_segment_eq_real_ivl)
  using interval_time init_time 
   apply (meson is_interval_1 order_trans) 
  using init_time by force

lemma ffb_orbit: "fb\<^sub>\<F> \<gamma>\<^sup>\<phi> Q = {s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. \<phi> t s \<in> Q)}"
  unfolding orbit_def ffb_g_ode by simp

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma ffb_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. Q s} = fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. H s}"
  unfolding ffb_g_orbital using assms by auto

lemma ffb_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  by (rule ffb_iso[OF assms(3)])

lemma ffb_diff_inv[simp]: 
  "({s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. I s}) = diff_invariant I f T S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma bdf_diff_inv:
  "diff_invariant I f T S t\<^sub>0 G = (bd\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. I s} \<le> {s. I s})"
  unfolding ffb_fbd_galois_var by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma diff_inv_guard_ignore:
  assumes "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. True) on T S @ t\<^sub>0) {s. I s}"
  shows "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. I s}"
  using assms unfolding ffb_diff_inv diff_invariant_eq image_le_pred by auto

context local_flow
begin

lemma ffb_diff_inv_eq: "diff_invariant I f T S 0 (\<lambda>s. True) = 
  ({s. s \<in> S \<longrightarrow> I s} = fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. True) on T S @ 0) {s. s \<in> S \<longrightarrow> I s})"
  unfolding ffb_diff_inv[symmetric] ffb_g_orbital 
  using init_time 
  apply(clarsimp simp: subset_eq ivp_sols_def)
  apply(safe, force, force)
   apply(subst ivp(2)[symmetric], simp)
   apply(erule_tac x="\<lambda>t. \<phi> t x" in allE)
  using in_domain has_vderiv_on_domain ivp(2) init_time by auto

lemma diff_inv_eq_inv_set:
  "diff_invariant I f T S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end

lemma ffb_g_odei: "P \<le> {s. I s} \<Longrightarrow> {s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. I s} \<Longrightarrow> 
  {s. I s \<and> G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. I s}" in order.trans)
   apply(rule_tac I="{s. I s}" in ffb_g_orbital_inv, simp_all)
  apply(subst ffb_g_orbital_guard, simp)
  by (rule ffb_iso, force)

subsection \<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) Q = 
  {s. \<forall>t\<in>T. (\<P> (\<lambda>\<tau>. s + \<tau> *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> (s + t *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_ode[of "\<lambda>s. c" _ _ "(\<lambda>t s. s + t *\<^sub>R c)"])
  using line_is_local_flow assms unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T UNIV @ 0) Q"
  using assms by(subst local_flow.ffb_g_ode) auto

lemma diff_weak_axiom: "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. G s \<longrightarrow> s \<in> Q}"
  unfolding ffb_g_orbital image_def by force
  
lemma diff_weak_rule: "{s. G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q"
  by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq ffb_eq)

lemma ffb_g_orbital_eq_univD:
  assumes "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. C s} = UNIV" 
    and "\<forall>\<tau>\<in>(down T t). x \<tau> \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s \<longrightarrow> C y" 
    using assms(1) unfolding ffb_eq by fastforce
  ultimately show "C (x \<tau>)" by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"\<P> X (down T \<tau>) \<subseteq> {s. G s}"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s]  by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using assms unfolding ffb_eq by fastforce
    hence "s' \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce}
  thus "(x\<acute>= f & G on T S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
    by blast
next show "\<And>s. (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & G on T S @ t\<^sub>0) s" 
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and ffb_C: "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. C s}"
    and ffb_Q: "P \<le> fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q"
proof(subst ffb_eq, subst g_orbital_eq, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "s \<in> P" and "t \<in> T"
    and x_ivp:"X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>\<tau>. s2p T \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  have "\<forall>\<tau>\<in>(down T t). X \<tau> \<in> (x\<acute>= f & G on T S @ t\<^sub>0) s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>\<tau>\<in>(down T t). C (X \<tau>)" 
    using ffb_C \<open>s \<in> P\<close> by (subst (asm) ffb_eq, auto)
  hence "X t \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "(X t) \<in> Q"
    using \<open>s \<in> P\<close> ffb_Q by (subst (asm) ffb_eq) auto
qed

text\<open>The rules of dL\<close>

abbreviation g_global_orbit ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>=f & G DINV I) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0 DINV I)"

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G) Q"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) by simp

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G) Q = {x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> (x + t *\<^sub>R c) \<in> Q}"
  by (subst diff_solve_axiom[of UNIV]) auto

lemma DW: "fb\<^sub>\<F> (x\<acute>= f & G) Q = fb\<^sub>\<F> (x\<acute>= f & G) {s. G s \<longrightarrow> s \<in> Q}"
  by (rule diff_weak_axiom)
  
lemma dW: "{s. G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>= f & G) Q"
  by (rule diff_weak_rule)

lemma DC:
  assumes "fb\<^sub>\<F> (x\<acute>= f & G) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>= f & G) Q = fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s)) Q"
  by (rule diff_cut_axiom) (auto simp: assms)

lemma dC:
  assumes "P \<le> fb\<^sub>\<F> (x\<acute>= f & G) {s. C s}"
    and "P \<le> fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s)) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G) Q"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "P \<le> {s. I s}" and "diff_invariant I f UNIV UNIV 0 G" and "{s. I s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G) Q"
  by (rule ffb_g_orbital_inv[OF assms(1) _ assms(3)]) (simp add: assms(2))

end