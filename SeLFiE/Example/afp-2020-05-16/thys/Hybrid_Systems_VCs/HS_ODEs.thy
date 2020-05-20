(*  Title:       ODEs and Dynamical Systems for HS verification
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Ordinary Differential Equations \<close>

text \<open>Vector fields @{text "f::real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)"} represent systems 
of ordinary differential equations (ODEs). Picard-Lindeloef's theorem guarantees existence 
and uniqueness of local solutions to initial value problems involving Lipschitz continuous 
vector fields. A (local) flow @{text "\<phi>::real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)"} for such 
a system is the function that maps initial conditions to their unique solutions. In dynamical 
systems, the set of all points @{text "\<phi> t s::'a"} for a fixed @{text "s::'a"} is the flow's 
orbit. If the orbit of each @{text "s \<in> I"} is conatined in @{text I}, then @{text I} is an 
invariant set of this system. This section formalises these concepts with a focus on hybrid 
systems (HS) verification.\<close>

theory HS_ODEs
  imports "HS_Preliminaries"
begin

subsection \<open> Initial value problems and orbits \<close>

notation image ("\<P>")

lemma image_le_pred[simp]: "(\<P> f A \<subseteq> {s. G s}) = (\<forall>x\<in>A. G (f x))"
  unfolding image_def by force

definition ivp_sols :: "(real \<Rightarrow> 'a \<Rightarrow> ('a::real_normed_vector)) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set" ("Sols")
  where "Sols f T S t\<^sub>0 s = {X |X. (D X = (\<lambda>t. f t (X t)) on T) \<and> X t\<^sub>0 = s \<and> X \<in> T \<rightarrow> S}"

lemma ivp_solsI: 
  assumes "D X = (\<lambda>t. f t (X t)) on T" "X t\<^sub>0 = s" "X \<in> T \<rightarrow> S"
  shows "X \<in> Sols f T S t\<^sub>0 s"
  using assms unfolding ivp_sols_def by blast

lemma ivp_solsD:
  assumes "X \<in> Sols f T S t\<^sub>0 s"
  shows "D X = (\<lambda>t. f t (X t)) on T"
    and "X t\<^sub>0 = s" and "X \<in> T \<rightarrow> S"
  using assms unfolding ivp_sols_def by auto

abbreviation "down T t \<equiv> {\<tau>\<in>T. \<tau>\<le> t}"

definition g_orbit :: "(('a::ord) \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set" ("\<gamma>")
  where "\<gamma> X G T = \<Union>{\<P> X (down T t) |t. \<P> X (down T t) \<subseteq> {s. G s}}"

lemma g_orbit_eq: 
  fixes X::"('a::preorder) \<Rightarrow> 'b"
  shows "\<gamma> X G T = {X t |t. t \<in> T \<and> (\<forall>\<tau>\<in>down T t. G (X \<tau>))}"
  unfolding g_orbit_def apply safe
  using le_left_mono by blast auto

definition g_orbital :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  ('a::real_normed_vector) \<Rightarrow> 'a set" 
  where "g_orbital f G T S t\<^sub>0 s = \<Union>{\<gamma> X G T |X. X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f G T S t\<^sub>0 s = 
  {X t |t X. t \<in> T \<and> \<P> X (down T t) \<subseteq> {s. G s} \<and> X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s }" 
  unfolding g_orbital_def ivp_sols_def g_orbit_eq image_le_pred by auto

lemma g_orbitalI:
  assumes "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s"
    and "t \<in> T" and "(\<P> X (down T t) \<subseteq> {s. G s})"
  shows "X t \<in> g_orbital f G T S t\<^sub>0 s"
  using assms unfolding g_orbital_eq(1) by auto

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f G T S t\<^sub>0 s"
  obtains X and t where "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s"
  and "X t = s'" and "t \<in> T" and "(\<P> X (down T t) \<subseteq> {s. G s})"
  using assms unfolding g_orbital_def g_orbit_eq by auto

no_notation g_orbit ("\<gamma>")


subsection \<open> Differential Invariants \<close>

definition diff_invariant :: "('a \<Rightarrow> bool) \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
  'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "diff_invariant I f T S t\<^sub>0 G \<equiv> (\<Union> \<circ> (\<P> (g_orbital f G T S t\<^sub>0))) {s. I s} \<subseteq> {s. I s}"

lemma diff_invariant_eq: "diff_invariant I f T S t\<^sub>0 G = 
  (\<forall>s. I s \<longrightarrow> (\<forall>X\<in>Sols (\<lambda>t. f) T S t\<^sub>0 s. (\<forall>t\<in>T.(\<forall>\<tau>\<in>(down T t). G (X \<tau>)) \<longrightarrow> I (X t))))"
  unfolding diff_invariant_def g_orbital_eq image_le_pred by auto

lemma diff_inv_eq_inv_set:
  "diff_invariant I f T S t\<^sub>0 G = (\<forall>s. I s \<longrightarrow> (g_orbital f G T S t\<^sub>0 s) \<subseteq> {s. I s})"
  unfolding diff_invariant_eq g_orbital_eq image_le_pred by auto

named_theorems diff_invariant_rules "rules for certifying differential invariants."

lemma diff_invariant_eq_rule [diff_invariant_rules]:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> (D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = ((*\<^sub>R) 0) on T)"
  shows "diff_invariant (\<lambda>s. \<mu> s = \<nu> s) f T S t\<^sub>0 G"
proof(simp add: diff_invariant_eq ivp_sols_def, clarsimp)
  fix X \<tau> assume tHyp:"\<tau> \<in> T" and x_ivp:"D X = (\<lambda>\<tau>. f (X \<tau>)) on T" "\<mu> (X t\<^sub>0) = \<nu> (X t\<^sub>0)" 
  hence obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R 0) at t within T"
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0--\<tau>} \<subseteq> T"
    using closed_segment_subset_interval tHyp Thyp by blast
  hence "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0--\<tau>}" and "\<mu> (X \<tau>) - \<nu> (X \<tau>) - (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) = (\<tau> - t\<^sub>0) * t *\<^sub>R 0"
    using mvt_very_simple_closed_segmentE by blast
  thus "\<mu> (X \<tau>) = \<nu> (X \<tau>)" 
    by (simp add: x_ivp(2))
qed

lemma diff_invariant_leq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> (\<forall>\<tau>\<in>T. (\<tau> > t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)) \<and> 
  (\<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))) \<and> (D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on T)"
  shows "diff_invariant (\<lambda>s. \<nu> s \<le> \<mu> s) f T S t\<^sub>0 G"
proof(simp add: diff_invariant_eq ivp_sols_def, clarsimp)
  fix X \<tau> assume "\<tau> \<in> T" and x_ivp:"D X = (\<lambda>\<tau>. f (X \<tau>)) on T" "\<nu> (X t\<^sub>0) \<le> \<mu> (X t\<^sub>0)"
  {assume "\<tau> \<noteq> t\<^sub>0"
  hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
    "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
    using x_ivp assms by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<mu>' (X t) - \<nu>' (X t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<\<tau>} \<subseteq> T" "{t\<^sub>0--\<tau>} \<subseteq> T"
    using \<open>\<tau> \<in> T\<close> Thyp \<open>\<tau> \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0<--<\<tau>}" and
    "(\<mu> (X \<tau>) - \<nu> (X \<tau>)) - (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<mu>' (X t) -  \<nu>' (X t))) (\<tau> - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>\<tau> \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<mu> (X \<tau>) - \<nu> (X \<tau>) = (\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0))" 
    by force
  have  "\<tau> > t\<^sub>0 \<Longrightarrow> t > t\<^sub>0" "\<not> t\<^sub>0 \<le> \<tau> \<Longrightarrow> t < t\<^sub>0" "t \<in> T"
    using \<open>t \<in> {t\<^sub>0<--<\<tau>}\<close> obs2 unfolding open_segment_eq_real_ivl by auto
  moreover have "t > t\<^sub>0 \<Longrightarrow> (\<mu>' (X t) -  \<nu>' (X t)) \<ge> 0" "t < t\<^sub>0 \<Longrightarrow> (\<mu>' (X t) -  \<nu>' (X t)) \<le> 0"
    using primed(1,2)[OF \<open>t \<in> T\<close>] by auto
  ultimately have "(\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) \<ge> 0"
    apply(case_tac "\<tau> \<ge> t\<^sub>0") 
    by (force, auto simp: split_mult_pos_le)
  hence "(\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) \<ge> 0" 
    using  x_ivp(2) by auto
  hence "\<nu> (X \<tau>) \<le> \<mu> (X \<tau>)" 
    using mvt by simp}
  thus "\<nu> (X \<tau>) \<le> \<mu> (X \<tau>)"
    using x_ivp by blast
qed

lemma diff_invariant_less_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall> X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> (\<forall>\<tau>\<in>T. (\<tau> > t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)) \<and> 
  (\<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))) \<and> (D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on T)"
  shows "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f T S t\<^sub>0 G"
proof(simp add: diff_invariant_eq ivp_sols_def, clarsimp)
  fix X \<tau> assume "\<tau> \<in> T" and x_ivp:"D X = (\<lambda>\<tau>. f (X \<tau>)) on T" "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)"
  {assume "\<tau> \<noteq> t\<^sub>0"
  hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
    "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
    using x_ivp assms by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<mu>' (X t) - \<nu>' (X t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<\<tau>} \<subseteq> T" "{t\<^sub>0--\<tau>} \<subseteq> T"
    using \<open>\<tau> \<in> T\<close> Thyp \<open>\<tau> \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0<--<\<tau>}" and
    "(\<mu> (X \<tau>) - \<nu> (X \<tau>)) - (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<mu>' (X t) -  \<nu>' (X t))) (\<tau> - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>\<tau> \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<mu> (X \<tau>) - \<nu> (X \<tau>) = (\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0))" 
    by force
  have  "\<tau> > t\<^sub>0 \<Longrightarrow> t > t\<^sub>0" "\<not> t\<^sub>0 \<le> \<tau> \<Longrightarrow> t < t\<^sub>0" "t \<in> T"
    using \<open>t \<in> {t\<^sub>0<--<\<tau>}\<close> obs2 unfolding open_segment_eq_real_ivl by auto
  moreover have "t > t\<^sub>0 \<Longrightarrow> (\<mu>' (X t) -  \<nu>' (X t)) \<ge> 0" "t < t\<^sub>0 \<Longrightarrow> (\<mu>' (X t) -  \<nu>' (X t)) \<le> 0"
    using primed(1,2)[OF \<open>t \<in> T\<close>] by auto
  ultimately have "(\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) \<ge> 0"
    apply(case_tac "\<tau> \<ge> t\<^sub>0") 
    by (force, auto simp: split_mult_pos_le)
  hence "(\<tau> - t\<^sub>0) * (\<mu>' (X t) -  \<nu>' (X t)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) > 0" 
    using x_ivp(2) by auto
  hence "\<nu> (X \<tau>) < \<mu> (X \<tau>)" 
    using mvt by simp}
  thus "\<nu> (X \<tau>) < \<mu> (X \<tau>)"
    using x_ivp by blast
qed

lemma diff_invariant_nleq_rule:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  shows "diff_invariant (\<lambda>s. \<not> \<nu> s \<le> \<mu> s) f T S t\<^sub>0 G \<longleftrightarrow> diff_invariant (\<lambda>s. \<nu> s > \<mu> s) f T S t\<^sub>0 G"
  unfolding diff_invariant_eq apply safe
  by (clarsimp, erule_tac x=s in allE, simp, erule_tac x=X in ballE, force, force)+

lemma diff_invariant_neq_rule [diff_invariant_rules]:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f T S t\<^sub>0 G"
    and "diff_invariant (\<lambda>s. \<nu> s > \<mu> s) f T S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. \<nu> s \<noteq> \<mu> s) f T S t\<^sub>0 G"
proof(unfold diff_invariant_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume "\<nu> s \<noteq> \<mu> s" and Xhyp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
     and thyp: "t \<in> T" and Ghyp: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  hence "\<nu> s < \<mu> s \<or> \<nu> s > \<mu> s"
    by linarith
  moreover have "\<nu> s < \<mu> s \<Longrightarrow> \<nu> (X t) < \<mu> (X t)"
    using assms(1) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  moreover have "\<nu> s > \<mu> s \<Longrightarrow> \<nu> (X t) > \<mu> (X t)"
    using assms(2) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  ultimately show "\<nu> (X t) = \<mu> (X t) \<Longrightarrow> False"
    by auto
qed

lemma diff_invariant_neq_rule_converse:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T" "\<forall>t\<in>T. t\<^sub>0 \<le> t"
      and conts: "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> 
  continuous_on (\<P> X T) \<nu> \<and> continuous_on (\<P> X T) \<mu>"
      and dIhyp:"diff_invariant (\<lambda>s. \<nu> s \<noteq> \<mu> s) f T S t\<^sub>0 G"
    shows "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f T S t\<^sub>0 G"
proof(unfold diff_invariant_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume ineq0: "\<nu> s < \<mu> s" and Xhyp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s"
    and Ghyp: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)" and thyp: "t\<in>T"
  hence ineq1: "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)"
    by (auto simp: ivp_solsD)
  have "t\<^sub>0 \<le> t" and "\<mu> (X t) \<noteq> \<nu> (X t)"
    using \<open>t \<in> T\<close> Thyp dIhyp thyp Xhyp Ghyp ineq0 
    unfolding diff_invariant_eq by force+
  moreover
  {assume ineq2:"\<nu> (X t) > \<mu> (X t)"
    note continuous_on_compose[OF vderiv_on_continuous_on[OF ivp_solsD(1)[OF Xhyp]]]
    hence "continuous_on T (\<nu> \<circ> X)" and "continuous_on T (\<mu> \<circ> X)"
      using ivp_solsD(1)[OF Xhyp] conts by auto
    also have "{t\<^sub>0--t} \<subseteq> T"
      using Thyp thyp by (simp add: closed_segment_subset_interval)
    ultimately have "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<nu> (X \<tau>))" 
      and "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<mu> (X \<tau>))"
      using continuous_on_subset by auto
    then obtain \<tau> where "\<tau> \<in> {t\<^sub>0--t}" "\<mu> (X \<tau>) = \<nu> (X \<tau>)"
      using IVT_two_functions_real_ivl[OF _ _ ineq1 ineq2] by force
    hence "\<forall>r\<in>down T \<tau>. G (X r)" and "\<tau> \<in> T"
      using Ghyp \<open>\<tau> \<in> {t\<^sub>0--t}\<close> \<open>t\<^sub>0 \<le> t\<close> \<open>{t\<^sub>0--t} \<subseteq> T\<close> 
      by (auto simp: closed_segment_eq_real_ivl)
    hence "\<mu> (X \<tau>) \<noteq> \<nu> (X \<tau>)"
      using dIhyp Xhyp \<open>\<nu> s < \<mu> s\<close> 
      unfolding diff_invariant_eq by force
    hence "False"
      using \<open>\<mu> (X \<tau>) = \<nu> (X \<tau>)\<close> by blast}
  ultimately show "\<nu> (X t) < \<mu> (X t)"
    by fastforce
qed

lemma diff_invariant_conj_rule [diff_invariant_rules]:
assumes "diff_invariant I\<^sub>1 f T S t\<^sub>0 G" 
    and "diff_invariant I\<^sub>2 f T S t\<^sub>0 G"
shows "diff_invariant (\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) f T S t\<^sub>0 G"
  using assms unfolding diff_invariant_def by auto

lemma diff_invariant_disj_rule [diff_invariant_rules]:
assumes "diff_invariant I\<^sub>1 f T S t\<^sub>0 G" 
    and "diff_invariant I\<^sub>2 f T S t\<^sub>0 G"
shows "diff_invariant (\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) f T S t\<^sub>0 G"
  using assms unfolding diff_invariant_def by auto


subsection \<open> Picard-Lindeloef \<close>

text\<open> A locale with the assumptions of Picard-Lindeloef theorem. It extends 
@{term "ll_on_open_it"} by providing an initial time @{term "t\<^sub>0 \<in> T"}.\<close>

locale picard_lindeloef =
  fixes f::"real \<Rightarrow> ('a::{heine_borel,banach}) \<Rightarrow> 'a" and T::"real set" and S::"'a set" and t\<^sub>0::real
  assumes open_domain: "open T" "open S"
    and interval_time: "is_interval T"
    and init_time: "t\<^sub>0 \<in> T"
    and cont_vec_field: "\<forall>s \<in> S. continuous_on T (\<lambda>t. f t s)"
    and lipschitz_vec_field: "local_lipschitz T S f"
begin

sublocale ll_on_open_it T f S t\<^sub>0
  by (unfold_locales) (auto simp: cont_vec_field lipschitz_vec_field interval_time open_domain) 

lemmas subintervalI = closed_segment_subset_domain

lemma csols_eq: "csols t\<^sub>0 s = {(X, t). t \<in> T \<and>  X \<in> Sols f {t\<^sub>0--t} S t\<^sub>0 s}"
  unfolding ivp_sols_def csols_def solves_ode_def using subintervalI[OF init_time] by auto

abbreviation "ex_ivl s \<equiv> existence_ivl t\<^sub>0 s"

lemma unique_solution:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on {t\<^sub>0--t}" "X t\<^sub>0 = s" "X \<in> {t\<^sub>0--t} \<rightarrow> S" and "t \<in> T"
    and yivp: "D Y = (\<lambda>t. f t (Y t)) on {t\<^sub>0--t}" "Y t\<^sub>0 = s" "Y \<in> {t\<^sub>0--t} \<rightarrow> S" and "s \<in> S" 
  shows "X t = Y t"
proof-
  have "(X, t) \<in> csols t\<^sub>0 s"
    using xivp \<open>t \<in> T\<close> unfolding csols_eq ivp_sols_def by auto
  hence ivl_fact: "{t\<^sub>0--t} \<subseteq> ex_ivl s"
    unfolding existence_ivl_def by auto
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>{t\<^sub>0--t}. X \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" X] xivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  also have "\<forall>\<tau>\<in>{t\<^sub>0--t}. Y \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" Y] yivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  ultimately show "X t = Y t"
    by auto
qed

lemma solution_eq_flow:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on ex_ivl s" "X t\<^sub>0 = s" "X \<in> ex_ivl s \<rightarrow> S" 
    and "t \<in> ex_ivl s" and "s \<in> S" 
  shows "X t = flow t\<^sub>0 s t"
proof-
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>ex_ivl s. X \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "ex_ivl s" X] existence_ivl_initial_time[OF init_time \<open>s \<in> S\<close>]
      xivp flow_initial_time[OF init_time \<open>s \<in> S\<close>] unfolding solves_ode_def by simp
  thus "X t = flow t\<^sub>0 s t"
    by (auto simp: \<open>t \<in> ex_ivl s\<close>)
qed

end

lemma local_lipschitz_add: 
  fixes f1 f2 :: "real \<Rightarrow> 'a::banach \<Rightarrow> 'a"
  assumes "local_lipschitz T S f1"
      and "local_lipschitz T S f2" 
    shows "local_lipschitz T S (\<lambda>t s. f1 t s + f2 t s)"
proof(unfold local_lipschitz_def, clarsimp)
  fix s and t assume "s \<in> S" and "t \<in> T"
  obtain \<epsilon>\<^sub>1 L1 where "\<epsilon>\<^sub>1 > 0" and L1: "\<And>\<tau>. \<tau>\<in>cball t \<epsilon>\<^sub>1 \<inter> T \<Longrightarrow> L1-lipschitz_on (cball s \<epsilon>\<^sub>1 \<inter> S) (f1 \<tau>)"
    using local_lipschitzE[OF assms(1) \<open>t \<in> T\<close> \<open>s \<in> S\<close>] by blast
  obtain \<epsilon>\<^sub>2 L2 where "\<epsilon>\<^sub>2 > 0" and L2: "\<And>\<tau>. \<tau>\<in>cball t \<epsilon>\<^sub>2 \<inter> T \<Longrightarrow> L2-lipschitz_on (cball s \<epsilon>\<^sub>2 \<inter> S) (f2 \<tau>)"
    using local_lipschitzE[OF assms(2) \<open>t \<in> T\<close> \<open>s \<in> S\<close>] by blast
  have ballH: "cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S \<subseteq> cball s \<epsilon>\<^sub>1 \<inter> S" "cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S \<subseteq> cball s \<epsilon>\<^sub>2 \<inter> S"
    by auto
  have obs1: "\<forall>\<tau>\<in>cball t \<epsilon>\<^sub>1 \<inter> T. L1-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (f1 \<tau>)"
    using lipschitz_on_subset[OF L1 ballH(1)] by blast
  also have obs2: "\<forall>\<tau>\<in>cball t \<epsilon>\<^sub>2 \<inter> T. L2-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (f2 \<tau>)"
    using lipschitz_on_subset[OF L2 ballH(2)] by blast
  ultimately have "\<forall>\<tau>\<in>cball t (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> T. 
    (L1 + L2)-lipschitz_on (cball s (min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2) \<inter> S) (\<lambda>s. f1 \<tau> s + f2 \<tau> s)"
    using lipschitz_on_add by fastforce
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. L-lipschitz_on (cball s u \<inter> S) (\<lambda>s. f1 t s + f2 t s)"
    apply(rule_tac x="min \<epsilon>\<^sub>1 \<epsilon>\<^sub>2" in exI)
    using \<open>\<epsilon>\<^sub>1 > 0\<close> \<open>\<epsilon>\<^sub>2 > 0\<close> by force
qed

lemma picard_lindeloef_add: "picard_lindeloef f1 T S t\<^sub>0 \<Longrightarrow> picard_lindeloef f2 T S t\<^sub>0 \<Longrightarrow> 
  picard_lindeloef (\<lambda>t s. f1 t s + f2 t s) T S t\<^sub>0"
  unfolding picard_lindeloef_def apply(clarsimp, rule conjI)
  using continuous_on_add apply fastforce
  using local_lipschitz_add by blast

lemma picard_lindeloef_constant: "picard_lindeloef (\<lambda>t s. c) UNIV UNIV t\<^sub>0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  by (rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)


subsection \<open> Flows for ODEs \<close>

text\<open> A locale designed for verification of hybrid systems. The user can select the interval 
of existence and the defining flow equation via the variables @{term "T"} and @{term "\<phi>"}.\<close>

locale local_flow = picard_lindeloef "(\<lambda> t. f)" T S 0 
  for f::"'a::{heine_borel,banach} \<Rightarrow> 'a" and T S L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp:
    "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--t}"
    "\<And> s. s \<in> S \<Longrightarrow> \<phi> 0 s = s"
    "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (\<lambda>t. \<phi> t s) \<in> {0--t} \<rightarrow> S"
begin

lemma in_ivp_sols_ivl: 
  assumes "t \<in> T" "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) {0--t} S 0 s"
  apply(rule ivp_solsI)
  using ivp assms by auto

lemma eq_solution_ivl:
  assumes xivp: "D X = (\<lambda>t. f (X t)) on {0--t}" "X 0 = s" "X \<in> {0--t} \<rightarrow> S" 
    and indom: "t \<in> T" "s \<in> S"
  shows "X t = \<phi> t s"
  apply(rule unique_solution[OF xivp \<open>t \<in> T\<close>])
  using \<open>s \<in> S\<close> ivp indom by auto

lemma ex_ivl_eq:
  assumes "s \<in> S"
  shows "ex_ivl s = T"
  using existence_ivl_subset[of s] apply safe
  unfolding existence_ivl_def csols_eq 
  using in_ivp_sols_ivl[OF _ assms] by blast

lemma has_derivative_on_open1: 
  assumes  "t > 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t + r/2 > 0"
    using \<open>r > 0\<close> \<open>t > 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t + r/2} \<subseteq> T"
    unfolding abs_le_eq abs_le_eq real_ivl_eqs[OF \<open>t > 0\<close>] real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] 
    by clarify (case_tac "t < x", simp_all add: cball_def ball_def dist_norm subset_eq field_simps)
  have "t + r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs[OF rHyp(1)] by (simp add: subset_eq)
  hence "{0--t + r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t + r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t + r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by auto
  have "t \<in> {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] using rHyp \<open>t > 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t + r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open2: 
  assumes "t < 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t - r/2 < 0"
    using \<open>r > 0\<close> \<open>t < 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t - r/2} \<subseteq> T"
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
      real_ivl_eqs[OF rHyp(1)] by(auto simp: subset_eq)
  have "t - r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs by (simp add: subset_eq)
  hence "{0--t - r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t - r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t - r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  have "t \<in> {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl using rHyp \<open>t < 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t - r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open3: 
  assumes "s \<in> S"
  obtains B where "0 \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) at 0 within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball 0 r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) init_time by blast
  hence "r/2 \<in> T" "-r/2 \<in> T" "r/2 > 0"
    unfolding real_ivl_eqs by auto
  hence subs: "{0--r/2} \<subseteq> T" "{0--(-r/2)} \<subseteq> T"
    using subintervalI[OF init_time] by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  also have "{0--r/2} = {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    "{0--(-r/2)} = {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  ultimately have vderivs:
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  have obs: "0 \<in> {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl using \<open>r/2 > 0\<close> by auto
  have union: "{-r/2--r/2} = {0--r/2} \<union> {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2--r/2})"
    using has_vderiv_on_union[OF vderivs] by simp
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2<--<r/2})"
    using has_vderiv_on_subset[OF _ segment_open_subset_closed[of "-r/2" "r/2"]] by auto
  hence "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) (at 0 within {-r/2<--<r/2})"
    unfolding has_vderiv_on_def has_vector_derivative_def using obs by blast
  moreover have "open {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl by simp
  moreover have "{-r/2<--<r/2} \<subseteq> T"
    using subs union segment_open_subset_closed by blast 
  ultimately show ?thesis
    using obs that by blast
qed

lemma has_derivative_on_open: 
  assumes "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
  apply(subgoal_tac "t < 0 \<or> t = 0 \<or> t > 0")
  using has_derivative_on_open1[OF _ assms] has_derivative_on_open2[OF _ assms]
    has_derivative_on_open3[OF \<open>s \<in> S\<close>] by blast force

lemma in_domain:
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> T \<rightarrow> S"
  unfolding ex_ivl_eq[symmetric] existence_ivl_def
  using local.mem_existence_ivl_subset ivp(3)[OF _ assms] by blast

lemma has_vderiv_on_domain:
  assumes "s \<in> S"
  shows "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T"
proof(unfold has_vderiv_on_def has_vector_derivative_def, clarsimp)
  fix t assume "t \<in> T"
  then obtain B where "t \<in> B" and "open B" and "B \<subseteq> T" 
    and Dhyp: "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B"
    using assms has_derivative_on_open[OF \<open>t \<in> T\<close>] by blast
  hence "t \<in> interior B"
    using interior_eq by auto
  thus "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within T"
    using has_derivative_at_within_mono[OF _ \<open>B \<subseteq> T\<close> Dhyp] by blast
qed

lemma in_ivp_sols: 
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) T S 0 s"
  using has_vderiv_on_domain ivp(2) in_domain apply(rule ivp_solsI)
  using assms by auto

lemma eq_solution:
  assumes "X \<in> Sols (\<lambda>t. f) T S 0 s" and "t \<in> T" and "s \<in> S"
  shows "X t = \<phi> t s"
proof-
  have "D X = (\<lambda>t. f (X t)) on (ex_ivl s)" and "X 0 = s" and "X \<in> (ex_ivl s) \<rightarrow> S"
    using ivp_solsD[OF assms(1)] unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by auto
  note solution_eq_flow[OF this]
  hence "X t = flow 0 s t"
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] using assms by blast
  also have "\<phi> t s = flow 0 s t"
    apply(rule solution_eq_flow ivp)
        apply(simp_all add: assms(2,3) ivp(2)[OF \<open>s \<in> S\<close>])
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by (auto simp: has_vderiv_on_domain assms in_domain)
  ultimately show "X t = \<phi> t s"
    by simp
qed

lemma ivp_sols_collapse: 
  assumes "T = UNIV" and "s \<in> S"
  shows "Sols (\<lambda>t. f) T S 0 s = {(\<lambda>t. \<phi> t s)}"
  using in_ivp_sols eq_solution assms by auto

lemma additive_in_ivp_sols:
  assumes "s \<in> S" and "\<P> (\<lambda>\<tau>. \<tau> + t) T \<subseteq> T"
  shows "(\<lambda>\<tau>. \<phi> (\<tau> + t) s) \<in> Sols (\<lambda>t. f) T S 0 (\<phi> (0 + t) s)"
  apply(rule ivp_solsI, rule vderiv_on_compose_add)
  using has_vderiv_on_domain has_vderiv_on_subset assms 
    apply blast
  using in_domain assms by auto

lemma is_monoid_action:
  assumes "s \<in> S" and "T = UNIV"
  shows "\<phi> 0 s = s" and "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
proof-
  show "\<phi> 0 s = s"
    using ivp assms by simp
  have "\<phi> (0 + t\<^sub>2) s = \<phi> t\<^sub>2 s" 
    by simp
  also have "\<phi> t\<^sub>2 s \<in> S"
    using in_domain assms by auto
  finally show "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
    using eq_solution[OF additive_in_ivp_sols] assms by auto
qed

definition orbit :: "'a \<Rightarrow> 'a set" ("\<gamma>\<^sup>\<phi>")
  where "\<gamma>\<^sup>\<phi> s = g_orbital f (\<lambda>s. True) T S 0 s"

lemma orbit_eq[simp]: 
  assumes "s \<in> S"
  shows "\<gamma>\<^sup>\<phi> s = {\<phi> t s| t. t \<in> T}"
  using eq_solution assms unfolding orbit_def g_orbital_eq ivp_sols_def
  by(auto intro!: has_vderiv_on_domain ivp(2) in_domain)

lemma g_orbital_collapses: 
  assumes "s \<in> S"
  shows "g_orbital f G T S 0 s = {\<phi> t s| t. t \<in> T \<and> (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s))}"
proof(rule subset_antisym, simp_all only: subset_eq)
  let ?gorbit = "{\<phi> t s |t. t \<in> T \<and> (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s))}"
  {fix s' assume "s' \<in> g_orbital f G T S 0 s"
    then obtain X and t where x_ivp:"X \<in> Sols (\<lambda>t. f) T S 0 s" 
      and "X t = s'" and "t \<in> T" and guard:"(\<P> X (down T t) \<subseteq> {s. G s})"
      unfolding g_orbital_def g_orbit_eq by auto
    have obs:"\<forall>\<tau>\<in>(down T t). X \<tau> = \<phi> \<tau> s"
      using eq_solution[OF x_ivp _ assms] by blast
    hence "\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}"
      using guard by auto 
    also have "\<phi> t s = X t"
      using eq_solution[OF x_ivp \<open>t \<in> T\<close> assms] by simp
    ultimately have "s' \<in> ?gorbit"
      using \<open>X t = s'\<close> \<open>t \<in> T\<close> by auto}
  thus "\<forall>s'\<in> g_orbital f G T S 0 s. s' \<in> ?gorbit"
    by blast
next
  let ?gorbit = "{\<phi> t s |t. t \<in> T \<and> (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s))}"
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> g_orbital f G T S 0 s"
      using assms by(auto intro!: g_orbitalI in_ivp_sols)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> g_orbital f G T S 0 s"
    by blast
qed

end

lemma line_is_local_flow: 
  "0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> local_flow (\<lambda> s. c) T UNIV (\<lambda> t s. s + t *\<^sub>R c)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
   apply(rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)
  apply(rule_tac f'1="\<lambda> s. 0" and g'1="\<lambda> s. c" in has_vderiv_on_add[THEN has_vderiv_on_eq_rhs])
    apply(rule derivative_intros, simp)+
  by simp_all

end