section \<open>Value Iteration for Reachability Probabilities of MDPs\<close>

theory MDP_RP
  imports "../Markov_Models"
begin

subsection \<open>Auxiliary Theorems\<close>

lemma INF_Union_eq: "(INF x\<in>\<Union>A. f x) = (INF a\<in>A. INF x\<in>a. f x)" for f :: "_ \<Rightarrow> 'a::complete_lattice"
  by (auto intro!: antisym INF_greatest intro: INF_lower2)

lemma lift_option_eq_None: "lift_option f A B = None \<longleftrightarrow> (A \<noteq> None \<longrightarrow> B = None)"
  by (cases A; cases B; auto)

lemma lift_option_eq_Some: "lift_option f A B = Some y \<longleftrightarrow> (\<exists>a b. A = Some a \<and> B = Some b \<and> y = f a b)"
  by (cases A; cases B; auto)

lemma ord_option_Some1_iff: "ord_option R (Some a) y \<longleftrightarrow> (\<exists>b. y = Some b \<and> R a b)"
  by (cases y; auto)

lemma ord_option_Some2_iff: "ord_option R x (Some b) \<longleftrightarrow> (\<forall>a. x = Some a \<longrightarrow> R a b)"
  by (cases x; auto)

lemma sym_Restr: "sym A \<Longrightarrow> sym (Restr A S)"
  by (auto simp: sym_def)

lemma trans_Restr: "trans A \<Longrightarrow> trans (Restr A S)"
  by (auto simp: trans_def)

lemma image_eq_singleton_iff: "inj_on f S \<Longrightarrow> f ` S = {y} \<longleftrightarrow> (\<exists>x. S = {x} \<and> y = f x)"
  by (auto elim: inj_img_insertE)

lemma quotient_eq_singleton: "equiv A r \<Longrightarrow> A // r = {B} \<Longrightarrow> B = A"
  using Union_quotient[of A r] by auto

lemma UN_singleton_image: "(\<Union>x\<in>A. {f x}) = f ` A"
  by auto

lemma image_eq_singeltonD: "f ` A = {x} \<Longrightarrow> \<forall>a\<in>A. f a = x"
  by auto

lemma fun_ord_refl: "reflp ord  \<Longrightarrow> reflp (fun_ord ord)"
  by (auto simp: fun_ord_def reflp_def)

lemma fun_ord_trans: "transp ord  \<Longrightarrow> transp (fun_ord ord)"
  by (fastforce simp: fun_ord_def transp_def)

lemma fun_ord_antisym: "antisymp ord  \<Longrightarrow> antisymp (fun_ord ord)"
  by (fastforce simp: fun_ord_def antisymp_def)

lemma fun_ord_combine:
  "fun_ord ord a b \<Longrightarrow> fun_ord ord c d \<Longrightarrow> (\<And>s. ord (a s) (b s) \<Longrightarrow> ord (c s) (d s) \<Longrightarrow> ord (e s) (f s)) \<Longrightarrow> fun_ord ord e f"
  by (auto simp: fun_ord_def)

lemma not_all_eq: "~ (\<forall>y. x \<noteq> y)"
  by auto

lemma ball_vimage_iff: "(\<forall>x\<in>f -` X. P x) \<longleftrightarrow> (\<forall>x. f x \<in> X \<longrightarrow> P x)"
  by auto

lemma UN_If_cases: "(\<Union>x\<in>X. if P x then A x else B x) = (\<Union>x\<in>{x\<in>X. P x}. A x) \<union> (\<Union>x\<in>{x\<in>X. \<not> P x}. B x)"
  by (auto split: if_splits)

lemma (in Reachability_Problem) n_eq_0_closed:
  assumes s: "s \<in> S'" and S': "S' \<subseteq> S" "S' \<inter> S2 = {}" and closed: "\<And>s. s \<in> S' \<Longrightarrow> \<exists>D\<in>K s. D \<subseteq> S'"
  shows "n s = 0"
proof -
  from closed obtain ct where ct: "\<And>s. s \<in> S' \<Longrightarrow> ct s \<in> K s" "\<And>s. s \<in> S' \<Longrightarrow> ct s \<subseteq> S'"
    by metis

  define cfg where "cfg = memoryless_on (\<lambda>s. if s \<in> S' then ct s else arb_act s)"

  have cfg_on: "cfg s \<in> cfg_on s" for s
    unfolding cfg_def using ct by (intro memoryless_on_cfg_onI) auto

  have state_cfg[simp]: "state (cfg s) = s" for s
    unfolding cfg_def by (intro state_memoryless_on)
  have action_cfg[simp]: "action (cfg s) = (if s \<in> S' then ct s else arb_act s)" for s
    unfolding cfg_def by (intro action_memoryless_on)
  have cont_cfg[simp]: "s \<in> S' \<Longrightarrow> t \<in> ct s \<Longrightarrow> cont (cfg s) t = cfg t" for s t
    unfolding cfg_def by (intro cont_memoryless_on) auto

  from s have "v (cfg s) = 0"
  proof (coinduction arbitrary: s rule: v_eq_0_coinduct)
    case (valid cfg') with cfg_on s S' show ?case
      by (auto simp: valid_cfg_def)
  next
    case (nS2 cfg') with S' show ?case
      by auto
  next
    case (cont cfg') with S' ct show ?case
      by (force simp: set_K_cfg)
  qed
  show "n s = 0"
  proof (rule n_eq_0)
    show "s \<in> S" using s S' by auto
  qed fact+
qed

lemma (in Reachability_Problem) n_lb_ennreal:
  fixes x
  assumes "s \<in> S"
  assumes solution: "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> x s \<le> (\<Sum>t\<in>S. ennreal (pmf D t) * x t)"
  assumes solution_n0: "\<And>s. s \<in> S \<Longrightarrow> n s = 0 \<Longrightarrow> x s = 0"
  assumes solution_S2: "\<And>s. s \<in> S2 \<Longrightarrow> x s = 1"
    and le_1:  "\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1"
  shows "x s \<le> n s" (is "_ \<le> ?y s")
proof -
  have x_less_top[simp]: "s \<in> S \<Longrightarrow> x s < top" for s
    using le_1[of s] by (auto simp: less_top[symmetric] top_unique)

  have "enn2real (x s) \<le> enn2real (n s)"
    apply (rule n_lb[OF \<open>s\<in>S\<close>])
    subgoal for s D
      by (rule ennreal_le_iff[THEN iffD1])
          (use S1 in \<open>auto intro!: sum_nonneg simp add: subset_eq solution sum_ennreal[symmetric] ennreal_mult simp del: sum_ennreal\<close>)
    apply (auto simp: solution_n0 solution_S2)
    done
  with \<open>s\<in>S\<close> show ?thesis
    by (subst (asm) ennreal_le_iff[symmetric]) (simp_all add: real_n)
qed

lifting_forget pmf_as_function.pmf.lifting

text \<open>
  Type to describe MDP components. The support (i.e. elements which are not mapped to an empty
set) is the set of states of the component.

Most of this is from:
  Formal verification of probabilistic systems
  Luca de Alfaro (PhD thesis, 1997)
and
  Reachability in MDPs: Refining Convergence of Value Iteration
  Serge Haddad and Benjamin Monmege (2014)
\<close>

typedef 's mdpc = "UNIV :: ('s \<rightharpoonup> 's pmf set) set"
  by auto

setup_lifting type_definition_mdpc

lift_definition states :: "'s mdpc \<Rightarrow> 's set"
  is dom .

declare [[coercion states]]

lift_definition actions :: "'s mdpc \<Rightarrow> 's \<Rightarrow> 's pmf set"
  is "\<lambda>f s. case f s of None \<Rightarrow> {} | Some a \<Rightarrow> a" .

lemma in_states: "actions \<phi> s \<noteq> {} \<Longrightarrow> s \<in> states \<phi>"
  by transfer auto

lemma mdpc_eqI: "states \<phi> = states \<psi> \<Longrightarrow> (\<And>s. s \<in> states \<phi> \<Longrightarrow> actions \<phi> s = actions \<psi> s) \<Longrightarrow> \<phi> = \<psi>"
  apply transfer
  apply (rule ext)
  subgoal premises prems for \<phi> \<psi> x
    using prems(1) prems(2)[of x]
    by (cases "x \<in> dom \<phi>") (auto simp: fun_eq_iff split: option.splits)
  done

lift_definition map_mdpc :: "('s \<Rightarrow> 't) \<Rightarrow> 's mdpc \<Rightarrow> 't mdpc"
  is "\<lambda>m f s. if f ` (m -` {s}) \<subseteq> {None} then None else Some {map_pmf m d | d A t. m t = s \<and> f t = Some A \<and> d \<in> A}" .

lemma states_map_mdpc: "states (map_mdpc f M) = f ` (states M)"
  by (transfer fixing: f) (auto simp: subset_eq image_iff dom_def split: if_splits)

lemma actions_map_mdpc_eq_Collect: "actions (map_mdpc f M) s = {map_pmf f d | d t. f t = s \<and> d \<in> actions M t}"
  by transfer (force simp: subset_eq split: option.splits)

lemma actions_map_mdpc: "actions (map_mdpc f M) s = map_pmf f ` (\<Union>t\<in>f -` {s}. actions M t)"
  by (auto simp: actions_map_mdpc_eq_Collect)

lemma map_mdpc_compose: "map_mdpc f (map_mdpc g M) = map_mdpc (f \<circ> g) M"
  by (intro mdpc_eqI)
     (auto simp add: states_map_mdpc image_comp actions_map_mdpc image_UN map_pmf_compose[symmetric]
                     vimage_comp[symmetric])

lemma map_mdpc_id: "map_mdpc id = id"
  by (auto simp: fun_eq_iff states_map_mdpc actions_map_mdpc intro!: mdpc_eqI)

lemma finite_states_map: "finite (states M) \<Longrightarrow> finite (map_mdpc f M)"
  by (simp add: states_map_mdpc)

lemma finite_actions_map:
  assumes "finite (states M)" "\<And>s. finite (actions M s)" shows "finite (actions (map_mdpc f M) s)"
proof -
  have "(\<Union>x\<in>f -` {s}. actions M x) = (\<Union>x\<in>f -` {s} \<inter> states M. actions M x)"
    using in_states[of M] by auto
  with assms show ?thesis
    by (auto simp add: actions_map_mdpc)
qed

lift_definition fix_loop :: "'s \<Rightarrow> 's mdpc \<Rightarrow> 's mdpc"
  is "\<lambda>s M t. if s = t then Some {return_pmf s} else M t" .

lemma states_fix_loop[simp]: "states (fix_loop s M) = insert s (states M)"
  by transfer (auto simp: subset_eq image_iff dom_def split: if_splits)

lemma actions_fix_loop[simp]: "actions (fix_loop s M) t = (if s = t then {return_pmf s} else actions M t)"
  by transfer auto

lemma fix_loop_idem: "fix_loop s (fix_loop s M) = fix_loop s M"
  by (auto intro!: mdpc_eqI)

lemma fix_loop_commute: "fix_loop s (fix_loop t M) = fix_loop t (fix_loop s M)"
  by (auto intro!: mdpc_eqI)

lemma map_fix_loop:
  assumes f_s: "\<And>t. f s = f t \<Longrightarrow> t = s"
  shows "map_mdpc f (fix_loop s M) = fix_loop (f s) (map_mdpc f M)"
  by (auto simp: states_map_mdpc actions_map_mdpc_eq_Collect split: if_splits intro!: mdpc_eqI dest!: f_s f_s[OF sym]) force+

lift_definition map_actions :: "('s \<Rightarrow> 's pmf set \<Rightarrow> 's pmf set) \<Rightarrow> 's mdpc \<Rightarrow> 's mdpc"
  is "\<lambda>m f s. map_option (m s) (f s)" .

lemma state_map_actions[simp]: "states (map_actions f \<phi>) = states \<phi>"
  by transfer auto

lemma actions_map_actions[simp]: "(s \<notin> states \<phi> \<Longrightarrow> f s {} = {}) \<Longrightarrow> actions (map_actions f \<phi>) s = f s (actions \<phi> s)"
  by transfer (auto split: option.splits)

lift_definition restrict_states :: "'s set \<Rightarrow> 's mdpc \<Rightarrow> 's mdpc"
  is "\<lambda>S f s. if s \<in> S then f s else None" .

lemma state_restrict_states[simp]: "states (restrict_states S \<phi>) = states \<phi> \<inter> S"
  by transfer (auto split: if_splits)

lemma actions_restrict_states[simp]: "actions (restrict_states S \<phi>) s = (if s \<in> S then actions \<phi> s else {})"
  by transfer (auto split: if_splits)

lemma restrict_states_idem: "states \<phi> \<subseteq> A \<Longrightarrow> restrict_states A \<phi> = \<phi>"
  by transfer (force simp: fun_eq_iff subset_eq dom_def)

instantiation mdpc :: (type) lattice
begin

lift_definition less_eq_mdpc :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> bool"
  is "fun_ord (ord_option (\<subseteq>))" .

definition less_mdpc :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> bool"
  where "less_mdpc f g \<longleftrightarrow> (f \<le> g \<and> \<not> g \<le> f)"

lift_definition inf_mdpc :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> 's mdpc"
  is "\<lambda>f g s. lift_option (\<inter>) (f s) (g s)" .

lift_definition sup_mdpc :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> 's mdpc"
  is "\<lambda>f g s. combine_options (\<union>) (f s) (g s)" .

instance
proof
  fix x y z :: "'s mdpc"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (rule less_mdpc_def)
  note ord =
    fun_ord_refl[where 'b="'s", OF reflp_ord_option[where 'a="'s pmf set"], of "(\<subseteq>)"]
    fun_ord_trans[where 'b="'s", OF transp_ord_option[where 'a="'s pmf set"], of "(\<subseteq>)"]
    fun_ord_antisym[where 'b="'s", OF antisymp_ord_option[where 'a="'s pmf set"], of "(\<subseteq>)"]
  show  "x \<le> x" "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (transfer; insert ord; auto simp: transp_def antisymp_def reflp_def)+
  show "x \<sqinter> y \<le> x" "x \<sqinter> y \<le> y"
    by (transfer; auto simp: fun_ord_def ord_option.simps lift_option_def split: Option.bind_split)+
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    apply transfer
    subgoal premises prems for a b c
      using prems by (rule fun_ord_combine) (auto simp: ord_option.simps)
    done
  show "x \<le> x \<squnion> y" "y \<le> x \<squnion> y"
    by (transfer; auto simp: fun_ord_def ord_option.simps combine_options_def not_all_eq split: option.splits)+
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    apply transfer
    subgoal premises prems for a b c
      using prems by (rule fun_ord_combine) (auto simp: ord_option.simps)
    done
qed
end

instantiation mdpc :: (type) complete_lattice
begin

lift_definition bot_mdpc :: "'a mdpc" is "\<lambda>_. None" .

lift_definition top_mdpc :: "'a mdpc" is "\<lambda>_. Some UNIV" .

lift_definition Sup_mdpc :: "'a mdpc set \<Rightarrow> 'a mdpc"
  is "\<lambda>M s. if \<exists>m\<in>M. m s \<noteq> None then Some (\<Union>{ d | m d. m \<in> M \<and> m s = Some d}) else None" .

lift_definition Inf_mdpc :: "'a mdpc set \<Rightarrow> 'a mdpc"
  is "\<lambda>M s. if \<exists>m\<in>M. m s = None then None else Some (\<Inter>{ d | m d. m \<in> M \<and> m s = Some d})" .

instance
proof
  fix x :: "'a mdpc" and X :: "'a mdpc set"
  show "x \<in> X \<Longrightarrow> \<Sqinter>X \<le> x" "x \<in> X \<Longrightarrow> x \<le> \<Squnion>X"
    by (transfer; force simp: fun_ord_def ord_option_Some1_iff ord_option_Some2_iff)+
  show "(\<And>y. y \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> x \<le> \<Sqinter>X"
    apply transfer
    apply (clarsimp simp: fun_ord_def ord_option.simps)
    subgoal premises P for X m x
      using P[rule_format, of _ x]
      by (cases "m x") fastforce+
    done
  show "(\<And>y. y \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> \<Squnion>X \<le> x"
    apply transfer
    apply (clarsimp simp: fun_ord_def ord_option.simps)
    subgoal premises P for X m x y z
      using P(1)[rule_format, of _ x] P(1)[rule_format, of y x] P(2,3)
      by auto force
    done
qed (transfer; auto)+
end

lemma states_sup[simp]: "states (\<phi> \<squnion> \<psi>) = states \<phi> \<union> states \<psi>"
  by transfer (auto simp: combine_options_def split: option.splits)

lemma states_SUP[simp]: "states (\<Squnion>A) = (\<Union>a\<in>A. states a)"
  by transfer (auto simp: dom_def split: option.splits if_splits)

lemma states_inf[simp]: "states (\<phi> \<sqinter> \<psi>) = states \<phi> \<inter> states \<psi>"
  by transfer (auto simp: lift_option_eq_Some split: option.splits)

lemma states_mono: "\<phi> \<le> \<psi> \<Longrightarrow> states \<phi> \<subseteq> states \<psi>"
  using states_sup[of \<phi> \<psi>] by (auto simp del: states_sup simp add: sup_absorb2)

lemma actions_sup[simp]: "actions (\<phi> \<squnion> \<psi>) = actions \<phi> \<squnion> actions \<psi>"
  by transfer (auto simp: combine_options_def split: option.splits)

lemma actions_SUP[simp]: "actions (\<Squnion>A) s = (\<Union>a\<in>A. actions a s)"
  by transfer (auto simp: dom_def split: option.splits if_splits, blast)

lemma actions_inf[simp]: "actions (\<phi> \<sqinter> \<psi>) = actions \<phi> \<sqinter> actions \<psi>"
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma actions_mono: assumes *: "\<phi> \<le> \<psi>" shows "actions \<phi> \<le> actions \<psi>"
proof -
  have "actions \<phi> \<le> actions \<phi> \<squnion> actions \<psi>"
    by auto
  also have "\<dots> = actions \<psi>"
    using * actions_sup[of \<phi> \<psi>] by (auto simp add: sup_absorb2)
  finally show ?thesis .
qed

lemma le_mdpcI: "states M \<subseteq> states N \<Longrightarrow> (\<And>s. s \<in> states M \<Longrightarrow> actions M s \<subseteq> actions N s) \<Longrightarrow> M \<le> N"
  by transfer
     (force simp: fun_ord_def ord_option.simps subset_eq split: option.splits)

lemma le_mdpc_iff: "M \<le> N \<longleftrightarrow> states M \<subseteq> states N \<and> (\<forall>s. actions M s \<subseteq> actions N s)"
  using states_mono[of M N] actions_mono[of M N] by (auto simp: le_fun_def intro!: le_mdpcI)

lemma map_actions_le: "(\<And>s A. s \<in> states \<phi> \<Longrightarrow> f s A \<subseteq> A) \<Longrightarrow> map_actions f \<phi> \<le> \<phi>"
  apply (intro le_mdpcI)
  subgoal by auto
  subgoal premises p for s using p(1)[of s] p(1)[of s "{}"] p(2) actions_map_actions by auto
  done

lemma restrict_states_mono: "A \<subseteq> B \<Longrightarrow> \<phi> \<le> \<psi> \<Longrightarrow> restrict_states A \<phi> \<le> restrict_states B \<psi>"
  using states_mono[of \<phi> \<psi>] actions_mono[of \<phi> \<psi>] by (intro le_mdpcI) (auto simp: le_fun_def)

lemma restrict_states_le: "restrict_states A M \<le> M"
  by (intro le_mdpcI) auto

lemma eq_bot_iff_states: "\<phi> = bot \<longleftrightarrow> states \<phi> = {}"
  by transfer auto

lemma fix_loop_neq_bot: "fix_loop s N \<noteq> bot"
  unfolding eq_bot_iff_states by simp

lemma
  shows states_bot[simp]: "states bot = {}"
    and actions_bot[simp]: "actions bot = (\<lambda>s. {})"
  unfolding fun_eq_iff by (transfer; auto)+

lemma inf_eq_bot_eq_disjnt_states: "A \<sqinter> B = bot \<longleftrightarrow> disjnt (states A) (states B)"
  unfolding disjnt_def by transfer  (auto simp: fun_eq_iff lift_option_eq_None)

text \<open>Enabled States\<close>
definition en :: "'s mdpc \<Rightarrow> 's rel"
  where "en \<phi> = {(s, t) | d s t. d \<in> actions \<phi> s \<and> t \<in> set_pmf d}"

lemma en_sup[simp]: "en (\<phi> \<squnion> \<psi>) = en \<phi> \<union> en \<psi>"
  by (auto simp: en_def)

lemma en_SUP[simp]: "en (Sup A) = (\<Union>a\<in>A. en a)"
  by (auto simp: en_def)

lemma en_mono: "\<phi> \<le> \<psi> \<Longrightarrow> en \<phi> \<subseteq> en \<psi>"
  unfolding en_def
  apply transfer
  apply (auto simp: fun_ord_def split: option.splits)
  subgoal for \<phi> \<psi> a b x y
    by (auto elim!: allE[of _ x] simp: ord_option.simps intro!: exI[of _ b] exI[of _ x])
  done

lemma en_states: "(s, t) \<in> en M \<Longrightarrow> s \<in> states M"
  using in_states[of M s] by (auto simp: en_def)

lemma en_bot[simp]: "en bot = {}"
  by (simp add: en_def)

lemma en_fix_loop[simp]: "en (fix_loop s M) = insert (s, s) (en M - {s} \<times> UNIV)"
  by (force simp add: en_def )

lift_definition trivial :: "'s \<Rightarrow> 's mdpc" is "\<lambda>s. (\<lambda>_. None)(s := Some {})" .

lemma states_trivial[simp]: "states (trivial s) = {s}"
  by transfer auto

lemma actions_trivial[simp]: "actions (trivial s) = (\<lambda>_. {})"
  by transfer (auto simp: fun_eq_iff)

lemma en_trivial[simp]: "en (trivial s) = {}"
  by (simp add: en_def)

lemma trivial_le_iff: "trivial x \<le> \<phi> \<longleftrightarrow> x \<in> states \<phi>"
  by transfer (auto simp: ord_option.simps fun_ord_def)

lemma trivial_le: "x \<in> states \<phi> \<Longrightarrow> trivial x \<le> \<phi>"
  unfolding trivial_le_iff .

lemma trivial_neq_bot: "trivial x \<noteq> bot"
  by transfer auto

lift_definition loop :: "'s \<Rightarrow> 's mdpc"
  is "\<lambda>s. (\<lambda>_. None)(s := Some {return_pmf s})" .

lemma states_loop[simp]: "states (loop s) = {s}"
  by transfer auto

lemma actions_loop: "actions (loop s) = ((\<lambda>_. {})(s := {return_pmf s}))"
  by transfer (auto simp: fun_eq_iff)

lemma
  shows actions_loop_self[simp]: "actions (loop s) s = {return_pmf s}"
    and actions_loop_neq[simp]: "s \<noteq> t \<Longrightarrow> actions (loop s) t = {}"
  by (simp_all add: actions_loop)

lemma en_loop[simp]: "en (loop s) = {(s, s)}"
  by (auto simp: en_def actions_loop)

lemma loop_neq_bot: "loop s \<noteq> bot"
  unfolding eq_bot_iff_states by simp

lemma loop_le: "loop x \<le> M \<longleftrightarrow> (x \<in> states M \<and> return_pmf x \<in> actions M x)"
  by (auto simp: le_mdpc_iff actions_loop)

lemma le_loop: "M \<le> loop x \<longleftrightarrow> (states M \<subseteq> {x} \<and> actions M x \<subseteq> {return_pmf x})"
  using in_states[of M] by (auto simp: le_mdpc_iff actions_loop)

text \<open>Strongly Connected (SC)\<close>
definition sc :: "'s mdpc \<Rightarrow> bool"
  where "sc \<phi> \<longleftrightarrow> states \<phi> \<times> states \<phi> \<subseteq> (en \<phi>)\<^sup>*"

lemma scD: "sc \<phi> \<Longrightarrow> x \<in> states \<phi> \<Longrightarrow> y \<in> states \<phi> \<Longrightarrow> (x, y) \<in> (en \<phi>)\<^sup>*"
  by (auto simp: sc_def)

lemma scI: "(\<And>x y. x \<in> states \<phi> \<Longrightarrow> y \<in> states \<phi> \<Longrightarrow> (x, y) \<in> (en \<phi>)\<^sup>*) \<Longrightarrow> sc \<phi>"
  by (auto simp: sc_def)

lemma sc_trivial[simp]: "sc (trivial s)"
  by (simp add: sc_def)

lemma sc_loop[simp]: "sc (loop s)"
  by (auto simp: sc_def)

lemma sc_bot[simp]: "sc bot"
  by (simp add: sc_def)

lemma sc_SupI_directed:
  assumes A: "\<And>a. a \<in> A \<Longrightarrow> sc a"
    and directed: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> \<exists>c\<in>A. a \<le> c \<and> b \<le> c"
  shows "sc (Sup A)"
  unfolding sc_def
proof clarsimp
  fix x y a b assume "a \<in> A" "b \<in> A" and xy: "x \<in> states a" "y \<in> states b"
  with directed obtain c where "c \<in> A" "a \<le> c" "b \<le> c"
    by auto
  with xy have "x \<in> states c" "y \<in> states c"
    using states_mono[of a c] states_mono[of b c] by auto
  with A[OF \<open>c \<in> A\<close>] \<open>c \<in> A\<close>
  have "(x, y) \<in> (en c)\<^sup>*"
    by (auto simp: sc_def subset_eq)
  then show "(x, y) \<in> (\<Union>x\<in>A. en x)\<^sup>*"
    using rtrancl_mono[of "en c" "\<Union>a\<in>A. en a"] \<open>c\<in>A\<close> by auto
qed

lemma sc_supI:
  assumes \<phi>: "sc \<phi>" and \<psi>: "sc \<psi>" and not_disjoint: "\<phi> \<sqinter> \<psi> \<noteq> bot"
  shows "sc (\<phi> \<squnion> \<psi>)"
  unfolding sc_def
proof safe
  fix x y assume "x \<in> states (\<phi> \<squnion> \<psi>)" "y \<in> states (\<phi> \<squnion> \<psi>)"
  moreover obtain z where "z \<in> states \<phi>" "z \<in> states \<psi>"
    using not_disjoint by (auto simp: inf_eq_bot_eq_disjnt_states disjnt_def)
  moreover have "(en \<phi>)\<^sup>* \<union> (en \<psi>)\<^sup>* \<subseteq> (en (\<phi> \<squnion> \<psi>))\<^sup>*"
    by (metis rtrancl_Un_subset en_sup)
  ultimately have "(x, z) \<in> (en (\<phi> \<squnion> \<psi>))\<^sup>*" "(z, y) \<in> (en (\<phi> \<squnion> \<psi>))\<^sup>*"
    using \<phi> \<psi> by (auto dest: scD)
  then show "(x, y) \<in> (en (\<phi> \<squnion> \<psi>))\<^sup>*"
    by auto
qed

lemma sc_eq_loop:
  assumes M: "sc M" and s: "s \<in> M" "actions M s = {return_pmf s}" shows "M = loop s"
proof -
  { fix t assume "t \<in> M"
    then have "(s, t) \<in> (en M)\<^sup>*"
      using M[THEN scD, OF \<open>s \<in> M\<close> \<open>t \<in> M\<close>] by simp
    from this have "t = s"
      by (induction rule: rtrancl_induct) (auto simp: en_def \<open>actions M s = {return_pmf s}\<close>) }
  then have "states M = {s}"
    using \<open>s \<in> M\<close> by blast
  then show ?thesis
    by (intro mdpc_eqI) (auto simp: \<open>actions M s = {return_pmf s}\<close>)
qed

lemma sc_eq_trivial:
  assumes M: "sc M" and s: "s \<in> M" "actions M s = {}" shows "M = trivial s"
proof -
  { fix t assume "t \<in> M" "t \<noteq> s"
    then have "(s, t) \<in> (en M)\<^sup>+"
      using M[THEN scD, OF \<open>s \<in> M\<close> \<open>t \<in> M\<close>] by (simp add: rtrancl_eq_or_trancl)
    from tranclD[OF this] \<open>actions M s = {}\<close> have False
      by (auto simp: en_def) }
  then have "states M = {s}"
    using \<open>s \<in> M\<close> by auto
  then show ?thesis
    by (intro mdpc_eqI) (auto simp: \<open>actions M s = {}\<close>)
qed

definition closed_mdpc :: "'s mdpc \<Rightarrow> bool"
  where "closed_mdpc \<phi> \<longleftrightarrow> en \<phi> \<subseteq> states \<phi> \<times> states \<phi>"

lemma closed_mdpcD: "closed_mdpc \<phi> \<Longrightarrow> D \<in> actions \<phi> x \<Longrightarrow> y \<in> D \<Longrightarrow> y \<in> states \<phi>"
  by (auto simp: closed_mdpc_def en_def)

lemma closed_mdpc_supI: "closed_mdpc \<phi> \<Longrightarrow> closed_mdpc \<psi> \<Longrightarrow> closed_mdpc (\<phi> \<squnion> \<psi>)"
  by (auto simp: closed_mdpc_def)

lemma closed_mdpc_SupI: "(\<And>a. a \<in> A \<Longrightarrow> closed_mdpc a) \<Longrightarrow> closed_mdpc (\<Squnion>A)"
  by (auto simp: closed_mdpc_def)

lemma closed_mdpc_infI: "closed_mdpc \<phi> \<Longrightarrow> closed_mdpc \<psi> \<Longrightarrow> closed_mdpc (\<phi> \<sqinter> \<psi>)"
  using en_mono[of "\<phi> \<sqinter> \<psi>" \<phi>] en_mono[of "\<phi> \<sqinter> \<psi>" \<psi>]
  by (auto simp: closed_mdpc_def lift_option_eq_Some)

lemma closed_mdpc_trivial[simp]: "closed_mdpc (trivial s)"
  by (simp add: closed_mdpc_def)

lemma closed_mdpc_bot[simp]: "closed_mdpc bot"
  by (simp add: closed_mdpc_def)

lemma closed_mdpc_loop[simp]: "closed_mdpc (loop s)"
  by (auto simp: closed_mdpc_def)

lemma closed_mdpc_fix_loop: "closed_mdpc M \<Longrightarrow> closed_mdpc (fix_loop s M)"
  by (auto simp: closed_mdpc_def)

lemma closed_mdpc_map: assumes M: "closed_mdpc M" shows "closed_mdpc (map_mdpc f M)"
  using closed_mdpcD[OF M]
  by (auto simp: closed_mdpc_def en_def actions_map_mdpc states_map_mdpc intro!: imageI intro: in_states)

definition close :: "'s mdpc \<Rightarrow> 's mdpc"
  where "close \<phi> = map_actions (\<lambda>s A. {a\<in>A. set_pmf a \<subseteq> states \<phi>}) \<phi>"

lemma
  shows states_close[simp]: "states (close \<phi>) = states \<phi>"
    and actions_close[simp]: "actions (close \<phi>) s = {a\<in>actions \<phi> s. a \<subseteq> states \<phi>}"
  by (auto simp: close_def)

lemma closed_close: "closed_mdpc (close \<phi>)"
  by (auto simp add: closed_mdpc_def en_def intro: in_states)

lemma close_closed: "closed_mdpc \<phi> \<Longrightarrow> close \<phi> = \<phi>"
  unfolding closed_mdpc_def by (intro mdpc_eqI) (auto simp: en_def)

lemma close_close: "close (close \<phi>) = close \<phi>"
  by (simp add: closed_close close_closed)

lemma close_le: "close M \<le> M"
  unfolding close_def by (intro map_actions_le) auto

lemma close_mono: "\<phi> \<le> \<psi> \<Longrightarrow> close \<phi> \<le> close \<psi>"
  using states_mono[of \<phi> \<psi>] actions_mono[of \<phi> \<psi>]
  unfolding close_def by (intro le_mdpcI) (auto simp: le_fun_def)

text \<open>End Component (EC)\<close>
definition ec :: "'s mdpc \<Rightarrow> bool"
  where "ec \<phi> \<longleftrightarrow> sc \<phi> \<and> closed_mdpc \<phi>"

lemma ec_trivial[simp]: "ec (trivial s)"
  by (auto simp: ec_def)

lemma ec_bot[simp]: "ec bot"
  by (auto simp: ec_def)

lemma ec_loop[simp]: "ec (loop s)"
  by (auto simp: ec_def)

lemma ec_sup: "ec \<phi> \<Longrightarrow> ec \<psi> \<Longrightarrow> \<phi> \<sqinter> \<psi> \<noteq> bot \<Longrightarrow> ec (\<phi> \<squnion> \<psi>)"
  by (simp add: ec_def sc_supI closed_mdpc_supI)

lemma ec_Sup_directed:
  "(\<And>a. a \<in> A \<Longrightarrow> ec a) \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> \<exists>c\<in>A. a \<le> c \<and> b \<le> c) \<Longrightarrow> ec (\<Squnion>A)"
  by (auto simp: ec_def closed_mdpc_SupI sc_SupI_directed)

text \<open>Maximal End Component (MEC) relative to @{term M}\<close>
definition mec :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> bool"
  where "mec M \<phi> \<longleftrightarrow> ec \<phi> \<and> \<phi> \<le> M \<and> (\<forall>\<psi>\<le>M. ec \<psi> \<longrightarrow> \<phi> \<le> \<psi> \<longrightarrow> \<phi> = \<psi>)"

lemma mec_refl: "ec M \<Longrightarrow> mec M M"
  by (auto simp: mec_def)

lemma mec_le: "mec M \<phi> \<Longrightarrow> \<phi> \<le> M"
  by (auto simp: mec_def)

lemma mec_ec: "mec M \<phi> \<Longrightarrow> ec \<phi>"
  by (auto simp: mec_def)

lemma mec_least: "mec M \<phi> \<Longrightarrow> \<psi> \<le> M \<Longrightarrow> \<phi> \<le> \<psi> \<Longrightarrow> ec \<psi> \<Longrightarrow> \<phi> \<ge> \<psi>"
  by (auto simp: mec_def)

lemma mec_bot_imp_bot: assumes "mec \<phi> bot" shows "\<phi> = bot"
proof (rule ccontr)
  assume "\<phi> \<noteq> bot"
  then obtain x where "x \<in> states \<phi>"
    unfolding eq_bot_iff_states by auto
  then have "ec (trivial x)" "trivial x \<le> \<phi>"
    by (auto intro: trivial_le)
  then have "trivial x = bot"
    using \<open>mec \<phi> bot\<close> by (auto simp: mec_def)
  then show False
    by (simp add: trivial_neq_bot)
qed

lemma mec_imp_bot_eq_bot: "mec \<phi> \<psi> \<Longrightarrow> \<phi> = bot \<longleftrightarrow> \<psi> = bot"
  using mec_bot_imp_bot[of \<phi>] by (auto simp: mec_def)

lemma mec_unique: assumes \<phi>: "mec M \<phi>" and \<psi>: "mec M \<psi>" and "\<phi> \<sqinter> \<psi> \<noteq> bot" shows "\<phi> = \<psi>"
proof -
  have "mec M (\<phi> \<squnion> \<psi>)"
    using assms
    by (auto intro!: mec_def[THEN iffD2] ec_sup antisym dest: mec_ec mec_le)
       (blast intro: le_supI1 mec_least[of M])
  with mec_least[OF \<phi>, of "\<phi> \<squnion> \<psi>"] mec_least[OF \<psi>,  of "\<phi> \<squnion> \<psi>"] mec_le[OF this] mec_ec[OF this]
  show "\<phi> = \<psi>"
    by auto
qed

lemma mec_exists: assumes \<phi>: "\<phi> \<noteq> bot" "ec \<phi>" and M: "\<phi> \<le> M" shows "\<exists>\<psi>\<ge>\<phi>. mec M \<psi>"
proof (intro exI conjI)
  show "\<phi> \<le> \<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>}"
    using \<phi> M by (intro Sup_upper) auto
  show "mec M (\<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>})"
    unfolding mec_def
  proof safe
    show "ec (\<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>})"
    proof (safe intro!: ec_Sup_directed)
      fix a b assume *: "\<phi> \<le> a" "\<phi> \<le> b" and "a \<le> M" "b \<le> M" "ec a" "ec b"
      moreover have "a \<sqinter> b \<noteq> bot"
        using * \<phi> bot_unique[of "\<phi>"] le_inf_iff[of \<phi> a b] by (auto simp del: inf.bounded_iff)
      ultimately show "\<exists>c\<in>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>}. a \<le> c \<and> b \<le> c"
        by (intro bexI[of _ "sup a b"]) (auto intro: le_supI1 intro!: ec_sup)
    qed
    fix \<psi> assume \<psi>: "\<psi> \<le> M" "ec \<psi>" "\<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>} \<le> \<psi>"
    have "\<phi> \<le> \<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>}"
      using assms by (auto intro!: Sup_upper)
    also have "\<dots> \<le> \<psi>" by fact
    finally show "\<Squnion>{\<psi>. \<phi> \<le> \<psi> \<and> \<psi> \<le> M \<and> ec \<psi>} = \<psi>"
      using \<psi> by (intro antisym Sup_upper) auto
  qed (auto intro!: Sup_least)
qed

lemma mec_exists': "x \<in> states M \<Longrightarrow> \<exists>\<psi>. x \<in> states \<psi> \<and> mec M \<psi>"
  using mec_exists[of "trivial x"] by (auto simp: trivial_neq_bot trivial_le_iff)

lemma mec_loop: "x \<in> states M \<Longrightarrow> actions M x = {return_pmf x} \<Longrightarrow> mec M (loop x)"
  apply (auto simp: mec_def loop_le ec_def)
  subgoal for \<phi>
    using sc_eq_loop[of \<phi> x] actions_mono[of \<phi> M, THEN le_funD, of x] by auto
  done

lemma mec_fix_loop: "mec (fix_loop s M) (loop s)"
  by (intro mec_loop) auto

definition trivials :: "'s mdpc \<Rightarrow> 's set"
  where "trivials M = {x. mec M (trivial x)}"

lemma trivials_subset_states: "trivials M \<subseteq> states M"
  by (auto simp: trivials_def mec_def trivial_le_iff)

text \<open>Bottom MEC (BEMC) in @{term M}\<close>
definition bmec :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> bool"
  where "bmec M \<phi> \<longleftrightarrow> mec \<phi> M \<and> (\<forall>s\<in>states \<phi>. actions \<phi> s = actions M s)"

definition actions' :: "'s mdpc \<Rightarrow> 's \<Rightarrow> 's pmf set"
  where "actions' M s = (if s \<in> states M then actions M s else {return_pmf s})"

lemma closed_mdpcD':
  "closed_mdpc M \<Longrightarrow> s \<in> states M \<Longrightarrow> (\<Union>D\<in>actions' M s. set_pmf D) \<subseteq> states M"
  by (auto simp: actions'_def dest: closed_mdpcD)

locale Finite_MDP =
  fixes M :: "'s mdpc"
  assumes closed_M: "closed_mdpc M" and M_neq_bot: "M \<noteq> bot"
    and actions_neq_empty_M: "\<And>s. s \<in> states M \<Longrightarrow> actions M s \<noteq> {}"
    and finite_states_M: "finite M"
    and finite_actions_M: "\<And>s. finite (actions M s)"
begin

sublocale Finite_Markov_Decision_Process "actions' M" "states M"
proof
  show "actions' M s \<noteq> {}" for s
    using actions_neq_empty_M by (auto simp: actions'_def )
  show "states M \<noteq> {}" "finite M" "\<And>s. finite (actions' M s)"
    using M_neq_bot finite_states_M finite_actions_M by (auto simp: eq_bot_iff_states actions'_def)
  show "s \<in> states M \<Longrightarrow> (\<Union>D\<in>actions' M s. set_pmf D) \<subseteq> states M" for s
    using closed_M by (rule closed_mdpcD')
qed

lemma Finite_MDP_map_loop: "Finite_MDP (map_mdpc f M \<squnion> loop s)"
proof
  show "closed_mdpc (map_mdpc f M \<squnion> loop s)"
    by (intro closed_mdpc_supI closed_mdpc_map closed_M closed_mdpc_loop)
  show "finite (actions (map_mdpc f M \<squnion> loop s) t)" for t
    by (auto simp: actions_loop intro!: finite_actions_map finite_states_M finite_actions_M)
  show "finite (map_mdpc f M \<squnion> loop s)"
    by (auto intro!: finite_states_M finite_states_map)
qed (auto simp: loop_neq_bot states_map_mdpc actions_loop actions_map_mdpc dest: actions_neq_empty_M)

lemma Finite_MDP_map_fix_loop: "Finite_MDP (fix_loop s (map_mdpc f M))"
proof
  show "closed_mdpc (fix_loop s (map_mdpc f M))"
    by (intro closed_mdpc_supI closed_mdpc_map closed_M closed_mdpc_fix_loop)
  show "finite (actions (fix_loop s (map_mdpc f M)) t)" for t
    by (auto simp: actions_loop intro!: finite_actions_map finite_states_M finite_actions_M)
  show "finite (fix_loop s (map_mdpc f M))"
    by (auto intro!: finite_states_M finite_states_map)
qed (auto simp: fix_loop_neq_bot states_map_mdpc actions_map_mdpc dest: actions_neq_empty_M)

end

context
  fixes M :: "'s mdpc"
    and F :: "'s set"
  assumes M_neq_bot: "M \<noteq> bot"
    and closed_M: "closed_mdpc M"
    and actions_neq_empty_M: "\<And>s. s \<in> states M \<Longrightarrow> actions M s \<noteq> {}"
    and finite_states_M: "finite M"
    and finite_actions_M: "\<And>s. finite (actions M s)"
    and F_subset: "F \<subseteq> states M"
begin

lemma finite_F[simp]: "finite F"
  using F_subset finite_states_M by (auto dest: finite_subset)

interpretation M: Finite_MDP M
  proof qed fact+

interpretation M: Reachability_Problem "actions' M" "states M" "states M - F" F
  proof qed (insert F_subset, auto)

definition r :: "'s \<Rightarrow> 's option"
  where "r s = (if s \<in> F then None else Some s)"

lemma r_eq_None[simp]: "r s = None \<longleftrightarrow> s \<in> F"
  by (simp add: r_def)

lemma r_eq_Some[simp]: "r s = Some t \<longleftrightarrow> (s \<notin> F \<and> s = t)"
  by (simp add: r_def)

lemma r_in_Some_image: "r s \<in> Some ` X \<longleftrightarrow> (s \<notin> F \<and> s \<in> X)"
  by (auto simp: r_def)

lemma r_inj: "s \<notin> F \<or> t \<notin> F \<Longrightarrow> r s = r t \<longleftrightarrow> s = t"
  by (auto simp: r_def)

lemma shows r_F: "s \<in> F \<Longrightarrow> r s = None" and r_nF: "s \<notin> F \<Longrightarrow> r s = Some s"
  by auto

definition R :: "'s option mdpc"
  where "R = fix_loop None (map_mdpc r M)"

lemma closed_R: "closed_mdpc R"
  unfolding R_def by (intro closed_mdpc_map closed_M closed_mdpc_fix_loop)

lemma states_R[simp]: "states R = Some ` (states M - F) \<union> {None}"
  by (auto simp add: R_def r_def[abs_def] states_map_mdpc)

lemma actions_R_None[simp]:
  "actions R None = {return_pmf None}"
  by (auto simp add: R_def)

lemma actions_R_Some[simp]:
  "actions R (Some s) = (if s \<in> F then {} else map_pmf r ` actions M s)"
  by (auto simp add: R_def actions_map_mdpc split: if_splits intro!: imageI)

lemma mec_R_loop: "mec R (loop None)"
  unfolding R_def by (intro mec_fix_loop)

interpretation R: Finite_MDP R
  unfolding R_def by (rule M.Finite_MDP_map_fix_loop)

interpretation R: Reachability_Problem "actions' R" "states R" "{None}" "{}"
  proof qed auto

lemma F_not_trivial: "s \<in> F \<Longrightarrow> Some s \<notin> trivials R"
  by (auto simp: trivials_def mec_def trivial_le_iff)

primrec min_state :: "'s option \<Rightarrow> 's + bool"
  where
    "min_state None = Inr True"
  | "min_state (Some s) = (if Some s \<in> trivials R then Inl s else Inr False)"

lemma min_state_eq_Inl: "min_state s = Inl t \<longleftrightarrow> (Some t \<in> trivials R \<and> s = Some t)"
  by (cases s) auto

lemma min_state_eq_Inr: "min_state s = Inr b \<longleftrightarrow> (if b then s = None else s \<noteq> None \<and> s \<notin> trivials R)"
  by (cases s) auto

lemma map_min_state_R: "map_mdpc min_state R = fix_loop (Inr True) (map_mdpc (min_state \<circ> r) M)"
  unfolding R_def
  by (subst map_fix_loop)
     (auto simp: map_mdpc_compose min_state_eq_Inr eq_commute[of "Inr True"])

definition min_mdpc :: "('s + bool) mdpc"
  where "min_mdpc = fix_loop (Inr False) (map_mdpc min_state R)"

lemma states_min_mdpc: "states min_mdpc = {Inl t | t. Some t \<in> trivials R} \<union> {Inr True, Inr False}"
  using trivials_subset_states[of R] by (auto simp add: min_mdpc_def states_map_mdpc image_comp split: if_splits)

lemma actions_min_mdpc_Inl:
  "actions min_mdpc (Inl t) = (if Some t \<in> trivials R then map_pmf (min_state \<circ> r) ` actions M t else {})"
proof -
  have eq: "min_state -` {Inl t} = (if Some t \<in> trivials R then {Some t} else {})"
    by (auto simp: min_state_eq_Inl)
  show ?thesis using F_not_trivial[of t]
    by (simp add: min_mdpc_def actions_map_mdpc eq image_comp map_pmf_compose[symmetric])
qed

lemma actions_min_mdpc_Inr: "actions min_mdpc (Inr b) = {return_pmf (Inr b)}"
  by (simp add: min_mdpc_def map_min_state_R)

interpretation min: Finite_MDP min_mdpc
  unfolding min_mdpc_def by (rule R.Finite_MDP_map_fix_loop)

interpretation min: Reachability_Problem "actions' min_mdpc" "states min_mdpc" "states min_mdpc - {Inr True}" "{Inr True}"
  proof qed (auto simp: states_min_mdpc)

lemma M_n_eq_0_not_trivials:
  assumes "s \<in> states M" "s \<notin> F" "Some s \<notin> trivials R"
  shows "M.n s = 0"
proof -
  have "Some s \<in> states R"
    using assms by auto

  obtain \<phi> where "mec R \<phi>" "s \<in> Some -` \<phi>"
    using mec_exists'[OF \<open>Some s \<in> states R\<close>] by auto
  then have action_\<phi>: "Some t \<in> \<phi> \<Longrightarrow> actions \<phi> (Some t) \<noteq> {}" for t
    using mec_ec[OF \<open>mec R \<phi>\<close>] \<open>Some s \<notin> trivials R\<close> sc_eq_trivial[of \<phi> "Some t"]
    by (auto simp: ec_def trivials_def)

  have None_notin_states: "None \<notin> states \<phi>"
    using mec_R_loop \<open>mec R \<phi>\<close> \<open>s \<in> Some -` \<phi>\<close> mec_unique[of R "loop None" \<phi>]
    by (auto simp: inf_eq_bot_eq_disjnt_states disjnt_def)

  from \<open>s \<in> Some -` \<phi>\<close> show "M.n s = 0"
  proof (rule M.n_eq_0_closed)
    show "Some -` states \<phi> \<subseteq> states M" "Some -` states \<phi> \<inter> F = {}"
      using mec_le[OF \<open>mec R \<phi>\<close>] by (auto simp: r_def le_mdpc_iff)
    fix s assume "s \<in> Some -` \<phi>"
    then have s: "s \<in> states M" "s \<notin> F" "actions \<phi> (Some s) \<noteq> {}"
      using mec_le[OF \<open>mec R \<phi>\<close>] by (auto simp: le_mdpc_iff action_\<phi>)
    then obtain D where D: "D \<in> actions \<phi> (Some s)"
      by auto
    then have "D \<in> actions R (Some s)"
      using mec_le[OF \<open>mec R \<phi>\<close>, THEN actions_mono] s by (auto simp add: le_fun_def simp del: actions_R_Some)
    with s obtain D' where D_eq: "D = map_pmf r D'" and D': "D' \<in> actions M s"
      by auto
    have "set_pmf D \<subseteq> states \<phi>"
      using closed_mdpcD[OF _ D] mec_ec[OF \<open>mec R \<phi>\<close>] by (auto simp: ec_def)
    then have "set_pmf D = Some ` set_pmf D'"
      using closed_mdpcD[of \<phi>, OF _ \<open>D \<in> actions \<phi> (Some s)\<close>] None_notin_states
        mec_ec[OF \<open>mec R \<phi>\<close>]
      unfolding D_eq by (auto intro!: image_cong simp: r_def ec_def)
    then show "\<exists>x\<in>actions' M s. set_pmf x \<subseteq> Some -` states \<phi>"
      using \<open>s \<in> states M\<close> \<open>set_pmf D \<subseteq> states \<phi>\<close> D'
      by (intro bexI[of _ D']) (auto simp: actions'_def)
  qed
qed

lemma min_state_r_in_min_mdpc[simp]: "s \<in> M \<Longrightarrow> min_state (r s) \<in> min_mdpc"
  by (auto simp add: states_min_mdpc min_state_eq_Inr min_state_eq_Inl r_def)

end

end
