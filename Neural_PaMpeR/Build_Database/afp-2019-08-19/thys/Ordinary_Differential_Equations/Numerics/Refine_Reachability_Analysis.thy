theory Refine_Reachability_Analysis
  imports
    Abstract_Reachability_Analysis
    Refine_Rigorous_Numerics
begin

lemma isDERIV_simps[simp]:
  "isDERIV i 1 xs" "isDERIV i 0 xs"
  "isDERIV i (a + b) xs \<longleftrightarrow>  isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a - b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a * b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs"
  "isDERIV i (a / b) xs \<longleftrightarrow> isDERIV i a xs \<and> isDERIV i b xs \<and> interpret_floatarith b xs \<noteq> 0"
  "isDERIV i (-a) xs = isDERIV i a xs"
  by (auto simp: one_floatarith_def zero_floatarith_def plus_floatarith_def minus_floatarith_def
      times_floatarith_def divide_floatarith_def uminus_floatarith_def)

lemma list_of_eucl_of_env:
  assumes [simp]: "length xs = DIM('a)"
  shows "(list_of_eucl (eucl_of_env xs vs::'a)) = (map (\<lambda>i. vs ! (xs ! i)) [0..<DIM('a::executable_euclidean_space)])"
  by (auto intro!: nth_equalityI simp: eucl_of_env_def eucl_of_list_inner)

context approximate_sets_ode
begin

lemma interpret_ode_fa[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)" "length vs \<ge> DIM('a)" "length ode_e = DIM('a)"
    and mV:  "max_Var_floatariths ode_e \<le> DIM('a)"
  shows "(eucl_of_list (interpret_floatariths (ode_fa xs) vs)::'a) = ode (eucl_of_list (interpret_floatariths xs vs))"
  unfolding ode_fa_def
  apply (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner ode_def)
  apply (subst interpret_floatarith_subst_floatarith[where D="length vs"])
   apply (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nth[le]
      mV[le])
  apply (rule interpret_floatarith_max_Var_cong)
  apply (drule max_Var_floatariths_lessI) apply simp
  apply (drule less_le_trans[OF _ mV])
  apply auto
  apply (subst nth_map)
   apply simp  using assms(2) order.strict_trans2 apply blast
  apply (subst nth_upt) apply simp
   apply (rule less_le_trans, assumption, simp)
  apply auto
  done

lemma length_ode_fa[simp]: "length (ode_fa xs) = length ode_e"
  by (auto simp: ode_fa_def)

lemma max_Var_ode_fa[le]:
  assumes "max_Var_floatariths ode_e \<le> length xs"
  shows "max_Var_floatariths (ode_fa xs) \<le> max_Var_floatariths xs"
  by (auto simp: ode_fa_def intro!: assms max_Var_floatariths_subst_floatarith_le)

lemma max_Var_floatariths_ode_d_expr[le]:
  "max_Var_floatariths ode_e \<le> d \<Longrightarrow> d > 0 \<Longrightarrow>
    max_Var_floatariths (ode_d_expr d m) \<le> 3 * d"
  by (auto simp: ode_d_expr_def
      intro!: max_Var_floatarith_FDERIV_n_floatariths[le]
        max_Var_floatarith_FDERIV_floatariths[le])

lemma interpret_ode_d_fa:
  assumes FDERIV: "(eucl_of_list (interpret_floatariths xs vs)::'a::executable_euclidean_space) \<in> Csafe"
  assumes [simp]: "length ds = DIM('a)" "length xs = DIM('a)"
  notes [simp] = safe_length[OF FDERIV]
  shows "(eucl_of_list (interpret_floatariths (ode_d_fa n xs ds) vs)::'a) =
      ode_d n (eucl_of_list (interpret_floatariths xs vs)) (eucl_of_list (interpret_floatariths ds vs))
        (eucl_of_list (interpret_floatariths ds vs))"
  apply (transfer fixing: xs ds vs n)
  using FDERIV apply (auto simp del: isnFDERIV.simps simp: interpret_floatariths_append)
  apply (auto simp add: list_of_eucl_of_env ode_def
      ode_d_raw_def eucl_of_list_inner
      intro!: euclidean_eqI[where 'a='a])
  apply (auto simp: ode_d_fa_def )
  apply (subst interpret_floatarith_subst_floatarith[OF max_Var_floatarith_le_max_Var_floatariths_nth], simp)
  apply (rule interpret_floatarith_max_Var_cong)
  subgoal premises prems for b i
  proof -
    from prems have i: "i < max_Var_floatariths (ode_d_expr DIM('a) n)"
      by (auto dest!: max_Var_floatariths_lessI)
    also have "\<dots> \<le> 3 * DIM('a)"
      by (auto intro!: max_Var_floatariths_ode_d_expr safe_max_Var[OF FDERIV])
    finally have "i < 3 * DIM('a)" .
    then show ?thesis
      using prems i
      by (auto simp: nth_append)
  qed
  done

lemma safe_at_within: "x \<in> Csafe \<Longrightarrow> at x = at x within Csafe"
  by (subst (2) at_within_open)  (auto simp: open_safe)

lemma ivlflowsD:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> \<Union>(plane_of ` stops) \<times> UNIV "
  shows "ivl \<subseteq> (snd (stopcont ivl))"
    "(fst (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "fst (stopcont ivl) \<subseteq> snd (stopcont ivl)"
    "(snd (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV"
    "flowsto (ivl) {0..} ((snd (stopcont ivl))) ((fst (stopcont ivl)) \<union> trap)"
  using assms(1)[unfolded ivlflows_def, rule_format, OF assms(2)]
  by auto

lemma ivlflows_flowsto:
  assumes "ivlflows stops stopcont trap rsctn" "ivl \<subseteq> \<Union>(plane_of ` stops) \<times> UNIV"
  assumes "stopcont ivl = (x, y)"
  shows "flowsto (ivl) {0..} y (x \<union> trap)"
  using ivlflowsD[OF assms(1,2)] assms(3)
  by auto

lemma ivlflows_emptyI: "ivlflows {} (\<lambda>x. (x, x)) J K"
  by (auto simp: ivlflows_def set_of_ivl_def)

lemma plane_of_neg[simp]: "plane_of (Sctn (- normal sctn) (- pstn sctn)) = plane_of sctn"
  by (auto simp: plane_of_def)

lemmas safe_max_Var_le[intro] = safe_max_Var[le]

lemmas [simp] = safe_length

lemma continuous_on_ode_d2: "continuous_on (Csafe) ode_d2"
proof -
  have isn: "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl x @ list_of_eucl i)
                 (Suc (Suc 0))"
    if "x \<in> Csafe"
    for x i::'a
    by (rule safe_isnFDERIV) fact
  have "continuous_on (Csafe::'a set) (\<lambda>x. ode_d_raw (Suc 0) x i j)"
     if "i \<in> Basis" "j \<in> Basis" for i j
    apply (rule has_derivative_continuous_on)
    apply (auto simp: ode_d_raw_def at_within_open[OF _ open_safe])
     apply (rule interpret_floatarith_FDERIV_floatariths_append)
    apply (auto simp: ode_d_expr_def 
        intro!: isDERIV_FDERIV_floatariths safe_isFDERIV_append that isFDERIV_map_Var
        safe_max_Var_le
        max_Var_floatarith_FDERIV_floatariths[le])
     apply assumption
    apply arith
    done
  then show ?thesis
    apply (auto intro!: continuous_on_blinfun_componentwise)
    subgoal for i j
    apply (rule continuous_on_eq[where f="(\<lambda>x. ode_d_raw (Suc 0) x i j)"])
       apply force
      apply (subst ode_d2.rep_eq)
      apply simp
      apply (subst ode_d.rep_eq)
      apply (split if_splits)
      apply (rule conjI) apply simp
      using isn apply force
      done
    done
qed

lemmas continuous_on_ode_d2_comp[continuous_intros] = continuous_on_compose2[OF continuous_on_ode_d2]


lemma map_ode_fa_nth[simp]:
  "d \<le> length ode_e \<Longrightarrow> map (ode_fa_nth CX) [0..<d] = map ((!) (ode_fa CX)) [0..<d]"
  by (auto simp: ode_fa_nth cong: map_cong)

lemma map_ode_d_fa_nth[simp]:
  "d \<le> length ode_e \<Longrightarrow> map (ode_d_fa_nth i CX X) [0..<d] = map ((!) (ode_d_fa i CX X)) [0..<d]"
  by (auto simp: ode_d_fa_nth cong: map_cong)

lemma einterpret_euler_incr_fas:
  assumes "length ode_e = DIM('a)" "length X0 = DIM('a)" "length CX = DIM('a)"
    "DIM('a) \<le> length vs" "max_Var_floatariths ode_e \<le> DIM('a)"
  shows "(einterpret (euler_incr_fas X0 h CX) vs::'a::executable_euclidean_space) =
    einterpret X0 vs + (interpret_floatarith h vs) *\<^sub>R ode (einterpret CX vs)"
  by (simp add: euler_incr_fas_def euler_incr_fas_nth_def assms ode_fa_nth cong: map_cong)

lemma einterpret_euler_err_fas:
  assumes safe: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (euler_err_fas X0 h CX) vs::'a::executable_euclidean_space) =
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  using safe_length[OF safe] safe_max_Var[OF safe]
  apply (simp add: euler_err_fas_def euler_err_fas_nth_def[abs_def] euler_incr_fas_def)
  apply (subst interpret_ode_d_fa)
  by (auto simp: safe)

lemma einterpret_euler_fas1:
  assumes safe[simp]: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (take DIM('a) (euler_fas X0 h CX)) vs::'a::executable_euclidean_space) =
    einterpret X0 vs + (interpret_floatarith h vs) *\<^sub>R ode (einterpret X0 vs) +
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  using safe_length[OF safe] safe_max_Var[OF safe]
  by (simp add: euler_fas_def euler_incr_fas_def euler_incr_fas_nth_def[abs_def]
      einterpret_euler_err_fas euler_err_fas_nth_def[abs_def] interpret_ode_d_fa)

lemma einterpret_euler_fas2:
  assumes [simp]: "(einterpret CX vs::'a) \<in> Csafe"
  assumes [simp]: "length X0 = DIM('a)" "length CX = DIM('a)" "DIM('a) \<le> length vs"
  shows "(einterpret (drop DIM('a) (euler_fas  X0 h CX)) vs::'a::executable_euclidean_space) =
    (((interpret_floatarith h vs))\<^sup>2/2) *\<^sub>R ode_d 0 (einterpret CX vs) (ode (einterpret CX vs)) (ode (einterpret CX vs))"
  by (simp add: euler_fas_def euler_incr_fas_def einterpret_euler_err_fas)

lemma ode_d_Suc_0_eq_ode_d2: "x \<in> Csafe \<Longrightarrow> ode_d (Suc 0) x = ode_d2 x"
  unfolding ode_d2.rep_eq by auto

lemma rk2_increment_rk2_fas_err:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "x0' \<in> Csafe" "cx' \<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0')\<in> Csafe"
  shows "(einterpret (rk2_fas_err rkp x0 h cx s2) vs::'a::executable_euclidean_space) =
    heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na     ode_d2_na 0 h' s2'"
  using safes
  using safe_length[OF safes(1)] safe_max_Var[OF safes(1)]
  apply (auto simp: heun_remainder1_def heun_remainder2_def discrete_evolution_def
      ode_na_def ode_d_na_def ode_d2_na_def rk2_increment x0'_def rkp'_def h'_def s2'_def
      cx'_def euler_incr_fas_def rk2_fas_err_def rk2_fas_err_nth_def[abs_def]
        euler_incr_fas_nth_def[abs_def]
        interpret_ode_d_fa)
  apply (simp add: ode_d1_eq[symmetric] ode_d_Suc_0_eq_ode_d2 inverse_eq_divide)
  apply (simp add: algebra_simps field_simps divide_simps)
  unfolding cx'_def[symmetric] cx_flow x0'_def h'_def
  apply (simp add: algebra_simps)
  done

lemma map_rk2_fas_err_nth[simp]:
  "d = length ode_e \<Longrightarrow> length b = length ode_e \<Longrightarrow> map (rk2_fas_err_nth a b c e f) [0..<d] = map ((!) (rk2_fas_err a b c e f)) [0..<d]"
  unfolding rk2_fas_err_nth_def rk2_fas_err_def
  by (rule map_cong) auto

lemma rk2_increment_rk2_fas1:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "(x0'::'a)\<in> Csafe" "(cx'::'a)\<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0'::'a)\<in> Csafe"
  shows "(einterpret (take DIM('a) (rk2_fas rkp x0 h cx s2)) vs::'a::executable_euclidean_space) =
    discrete_evolution (rk2_increment rkp' (\<lambda>_. ode)) h' 0 x0' + (heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na ode_d2_na 0 h' s2')"
  using safes  using safe_length[OF safes(1)] safe_max_Var[OF safes(1)]
  apply (auto simp: discrete_evolution_def rk2_fas_def)
  apply (subst rk2_increment_rk2_fas_err[OF cx_flow[unfolded cx'_def x0'_def h'_def]])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: x0'_def)
  subgoal by (simp add: cx'_def)
  subgoal by (simp add: x0'_def s2'_def h'_def rkp'_def)
  subgoal using [[show_consts, show_sorts, show_types]]
    by (auto simp: x0'_def s2'_def h'_def rkp'_def rk2_increment euler_incr_fas_def
        euler_incr_fas_nth_def[abs_def] inverse_eq_divide)
  done

lemma rk2_increment_rk2_fas2:
  fixes h s1 s2 rkp x0 cx vs
  defines "h' \<equiv> interpret_floatarith h vs"
  defines "s2' \<equiv> interpret_floatarith s2 vs"
  defines "rkp' \<equiv> interpret_floatarith rkp vs"
  defines "x0' \<equiv> einterpret x0 vs"
  defines "cx' \<equiv> einterpret cx vs"
  assumes cx_flow: "cx' = flow0 x0' (h' * s1')"
  assumes [simp]: "length x0 = DIM('a)" "length cx = DIM('a)" "DIM('a) \<le> length vs"
  assumes safes: "x0'\<in> Csafe" "cx'\<in> Csafe" "(x0' + (s2' * h' * rkp') *\<^sub>R ode x0')\<in> Csafe"
  shows "(einterpret (drop DIM('a) (rk2_fas rkp x0 h cx s2)) vs::'a::executable_euclidean_space) =
    (heun_remainder1 (flow0 x0') ode_na ode_d_na ode_d2_na 0 h' s1' -
    heun_remainder2 rkp' (flow0 x0') ode_na      ode_d2_na 0 h' s2')"
  using safes
  apply (auto simp: discrete_evolution_def rk2_fas_def)
  apply (subst rk2_increment_rk2_fas_err[OF cx_flow[unfolded cx'_def x0'_def h'_def]])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: x0'_def)
  subgoal by (simp add: cx'_def)
  subgoal by (simp add: x0'_def s2'_def h'_def rkp'_def)
  subgoal by (auto simp: x0'_def s2'_def h'_def rkp'_def rk2_increment euler_incr_fas_def inverse_eq_divide)
  done

subsubsection \<open>safe set relation\<close>

lemma mk_safe[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space)\<Longrightarrow>
  mk_safe X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_def
  by refine_vcg

lemma mk_safe_coll[le, refine_vcg]: "wd TYPE('a::executable_euclidean_space) \<Longrightarrow>
    mk_safe_coll X \<le> SPEC (\<lambda>R::'a set. R = X \<and> X \<subseteq> Csafe)"
  unfolding mk_safe_coll_def autoref_tag_defs
  by (refine_vcg FORWEAK_invarI[where I="\<lambda>a b. X = \<Union>b \<union> a \<and> a \<subseteq> Csafe"]) auto


lemma ode_set_spec[THEN order.trans, refine_vcg]:
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "ode_set X \<le> SPEC (\<lambda>r. ode ` X \<subseteq> (r::'a set))"
  using assms wdD[OF assms(1)]
  unfolding ode_set_def
  apply (refine_vcg)
  subgoal by (auto simp: env_len_def ode_slp_def)
  subgoal premises prems
    using prems(1,2,4-)
    by (auto simp: env_len_def eucl_of_list_prod ode_def)
  done

lemmas fderiv[derivative_intros] = ode_has_derivative_safeI

lemma fderiv2[derivative_intros]:
  "x \<in> Csafe \<Longrightarrow> (ode_d1 has_derivative ode_d2 x) (at x)"
  by (frule ode_d1_has_derivative_safeI)
    (simp add: ode_d_Suc_0_eq_ode_d2)

lemma derivative_within_safe[derivative_intros]:
  "(g has_derivative h) (at x) \<Longrightarrow> (g has_derivative h) (at x within Csafe)"
  by (rule has_derivative_at_withinI)

lemma cont_fderiv: "continuous_on (Csafe) ode_d1"
  by (rule has_derivative_continuous_on) (auto intro!: derivative_intros)

lemmas cont_fderiv'[continuous_intros] = continuous_on_compose2[OF cont_fderiv]

lemma continuous_on_ode1:
  "continuous_on (Csafe) (ode)"
  using fderiv
  by (auto intro!: has_derivative_continuous_on derivative_intros)

lemma continuous_on_ode[continuous_intros]:
  "continuous_on s g \<Longrightarrow> (\<And>x. x \<in> s \<Longrightarrow> (g x) \<in> Csafe) \<Longrightarrow> continuous_on s (\<lambda>x. ode (g x))"
  using continuous_on_ode1
  by (rule continuous_on_compose2) auto

lemma fderiv'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "(g y) \<in> Csafe"
  shows "((\<lambda>y. ode (g y)) has_derivative
    (blinfun_apply (ode_d1 (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv]] assms(2)
  by (simp add: o_def)

lemma fderiv2'[derivative_intros]:
  assumes "(g has_derivative g' y) (at y within X)"
  assumes "(g y) \<in> Csafe"
  shows "((\<lambda>y. ode_d1 (g y)) has_derivative
    (blinfun_apply (ode_d2 (g y)) \<circ>\<circ> g') y) (at y within X)"
  using diff_chain_within[OF assms(1) has_derivative_within_subset[OF fderiv2]] assms(2)
  by (simp add: o_def)


subsubsection \<open>step of Picard iteration\<close>

lemma ncc_interval: "ncc {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: ncc_def)
lemma nonempty_interval: "nonempty {a .. b::'a::executable_euclidean_space} \<longleftrightarrow> a \<le> b"
  by (auto simp: nonempty_def)

lemmas [refine_vcg] = Picard_step_def[THEN eq_refl, THEN order.trans]

lemma Basis_list_zero_mem_Basis[simp]:
  "Basis_list ! 0 \<in> Basis"
  unfolding Basis_list[symmetric]
  apply (rule nth_mem)
  apply (rule length_Basis_list_pos)
  done

lemma cfuncset_empty_iff:
  fixes l u::"'d::ordered_euclidean_space"
  shows "l \<le> u \<Longrightarrow> cfuncset l u X = {} \<longleftrightarrow> X = {}"
  unfolding cfuncset_def Pi_def
proof (safe, goal_cases)
  case hyps: (1 x)
  from \<open>x \<in> X\<close>
  have "(\<lambda>_. x) \<in> {f. \<forall>x. x \<in> {l..u} \<longrightarrow> f x \<in> X} \<inter> Collect (continuous_on {l..u})"
    by (auto intro!: continuous_on_const)
  then show ?case using hyps by auto
qed auto

lemma lv_ivl_sings: "lv_ivl [x] [y] = (\<lambda>x. [x]) ` {x .. y}"
  apply (auto simp: lv_ivl_def)
  subgoal for x by (cases x) auto
  done

lemma Picard_step_ivl_refine[le, refine_vcg]:
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  assumes "(X::'a set) \<subseteq> Csafe"
  assumes "0 \<le> h"
  shows "Picard_step_ivl X0 t0 h X \<le> Picard_step X0 t0 h X"
proof -
  have "h' \<in> {t0..t0 + h} \<Longrightarrow> t0 \<le> h'" for h' by simp
  then show ?thesis
    unfolding Picard_step_ivl_def Picard_step_def
    apply (refine_vcg, clarsimp_all simp del: atLeastAtMost_iff)
    subgoal using \<open>0 \<le> h\<close> by simp
    subgoal by (auto simp: euler_incr_slp_def wdD)
    subgoal by (auto simp: euler_incr_fas'_def)
    subgoal for XS l u
      apply (auto simp: lv_ivl_sings nonempty_interval
          simp del: atLeastAtMost_iff
          intro!: add_integral_ivl_bound)
      subgoal for x0 h' phi x h''
        apply (drule bspec, assumption)
        apply (drule bspec[where x="h'' - t0"], force)
      proof goal_cases
        case (1)
        have *: "map ((!) (list_of_eucl b)) [0..<DIM('a) - Suc 0] @ [b \<bullet> Basis_list ! (DIM('a) - Suc 0)]
          = list_of_eucl b" for b::'a
          apply (auto intro!: nth_equalityI simp: nth_append not_less)
          using Intersection.le_less_Suc_eq by blast
        have "phi x \<in> X" if "x \<in> {t0 .. h''}" for x
          using 1 that by (auto simp: cfuncset_iff)
        have "x0 + (h'' - t0) *\<^sub>R ode b \<in> {l .. u}" if "b \<in> X" for b
        proof -
          from 1(16)[rule_format, OF that] assms(1)
          have "einterpret (euler_incr_fas' D) (list_of_eucl x0 @ (h'' - t0) # list_of_eucl b) \<in> eucl_of_list ` XS"
            by (auto simp: wdD)
          also have "eucl_of_list ` XS \<subseteq> {l .. u}" by fact
          finally show ?thesis
            by (simp add: euler_incr_fas'_def einterpret_euler_incr_fas map_nth_append1 nth_append wdD[OF \<open>wd _\<close>] *)
        qed
        then have *: "(h'' - t0) *\<^sub>R ode b \<in> {l - x0..u - x0}" if "b \<in> X" for b using that
          by (auto simp: algebra_simps)
        show ?case
          apply (rule *)
          using 1 by (auto simp: cfuncset_iff)
      qed
      subgoal
        using assms(2)
        by (auto intro!: integrable_continuous_real continuous_intros
            simp: cfuncset_iff)
      done
    done
qed

subsubsection \<open>Picard iteration\<close>

lemma inf_le_supI[simp]:
  fixes a b c d::"'d::ordered_euclidean_space"
  shows
    "a \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "a \<le> d \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> c \<Longrightarrow> inf a b \<le> sup c d"
    "b \<le> d \<Longrightarrow> inf a b \<le> sup c d"
  by (auto simp: eucl_le[where 'a='d] eucl_inf[where 'a='d] eucl_sup[where 'a='d] inf_real_def sup_real_def
    intro!: sum_mono scaleR_right_mono)

lemmas [refine_vcg_def] = do_widening_spec_def

lemma P_iter_spec[le, refine_vcg]:
  assumes "PHI \<subseteq> Csafe"
  assumes "0 \<le> h"
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "P_iter X0 h i PHI \<le>
    SPEC (\<lambda>r. case r of
        None \<Rightarrow> True
      | Some (PHI'::'a set) \<Rightarrow> nonempty PHI' \<and> compact PHI' \<and> (\<exists>PHI'' \<subseteq> PHI'. RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'))"
  using assms[unfolded autoref_tag_defs]
proof (induction i arbitrary: PHI)
  case 0 then show ?case
    unfolding P_iter.simps
    by refine_vcg
next
  case (Suc i)
  show ?case
    unfolding P_iter.simps
    apply (refine_vcg Suc)
    subgoal by (auto simp: cfuncset_iff Picard_step_def algebra_simps add_increasing2)
    subgoal for lu l u b CX CX' lu' l' u' b'
      apply (simp add: nonempty_interval Picard_step_def)
      apply (safe intro!: exI[where x="{l .. u}"] compact_interval)
      subgoal by (auto simp: nonempty_interval)
      apply (rule subsetD[of CX' "{l .. u}"])
      subgoal
        apply (rule order_trans, assumption)
        unfolding atLeastatMost_subset_iff
        apply (rule disjI2)
        apply (rule conjI)
        subgoal
          apply (rule order_trans[where y="inf l' l - (if b' then \<bar>l' - l\<bar> else 0)"])
          by (simp_all split: if_split_asm add: algebra_simps add_increasing2)
        subgoal
          apply (split if_split_asm)
          apply (rule order_trans[where y="sup u' u + \<bar>u' - u\<bar>"])
          by (auto split: if_split_asm simp add: algebra_simps add_increasing2)
        done
      subgoal by force
      done
    done
qed


subsubsection \<open>iterate step size\<close>
lemma Ball_cfuncset_continuous_on:
  "\<forall>f\<in>cfuncset a b X. continuous_on {a..b} f"
  by (simp add: cfuncset_iff)

lemmas one_step_methodD = one_step_method_def[THEN iffD1, rule_format, le]
lemmas one_step_methodI = one_step_method_def[THEN iffD2, rule_format]

lemma cert_stepsize_lemma:
  assumes prems: " 0 < h"
    "X0 \<subseteq> {l..u}"
    "Res \<subseteq> Csafe"
    "Res_ivl \<subseteq> Csafe"
    "{l..u} \<subseteq> Csafe"
    "nonempty PHI'"
    "nonempty Res"
    "\<forall>x0\<in>X0.
       x0 \<in> Csafe \<longrightarrow>
       h \<in> existence_ivl0 x0 \<longrightarrow>
       (\<forall>h'\<in>{0..h}. flow0 x0 h' \<in> PHI') \<longrightarrow>
       x0 + h *\<^sub>R ode x0 \<in> PHI' \<longrightarrow> flow0 x0 h \<in> Res"
    "nonempty Res_ivl"
    "\<forall>x0\<in>X0.
       x0 \<in> Csafe \<longrightarrow>
       (\<forall>h\<in>{0..h}.
           h \<in> existence_ivl0 x0 \<longrightarrow>
           (\<forall>h'\<in>{0..h}. flow0 x0 h' \<in> PHI') \<longrightarrow>
           x0 + h *\<^sub>R ode x0 \<in> PHI' \<longrightarrow> flow0 x0 h \<in> Res_ivl)"
    "compact PHI'"
    "PHI'' \<subseteq> PHI'"
    "RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'"
  shows "flowpipe0 X0 h h Res_ivl Res"
proof -
  from prems
  have Ps: "RETURN (Some PHI'') \<le> Picard_step X0 0 h PHI'"
    by simp
  from Ps have PHI':
    "compact PHI''" "PHI'' \<subseteq> Csafe"
    "\<forall>x\<in>PHI''. x \<in> Csafe"
    "\<And>x0 h'' phi. x0 \<in> X0 \<Longrightarrow> 0 \<le> h'' \<Longrightarrow> h'' \<le> h \<Longrightarrow> phi \<in> cfuncset 0 h'' PHI' \<Longrightarrow>
    x0 + integral {0..h''} (\<lambda>t. ode (phi t)) \<in> PHI''"
    by (auto simp: Picard_step_def)
  then obtain cx where cx: "(\<lambda>t::real. cx) \<in> cfuncset 0 0 PHI'"
    using \<open>PHI'' \<subseteq> PHI'\<close> \<open>nonempty PHI'\<close> by (auto simp: cfuncset_def continuous_on_const nonempty_def)
  show "flowpipe0 X0 h h Res_ivl Res"
    unfolding flowpipe0_def atLeastAtMost_singleton
  proof safe
    show "0 \<le> h" using \<open>0 < h\<close> by simp
    show safe_X0: "x \<in> Csafe" if "x \<in> X0" for x using that \<open>{l..u} \<subseteq> Csafe\<close> \<open>X0 \<subseteq> {l..u}\<close> by blast
    show "x \<in> Csafe" if "x \<in> Res_ivl" for x using prems that
      by (auto simp: )
    show "x \<in> Csafe" if "x \<in> Res" for x using prems that by (auto simp:)
    fix x0 assume "x0 \<in> X0"
    from PHI'(4)[OF \<open>x0 \<in> X0\<close> order_refl \<open>0 \<le> h\<close> cx]
    have "x0 \<in> PHI''" by simp
    have *: "h \<in> existence_ivl0 x0" "s \<in> {0 .. h} \<Longrightarrow> flow0 x0 s \<in> PHI''" for s
      using \<open>x0 \<in> X0\<close> \<open>PHI'' \<subseteq> PHI'\<close> \<open>0 \<le> h\<close> PHI'(3) \<open>x0 \<in> PHI''\<close>
      by (auto
          simp: cfuncset_def Pi_iff closed_segment_eq_real_ivl ivl_integral_def
          intro!: Picard_iterate_mem_existence_ivlI[OF UNIV_I _ UNIV_I \<open>compact PHI''\<close>
            \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> Csafe\<close>] PHI'(4)) force+
    show h_ex: "h \<in> existence_ivl0 x0" by fact
    have cf: "(\<lambda>t::real. x0) \<in> cfuncset 0 h PHI'" for h
      using \<open>x0 \<in> PHI''\<close> \<open>PHI'' \<subseteq> PHI'\<close>
      by (auto simp: cfuncset_def continuous_intros)
    have mem_PHI': "x0 + h' *\<^sub>R ode x0 \<in> PHI'" if "0 \<le> h'" "h' \<le> h" for h'
      using that \<open>PHI'' \<subseteq> PHI'\<close> PHI'(4)[OF \<open>x0 \<in> X0\<close> that cf]
      by auto
    from this prems safe_X0
    show "flow0 x0 h \<in> Res"
      using \<open>0 \<le> h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close>
      by (auto simp: subset_iff dest!: bspec[where x=x0])
    fix h' assume h': "h' \<in> {0..h}"
    then have "h' \<in> existence_ivl0 x0"
      by (meson atLeastAtMost_iff existence_ivl_zero h_ex is_interval_1
          local.is_interval_existence_ivl local.mem_existence_ivl_iv_defined(2))
    from h' this prems safe_X0
    show "flow0 x0 h' \<in> Res_ivl"
      using \<open>0 < h\<close> h_ex * \<open>PHI'' \<subseteq> PHI'\<close> \<open>x0 \<in> X0\<close> mem_PHI' \<open>x0 \<in> PHI''\<close>
      by (auto simp: subset_iff dest!: bspec[where x=x0])
  qed
qed

lemma cert_stepsize_spec[le,refine_vcg]:
  assumes "h > 0"
  assumes "one_step_method m"
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "cert_stepsize m X0 h i n \<le> SPEC (\<lambda>(h', RES::'a set, RES_ivl, _). nonempty RES \<and> nonempty RES_ivl \<and> 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using assms(1)[unfolded autoref_tag_defs]
proof (induction n arbitrary: h)
  case 0 then show ?case by simp
next
  case (Suc n)
  note [refine_vcg] = Suc.IH[of "h/2", le]
  show ?case
    unfolding cert_stepsize.simps
    using Suc.prems
    by (refine_vcg Ball_cfuncset_continuous_on one_step_methodD[OF assms(2)])
       (clarsimp_all simp: cert_stepsize_lemma)
qed


subsubsection \<open>Euler step\<close>

lemma embed_real_ivl_iff[simp]:
   "(\<forall>x \<in> {0 .. h *\<^sub>R (One::'a::executable_euclidean_space)}. P (x \<bullet> hd Basis_list)) \<longleftrightarrow> (\<forall>x \<in> {0 .. h}. P x)"
proof (auto simp: eucl_le[where 'a='a], goal_cases)
  case hyps: (1 x)
  have "x = x *\<^sub>R (One::'a) \<bullet> hd Basis_list"
    by auto
  also have "P \<dots>"
    apply (rule hyps[rule_format])
    using hyps
    by (auto simp: eucl_le[where 'a='a])
  finally show ?case .
qed

lemma convex_on_segmentI:
  assumes mem_convex: "convex C" "a \<in> C" "a + j *\<^sub>R b \<in> C"
  assumes "0 \<le> i" "i \<le> j"
  shows "a + i *\<^sub>R b \<in> C"
proof -
  have "a + i *\<^sub>R b = (1 - i / j) *\<^sub>R a + (i / j) *\<^sub>R (a + j *\<^sub>R b)"
    using assms
    by (auto simp: algebra_simps diff_divide_distrib)
  also have "\<dots> \<in> C"
    using assms
    by (auto simp: divide_simps intro!: convexD[OF mem_convex])
  finally show ?thesis .
qed

lemma one_step_flowpipe:
  assumes [THEN one_step_methodD, refine_vcg]: "one_step_method m"
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "one_step X0 h m \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using assms
  unfolding one_step_def
  by refine_vcg

lemma ncc_imageD:
  assumes "ncc ((\<lambda>x. x ! i) ` env)"
  assumes "nth_image_precond env i"
  shows "compact ((\<lambda>x. x ! i) ` env::real set)" "closed ((\<lambda>x. x ! i) ` env)" "bounded ((\<lambda>x. x ! i) ` env)"
    "((\<lambda>x. x ! i) ` env) \<noteq> {}" "convex ((\<lambda>x. x ! i) ` env)"
  using assms
  by (auto simp: ncc_def nth_image_precond_def compact_eq_bounded_closed)

lemma max_Var_floatariths_ode_d_fa[le]:
  assumes [simp]: "length ode_e > 0" "max_Var_floatariths ode_e \<le> length ode_e"
    "length cxs = length ode_e" "length ys = length ode_e"
  shows "max_Var_floatariths (ode_d_fa i cxs ys) \<le> max (max_Var_floatariths (cxs)) (max_Var_floatariths ys)"
  apply (auto simp: ode_d_fa_def max_Var_floatariths_Max )
  using assms apply auto[1]
  apply (auto intro!: max_Var_floatarith_subst_floatarith_le max_Var_floatariths_ode_d_expr
      max_Var_floatarith_le_max_Var_floatariths_nthI max_Var_ode_fa
      simp: in_set_conv_nth)
   apply (auto simp: max_Var_floatariths_Max in_set_conv_nth)
  done

lemma max_Var_floatariths_euler_err_fas[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  shows "max_Var_floatariths (euler_err_fas xs h cxs)
    \<le> max (max_Var_floatariths xs) (max (max_Var_floatarith h) (max_Var_floatariths cxs))"
  using nz
  by (auto simp: euler_err_fas_def[abs_def] euler_err_fas_nth_def[abs_def] map_nth_eq_self simp del: length_0_conv
      intro!: max_Var_floatariths_ode_d_fa max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa; arith)

lemma max_Var_floatariths_euler_incr_fas[le]:
  assumes [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  shows "max_Var_floatariths (euler_incr_fas xs h cxs)
    \<le> max (max_Var_floatariths xs) (max (max_Var_floatarith h) (max_Var_floatariths cxs))"
  using length_ode_fa
  by (auto simp: euler_incr_fas_def euler_incr_fas_nth_def[abs_def] simp del: length_ode_fa
      intro!: max_Var_floatariths_ode_d_fa max_Var_floatariths_map_plus max_Var_floatariths_map_times
      max_Var_floatariths_map_const max_Var_ode_fa)

lemma map_euler_incr_fas_nth: "length X0 = d \<Longrightarrow> map (euler_incr_fas_nth X0 h CX) [0..<d] = euler_incr_fas X0 h CX"
  by (auto simp: euler_incr_fas_def)

lemma map_euler_err_fas_nth: "length X0 = d \<Longrightarrow> map (euler_err_fas_nth X0 h CX) [0..<d] = euler_err_fas X0 h CX"
  by (auto simp: euler_err_fas_def)

lemma max_Var_floatariths_euler_fas[le]:
  assumes [simp]: "max_Var_floatariths ode_e \<le> length ode_e"
    "length xs = length ode_e"
    "length cxs = length ode_e"
  assumes nz: "0 < length ode_e"
  shows "max_Var_floatariths (euler_fas xs h cxs) \<le> Max {max_Var_floatariths xs, max_Var_floatarith h, max_Var_floatariths cxs}"
  using nz
  by (auto simp: euler_fas_def map_euler_incr_fas_nth map_euler_err_fas_nth
      intro!: max_Var_floatariths_map_plus max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_euler_err_fas)

lemma take_interpret_floatariths:
  "d < length fas \<Longrightarrow> take d (interpret_floatariths fas vs) = interpret_floatariths (take d fas) vs"
  by (auto intro!: nth_equalityI)

lemma length_euler_slp_le: "2 * D \<le> length euler_slp"
  by (auto simp: euler_fas'_def euler_slp_def intro!: order_trans[OF _ length_slp_of_fas_le])

lemma ncc_nonempty[simp]: "ncc x \<Longrightarrow> nonempty x"
  by (simp add: ncc_def nonempty_def)

lemma nccD:
  assumes "ncc X"
  shows "compact X" "closed X" "bounded X" "X \<noteq> {}" "convex X"
  using assms
  by (auto simp: ncc_def nth_image_precond_def compact_eq_bounded_closed)

lemma D_DIM_wdD[simp]: "wd TYPE('a::executable_euclidean_space) \<Longrightarrow> D = DIM('a)"
  by (auto simp: wdD)

lemma euler_step_flowpipe:
  includes floatarith_notation
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "euler_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  unfolding euler_step_def THE_NRES_def
  apply (intro SPEC_rule_conjI one_step_flowpipe one_step_methodI)
    apply (refine_vcg, clarsimp_all)
  subgoal using assms by (auto simp: euler_slp_def euler_fas'_def)
  subgoal by (auto simp: euler_slp_def euler_fas'_def)
  subgoal using length_euler_slp_le assms by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
  subgoal using length_euler_slp_le assms by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
proof (goal_cases)
  case hyps: (1 X0 CX hl hu env res b x0 enve h)
  then interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_. ode" "\<lambda>(t, x). ode_d1 x o\<^sub>L snd_blinfun"
    by unfold_locales (auto intro!: continuous_intros derivative_eq_intros
        simp: split_beta' subset_iff  wdD[OF \<open>wd _\<close>])
  from \<open>h \<in> existence_ivl0 x0\<close> have s_ex: "s \<in> existence_ivl0 x0" if "0 \<le> s" "s \<le> h" for s
    by (metis (no_types, lifting) atLeastAtMost_iff ivl_subset_existence_ivl subset_iff that)
  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> eucl_of_list ` take D ` env"
    using hyps
    apply (intro euler_consistent_traj_set[where x="flow0 x0" and u = "h"])
            apply (auto intro!: \<open>0 \<le> h\<close> flow_has_vector_derivative[THEN has_vector_derivative_at_within]
        simp: nccD discrete_evolution_def euler_increment subset_iff wdD[OF \<open>wd _\<close>]
          Let_def s_ex min_def max_def lv_ivl_sings)
    subgoal premises prems for s
    proof -
      have "interpret_floatariths (euler_fas' DIM('a)) (list_of_eucl x0 @ list_of_eucl (flow0 x0 s) @ [h]) \<in> env"
        using prems
        by (auto intro!: prems(1)[rule_format])
      then have "eucl_of_list (take D (interpret_floatariths (euler_fas' DIM('a)) (list_of_eucl x0 @ list_of_eucl (flow0 x0 s) @ [h])))
        \<in> eucl_of_list ` take D ` env"
        (is "eucl_of_list (take _ (interpret_floatariths  _ ?vs)) \<in> _")
        by auto
      also
      have "take (2 * D) (interpret_floatariths (euler_fas' DIM('a)) ?vs) =
        interpret_floatariths (map fold_const_fa (euler_fas (map floatarith.Var [0..<D]) (Var (2 * D)) (map floatarith.Var [D..<2 * D]))) ?vs"
        unfolding euler_fas'_def
        by (auto simp: euler_fas_def wdD[OF \<open>wd _\<close>] simp del: map_map
            intro!: max_Var_floatariths_map_plus max_Var_floatariths_euler_incr_fas
              max_Var_floatariths_euler_err_fas \<open>wd _\<close>
              max_Var_floatariths_fold_const_fa[le])
      then have "take D (take (2 * D) (interpret_floatariths (euler_fas' DIM('a)) ?vs)) =
        take D (interpret_floatariths (euler_fas  (map floatarith.Var [0..<D]) (Var(2 * D)) (map floatarith.Var [D..<2 * D])) ?vs)"
        by simp
      then have "take D (interpret_floatariths (euler_fas' DIM('a)) ?vs) =
        take DIM('a) (interpret_floatariths (euler_fas  (map floatarith.Var [0..<D]) (Var(2 * D)) (map floatarith.Var [D..<2 * D])) ?vs)"
        by (simp add: wdD[OF \<open>wd _\<close>])
      also have "eucl_of_list \<dots> =
          x0 + h *\<^sub>R ode x0 + (h\<^sup>2 / 2) *\<^sub>R (ode_d 0 (flow0 x0 s) (ode (flow0 x0 s))) (ode (flow0 x0 s))"
        by (auto simp: take_interpret_floatariths einterpret_euler_fas1 map_nth_append1 prems nth_append
            wdD[OF \<open>wd _\<close>])
      finally show ?thesis
        by (simp add: prems(10) prems(13) prems(14) prems(5) ode_d1_eq[symmetric] wdD[OF \<open>wd _\<close>])
    qed
    done
  also have "\<dots> \<subseteq> res" using assms hyps by auto
  finally show ?case by simp
qed (auto simp: assms)

lemma length_rk2_slp_le: "2 * D \<le> length rk2_slp"
  by (auto simp: rk2_slp_def rk2_fas'_def intro!: order_trans[OF _ length_slp_of_fas_le])

lemma max_Var_floatarith_R\<^sub>e[simp]: "max_Var_floatarith (R\<^sub>e x) = 0"
  by (auto simp: R\<^sub>e_def split: prod.splits)

lemma max_Var_floatariths_rk2_fas_err[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e" "length x0 = length ode_e" "length cx = length ode_e"
  shows "max_Var_floatariths (rk2_fas_err rkp x0 h cx s2) \<le>
    Max {max_Var_floatarith rkp, max_Var_floatariths x0, max_Var_floatarith h, max_Var_floatariths cx,
      max_Var_floatarith s2}"
  using nz
  unfolding rk2_fas_err_def rk2_fas_err_nth_def
  by (auto simp: rk2_fas_err_def
      intro!: max_Var_floatariths_append max_Var_floatariths_map_plus max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_ode_d_fa; arith)

lemma max_Var_floatarith_one[simp]: "max_Var_floatarith 1 = 0"
  and max_Var_floatarith_zero[simp]: "max_Var_floatarith 0 = 0"
  by (auto simp: one_floatarith_def zero_floatarith_def)

lemma max_Var_floatariths_rk2_fas[le]:
  assumes nz: "0 < length ode_e"
    and [simp]: "max_Var_floatariths ode_e \<le> length ode_e" "length x0 = length ode_e" "length cx = length ode_e"
  shows "max_Var_floatariths (rk2_fas rkp x0 h cx s2) \<le>
    Max {max_Var_floatarith rkp, max_Var_floatariths x0, max_Var_floatarith h, max_Var_floatariths cx,
      max_Var_floatarith s2}"
  using nz
  by (auto simp: rk2_fas_def
      intro!: max_Var_floatariths_append max_Var_floatariths_map_plus max_Var_floatariths_map_times
        max_Var_floatariths_map_const max_Var_ode_fa max_Var_floatariths_euler_incr_fas
        max_Var_floatariths_rk2_fas_err)

lemma rk2_step_flowpipe:
  includes floatarith_notation
  assumes [refine_vcg]: "wd TYPE('a::executable_euclidean_space)"
  shows "rk2_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'a set).
    0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  unfolding rk2_step_def THE_NRES_def
  apply (intro one_step_flowpipe assms one_step_methodI)
  apply (refine_vcg, clarsimp_all)
  subgoal using assms by (auto simp: rk2_slp_def rk2_fas'_def)
  subgoal by (auto simp: rk2_slp_def rk2_fas'_def)
  subgoal using length_rk2_slp_le by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
  subgoal using length_rk2_slp_le by (auto simp: env_len_def wdD[OF \<open>wd _\<close>])
proof (goal_cases)
  case hyps: (1 X0 CX hl hu rk2_param env res b x0 el h)
  from assms have "D = DIM('a)" by simp
  have aux: "ode (flow0 x0 s) = ode (snd (s, flow0 x0 s))" for s
    by simp
  from hyps interpret derivative_on_prod "{0 .. h}" CX "\<lambda>_ x. ode x" "\<lambda>(t, x). ode_d1 x o\<^sub>L snd_blinfun"
    by unfold_locales
      (auto intro!: continuous_intros derivative_eq_intros simp: split_beta' subset_iff)

  have aux2: "blinfun_apply (ode_d1 (snd tx)) \<circ> snd = blinfun_apply (ode_d1 (snd tx) o\<^sub>L snd_blinfun)"
    for tx::"real\<times>'a"
    by (auto intro!: blinfun_eqI)

  have aux3: "blinfun_apply (ode_d2 (snd tx)) (snd h) o\<^sub>L snd_blinfun =
    (flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun)) h"
    for tx h::"real\<times>'a"
    by (auto intro!: blinfun_eqI)


  have "flow0 x0 (h) = flow0 x0 (0 + (h))" by simp
  also have "\<dots> \<in> eucl_of_list ` take D ` env"
    using hyps assms
    apply (intro rk2_consistent_traj_set[where
      x="flow0 x0" and u = "h" and T="{0..h}" and X="CX" and p="rk2_param"
      and f = "ode_na" and f' = ode_d_na and g' = ode_d_na and f'' = ode_d2_na and g'' = ode_d2_na])
    subgoal by (simp add: \<open>0 \<le> h\<close>)
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by (auto simp add: ncc_def nonempty_def)
    subgoal
      apply (rule flow_has_vector_derivative[THEN has_vector_derivative_at_within, THEN has_vector_derivative_eq_rhs])
      subgoal by (metis (no_types, lifting) ivl_subset_existence_ivl subset_iff)
      subgoal by (force simp: ode_na_def[abs_def] ode_d_na_def[abs_def] ode_d2_na_def[abs_def])
      done
    subgoal
      unfolding ode_na_def ode_d_na_def ode_d2_na_def
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
        apply (rule derivative_intros)
      subgoal by (force simp: ncc_def nonempty_def)\<comment> \<open>unnecessarily slow\<close>
      subgoal by force
      done
    subgoal
      unfolding ode_na_def ode_d_na_def ode_d2_na_def
      apply (rule derivative_eq_intros)
        apply (rule derivative_intros)
         apply (rule derivative_intros)
         apply (rule derivative_intros)
      subgoal by (force simp: nonempty_def)
       apply (rule derivative_intros)
      subgoal by (auto intro!: aux3)
      done
    subgoal by (rule refl)
    subgoal by (rule refl)
    subgoal
      apply (rule compact_imp_bounded)
      apply (rule compact_continuous_image)
      subgoal
        by (auto intro!: continuous_intros simp: ode_na_def ode_d_na_def ode_d2_na_def)
      subgoal by (auto simp: ncc_def intro!: compact_Times)
      done
    subgoal by auto
    subgoal by simp
    subgoal by simp
    subgoal
      apply (rule convex_on_segmentI[where j=h])
      using mult_left_le_one_le[of h "rk2_param"]
      by (auto simp: ncc_def mult_left_le_one_le mult_le_one ac_simps ode_na_def
          ode_d_na_def ode_d2_na_def dest: bspec[where x=0])
    subgoal by (simp add: ncc_def)
    subgoal by (simp add: ncc_def compact_imp_closed)
    subgoal for s1 s2
      apply (clarsimp simp add: lv_ivl_sings)
      subgoal premises prems
      proof -
        have "s2 * rk2_param * h \<le> h"
          apply (rule mult_left_le_one_le)
          using assms prems
          by (auto intro!: mult_le_one)
        then have s2: "(s2 * h * rk2_param) \<in> {0 .. h}"
          using prems assms by (auto simp: ac_simps)
        have s1: "h * s1 \<in> {0 .. h}" using prems
          by (auto intro!: mult_right_le_one_le)
        then have
          "interpret_floatariths (rk2_fas' D)
              (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param, h, s2]) \<in> env"
          unfolding \<open>D = _\<close> using prems
          by (intro prems(17)[rule_format]) auto
        then have "take (2 * D) (interpret_floatariths (rk2_fas' D)
              (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param, h, s2])) \<in> take (2 * D) ` env"
          (is "?l \<in> _")
          by auto
        also have "?l = interpret_floatariths
         (map fold_const_fa (rk2_fas (Var (2 * D)) (map floatarith.Var [0..<D]) (Var (2 * D + 1))
          (map floatarith.Var [D..<2 * D])
           (Var (2 * D + 2))))
         (list_of_eucl x0 @ list_of_eucl (flow0 x0 (h * s1)) @ [rk2_param, h, s2])"
          (is "_ = interpret_floatariths (map fold_const_fa ?fas) ?xs")
          unfolding rk2_fas'_def
          by (auto intro!: max_Var_floatariths_rk2_fas max_Var_floatariths_fold_const_fa[le] simp: wdD[OF \<open>wd _\<close>])
        finally have "take D (interpret_floatariths ?fas ?xs) \<in> take D ` take (2 * D) ` env"
          by auto
        also have "\<dots> = take D ` env" by (auto simp: image_image wdD[OF \<open>wd _\<close>])
        finally have "eucl_of_list (take D (interpret_floatariths ?fas ?xs)) \<in> eucl_of_list ` take D ` env"
          by simp
        then have "einterpret (take D ?fas) ?xs \<in> eucl_of_list ` take D ` env"
          by (simp add: take_interpret_floatariths wdD[OF \<open>wd _\<close>])
        also have "einterpret (take D ?fas) ?xs =
          discrete_evolution (rk2_increment (rk2_param) (\<lambda>t x. ode_na (t, x))) h 0 x0 +
          heun_remainder1 (flow0 x0) ode_na ode_d_na ode_d2_na 0 h s1 -
          heun_remainder2 (rk2_param) (flow0 x0) ode_na ode_d2_na 0 h s2"
          apply (simp add: wdD[OF \<open>wd _\<close>])
          apply (subst rk2_increment_rk2_fas1[where ?s1'.0 = s1])
          subgoal by (auto simp: nth_append map_nth_append1)
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close>)
          subgoal
            apply (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close>)
            by (meson connectedD_interval existence_ivl_zero flow0_defined hyps
                mult_right_le_one_le mult_sign_intros(1) mvar.connected prems)
          subgoal
          proof -
            have "x0 + ((rk2_param * s2) * h) *\<^sub>R ode x0 \<in> CX"
              by (rule convex_on_segmentI[where j=h])
                 (use prems in \<open>auto simp: ncc_def mult_left_le_one_le mult_le_one
                  dest: bspec[where x=0]\<close>)
            also note \<open>\<dots> \<subseteq> Csafe\<close>
            finally show ?thesis
              by (auto simp: nth_append map_nth_append1 \<open>x0 \<in> Csafe\<close> ac_simps)
          qed
          subgoal by (auto simp: nth_append map_nth_append1 ode_na_def)
          done
        finally show ?thesis by (simp add: \<open>D = _\<close>)
      qed
      done
    done
  also have "\<dots> \<subseteq> res" using hyps(5) by (auto simp: \<open>D = _\<close>)
  finally show ?case by (simp add: \<open>D = _\<close>)
qed

lemma interpret_adapt_stepsize_fa:
  "interpret_floatarith (adapt_stepsize_fa rtol m_id e h') []
    = float_of h' * (float_of(rtol) / float_of e) powr (1 / (float_of (m_id) + 1))"
  by (auto simp: inverse_eq_divide adapt_stepsize_fa_def)

lemma choose_step_flowpipe[le, refine_vcg]:
  assumes "wd TYPE('a::executable_euclidean_space)"
  shows "choose_step X0 h \<le> SPEC (\<lambda>(h', _, RES_ivl, (RES::'a set)). 0 < h' \<and> h' \<le> h \<and> flowpipe0 X0 h' h' RES_ivl RES)"
  using assms
  unfolding choose_step_def
  by (refine_vcg rk2_step_flowpipe euler_step_flowpipe)

lemma CsafeI: "t \<in> existence_ivl0 x \<Longrightarrow> x \<in> Csafe"
  using local.mem_existence_ivl_iv_defined(2) by blast

lemma apply_vareq: "blinfun_apply (vareq x t) = ode_d1 (flow0 x t)"
  by (auto simp: vareq_def)

lemma Dflow_has_derivative:
  "t \<in> existence_ivl0 x \<Longrightarrow> (Dflow x has_derivative blinfun_scaleR_left (ode_d1 (flow0 x t) o\<^sub>L Dflow x t)) (at t)"
  by (auto simp: Dflow_def blinfun.bilinear_simps scaleR_blinfun_compose_left apply_vareq CsafeI
      intro!: derivative_eq_intros mvar.flow_has_derivative[THEN has_derivative_eq_rhs] ext
        blinfun_eqI)

lemma matrix_scaleR: "matrix (blinfun_apply (h *\<^sub>R X)) = h *\<^sub>R matrix X"
  by (vector matrix_def blinfun.bilinear_simps)

lemma blinfun_of_vmatrix_matrix_matrix_mult[simp]:
  "blinfun_of_vmatrix (A ** B) = blinfun_of_vmatrix A o\<^sub>L blinfun_of_vmatrix B"
  including blinfun.lifting
  by transfer (auto simp: o_def matrix_vector_mul_assoc)

lemma blinfun_of_vmatrix_mat_1[simp]: "blinfun_of_vmatrix (mat 1) = 1\<^sub>L"
  including blinfun.lifting
  by transfer (auto simp: matrix_vector_mul_lid)

lemma blinfun_of_vmatrix_matrix[simp]:
  "blinfun_of_vmatrix (matrix (blinfun_apply A)) = A"
  including blinfun.lifting
  by transfer (auto simp: bounded_linear.linear matrix_works)

lemma inner_Basis_eq_vec_nth: "b \<in> Basis \<Longrightarrow> v \<bullet> b = vec_nth v (enum_class.enum ! index Basis_list b)"
  by (auto simp: inner_vec_def vec_nth_Basis if_distrib Basis_vec_def axis_eq_axis
        index_Basis_list_axis1
      cong: if_cong)

lemma intersects_sctns_spec_nres[le, refine_vcg]:
  "intersects_sctns X' sctns \<le> intersects_sctns_spec X' sctns"
  unfolding intersects_sctns_spec_def intersects_sctns_def
  by refine_vcg auto

lemma intersects_sections_spec_clw_ref[le, refine_vcg]:
  "intersects_sctns_spec_clw R sctns \<le> intersects_sctns_spec R sctns"
  unfolding intersects_sctns_spec_def intersects_sctns_spec_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>S b. \<not>b \<longrightarrow> \<Union>S \<inter> \<Union>(plane_of ` sctns) = {}"]) auto

lemma eq_nth_iff_index:
  "distinct xs \<Longrightarrow> n < length xs \<Longrightarrow> i = xs ! n  \<longleftrightarrow> index xs i = n"
  using index_nth_id by fastforce

lemma
  max_Var_floatariths_ode_e_wd:
  assumes wd: "wd (TYPE('n::enum rvec))"
  assumes "CARD('n) \<le> K"
  shows "max_Var_floatariths ode_e \<le> K"
  using wdD[OF wd] assms by auto

lemma nonzero_component[le, refine_vcg]: "nonzero_component s X n \<le> SPEC (\<lambda>_. \<forall>b\<in>X. b \<bullet> n \<noteq> 0)"
  unfolding nonzero_component_def
  by refine_vcg auto

lemma
  interpret_slp_env_lenD:
  assumes "\<forall>cx\<in>CX. interpret_slp (slp_of_fas (fas)) (env cx) \<in> R"
  assumes "cx \<in> CX"
  shows "interpret_floatariths fas (env cx) \<in> take (length fas) ` R"
proof -
  from slp_of_fas
  have "take (length fas) (interpret_slp (slp_of_fas fas) (env cx)) = interpret_floatariths fas (env cx)"
    by auto
  moreover
  from assms(1)[rule_format, OF \<open>cx \<in> CX\<close>]
  have "interpret_slp (slp_of_fas fas) (env cx) \<in> R" by auto
  ultimately show ?thesis by force
qed

lemma flowpipe0_imp_flowpipe:
  assumes "flowpipe0 (fst ` X0) x1 x1 aba bba"
  shows "flowpipe X0 x1 x1 (aba \<times> UNIV) (bba \<times> UNIV)"
  using assms
  by (auto simp: flowpipe0_def flowpipe_def)

lemma disjoints_spec[le, refine_vcg]:
  "disjoints_spec X Y \<le> SPEC (\<lambda>b. b \<longrightarrow> (X \<inter> Y = {}))"
  unfolding disjoints_spec_def autoref_tag_defs
  by refine_vcg auto

lemma inner_eq_zero_abs_BasisI:
  "\<bar>y\<bar> \<in> Basis \<Longrightarrow> b \<in> Basis \<Longrightarrow> \<bar>y\<bar> \<noteq> b \<Longrightarrow> y \<bullet> b = 0"
  for b y::"'a::executable_euclidean_space"
  by (metis abs_inner inner_Basis linorder_not_le order_refl zero_less_abs_iff)

lemma abs_in_Basis_absE:
  fixes x y::"'a::executable_euclidean_space"
  assumes "abs y \<in> Basis"
  obtains "abs y = y" | "abs y = -y"
proof -
  have "abs y = (\<Sum>i\<in>Basis. (abs (y \<bullet> i)) *\<^sub>R i)"
    by (simp add: euclidean_representation abs_inner[symmetric] assms)
  also have "Basis = insert (abs y) (Basis - {abs y})" using assms by auto
  also have "(\<Sum>i\<in>insert \<bar>y\<bar> (Basis - {\<bar>y\<bar>}). \<bar>y \<bullet> i\<bar> *\<^sub>R i) = \<bar>y \<bullet> \<bar>y\<bar>\<bar> *\<^sub>R \<bar>y\<bar>"
    apply (subst sum.insert)
    using assms
    by (auto simp: abs_inner[symmetric] inner_Basis if_distribR if_distrib
        cong: if_cong)
  finally have "\<bar>y\<bar> = \<bar>y \<bullet> \<bar>y\<bar>\<bar> *\<^sub>R \<bar>y\<bar>" by simp
  moreover have "\<dots> = y \<or> \<dots> = - y"
    using assms
    by (auto simp: abs_real_def algebra_simps  intro!: euclidean_eqI[where 'a='a]
        simp: inner_Basis inner_eq_zero_abs_BasisI split: if_splits)
  ultimately consider "\<bar>y\<bar> = y" | "\<bar>y\<bar> = - y" by auto
  then show ?thesis
    by (cases; rule that)
qed

lemma abs_in_BasisE:
  fixes x y::"'a::executable_euclidean_space"
  assumes "abs y \<in> Basis"
  obtains i where "i \<in> Basis" "y = i" | i where "i \<in> Basis" "y = -i"
proof -
  from abs_in_Basis_absE[OF assms]
  consider "\<bar>y\<bar> = y" | "\<bar>y\<bar> = - y"
    by auto
  then show ?thesis
  proof cases
    case 1 with assms have "abs y \<in> Basis" "y = abs y" by auto
    then show ?thesis ..
  next
    case 2
    with assms have "abs y \<in> Basis" "y = - abs y" by auto
    then show ?thesis ..
  qed
qed

lemma subset_spec_plane[le, refine_vcg]:
  "subset_spec_plane X sctn \<le> SPEC (\<lambda>b. b \<longrightarrow> X \<subseteq> plane_of sctn)"
  unfolding subset_spec_plane_def
  by (refine_vcg) (auto simp: plane_of_def eucl_le[where 'a='a] dest!: bspec elim!: abs_in_BasisE)

lemma subset_spec_coll_refine[le, refine_vcg]: "subset_spec_coll X Y \<le> subset_spec X Y"
  unfolding subset_spec_coll_def autoref_tag_defs subset_spec_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> \<Union>X \<subseteq> Y"]) auto

lemma
  eventually_in_planerectI:
  fixes n::"'a::executable_euclidean_space"
  assumes "abs n \<in> Basis"
  assumes "{l .. u} \<subseteq> plane n c" "l \<le> u"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> i \<noteq> abs n \<Longrightarrow> l \<bullet> i < x \<bullet> i"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> i \<noteq> abs n \<Longrightarrow> x \<bullet> i < u \<bullet> i"
  shows "\<forall>\<^sub>F x in at x within plane n c. x \<in> {l .. u}"
proof -
  have "\<forall>\<^sub>F x in at x within plane n c. x \<in> plane n c"
    unfolding eventually_at_filter
    by simp
  then have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> abs n \<le> x \<bullet> abs n \<and> x \<bullet> abs n \<le> u \<bullet> abs n"
    apply eventually_elim
    using assms(1,2,3)
    by (auto simp: elim!: abs_in_BasisE)
  moreover
  {
    fix i assume that: "i \<in> Basis" "i \<noteq> abs n"
    have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> i < x \<bullet> i" "\<forall>\<^sub>F x in at x within plane n c. x \<bullet> i < u \<bullet> i"
      by (auto intro!: order_tendstoD assms tendsto_eq_intros that)
    then have "\<forall>\<^sub>F x in at x within plane n c. l \<bullet> i < x \<bullet> i \<and> x \<bullet> i < u \<bullet> i"
      by eventually_elim auto
  } then have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i \<in> Basis - {abs n}. l \<bullet> i < x \<bullet> i \<and> x \<bullet> i < u \<bullet> i"
    by (auto intro!: eventually_ball_finite)
  then have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i \<in> Basis - {abs n}. l \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> u \<bullet> i"
    by eventually_elim (auto intro!: less_imp_le)
  ultimately
  have "\<forall>\<^sub>F x in at x within plane n c. \<forall>i\<in>Basis. l \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> u \<bullet> i"
    by eventually_elim auto
  then show ?thesis
    by eventually_elim (auto simp: eucl_le[where 'a='a])
qed

lemma mem_ivl_euclI: "k \<in> {c..d::'x::ordered_euclidean_space}" if "\<And>i. i \<in> Basis \<Longrightarrow> c \<bullet> i \<le> k \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> k \<bullet> i \<le> d \<bullet> i"
  using that
  by (auto simp: eucl_le[where 'a='x])

lemma op_eventually_within_sctn[le, refine_vcg]:
  "op_eventually_within_sctn X sctn S \<le>
    SPEC (\<lambda>b. b \<longrightarrow> (\<forall>x \<in> X. x \<in> S \<and> (\<forall>\<^sub>F x in at x within plane_of sctn. x \<in> S)))"
  unfolding op_eventually_within_sctn_def
  apply refine_vcg
  unfolding plane_of_def autoref_tag_defs
  apply (safe intro!: eventually_in_planerectI mem_ivl_euclI)
  subgoal premises prems for a b c d e f g h i j k B
  proof cases
    assume "B = \<bar>normal sctn\<bar>"
    moreover
    have "c \<in> plane (normal sctn) (pstn sctn)" "k \<in> plane (normal sctn) (pstn sctn)"
      using prems by auto
    ultimately show "c \<bullet> B \<le> k \<bullet> B" using \<open>\<bar>normal sctn\<bar> \<in> set Basis_list\<close>
      by (auto simp: elim!: abs_in_Basis_absE)
  next
    assume B: "B \<noteq> \<bar>normal sctn\<bar>"
    have "k \<bullet> B \<in> {g \<bullet> B .. h  \<bullet> B}"
      using \<open>k \<in> X\<close> \<open>X \<subseteq> {g..h}\<close> \<open>B \<in> Basis\<close> by (auto simp: eucl_le[where 'a='a])
    with B prems show ?thesis by (auto dest!: bspec elim!: abs_in_Basis_absE)
  qed
  subgoal premises prems for a b c d e f g h i j k B
  proof cases
    assume "B = \<bar>normal sctn\<bar>"
    moreover
    have "d \<in> plane (normal sctn) (pstn sctn)" "k \<in> plane (normal sctn) (pstn sctn)"
      using prems by auto
    ultimately show "d \<bullet> B \<ge> k \<bullet> B" using \<open>\<bar>normal sctn\<bar> \<in> set Basis_list\<close>
      by (auto simp: elim!: abs_in_Basis_absE)
  qed (use prems in \<open>auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD\<close>)
  subgoal by simp
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD cong del: image_cong_simp)
  subgoal by (auto elim!: abs_in_BasisE simp: eucl_le[where 'a='a] dest!: bspec subsetD cong del: image_cong_simp)
  done

lemma Let_unit: "Let (x::unit) f = f ()"
  by auto
lemma CHECK_no_text: "CHECKs (x#ys) a = CHECKs [] a"
  by auto

lemma frontier_above_halfspace:
  "normal sctn \<noteq> 0 \<Longrightarrow> frontier (above_halfspace sctn) = plane_of sctn"
  using frontier_halfspace_ge[of "normal sctn" "pstn sctn"]
  by (auto simp: halfspace_simps plane_of_def inner_commute)

lemma
  flowpipe_subset:
  assumes "flowpipe X0 hl hu CX X1"
    and subs: "Y0 \<subseteq> X0" "hl \<le> il" "il \<le> iu" "iu \<le> hu" "CX \<subseteq> CY" "X1 \<subseteq> Y1"
    and safe: "fst ` CY \<union> fst ` Y1 \<subseteq> Csafe"
  shows "flowpipe Y0 il iu CY Y1"
proof -
  from assms(1) have fp: "0 \<le> hl" "hl \<le> hu" "fst ` X0 \<subseteq> Csafe" "fst ` CX \<subseteq> Csafe" "fst ` X1 \<subseteq> Csafe"
    "\<forall>(x0, d0)\<in>X0. \<forall>h\<in>{hl..hu}. h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1 \<and> (\<forall>h'\<in>{0..h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by (auto simp: flowpipe_def)
  then show ?thesis
    unfolding flowpipe_def
    apply safe
    subgoal using subs by auto
    subgoal using subs by auto
    subgoal using subs by fastforce
    subgoal using safe by auto
    subgoal using safe by auto
    subgoal using subs by fastforce
    subgoal using subs fp by fastforce
    subgoal for x0 d0 h h'
      using subs fp
      apply -
      apply (rule subsetD, assumption)
      apply (drule bspec)
       apply (rule subsetD; assumption)
      apply safe
      apply (drule bspec[where x=h], force)
      apply auto
      done
    done
qed

lemma poincare_mapsto_unionI:
  assumes "poincare_mapsto P r U t d"
  assumes "poincare_mapsto P s U u e"
  shows "poincare_mapsto P (r \<union> s) U (t \<union> u) (d \<union> e)"
  using assms
  apply (auto simp: poincare_mapsto_def)
  subgoal
    apply (drule bspec, assumption)
    by auto
  subgoal by fastforce
  done

lemma sabove_not_le_halfspace:
  "x \<in> sabove_halfspace sctn \<longleftrightarrow> \<not> le_halfspace sctn x"
  by (auto simp: sabove_halfspace_def le_halfspace_def gt_halfspace_def)

lemma (in c1_on_open_euclidean) flowsto_self:\<comment> \<open>TODO: move!\<close>
  "0 \<in> T \<Longrightarrow> X0 \<subseteq> Z \<Longrightarrow> fst ` X0 \<subseteq> X \<Longrightarrow> flowsto X0 T Y Z"
  by (force simp: flowsto_def intro!: bexI[where x=0])

lemma (in c1_on_open_euclidean) flowpipe_imp_flowsto:\<comment> \<open>TODO: move!\<close>
  assumes "flowpipe X0 hl hu CX Y" "hl > 0"
  shows "flowsto X0 {0<..hl} CX Y"
  using assms
  by (fastforce simp: flowsto_def flowpipe_def open_segment_eq_real_ivl
      dest: bspec[where x=hl]
      intro!: bexI[where x=hl])

lemma flowsto_source_unionI:
  "flowsto X0 T A B \<Longrightarrow> flowsto Z T A B \<Longrightarrow> flowsto (X0 \<union> Z) T A B"
  by (fastforce simp: flowsto_def dest: bspec)

lemma poincare_mapsto_subset:
  "poincare_mapsto P X0 U CX1 X1 \<Longrightarrow> X0' \<subseteq> X0 \<Longrightarrow> X1 \<subseteq> X2 \<Longrightarrow> CX1 \<subseteq> CX2 \<Longrightarrow> fst ` X2 \<subseteq> Csafe
  \<Longrightarrow> poincare_mapsto P X0' U CX2 X2"
  by (force simp: poincare_mapsto_def)

lemma PDP_abs_lemma:
  fixes n::"'a::executable_euclidean_space"
  assumes "abs n \<in> Basis"
  shows
    "(x, d - (blinfun_scaleR_left (f (x)) o\<^sub>L (blinfun_scaleR_left (inverse (f x \<bullet> n)) o\<^sub>L (blinfun_inner_left n o\<^sub>L d)))) =
     (x, d - (blinfun_scaleR_left (f (x)) o\<^sub>L (blinfun_scaleR_left (inverse (f x \<bullet> (abs n))) o\<^sub>L (blinfun_inner_left (abs n) o\<^sub>L d))))"
proof -
  consider "n \<in> Basis" | "- n \<in> Basis"
    using abs_in_Basis_absE[OF assms] assms by metis
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    define i where "i = -n"
    with 2 have "i \<in> Basis" "n = -i"
      by (auto simp: )
    then show ?thesis
      by (auto simp: inverse_eq_divide intro!: blinfun_eqI blinfun.bilinear_simps euclidean_eqI[where 'a='a])
  qed
qed

lemma abs_in_BasisI:
  "\<bar>n\<bar> \<in> Basis" if n: "n \<in> Basis \<or> - n \<in> Basis" for n::"'a::executable_euclidean_space"
proof -
  consider "n \<in> Basis" | "- n \<in> Basis"
    using n by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    define i where "i = -n"
    with 2 have "i \<in> Basis" "n = -i"
      by (auto simp: )
    then show ?thesis
      by (auto simp: inverse_eq_divide intro!: blinfun_eqI blinfun.bilinear_simps euclidean_eqI[where 'a='a])
  qed
qed

lemma flowsto_poincareD:
  assumes f: "flowsto X0 T CX X1"
  assumes X1: "fst ` X1 \<subseteq> P"
  assumes P: "(P \<times> UNIV) \<inter> CX = {}" "closed P"
  assumes pos: "\<And>t. t \<in> T \<Longrightarrow> t > 0"
  assumes x0: "x0 \<in> fst ` X0"
  assumes "fst ` X1 \<subseteq> K"
  shows returns_to_flowstoI: "returns_to P x0"
    and poincare_map_mem_flowstoI: "poincare_map P x0 \<in> K"
proof -
  from x0 obtain d where x0d: "(x0, d) \<in> X0" by auto
  from flowstoE[OF f x0d] obtain h
    where h:
      "h \<in> T"
      "h \<in> existence_ivl0 x0"
      "(flow0 x0 h, Dflow x0 h o\<^sub>L d) \<in> X1"
      and CX: "\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d) \<in> CX"
    by auto
  have "h > 0" by (auto intro!: pos h)
  have "flow0 x0 h \<in> P" using X1 h by auto
  have "\<forall>\<^sub>F t in at_right 0. t \<in> {0<..<h}"
    using order_tendstoD(2)[OF tendsto_ident_at \<open>0 < h\<close>, of "{0<..}"]
    by (auto simp: eventually_at_filter)
  then have "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<in> fst ` CX"
    by eventually_elim (use CX \<open>0 < h\<close> open_segment_eq_real_ivl in auto)
  then have evnP: "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<notin> P"
    by eventually_elim (use P in force)
  from \<open>h > 0\<close> h(2) \<open>flow0 x0 h \<in> P\<close> evnP P(2) show "returns_to P x0"
    by (rule returns_toI)
  have nin_P: "0 < s \<Longrightarrow> s < h \<Longrightarrow> flow0 x0 s \<notin> P" for s
    using CX[of s] P by (auto simp: open_segment_eq_real_ivl)
  have "return_time P x0 = h"
    using h X1
    by (auto intro!: return_time_eqI \<open>0 < h\<close> h assms simp: nin_P)
  then have "poincare_map P x0 = flow0 x0 h" by (auto simp: poincare_map_def)
  also have "\<dots> \<in> fst ` X1" using h by auto
  also note \<open>_ \<subseteq> K\<close>
  finally show "poincare_map P x0 \<in> K" .
qed

lemma
  inner_abs_Basis_eq_zero_iff:
  "abs n \<in> Basis \<Longrightarrow> x \<bullet> \<bar>n\<bar> = 0 \<longleftrightarrow> x \<bullet> n = 0" for n::"'a::executable_euclidean_space"
  by (auto simp: elim!: abs_in_BasisE)

lemmas [simp] = sbelow_halfspaces_insert

lemma Int_Un_eq_emptyI: "a \<inter> (b \<union> c) = {}" if "a \<inter> b = {}" "a \<inter> c = {}"
  using that by auto

lemma cancel_times_UNIV_subset: "A \<times> UNIV \<subseteq> B \<times> UNIV \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma split_spec_coll_spec[le,refine_vcg]:
  "split_spec_coll X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_coll_def
  by (refine_vcg)

lemma Un_snd_sing_Pair_eq:
  "(e, f) \<in> a \<Longrightarrow> f \<union> (\<Union>x\<in>a - {(e, f)}. snd x) = (\<Union>x\<in>a. snd x)"
  by force

lemma let_unit: "Let X y = y ()" by simp

lemma (in c1_on_open_euclidean) flowpipe_imp_flowsto_nonneg:\<comment> \<open>TODO: move!\<close>
  assumes "flowpipe X0 hl hu CX Y"
  shows "flowsto X0 {0..} CX Y"
  using assms
  by (fastforce simp: flowsto_def flowpipe_def open_segment_eq_real_ivl
      dest: bspec[where x=hl]
      intro!: bexI[where x=hl])

lemma subset_DiffI: "A \<subseteq> B \<Longrightarrow> A \<inter> C = {} \<Longrightarrow> A \<subseteq> B - C"
  by auto

lemma flowsto_source_Union: "flowsto (\<Union>x\<in>R. X0 x) T CX X1"
  if "\<And>x. x \<in> R \<Longrightarrow> flowsto (X0 x) T CX X1"
  using that
  by (auto simp: flowsto_def)

lemma times_subset_iff: "A \<times> B \<subseteq> C \<times> E \<longleftrightarrow> A = {} \<or> B = {} \<or> A \<subseteq> C \<and> B \<subseteq> E"
  by auto

lemma
  flowsto_UnionE:
  assumes "finite Gs"
  assumes "flowsto X T CX (\<Union>Gs)"
  obtains XGs where "\<And>X G. (X, G) \<in> XGs \<Longrightarrow> flowsto X T CX G" "Gs = snd ` XGs" "X = \<Union>(fst ` XGs)"
  apply atomize_elim
  using assms
proof (induction arbitrary: X)
  case empty
  then show ?case by auto
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X = X1 \<union> X2" and X1: "flowsto X1 T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  from insert.IH[OF X2] obtain XGs where XGs:
    "\<And>X G. (X, G) \<in> XGs \<Longrightarrow> flowsto X T CX G" "F = snd ` XGs" "X2 = (\<Union>a\<in>XGs. fst a)"
    by auto
  then show ?case
    using X X1 X2
    by (intro exI[where x="insert (X1, x) XGs"]) auto
qed

lemma flowsto_Union_funE:
  assumes "finite Gs"
  assumes "flowsto X T CX (\<Union>Gs)"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G) T CX G" "X = \<Union>(f ` Gs)"
  apply atomize_elim
  using assms
proof (induction arbitrary: X)
  case empty
  then show ?case by auto
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X = X1 \<union> X2" and X1: "flowsto X1 T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  from insert.IH[OF X2] obtain f where f:
    "\<And>G. G \<in> F \<Longrightarrow> flowsto (f G) T CX G" "X2 = (\<Union>a\<in>F. f a)"
    by auto
  then show ?case
    using X X1 X2 insert.hyps
    by (intro exI[where x="f (x:=X1)"]) (auto split: if_splits)
qed

lemma flowsto_Union_Un_funE:
  assumes "flowsto X T CX (\<Union>Gs \<union> trap)"
  assumes "finite Gs" "Gs \<noteq> {}"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G) T CX (G \<union> trap)" "X = \<Union>(f ` Gs)"
proof -
  from assms have "flowsto X T CX (\<Union>g \<in> Gs. g \<union> trap)" by auto
  from flowsto_Union_funE[OF finite_imageI[OF \<open>finite Gs\<close>] this]
  obtain f where f: "\<And>G. G \<in> (\<lambda>g. g \<union> trap) ` Gs \<Longrightarrow> flowsto (f G) T CX G"
    "X = \<Union> (f ` ((\<lambda>g. g \<union> trap) ` Gs))"
    by auto
  define f' where "f' g = f (g \<union> trap)" for g
  have "G \<in> Gs \<Longrightarrow> flowsto (f' G) T CX (G \<union> trap)" for G
    using f(1)[of "G \<union> trap"]
    by (auto simp: f'_def)
  moreover
  have "X = \<Union>(f' ` Gs)"
    using f by (auto simp: f'_def)
  ultimately show ?thesis ..
qed

lemma flowsto_Diff_to_Union_funE:
  assumes "flowsto (X - trap) T CX (\<Union>Gs)"
  assumes "finite Gs"
  obtains f where "\<And>G. G \<in> Gs \<Longrightarrow> flowsto (f G - trap) T CX G" "Gs \<noteq> {} \<Longrightarrow> X = \<Union>(f ` Gs)"
  apply atomize_elim
  using assms(2,1)
proof (induction arbitrary: X)
  case empty then show ?case by simp
next
  case (insert x F)
  from insert.prems obtain X1 X2 where X: "X - trap = X1 \<union> X2" and X1: "flowsto (X1) T CX x" and X2: "flowsto X2 T CX (\<Union>F)"
    by (auto elim!: flowsto_unionE)
  then have "X1 = X1 - trap" "X2 = X2 - trap" by auto
  then have X1': "flowsto (X1 - trap) T CX x" and X2': "flowsto (X2 - trap) T CX (\<Union>F)"
    using X1 X2 by auto
  from insert.IH[OF X2'] obtain f where f: "\<And>G. G \<in> F \<Longrightarrow> flowsto (f G - trap) T CX G" "F \<noteq> {} \<Longrightarrow> X2 = (\<Union>a\<in>F. f a)"
    by auto
  show ?case
    apply (cases "F = {}")
    subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems by auto
    subgoal
      apply (rule exI[where x="f (x:=X1 \<union> (trap \<inter> X))"])
      apply auto
      subgoal
        using X1
        by (rule flowsto_subset) auto
      subgoal using X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 insert.hyps by auto
      subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems by auto
      subgoal using f X X1 X2 X1' X2' insert.hyps insert.prems insert by auto
      subgoal using f X X1 X2 insert.hyps by (auto split: if_splits)
      done
    done
qed

lemma refine_case_list[refine_vcg]:
  assumes "xs = [] \<Longrightarrow> f \<le> SPEC P"
  assumes "\<And>y ys. xs = y # ys \<Longrightarrow> g y ys \<le> SPEC P"
  shows "(case xs of [] \<Rightarrow> f | (x#xs) \<Rightarrow> g x xs) \<le> SPEC P"
  using assms
  by (auto split: list.splits)

lemma flowsto_stays_sbelow:
  assumes "flowsto X0 {0<..} CXS X1"
  assumes "fst ` X0 \<subseteq> below_halfspace sctn"
  assumes "\<And>x d. (x, d) \<in> CXS \<Longrightarrow> ode x \<bullet> normal sctn < 0"
  shows "flowsto X0 {0<..} (CXS \<inter> sbelow_halfspace sctn \<times> UNIV) X1"
  unfolding flowsto_def
proof safe
  fix x d assume "(x, d) \<in> X0"
  with assms obtain t where
    "t>0" "t \<in> existence_ivl0 x" "(\<forall>s\<in>{0<..<t}. (flow0 x s, Dflow x s o\<^sub>L d) \<in> CXS)"
    "(flow0 x t, Dflow x t o\<^sub>L d) \<in> X1"
    by (auto simp: flowsto_def subset_iff open_segment_eq_real_ivl)
  moreover
  have "\<forall>s\<in>{0<..<t}. flow0 x s \<in> sbelow_halfspace sctn"
  proof (rule ccontr, clarsimp)
    fix s assume s: "flow0 x s \<notin> sbelow_halfspace sctn" "0 < s" "s < t"
    let ?f = "\<lambda>t. flow0 x t \<bullet> normal sctn - pstn sctn"
    let ?f' = "\<lambda>t dx. dx * (ode (flow0 x t) \<bullet> normal sctn)"
    have "\<exists>xa\<in>{0<..<s}. ?f s - ?f 0 = ?f' xa (s - 0)"
      by (rule mvt[OF \<open>0 < s\<close>, of ?f ?f'])
        (use ivl_subset_existence_ivl[OF \<open>t \<in> existence_ivl0 x\<close>] \<open>0 < s\<close> \<open>s < t\<close> in
          \<open>auto intro!: continuous_intros derivative_eq_intros flow_has_derivative
            simp: flowderiv_def blinfun.bilinear_simps\<close>)
    then obtain s' where "?f s - ?f 0 = ?f' s' (s - 0)" "0 < s'" "s' < s"
      by (auto simp: algebra_simps)
    note this(1)
    also
    have "(flow0 x s', Dflow x s' o\<^sub>L d )\<in> CXS"
      using \<open>0 < s'\<close> \<open>\<forall>s\<in>{0<..<t}. _ \<in> CXS\<close> \<open>s < t\<close> \<open>s' < s\<close> by auto
    then have "?f' s' (s - 0) < 0"
      using assms \<open>(x, d) \<in> X0\<close> \<open>0 < s\<close>
      by (auto simp: flowsto_def halfspace_simps algebra_simps subset_iff intro!: mult_pos_neg)
    finally have 1: "?f s < ?f 0"
      by simp
    also have "?f 0 \<le> 0"
      using \<open>(x, d) \<in> X0\<close> assms mem_existence_ivl_iv_defined[OF \<open>t \<in> existence_ivl0 _\<close>]
      by (auto simp: halfspace_simps subset_iff)
    finally have "?f s < 0" .
    moreover from s have "0 \<le> ?f s"
      by (auto simp: halfspace_simps not_less)
    ultimately show False by simp
  qed
  ultimately
  show "\<exists>t\<in>{0<..}. t \<in> existence_ivl0 x \<and> (flow0 x t, Dflow x t o\<^sub>L d) \<in> X1 \<and>
                (\<forall>s\<in>{0<--<t}. (flow0 x s, Dflow x s o\<^sub>L d) \<in> CXS \<inter> sbelow_halfspace sctn \<times> UNIV)"
    by (auto intro!: simp: open_segment_eq_real_ivl)
qed

lemma poincare_mapsto_Union: "poincare_mapsto P (\<Union>xa) S CXS PS" 
  if "\<And>x. x \<in> xa \<Longrightarrow> poincare_mapsto P x S CXS PS"
  by (force simp: poincare_mapsto_def dest!: that)

lemma diff_subset: "(\<Union>x\<in>xa. f x) - (\<Union>x\<in>xa. g x) \<subseteq> (\<Union>x\<in>xa. f x - g x)"
  by auto

lemma poincare_mapsto_imp_flowsto:
  assumes "poincare_mapsto P X0 S CX X1"
  assumes "closed P"
  shows "flowsto X0 {0<..} (CX \<times> UNIV) (fst ` X1 \<times> UNIV)"
  unfolding flowsto_def
proof safe
  fix x0 d0 assume "(x0, d0) \<in> X0"
  with assms obtain D where D:
    "returns_to P x0"
    "fst ` X0 \<subseteq> S"
    "return_time P differentiable at x0 within S"
    "(poincare_map P has_derivative blinfun_apply D) (at x0 within S)"
    "(flow0 x0 (return_time P x0), D o\<^sub>L d0) \<in> X1"
    "\<And>t. 0 < t \<Longrightarrow> t < return_time P x0 \<Longrightarrow> flow0 x0 t \<in> CX"
    by (auto simp: poincare_mapsto_def poincare_map_def)
  show "\<exists>h\<in>{0<..}.
    h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> fst ` X1 \<times> UNIV \<and>
    (\<forall>h'\<in>{0<--<h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX \<times> UNIV)"
    by (auto intro!: bexI[where x="return_time P x0"] return_time_exivl D assms return_time_pos
        simp: open_segment_eq_real_ivl)
qed

lemma flowsto_poincare_mapsto_trans_flowsto:
  assumes "flowsto X0 T CX X1'"
  assumes "poincare_mapsto P X1 S CY X2"
  assumes "closed P"
  assumes "fst ` X1' \<subseteq> fst ` X1"
  assumes "X1' \<union> CX \<union> CY \<times> UNIV \<subseteq> CZ"
  assumes "\<And>t. t \<in> T \<Longrightarrow> t \<ge> 0"
  shows "flowsto X0 {0<..} CZ (fst ` X2 \<times> UNIV)"
proof -
  have X1D: "(a, b) \<in> X1' \<Longrightarrow> \<exists>c. (a, c) \<in> X1" for a b using assms(4) by force
  from poincare_mapsto_imp_flowsto[OF assms(2,3)]
  have "flowsto X1 {0<..} (CY \<times> UNIV) (fst ` X2 \<times> UNIV)" .
  then have "flowsto X1' {0<..} (CY \<times> UNIV) (fst ` X2 \<times> UNIV)"
    by (auto simp: flowsto_def dest!: X1D)
  from flowsto_trans[OF assms(1) this]
  show ?thesis
    apply (rule flowsto_subset)
    using assms
    by (auto intro!: add_nonneg_pos)
qed

lemma eq_blinfun_inner_left[intro]:
  "(\<lambda>x. x \<bullet> n) = blinfun_apply (blinfun_inner_left n)"
  by force

lemma flowsto_union_DiffE:
  assumes "flowsto X0 T CX (Y \<union> Z)"
  obtains X1 where "X1 \<subseteq> X0" "flowsto X1 T CX Y" "flowsto (X0 - X1) T CX Z"
proof -
  let ?X1 = "{x\<in>X0. flowsto {x} T CX Y}"
  from assms have "?X1 \<subseteq> X0" "flowsto ?X1 T CX Y" "flowsto (X0 - ?X1) T CX Z"
    by (auto simp: flowsto_def)
  thus ?thesis ..
qed

lemma eucl_less_le_trans:
  fixes a b::"'a::executable_euclidean_space"
  shows "eucl_less a b \<Longrightarrow> b \<le> c \<Longrightarrow> eucl_less a c"
  by (force simp: eucl_less_def[where 'a='a] eucl_le[where 'a='a])

lemma le_eucl_less_trans:
  fixes a b::"'a::executable_euclidean_space"
  shows "a \<le> b \<Longrightarrow> eucl_less b c \<Longrightarrow> eucl_less a c"
  by (force simp: eucl_less_def[where 'a='a] eucl_le[where 'a='a])

lemma flowsto_source_UnionI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> flowsto i T CXS (f i)"
  shows "flowsto (\<Union>I) T CXS (\<Union>(f ` I))"
  apply (auto simp: flowsto_def)
  subgoal premises prems for y a b
    using assms[unfolded flowsto_def, OF \<open>y \<in> I\<close>, rule_format, OF \<open>_ \<in> y\<close>] prems
    by auto
  done

lemma poincare_mapsto_UnionI:
  assumes pm[unfolded poincare_mapsto_def, rule_format]: "\<And>i. i \<in> I \<Longrightarrow> poincare_mapsto p (X0 i) S (CX i) (X1 i)"
  assumes R: "\<And>i x. i \<in> I \<Longrightarrow> x \<in> X1 i \<Longrightarrow> x \<in> R"
  shows "poincare_mapsto p (\<Union>x\<in>I. X0 x) S ((\<Union>x\<in>I. CX x)) R"
  unfolding poincare_mapsto_def
proof (safe del: conjI, goal_cases)
  case (1 x0 d0 i)
  moreover
  have "fst ` \<Union>(X0 ` I) \<subseteq> S"
    proof (safe, goal_cases)
      case (1 _ x0 d0 i)
      from this pm[OF 1]
      show ?case by auto
    qed
  ultimately show ?case using pm[OF 1]
    by (auto intro!: R)
qed

lemma tendsto_at_top_translateI:
  assumes "(f \<longlongrightarrow> l) (at_top::real filter)"
  shows "((\<lambda>x. f (x + t)::'a::topological_space) \<longlongrightarrow> l) at_top"
proof (rule topological_tendstoI)
  fix S::"'a set" assume "open S" "l \<in> S"
  from topological_tendstoD[OF assms this]
  obtain N where "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> S" by (auto simp: eventually_at_top_linorder)
  then have "\<And>n. n \<ge> N - t \<Longrightarrow> f (n + t) \<in> S" by auto
  then show "\<forall>\<^sub>F x in at_top. f (x + t) \<in> S"
    unfolding eventually_at_top_linorder
    by blast
qed

lemma tendsto_at_top_translate_iff:
  "((\<lambda>x. f (x + t)::'a::topological_space) \<longlongrightarrow> l) at_top \<longleftrightarrow> (f \<longlongrightarrow> l) (at_top::real filter)"
  using tendsto_at_top_translateI[of f l t]
    tendsto_at_top_translateI[of "\<lambda>x. f (x + t)" l "- t"]
  by auto

lemma stable_on_mono:
  "stable_on A B" if "stable_on C B" "A \<subseteq> C"
  using that
  unfolding stable_on_def
  by fastforce

lemma
  flowsto_mapsto_avoid_trap:
  assumes "flowsto (X0 - trap \<times> UNIV) {0<..} CX P"
  assumes trapprop: "stable_on (fst ` (CX \<union> P)) trap"
  shows "flowsto (X0 - trap \<times> UNIV) {0<..} CX (P - trap \<times> UNIV)"
  unfolding flowsto_def
proof (rule, goal_cases)
  case (1 xd)
  from assms(1)[unfolded flowsto_def, rule_format, OF this] obtain h x0 d0 where
    "xd = (x0, d0)" "0 < h"
    "h \<in> existence_ivl0 (x0)"
    "(flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> P"
    "(\<forall>h'\<in>{0<--<h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by auto
  then show ?case
    using 1 trapprop
    apply (auto intro!: bexI[where x=h] dest!: stable_onD simp: open_segment_eq_real_ivl image_Un)
    subgoal for s by (cases "s = h") auto
    done
qed

end

lemma map_prod_def': "map_prod f g x = (f (fst x), g (snd x))"
  by (cases x) auto

lemmas rel_prod_br = br_rel_prod

lemmas lvivl_relI = lv_relivl_relI

end
