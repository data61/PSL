theory Example_Utilities
imports
  Init_ODE_Solver
begin

definition "true_form = Less (floatarith.Num 0) (floatarith.Num 1)"

lemma open_true_form[intro, simp]: "open_form true_form"
  by (auto simp: true_form_def)

lemma max_Var_form_true_form[simp]: "max_Var_form true_form = 0"
  by (auto simp: true_form_def)

lemma interpret_form_true_form[simp]: "interpret_form true_form = (\<lambda>_. True)"
  by (auto simp: true_form_def)

lemmas [simp] = length_aforms_of_ivls

declare INF_cong_simp [cong] SUP_cong_simp [cong] image_cong_simp [cong del]

declare [[ cd_patterns "_ = interpret_floatariths ?fas _" "_ = interpret_floatarith ?fa _"]]

concrete_definition reify_example for i j k uses reify_example

hide_const (open) Print.file_output
definition "file_output s f =
  (if s = STR ''''      then f (\<lambda>_. ())
  else if s = STR ''-'' then f print
  else                                  Print.file_output s f)"

definition "aforms_of_point xs = aforms_of_ivls xs xs"

definition "unit_matrix_list D = concat (map (\<lambda>i. map (\<lambda>j. if i = j then 1 else 0::real) [0..<D]) [0..<D])"

definition "with_unit_matrix D X = (fst X @ unit_matrix_list D, snd X @ unit_matrix_list D)"

definition "list_interval l u = {x. list_all2 (\<le>) l x \<and> list_all2 (\<le>) x u}"

context includes lifting_syntax begin
lemma list_interval_transfer[transfer_rule]:
  "((list_all2 A) ===> (list_all2 A) ===> rel_set (list_all2 A))
    list_interval list_interval"
  if [transfer_rule]: "(A ===> A ===> (=)) (\<le>) (\<le>)" "bi_total A"
  unfolding list_interval_def
  by transfer_prover
end

lemma in_list_interval_lengthD: "x \<in> list_interval a b \<Longrightarrow> length x = length a"
  by (auto simp: list_interval_def list_all2_lengthD)

context includes floatarith_notation begin

definition "varvec_fas' D C = ((map Var [0..<D]) @
      concat (map (\<lambda>b.
        (map (\<lambda>i. (Num (C i)) +
          Var (D + D * D) * (mvmult_fa D D (map Var [D..<D + D * D]) (map Num ((replicate D 0)[i:=1])) ! b)) [0..<D])) [0..<D]))"

definition "varvec_fas D C = ((map Var [0..<D]) @
      concat (map (\<lambda>i. (map (\<lambda>j. (Num (C i)) + Var (D + D * D) * Var (D + D * i + j)) [0..<D])) [0..<D]))"

lemma \<comment> \<open>for illustration\<close>
  assumes[simp]: "D=3" "rf = real_of_float"
  shows "interpret_floatariths (varvec_fas D (\<lambda>i. [a, b, c] ! i))
  [a, b, c, d11, d12, d13,
            d21, d22, d23,
            d31, d32, d33, 2] =
  [rf a, rf b, rf c,
  rf a + 2 * rf d11, rf a + 2 * rf d12, rf a + 2 * rf d13,
  rf b + 2 * rf d21, rf b + 2 * rf d22, rf b + 2 * rf d23,
  rf c + 2 * rf d31, rf c + 2 * rf d32, rf c + 2 * rf d33]"
  by (simp add: varvec_fas_def mvmult_fa_def eval_nat_numeral)

definition "vareq_projections
    n  \<comment> \<open>dimension\<close>
    ps \<comment> \<open>pairs of coordinates to project onto\<close>
    ds \<comment> \<open>partial derivatives w.r.t. which variables\<close>
    cs \<comment> \<open>(color) coding for partial derivatives\<close>
  =
  [(i + n * (x + 1)::nat, i + n * (y + 1), c). (i, c) \<leftarrow> zip ds cs, (x, y) \<leftarrow> ps]"

definition "varvec_aforms_line D X line =
  approx_floatariths
    30
    (varvec_fas D (\<lambda>i. float_of (fst (X ! i))))
    (take (D + D*D) X @ line)"

definition "varvec_aforms_head D X s = varvec_aforms_line D X (aforms_of_point [s])"
definition "varvec_aforms_vec D X s = varvec_aforms_line D (map (\<lambda>x. (fst x, zero_pdevs)) X) [aform_of_ivl 0 s]"

definition
  "shows_aforms_vareq
      n                \<comment> \<open>dimension\<close>
      ps               \<comment> \<open>pairs of coordinates to project onto\<close>
      ds               \<comment> \<open>partial derivatives w.r.t. which variables\<close>
      csl              \<comment> \<open>color coding for partial derivatives ('arrow' heads)\<close>
      csh              \<comment> \<open>color coding for partial derivatives (lines)\<close>
      s                \<comment> \<open>scale vectors for partial derivatives\<close>
      (no_str::string) \<comment> \<open>default string if no C1 info is present\<close>
      X                \<comment> \<open>affine form with C1 info\<close>
   =
    (case (varvec_aforms_head n X s, varvec_aforms_vec n X s) of (Some X, Some Y) \<Rightarrow>
        shows_sep (\<lambda>(x, y, c). shows_segments_of_aform x y X c) shows_nl (vareq_projections n ps ds csl) o shows_nl
      o shows_sep (\<lambda>(x, y, c). shows_segments_of_aform x y Y c) shows_nl (vareq_projections n ps ds csh) o shows_nl
    | _ \<Rightarrow> shows_string no_str o shows_nl)"

abbreviation "print_string s \<equiv> print (String.implode s)"
abbreviation "print_show s \<equiv> print_string (s '''')"

value [code] "print_show (shows_aforms_vareq 3 [(x, y). x \<leftarrow> [0..<3], y \<leftarrow> [0..<3], x < y]
  [0..<3] [''0x0000ff'', ''0x00ff00'', ''0xff0000''] [''0x0000ff'', ''0x00ff00'', ''0xff0000'']
  (FloatR 1 (-1)) ''# no C1 info''
    ((((\<lambda>(a, b). aforms_of_ivls a b) (with_unit_matrix 3 ([10, 20, 30], [12, 22, 32]))))))"

method_setup guess_rhs = \<open>
let
  fun compute ctxt var lhs =
    let
      val lhs' = Code_Evaluation.dynamic_value_strict ctxt lhs;
      val clhs' = Thm.cterm_of ctxt lhs';
      val inst = Thm.instantiate ([], [(var, clhs')]);
    in PRIMITIVE inst end;
  fun eval_schematic_rhs ctxt t = (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) t of
      SOME (lhs, Var var) => compute ctxt var lhs
    | _ => no_tac);
in
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (HEADGOAL (SUBGOAL (fn (t, _) => eval_schematic_rhs ctxt t))))
end
\<close>

lemma length_aforms_of_point[simp]: "length (aforms_of_point xs) = length xs"
  by (auto simp: aforms_of_point_def)

definition "aform2d_plot_segments x y a = shows_segments_of_aform x y a ''0x000000''"

lemma list_of_eucl_prod[simp]: "list_of_eucl (x, y) = list_of_eucl x @ list_of_eucl y"
  by (auto simp: list_of_eucl_def Basis_list_prod_def intro!: nth_equalityI)

lemma list_of_eucl_real[simp]: "list_of_eucl (x::real) = [x]"
  by (auto simp: list_of_eucl_def Basis_list_real_def)

lemma Joints_aforms_of_ivls_self[simp]: "xs \<in> Joints (aforms_of_ivls xs xs)"
  by (auto intro!: aforms_of_ivls)

lemma Joints_aforms_of_ivls_self_eq[simp]: "Joints (aforms_of_ivls xs xs) = {xs}"
  apply (auto )
  by (auto simp: aforms_of_ivls_def Joints_def valuate_def aform_val_def
      intro!: nth_equalityI)

lemma local_lipschitz_c1_euclideanI:
  fixes T::"real set" and X::"'a::euclidean_space set"
    and f::"real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f': "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> (f t has_derivative f' t x) (at x)"
  assumes cont_f': "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on (T \<times> X) (\<lambda>(t, x). f' t x i)"
  assumes "open T"
  assumes "open X"
  shows "local_lipschitz T X f"
  using assms
  apply (intro c1_implies_local_lipschitz[where f'="\<lambda>(t, x). Blinfun (f' t x)"])
     apply (auto simp: bounded_linear_Blinfun_apply has_derivative_bounded_linear split_beta'
      intro!: has_derivative_Blinfun continuous_on_blinfun_componentwise)
  apply (subst continuous_on_cong[OF refl]) defer apply assumption
  apply auto
  apply (subst bounded_linear_Blinfun_apply)
   apply (rule has_derivative_bounded_linear)
  by auto

definition "list_aform_of_aform (x::real aform) = (fst x, list_of_pdevs (snd x))"
primrec split_aforms_list:: "(real aform) list list
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real aform) list list" where
  "split_aforms_list Xs i 0 = Xs"
| "split_aforms_list Xs i (Suc n) = split_aforms_list (concat (map (\<lambda>x. (let (a, b) = split_aforms x i in [a, b])) Xs)) i n"

definition "shows_aforms x y c X = shows_lines (map (\<lambda>b. (shows_segments_of_aform x y b c ''\<newline>'')) X)"

end

definition "the_odo ode_fas safe_form = the(mk_ode_ops ode_fas safe_form)"

locale ode_interpretation =
  fixes safe_form::form and safe_set::"'a::executable_euclidean_space set"
    and ode_fas::"floatarith list"
    and ode::"'a \<Rightarrow> 'a"
    and finite::"'n::enum"
  assumes dims: "DIM('a) = CARD('n)"
  assumes len: "length ode_fas = CARD('n)"
  assumes safe_set_form: "safe_set = {x. interpret_form safe_form (list_of_eucl x)}"
  assumes interpret_fas: "\<And>x. x \<in> safe_set \<Longrightarrow> einterpret ode_fas (list_of_eucl x) = ode x"
  assumes odo: "mk_ode_ops ode_fas safe_form \<noteq> None"
  assumes isFDERIV: "\<And>xs. interpret_form safe_form xs \<Longrightarrow>
    isFDERIV (length ode_fas) [0..<length ode_fas] ode_fas xs"
begin

abbreviation "odo \<equiv> the_odo ode_fas safe_form"
lemmas odo_def = the_odo_def

lemma odo_simps[simp]: "ode_expression odo = ode_fas" "safe_form_expr odo = safe_form"
  using odo
  by (auto simp: odo_def ode_expression_mk_ode_ops safe_form_expr_mk_ode_ops)

lemma safe_set: "safe_set = aform.Csafe odo"
  using odo dims safe_set_form isFDERIV
  unfolding aform.Csafe_def aform.safe_def aform.safe_form_def aform.ode_e_def
  by (auto simp: mk_ode_ops_def safe_set_form len split: if_splits)

lemma ode: "\<And>x. x \<in> safe_set \<Longrightarrow> ode x = aform.ode odo x"
  by (auto simp: aform.ode_def aform.ode_e_def interpret_fas)

sublocale auto_ll_on_open ode safe_set
  by (rule aform.auto_ll_on_open_congI[OF safe_set[symmetric] ode[symmetric]])

lemma ode_has_derivative_ode_d1: "(ode has_derivative blinfun_apply (aform.ode_d1 odo x)) (at x)"
  if "x \<in> safe_set" for x
proof -
  from aform.fderiv[OF that[unfolded safe_set]]
  have "(aform.ode odo has_derivative blinfun_apply (aform.ode_d1 odo x)) (at x)"
    by simp
  moreover
  from topological_tendstoD[OF tendsto_ident_at open_domain(2) that]
  have "\<forall>\<^sub>F x' in at x. x' \<in> safe_set" .
  then have "\<forall>\<^sub>F x' in at x. aform.ode odo x' = ode x'"
    by eventually_elim (auto simp: ode)
  ultimately show ?thesis
    by (rule has_derivative_transform_eventually) (auto simp: ode that)
qed

sublocale c1_on_open_euclidean ode "aform.ode_d1 odo" safe_set
  apply unfold_locales
  subgoal by simp
  subgoal by (simp add: ode_has_derivative_ode_d1)
  subgoal by (rule aform.cont_fderiv') (auto intro!: continuous_intros simp: safe_set)
  done

sublocale transfer_eucl_vec for a::'a and n::'n
  by unfold_locales (simp add: dims)

lemma flow_eq: "t \<in> existence_ivl0 x \<Longrightarrow> aform.flow0 odo x t = flow0 x t"
  and Dflow_eq: "t \<in> existence_ivl0 x \<Longrightarrow> aform.Dflow odo x t = Dflow x t"
  and ex_ivl_eq: "t \<in> aform.existence_ivl0 odo x \<Longrightarrow> aform.existence_ivl0 odo x = existence_ivl0 x"
  and poincare_mapsto_eq: "closed a \<Longrightarrow> aform.poincare_mapsto odo a b c d e = poincare_mapsto a b c d e"
  and flowsto_eq: "aform.flowsto odo = flowsto"
      apply -
  subgoal by (rule flow0_cong[symmetric]) (auto simp: safe_set ode)
  subgoal by (rule Dflow_cong[symmetric]) (auto simp: safe_set ode)
  subgoal by (rule existence_ivl0_cong[symmetric]) (auto simp: safe_set ode)
  subgoal
    apply (subst aform.poincare_mapsto_cong[OF safe_set[symmetric]])
    by (auto simp: ode)
  subgoal
    apply (intro ext)
    apply (subst flowsto_congI[OF safe_set ode])
    by (auto simp: safe_set)
  done

definition "avf \<equiv> \<lambda>x::'n rvec. cast (aform.ode odo (cast x)::'a)::'n rvec"

context includes lifting_syntax begin
lemma aform_ode_transfer[transfer_rule]: "((=) ===> rel_ve ===> rel_ve) aform.ode aform.ode"
  unfolding aform.ode_def
  by transfer_prover
lemma cast_aform_ode: "cast (aform.ode odo (cast (x::'n rvec))::'a) = aform.ode odo x"
  by transfer simp

lemma aform_safe_transfer[transfer_rule]: "((=) ===> rel_ve ===> (=)) aform.safe aform.safe"
  unfolding aform.safe_def
  by transfer_prover

lemma aform_Csafe_transfer[transfer_rule]: "((=) ===> rel_set rel_ve) aform.Csafe aform.Csafe"
  unfolding aform.Csafe_def
  by transfer_prover

lemma cast_safe_set: "(cast ` safe_set::'n rvec set) = aform.Csafe odo"
  unfolding safe_set
  by transfer simp

lemma aform_ode_d_raw_transfer[transfer_rule]:
  "((=) ===> (=) ===> rel_ve ===> rel_ve ===> rel_ve ===> rel_ve) aform.ode_d_raw aform.ode_d_raw"
  unfolding aform.ode_d_raw_def
  by transfer_prover

lemma
  aform_ode_d_raw_aux_transfer:
  "((=) ===> rel_ve ===> rel_ve ===> rel_ve)
    (\<lambda>x xb xa. if xb \<in> aform.Csafe x then aform.ode_d_raw x 0 xb 0 xa else 0)
    (\<lambda>x xb xa. if xb \<in> aform.Csafe x then aform.ode_d_raw x 0 xb 0 xa else 0)"
  by transfer_prover

lemma aform_ode_d1_transfer[transfer_rule]:
  "((=) ===> rel_ve ===> rel_blinfun rel_ve rel_ve) aform.ode_d1 aform.ode_d1"
  apply (auto simp: rel_blinfun_def aform.ode_d1_def intro!: rel_funI)
  unfolding aform.ode_d.rep_eq
  using aform_ode_d_raw_aux_transfer
  apply -
  apply (drule rel_funD, rule refl)
  apply (drule rel_funD, assumption)
  apply (drule rel_funD; assumption)
  done

lemma cast_bl_transfer[transfer_rule]:
  "(rel_blinfun (=) (=) ===> rel_blinfun rel_ve rel_ve) id_blinfun cast_bl"
  by (auto simp: rel_ve_cast rel_blinfun_def intro!: rel_funI dest!: rel_funD)
lemma cast_bl_transfer'[transfer_rule]:
  "(rel_blinfun rel_ve rel_ve ===> rel_blinfun (=) (=)) id_blinfun cast_bl"
  apply (auto simp: rel_ve_cast rel_blinfun_def cast_cast intro!: rel_funI dest!: rel_funD)
  by (subst cast_cast) auto

lemma rel_blinfun_eq[relator_eq]: "rel_blinfun (=) (=) = (=)"
  by (auto simp: Rel_def rel_blinfun_def blinfun_ext rel_fun_eq intro!: rel_funI ext)

lemma cast_aform_ode_D1:
  "cast_bl (aform.ode_d1 odo (cast (x::'n rvec))::'a\<Rightarrow>\<^sub>L'a) =
    (aform.ode_d1 odo x::'n rvec \<Rightarrow>\<^sub>L 'n rvec)"
  by transfer simp

end

definition "vf \<equiv> \<lambda>x. cast (ode (cast x))"
definition "vf' \<equiv> \<lambda>x::'n rvec. cast_bl (aform.ode_d1 odo (cast x::'a))
  ::'n rvec \<Rightarrow>\<^sub>L 'n rvec"
definition "vX \<equiv> cast ` safe_set"
sublocale a?: transfer_c1_on_open_euclidean a n ode "aform.ode_d1 odo" safe_set vf vf' vX
  for a::'a and n::'n
  by unfold_locales
    (simp_all add: dims vf_def vf'_def vX_def)

sublocale av: transfer_c1_on_open_euclidean a n "aform.ode odo" "aform.ode_d1 odo"
  "(aform.Csafe odo)" avf vf' vX
  for a::'a and n::'n
     apply unfold_locales
  unfolding vX_def
  by (simp_all add: dims avf_def  safe_set)

lemma vflow_eq: "t \<in> v.existence_ivl0 x \<Longrightarrow> aform.flow0 odo x t = v.flow0 x t"
  thm flow_eq[of t "cast x"] flow_eq[of t "cast x", untransferred]
  apply (subst flow_eq[of t "cast x", untransferred, symmetric])
   apply simp
  unfolding avf_def vX_def cast_aform_ode cast_safe_set
  ..

lemma vf'_eq: "vf' = aform.ode_d1 odo"
  unfolding vf'_def cast_aform_ode_D1 ..

lemma vDflow_eq: "t \<in> v.existence_ivl0 x \<Longrightarrow> aform.Dflow odo x t = v.Dflow x t"
  apply (subst Dflow_eq[of t "cast x", untransferred, symmetric])
   apply simp
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  ..

lemma vex_ivl_eq: "t \<in> aform.existence_ivl0 odo x \<Longrightarrow> aform.existence_ivl0 odo x = v.existence_ivl0 x"
  apply (subst ex_ivl_eq[of t "cast x", untransferred, symmetric])
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  by auto

context includes lifting_syntax begin
lemma id_cast_eucl1_transfer_eq: "(\<lambda>x. x) = (\<lambda>x. (fst x, 1\<^sub>L o\<^sub>L snd x o\<^sub>L 1\<^sub>L))"
  by auto
lemma cast_eucl1_transfer[transfer_rule]:
  "(rel_prod (=) (rel_blinfun (=) (=)) ===> rel_prod rel_ve (rel_blinfun rel_ve rel_ve)) (\<lambda>x. x) cast_eucl1"
  unfolding cast_eucl1_def id_cast_eucl1_transfer_eq
  apply transfer_prover_start
       apply (transfer_step)
      apply (transfer_step)
     apply (transfer_step)
    apply (transfer_step)
   apply (transfer_step)
  apply simp
  done

end

lemma avpoincare_mapsto_eq:
  "aform.poincare_mapsto odo a (b::'n eucl1 set) c d e = av.v.poincare_mapsto a b c d e"
  if "closed a"
  unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
  by auto

lemma vpoincare_mapsto_eq:
  "aform.poincare_mapsto odo a (b::'n eucl1 set) c d e = v.poincare_mapsto a b c d e"
  if "closed a"
proof -
  have "closed (cast ` a::'a set)" using that
    by transfer auto
  from poincare_mapsto_eq[of "cast ` a::'a set"
      "cast_eucl1 ` b::('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set"
      "cast ` c::'a set" "cast ` d::'a set" "cast_eucl1 ` e::('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set", OF this, untransferred]
  have "v.poincare_mapsto a b c d e = av.v.poincare_mapsto a b c d e"
    by auto
  also have "\<dots> = aform.poincare_mapsto odo a (b::'n eucl1 set) c d e"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  finally show ?thesis by simp
qed

lemma avflowsto_eq: "aform.flowsto odo = (av.v.flowsto::'n eucl1 set \<Rightarrow> _)"
proof (intro ext, goal_cases)
  case (1 a b c d)
  have "av.v.flowsto a b c d = aform.flowsto odo a b c d"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  then show ?case by simp
qed

lemma vflowsto_eq: "aform.flowsto odo = (v.flowsto::'n eucl1 set \<Rightarrow> _)"
proof (intro ext, goal_cases)
  case (1 a b c d)
  have "aform.flowsto odo (cast_eucl1 ` a::'a c1_info set) b
    (cast_eucl1 ` c)  (cast_eucl1 ` d) =
    flowsto (cast_eucl1 ` a::'a c1_info set) b (cast_eucl1 ` c)  (cast_eucl1 ` d)"
    by (subst flowsto_eq) auto
  from this[untransferred] have "v.flowsto a b c d = av.v.flowsto a b c d" by auto
  also have "\<dots> = aform.flowsto odo a b c d"
    unfolding avf_def vX_def cast_aform_ode cast_safe_set vf'_eq
    by auto
  finally show ?case by simp
qed

context includes lifting_syntax begin
lemma flow1_of_list_transfer[transfer_rule]:
  "(list_all2 (=) ===> rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   flow1_of_list flow1_of_list"
  unfolding flow1_of_list_def blinfun_of_list_def o_def flow1_of_vec1_def
  by transfer_prover

lemma c1_info_of_appr_transfer[transfer_rule]:
  "(rel_prod (list_all2 (=)) (rel_option (list_all2 (=))) ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appr
    aform.c1_info_of_appr"
  unfolding aform.c1_info_of_appr_def
  by transfer_prover

lemma c0_info_of_appr_transfer[transfer_rule]:
  "((list_all2 (=)) ===> rel_set rel_ve) aform.c0_info_of_appr aform.c0_info_of_appr"
  unfolding aform.c0_info_of_appr_def
  by transfer_prover

lemma aform_scaleR2_transfer[transfer_rule]:
  "((=) ===> (=) ===> rel_set (rel_prod A B) ===> rel_set (rel_prod A B))
    scaleR2 scaleR2"
  if [unfolded Rel_def, transfer_rule]: "((=) ===> B ===> B) (*\<^sub>R) (*\<^sub>R)"
  unfolding scaleR2_def
  by transfer_prover
lemma scaleR_rel_blinfun_transfer[transfer_rule]: "((=) ===> rel_blinfun rel_ve rel_ve ===> rel_blinfun rel_ve rel_ve) (*\<^sub>R) (*\<^sub>R)"
  apply (auto intro!: rel_funI simp: rel_blinfun_def blinfun.bilinear_simps)
  apply (drule rel_funD)
   apply assumption
  apply (rule scaleR_transfer[THEN rel_funD, THEN rel_funD])
   apply auto
  done
lemma c1_info_of_appre_transfer[transfer_rule]:
  "(rel_prod (rel_prod (=) (=)) (rel_prod (list_all2 (=)) (rel_option (list_all2 (=)))) ===>
      rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appre
    aform.c1_info_of_appre"
  unfolding aform.c1_info_of_appre_def
  by transfer_prover

lemma c1_info_of_apprs_transfer[transfer_rule]:
  "((=) ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_apprs
    aform.c1_info_of_apprs"
  unfolding aform.c1_info_of_apprs_def
  by transfer_prover
lemma c1_info_of_appr'_transfer[transfer_rule]:
  "(rel_option (list_all2 (=)) ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_appr' aform.c1_info_of_appr'"
  unfolding aform.c1_info_of_appr'_def
  by transfer_prover

lemma c0_info_of_apprs_transfer[transfer_rule]:
  "((=) ===> rel_set rel_ve)
    aform.c0_info_of_apprs
    aform.c0_info_of_apprs"
  unfolding aform.c0_info_of_apprs_def
  by transfer_prover
lemma c0_info_of_appr'_transfer[transfer_rule]:
  "(rel_option (list_all2 (=)) ===> rel_set rel_ve)
    aform.c0_info_of_appr' aform.c0_info_of_appr'"
  unfolding aform.c0_info_of_appr'_def
  by transfer_prover

lemma aform_Csafe_vX[simp]: "aform.Csafe odo = (vX::'n rvec set)"
  by (simp add: vX_def cast_safe_set)

definition blinfuns_of_lvivl::"real list \<times> real list \<Rightarrow> ('b \<Rightarrow>\<^sub>L 'b::executable_euclidean_space) set"
  where "blinfuns_of_lvivl x = blinfun_of_list ` list_interval (fst x) (snd x)"

lemma blinfun_of_list_transfer[transfer_rule]:
  "(list_all2 (=) ===> rel_blinfun rel_ve rel_ve) blinfun_of_list blinfun_of_list"
  unfolding blinfun_of_list_def
  by transfer_prover

lemma blinfuns_of_lvivl_transfer[transfer_rule]:
  "(rel_prod (list_all2 (=)) (list_all2 (=)) ===> rel_set (rel_blinfun rel_ve rel_ve))
    blinfuns_of_lvivl
    blinfuns_of_lvivl"
  unfolding blinfuns_of_lvivl_def
  by transfer_prover

definition "blinfuns_of_lvivl' x = (case x of None \<Rightarrow> UNIV | Some x \<Rightarrow> blinfuns_of_lvivl x)"

lemma blinfuns_of_lvivl'_transfer[transfer_rule]:
  "(rel_option (rel_prod (list_all2 (=)) (list_all2 (=))) ===> rel_set (rel_blinfun rel_ve rel_ve))
    blinfuns_of_lvivl'
    blinfuns_of_lvivl'"
  unfolding blinfuns_of_lvivl'_def
  by transfer_prover


lemma atLeastAtMost_transfer[transfer_rule]:
  "(A ===> A ===> rel_set A) atLeastAtMost atLeastAtMost"
  if [transfer_rule]: "(A ===> A ===> (=)) (\<le>) (\<le>)" "bi_total A" "bi_unique A"
  unfolding atLeastAtMost_def atLeast_def atMost_def
  by transfer_prover

lemma set_of_ivl_transfer[transfer_rule]:
  "(rel_prod A A ===> rel_set A) set_of_ivl set_of_ivl"
  if [transfer_rule]: "(A ===> A ===> (=)) (\<le>) (\<le>)" "bi_total A" "bi_unique A"
  unfolding set_of_ivl_def
  by transfer_prover

lemma set_of_lvivl_transfer[transfer_rule]:
  "(rel_prod (list_all2 (=)) (list_all2 (=)) ===> rel_set rel_ve) set_of_lvivl set_of_lvivl"
  unfolding set_of_lvivl_def
  by transfer_prover

lemma set_of_lvivl_eq: "set_of_lvivl I =
    (eucl_of_list ` list_interval (fst I) (snd I)::'b::executable_euclidean_space set)"
  if [simp]: "length (fst I) = DIM('b)" "length (snd I) = DIM('b)"
proof (auto simp: set_of_lvivl_def list_interval_def set_of_ivl_def, goal_cases)
  case (1 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of  "fst I" "list_of_eucl x"]
    lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of "list_of_eucl x" "snd I"]
  show ?case by force
next
  case (2 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of  "fst I" "x"]
  show ?case by (auto simp: list_all2_lengthD)
next
  case (3 x)
  with lv_rel_le[where 'a='b, param_fo, OF lv_relI lv_relI, of "x" "snd I"]
  show ?case by (auto simp: list_all2_lengthD)
qed

lemma bounded_linear_matrix_vector_mul[THEN bounded_linear_compose, bounded_linear_intros]:
  "bounded_linear ((*v) x)" for x::"real^'x^'y"
  unfolding linear_linear
  by (rule matrix_vector_mul_linear)

lemma blinfun_of_list_eq: "blinfun_of_list x = blinfun_of_vmatrix (eucl_of_list x::((real, 'b) vec, 'b) vec)"
  if "length x = CARD('b::enum)*CARD('b)"
  unfolding blinfun_of_list_def
  apply (transfer fixing: x)
  apply (rule linear_eq_stdbasis)
  unfolding linear_conv_bounded_linear
    apply (auto intro!: bounded_linear_intros)
proof goal_cases
  case (1 b)
  have "(eucl_of_list x::((real, 'b) vec, 'b) vec) *v b = (eucl_of_list x::((real, 'b) vec, 'b) vec) *v eucl_of_list (list_of_eucl b)"
    by simp
  also have "\<dots> = (\<Sum>i<CARD('b).
        (\<Sum>j<CARD('b). x ! (i * CARD('b) + j) * (b \<bullet> Basis_list ! j)) *\<^sub>R Basis_list ! i)"
    by (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
      (auto simp: that)
  also have "\<dots> = (\<Sum>i\<in>Basis.
       \<Sum>j\<in>Basis. (b \<bullet> j * x ! (index Basis_list i * CARD('b) + index Basis_list j)) *\<^sub>R i)"
    apply (subst sum_list_Basis_list[symmetric])+
    apply (subst sum_list_sum_nth)+
    by (auto simp add: atLeast0LessThan scaleR_sum_left intro!: sum.cong)
  finally show ?case by simp
qed

lemma blinfuns_of_lvivl_eq: "blinfuns_of_lvivl x =
    (blinfun_of_vmatrix ` set_of_lvivl x::((real, 'b) vec \<Rightarrow>\<^sub>L (real, 'b) vec) set)"
  if "length (fst x) = CARD('b::enum)*CARD('b)" "length (snd x) = CARD('b)*CARD('b)"
  apply (subst set_of_lvivl_eq)
  subgoal by (simp add: that)
  subgoal by (simp add: that)
  unfolding blinfuns_of_lvivl_def image_image
  by (auto simp: that blinfun_of_list_eq[symmetric] in_list_interval_lengthD cong: image_cong)

lemma range_blinfun_of_vmatrix[simp]: "range blinfun_of_vmatrix = UNIV"
  apply auto
  apply transfer
  subgoal for x by (rule image_eqI[where x="matrix x"]) auto
  done

lemma blinfun_of_vmatrix_image:
  "blinfun_of_vmatrix ` aform.set_of_lvivl' x =
    (blinfuns_of_lvivl' x::((real, 'b) vec \<Rightarrow>\<^sub>L (real, 'b) vec) set)"
  if "aform.lvivl'_invar (CARD('b)*CARD('b::enum)) x"
  using that
  by (auto simp: aform.set_of_lvivl'_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_eq 
    aform.lvivl'_invar_def
      split: option.splits)

lemma one_step_result123:
  "solves_one_step_until_time_aform optns odo X0i t1 t2 E dE \<Longrightarrow>
    (x0, d0) \<in> aform.c1_info_of_appre X0i \<Longrightarrow>
    t \<in> {t1 .. t2} \<Longrightarrow>
    set_of_lvivl E \<subseteq> S \<Longrightarrow>
    blinfuns_of_lvivl' dE \<subseteq> dS \<Longrightarrow>
    length (fst E) = CARD('n) \<Longrightarrow> length (snd E) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dE \<Longrightarrow>
    aform.c1_info_invare DIM('a) X0i \<Longrightarrow>
    aform.D odo = DIM('a) \<Longrightarrow>
      (t \<in> existence_ivl0 (x0::'a) \<and> flow0 x0 t \<in> S) \<and> Dflow x0 t o\<^sub>L d0 \<in> dS"
  apply (transfer fixing: optns X0i t1 t2 t E dE)
  subgoal premises prems for x0 d0 S dS
  proof -
    have "t \<in> aform.existence_ivl0 odo x0 \<and> aform.flow0 odo x0 t \<in> S \<and> aform.Dflow odo x0 t o\<^sub>L d0 \<in> dS"
      apply (rule one_step_in_ivl[of t t1 t2 x0 d0 X0i "fst E" "snd E" S dE dS odo optns])
      using prems
      by (auto simp: eucl_of_list_prod set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image aform.D_def
          solves_one_step_until_time_aform_def)
    with vflow_eq[of t x0] vDflow_eq[of t x0] vex_ivl_eq[symmetric, of t x0] 
    show ?thesis
      by simp
  qed
  done

lemmas one_step_result12 = one_step_result123[THEN conjunct1]
  and one_step_result3 = one_step_result123[THEN conjunct2]
lemmas one_step_result1 = one_step_result12[THEN conjunct1]
  and one_step_result2 = one_step_result12[THEN conjunct2]

lemma plane_of_transfer[transfer_rule]: "(rel_sctn A ===> rel_set A) plane_of plane_of"
  if [transfer_rule]: "(A ===> A ===> (=)) (\<bullet>) (\<bullet>)" "bi_total A"
  unfolding plane_of_def
  by transfer_prover

lemma below_halfspace_transfer[transfer_rule]: "(rel_sctn A ===> rel_set A) below_halfspace below_halfspace"
  if [transfer_rule]: "(A ===> A ===> (=)) (\<bullet>) (\<bullet>)" "bi_total A"
  unfolding below_halfspace_def le_halfspace_def
  by transfer_prover

definition "rel_nres A a b \<longleftrightarrow> (a, b) \<in> \<langle>{(a, b). A a b}\<rangle>nres_rel"

lemma FAILi_transfer[transfer_rule]: "(rel_nres B) FAILi FAILi"
  by (auto simp: rel_nres_def nres_rel_def)

lemma RES_transfer[transfer_rule]: "(rel_set B ===> rel_nres B) RES RES"
  by (auto simp: rel_nres_def nres_rel_def rel_set_def intro!: rel_funI RES_refine)

context includes autoref_syntax begin
lemma RETURN_dres_nres_relI:
  "(fi, f) \<in> A \<rightarrow> B \<Longrightarrow> (\<lambda>x. dRETURN (fi x), (\<lambda>x. RETURN (f x))) \<in> A \<rightarrow> \<langle>B\<rangle>dres_nres_rel"
  by (auto simp: dres_nres_rel_def dest: fun_relD)
end

lemma br_transfer[transfer_rule]:
  "((B ===> C) ===> (B ===> (=)) ===> rel_set (rel_prod B C)) br br"
  if [transfer_rule]: "bi_total B"  "bi_unique C" "bi_total C"
  unfolding br_def
  by transfer_prover

lemma aform_appr_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod (list_all2 (=)) (rel_set rel_ve))) aform.appr_rel aform.appr_rel"
  unfolding aform.appr_rel_br
  by (transfer_prover)

lemma appr1_rel_transfer[transfer_rule]: "(rel_set (rel_prod
  (rel_prod (list_all2 (=)) (rel_option (list_all2 (=))))
  (rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))))) aform.appr1_rel aform.appr1_rel"
  unfolding aform.appr1_rel_internal
  by transfer_prover

lemma relAPP_transfer[transfer_rule]:
  "((rel_set (rel_prod B C) ===> D) ===> rel_set (rel_prod B C) ===> D) Relators.relAPP Relators.relAPP"
  unfolding relAPP_def
  by transfer_prover

lemma prod_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod D E) ===> rel_set (rel_prod (rel_prod B D) (rel_prod C E)))
    prod_rel prod_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  "bi_unique E" "bi_total E"
  unfolding prod_rel_def_internal
  by transfer_prover

lemma Domain_transfer[transfer_rule]:
  "(rel_set (rel_prod A B) ===> rel_set A) Domain Domain"
  if [transfer_rule]:
  "bi_total A" "bi_unique A"
  "bi_total B" "bi_unique B"
  unfolding Domain_unfold
  by transfer_prover

lemma set_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod (rel_set B) (rel_set C))) set_rel set_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  unfolding set_rel_def_internal
  by transfer_prover

lemma relcomp_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod C D) ===> rel_set (rel_prod B D)) relcomp relcomp"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  unfolding relcomp_unfold
  by transfer_prover

lemma Union_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B (rel_set C)) ===> rel_set (rel_prod C (rel_set D)) ===> rel_set (rel_prod B (rel_set D)))
    Union_rel Union_rel"
  if [transfer_rule]:
  "bi_total B" "bi_unique B"
  "bi_unique C" "bi_total C"
  "bi_unique D" "bi_total D"
  unfolding Union_rel_internal top_fun_def top_bool_def
  by transfer_prover

lemma fun_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod B C) ===> rel_set (rel_prod D E) ===> rel_set (rel_prod (B ===> D) (C ===> E))) Relators.fun_rel Relators.fun_rel"
  if [transfer_rule]:
  "bi_unique B"
  "bi_unique C"
  "bi_unique D" "bi_total D"
  "bi_unique E" "bi_total E"
  unfolding fun_rel_def_internal
  by transfer_prover

lemma c1_info_of_apprse_transfer[transfer_rule]:
  "(list_all2 (rel_prod (rel_prod (=) (=)) (rel_prod (list_all2 (=)) (rel_option (list_all2 (=)))))
    ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve)))
    aform.c1_info_of_apprse
    aform.c1_info_of_apprse"
  unfolding aform.c1_info_of_apprse_def
  by transfer_prover

term scaleR2_rel
(*
"scaleR2_rel"
  ::
  "('b \<times> ('c \<times> 'd) set) set
   \<Rightarrow> (((ereal \<times> ereal) \<times> 'b) \<times> ('c \<times> 'd) set) set"
*)
lemma scaleR2_rel_transfer[transfer_rule]:
  "(rel_set (rel_prod (=) (rel_set (rel_prod (=) (=)))) ===>
    rel_set (rel_prod (rel_prod (rel_prod (=) (=)) (=)) (rel_set (rel_prod (=) (=))))) scaleR2_rel scaleR2_rel"
  unfolding scaleR2_rel_internal
  by transfer_prover

lemma appr1_rele_transfer[transfer_rule]:
  "(rel_set (rel_prod
    (rel_prod (rel_prod (=) (=)) (rel_prod (list_all2 (=)) (rel_option (list_all2 (=)))))
    (rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))))) aform.appr1e_rel aform.appr1e_rel"
  unfolding scaleR2_rel_internal
  by transfer_prover

lemma flow1_of_vec1_times: "flow1_of_vec1 ` (A \<times> B) = A \<times> blinfun_of_vmatrix ` B"
  by (auto simp: flow1_of_vec1_def vec1_of_flow1_def)

lemma stable_on_transfer[transfer_rule]:
  "(rel_set rel_ve ===> rel_set rel_ve ===> (=)) v.stable_on stable_on"
  unfolding stable_on_def v.stable_on_def
  by transfer_prover

theorem solves_poincare_map_aform:
  "solves_poincare_map_aform optns odo (\<lambda>x. dRETURN (symstart x)) [S] guards ivl sctn roi XS RET dRET \<Longrightarrow>
    (symstart, symstarta) \<in> fun_rel (aform.appr1e_rel) (clw_rel aform.appr_rel \<times>\<^sub>r clw_rel aform.appr1e_rel) \<Longrightarrow>
    (\<And>X0. (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X) (symstarta X0)) \<Longrightarrow>
    stable_on (aform.Csafe odo - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn)) trap \<Longrightarrow>
    (\<And>X. X \<in> set XS \<Longrightarrow> aform.c1_info_invare DIM('a) X) \<Longrightarrow>
    aform.D odo = DIM('a) \<Longrightarrow>
    length (normal sctn) = DIM('a) \<Longrightarrow>
    length (fst ivl) = DIM('a) \<Longrightarrow>
    length (snd ivl) = DIM('a) \<Longrightarrow>
    length (normal S) = DIM('a) \<Longrightarrow>
    (\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
        ((a, b), ba) \<in> set xs \<Longrightarrow>
        length a = DIM('a) \<and>
        length b = DIM('a) \<and> length (normal ba) = DIM('a)) \<Longrightarrow>
    length (fst RET) = CARD('n) \<Longrightarrow> length (snd RET) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dRET \<Longrightarrow>
    poincare_mapsto
     ((set_of_lvivl ivl::('a set)) \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS - trap \<times> UNIV)
     (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe odo -
      set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (set_of_lvivl RET \<times> blinfuns_of_lvivl' dRET)"
  apply (transfer fixing: optns symstart S guards ivl sctn roi XS RET dRET)
  subgoal premises prems for symstarta trap
  proof -
    have "aform.poincare_mapsto odo (set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS - trap \<times> UNIV) (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe odo - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (flow1_of_vec1 ` ({eucl_of_list (fst RET)..eucl_of_list (snd RET)} \<times> aform.set_of_lvivl' dRET))"
      apply (rule solves_poincare_map[OF _ RETURN_dres_nres_relI RETURN_rule,
        of optns odo symstart S guards ivl sctn roi XS "fst RET" "snd RET" dRET symstarta trap])
      subgoal using prems(1) by (simp add: solves_poincare_map_aform_def)
      subgoal using prems(2) by (auto simp: fun_rel_def_internal)
      subgoal for X0
        using prems(3)[of X0] vflowsto_eq
        by auto
      subgoal
        unfolding aform.stable_on_def
      proof (safe, goal_cases)
        case (1 t x0)
        from 1 have a: "t \<in> v.existence_ivl0 x0" using vex_ivl_eq by blast
        with 1 have b: "v.flow0 x0 t \<in> trap" using vflow_eq by simp
        have c: "v.flow0 x0 s \<in> vX - set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn)"
          if s: "s \<in> {0<..t}"
          for s
          using 1(4)[rule_format, OF s]
          apply (subst (asm) vflow_eq)
          unfolding aform_Csafe_vX[symmetric]
          using s a
          by (auto dest!: a.v.ivl_subset_existence_ivl)
        from a b c show ?case 
          using prems(4)[unfolded v.stable_on_def, rule_format, OF b a 1(3) c]
          by simp
      qed
      subgoal using prems by auto
      subgoal using prems by (auto simp: aform.D_def)
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      subgoal using prems by auto
      done
    then show ?thesis
      using vflow_eq vex_ivl_eq vflowsto_eq prems
      apply (subst vpoincare_mapsto_eq[symmetric])
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image flow1_of_vec1_times)
  qed
  done

theorem solves_poincare_map_aform':
  "solves_poincare_map_aform' optns odo S guards ivl sctn roi XS RET dRET\<Longrightarrow>
    (\<And>X. X \<in> set XS \<Longrightarrow> aform.c1_info_invare DIM('a) X) \<Longrightarrow>
    aform.D odo = DIM('a) \<Longrightarrow>
    length (normal sctn) = DIM('a) \<Longrightarrow>
    length (fst ivl) = DIM('a) \<Longrightarrow>
    length (snd ivl) = DIM('a) \<Longrightarrow>
    length (normal S) = DIM('a) \<Longrightarrow>
    (\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
        ((a, b), ba) \<in> set xs \<Longrightarrow>
        length a = DIM('a) \<and>
        length b = DIM('a) \<and> length (normal ba) = DIM('a)) \<Longrightarrow>
    length (fst RET) = CARD('n) \<Longrightarrow> length (snd RET) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dRET \<Longrightarrow>
    poincare_mapsto
     ((set_of_lvivl ivl::('a set)) \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS)
     (below_halfspace (map_sctn eucl_of_list S))
     (aform.Csafe odo -
      set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (set_of_lvivl RET \<times> blinfuns_of_lvivl' dRET)"
  apply (transfer fixing: optns S guards ivl sctn roi XS RET dRET)
  subgoal
    using solves_poincare_map'[of optns odo S guards ivl sctn roi XS "fst RET" "snd RET" dRET]
    using vflow_eq vex_ivl_eq vflowsto_eq
    apply (subst vpoincare_mapsto_eq[symmetric])
    by (auto intro!: closed_Int simp: set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image
        flow1_of_vec1_times aform.D_def solves_poincare_map_aform'_def)
  done

theorem solves_poincare_map_onto_aform:
  "solves_poincare_map_onto_aform optns odo guards ivl sctn roi XS RET dRET\<Longrightarrow>
    (\<And>X. X \<in> set XS \<Longrightarrow> aform.c1_info_invare DIM('a) X) \<Longrightarrow>
    aform.D odo = DIM('a) \<Longrightarrow>
    length (normal sctn) = DIM('a) \<Longrightarrow>
    length (fst ivl) = DIM('a) \<Longrightarrow>
    length (snd ivl) = DIM('a) \<Longrightarrow>
    (\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
        ((a, b), ba) \<in> set xs \<Longrightarrow>
        length a = DIM('a) \<and>
        length b = DIM('a) \<and> length (normal ba) = DIM('a)) \<Longrightarrow>
    length (fst RET) = CARD('n) \<Longrightarrow> length (snd RET) = CARD('n) \<Longrightarrow>
    aform.lvivl'_invar (CARD('n) * CARD('n)) dRET \<Longrightarrow>
    poincare_mapsto
     ((set_of_lvivl ivl::('a set)) \<inter> plane_of (map_sctn eucl_of_list sctn))
     (aform.c1_info_of_apprse XS)
     UNIV
     (aform.Csafe odo -
      set_of_lvivl ivl \<inter> plane_of (map_sctn eucl_of_list sctn))
     (set_of_lvivl RET \<times> blinfuns_of_lvivl' dRET)"
  apply (transfer fixing: optns guards ivl sctn roi XS RET dRET)
  subgoal
    using solves_poincare_map_onto[of optns odo guards ivl sctn roi XS "fst RET" "snd RET" dRET, where 'n='n,
          unfolded aform.poincare_maps_onto_def]
    using vflow_eq vex_ivl_eq vflowsto_eq
    apply (subst vpoincare_mapsto_eq[symmetric])
    by (auto intro!: closed_Int simp: set_of_lvivl_def set_of_ivl_def blinfun_of_vmatrix_image
        flow1_of_vec1_times aform.D_def solves_poincare_map_onto_aform_def)
  done

end

end

subsection \<open>Example Utilities!\<close>

hide_const floatarith.Max floatarith.Min

lemma degree_sum_pdevs_scaleR_Basis:
  "degree (sum_pdevs (\<lambda>i. pdevs_scaleR (a i) i) (Basis::'b::euclidean_space set)) = Max ((\<lambda>i. degree (a i)) ` Basis)"
  apply (rule antisym)
  subgoal apply (rule degree_le)
    by (auto )
  subgoal
    apply (rule Max.boundedI)
      apply simp
     apply simp
    apply (auto simp: intro!: degree_leI)
    by (auto simp: euclidean_eq_iff[where 'a='b])
  done

lemma Inf_aform_eucl_of_list_aform:
  assumes "length a = DIM('b::executable_euclidean_space)"
  shows "Inf_aform (eucl_of_list_aform a::'b aform) = eucl_of_list (map Inf_aform a)"
  using assms
  apply (auto simp: eucl_of_list_aform_def Inf_aform_def[abs_def] algebra_simps
      eucl_of_list_inner inner_sum_left
      intro!: euclidean_eqI[where 'a='b])
  apply (auto simp: tdev_def inner_sum_left abs_inner inner_Basis if_distrib cong: if_cong)
  apply (rule sum.mono_neutral_cong_left)
     apply simp
  by (auto simp: degree_sum_pdevs_scaleR_Basis)

lemma Sup_aform_eucl_of_list_aform:
  assumes "length a = DIM('b::executable_euclidean_space)"
  shows "Sup_aform (eucl_of_list_aform a::'b aform) = eucl_of_list (map Sup_aform a)"
  using assms
  apply (auto simp: eucl_of_list_aform_def Sup_aform_def[abs_def] algebra_simps
      eucl_of_list_inner inner_sum_left
      intro!: euclidean_eqI[where 'a='b])
  apply (auto simp: tdev_def inner_sum_left abs_inner inner_Basis if_distrib cong: if_cong)
  apply (rule sum.mono_neutral_cong_right)
     apply simp
  by (auto simp: degree_sum_pdevs_scaleR_Basis)

lemma
  eucl_of_list_map_Inf_aform_leI:
  assumes "x \<in> Affine (eucl_of_list_aform a::'b::executable_euclidean_space aform)"
  assumes "length a = DIM('b)"
  shows "eucl_of_list (map Inf_aform a) \<le> x"
  using Inf_aform_le_Affine[OF assms(1)] assms(2)
  by (auto simp: Inf_aform_eucl_of_list_aform)

lemma
  eucl_of_list_map_Sup_aform_geI:
  assumes "x \<in> Affine (eucl_of_list_aform a::'b::executable_euclidean_space aform)"
  assumes "length a = DIM('b)"
  shows "x \<le> eucl_of_list (map Sup_aform a)"
  using Sup_aform_ge_Affine[OF assms(1)] assms(2)
  by (auto simp: Sup_aform_eucl_of_list_aform)

lemma
  mem_Joints_appendE:
  assumes "x \<in> Joints (xs @ ys)"
  obtains x1 x2 where "x = x1 @ x2" "x1 \<in> Joints xs" "x2 \<in> Joints ys"
  using assms
  by (auto simp: Joints_def valuate_def)

lemma c1_info_of_appr_subsetI1:
  fixes X1::"'b::executable_euclidean_space set"
  assumes subset: "{eucl_of_list (map Inf_aform (fst R)) .. eucl_of_list (map Sup_aform (fst R))} \<subseteq> X1"
  assumes len: "length (fst R) = DIM('b)"
  shows "aform.c1_info_of_appr R \<subseteq> X1 \<times> UNIV"
  using len
  apply (auto simp: aform.c1_info_of_appr_def flow1_of_list_def
      split: option.splits
      intro!: subsetD[OF subset] elim!: mem_Joints_appendE)
  subgoal
    by (auto intro!: eucl_of_list_mem_eucl_of_list_aform eucl_of_list_map_Inf_aform_leI eucl_of_list_map_Sup_aform_geI)
  subgoal
    by (auto intro!: eucl_of_list_mem_eucl_of_list_aform eucl_of_list_map_Inf_aform_leI eucl_of_list_map_Sup_aform_geI)
  subgoal
    apply (subst (2) eucl_of_list_take_DIM[symmetric, OF refl])
      apply (auto simp: min_def)
    apply (simp add: Joints_imp_length_eq eucl_of_list_map_Inf_aform_leI eucl_of_list_mem_eucl_of_list_aform)
    apply (simp add: Joints_imp_length_eq eucl_of_list_map_Inf_aform_leI eucl_of_list_mem_eucl_of_list_aform)
      done
  subgoal
    apply (subst (2) eucl_of_list_take_DIM[symmetric, OF refl])
      apply (auto simp: min_def)
    by (simp add: Joints_imp_length_eq eucl_of_list_map_Sup_aform_geI eucl_of_list_mem_eucl_of_list_aform)
  done

lemmas [simp] = compute_tdev

syntax product_aforms::"(real aform) list \<Rightarrow> (real aform) list \<Rightarrow> (real aform) list"
  (infixr "\<times>\<^sub>a" 70)

lemma matrix_inner_Basis_list:
  includes vec_syntax
  assumes "k < CARD('n) * CARD('m)"
  shows "(f::(('n::enum rvec, 'm::enum) vec)) \<bullet> Basis_list ! k =
    vec_nth (vec_nth f (enum_class.enum ! (k div CARD('n)))) (enum_class.enum ! (k mod CARD('n)))"
proof -
  have "f \<bullet> Basis_list ! k =
    (\<Sum>x\<in>UNIV.
       \<Sum>xa\<in>UNIV.
         if enum_class.enum ! (k mod CARD('n)) = xa \<and> enum_class.enum ! (k div CARD('n)) = x then f $ x $ xa else 0)"
    using assms
    unfolding inner_vec_def
    apply (auto simp: Basis_list_vec_def concat_map_map_index)
    apply (subst (2) sum.cong[OF refl])
     apply (subst sum.cong[OF refl])
      apply (subst (2) vec_nth_Basis2)
       apply (force simp add: Basis_vec_def Basis_list_real_def)
      apply (rule refl)
     apply (rule refl)
    apply (auto simp: if_distribR if_distrib axis_eq_axis Basis_list_real_def cong: if_cong)
    done
  also have "\<dots> = f $ enum_class.enum ! (k div CARD('n)) $ enum_class.enum ! (k mod CARD('n))"
    apply (subst if_conn)
    apply (subst sum.delta')
     apply simp
    by (simp add: sum.delta')
  finally show ?thesis by simp
qed

lemma list_of_eucl_matrix:
  includes vec_syntax
  shows "(list_of_eucl (M::(('n::enum rvec, 'm::enum) vec))) =
    concat (map (\<lambda>i. map (\<lambda>j. M $ (enum_class.enum ! i)$ (enum_class.enum ! j) )
      [0..<CARD('n)]) [0..<CARD('m)])"
  by (auto intro!: nth_equalityI simp: length_concat o_def sum_list_distinct_conv_sum_set ac_simps
      concat_map_map_index matrix_inner_Basis_list)

lemma axis_eq_eucl_of_list:
  "(axis i 1::'n::enum rvec) = eucl_of_list ((replicate CARD('n) 0)[index enum_class.enum i := 1])"
  apply (auto intro!: euclidean_eqI[where 'a="'n rvec"]
      simp: eucl_of_list_inner nth_list_update )
   apply (auto simp: index_Basis_list_axis1[symmetric])
  by (simp add: inner_axis inner_commute vec_nth_Basis)

lemma eucl_of_list_012: "eucl_of_list [vec_nth A 0, vec_nth A 1, vec_nth A 2] = A" for A::"3 rvec"
  apply vector
  apply (auto simp: vec_nth_eucl_of_list_eq index_Basis_list_axis1)
  using exhaust_3 three_eq_zero by blast


definition "ldec x = (case quotient_of x of (i, j) \<Rightarrow> real_of_float (lapprox_rat 20 i j))"
definition "udec x = (case quotient_of x of (i, j) \<Rightarrow> real_of_float (rapprox_rat 20 i j))"

lemma ldec: "ldec x \<le> real_of_rat x"
  and udec: "real_of_rat x \<le> udec x"
   apply (auto simp: ldec_def udec_def split: prod.splits
      intro!: lapprox_rat[le] rapprox_rat[ge])
   apply (metis Fract_of_int_quotient less_eq_real_def less_int_code(1) of_rat_rat
      quotient_of_denom_pos quotient_of_div)
  apply (metis Fract_of_int_quotient less_eq_real_def less_int_code(1) of_rat_rat
      quotient_of_denom_pos quotient_of_div)
  done

context includes floatarith_notation begin

definition "matrix_of_degrees\<^sub>e =
  (let
    ur = Rad_of (Var 0);
    vr = Rad_of (Var 1)
   in
    [Cos ur, Cos vr, 0,
     Sin ur, Sin vr, 0,
     0, 0, 0])"

definition "matrix_of_degrees u v =
  approx_floatariths 30 matrix_of_degrees\<^sub>e (aforms_of_point ([u, v, 0]))"

lemma interpret_floatariths_matrix_of_degrees:
  "interpret_floatariths matrix_of_degrees\<^sub>e
    (([u::real, v::real, 0]))
   =
  [cos (rad_of u), cos (rad_of v), 0,
   sin (rad_of u), sin (rad_of v), 0,
   0, 0, 0]"
  by (auto simp: matrix_of_degrees\<^sub>e_def Let_def inverse_eq_divide)

definition "num_options p sstep m N a projs print_fun =
  \<lparr>
    precision = p,
    adaptive_atol = FloatR 1 (- a),
    adaptive_rtol = FloatR 1 (- a),
    method_id = 2,
    start_stepsize  = FloatR 1 (- sstep),
    iterations = 40,
    halve_stepsizes = 40,
    widening_mod = 10,
    rk2_param = FloatR 1 0,
    default_reduce = correct_girard (p) (m) (N),
    printing_fun = (\<lambda>a b.
        let
           _ = fold (\<lambda>(x, y, c) _.
               print_fun (String.implode (shows_segments_of_aform (x) (y) b c ''\<newline>''))) projs ();
           _ = print_fun (String.implode (''# '' @ shows_box_of_aforms_hr (b) '''' @ ''\<newline>''))
        in
         ()
    ),
    tracing_fun = (\<lambda>a b.
      let
        _ = print_fun (String.implode (''# '' @ a @ ''\<newline>''))
      in case b of Some b \<Rightarrow>
        (let
          _ = ()
        in print_fun (String.implode (''# '' @ shows_box_of_aforms_hr (b) '''' @ ''\<newline>'')))
        | None \<Rightarrow> ())
  \<rparr>"

definition "num_options_c1 p sstep m N a projs dcolors print_fun =
  (let
    no = num_options p sstep m N a (map (\<lambda>(x, y, c, ds). (x, y, c)) projs) print_fun;
    D = length dcolors
  in no
    \<lparr>printing_fun:=
      (\<lambda>a b. let _ = printing_fun no a b
          in if a then ()
          else fold (\<lambda>(x, y, c, ds) _. print_fun
              (String.implode (shows_aforms_vareq D [(x, y)] ds
                dcolors
                dcolors
            (FloatR 1 (-1)) ''# no C1 info'' b ''''))) projs ()
      )
    \<rparr>)"

definition "num_options_code p sstep m N a projs print_fun =
  num_options (nat_of_integer p) (int_of_integer sstep) (nat_of_integer m) (nat_of_integer N)
    (int_of_integer a) (map (\<lambda>(i, j, k). (nat_of_integer i, nat_of_integer j, k)) projs) print_fun"

definition "ro s n M g0 g1 inter_step =
  \<lparr>max_tdev_thres = FloatR 1 s,
      pre_split_reduce = correct_girard 30 n M,
      pre_inter_granularity = FloatR 1 g0,
      post_inter_granularity = (FloatR 1 g1),
      pre_collect_granularity = FloatR 1 g0,
      max_intersection_step = FloatR 1 inter_step\<rparr>"

definition "code_ro s n m g0 g1 inter_step =
  ro (int_of_integer s) (nat_of_integer n) (nat_of_integer m) (int_of_integer g0) (int_of_integer g1) (int_of_integer inter_step)"

fun xsec:: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec x (y0, y1) (z0, z1) = (([x, y0, z0], [x, y1, z1]), Sctn [1,0,0] x)"
fun xsec':: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec' x (y0, y1) (z0, z1) = (([x, y0, z0], [x, y1, z1]), Sctn [-1,0,0] (-x))"

fun ysec:: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec (x0, x1) y (z0, z1) = (([x0, y, z0], [x1, y, z1]), Sctn [0, 1,0] y)"
fun ysec':: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec' (x0, x1) y (z0, z1) = (([x0, y, z0], [x1, y, z1]), Sctn [0, -1,0] (-y))"

fun zsec:: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "zsec (x0, x1) (y0, y1) z = (([x0, y0, z], [x1, y1, z]), Sctn [0, 0, 1] z)"
fun zsec':: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "zsec' (x0, x1) (y0, y1) z = (([x0, y0, z], [x1, y1, z]), Sctn [0, 0, -1] (-z))"


fun xsec2:: "real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "xsec2 x (y0, y1) = (([x, y0], [x, y1]), Sctn [1,0] x)"
fun xsec2':: "real \<Rightarrow> real \<times> real \<Rightarrow>(real list \<times> real list) \<times> real list sctn"
  where "xsec2' x (y0, y1) = (([x, y0], [x, y1]), Sctn [-1,0] (-x))"

fun ysec2:: "real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec2 (x0, x1) y = (([x0, y], [x1, y]), Sctn [0, 1] y)"
fun ysec2':: "real \<times> real \<Rightarrow> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec2' (x0, x1) y = (([x0, y], [x1, y]), Sctn [0, -1] (-y))"

fun ysec4:: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec4 (x0, x1) y (z0, z1) (m0, m1) = (([x0, y, z0, m0], [x1, y, z1, m1]), Sctn [0, 1,0, 0] (y))"

fun ysec4':: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> (real list \<times> real list) \<times> real list sctn"
  where "ysec4' (x0, x1) y (z0, z1) (m0, m1) = (([x0, y, z0, m0], [x1, y, z1, m1]), Sctn [0, -1,0, 0] (-y))"

definition "code_sctn N n c = Sctn ((replicate (nat_of_integer N) (0::real))[nat_of_integer n := 1]) c"
definition "code_sctn' N n c = Sctn ((replicate (nat_of_integer N) (0::real))[nat_of_integer n := -1]) (-c)"

definition "lrat i j = real_of_float (lapprox_rat 30 (int_of_integer i) (int_of_integer j))"
definition "urat i j = real_of_float (lapprox_rat 30 (int_of_integer i) (int_of_integer j))"

definition [simp]: "TAG_optns (optns::string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow> (real aform) numeric_options)) = True"
lemma TAG_optns: "P \<Longrightarrow> (TAG_optns optns \<Longrightarrow> P)"
  by (auto simp: )

definition [simp]: "TAG_reach_optns (roi::real aform reach_options) = True"
lemma TAG_reach_optns: "P \<Longrightarrow> (TAG_reach_optns optns \<Longrightarrow> P)"
  by (auto simp: )

definition [simp]: "TAG_sctn (b::bool) = True"
lemma TAG_sctn: "P \<Longrightarrow> (TAG_sctn optns \<Longrightarrow> P)"
  by (auto simp: )

subsection \<open>Integrals and Computation\<close>

lemma has_vderiv_on_PairD:
  assumes "((\<lambda>t. (f t, g t)) has_vderiv_on fg') T"
  shows "(f has_vderiv_on (\<lambda>t. fst (fg' t))) T" "(g has_vderiv_on (\<lambda>t. snd (fg' t))) T"
proof -
  from assms have "((\<lambda>x. (f x, g x)) has_derivative (\<lambda>xa. xa *\<^sub>R fg' t)) (at t within T)"
     if "t \<in> T" for t
    by (auto simp: has_vderiv_on_def has_vector_derivative_def that
        intro!: derivative_eq_intros)
  from diff_chain_within[OF this has_derivative_fst[OF has_derivative_ident]]
    diff_chain_within[OF this has_derivative_snd[OF has_derivative_ident]]
  show "(f has_vderiv_on (\<lambda>t. fst (fg' t))) T" "(g has_vderiv_on (\<lambda>t. snd (fg' t))) T"
    by (auto simp: has_vderiv_on_def has_vector_derivative_def o_def)
qed

lemma solves_autonomous_odeI:
  assumes "((\<lambda>t. (t, phi t)) solves_ode (\<lambda>t x. (1, f (fst x) (snd x)))) S (T \<times> X)"
  shows "(phi solves_ode f) S X"
proof (rule solves_odeI)
  from solves_odeD[OF assms]
  have
    "((\<lambda>t. (t, phi t)) has_vderiv_on (\<lambda>t. (1, f (fst (t, phi t)) (snd (t, phi t))))) S"
    "\<And>t. t \<in> S \<Longrightarrow> (phi t) \<in> X"
    by (auto simp: )
  from has_vderiv_on_PairD(2)[OF this(1)] this(2)
  show "(phi has_vderiv_on (\<lambda>t. f t (phi t))) S" "\<And>t. t \<in> S \<Longrightarrow> phi t \<in> X"
    by auto
qed

lemma integral_solves_autonomous_odeI:
  fixes f::"real \<Rightarrow> 'a::executable_euclidean_space"
  assumes "(phi solves_ode (\<lambda>t _. f t)) {a .. b} X" "phi a = 0"
  assumes "a \<le> b"
  shows "(f has_integral phi b) {a .. b}"
proof -
  have "(f has_integral phi b - phi a) {a..b}"
    apply (rule fundamental_theorem_of_calculus[of a b phi f])
    unfolding has_vderiv_on_def[symmetric]
     apply fact
    using solves_odeD[OF assms(1)]
    by (simp add: has_vderiv_on_def)
  then show ?thesis by (simp add: assms)
qed

lemma zero_eq_eucl_of_list_rep_DIM: "(0::'a::executable_euclidean_space) = eucl_of_list (replicate (DIM('a)) 0)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner)

lemma zero_eq_eucl_of_list_rep: "(0::'a::executable_euclidean_space) = eucl_of_list (replicate D 0)"
  if "D \<ge> DIM('a)"
proof -
  from that have "replicate D (0::real) = replicate (DIM('a)) 0 @ replicate (D - DIM('a)) 0"
    by (auto simp: replicate_add[symmetric])
  also have "eucl_of_list \<dots> = (eucl_of_list (replicate DIM('a) 0)::'a)"
    by (rule eucl_of_list_append_zeroes)
  also have "\<dots> = 0"
    by (rule zero_eq_eucl_of_list_rep_DIM[symmetric])
  finally show ?thesis by simp
qed

lemma one_has_ivl_integral: "((\<lambda>x. 1::real) has_ivl_integral b - a) a b"
  using has_integral_const_real[of "1::real" a b] has_integral_const_real[of "1::real" b a]
  by (auto simp: has_ivl_integral_def split: if_splits)

lemma Joints_aforms_of_point_self[simp]: "xs \<in> Joints (aforms_of_point xs)"
  by (simp add: aforms_of_point_def)

lemma bind_eq_dRETURN_conv:
  "(f \<bind> g = dRETURN S) \<longleftrightarrow> (\<exists>R. f = dRETURN R \<and> g R = dRETURN S)"
  by (cases f) auto

end

lemma list_of_eucl_memI: "list_of_eucl (x::'x::executable_euclidean_space) \<in> S"
  if "x \<in> eucl_of_list ` S" "\<And>x. x \<in> S \<Longrightarrow> length x = DIM('x)"
  using that
  by auto

lemma Joints_aforms_of_ivls_append_point:
  "Joints (xs @ aforms_of_ivls p p) = (\<lambda>x. x @ p) ` Joints xs"
  using aform.set_of_appr_of_ivl_append_point[unfolded aform_ops_def approximate_set_ops.simps] .


context ode_interpretation begin

theorem solves_one_step_ivl:
  assumes T: "T \<subseteq> {t1 .. t2}"
  assumes X: "X \<subseteq> {eucl_of_list lx .. eucl_of_list ux}" "length lx = DIM('a)" "length ux = DIM('a)"
  assumes S: "{eucl_of_list ls::'a .. eucl_of_list us} \<subseteq> S"
  assumes lens: "length ls = DIM('a)" "length us = DIM('a)" \<comment> \<open>TODO: this could be verified\<close>
  assumes [simp]: "aform.D odo = DIM('a)"
  assumes r: "solves_one_step_until_time_aform optns odo ((1,1), aforms_of_ivls lx ux, None) t1 t2 (ls, us) None"
  shows "t \<in> T \<longrightarrow> x0 \<in> X \<longrightarrow> t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
proof (intro impI)
  assume t: "t \<in> T" and x0: "x0 \<in> X"
  from S have S: "set_of_lvivl (ls, us) \<subseteq> S"
    by (auto simp: set_of_lvivl_def set_of_ivl_def)
  have lens: "length (fst (ls, us)) = CARD('n)" "length (snd (ls, us)) = CARD('n)"
    by (auto simp: lens)
  have x0: "list_of_eucl x0 \<in> Joints (aforms_of_ivls lx ux)"
    apply (rule aforms_of_ivls)
    subgoal by (simp add: X)
    subgoal by (simp add: X)
    using subsetD[OF X(1) x0]
    apply (auto simp: eucl_le[where 'a='a] X)
    apply (metis assms(3) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    apply (metis assms(4) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    done
  from t T have t: "t \<in> {t1 .. t2}" by auto
  show "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S"
    by (rule one_step_result12[OF r aform.c1_info_of_appre_c0_I[OF x0] t S subset_UNIV lens])
      (auto simp: aform.c1_info_invare_None lens X)
qed

theorem solves_one_step_ivl':
  assumes T: "T \<subseteq> {t1 .. t2}"
  assumes X: "X \<subseteq> {eucl_of_list lx .. eucl_of_list ux}"
    "length lx = DIM('a)" "length ux = DIM('a)"
  assumes DS: "list_interval lds uds \<subseteq> list_interval ld ud"
    and lends: "length lds = DIM('a)*DIM('a)" "length uds = DIM('a)*DIM('a)"
  assumes S: "{eucl_of_list ls::'a .. eucl_of_list us} \<subseteq> S"
  assumes lens0: "length ls = DIM('a)" "length us = DIM('a)" \<comment> \<open>TODO: this could be verified\<close>
    "length dx0s = DIM('a)*DIM('a)"
  assumes [simp]: "aform.D odo = DIM('a)"
  assumes r: "solves_one_step_until_time_aform optns odo
    ((1,1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s)) t1 t2 (ls, us) (Some (lds, uds))"
  shows "t \<in> T \<longrightarrow> x0 \<in> X \<longrightarrow> t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and>
    Dflow x0 t o\<^sub>L blinfun_of_list dx0s \<in> blinfuns_of_lvivl (ld, ud)"
proof (intro impI)
  assume t: "t \<in> T" and x0: "x0 \<in> X"
  from S have S: "set_of_lvivl (ls, us) \<subseteq> S"
    by (auto simp: set_of_lvivl_def set_of_ivl_def)
  have lens: "length (fst (ls, us)) = CARD('n)" "length (snd (ls, us)) = CARD('n)"
    by (auto simp: lens0)
  have x0: "list_of_eucl x0 \<in> Joints (aforms_of_ivls lx ux)"
    apply (rule aforms_of_ivls)
    subgoal by (simp add: X)
    subgoal by (simp add: X)
    using subsetD[OF X(1) x0]
    apply (auto simp: eucl_le[where 'a='a] X)
    apply (metis assms(3) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    apply (metis assms(4) dim length_Basis_list list_of_eucl_eucl_of_list list_of_eucl_nth nth_Basis_list_in_Basis)
    done
  have x0dx0: "(x0, blinfun_of_list dx0s) \<in>
      aform.c1_info_of_appre ((1, 1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s))"
    apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def)
    apply (rule image_eqI[where x="list_of_eucl x0@dx0s"])
    using lens0
     apply (auto simp: flow1_of_list_def aforms_of_point_def Joints_aforms_of_ivls_append_point)
    apply (rule imageI)
    apply (rule x0)
    done
  from t T have t: "t \<in> {t1 .. t2}" by auto
  have DS: "blinfuns_of_lvivl' (Some (lds, uds)) \<subseteq> blinfun_of_list ` list_interval ld ud"
    using DS
    by (auto simp: blinfuns_of_lvivl'_def blinfuns_of_lvivl_def)
  have inv: "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lds, uds))"
    "aform.c1_info_invare DIM('a) ((1::ereal, 1), aforms_of_ivls lx ux, Some (aforms_of_point dx0s))"
    by (auto simp: aform.lvivl'_invar_def lends aform.c1_info_invare_def X lens0 power2_eq_square
        aform.c1_info_invar_def)
  from one_step_result123[OF r x0dx0 t S DS lens inv \<open>aform.D _ = _\<close>]
  show "t \<in> existence_ivl0 x0 \<and> flow0 x0 t \<in> S \<and> Dflow x0 t o\<^sub>L blinfun_of_list dx0s \<in> blinfuns_of_lvivl (ld, ud)"
    by (auto simp: blinfuns_of_lvivl_def)
qed

end

definition "zero_aforms D = map (\<lambda>_. (0, zero_pdevs)) [0..<D]"

definition "solves_one_step_until_time_aform_fo soptns a b c d e f =
  file_output (String.implode (fst soptns)) (\<lambda>pf. solves_one_step_until_time_aform (snd soptns pf) a b c d e f)"

definition "solves_poincare_map_aform'_fo soptns a b c d e f g h i =
  file_output (String.implode (fst soptns)) (\<lambda>pf. solves_poincare_map_aform' (snd soptns pf) a b c d e f g h i)"

definition "solves_poincare_map_onto_aform_fo soptns a b c d e f g h =
  file_output (String.implode (fst soptns)) (\<lambda>pf. solves_poincare_map_onto_aform (snd soptns pf) a b c d e f g h)"

lemma solves_one_step_until_time_aform_foI:
  "solves_one_step_until_time_aform (snd optns (\<lambda>_. ())) a b c d e f"
  if "solves_one_step_until_time_aform_fo optns a b c d e f"
  using that
  by (auto simp: solves_one_step_until_time_aform_fo_def file_output_def Print.file_output_def
      print_def[abs_def]
      split: if_splits)

lemma solves_poincare_map_aform'_foI:
  "solves_poincare_map_aform' (snd optns (\<lambda>_. ())) a b c d e f g h i"
  if "solves_poincare_map_aform'_fo optns a b c d e f g h i"
  using that
  by (auto simp: solves_poincare_map_aform'_fo_def file_output_def Print.file_output_def
      print_def[abs_def]
      split: if_splits)

lemma solves_poincare_map_onto_aform_foI:
  "solves_poincare_map_onto_aform (snd optns (\<lambda>_. ())) a b c d e f g h"
  if "solves_poincare_map_onto_aform_fo optns a b c d e f g h"
  using that
  by (auto simp: solves_poincare_map_onto_aform_fo_def file_output_def Print.file_output_def
      print_def[abs_def]
      split: if_splits)

definition "can_mk_ode_ops fas safe_form \<longleftrightarrow> mk_ode_ops fas safe_form \<noteq> None"

theorem solve_one_step_until_time_aform_integral_bounds:
  fixes f::"real \<Rightarrow> 'a::executable_euclidean_space"
  assumes "a \<le> b"
  assumes ba: "b - a \<in> {t1 .. t2}"
  assumes a: "a \<in> {a1 .. a2}"
  assumes ls_us_subset: "{eucl_of_list ls .. eucl_of_list us} \<subseteq> {l .. u}"
  assumes fas: "\<And>xs::real list. length xs > 0 \<Longrightarrow> interpret_form safe_form xs \<Longrightarrow>
    (1::real, f (xs ! 0)) = einterpret fas xs"
  assumes D: "D = DIM('a) + 1" "D = CARD('i::enum)"
  assumes lenlu: "length ls + 1 = D" "length us + 1 = D"
  assumes lfas: "length fas = D"
  assumes mv: "can_mk_ode_ops fas safe_form"
  assumes FDERIV: "\<And>xs. interpret_form safe_form xs \<Longrightarrow> isFDERIV (length fas) [0..<length fas] fas xs"
  assumes sos[THEN solves_one_step_until_time_aform_foI]:
    "solves_one_step_until_time_aform_fo optns (the(mk_ode_ops fas safe_form))
      ((1,1), (aforms_of_ivls (a1#replicate (D - 1) 0) (a2#replicate (D - 1) 0)), None) t1 t2 (0#ls, t2#us) None"
  shows "integral {a .. b} f \<in> {l .. u}"
proof -
  have lens0: "length ((x::real) # replicate (D - 1) 0) = DIM(real \<times> 'a)" for x
    using assms
    by auto
  have a0: "(a, 0) \<in> {eucl_of_list (a1 # replicate (D - 1) 0)..eucl_of_list (a2 # replicate (D - 1) 0)}"
    using assms
    by (auto simp: eucl_of_list_prod)
  let ?U = "{x::real\<times>'a. interpret_form safe_form (list_of_eucl x)}"
  interpret ode_interpretation safe_form ?U fas "\<lambda>x. (1::real, f (fst x))" "undefined::'i"
    apply unfold_locales
    subgoal using assms by simp
    subgoal using assms by simp
    subgoal using mv by (simp add: D lfas)
    subgoal for x
      apply (cases x)
      by (rule HOL.trans[OF fas[symmetric]]) (auto simp: fas)
    subgoal using mv by (simp add: can_mk_ode_ops_def)
    subgoal by (rule FDERIV)
    done
  have lens: "length (0 # ls) = DIM(real \<times> 'a)" "length (t2 # us) = DIM(real \<times> 'a)" "aform.D odo = DIM(real \<times> 'a)"
    using lenlu
    by (simp_all add: lfas aform.D_def D aform.ode_e_def )
  have D_odo: "aform.D odo = DIM(real \<times> 'a)"
    by (auto simp: aform.D_def aform.ode_e_def lfas D)
  from solves_one_step_ivl[rule_format, OF order_refl order_refl lens0 lens0 order_refl lens(1,2) D_odo,
    unfolded odo_def,
    OF sos ba a0]
  have lsus: "flow0 (a, 0) (b - a) \<in> {eucl_of_list (0#ls)..eucl_of_list (t2#us)}"
    and exivl: "b - a \<in> existence_ivl0 (a, 0)"
    by auto
  have flow: "flow0 (a, 0) (b - a) \<in> UNIV \<times> {l..u}"
    using lsus
    apply (rule rev_subsetD)
    using ls_us_subset
    by (auto simp: eucl_of_list_prod)
  from ivl_subset_existence_ivl[OF exivl] \<open>a \<le> b\<close> exivl
  have "0 \<in> existence_ivl0 (a, 0)"
    by (auto simp del: existence_ivl_initial_time_iff)
  from mem_existence_ivl_iv_defined(2)[OF this]
  have safe: "(a, 0::'a) \<in> ?U" by simp
  from flow_solves_ode[OF UNIV_I this]
  have fs: "((\<lambda>t. (fst (flow0 (a, 0) t), snd (flow0 (a, 0) t))) solves_ode (\<lambda>_ x. (1, f (fst x)))) (existence_ivl0 (a, 0)) ?U"
    by simp
  with solves_odeD[OF fs]
  have vdp: "((\<lambda>t. (fst (flow0 (a, 0) t), snd (flow0 (a, 0) t))) has_vderiv_on (\<lambda>t. (1, f (fst (flow0 (a, 0) t))))) (existence_ivl0 (a, 0))"
    by simp
  have "fst (flow0 (a, 0) t) = a + t" if "t \<in> existence_ivl0 (a, 0)" for t
  proof -
    have "fst (flow0 (a, 0) 0) = a" using safe
      by (auto simp: )
    have "((\<lambda>t. fst (flow0 (a, 0) t)) has_vderiv_on (\<lambda>x. 1)) (existence_ivl0 (a, 0))"
      using has_vderiv_on_PairD[OF vdp] by auto
    then have "((\<lambda>t. fst (flow0 (a, 0) t)) has_vderiv_on (\<lambda>x. 1)) {0--t}"
      apply (rule has_vderiv_on_subset)
      using closed_segment_subset_existence_ivl[OF that]
      by auto
    from fundamental_theorem_of_calculus_ivl_integral[OF this, THEN ivl_integral_unique]
      one_has_ivl_integral[of t 0, THEN ivl_integral_unique] safe
    show ?thesis
      by auto
  qed
  with vdp have "((\<lambda>t. (t, snd (flow0 (a, 0) t))) solves_ode (\<lambda>t x. (1, f (a + fst x))))
    (existence_ivl0 (a, 0)) ((existence_ivl0 (a, 0)) \<times> UNIV)"
    apply (intro solves_odeI)
     apply auto
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def)
  proof goal_cases
    case (1 x)
    have r: "((\<lambda>(x, y). (x - a, y::'a)) has_derivative (\<lambda>x. x)) (at x within t)" for x t
      by (auto intro!: derivative_eq_intros)
    from 1 have "((\<lambda>x. (a + x, snd (flow0 (a, 0) x))) has_derivative (\<lambda>xa. (xa, xa *\<^sub>R f (a + x))))
        (at x within existence_ivl0 (a, 0))"
      by auto
    from has_derivative_in_compose2[OF r subset_UNIV _ this, simplified] 1
    have "((\<lambda>x. (x, snd (flow0 (a, 0) x))) has_derivative (\<lambda>y. (y, y *\<^sub>R f (a + x)))) (at x within existence_ivl0 (a, 0))"
      by auto
    then show ?case
      by simp
  qed
  from solves_autonomous_odeI[OF this]
  have "((\<lambda>t. snd (flow0 (a, 0) t)) solves_ode (\<lambda>b c. f (a + b))) (existence_ivl0 (a, 0)) UNIV"
    by simp \<comment> \<open>TODO: do non-autonomous -- autonomous conversion automatically!\<close>
  then have "((\<lambda>t. snd (flow0 (a, 0) t)) solves_ode (\<lambda>b c. f (a + b))) {0 .. b - a} UNIV"
    apply (rule solves_ode_on_subset)
    using exivl
    by (rule ivl_subset_existence_ivl) (rule order_refl)
  from integral_solves_autonomous_odeI[OF this]
  have "((\<lambda>b. f (a + b)) has_integral snd (flow0 (a, 0) (b - a))) (cbox 0 (b - a))"
    using \<open>a \<le> b\<close> safe
    by auto
  from has_integral_affinity[OF this, where m=1 and c="-a"]
  have "(f has_integral snd (flow0 (a, 0) (b - a))) {a..b}"
    by auto
  then have "integral {a..b} f = snd (flow0 (a, 0) (b - a))" by blast
  also have "\<dots> \<in> {l .. u}"
    using flow
    by auto
  finally show ?thesis by simp
qed

lemma [code_computation_unfold]:
  "numeral x = real_of_int (Code_Target_Int.positive x)"
  by simp
lemma [code_computation_unfold]: "numeral x \<equiv> Float (Code_Target_Int.positive x) 0"
  by (simp add: Float_def float_of_numeral)

definition no_print::"String.literal \<Rightarrow> unit" where "no_print x = ()"

lemmas [approximation_preproc] = list_of_eucl_real list_of_eucl_prod append.simps

named_theorems DIM_simps
lemmas [DIM_simps] =
  DIM_real DIM_prod length_nth_simps
  add_numeral_special
  add_numeral_special card_sum card_prod card_bit0 card_bit1 card_num0 card_num1
  numeral_times_numeral numeral_mult mult_1_right mult_1
  aform.D_def

lemma numeral_refl: "numeral x = numeral x" by simp

lemma plain_floatarith_approx_eq_SomeD:
  "approx prec fa [] = Some (the (approx prec fa []))"
  if "plain_floatarith 0 fa"
  using that
  by (auto dest!: plain_floatarith_approx_not_None[where p=prec and XS=Nil])

definition [simp]: "approx1 p f xs = real_of_float (lower (the (approx p f xs)))"
definition [simp]: "approx2 p f xs = real_of_float (upper (the (approx p f xs)))"
definition [simp]: "approx_defined p f xs \<longleftrightarrow> approx p f xs \<noteq> None"

definition "approxs p fs xs = those (map (\<lambda>f. approx p f xs) fs)"
definition [simp]: "approxs1 p f xs =
  (case approxs p f xs of Some y \<Rightarrow> (map (real_of_float o lower) y) | None \<Rightarrow> replicate (length f) 0)"
definition [simp]: "approxs2 p f xs =
  (case approxs p f xs of Some y \<Rightarrow> (map (real_of_float o upper) y) | None \<Rightarrow> replicate (length f) 0)"
definition "approxs_defined p fs xs \<longleftrightarrow> (those (map (\<lambda>f. approx p f xs) fs) \<noteq> None)"

lemma length_approxs:
  "length (approxs1 p f xs) = length f"
  "length (approxs2 p f xs) = length f"
  by (auto simp: approxs_def dest!: those_eq_SomeD split: option.splits)

lemma real_in_approxI:
  "x \<in> {(approx1 prec fa []) .. (approx2 prec fa [])}"
  if "x = interpret_floatarith fa []"
    "approx_defined prec fa []"
  using that
  by (force dest: approx_emptyD simp: set_of_eq)

lemma real_subset_approxI:
  "{a .. b} \<subseteq> {(approx1 prec fa []) .. (approx2 prec fb [])}"
  if "a = interpret_floatarith fa []"
    "b = interpret_floatarith fb []"
    "approx_defined prec fa []"
    "approx_defined prec fb []"
  using that
  by (force dest: approx_emptyD simp: set_of_eq)


lemma approxs_eq_Some_lengthD: "length ys = length fas" if "approxs prec fas XS = Some ys"
  using that
  by (auto simp: approxs_def dest!: those_eq_SomeD)

lemma approxs_pointwise:
  "interpret_floatarith (fas ! ia) xs \<in> {real_of_float (lower (ys ! ia)) .. (upper (ys ! ia))}"
  if "approxs prec fas XS = Some ys" "bounded_by xs XS" "ia < length fas"
proof -
  from those_eq_SomeD[OF that(1)[unfolded approxs_def]]
  have ys: "ys = map (the \<circ> (\<lambda>f. approx prec f XS)) fas"
    and ex: "\<exists>y. i < length fas \<longrightarrow> approx prec (fas ! i) XS = Some y" for i
    by auto
  from ex[of ia] that obtain ivl where ivl: "approx prec (fas ! ia) XS = Some ivl" by auto
  from approx[OF that(2) this]
  have "interpret_floatarith (fas ! ia) xs \<in>\<^sub>r ivl"
    by auto
  moreover
  have "ys ! ia = ivl"
    unfolding ys
    apply (auto simp: o_def)
    apply (subst nth_map)
     apply (simp add: that)
    using ivl by simp
  ultimately show ?thesis
    using that
    by (auto simp: approxs_eq_Some_lengthD set_of_eq split: prod.splits)
qed

lemmas approxs_pointwise_le = approxs_pointwise[simplified, THEN conjunct1]
  and approxs_pointwise_ge = approxs_pointwise[simplified, THEN conjunct2]

lemma approxs_eucl:
  "eucl_of_list (interpret_floatariths fas xs) \<in>
    {eucl_of_list (map lower ys) .. eucl_of_list (map upper ys)::'a::executable_euclidean_space}"
  if "approxs prec fas XS = Some ys"
    "length fas = DIM('a)"
    "bounded_by xs XS"
  using that
  by (auto simp: eucl_le[where 'a='a] eucl_of_list_inner o_def approxs_eq_Some_lengthD
      intro!: approxs_pointwise_le approxs_pointwise_ge)

lemma plain_floatariths_approx_eq_SomeD:
  "approxs prec fas [] = Some (the (approxs prec fas []))"
  if "list_all (plain_floatarith 0) fas"
  using that
  apply (induction fas)
   apply (auto simp: approxs_def split: option.splits dest!: plain_floatarith_approx_eq_SomeD)
  subgoal for a fas aa
    apply (cases "those (map (\<lambda>f. approx prec f []) fas)")
    by auto
  done

lemma approxs_definedD:
  "approxs prec fas xs = Some (the (approxs prec fas xs))"
  if "approxs_defined prec fas xs"
  using that
  by (auto simp: approxs_defined_def approxs_def)

lemma approxs_defined_ne_None[simp]:
  "approxs prec fas xs \<noteq> None"
  if "approxs_defined prec fas xs"
  using that
  by (auto simp: approxs_defined_def approxs_def)

lemma approx_subset_euclI:
  "{eucl_of_list (approxs2 prec fals [])::'a .. eucl_of_list (approxs1 prec faus [])} \<subseteq> {l .. u}"
  if "list_of_eucl l = interpret_floatariths fals []"
    and "list_of_eucl u = interpret_floatariths faus []"
    and "length fals = DIM('a::executable_euclidean_space)"
    and "length faus = DIM('a::executable_euclidean_space)"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  by (auto intro!: bounded_by_Nil
      dest!: approxs_eucl[where 'a='a] list_of_eucl_eqD plain_floatariths_approx_eq_SomeD[where prec=prec]
        split: option.splits)

lemma eucl_subset_approxI:
  "{l .. u} \<subseteq> {eucl_of_list (approxs1 prec fals [])::'a .. eucl_of_list (approxs2 prec faus [])}"
  if "list_of_eucl l = interpret_floatariths fals []"
    and "list_of_eucl u = interpret_floatariths faus []"
    and "length fals = DIM('a::executable_euclidean_space)"
    and "length faus = DIM('a::executable_euclidean_space)"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  by (auto intro!: bounded_by_Nil
      dest!: approxs_eucl[where 'a='a] list_of_eucl_eqD plain_floatariths_approx_eq_SomeD[where prec=prec]
        split: option.splits)

lemma approx_subset_listI:
  "list_interval (approxs2 prec fals []) (approxs1 prec faus []) \<subseteq> list_interval l u"
  if "l = interpret_floatariths fals []"
    and "u = interpret_floatariths faus []"
    and "length fals = length l"
    and "length faus = length u"
    and "approxs_defined prec fals []"
    and "approxs_defined prec faus []"
  using that
  apply (auto
      simp: list_interval_def list_all2_conv_all_nth
      dest: approxs_eq_Some_lengthD
      intro!: bounded_by_Nil
      dest!: plain_floatariths_approx_eq_SomeD[where prec=prec]
      split: option.splits)
   apply (rule order_trans)
    apply (rule approxs_pointwise_ge)
      apply assumption
     apply (rule bounded_by_Nil)
    apply (auto dest: approxs_eq_Some_lengthD)
  apply (subst interpret_floatariths_nth)
   apply (auto dest: approxs_eq_Some_lengthD)
    apply (rule approxs_pointwise_le[ge])
      apply assumption
     apply (rule bounded_by_Nil)
  apply (auto dest: approxs_eq_Some_lengthD)
  done


definition "unit_list D n = (replicate D 0)[n:=1]"

definition "mirror_sctn (sctn::real list sctn) = Sctn (map uminus (normal sctn)) (- pstn sctn)"
definition "mirrored_sctn b (sctn::real list sctn) = (if b then mirror_sctn sctn else sctn)"

lemma mirror_sctn_simps[simp]: "pstn (mirror_sctn sctn) = - pstn sctn"
  "normal (mirror_sctn sctn) = map uminus (normal sctn)"
  by (cases sctn) (auto simp: mirror_sctn_def)

lemma length_unit_list[simp]: "length (unit_list D n) = D"
  by (auto simp: unit_list_def)

lemma eucl_of_list_unit_list[simp]:
  "(eucl_of_list (unit_list D n)::'a::executable_euclidean_space) = Basis_list ! n"
  if "D = DIM('a)" "n < D"
  using that
  by (auto simp: unit_list_def eucl_of_list_inner inner_Basis nth_list_update'
      intro!: euclidean_eqI[where 'a='a])

lemma le_eucl_of_list_iff: "(t::'a::executable_euclidean_space) \<le> eucl_of_list uX0 \<longleftrightarrow>
  (\<forall>i. i < DIM('a) \<longrightarrow> t \<bullet> Basis_list ! i \<le> uX0 ! i)"
  if "length uX0 = DIM('a)"
  using that
  apply (auto simp: eucl_le[where 'a='a] eucl_of_list_inner)
  using nth_Basis_list_in_Basis apply force
  by (metis Basis_list in_Basis_index_Basis_list index_less_size_conv length_Basis_list)

lemma eucl_of_list_le_iff: "eucl_of_list uX0 \<le> (t::'a::executable_euclidean_space) \<longleftrightarrow>
  (\<forall>i. i < DIM('a) \<longrightarrow> uX0 ! i \<le> t \<bullet> Basis_list ! i)"
  if "length uX0 = DIM('a)"
  using that
  apply (auto simp: eucl_le[where 'a='a] eucl_of_list_inner)
  using nth_Basis_list_in_Basis apply force
  by (metis Basis_list in_Basis_index_Basis_list index_less_size_conv length_Basis_list)

lemma Joints_aforms_of_ivls: "Joints (aforms_of_ivls lX0 uX0) = list_interval lX0 uX0"
  if "list_all2 (\<le>) lX0 uX0"
  using that
  apply (auto simp: list_interval_def dest: Joints_aforms_of_ivlsD1[OF _ that]
      Joints_aforms_of_ivlsD2[OF _ that] list_all2_lengthD
      intro!: aforms_of_ivls)
  by (auto simp: list_all2_conv_all_nth)

lemma list_of_eucl_in_list_interval_iff:
  "list_of_eucl x0 \<in> list_interval lX0 uX0 \<longleftrightarrow> x0 \<in> {eucl_of_list lX0 .. eucl_of_list uX0::'a}"
  if "length lX0 = DIM('a::executable_euclidean_space)"
     "length uX0 = DIM('a::executable_euclidean_space)"
  using that
  by (auto simp: list_interval_def eucl_of_list_le_iff le_eucl_of_list_iff list_all2_conv_all_nth)


text \<open>TODO: make a tactic out of this?!\<close>

lemma file_output_iff: "file_output s f = f (\<lambda>_. ())"
  by (auto simp: file_output_def print_def[abs_def] Print.file_output_def)

context ode_interpretation begin

lemma poincare_mapsto_subset:
     "poincare_mapsto P  X0 SS CX R"
  if "poincare_mapsto P' Y0 RR CZ S" "X0 \<subseteq> Y0" "CZ \<subseteq> CX" "S \<subseteq> R" "RR = SS" "P = P'"
  using that
  by (force simp: poincare_mapsto_def)

theorem solves_poincare_map_aform'_derivI:
  assumes solves:
    "solves_poincare_map_aform'_fo optns odo
      (Sctn (unit_list D n) (lP ! n))
      guards
      (lP, uP)
      (Sctn (unit_list D n) (lP ! n))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))]
      (lR, uR)
      (Some (lDR, uDR))"
    and D: "D = DIM('a)"
  assumes DS: "list_interval lDR uDR \<subseteq> list_interval lDS uDS"
  and dim: "aform.D odo = DIM('a)"
  and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
    "length DX0 = DIM('a)*DIM('a)"
    "length lDR = CARD('n) * CARD('n)"
    "length uDR = CARD('n) * CARD('n)"
    and guards:
    "(\<And>a xs b ba ro.
        (xs, ro) \<in> set guards \<Longrightarrow>
      ((a, b), ba) \<in> set xs \<Longrightarrow>
          length a = DIM('a) \<and> length b = DIM('a) \<and> length (normal ba) = DIM('a))"
  and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
  and plane: "uP ! n = lP ! n"
  and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
  and nD: "n < DIM('a)"
  and SS: "SS = {x::'a. x \<bullet> Basis_list ! n \<le> lP ! n}"
  and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
  shows "\<forall>x\<in>X0. returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
proof (rule ballI)
  fix x assume "x \<in> X0"
  then have la2: "list_all2 (\<le>) lX0 uX0"
    using X0
    by (force simp: subset_iff eucl_of_list_le_iff le_eucl_of_list_iff lens list_all2_conv_all_nth)
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens power2_eq_square)
  have 2: "length (normal (Sctn (unit_list D n) (lP ! n))) = DIM('a)"
    by (auto simp: D)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (Sctn (unit_list D n) (lP ! n))) = DIM('a)"
    by (auto simp: D)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lDR, uDR))"
    by (auto simp: lens aform.lvivl'_invar_def)
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have "poincare_mapsto
     (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))])
     (below_halfspace
       (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (aform.Csafe odo -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' (Some (lDR, uDR)))"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 dim 2 3 4 guards 5])
      auto
  then have "poincare_mapsto P (X0 \<times> {blinfun_of_list DX0}::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set) SS UNIV
    (R \<times> blinfuns_of_lvivl (lDS, uDS))"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def
          aform.c1_info_of_apprse_def)
      subgoal for x0
        apply (rule image_eqI[where x="list_of_eucl x0@DX0"])
        using lens
         apply (auto simp: flow1_of_list_def aforms_of_point_def Joints_aforms_of_ivls_append_point)
        apply (rule imageI)
        using X0
        by (auto simp: Joints_aforms_of_ivls la2 list_of_eucl_in_list_interval_iff)
      done
    subgoal by simp
    subgoal using R DS
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_def
          lens)
    subgoal
      using assms
      by (simp add: below_halfspace_def le_halfspace_def[abs_def])
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff)
    done
  then show "returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
    using \<open>x \<in> X0\<close>
    by (auto simp: poincare_mapsto_def)
qed

definition guards_invar::"nat \<Rightarrow> (((real list \<times> real list) \<times> real list sctn) list \<times>
    (real \<times> real pdevs) reach_options) list \<Rightarrow> bool"
  where "guards_invar D guards = (\<forall>(xs, ro) \<in> set guards.
    \<forall>((a, b), ba) \<in> set xs. length a = D \<and> length b = D \<and> length (normal ba) = D)"

theorem solves_poincare_map_aform'I:
  assumes "TAG_optns optns"
  assumes "TAG_reach_optns roi"
  assumes "TAG_sctn mirrored"
  assumes D: "D = DIM('a)"
  assumes guards: "guards_invar DIM('a) guards"
  and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
  and plane: "uP ! n = lP ! n"
  and dim: "aform.D odo = DIM('a)"
  and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
  and nD: "n < DIM('a)"
  and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
  and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
  and solves:
    "solves_poincare_map_aform'_fo optns odo
      (Sctn (unit_list D n) (lP ! n))
      guards
      (lP, uP)
      (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, None)]
      (lR, uR)
      None"
shows "\<forall>x\<in>X0. returns_to P x \<and> poincare_map P x \<in> R"
proof -
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, None)] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens)
  have 2: "length (normal ((mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n))))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (((Sctn (unit_list D n) (lP ! n))))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  from guards have guards: "(xs, ro) \<in> set guards \<Longrightarrow>
       ((a, b), ba) \<in> set xs \<Longrightarrow>
       length a = DIM('a) \<and>
       length b = DIM('a) \<and> length (normal ba) = DIM('a)" for xs ro a b ba
    by (auto simp: guards_invar_def)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) None"
    by (auto simp: lens)
  have "poincare_mapsto
    (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
    (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, None)])
    (below_halfspace (map_sctn eucl_of_list (Sctn (unit_list D n) (lP ! n))))
    (aform.Csafe odo -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' None)"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 dim 2 3 4 guards 5])
  then have "poincare_mapsto P (X0 \<times> UNIV::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set)
      (below_halfspace (map_sctn eucl_of_list (((Sctn (unit_list D n) (lP ! n)))))) UNIV (R \<times> UNIV)"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_apprse_def aform.c1_info_of_appre_def
          aform.c1_info_of_appr_def)
      apply (rule image_eqI) apply (rule eucl_of_list_list_of_eucl[symmetric])
      apply (rule aforms_of_ivls)
      by (auto simp add: lens subset_iff le_eucl_of_list_iff eucl_of_list_le_iff)
    subgoal by simp
    subgoal using R by (auto simp: set_of_lvivl_def set_of_ivl_def)
    subgoal
      using assms
      by (simp add: below_halfspace_def le_halfspace_def[abs_def])
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff mirrored_sctn_def mirror_sctn_def)  
    done
  then show "\<forall>x\<in>X0. returns_to P x \<and> poincare_map P x \<in> R"
    by (auto simp: poincare_mapsto_def)
qed

definition "poincare_map_from_outside = poincare_map"

theorem poincare_maps_onto_aformI:
  assumes "TAG_optns optns"
  assumes "TAG_reach_optns roi"
  assumes "TAG_sctn mirrored"
  assumes D: "D = DIM('a)"
  assumes guards: "guards_invar DIM('a) guards"
  and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
  and plane: "uP ! n = lP ! n"
  and dim: "aform.D odo = DIM('a)"
  and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
  and nD: "n < DIM('a)"
  and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
  and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
  and solves:
    "solves_poincare_map_onto_aform_fo optns odo
      guards
      (lP, uP)
      (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, None)]
      (lR, uR)
      None"
shows "\<forall>x\<in>X0. returns_to P x \<and> poincare_map_from_outside P x \<in> R"
proof -
  note solves = solves[unfolded solves_poincare_map_onto_aform_fo_def file_output_iff]
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, None)] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens)
  have 2: "length (normal ((mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n))))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  from guards have guards: "(xs, ro) \<in> set guards \<Longrightarrow>
       ((a, b), ba) \<in> set xs \<Longrightarrow>
       length a = DIM('a) \<and>
       length b = DIM('a) \<and> length (normal ba) = DIM('a)" for xs ro a b ba
    by (auto simp: guards_invar_def)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) None"
    by (auto simp: lens)
  have "poincare_mapsto
    (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
    (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, None)])
    UNIV
    (aform.Csafe odo -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' None)"
    by (rule solves_poincare_map_onto_aform[OF solves, OF 1 dim 2 3 guards 5])
  then have "poincare_mapsto P (X0 \<times> UNIV::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set) UNIV UNIV (R \<times> UNIV)"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_apprse_def aform.c1_info_of_appre_def
          aform.c1_info_of_appr_def)
      apply (rule image_eqI) apply (rule eucl_of_list_list_of_eucl[symmetric])
      apply (rule aforms_of_ivls)
      by (auto simp add: lens subset_iff le_eucl_of_list_iff eucl_of_list_le_iff)
    subgoal by simp
    subgoal using R by (auto simp: set_of_lvivl_def set_of_ivl_def)
    subgoal by simp
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff mirrored_sctn_def mirror_sctn_def)  
    done
  then show "\<forall>x\<in>X0. returns_to P x \<and> poincare_map_from_outside P x \<in> R"
    by (auto simp: poincare_mapsto_def poincare_map_from_outside_def)
qed

end

lemmas [simp] = length_approxs

context includes ode_ops.lifting begin
lift_definition empty_ode_ops::"ode_ops" is "([], true_form)"
  by (auto simp: )
end

ML \<open>val ode_numerics_conv = @{computation_check
  terms:
    Trueprop

    Not

    solves_one_step_until_time_aform_fo
    solves_poincare_map_aform'_fo
    solves_poincare_map_onto_aform_fo

    num_options
    num_options_c1
    ro

    (* nat *)
    Suc "0::nat" "1::nat" "(+)::nat \<Rightarrow> nat \<Rightarrow> nat" "(-) ::nat \<Rightarrow> nat \<Rightarrow> nat" "(=)::nat\<Rightarrow>nat\<Rightarrow>bool"
    "(^)::nat\<Rightarrow>nat\<Rightarrow>nat"

    (* int / integer*)
    "(=)::int\<Rightarrow>int\<Rightarrow>bool"
    "(+)::int\<Rightarrow>int\<Rightarrow>int"
    "uminus::_\<Rightarrow>int"
    "uminus::_\<Rightarrow>integer"
    int_of_integer integer_of_int
    "0::int"
    "1::int"
    "(^)::int\<Rightarrow>nat\<Rightarrow>int"

    (* real *)
    "(=)::real\<Rightarrow>real\<Rightarrow>bool"
    "real_of_float"
    "(/)::real\<Rightarrow>real\<Rightarrow>real"
    "(^)::real\<Rightarrow>nat\<Rightarrow>real"
    "uminus::real\<Rightarrow>_"
    "(+)::real\<Rightarrow>real\<Rightarrow>real" "(-)::real\<Rightarrow>real\<Rightarrow>real"  "(*)::real\<Rightarrow>real\<Rightarrow>real"
    real_divl real_divr
    real_of_int
    "0::real"
    "1::real"

    (* rat *)
    Fract
    "0::rat"
    "1::rat"
    "(+)::rat\<Rightarrow>rat\<Rightarrow>rat"
    "(-)::rat\<Rightarrow>rat\<Rightarrow>rat"
    "(*)::rat\<Rightarrow>rat\<Rightarrow>rat"
    "uminus::rat\<Rightarrow>_"
    "(/)::rat\<Rightarrow>rat\<Rightarrow>rat"
    "(^)::rat\<Rightarrow>nat\<Rightarrow>rat"

    (* ereal *)
    "1::ereal"

    (* lists: *)
    "replicate::_\<Rightarrow>real\<Rightarrow>_"
    "unit_list::_\<Rightarrow>_\<Rightarrow>real list"
    "Nil::(nat \<times> nat \<times> string) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string) list"
    "Nil::(nat \<times> nat \<times> string \<times> nat list) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string \<times> nat list) list"
    "Nil::real list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real list"
    "Nil::nat list"
    "Cons::_\<Rightarrow>_\<Rightarrow>nat list"
    "Nil::string list"
    "Cons::_\<Rightarrow>_\<Rightarrow>string list"
    "Nil::real aform list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real aform list"
    "Nil::(float interval) option list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(float interval) option list"

    "nth::_\<Rightarrow>_\<Rightarrow>real"
    "upt"

    (* products: *)
    "Pair::_\<Rightarrow>_\<Rightarrow>(nat \<times> string)"
    "Pair::_\<Rightarrow>_\<Rightarrow>(nat \<times> nat \<times> string)"

    "Pair::_\<Rightarrow>_\<Rightarrow>char list \<times> nat list"
    "Pair::_\<Rightarrow>_\<Rightarrow>nat \<times> char list \<times> nat list"
    "Pair::_\<Rightarrow>_\<Rightarrow>nat \<times> nat \<times> char list \<times> nat list"

    "Pair::_\<Rightarrow>_\<Rightarrow>char list \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow> (real \<times> real pdevs) numeric_options)"
    "Pair::_\<Rightarrow>_\<Rightarrow>ereal\<times>ereal"
    "Pair::_\<Rightarrow>_\<Rightarrow>real aform list \<times> real aform list option"
    "Pair::_\<Rightarrow>_\<Rightarrow>(ereal \<times> ereal) \<times> real aform list \<times> real aform list option"

    "Pair::_\<Rightarrow>_\<Rightarrow>real aform"
    "Pair::_\<Rightarrow>_\<Rightarrow>real list \<times> real list"

    "Nil::(((real list \<times> real list) \<times> real list sctn) list \<times> (real aform) reach_options) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(((real list \<times> real list) \<times> real list sctn) list \<times> (real aform) reach_options) list"
    "Nil::((real list \<times> real list) \<times> real list sctn) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list"

    "Pair::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list \<times> real aform reach_options"

    "Nil::((ereal \<times> ereal) \<times> (real aform) list \<times> (real aform) list option) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>((ereal \<times> ereal) \<times> (real aform) list \<times> (real aform) list option) list"

    (* option *)
    "None::(real aform) list option"
    "Some::_\<Rightarrow>(real aform) list option"
    "None::(real list \<times> real list) option"
    "Some::_\<Rightarrow>(real list \<times> real list) option"

    (* aforms *)
    "aform_of_ivl::_\<Rightarrow>_\<Rightarrow>real aform"
    aforms_of_ivls
    aforms_of_point

    (* pdevs*)
    "zero_pdevs::real pdevs"
    "zero_aforms::_ \<Rightarrow> real aform list"

    (* ode_ops *)
    mk_ode_ops
    init_ode_ops
    empty_ode_ops
    can_mk_ode_ops
    "the::ode_ops option \<Rightarrow> ode_ops"
    the_odo

    (* Characters/Strings *)
    String.Char
    String.implode
    "Nil::string"
    "Cons::_\<Rightarrow>_\<Rightarrow>string"

    (* float *)
    "(=)::float\<Rightarrow>float\<Rightarrow>bool" "(+)::float\<Rightarrow>float\<Rightarrow>float" "uminus::_\<Rightarrow>float" "(-)::_\<Rightarrow>_\<Rightarrow>float"
    Float float_of_int float_of_nat

    (* approximation... *)
    approx
    approx1
    approx2
    approxs1
    approxs2
    approx_defined
    approxs_defined

    (* floatarith *)
    "0::floatarith"
    "1::floatarith"
    "(+)::_\<Rightarrow>_\<Rightarrow>floatarith"
    "(-)::_\<Rightarrow>_\<Rightarrow>floatarith"
    "(*)::_\<Rightarrow>_\<Rightarrow>floatarith"
    "(/)::_\<Rightarrow>_\<Rightarrow>floatarith"
    "inverse::_\<Rightarrow>floatarith"
    "uminus::_\<Rightarrow>floatarith"
    "Sum\<^sub>e::_\<Rightarrow>nat list\<Rightarrow>floatarith"
    Sin Half Tan
    R\<^sub>e Norm

    (* form *)
    true_form
    Half

    (* Printing *)
    print
    no_print

    (* sections *)
    xsec xsec' ysec ysec' zsec zsec'
    xsec2 xsec2' ysec2 ysec2'
    ysec4 ysec4'
    mirrored_sctn

    Code_Target_Nat.natural
    Code_Target_Int.positive
    Code_Target_Int.negative
    Code_Numeral.positive
    Code_Numeral.negative

  datatypes:
    bool
    num
    floatarith
    "floatarith list"
    form
    "real list sctn"
    "real \<times> real"
}
\<close>
ML \<open>fun ode_numerics_tac ctxt =
  CONVERSION (ode_numerics_conv ctxt) THEN' (resolve_tac ctxt [TrueI])\<close>

lemma eq_einterpretI:
  assumes "list_of_eucl (VS::'a::executable_euclidean_space) = interpret_floatariths fas xs"
  assumes "length fas = DIM('a)"
  shows "VS = eucl_of_list (interpret_floatariths fas xs)"
  using assms
  apply (subst (asm) list_of_eucl_eucl_of_list[symmetric])
  apply (auto intro!: )
  by (metis eucl_of_list_list_of_eucl)

lemma one_add_square_ne_zero[simp]: "1 + t * t \<noteq> 0" for t::real
  by (metis semiring_normalization_rules(12) sum_squares_eq_zero_iff zero_neq_one)

lemma abs_rat_bound:
  "abs (x - y) \<le> e / f" if "y \<in> {yl .. yu}" "x \<in> {yu - real_divl p e f.. yl + real_divl p e f}" for x y e::real
proof -
  note \<open>x \<in> _\<close>
  also have "{yu - real_divl p e f.. yl + real_divl p e f} \<subseteq> {yu - e / f .. yl + e / f}"
    by (auto intro!: diff_mono real_divl)
  finally show ?thesis
    using that
    unfolding abs_diff_le_iff
    by auto
qed

lemma in_ivl_selfI: "a \<in> {a .. a}" for a::real by auto

lemma pi4_bnds: "pi / 4 \<in> {real_divl 80 (lb_pi 80) 4 .. real_divr 80 (ub_pi 80) 4}"
  using pi_boundaries[of 80]
  unfolding atLeastAtMost_iff
  by (intro conjI real_divl[le] real_divr[ge] divide_right_mono) auto

lemma abs_minus_leI: "\<bar>x - x'\<bar> \<le> e" if "x \<in> {x' - e .. x' + e}" for x e::real
  using that
  by (auto simp: )

lemmas [DIM_simps] = Suc_numeral One_nat_def[symmetric] TrueI Suc_1 length_approxs arith_simps
lemma (in ode_interpretation) length_ode_e[DIM_simps]: "length (ode_expression odo) = DIM('a)"
  by (auto simp: len)


named_theorems solves_one_step_ivl_thms

context ode_interpretation begin

lemmas [solves_one_step_ivl_thms] =
  TAG_optns[OF solves_one_step_ivl[OF _ _ _ _ _ _ _ _ solves_one_step_until_time_aform_foI], rotated -1,
    of optns _ _ _ _ _ _ _ _ _ optns for optns]

lemmas [solves_one_step_ivl_thms] =
  TAG_optns[OF solves_one_step_ivl'[OF _ _ _ _ _ _ _ _ _ _ _ _ solves_one_step_until_time_aform_foI], rotated -1,
    of optns _ _ _ _ _ _ _ _ _ _ _ _ _ _ optns for optns]

lemmas [solves_one_step_ivl_thms] = solves_poincare_map_aform'I poincare_maps_onto_aformI

end

lemma TAG_optnsI: "TAG_optns optns" by simp

named_theorems poincare_tac_theorems

lemmas [DIM_simps] = one_less_numeral_iff rel_simps


abbreviation "point_ivl a \<equiv> {a .. a}"

lemma isFDERIV_compute: "isFDERIV D vs fas xs \<longleftrightarrow>
   (list_all (\<lambda>i. list_all (\<lambda>j. isDERIV (vs ! i) (fas ! j) xs) [0..<D]) [0..<D]) \<and> length fas = D \<and> length vs = D"
  unfolding isFDERIV_def
  by (auto simp: list.pred_set)


theorem (in ode_interpretation) solves_poincare_map_aform'_derivI'[solves_one_step_ivl_thms]:
\<comment> \<open>TODO: replace @{thm solves_poincare_map_aform'_derivI}\<close>
  assumes "TAG_optns optns"
  assumes "TAG_reach_optns roi"
  assumes "TAG_sctn mirrored"
    and D: "D = DIM('a)"
  assumes DS: "list_interval lDR uDR \<subseteq> list_interval lDS uDS"
    and ode_fas: "aform.D odo = DIM('a)"
    and guards: "guards_invar DIM('a) guards"
    and P: "P = {eucl_of_list lP .. eucl_of_list uP}"
    and plane: "uP ! n = lP ! n"
    and X0: "X0 \<subseteq> {eucl_of_list lX0 .. eucl_of_list uX0}"
    and nD: "n < DIM('a)"
    and R: "{eucl_of_list lR .. eucl_of_list uR} \<subseteq> R"
    and lens:
    "length (lP) = DIM('a)" "length (uP) = DIM('a)"
    "length (lX0) = DIM('a)" "length (uX0) = DIM('a)"
    "length (lR) = DIM('a)" "length (uR) = DIM('a)"
    "length DX0 = DIM('a)*DIM('a)"
    "length lDR = CARD('n) * CARD('n)"
    "length uDR = CARD('n) * CARD('n)"
    and SS: "SS = {x::'a. if mirrored then x \<bullet> Basis_list ! n \<le> lP ! n
        else x \<bullet> Basis_list ! n \<ge> lP ! n}"
  assumes solves:
    "solves_poincare_map_aform'_fo optns odo
      (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))
      guards
      (lP, uP)
      (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))
      roi
      [((1,1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))]
      (lR, uR)
      (Some (lDR, uDR))"
  shows "\<forall>x\<in>X0. returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
proof (rule ballI)
  fix x assume "x \<in> X0"
  then have la2: "list_all2 (\<le>) lX0 uX0"
    using X0
    by (force simp: subset_iff eucl_of_list_le_iff le_eucl_of_list_iff lens list_all2_conv_all_nth)
  have 1: "\<And>X. X \<in> set [((1::ereal, 1::ereal), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))] \<Longrightarrow>
      aform.c1_info_invare DIM('a) X"
    for X
    by (auto simp: aform.c1_info_invare_def aform.c1_info_invar_def lens power2_eq_square)
  have 2: "length (normal (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 3: "length (fst (lP, uP)) = DIM('a)" "length (snd (lP, uP)) = DIM('a)"
    by (auto simp: lens)
  have 4: "length (normal (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))) = DIM('a)"
    by (auto simp: D mirrored_sctn_def)
  have 5: "length (fst (lR, uR)) = CARD('n)" "length (snd (lR, uR)) = CARD('n)"
    "aform.lvivl'_invar (CARD('n) * CARD('n)) (Some (lDR, uDR))"
    by (auto simp: lens aform.lvivl'_invar_def)
  note solves = solves[unfolded solves_poincare_map_aform'_fo_def file_output_iff]
  have "poincare_mapsto
     (set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (aform.c1_info_of_apprse [((1, 1), aforms_of_ivls lX0 uX0, Some (aforms_of_point DX0))])
     (below_halfspace (map_sctn eucl_of_list (mirrored_sctn (\<not>mirrored) (Sctn (unit_list D n) (lP ! n)))))
     (aform.Csafe odo -
      set_of_lvivl (lP, uP) \<inter>
      plane_of (map_sctn eucl_of_list (mirrored_sctn mirrored (Sctn (unit_list D n) (lP ! n)))))
     (set_of_lvivl (lR, uR) \<times> blinfuns_of_lvivl' (Some (lDR, uDR)))"
    by (rule solves_poincare_map_aform'[OF solves, OF 1 ode_fas 4 3 2 _ 5])
      (use guards in \<open>auto simp: guards_invar_def\<close>)
  then have "poincare_mapsto P (X0 \<times> {blinfun_of_list DX0}::('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set) SS UNIV
    (R \<times> blinfuns_of_lvivl (lDS, uDS))"
    apply (rule poincare_mapsto_subset)
    subgoal using X0
      apply (auto simp: aform.c1_info_of_appre_def aform.c1_info_of_appr_def
          aform.c1_info_of_apprse_def)
      subgoal for x0
        apply (rule image_eqI[where x="list_of_eucl x0@DX0"])
        using lens
         apply (auto simp: flow1_of_list_def aforms_of_point_def Joints_aforms_of_ivls_append_point)
        apply (rule imageI)
        using X0
        by (auto simp: Joints_aforms_of_ivls la2 list_of_eucl_in_list_interval_iff)
      done
    subgoal by simp
    subgoal using R DS
      by (auto simp: set_of_lvivl_def set_of_ivl_def blinfuns_of_lvivl'_def blinfuns_of_lvivl_def
          lens)
    subgoal
      using assms
      by (auto simp:
          below_halfspace_def le_halfspace_def[abs_def] mirrored_sctn_def mirror_sctn_def)
    subgoal
      using assms
      by (fastforce simp add: P set_of_lvivl_def set_of_ivl_def plane_of_def
          le_eucl_of_list_iff eucl_of_list_le_iff mirrored_sctn_def mirror_sctn_def)
    done
  then show "returns_to P x \<and>
    return_time P differentiable at x within SS \<and>
    (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within SS) \<and>
         poincare_map P x \<in> R \<and> D o\<^sub>L blinfun_of_list DX0 \<in> blinfuns_of_lvivl (lDS, uDS))"
    using \<open>x \<in> X0\<close>
    by (auto simp: poincare_mapsto_def)
qed

lemmas [DIM_simps] = aform.ode_e_def

ML \<open>
structure ODE_Numerics_Tac = struct
fun mk_nat n = HOLogic.mk_number @{typ nat} n
fun mk_int n = HOLogic.mk_number @{typ int} n
fun mk_integer n = @{term integer_of_int} $ (HOLogic.mk_number @{typ int} n)
fun mk_bool b = if b then @{term True} else @{term False}

fun mk_numeralT n =
  let
    fun mk_bit 0 ty = Type (@{type_name bit0}, [ty])
      | mk_bit 1 ty = Type (@{type_name bit1}, [ty]);
    fun bin_of n =
      if n = 1 then @{typ num1}
      else if n = 0 then @{typ num0}
      else if n = ~1 then raise TERM ("negative type numeral", [])
      else
        let val (q, r) = Integer.div_mod n 2;
        in mk_bit r (bin_of q) end;
  in bin_of n end;

fun print_tac' ctxt s = K (print_tac ctxt s)

val using_master_directory =
  File.full_path o Resources.master_directory o Proof_Context.theory_of;

fun using_master_directory_term ctxt s =
  (if s = "-" orelse s = ""
  then s
  else
    Path.explode s
    |> using_master_directory ctxt
    |> Path.implode)
  |> HOLogic.mk_string

fun real_in_approx_tac ctxt p =
  let
    val inst_approx =
       ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
    val approx_thm = Thm.instantiate inst_approx @{thm real_in_approxI}
  in
    resolve_tac ctxt [approx_thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' ode_numerics_tac ctxt
  end

fun real_subset_approx_tac ctxt p =
  let
    val inst_approx =
       ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
    val approx_thm = Thm.instantiate inst_approx @{thm real_subset_approxI}
  in
    resolve_tac ctxt [approx_thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' ode_numerics_tac ctxt
      THEN' ode_numerics_tac ctxt
  end

fun basic_nt_ss ctxt nt =
  put_simpset HOL_basic_ss ctxt addsimps Named_Theorems.get ctxt nt

fun DIM_tac defs ctxt = (Simplifier.simp_tac (basic_nt_ss ctxt @{named_theorems DIM_simps} addsimps defs))

fun subset_approx_preconds_tac ctxt p thm =
  let
    val inst_approx = ([], [((("prec", 0), @{typ nat}), mk_nat p |> Thm.cterm_of ctxt)])
  in
            resolve_tac ctxt [Thm.instantiate inst_approx thm]
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (reify_floatariths_tac ctxt)
      THEN' SOLVED' (DIM_tac [] ctxt)
      THEN' SOLVED' (DIM_tac [] ctxt)
      THEN' SOLVED' (ode_numerics_tac ctxt)
      THEN' SOLVED' (ode_numerics_tac ctxt)
  end

val cfg_trace = Attrib.setup_config_bool @{binding ode_numerics_trace} (K false)
fun tracing_tac ctxt = if Config.get ctxt cfg_trace then print_tac ctxt else K all_tac
fun tracing_tac' ctxt = fn s => K (tracing_tac ctxt s)

fun eucl_subset_approx_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm eucl_subset_approxI}
fun approx_subset_eucl_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm approx_subset_euclI}
fun approx_subset_list_tac ctxt p = subset_approx_preconds_tac ctxt p @{thm approx_subset_listI}

val static_simpset = Simplifier.simpset_of @{context}

fun nth_tac ctxt =
  Simplifier.simp_tac
    (put_simpset HOL_basic_ss ctxt addsimps @{thms nth_Cons_0 nth_Cons_Suc numeral_nat})
fun nth_list_eq_tac ctxt n = Subgoal.FOCUS_PARAMS (fn {context, concl, ...} =>
  case try (Thm.term_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) concl
  of
    SOME (@{const List.nth(real)} $ xs $ Var _, @{const List.nth(real)} $ ys $ Var _) =>
    let
      val i = find_index (op=) (HOLogic.dest_list xs ~~ HOLogic.dest_list ys)
      val thm = Goal.prove context [] []
        (HOLogic.mk_eq (@{const List.nth(real)} $ xs $ HOLogic.mk_number @{typ nat} i,
          @{const List.nth(real)} $ ys $ HOLogic.mk_number @{typ nat} i) |> HOLogic.mk_Trueprop)
        (fn {context, ...} => HEADGOAL (nth_tac context))
    in
      SOLVE (HEADGOAL (resolve_tac context [thm]))
    end
  | _ => no_tac
  ) ctxt n

fun numeric_precond_step_tac defs thms p = Subgoal.FOCUS_PARAMS (fn {context, concl, ...} =>
  let
    val prems = Logic.strip_imp_prems (Thm.term_of concl)
    val conclusion = Logic.strip_imp_concl (Thm.term_of concl)
  in
    (case conclusion |> HOLogic.dest_Trueprop of
      @{const Set.member(real)} $ _ $ _ =>
        tracing_tac context "numeric_precond_step: real in approx"
        THEN HEADGOAL (real_in_approx_tac context p)
    | Const(@{const_name less_eq}, _) $
      (Const (@{const_name atLeastAtMost}, _) $ _ $ _) $
      (Const (@{const_name atLeastAtMost}, _) $ Var _ $ Var _)  =>
        tracing_tac context "numeric_precond_step: approx subset eucl"
        THEN HEADGOAL (real_subset_approx_tac context p)
    | Const (@{const_name less_eq}, _) $
        (Const (@{const_name atLeastAtMost}, _) $ (Const (@{const_name eucl_of_list}, _) $ Var _) $ _) $ _ =>
        tracing_tac context "numeric_precond_step: approx subset eucl"
        THEN HEADGOAL (approx_subset_eucl_tac context p)
    | Const (@{const_name less_eq}, _) $ _ $
        (Const (@{const_name atLeastAtMost}, _) $ (Const (@{const_name eucl_of_list}, _) $ Var _) $ _) =>
        tracing_tac context "numeric_precond_step: eucl subset approx"
        THEN HEADGOAL (eucl_subset_approx_tac context p)
    | Const (@{const_name less_eq}, _) $
      (@{const list_interval(real)} $ _ $ _) $
      (@{const list_interval(real)} $ _ $ _) =>
        tracing_tac context "numeric_precond_step: approx subset list"
        THEN HEADGOAL (approx_subset_list_tac context p)
    | @{const HOL.eq(nat)} $ _ $ _ =>
        tracing_tac context "numeric_precond_step: DIM_tac"
        THEN HEADGOAL (SOLVED' (DIM_tac [] context))
    | @{const less(nat)} $ _ $ _ =>
        tracing_tac context "numeric_precond_step: DIM_tac"
        THEN HEADGOAL (SOLVED' (DIM_tac [] context))
    | @{const HOL.eq(real)} $ (@{const nth(real)} $ _ $ _) $ (@{const nth(real)} $ _ $ _) =>
        tracing_tac context "numeric_precond_step: nth_list_eq_tac"
        THEN HEADGOAL (SOLVED' (nth_list_eq_tac context))
    | Const (@{const_name "HOL.eq"}, _) $ _ $
        (Const (@{const_name eucl_of_list}, _) $ (@{const interpret_floatariths} $ _ $ _)) =>
        tracing_tac context "numeric_precond_step: reify floatariths"
        THEN HEADGOAL (resolve_tac context @{thms eq_einterpretI} THEN' reify_floatariths_tac context)
    | t as _ $ _ =>
      let
        val (c, args) = strip_comb t
      in
        if member (op=)
          [@{const "solves_one_step_until_time_aform_fo"},
           @{const "solves_poincare_map_aform'_fo"},
           @{const "solves_poincare_map_onto_aform_fo"},
           @{const "can_mk_ode_ops"}
          ] c
        then
          tracing_tac context "numeric_precond_step: ode_numerics_tac"
          THEN HEADGOAL (
            CONVERSION (Simplifier.rewrite (put_simpset HOL_basic_ss context addsimps defs))
            THEN' tracing_tac' context "numeric_precond_step: ode_numerics_tac (unfolded)"
            THEN' ode_numerics_tac context)
        else if member (op=)
          [@{const "isFDERIV"}] c
        then
          tracing_tac context "numeric_precond_step: isFDERIV"
          THEN HEADGOAL (SOLVED'(Simplifier.asm_full_simp_tac
              (put_simpset static_simpset context addsimps (@{thms isFDERIV_def less_Suc_eq_0_disj isDERIV_Power_iff} @ thms @ defs))
              THEN' tracing_tac' context "numeric_precond_step: simplified isFDERIV"
          ))
        else
          tracing_tac context "numeric_precond_step: boolean, try thms"
          THEN HEADGOAL (SOLVED' (resolve_tac context thms))
      end
    | _ =>
        tracing_tac context "numeric_precond_step: boolean constant"
        THEN no_tac
    )
  end)

fun integral_bnds_tac_gen_start sstep d p m N atol filename ctxt i =
  let
    val insts =
       ([((("'i", 0), @{sort "{enum}"}), mk_numeralT (d + 1) |> Thm.ctyp_of ctxt)],
        [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
              (@{term num_options} $ mk_nat p $ mk_int sstep $ mk_nat m $ mk_nat N $ mk_int atol $
              @{term "[(0::nat, 1::nat, ''0x000000'')]"}))
          |> Thm.cterm_of ctxt),
        ((("safe_form", 0), @{typ form}), @{cterm true_form})
        ])
  in
          resolve_tac ctxt [Thm.instantiate insts @{thm solve_one_step_until_time_aform_integral_bounds}] i
    THEN (Lin_Arith.tac ctxt i ORELSE Simplifier.simp_tac ctxt i)
  end
fun integral_bnds_tac_gen sstep d p m N atol filename thms ctxt =
  integral_bnds_tac_gen_start sstep d p m N atol filename ctxt
  THEN_ALL_NEW_FWD REPEAT_ALL_NEW_FWD (numeric_precond_step_tac [] thms p ctxt)

val integral_bnds_tac = integral_bnds_tac_gen 5

fun mk_proj (m, n, s) = HOLogic.mk_tuple [mk_nat m, mk_nat n, HOLogic.mk_string s]
fun mk_projs projs = HOLogic.mk_list @{typ "nat \<times> nat \<times> string"} (map mk_proj projs)

fun mk_string_list ds = HOLogic.mk_list @{typ "string"} (map HOLogic.mk_string ds)
fun mk_nat_list ds = HOLogic.mk_list @{typ "nat"} (map mk_nat ds)
fun mk_proj_c1 (m, n, s, ds) = HOLogic.mk_tuple [mk_nat m, mk_nat n, HOLogic.mk_string s, mk_nat_list ds]
fun mk_projs_c1 projs = HOLogic.mk_list @{typ "nat \<times> nat \<times> string \<times> nat list"} (map mk_proj_c1 projs)

fun TAG_optns_thm p sstep m N atol projs filename ctxt =
  Thm.instantiate ([],
          [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
             @{term num_options} $ mk_nat p $ mk_int sstep $ mk_nat m $ mk_nat N $ mk_int atol $ mk_projs projs)
          |> Thm.cterm_of ctxt)]) @{thm TAG_optnsI}

fun TAG_optns_c1_thm p sstep m N atol projs ds filename ctxt =
  Thm.instantiate ([],
          [((("optns", 0), @{typ "string \<times> ((String.literal \<Rightarrow> unit) \<Rightarrow>(real aform) numeric_options)"}),
           HOLogic.mk_prod
             (using_master_directory_term ctxt filename,
             @{term num_options_c1} $ mk_nat p $ mk_int sstep $ mk_nat m $ mk_nat N $ mk_int atol $ mk_projs_c1 projs $
              mk_string_list ds)
          |> Thm.cterm_of ctxt)]) @{thm TAG_optnsI}

fun ode_bnds_tac_gen_start sstep p m N atol projs filename ctxt =
  tracing_tac' ctxt "solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
  THEN' tracing_tac' ctxt "resolved solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt [TAG_optns_thm p sstep m N atol projs filename ctxt]

fun ode_bnds_tac_gen sstep ode_defs p m N atol projs filename ctxt =
  ode_bnds_tac_gen_start sstep p m N atol projs filename ctxt
  THEN_ALL_NEW_FWD REPEAT_ALL_NEW_FWD (numeric_precond_step_tac ode_defs [] p ctxt)
val ode_bnds_tac = ode_bnds_tac_gen 5

fun ode'_bnds_tac_gen_start sstep p m N atol projs ds filename ctxt =
  tracing_tac' ctxt "solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
  THEN' tracing_tac' ctxt "resolved solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt [TAG_optns_c1_thm p sstep m N atol projs ds filename ctxt]
fun ode'_bnds_tac_gen sstep ode_defs p m N atol projs ds filename ctxt =
  ode'_bnds_tac_gen_start sstep p m N atol projs ds filename ctxt
  THEN_ALL_NEW_FWD REPEAT_ALL_NEW_FWD (numeric_precond_step_tac ode_defs [] p ctxt)

val ode'_bnds_tac = ode'_bnds_tac_gen 5

fun poincare_bnds_tac_gen_start sstep p m N atol projs filename ctxt =
  tracing_tac' ctxt "solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
  THEN' tracing_tac' ctxt "resolved solves_one_step_ivl_thms"
  THEN' resolve_tac ctxt [TAG_optns_thm p sstep m N atol projs filename ctxt]
fun poincare_bnds_tac_gen sstep ode_defs p m N atol projs filename ctxt =
   poincare_bnds_tac_gen_start sstep p m N atol projs filename ctxt
  THEN_ALL_NEW_FWD REPEAT_ALL_NEW_FWD (
    numeric_precond_step_tac ode_defs
      (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
      p
      ctxt)

val poincare_bnds_tac = poincare_bnds_tac_gen 5

fun poincare'_bnds_tac_gen_start sstep p m N atol projs filename ctxt =
         resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems solves_one_step_ivl_thms})
    THEN' resolve_tac ctxt [TAG_optns_thm p sstep m N atol projs filename ctxt]
fun poincare'_bnds_tac_gen sstep ode_defs p m N atol projs filename ctxt =
  poincare'_bnds_tac_gen_start sstep p m N atol projs filename ctxt
  THEN_ALL_NEW_FWD REPEAT_ALL_NEW_FWD (
    numeric_precond_step_tac ode_defs
      (Named_Theorems.get ctxt @{named_theorems poincare_tac_theorems})
      p
      ctxt)
val poincare'_bnds_tac = poincare'_bnds_tac_gen 5
end
\<close>

lemma (in auto_ll_on_open) Poincare_Banach_fixed_pointI:
  assumes "convex S" and c: "complete S" "S \<noteq> {}" and "S \<subseteq> T"
  assumes derivative_bounded: "\<forall>x\<in>S.
    poincare_map \<Sigma> x \<in> S \<and> (\<exists>D. (poincare_map \<Sigma> has_derivative D) (at x within T) \<and> onorm D \<le> B)"
  assumes B: "B < 1"
  shows "\<exists>!x. x \<in> S \<and> poincare_map \<Sigma> x = x"
  using c _ B
proof (rule banach_fix)
  from derivative_bounded c show "0 \<le> B"
    by (auto dest!: has_derivative_bounded_linear onorm_pos_le)
  from derivative_bounded show "poincare_map \<Sigma> ` S \<subseteq> S" by auto
  obtain D where D:
    "\<forall>x \<in> S. (poincare_map \<Sigma> has_derivative D x) (at x within T) \<and>
      onorm (D x) \<le> B"
    apply atomize_elim
    apply (rule bchoice)
    using derivative_bounded
    by auto
  with \<open>S \<subseteq> T\<close> have "(\<And>x. x \<in> S \<Longrightarrow> (poincare_map \<Sigma> has_derivative D x) (at x within S))"
    by (auto intro: has_derivative_within_subset)
  from bounded_derivative_imp_lipschitz[of S "poincare_map \<Sigma>" D B, OF this] \<open>convex S\<close> D c
    \<open>0 \<le> B\<close>
  have "B-lipschitz_on S (poincare_map \<Sigma>)" by auto
  then show "\<forall>x\<in>S. \<forall>y\<in>S. dist (poincare_map \<Sigma> x) (poincare_map \<Sigma> y) \<le> B * dist x y"
    by (auto simp: lipschitz_on_def)
qed

ML \<open>open ODE_Numerics_Tac\<close>

lemma isFDERIV_product: "isFDERIV n xs fas vs \<longleftrightarrow>
  length fas = n \<and> length xs = n \<and>
  list_all (\<lambda>(x, f). isDERIV x f vs) (List.product xs fas)"
  apply (auto simp: isFDERIV_def list_all2_iff in_set_zip list_all_length product_nth)
   apply (metis gt_or_eq_0 less_mult_imp_div_less mod_less_divisor not_less0)
  by auto

end
