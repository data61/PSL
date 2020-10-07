theory Abstract_Reachability_Analysis_C1
  imports
    Abstract_Reachability_Analysis
  "../Refinement/Weak_Set"
  "../Refinement/Refine_Parallel"
  "../Refinement/Refine_Default"
  "../Refinement/Refine_Phantom"
  "../Refinement/Refine_ScaleR2"
begin

definition blinfun_of_list :: "real list \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a::executable_euclidean_space"
  where "blinfun_of_list xs = blinfun_of_matrix (\<lambda>i j. xs ! ((index Basis_list i) * DIM('a) + (index Basis_list j)))"

definition vec1_of_list :: "real list \<Rightarrow> 'n::{finite, one, plus} vec1"
  where "vec1_of_list xs =
    (vector (take CARD('n) xs), vector (map (\<lambda>i. vector (nths xs {CARD('n)*i..CARD('n)*Suc i})) [1..<Suc (CARD('n))]))"

definition flow1_of_vec1 :: "'n vec1 \<Rightarrow> ('n rvec * ('n rvec \<Rightarrow>\<^sub>L 'n::finite rvec))"
  where "flow1_of_vec1 xs = (fst xs, blinfun_of_vmatrix (snd xs))"

definition vec1_of_flow1 :: "('n::finite eucl1) \<Rightarrow> 'n vec1"
  where "vec1_of_flow1 xs = (fst xs, matrix (snd xs))"

lemma vec1_of_flow1_flow1_of_vec1[simp]:
  "vec1_of_flow1 (flow1_of_vec1 X) = X"
  unfolding vec1_of_flow1_def flow1_of_vec1_def
  by (transfer) (auto simp: matrix_of_matrix_vector_mul)

definition "flow1_of_list xs =
  (eucl_of_list (take DIM('a::executable_euclidean_space) xs)::'a,
    blinfun_of_list (take (DIM('a)*DIM('a)) (drop DIM('a) xs @
    replicate (DIM('a)*DIM('a) - (length xs - DIM('a))) 0))::'a\<Rightarrow>\<^sub>L'a)"


lemma blinfun_of_list_eq_blinfun_of_vmatrix:
  assumes "length xs = CARD('n)*CARD('n::enum)"
  shows "blinfun_of_list xs = blinfun_of_vmatrix (eucl_of_list xs::((real, 'n) vec, 'n) vec)"
  using assms
  apply (auto simp: blinfun_of_list_def)
  apply (auto intro!: simp: blinfun_ext blinfun_of_vmatrix.rep_eq blinfun_of_matrix.rep_eq)
  subgoal for i
    apply (subst (2) eucl_of_list_list_of_eucl[symmetric, of i])
    apply (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
    by (auto simp: sum_Basis_sum_nth_Basis_list scaleR_sum_left intro!: sum.cong)
  done


definition "ghost_rel = Pair () ` UNIV"
consts i_ghost::interface
lemmas [autoref_rel_intf] = REL_INTFI[of ghost_rel i_ghost]
lemma ghost_relI: "((), x) \<in> ghost_rel" by (auto simp: ghost_rel_def)

definition [refine_vcg_def]: "GSPEC x = SPEC x"
lemma [autoref_op_pat_def]: "GSPEC x \<equiv> Autoref_Tagging.OP (GSPEC x)" by auto

lemma GSPEC_impl[autoref_rules]:
  assumes "SIDE_PRECOND (Ex P)"
  shows "(RETURN (), GSPEC P) \<in> \<langle>ghost_rel\<rangle>nres_rel"
  using assms by (auto simp: nres_rel_def ghost_rel_def GSPEC_def intro!: RETURN_SPEC_refine)

context approximate_sets_ode' begin

definition "c1_info_of_appr XD =
  (case snd XD of None \<Rightarrow> eucl_of_list ` set_of_appr (fst XD) \<times> UNIV
   | Some DD \<Rightarrow> flow1_of_list ` set_of_appr (fst XD @ DD))"
definition "c1_info_of_apprs x = \<Union>(set (map c1_info_of_appr x))"
definition "c1_info_of_appr' x = Affine_Code.the_default UNIV (map_option c1_info_of_apprs x)"
definition "c1_info_of_appre X = scaleR2 (fst (fst X)) (snd (fst X)) (c1_info_of_appr (snd X))"
definition "c1_info_of_apprse x = \<Union>(set (map c1_info_of_appre x))"


definition [simp]: "op_image_flow1_of_vec1 = (`) flow1_of_vec1"

definition [simp]: "op_image_flow1_of_vec1_coll = (`) flow1_of_vec1"

definition [simp]: "op_image_fst = (`) fst"

definition [refine_vcg_def]:
  "vec1rep CX = SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"

definition [simp]: "op_times_UNIV X = X \<times> UNIV"

definition appr1_rel::"(('b list \<times> 'b list option) \<times>
  ('a::executable_euclidean_space c1_info set)) set"
  where appr1_rel_internal: "appr1_rel = {((xs, None), X \<times> UNIV) |xs X. (xs, X) \<in> appr_rel} \<union>
{((xs, Some ys), X::('a c1_info) set) |xs ys X. X = flow1_of_list ` set_of_appr (xs @ ys) \<and>
  length xs = DIM('a::executable_euclidean_space) \<and>
  length ys = DIM('a) * DIM('a)}"

abbreviation "appr1e_rel \<equiv> \<langle>appr1_rel\<rangle>scaleR2_rel"

text \<open>TODO: remove \<open>...:::relation\<close> from this file\<close>
definition "solve_poincare_plane (n::'n::enum rvec) (CX::'n eucl1 set) = do {
    X \<leftarrow> mk_safe (((`) fst CX::'n rvec set));
    F \<leftarrow> ode_set (X);
    nonzero_component (ST ''solve_poincare_map: not nonzero!'') F n;
    let i = index Basis_list n;
    ASSERT (i < length solve_poincare_slp);
    vCX \<leftarrow> vec1rep CX;
    case vCX of None \<Rightarrow>
      do {
        RETURN (op_times_UNIV (X))
      }
    | Some vCX \<Rightarrow>
      do {
        (R::'n vec1 set) \<leftarrow> approx_slp_appr (map fold_const_fa (solve_poincare_fas i)) (solve_poincare_slp ! i) (list_of_eucl ` vCX);
        let R = (op_image_flow1_of_vec1 (R:::appr_rel):::appr1_rel);
        X \<leftarrow> mk_safe (op_image_fst R);
        F \<leftarrow> ode_set (X);
        nonzero_component (ST ''solve_poincare_map: not nonzero!'') (F) n;
        RETURN (R::'n eucl1 set)
      }
  }"

definition embed1::"'n::enum rvec \<Rightarrow> ('n rvec * (real^'n::enum^'n::enum))" where [simp]: "embed1 x = (x, 0)"

definition "choose_step1 (X::'n::enum eucl1 set) h = do {
    lX \<leftarrow> vec1rep X;
    case lX of None \<Rightarrow>
      do {
        sX \<leftarrow> mk_safe (fst ` X);
        (h, err, CX', X') \<leftarrow> choose_step sX h;
        \<^cancel>\<open>err \<leftarrow> width_spec (err:::appr_rel);\<close>
        RETURN (h, err \<times> UNIV, (CX') \<times> UNIV, (X') \<times> UNIV)
      }
    | Some vX \<Rightarrow>
      do {
        sX \<leftarrow> var.mk_safe vX;
        (h, err, CX', X') \<leftarrow> var.choose_step sX h;
        let CX' = flow1_of_vec1 ` ((CX':::appr_rel):::appr_rel);
        let X' = flow1_of_vec1 ` ((X':::appr_rel):::appr_rel);
        let err' = flow1_of_vec1 ` (err:::appr_rel);
        \<^cancel>\<open>err \<leftarrow> width_spec (fst ` (flow1_of_vec1 ` (err:::appr_rel)):::appr_rel);\<close>
        RETURN (h, err', CX', X'::'n eucl1 set)
      }
  }"

definition "plane1_of x = plane_of x \<times> UNIV"
definition "below1_halfspaces x = below_halfspaces x \<times> UNIV"
definition "sbelow1_halfspaces x = sbelow_halfspaces x \<times> UNIV"
abbreviation "plane1_invar_rel \<equiv> \<lambda>A. \<langle>(\<langle>lv_rel\<rangle>sctn_rel), A\<rangle>invar_rel plane1_of "

definition "c1_info_invar N XD \<longleftrightarrow> length (fst XD) = N \<and> (case snd XD of Some DD \<Rightarrow> length DD = (length (fst XD))\<^sup>2 | None \<Rightarrow> True)"

definition op_image_zerofst :: "('a \<times> 'c) set \<Rightarrow> ('a::zero \<times> 'c) set"
  where [simp]: "op_image_zerofst \<equiv> \<lambda>X. (\<lambda>x. (0, snd x)) ` X"

definition op_image_zerofst_vec :: "('n::enum vec1) set \<Rightarrow> ('n::enum vec1) set"
  where [simp]: "op_image_zerofst_vec \<equiv> \<lambda>X. (\<lambda>x. (0, snd x)) ` X"

definition [simp]: "op_image_embed1 X = embed1 ` X"

definition "inter_sctn1_spec (X::'n::enum eucl1 set) (sctn::'n rvec sctn) = do {
    R \<leftarrow> inter_sctn_spec (fst ` X) sctn;
    vX \<leftarrow> vec1rep X;
    case vX of None \<Rightarrow>
      do {
        let R1 = R \<times> UNIV;
        RETURN (R1, R1)
      }
    | Some X \<Rightarrow>
      do {
        let sctn = ((Sctn (embed1 (normal sctn)) (pstn sctn)::'n vec1 sctn));
        R1 \<leftarrow> inter_sctn_spec X sctn;
        let R2 = op_image_zerofst_vec X + op_image_embed1 R;
        RETURN ((flow1_of_vec1 ` R1), (flow1_of_vec1 ` R2))
      }
  }"

definition "op_image_fst_coll_nres XS = do {
    XSs \<leftarrow> sets_of_coll XS;
    FORWEAK XSs (RETURN op_empty_coll) (\<lambda>X.
      RETURN (mk_coll (op_image_fst X:::appr_rel))) (\<lambda>A B. RETURN (B \<union> A))
  }"

lemma op_image_fst_coll_nres_spec[le, refine_vcg]: "op_image_fst_coll_nres X \<le> SPEC (\<lambda>R. R = fst ` X)"
  unfolding op_image_fst_coll_nres_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>it s. fst ` \<Union>it \<subseteq> s \<and> s \<subseteq> fst ` X"])
    (auto, force+)

definition [simp]: "op_image_fst_coll = (`) fst"

definition "fst_safe_coll XS = do {
    C \<leftarrow> op_image_fst_coll_nres XS;
    mk_safe_coll (C:::clw_rel appr_rel)
  }"

definition [refine_vcg_def]:
  "vec1reps X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN (Some op_empty_coll))
      (\<lambda>x. do {
        x \<leftarrow> vec1rep x;
        RETURN (map_option mk_coll x:::\<langle>clw_rel appr_rel\<rangle>option_rel)
      })
      (\<lambda>a b.
        case (a, b) of (Some a, Some b) \<Rightarrow> RETURN (Some (b \<union> a))
        | _ \<Rightarrow> RETURN None)
  }"

definition "do_intersection_spec S guards ivl sctn X0 = (\<lambda>(PS, CXS).
    poincare_mapsto {x \<in> ivl. x \<in> plane_of sctn} X0 S CXS PS \<and>
      CXS \<inter> guards = {} \<and>
      CXS \<inter> ivl \<inter> plane_of sctn = {} \<and>
      fst ` PS \<inter> guards = {} \<and>
      fst ` PS \<subseteq> {x \<in> ivl. x \<in> plane_of sctn} \<and>
      fst ` PS \<union> CXS \<subseteq> Csafe \<and>
      0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` PS \<and>
      (\<forall>x\<in>PS. (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)))"

abbreviation "inter_sbelows X sctns \<equiv> mk_inter X (sbelow_halfspaces sctns)"

definition "list_of_appr1 X = fst X @ the_default [] (snd X)"

definition print_set1::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set1 _ _ = ()"

definition "nonzero_component_within ivl sctn PDP = do {
  fPDP \<leftarrow> mk_safe (fst ` PDP);
  F \<leftarrow> ode_set (fPDP);
  nonzero_component (ST ''solve_poincare_map: not nonzero!'') F (normal sctn);
  op_eventually_within_sctn (op_image_fst PDP:::appr_rel) sctn ivl
}"

definition "do_intersection_invar guards GUARDS ivl sctn X \<equiv> \<lambda>(X', T, PS, PS2, CXS, intersects, inside).
  (inside \<longrightarrow>
          (fst ` X \<inter> GUARDS = {} \<and>
          fst ` X \<subseteq> sbelow_halfspace sctn \<and>
          ivl \<subseteq> plane_of sctn \<and>
          fst ` X \<subseteq> CXS \<and>
          fst ` PS \<union> fst ` PS2 \<union> CXS \<union> fst ` X' \<subseteq> Csafe \<and>
          T \<subseteq> nonneg_reals \<and>
          (\<not>intersects \<longrightarrow> (fst ` X' \<inter> plane_of sctn = {} \<and> T = pos_reals)) \<and>
          CXS \<subseteq> (sbelow_halfspace sctn - guards) \<and>
          X' \<subseteq> (- guards) \<times> UNIV \<and>
          fst ` (PS \<union> PS2) \<inter> guards = {} \<and>
          (0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (PS \<union> PS2)) \<and>
          ((\<forall>x\<in>PS \<union> PS2. (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl))) \<and>
          (\<exists>A B. X = A \<union> B \<and>
            flowsto A T (CXS \<times> UNIV) (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) \<and>
            poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV CXS PS \<and>
            poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV CXS PS2)))"

definition "list_of_appr1e X = fst (snd X) @ the_default [] (snd (snd X)) @
  (let (l, u) = fst X;
    roer = (\<lambda>x. if x = - \<infinity> then FloatR 1 (-88) else if x = \<infinity> then FloatR 1 88 else real_of_ereal x)
  in
    appr_of_ivl ops [roer l] [roer u]
    )"

definition print_set1e::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set1e _ _ = ()"

definition trace_set1e::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set1e _ _ = ()"
definition trace_set1::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set1 _ _ = ()"

definition "split_spec_param1 X = do {
    (vX) \<leftarrow> vec1rep X;
    let D = CARD('n);
    case vX of None \<Rightarrow> do {
      (a, b) \<leftarrow> split_spec_param D (fst ` X::'n::finite rvec set);
      RETURN (a \<times> UNIV, b \<times> UNIV)
    }
    | Some X \<Rightarrow> do {
      (a, b) \<leftarrow> split_spec_param D X;
      RETURN (op_image_flow1_of_vec1 a, op_image_flow1_of_vec1 b)
    }
  }"

abbreviation iinfo_rel :: "('c \<times> 'a set) set \<Rightarrow> ((real \<times> 'c) \<times> 'a::real_normed_vector set) set"
where "iinfo_rel \<equiv> \<lambda>s. \<langle>rnv_rel, s\<rangle>info_rel"

definition "split_spec_param1e X = do {
    ((l, u), Y) \<leftarrow> scaleR2_rep X;
    (a, b) \<leftarrow> split_spec_param1 Y;
    a \<leftarrow> scaleRe_ivl_spec l u a;
    b \<leftarrow> scaleRe_ivl_spec l u b;
    RETURN (a, b)
  }"

definition "reduce_spec1 C X = do {
  vX \<leftarrow> vec1rep X;
  case vX of None \<Rightarrow> do {
    X \<leftarrow> reduce_spec C (fst ` X);
    RETURN (X \<times> UNIV)
  }
  | Some vX \<Rightarrow> do {
    vX \<leftarrow> reduce_spec C vX;
    RETURN (flow1_of_vec1 ` vX)
  }
}"
definition "reduce_spec1e C X = do {
  ((l, u), X) \<leftarrow> scaleR2_rep X;
  X \<leftarrow> reduce_spec1 C X;
  scaleRe_ivl_spec l u X
}"

definition [refine_vcg_def]: "pre_split_reduce_spec (ro::unit) = SPEC (\<lambda>x::unit. True)"

definition split_under_threshold::"_ \<Rightarrow> real \<Rightarrow> 'n::enum eucl1 set \<Rightarrow> 'n eucl1 set nres" where
  "split_under_threshold ro th X = do {
    (_, Ys) \<leftarrow> WHILE\<^bsup>\<lambda>(Xs, Ys). X \<subseteq> Xs \<union> Ys\<^esup> (\<lambda>(Xs, Ys). \<not> op_coll_is_empty Xs) (\<lambda>(Xs, Ys). do {
      (X, Xs') \<leftarrow> (split_spec_coll (Xs:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)):::\<langle>\<langle>appr1_rel\<rangle>scaleR2_rel \<times>\<^sub>r clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel)\<rangle>nres_rel);
      w \<leftarrow> width_spec (op_image_fste X:::appr_rel);
      if w \<le> th then RETURN (Xs', mk_coll X \<union> Ys)
      else do {
        ra \<leftarrow> pre_split_reduce_spec ro;
        X \<leftarrow> reduce_spec1e ra X;
        (a, b) \<leftarrow> split_spec_param1e (X:::\<langle>appr1_rel\<rangle>scaleR2_rel);
        RETURN (mk_coll (a:::\<langle>appr1_rel\<rangle>scaleR2_rel) \<union> mk_coll (b:::\<langle>appr1_rel\<rangle>scaleR2_rel) \<union> Xs', Ys)
      }
    }) (X:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel), op_empty_coll:::clw_rel (\<langle>appr1_rel\<rangle>scaleR2_rel));
    RETURN Ys
  }"

definition "choose_step1e X h = do {
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    (h', error, CY, Y) \<leftarrow> choose_step1 X h;
    Y \<leftarrow> scaleRe_ivl_spec l u Y;
    RETURN (h', error, fst ` CY, Y)
  }"

definition "step_split ro (X::'n::enum eucl1 set) =
  do {
    ra \<leftarrow> pre_split_reduce_spec ro;
    X \<leftarrow> reduce_spec1e ra X;
    (a, b) \<leftarrow> split_spec_param1e (X:::appr1e_rel);
    _ \<leftarrow> mk_safe (op_image_fste a);
    _ \<leftarrow> mk_safe (op_image_fste b);
    width_X \<leftarrow> width_spec (op_image_fste X:::appr_rel);
    wa \<leftarrow> width_spec (op_image_fste a:::appr_rel);
    wb \<leftarrow> width_spec (op_image_fste b:::appr_rel);
    let _ = trace_set (ST ''splitting: '' @ show (lfloat10 width_X) @ ST ''-->'' @ show (lfloat10 wa) @
      ST '', ''  @ show (lfloat10 wb)) (None::'n::enum eucl1 set option);
    RETURN (mk_coll a \<union> mk_coll b)
  }"

definition "width_spec_appr1 X = do {
    vX \<leftarrow> vec1rep X;
    case vX of None \<Rightarrow> width_spec (fst ` X:::appr_rel)
    | Some vX \<Rightarrow> width_spec (vX:::appr_rel)
  }"

definition "tolerate_error1 Y E = tolerate_error (fst ` Y) (fst ` E)"

definition "step_adapt_time (X::'n::enum eucl1 set) h =
  do {
    let X0 = fst ` X;
    _ \<leftarrow> mk_safe (X0:::appr_rel);
    (h', error, CY, Y) \<leftarrow> choose_step1e X h;
    (te, e) \<leftarrow> tolerate_error1 Y error;
    let _ = trace_set1 (ST ''discrete time step: stepsize = '' @ show (lfloat10 h)) (None::'n eucl1 set option);
    let _ = trace_set1 (ST ''discrete time step: stepsize' = '' @ show (lfloat10 h')) (None::'n eucl1 set option);
    let _ = trace_set1 (ST ''error estimation: '' @ show (lfloat10 e)) (None::'n eucl1 set option);
    if \<not> te
    then do {
      let _ = trace_set (ST ''revoking step'') (None::'n eucl1 set option);
      RETURN (0, fst ` X, X, 3 * h' / 2 / 2)
    } else do {
      let _ = trace_set1 (ST ''error OK, step_adapt_time stepped '') (None::'n eucl1 set option);
      let _ = trace_set (ST ''interpolated step:'') (Some (CY));
      let _ = print_set True CY;
      let _ = trace_set1e (ST ''discrete step:'') (Some (Y));
      let _ = print_set1e False Y;
      rtol \<leftarrow> adaptive_rtol_spec;
      method_id \<leftarrow> method_spec;
      prec \<leftarrow> precision_spec;
      case approx prec (adapt_stepsize_fa rtol method_id e h') []
      of Some (h'', _) \<Rightarrow>
        let _ = trace_set1 (ST ''increase step: stepsize = '' @ show (lfloat10 h'')) (None::'n eucl1 set option)
        in RETURN (h', CY, Y, 15/2/2/2/2 * h'')
      | None \<Rightarrow>
        let _ = trace_set1 (ST ''increase time step (failure): stepsize = '' @ show (lfloat10 h')) (None::'n eucl1 set option)
        in RETURN (h', CY, Y, h' * 5 / 2 / 2)
    }
  }"

definition [simp]: "eq_spec x y = SPEC (\<lambda>r. r \<longrightarrow> x = y)"
lemma [autoref_itype]: "eq_spec ::\<^sub>i A \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_bool\<rangle>\<^sub>ii_nres" by simp

definition "select_with_inter ci a = do {
    CIs \<leftarrow> (sets_of_coll ci);
    As \<leftarrow> sets_of_coll a;
    FORWEAK CIs (RETURN op_empty_coll)
      (\<lambda>ci. do {
        (c, I) \<leftarrow> (get_inter ci);
        FORWEAK As (RETURN op_empty_coll)
        (\<lambda>a. do {
          b \<leftarrow> eq_spec a c;
          if b then RETURN (mk_coll ci)
          else RETURN (op_empty_coll)
        })
        (\<lambda>CIS CIS'. RETURN (CIS' \<union> CIS))
      })
      (\<lambda>CIS CIS'. RETURN (CIS' \<union> CIS))
  }"

abbreviation "fst_safe_colle XS \<equiv> (mk_safe_coll (op_image_fst_colle XS:::clw_rel appr_rel):::\<langle>clw_rel appr_rel\<rangle>nres_rel)"

definition "do_intersection_body GUARDS ivl sctn h \<equiv> \<lambda>(X, T, PDPS, PDPS2, CXS, _, _).
  do {
    (_, _, CX', X') \<leftarrow> choose_step1 (X:::appr1_rel) (h:::rnv_rel);
    let _ = trace_set1 (ST ''interpolated step during intersection:'') (Some (CX'));
    let _ = print_set1 True (CX');
    let _ = trace_set1 (ST ''step during intersection:'') (Some (X'));
    let _ = print_set1 False (X');
    CHECKs (ST ''unnormal intersection'') (abs (normal sctn) \<in> set Basis_list);
    CPDP \<leftarrow> solve_poincare_plane (abs (normal sctn)) CX';
    let _ = trace_set1 (ST ''CPDP: '') (Some CPDP);
    let _ = print_set1 False (CPDP);
    (PDP, PDP2) \<leftarrow> inter_sctn1_spec CPDP sctn;
    b1 \<leftarrow> disjoints_spec (mk_coll (op_image_fst X')) (GUARDS);
    b2 \<leftarrow> disjoints_spec (mk_coll (op_image_fst CX')) (GUARDS);
    b3 \<leftarrow> disjoints_spec (mk_coll (op_image_fst PDP)) (GUARDS);
    b4 \<leftarrow> disjoints_spec (mk_coll (op_image_fst PDP2)) (GUARDS);
    CHECKs (ST ''do_intersection: hitting several planes :('') (b1 \<and> b2 \<and> b3 \<and> b4);
    intersects \<leftarrow> op_intersects (op_image_fst X') sctn;
    CX's \<leftarrow> mk_safe (op_image_fst CX');
    c1 \<leftarrow> nonzero_component_within ivl sctn PDP;
    c2 \<leftarrow> nonzero_component_within ivl sctn PDP2;
    RETURN (X', pos_reals:::\<langle>Id\<rangle>phantom_rel, mk_coll PDP \<union> PDPS,
      mk_coll PDP2 \<union> PDPS2,
      mk_coll (inter_sbelows (CX's:::appr_rel) {sctn}) \<union> CXS, intersects, c1 \<and> c2)
  }"

definition "do_intersection guards ivl sctn (X::'n::enum eucl1 set) (h::real) =
  do {
    ASSUME (closed ivl);
    sp \<leftarrow> subset_spec_plane ivl sctn;
    sX \<leftarrow> mk_safe (op_image_fst (X:::appr1_rel));
    GUARDS \<leftarrow> unintersect_coll guards;
    a \<leftarrow> sbelow_sctn (op_image_fst X) sctn;
    b \<leftarrow> disjoints_spec (mk_coll (op_image_fst X)) GUARDS;
    let inside = sp \<and> a \<and> b; \<comment> \<open>this is a bit of a hack: if the \<open>ivl\<close> is not subset of the plane,\<close>
      \<comment> \<open>then do not do intersections\<close>
    (X, T, PDPS, PDPS2, CXS, intersects, inside) \<leftarrow>
      WHILE\<^bsup>do_intersection_invar guards GUARDS ivl sctn X\<^esup>
      (\<lambda>(X, T, PDPS, PDPS2, CXS, intersects, inside). intersects \<and> inside)
      (do_intersection_body GUARDS ivl sctn h)
      (X, nonneg_reals:::\<langle>Id\<rangle>phantom_rel, op_empty_coll:::clw_rel appr1_rel::'n eucl1 set,
        op_empty_coll:::clw_rel appr1_rel::'n eucl1 set,
        mk_coll (inter_sbelows (sX:::appr_rel) {sctn}), True, inside);
    a \<leftarrow> above_sctn (op_image_fst X) sctn;
    b \<leftarrow> subset_spec_coll (op_image_fst_coll PDPS) ivl;
    b2 \<leftarrow> subset_spec_coll (op_image_fst_coll PDPS2) ivl;
    RETURN (inside \<and> b \<and> b2 \<and> a, PDPS, PDPS2, CXS)
  }"

definition "resolve_step roptns X h = do {
    width_X \<leftarrow> width_spec (op_image_fste X:::appr_rel);
    mtdt \<leftarrow> max_tdev_thres_spec roptns;
    if \<not> width_X \<le> mtdt
    then do {
      Y \<leftarrow> step_split roptns X;
      RETURN (h, fst ` Y, Y, h)
    }
    else do {
      (h0, CY, Y, h') \<leftarrow> step_adapt_time (X::'n::enum eucl1 set) h;
      RETURN (h0, mk_coll (fst ` Y) \<union> mk_coll CY, mk_coll Y, h')
    }
  }"

definition "pre_intersection_step ro X h = do {
    mis \<leftarrow> max_intersection_step_spec ro;
    if h > mis
    then RETURN (with_infos (h/2) (mk_coll X), mk_coll (fst ` X), op_empty_coll:::clw_rel (iinfo_rel appr1e_rel))
    else do {
      width_X \<leftarrow> width_spec (op_image_fste X:::appr_rel);
      pig \<leftarrow> pre_inter_granularity_spec ro;
      if width_X \<le> pig then
        RETURN (with_infos h (op_empty_coll:::clw_rel appr1e_rel), mk_coll (fst ` X),
                with_infos (5 * h / 2 / 2) (mk_coll X))
      else do {
        X' \<leftarrow> step_split ro X;
        RETURN (with_infos h X', fst ` X', op_empty_coll:::clw_rel (iinfo_rel appr1e_rel))
      }
    }
  }"

definition "reach_cont ro (guardsi::'n::enum rvec set) XS0 =
  do {
    startstep \<leftarrow> start_stepsize_spec;
    (_, XS0') \<leftarrow> scaleR2_rep_coll XS0;
    sXS0 \<leftarrow> fst_safe_coll XS0';
    let fX0 = op_image_fst_colle XS0;
    guards \<leftarrow> (unintersect_coll (guardsi:::clw_rel (iplane_rel lvivl_rel)):::\<langle>clw_rel lvivl_rel\<rangle>nres_rel);
    d \<leftarrow> disjoints_spec fX0 (guards);
    CHECKs (ST ''reach_cont: starting from guarded set'') d;
    (_, CXS, GS) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(XS, CXS, GS).
        flowsto XS0 {0..} (CXS \<times> UNIV) (XS \<union> GS) \<and>
        (XS \<union> GS \<union> CXS \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
        XS0 \<union> GS \<subseteq> CXS \<times> UNIV)\<^esup>
          (\<lambda>(XS, CXS, GS). \<not> op_coll_is_empty XS) (\<lambda>(XS, CXS, GS).
      do {
        (hX, XS') \<leftarrow> (split_spec_exact XS:::\<langle>iinfo_rel (appr1e_rel) \<times>\<^sub>r clw_rel (iinfo_rel (appr1e_rel))\<rangle>nres_rel);
        (h::real, X) \<leftarrow> get_info hX;
        let _ = trace_set1e (ST ''next step in resolve_sctns using'') (Some X);
        cXS::nat \<leftarrow> card_info XS;
        cGS::nat \<leftarrow> card_info GS;
        let _ = trace_set1 (ST ''XS: '' @ show cXS) (None::'n eucl1 set option);
        let _ = trace_set1 (ST ''GS: '' @ show cGS) (None::'n eucl1 set option);
        (h0, fCX', X', h') \<leftarrow> resolve_step ro X h;
        sfCX' \<leftarrow> (mk_safe_coll (fCX':::clw_rel appr_rel):::\<langle>clw_rel appr_rel\<rangle>nres_rel);
        let fX' = (fst ` X');
        fXS \<leftarrow> ivls_of_sets (fCX' \<union> fX');
        IS \<leftarrow> inter_overappr guards fXS;
        let d = op_coll_is_empty IS;
        if d then RETURN (with_infos h' X' \<union> XS':::clw_rel (iinfo_rel appr1e_rel), sfCX' \<union> CXS, GS)
        else do {
          (hX', fCX', hG') \<leftarrow> pre_intersection_step ro X h0;
          sfCX' \<leftarrow> (mk_safe_coll (fCX':::clw_rel appr_rel):::\<langle>clw_rel appr_rel\<rangle>nres_rel);
          _ \<leftarrow> fst_safe_colle (uninfo hX');
          _ \<leftarrow> fst_safe_colle (uninfo hG');
          fGs \<leftarrow> ivls_of_sets (op_image_fst_colle (uninfo hG') \<union> fCX' \<union> op_image_fst_colle (uninfo hX'));
          d \<leftarrow> disjoints_spec (sets_of_ivls guards) fGs;
          CHECKs (ST ''reach_cont: pre_intersection_step should not change disjointness condition!'') d;
          iguards \<leftarrow> select_with_inter guardsi IS;
          iG' \<leftarrow> with_coll_infos iguards hG';
          RETURN (hX' \<union> XS', sfCX' \<union> CXS, iG' \<union> GS)
        }
      })
      (with_infos startstep (XS0:::clw_rel appr1e_rel):::clw_rel (iinfo_rel appr1e_rel),
        sXS0:::clw_rel appr_rel, op_empty_coll:::clw_rel (\<langle>iplane_rel (lvivl_rel::(_\<times>'n rvec set)set), iinfo_rel appr1e_rel\<rangle>info_rel));
    RETURN (CXS, GS)
  }"

definition "reach_cont_par roptns guards XS = do {
  XS \<leftarrow> sets_of_coll XS;
  PARS \<leftarrow> PAR_IMAGE (\<lambda>X (CX, G).
      G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
      X \<union> G \<subseteq> CX \<times> UNIV \<and> flowsto X {0..} (CX \<times> UNIV) G)
    (\<lambda>X. reach_cont roptns guards (mk_coll X)) XS;
  RETURN (\<Union>(fst ` snd ` PARS), \<Union>(snd ` snd ` PARS))
}"


definition "subset_iplane_coll x ics = do {
    X \<leftarrow> unintersect x;
    ics \<leftarrow> sets_of_coll ics;
    FORWEAK ics (RETURN False) (\<lambda>ic. do {
      (i, c) \<leftarrow> get_inter ic;
      sctn \<leftarrow> get_plane c;
      b1 \<leftarrow> subset_spec_plane X sctn;
      RETURN (b1 \<and> op_subset_ivl X i)
    }) (\<lambda>b c. RETURN (b \<or> c))
  }"

definition "subsets_iplane_coll xs ics = FORWEAK xs (RETURN True) (\<lambda>x. subset_iplane_coll x ics) (\<lambda>a b. RETURN (a \<and> b))"


definition "stable_set p = {x. {0..} \<subseteq> existence_ivl0 x \<and> (flow0 x \<longlongrightarrow> p) at_top}"

definition symstart_coll::"('n::enum eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres) \<Rightarrow>
  'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres"
  where
"symstart_coll symstart X0 = do {
    _ \<leftarrow> (fst_safe_colle (X0:::clw_rel appr1e_rel):::\<langle>clw_rel appr_rel\<rangle>nres_rel);
    X0s \<leftarrow> sets_of_coll X0;
    (CX1, X1) \<leftarrow> FORWEAK X0s (RETURN (op_empty_coll, op_empty_coll)) (symstart)
      (\<lambda>(CX, X) (CX', X'). RETURN (CX' \<union> CX, X' \<union> X));
    RETURN (CX1, X1)
  }"

definition reach_cont_symstart ::
  "_ \<Rightarrow> _ \<Rightarrow> 'n::enum rvec set
      \<Rightarrow> 'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set) nres"
  where "reach_cont_symstart ro symstart (guards::'n rvec set) X0 = do {
    let fX0 = op_image_fst_colle X0;
    GUARDS \<leftarrow> unintersect_coll guards;
    d \<leftarrow> disjoints_spec fX0 GUARDS;
    CHECKs (ST ''reach_cont_symstart: starting from guarded set'') d;
    (CY, Y0) \<leftarrow> symstart_coll symstart X0;
    sCY \<leftarrow> (mk_safe_coll (op_image_fst_colle X0 \<union> CY:::clw_rel appr_rel):::\<langle>clw_rel appr_rel\<rangle>nres_rel);
    b \<leftarrow> disjoints_spec (op_image_fst_colle Y0 \<union> CY) GUARDS;
    CHECKs ''reach_cont_symstart with a stupid guard'' b;
    (CX, GS) \<leftarrow> (reach_cont_par ro guards Y0:::\<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel (\<langle>iplane_rel lvivl_rel::(_ \<times> 'n rvec set) set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel);
    let CZ = sCY \<union> CX;
    RETURN (CZ, GS)
  }"

context includes autoref_syntax begin\<comment> \<open>TODO: should not be annotating relations here\<close>
definition reach_conts ::
  "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'n::enum rvec set
      \<Rightarrow> 'n eucl1 set \<Rightarrow> ('n rvec set \<times> ('n rvec set \<times> 'n eucl1 set) set \<times> ('n eucl1 set \<Rightarrow> 'n eucl1 set)) nres"
  where "reach_conts ro symstart trap (guardsi::'n rvec set) X0 = do {
    (CX, GS) \<leftarrow> (reach_cont_symstart ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) guardsi X0:::
      \<langle>clw_rel appr_rel \<times>\<^sub>r
       clw_rel (\<langle>iplane_rel lvivl_rel::(_\<times>'n rvec set) set, iinfo_rel appr1e_rel\<rangle>info_rel)\<rangle>nres_rel);
    (IGSs:: ('n rvec set \<times> 'n eucl1 set) set) \<leftarrow> explicit_info_set GS;
    let GSs = snd ` IGSs;
    ASSUME (finite GSs);
    CHECKs '''' (GSs \<noteq> {});
    ASSERT       (\<exists>f. X0 = \<Union>(f ` GSs) \<and> (\<forall>G \<in> GSs. flowsto (f G - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G)));
    X0f \<leftarrow> GSPEC (\<lambda>f. X0 = \<Union>(f ` GSs) \<and> (\<forall>G \<in> GSs. flowsto (f G - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G)));
    let K = (fst ` IGSs);
    b \<leftarrow> subsets_iplane_coll K guardsi;
    CHECKs (ST ''reach_conts: subsets_iplane_coll'') b;
    RETURN (CX, IGSs:::\<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel, X0f)
  }"
end

definition [refine_vcg_def]: "get_sctns X = SPEC (\<lambda>R. X = below_halfspaces R)"

definition "leaves_halfspace S X = do {
    sctns \<leftarrow> get_sctns S;
    sctnss \<leftarrow> op_set_to_list sctns;
    (case sctnss of
      [] \<Rightarrow> RETURN None
    | [sctn] \<Rightarrow>
      do {
        (Xi, Xs) \<leftarrow> ivl_rep_of_set_coll X;
        ASSERT (Xi \<le> Xs);
        b \<leftarrow> subset_spec_plane ({Xi .. Xs}:::lvivl_rel) sctn;
        CHECKs (ST ''leaves_halfspace: not subset of plane'') b;
        F \<leftarrow> ode_set ({Xi .. Xs}:::appr_rel);
        sF \<leftarrow> Sup_inner F (normal sctn);
        CHECKs (ST ''leaves_halfspace: not down from plane'') (sF < 0);
        RETURN (Some sctn)
      }
    | _ \<Rightarrow> do {CHECKs (ST ''leaves_halfspace: not a good halfspace'') False; SUCCEED})
  }"

definition "poincare_start_on guards sctn X0S =
  do {
    X0SS \<leftarrow> sets_of_coll X0S;
    (FORWEAK X0SS (RETURN (op_empty_coll:::clw_rel appr1e_rel, op_empty_coll:::clw_rel appr_rel)) (\<lambda>X0. do {
      mk_safe (fst ` X0);
      startstep \<leftarrow> start_stepsize_spec;
      (h, err, CX1, X1) \<leftarrow> choose_step1e X0 (startstep);
      let _ = trace_set (ST ''interpolated start step:'') (Some CX1);
      let _ = print_set True CX1;
      let _ = trace_set1e (ST ''discrete start step:'') (Some X1);
      let _ = print_set1e False X1;
      let fX1 = op_image_fste X1;
      c0 \<leftarrow> below_sctn (op_image_fste X0) (sctn);
      c1 \<leftarrow> sbelow_sctn (fX1) (sctn);
      c2 \<leftarrow> disjoints_spec (mk_coll (fX1)) guards;
      c3 \<leftarrow> disjoints_spec (mk_coll (CX1)) guards;
      mk_safe (fX1);
      mk_safe (CX1);
      D \<leftarrow> (ode_set (CX1):::\<langle>appr_rel\<rangle>nres_rel);
      d \<leftarrow> Sup_inner D (normal sctn);
      let _ = trace_set (ST ''poincare_start_on: D '') (Some D);
      CHECKs (ST ''poincare_start_on: is away and really moves away'') (c0 \<and> c1 \<and> c2 \<and> c3 \<and> d < 0);
      RETURN (mk_coll X1:::clw_rel appr1e_rel, (mk_coll CX1):::clw_rel appr_rel)
    })
    (\<lambda>(X1, CX1) (X1S, CX1S). RETURN (op_union_coll X1 X1S:::clw_rel appr1e_rel, op_union_coll CX1 CX1S:::clw_rel appr_rel)))
  }"

definition [simp]: "isets_of_iivls x = x"

abbreviation "inter_plane A B \<equiv> mk_inter A (plane_of B)"

definition "do_intersection_core guards ivl sctn hX =
  do {
    (h, eX) \<leftarrow> get_info hX;
    ((l, u), X) \<leftarrow> scaleR2_rep eX;
    (b, PS1, PS2, CXS) \<leftarrow> do_intersection (guards:::clw_rel (iplane_rel lvivl_rel)) ivl sctn X h;
    if b then do {
      PS1e \<leftarrow> scaleRe_ivl_coll_spec l u PS1;
      PS2e \<leftarrow> scaleRe_ivl_coll_spec l u PS2;
      RETURN (PS1e, PS2e, CXS, op_empty_coll)
    }
    else RETURN (op_empty_coll, op_empty_coll, op_empty_coll, mk_coll eX)
  }"

definition "do_intersection_coll guards ivl sctn X =
  do {
    Xs \<leftarrow> sets_of_coll X;
    CHECKs ''nonempty inter nonfinite: '' (Xs \<noteq> {});
    RS \<leftarrow> PAR_IMAGE (\<lambda>X. \<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV guards ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV guards ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X) (do_intersection_core guards ivl sctn) Xs;
    ASSUME (finite RS);
    RETURN ((\<Union>(X, (P1, P2, CX, X0s))\<in>RS. P1),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. P2),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. CX),
            (\<Union>(X, (P1, P2, CX, X0s))\<in>RS. X0s))
  }"

definition "op_enlarge_ivl_sctn ivl sctn d = do {
    (l, u) \<leftarrow> ivl_rep ivl;
    CHECKs ''op_enlarge_ivl_sctn: trying to shrink'' (d \<ge> 0);
    CHECKs ''op_enlarge_ivl_sctn: empty ivl'' (l \<le> u);
    CHECKs ''op_enlarge_ivl_sctn: not in Basis'' (abs (normal sctn) \<in> set Basis_list);
    let dOne = sum_list (map (\<lambda>i. d *\<^sub>R i) Basis_list) - d *\<^sub>R abs (normal sctn);
    ASSERT (l - dOne \<le> u + dOne);
    RETURN (op_atLeastAtMost_ivl (l - dOne) (u + dOne))
  }"

definition "guardset guards = Union (case_prod (\<inter>) ` (\<lambda>(x, y). (x, plane_of y)) ` guards)"

definition "resolve_ivlplanes (guards::'n::enum rvec set)
                          (ivlplanes::'n::enum rvec set)
                          XS
                           =
  FORWEAK XS (RETURN ({}))
     (\<lambda>(ivlplane, X).
      do {
        (ivl, plane) \<leftarrow> (get_inter (ivlplane));
        ASSUME (closed ivl);
        sctn \<leftarrow> (get_plane plane);
        b \<leftarrow> subset_iplane_coll ivlplane ivlplanes;
        CHECKs ''reach_conts: subsets_iplane_coll'' b;
        (PS1, PS2, CXS, RS) \<leftarrow> (do_intersection_coll guards ivl sctn X);
        RETURN {(uninfo X, PS1, PS2, RS, ivl, sctn, CXS)}
      })
      (\<lambda>(PS) (PS'). RETURN (PS' \<union> PS))"

context includes autoref_syntax begin
definition "poincare_onto ro \<comment> \<open>options\<close>
                          symstart trap \<comment> \<open>symbolic start and trap\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set)
                          (CXS0::'n rvec set)
     =
  do {
    (CXS, XS, X0s) \<leftarrow> (reach_conts ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (ivlplanes \<union> guards) XS0:::
      \<langle>clw_rel appr_rel \<times>\<^sub>r \<langle>iplane_rel lvivl_rel \<times>\<^sub>r clw_rel (iinfo_rel appr1e_rel)\<rangle>list_wset_rel \<times>\<^sub>r
     ghost_rel\<rangle>nres_rel);
    PS \<leftarrow> resolve_ivlplanes guards ivlplanes XS;
    _ \<leftarrow> mk_safe_coll CXS0;
    RETURN ((\<lambda>(X, P1, P2, R, ivl, sctn, CX). (X, P1, P2, R, ivl, sctn, CX, CXS \<union> CXS0)) ` PS)
  }"

definition "empty_remainders PS =
  FORWEAK PS (RETURN True) (\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). do { e \<leftarrow> isEmpty_spec R; RETURN e})
    (\<lambda>a b. RETURN (a \<and> b))"

definition [simp]: "empty_trap = {}"

definition empty_symstart::"((real, 'a) vec \<times> (real, 'a) vec \<Rightarrow>\<^sub>L (real, 'a) vec) set
   \<Rightarrow> ((real, 'a) vec set \<times> ((real, 'a) vec \<times> (real, 'a) vec \<Rightarrow>\<^sub>L (real, 'a) vec) set) nres"
  where [simp]: "empty_symstart \<equiv> \<lambda>X. RETURN (op_empty_coll, mk_coll X)"

definition "poincare_onto_empty ro \<comment> \<open>options\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set) =
  poincare_onto ro (OP empty_symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel)
    empty_trap guards ivlplanes XS0"


definition "poincare_onto2 ro \<comment> \<open>options\<close>
                          symstart trap \<comment> \<open>symbolic start and trap\<close>
                          (guards::'n::enum rvec set) \<comment> \<open>avoiding guards\<close>
                          (ivlplanes::'n::enum rvec set) \<comment> \<open>target sections\<close>
                          (XS0::'n eucl1 set) =
  do {
    (PS) \<leftarrow> (poincare_onto ro (symstart:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel)
      trap guards ivlplanes XS0 op_empty_coll:::
      \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
        clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    (PS2) \<leftarrow> FORWEAK PS (RETURN ({})) (\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS).
      if op_coll_is_empty R then RETURN ({})
      else do {
        ivlplaness \<leftarrow> (sets_of_coll ivlplanes:::\<langle>\<langle>iplane_rel lvivl_rel\<rangle>list_wset_rel\<rangle>nres_rel);
        ivlplaness' \<leftarrow> op_set_ndelete (mk_inter ivl (plane_of sctn)) ivlplaness;
        let ivlplanes' = (\<Union>(mk_coll ` ivlplaness':::\<langle>clw_rel (iplane_rel lvivl_rel)\<rangle>list_wset_rel));
        PS' \<leftarrow> (poincare_onto_empty ro (guards) ivlplanes' R CXS:::
            \<langle>\<langle>clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel
            \<times>\<^sub>r clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
        b \<leftarrow> empty_remainders PS';
        CHECKs (ST ''poincare_onto2: empty remainders!'') b;
        ASSUME (finite PS');
        RETURN PS'
        }) (\<lambda>PS PS'. RETURN (PS' \<union> PS));
      RETURN (Pair True ` PS2 \<union> Pair False ` PS)
    }"

definition "width_spec_ivl M x = do {
    (i, s) \<leftarrow> ivl_rep x;
    RETURN (\<Sum>(i, s)\<leftarrow>zip (take M (list_of_eucl i)) (take M (list_of_eucl s)). abs (s - i))
  }"

definition partition_ivl::"_ \<Rightarrow> 'a::executable_euclidean_space set \<Rightarrow> 'a::executable_euclidean_space set nres"
  where
 "partition_ivl roptns xs = (if op_coll_is_empty xs then RETURN (op_empty_coll:::clw_rel lvivl_rel) else do {
    (i, s) \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls (xs:::clw_rel lvivl_rel):::clw_rel appr_rel);
    ASSERT (i \<le> s);
    let r = (op_atLeastAtMost_ivl i s);
    (rs, ps) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(rs, ps). (xs) \<subseteq> rs \<union> ps)\<^esup> (\<lambda>(rs, ps). \<not> op_coll_is_empty (rs:::clw_rel lvivl_rel))
      (\<lambda>(rs, ps).
      do {
        (r, rs') \<leftarrow> (split_spec_exact rs:::\<langle>lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel);
        (ri, rs) \<leftarrow> ivl_rep r;
        CHECKs (ST ''partition_ivl with strange ivl'') (ri \<le> rs);
        width \<leftarrow> width_spec ({ri .. rs}:::appr_rel);
        pig \<leftarrow> post_inter_granularity_spec roptns;
        if width \<le> pig then
          RETURN (rs', mk_coll r \<union> ps)
        else do {
          (a, b) \<leftarrow> split_spec_ivl (DIM('a)) r;
          let isa = (op_inter_ivl_coll (xs:::clw_rel lvivl_rel) (a:::lvivl_rel));
          let isb = (op_inter_ivl_coll(xs:::clw_rel lvivl_rel) (b:::lvivl_rel));
          ra' \<leftarrow> (if op_coll_is_empty isa then RETURN op_empty_coll else do {
            (i', s') \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls isa);
            RETURN (mk_coll (({i' .. s'}:::lvivl_rel) \<inter> a))
          });
          rb' \<leftarrow> (if op_coll_is_empty isb then RETURN op_empty_coll else do {
            (i', s') \<leftarrow> ivl_rep_of_set_coll (sets_of_ivls isb);
            RETURN (mk_coll (({i' .. s'}:::lvivl_rel) \<inter> b))
          });
          RETURN (ra' \<union> rb' \<union> rs', ps)
        }
      }) (mk_coll r:::clw_rel lvivl_rel, op_empty_coll :::clw_rel lvivl_rel);
    RETURN ps
  })"

definition
  "vec1repse X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN (Some op_empty_coll))
      (\<lambda>x. do {
        ((l, u), x) \<leftarrow> scaleR2_rep x;
        xo \<leftarrow> vec1rep x;
        case xo of None \<Rightarrow> RETURN None
        | Some x \<Rightarrow> do {
            xe \<leftarrow> scaleRe_ivl_spec l u x;
            RETURN (Some (mk_coll xe))
          }
      })
      (\<lambda>a b.
        case (a, b) of (Some a, Some b) \<Rightarrow> RETURN (Some (b \<union> a))
        | _ \<Rightarrow> RETURN None)
  }"

abbreviation "appre_rel \<equiv> \<langle>appr_rel\<rangle>scaleR2_rel"

definition "scaleR2_rep1 (Y::('a::executable_euclidean_space\<times>_) set) = do {
    let D = DIM('a);
    ((l, u), X) \<leftarrow> scaleR2_rep Y;
    (i, s) \<leftarrow> op_ivl_rep_of_set X;
    let mig = inf (abs i) (abs s);
    CHECKs (ST ''scaleR2_rep1: strange'') (i \<le> s);
    (N::real set) \<leftarrow> approx_slp_appr [floatarith.Inverse (norm2\<^sub>e D)] (norm2_slp D) (list_of_eucl ` ({mig .. mig}:::appr_rel));
    (sl, su) \<leftarrow> op_ivl_rep_of_set (N:::appr_rel);
    let scale = (rnv_of_lv sl + rnv_of_lv su)/2;
    CHECKs (ST ''scaleR2_rep1: scale 0'') (scale > 0);
    CHECKs (ST ''scaleR2_rep1: l 0'') (l > 0);
    CHECKs (ST ''scaleR2_rep1: u 0'') (u > 0);
    precision \<leftarrow> precision_spec;
    let scalel = real_divl (precision) 1 scale;
    let scaleu = real_divr (precision) 1 scale;
    CHECKs (ST ''scaleR2_rep1: scalel 0'') (scalel > 0);
    CHECKs (ST ''scaleR2_rep1: scaleu 0'') (scaleu > 0);
    (i, s) \<leftarrow> op_ivl_rep_of_set X;
    let (i0, i1) = split_lv_rel i;
    let (s0, s1) = split_lv_rel s;
    scaleRe_ivl_spec (scalel * l) (scaleu * u)
      (op_atLeastAtMost_ivl (Pair_lv_rel i0 (scale *\<^sub>R i1)) (Pair_lv_rel s0 (scale *\<^sub>R s1)))
  }"

definition "ivlse_of_setse X = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
    I \<leftarrow> scaleR2_rep1 X;
    I \<leftarrow> reduces_ivle I;
    RETURN (mk_coll I)
  }) (\<lambda>X' X. RETURN (X' \<union> X))
  }"

definition [simp]: "op_image_flow1_of_vec1_colle \<equiv> op_image_flow1_of_vec1_coll"

definition "okay_granularity ro r = do {
    (ri, rs) \<leftarrow> ivl_rep r;
    CHECKs (ST ''partition_ivle with strange ivl'') (ri \<le> rs);
    width \<leftarrow> width_spec ({ri .. rs}:::appr_rel);
    pig \<leftarrow> post_inter_granularity_spec ro;
    RETURN (width\<le>pig)
  }"

definition partition_set::"unit \<Rightarrow> 'n::enum eucl1 set \<Rightarrow> 'n eucl1 set nres"
  where
    "partition_set ro xs =
    (if op_coll_is_empty xs then RETURN (op_empty_coll:::clw_rel appr1e_rel) else do {
    ASSERT (xs \<noteq> {});
    pcg \<leftarrow> pre_collect_granularity_spec ro;
    xs \<leftarrow> split_under_threshold ro pcg
            (xs:::clw_rel appr1e_rel);
    vxs \<leftarrow> vec1repse xs;
    case vxs of None \<Rightarrow> do {
      xs \<leftarrow> ivls_of_sets (op_image_fst_colle xs);
      ps \<leftarrow> partition_ivl ro xs;
      scaleRe_ivl_coll_spec 1 1 (sets_of_ivls ps \<times> UNIV:::clw_rel appr1_rel)
    }
    | Some xs \<Rightarrow> do {
      xs \<leftarrow> ivlse_of_setse xs;
      ps \<leftarrow> (OP partition_ivle) $ ro $ xs;
      ps \<leftarrow> setse_of_ivlse ps;
      RETURN (op_image_flow1_of_vec1_colle ps)
    }
  })"

definition partition_sets::"unit \<Rightarrow>
  (bool \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a::enum eucl1 set \<times> 'a rvec set \<times> 'a rvec sctn \<times> 'a rvec set \<times> 'a rvec set) set \<Rightarrow>
  'a eucl1 set nres"
  where
 "partition_sets ro xs =
    FORWEAK xs (RETURN op_empty_coll) (\<lambda>(b, X, PS1, PS2, R, ivl', sctn', CX, CXS). do {
      PS \<leftarrow> partition_set ro PS1;
      RETURN PS
    })
    (\<lambda>a b. RETURN (b \<union> a))"

definition "ivlsctn_to_set xs = (\<Union>(ivl, sctn)\<in>set xs. ivl \<inter> plane_of sctn)"

definition [refine_vcg_def]: "singleton_spec X = SPEC (\<lambda>x. X = {x})"

primrec poincare_onto_series where
  "poincare_onto_series interrupt trap [] XS0 ivl sctn ro = do {
    let guard0 = mk_coll (mk_inter ivl (plane_of sctn));
    ASSUME (closed guard0);
    XS1 \<leftarrow> (poincare_onto2 (ro:::Id)
       (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap
        (op_empty_coll:::clw_rel (iplane_rel lvivl_rel)) guard0 XS0:::
      \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    (b, X, PS1, PS2, R, ivl', sctn', CX, CXS) \<leftarrow> singleton_spec XS1;
    CHECKs (ST ''poincare_onto_series: last return!'') (ivl' = ivl \<and> sctn' = sctn);
    RETURN PS2
  }"
| "poincare_onto_series interrupt trap ((guardro)#guards) XS0 ivl sctn ro0 = (case guardro of (guard, ro) \<Rightarrow>
    do {
      ASSUME (closed ivl);
      let guard0 = mk_coll (mk_inter ivl (plane_of sctn));
      ASSUME (closed guard0);
      ASSUME (\<forall>(guard, ro) \<in> set (guardro#guards). closed guard);
      let guardset = (\<Union>(guard, ro)\<in>set ((guard0, ro0)#guards). guard);
      XS1 \<leftarrow> (poincare_onto2 ro (interrupt:::appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel) trap (guardset:::clw_rel (iplane_rel lvivl_rel)) guard XS0 :::
        \<langle>\<langle>bool_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r clw_rel appr1e_rel \<times>\<^sub>r lvivl_rel \<times>\<^sub>r \<langle>lv_rel\<rangle>sctn_rel \<times>\<^sub>r
      clw_rel (isbelows_rel appr_rel) \<times>\<^sub>r clw_rel appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
      ASSUME (\<forall>(b, X, PS1, PS1, R, ivl, sctn, CX, CXS) \<in> XS1. closed ivl);
      XS2 \<leftarrow> partition_sets ro XS1;
      _ \<leftarrow> fst_safe_colle XS2;
      XS3 \<leftarrow> poincare_onto_series interrupt trap guards XS2 ivl sctn (ro0:::Id);
      RETURN XS3
    })"

definition "poincare_onto_from interrupt trap
                               S                      \<comment> \<open>leaving this (half)space in the beginning\<close>
                          (guards)                    \<comment> \<open>avoiding guards\<close>
                          (ivl::'n rvec set)          \<comment> \<open>onto \<open>ivl\<close>\<close>
                          sctn                        \<comment> \<open>which is part of \<open>sctn\<close>\<close>
                          ro
                          (XS0::'n::enum eucl1 set) =
  do {
    ASSUME (closed ivl);
    let guardset = (\<Union>(ivlsctn, ro)\<in>set (guards). ivlsctn:::clw_rel (iplane_rel lvivl_rel));
    lsctn \<leftarrow> leaves_halfspace S (op_image_fst_colle XS0);
    XS0 \<leftarrow> (case lsctn of
        None \<Rightarrow> RETURN XS0
      | Some lsctn =>
        do {
            CHECKs (ST ''poincare_onto_from: section only makes sense if start section = end section'')
              (lsctn = sctn \<or> normal lsctn = - normal sctn \<and> pstn lsctn = - pstn sctn);
            guards \<leftarrow> unintersect_coll guardset;
            b \<leftarrow> subset_spec_coll (op_image_fst_colle XS0) ivl;
            CHECKs (ST ''poincare_onto_from: section only makes sense if we start from there'') b;
            (XS0, _) \<leftarrow> poincare_start_on guards lsctn (XS0);
            RETURN XS0
        }
      );
    PS \<leftarrow> poincare_onto_series interrupt trap guards XS0 ivl sctn ro;
    RETURN PS
  }"

definition "subset_spec1 R P dP = do {
    R1 \<leftarrow> vec1rep R;
    dP \<leftarrow> default_rep UNIV dP;
    case (R1, dP) of (_, None) \<Rightarrow>
      op_subset (fst ` R) P
    | (Some RdR, Some dP) \<Rightarrow>
      op_subset RdR (P \<times> dP)
    | (None, Some _) \<Rightarrow> RETURN False
  }"

definition "subset_spec1_coll R P dP = do {
    XS \<leftarrow> sets_of_coll R;
    WEAK_ALL (\<lambda>x. x \<subseteq> flow1_of_vec1 ` (P \<times> dP)) XS (\<lambda>X. subset_spec1 X P dP)
  }"

definition "one_step_until_time X0 (ph::bool) (t1::real) =
  do {
    CHECKs ''one_step_until_time optns'' (0 \<le> t1);
    startstep \<leftarrow> start_stepsize_spec;
    rk2param \<leftarrow> rk2_param_spec;
    let fX0 = fst ` X0;
    mk_safe (fX0);
    (t, _, X, CX) \<leftarrow> WHILE (\<lambda>(t, _, _, _). t < t1) (\<lambda>(t, h, X, CXs). do {
        let _ = trace_set1e (ST ''choose step from:'') (Some X);
        (h0, CX, X, h') \<leftarrow> step_adapt_time X (min h (t1 - t));
        CHECKs (ST ''one_step negative step'') (h0 \<ge> 0 \<and> h' > 0 \<and> h0 \<le> min h (t1 - t));
        let _ = trace_set (ST ''interpolated step:'') (Some CX);
        let _ = print_set True CX;
        let _ = trace_set1e (ST ''step:'') (Some X);
        let _ = print_set1e False X;
        let fCX = CX;
        mk_safe fCX;
        let fX = fst ` X;
        mk_safe fX;
        RETURN (t + h0, h', X, mk_phantom (mk_coll CX) \<union> CXs)
    }) (0::real, startstep, X0, op_union_phantom (mk_phantom (mk_coll fX0)) (op_empty_phantom ph));
    RETURN (X, CX)
  }"

definition "ivl_of_eucl_coll CY =
  do {
    (i, s) \<leftarrow> ivl_rep_of_set_coll CY;
    ASSERT (i \<le> s);
    RETURN (({i .. s}\<times>UNIV):::appr1_rel)
  }"

definition "one_step_until_time_ivl X0 (ph::bool) (t1::real) (t2::real) =
  do {
    (X, CX) \<leftarrow>  one_step_until_time X0 ph t1;
    CHECKs (ST ''one_step_until_time_ivl empty time interval'') (0 \<le> t1 \<and> t1 \<le> t2);
    (if t2 = t1 then RETURN (X, CX)
    else do {
      (Y, CYp) \<leftarrow> one_step_until_time X False (t2 - t1);
      CY \<leftarrow> get_phantom CYp;
      R \<leftarrow> ivl_of_eucl_coll CY;
      mk_safe (fst ` R);
      R \<leftarrow> scaleRe_ivl_spec 1 1 R;
      RETURN (R, CYp \<union> CX)
    })
  }"

definition "c1_info_invare n X = (let l = (fst (fst X)); u = (snd (fst X))
  in (c1_info_invar n (snd X)) \<and> (l < u \<or> -\<infinity> < l \<and> l \<le> u \<and> u < \<infinity>))"

definition "c0_info_of_appr X = eucl_of_list ` set_of_appr X"
definition "c0_info_of_apprs X = (\<Union>x\<in>set X. c0_info_of_appr x)"

definition "c0_info_of_appr' X = the_default UNIV (map_option c0_info_of_apprs X)"

lemma the_default_eq: "the_default a x = (case x of None \<Rightarrow> a | Some b \<Rightarrow> b)"
  by (auto split: option.splits)

definition "poincare_onto_from_in_ivl interrupt trap
                               S                      \<comment> \<open>leaving this (half)space in the beginning\<close>
                          (guards)                    \<comment> \<open>avoiding guards\<close>
                          (ivl::'n rvec set)          \<comment> \<open>onto \<open>ivl\<close>\<close>
                          sctn                        \<comment> \<open>which is part of \<open>sctn\<close>\<close>
                          ro
                          (XS0::'n::enum eucl1 set)
                          P dP =
  do {
    RS \<leftarrow> poincare_onto_from interrupt trap S guards ivl sctn ro XS0;
    ((l, u), R) \<leftarrow> scaleR2_rep_coll RS;
    CHECKs (ST ''poincare_onto_from_in: there should not be scaleR2'') (l = 1 \<and> u = 1);
    (l, u) \<leftarrow> ivl_rep P;
    CHECKs (ST ''poincare_onto_from_in: strange interval'') (l \<le> u);
    _ \<leftarrow> mk_safe {l .. u};
    subset_spec1_coll R P dP
  }"

definition "set_of_lvivl' x = (case x of None \<Rightarrow> UNIV | Some x \<Rightarrow> set_of_lvivl x)"

definition "lvivl'_invar n x =
  (case x of None \<Rightarrow> True | Some (l, u) \<Rightarrow> length l = length u \<and> length u = n)"

definition "one_step_until_time_ivl_in_ivl X0 (t1::real) (t2::real) R dR =
  do {
    (X, CX) \<leftarrow> one_step_until_time_ivl X0 True t1 t2;
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    CHECKs (ST ''one_step_until_time_ivl_in_ivl: there should not be scaleR2'') (l = 1 \<and> u = 1);
    (l, u) \<leftarrow> ivl_rep R;
    CHECKs (ST ''one_step_until_time_ivl_in_ivl: strange interval'') (l \<le> u);
    _ \<leftarrow> mk_safe {l .. u};
    let _ = trace_set1 (ST ''final step to:'') (Some X);
    let _ = trace_set (ST ''contained in?'') (Some {l .. u});
    let _ = print_set1 False X;
    let _ = print_set False {l .. u};
    subset_spec1 X R dR
}"

definition "poincare_onto_in_ivl
                          (guards)                    \<comment> \<open>avoiding guards\<close>
                          (ivl::'n rvec set)          \<comment> \<open>onto \<open>ivl\<close>\<close>
                          sctn                        \<comment> \<open>which is part of \<open>sctn\<close>\<close>
                          ro
                          (XS0::'n::enum eucl1 set)
                          P dP =
  do {
    RS \<leftarrow> poincare_onto_series empty_symstart empty_trap guards XS0 ivl sctn ro;
    ((l, u), R) \<leftarrow> scaleR2_rep_coll RS;
    CHECKs (ST ''poincare_onto_in_ivl: there should not be scaleR2'') (l = 1 \<and> u = 1);
    (l, u) \<leftarrow> ivl_rep P;
    CHECKs (ST ''poincare_onto_in_ivl: strange interval'') (l \<le> u);
    (lR, uR) \<leftarrow> ivl_rep_of_set_coll (op_image_fst_coll R);
    CHECKs (ST ''poincare_onto_in_ivl: strange interval2'') (lR \<le> uR);
    let _ = trace_set (ST ''final step to:'') (Some {lR .. uR});
    let _ = trace_set (ST ''contained in?'') (Some {l .. u});
    _ \<leftarrow> mk_safe {l .. u};
    subset_spec1_coll R P dP
  }"

definition "poincare_maps_onto \<Sigma> X0 X1 \<longleftrightarrow> poincare_mapsto \<Sigma> X0 UNIV (Csafe - \<Sigma>) X1"

end

end

end