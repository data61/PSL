section"Example: Lorenz attractor"
theory Lorenz_Approximation
imports
  "HOL-ODE-Numerics.ODE_Numerics"
  Result_File_Coarse
begin
text \<open>\label{sec:lorenz}\<close>

text \<open>TODO: move to isabelle? \<close>
lifting_update blinfun.lifting
lifting_forget blinfun.lifting


lemma eventually_uniformly_on:
  "(\<forall>\<^sub>F x in uniformly_on T l. P x) = (\<exists>e>0. \<forall>f. (\<forall>x\<in>T. dist (f x) (l x) < e) \<longrightarrow> P f)"
  unfolding uniformly_on_def
  apply (subst eventually_INF)
  apply safe
  subgoal for E
    apply (cases "E = {}")
    subgoal by (auto intro!: exI[where x=1])
    subgoal
      apply (auto simp: INF_principal_finite eventually_principal elim!: )
    proof goal_cases
      case (1 x)
      from 1 have "0 < Min E"
        apply (subst Min_gr_iff)
          apply force apply force apply force done
      have *: "(\<Inter>e\<in>E. {f. \<forall>t\<in>T. dist (f t) (l t) < e}) = {f. \<forall>t\<in>T. dist (f t) (l t) < Min E}"
        using 1 apply (auto simp: )
         apply (subst Min_gr_iff)
           apply force apply force apply force
        apply (drule bspec, assumption)
        apply (rule less_le_trans, assumption)
        apply auto
        done
      from 1 have "\<forall>f. (\<forall>x\<in>T. dist (f x) (l x) < Min E) \<longrightarrow> P f" unfolding * by simp
      then show ?case
        using 1(4)[rule_format, OF \<open>0 < Min E\<close>] by auto
    qed
    done
  subgoal for e
    apply (rule exI[where x="{e}"])
    by (auto simp: eventually_principal)
  done


lemma op_cast_image_impl[autoref_rules]:
  "(\<lambda>x. x, op_cast_image::'a::executable_euclidean_space set \<Rightarrow>
                          'b::executable_euclidean_space set)
    \<in> aform.appr_rel \<rightarrow> aform.appr_rel"
  if "DIM('a) = DIM('b)"
  using that
  apply (auto simp: aform.appr_rel_def intro!: relcompI)
  unfolding lv_rel_def set_rel_br
  by (force simp: intro!: brI dest!: brD)

lemma cast_bl_blinfun_of_list[simp]:
  "cast_bl (blinfun_of_list xs::'a \<Rightarrow>\<^sub>L 'a) =
    (blinfun_of_list xs::'b\<Rightarrow>\<^sub>L'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  using that
  apply (auto simp: cast_bl_rep intro!: blinfun_eqI)
  by (auto simp: blinfun_of_list_def blinfun_of_matrix_apply
      linear_sum linear.scaleR sum_Basis_sum_nth_Basis_list
      linear_cast)

lemma cast_idem[simp]: "cast x = x"
  by (auto simp: cast_def)

lemma cast_bl_idem[simp]: "cast_bl x = x"
  by (auto simp: cast_bl_rep intro!: blinfun_eqI)

lemma op_cast_eucl1_image_impl[autoref_rules]:
  "(\<lambda>x. x, op_cast_eucl1_image::'a::executable_euclidean_space c1_info set \<Rightarrow>
                          'b::executable_euclidean_space c1_info set)
    \<in> aform.appr1_rel \<rightarrow> aform.appr1_rel"
  if "DIM_precond TYPE('a) D"
    "DIM_precond TYPE('b) D"
  using that
proof (auto, goal_cases)
  case (1 a b a')
  then show ?case
    apply (auto simp: aform.appr1_rel_br set_rel_br br_def)
    subgoal for w x y z
      apply (auto simp: aform.c1_info_of_appr_def cast_eucl1_def aform.c1_info_invar_def
          split: option.splits)
       apply (rule image_eqI)
        apply (rule cast_eucl_of_list, force, force simp: Joints_imp_length_eq, force)
      subgoal for s t
        apply (rule image_eqI[where x="t"])
         supply [simp del] = eucl_of_list_take_DIM
        apply (auto simp: flow1_of_list_def)
        apply (subst cast_eucl_of_list)
        subgoal by simp
        subgoal
          by (auto dest!: Joints_imp_length_eq
              simp: power2_eq_square flow1_of_list_def[abs_def])
        subgoal by simp
        done
      done
    subgoal for w x
      apply (rule image_eqI[where x="cast_eucl1 (w, x)"])
       apply (auto simp: aform.c1_info_of_appr_def cast_eucl1_def
          aform.c1_info_invar_def
          split: option.splits)
       apply (rule image_eqI)
        apply (rule cast_eucl_of_list, force, force simp: Joints_imp_length_eq, force)
      subgoal for s t
        apply (rule image_eqI[where x="t"])
         supply [simp del] = eucl_of_list_take_DIM
        apply (auto simp: flow1_of_list_def)
        apply (subst cast_eucl_of_list)
        subgoal by simp
        subgoal
          by (auto dest!: Joints_imp_length_eq
              simp: power2_eq_square flow1_of_list_def[abs_def])
        subgoal by simp
        done
      done
    done
qed

lemma less_3_iff: "i < (3::nat) \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2"
  by arith

definition mat3_of_vec::"R3 \<Rightarrow> real^3^3" where
  "mat3_of_vec x = (let xs = list_of_eucl x in eucl_of_list [xs!0,0,0,  xs!1,0,0,  xs!2,0,0])"

lemma ll3: "{..<3} = {0,1,2::nat}"
  by (auto simp: less_3_iff)

lemma mat3_of_vec: "cast (mat3_of_vec x *v eucl_of_list [1, 0, 0]) = x"
  by (auto simp: mat3_of_vec_def eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list
      linear_sum linear_cast linear.scaleR ll3 linear_add Basis_list_R3 inner_prod_def
      prod_eq_iff)

primrec bisect_form where
  "bisect_form p f xs l u 0 = (l, u)"
| "bisect_form p f xs l u (Suc n) =
    (let m = (l + u)/2 in
    if approx_form_aform p (f m) xs
    then bisect_form p f xs l m n
    else bisect_form p f xs m u n)"

text \<open>This should prove that the expansion estimates are sufficient.\<close>

lemma expansion_main: "expansion_main (coarse_results) = Some True"
  by eval

context includes floatarith_notation begin

definition "matrix_of_degrees2\<^sub>e =
  (let
    e = Var 2;
    ur = Rad_of (Var 0);
    vr = Rad_of (Var 1);
    x1 = Cos ur;
    x2 = Cos vr;
    y1 = Sin ur;
    y2 = Sin vr
   in
    [x1 + (e * (x2 - x1)), 0, 0,
    y1 + (e * (y2 - y1)), 0, 0,
    0, 0, 0])"

definition "matrix_of_degrees2 u v =
  approx_floatariths 30 matrix_of_degrees2\<^sub>e (aforms_of_ivls [u, v, 0] [u, v, 1])"

text \<open>following \<open>vector_field.h\<close> / \<open>vector_field.cc\<close>\<close>

abbreviation "S \<equiv> 10::real"
abbreviation "B \<equiv> 8/3::real"
abbreviation "TEMP \<equiv> sqrt((S + 1) * (S + 1) + 4 * S * (28 - 1))"
abbreviation "K1 \<equiv> S / TEMP"
abbreviation "K2 \<equiv> (S - 1 + TEMP) / (2 * S)"
abbreviation "K3 \<equiv> (S - 1 - TEMP) / (2 * S)"
abbreviation "E1 \<equiv> (- (S + 1) + TEMP) / 2"
abbreviation "E2 \<equiv> (- (S + 1) - TEMP) / 2"
abbreviation "E3 \<equiv> - B"
abbreviation "C1 \<equiv> \<lambda>X. X ! 0 + X ! 1"
abbreviation "C2 \<equiv> \<lambda>X. K1 * C1 X * X ! 2"

schematic_goal
  lorenz_fas:
  "[E1 * X!0 - C2 X,
    E2 * X!1 + C2 X,
    E3 * X!2 + C1 X * (K2 * X!0 + K3 * X!1)] =
  interpret_floatariths ?fas X"
  by (reify_floatariths)
concrete_definition lorenz_fas uses lorenz_fas
end

interpretation lorenz: ode_interpretation true_form UNIV lorenz_fas "\<lambda>(X0, X1, X2).
 (E1 * X0 -        K1 * (X0 + X1) * X2,
  E2 * X1 +        K1 * (X0 + X1) * X2,
  E3 * X2 + (X0 + X1) * (K2 * X0 + K3 * X1))::real*real*real"
  "d::3" for d
  by standard
    (auto simp: lorenz_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

value [code] "length (slp_of_fas lorenz_fas)"

definition "mig_aform p x = mig_componentwise (Inf_aform' p x) (Sup_aform' p x)"

context includes floatarith_notation begin

definition "mig_aforms p x = real_of_float ((fst o the) ((approx p (Norm (map (Num o float_of o (mig_aform p)) x))) []))"

definition
  "column_of_c1_info x N j = (map (\<lambda>i. the (snd x) ! i) (map (\<lambda>i. i * N + j) [0..<N]))"

definition "rotate_x_fa a =
  [1, 0, 0,
  0, Cos a, - Sin a,
  0, Sin a, Cos a]"

definition "rotate_y_fa a =
  [Cos a, 0, Sin a,
  0, 1, 0,
  - Sin a, 0, Cos a]"

definition "rotate_z_fa a =
  [Cos a, - Sin a, 0,
  Sin a, Cos a, 0,
  0, 0, 1]"

definition "rotate_zx_slp a b xs =
  slp_of_fas (mvmult_fa 3 3 (mmult_fa 3 3 3 (rotate_x_fa (Rad_of (R\<^sub>e b))) (rotate_z_fa (Rad_of (R\<^sub>e a)))) xs)"

definition "perspective_projection_aforms xs =
  the (approx_slp_outer 30 3 (rotate_zx_slp (-30) (-60) (map Var [0..<3])) xs)"

definition "print_lorenz_aform print_fun cx cy cz ci
    cd1 cd2
  = (\<lambda>a b.
        let (s1, n) = ((-6), False);
            _ = print_fun (String.implode (''# gen(''@ show a@''): ''@ shows_aforms_hr (b) '''' @ ''\<newline>''));
            _ = print_fun (String.implode (''# box(''@ show a@''): ''@ shows_box_of_aforms_hr (b) '''' @ ''\<newline>''));
            ((x0, y0, z0), (x1, y1, z1)) = case (map (Inf_aform' 30) (take 3 b), map (Sup_aform' 30) (take 3 b)) of
              ([x0, y0, z0], [x1, y1, z1]) \<Rightarrow> ((x0, y0, z0), (x1, y1, z1));
            _ = print_fun (String.implode (shows_segments_of_aform 0 1 b ((shows cx o shows_space o shows z0 o shows_space o shows z1)'''') ''\<newline>''));
            _ = print_fun (String.implode (shows_segments_of_aform 0 2 b ((shows cy o shows_space o shows y0 o shows_space o shows y1)'''') ''\<newline>''));
            _ = print_fun (String.implode (shows_segments_of_aform 1 2 b ((shows cz o shows_space o shows x0 o shows_space o shows x1)'''') ''\<newline>''));
            PS = perspective_projection_aforms b;
            _ = print_fun (String.implode (shows_segments_of_aform 0 1 PS
                  ((shows ci o shows_space o shows (fst (PS ! 2)) o shows_space o shows (fst (b ! 2))) '''') ''\<newline>''))
        in if \<not> a \<and> length b > 10 then
          print_fun (String.implode (shows_aforms_vareq 3 [(0, 1), (0, 2), (1, 2)] [0..<3]
              cd1
              cd2
          (FloatR 1 s1 * (if n then
              real_divl 30 1 (max (mig_aforms 30 (map (\<lambda>i. b ! i) [3,6,9]))
                         (mig_aforms 30 (map (\<lambda>i. b ! i) [4,7,10])))
            else 1)) \<comment> \<open>always length \<open>2^s!\<close>\<close>
          ''# no C1 info'' b ''''))
        else ())"

definition "print_lorenz_aform_std print_fun =
  print_lorenz_aform print_fun ''0x000001'' ''0x000002'' ''0x000012'' ''0x000003''
    [''0xa66f00'', ''0x06266f'', ''0xc60000'']
    [''0xffaa00'', ''0x1240ab'', ''0xc60000'']"

definition "lorenz_optns print_funo =
  (let
    pf = the_default (\<lambda>_ _. ()) (map_option print_lorenz_aform_std print_funo);
    tf = the_default (\<lambda>_ _. ()) (map_option (\<lambda>print_fun a b.
          let
            _ = print_fun (String.implode (''# '' @ a @ ''\<newline>''))
          in case b of Some b \<Rightarrow>
            (print_fun (String.implode (''# '' @ shows_box_of_aforms_hr (b) '''' @ ''\<newline>'')))
            | None \<Rightarrow> ()) print_funo)
  in
    \<lparr>
    precision = 30,
    adaptive_atol = FloatR 1 (-30),
    adaptive_rtol = FloatR 1 (-30),
    method_id = 2,
    start_stepsize  = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    rk2_param = FloatR 1 0,
    default_reduce = correct_girard 30 50 25,
    printing_fun = pf,
    tracing_fun = tf
  \<rparr>)"

definition lorenz_optns'
  where "lorenz_optns' pf m N rk2p a = lorenz_optns pf \<lparr>
      default_reduce := correct_girard 30 m N,
      rk2_param := rk2p,
      adaptive_atol := a,
      adaptive_rtol := a
    \<rparr>"

definition mirror_irects
  where "mirror_irects =
    map (\<lambda>irect. case irect of [i, j, k] \<Rightarrow> [if j < 0 then - i else i , abs j, k] | irect \<Rightarrow> irect)"

definition "print_irects irects =
  (let _ = map (\<lambda>is.
    let _ = map (\<lambda>j.
      let _ = print (String.implode (show j)) in print (STR '' '')) is in print (STR ''\<newline>'')) irects
  in ())"

abbreviation "aforms_of_ivl \<equiv> \<lambda>x. aforms_of_ivls (fst x) (snd x)"

definition "conefield_propagation\<^sub>e =
  ([Deg_of (Arctan (Var (6) / Var (3))),
   Deg_of (Arctan (Var (7) / Var (4))),
   Min (Norm [Var(3), Var (6), Var (9)]) (Norm [Var(4), Var (7), Var (10)])])"

definition "conefield_propagation DX = approx_floatariths 30 conefield_propagation\<^sub>e DX"

definition "conefield_propagation_slp = slp_of_fas conefield_propagation\<^sub>e"
lemma [simp]: "length conefield_propagation_slp = 51"
  by eval

definition op_with_unit_matrix :: "'a::real_normed_vector \<Rightarrow> 'a \<times> 'a \<Rightarrow>\<^sub>L 'a" where
  "op_with_unit_matrix X = (X, 1\<^sub>L)"

context includes blinfun.lifting begin
lemma matrix_vector_mult_blinfun_works[simp]: "matrix e *v g = e g" for e::"(real^'n) \<Rightarrow>\<^sub>L (real^'m)"
  by transfer (simp add: bounded_linear_def matrix_works)
end

lemma length_conefield_propagation\<^sub>e[simp]: "length conefield_propagation\<^sub>e = 3"
  by (simp add: conefield_propagation\<^sub>e_def)

lemma interpret_floatariths_conefield_propagation:
  "interpret_floatariths conefield_propagation\<^sub>e
    (list_of_eucl (vec1_of_flow1 (xDX::(real^3) \<times> ((real^3)\<Rightarrow>\<^sub>L(real^3)))))
   =
  (let
    DX = snd xDX;
    DXu = DX (eucl_of_list [1, 0, 0]);
    DXv = DX (eucl_of_list [0, 1, 0])
  in
  [deg_of (arctan (vec_nth DXu 1 / vec_nth DXu 0)),
   deg_of (arctan (vec_nth DXv 1 / vec_nth DXv 0)),
   min (norm DXu) (norm DXv)]
  )"
  apply (auto simp: conefield_propagation\<^sub>e_def Let_def interpret_mvmult_nth[where 'n=3 and 'm=3]
      inverse_eq_divide vec1_of_flow1_def nth_append)
    apply (auto simp: matrix_inner_Basis_list )
    apply (auto simp: interpret_floatarith_norm[where 'a="real ^ 3"]
      einterpret_mvmult_fa[where 'n=3 and 'm=3] matrix_inner_Basis_list nth_append)
  by (auto simp: matrix_def axis_eq_eucl_of_list eucl_of_list_012)

definition "conefield_bounds_form l u =
  (fold Conj [
    Less (-90) (N\<^sub>r l),
    LessEqual (N\<^sub>r l) (N\<^sub>r u),
    LessEqual (Var 9) (0),
    LessEqual 0 (Var 9),
    Less (N\<^sub>r u) (90),
    Less 0 (Var 3),
    AtLeastAtMost (Var 6) (Tan (Rad_of (N\<^sub>r l)) * Var 3) (Tan (Rad_of (N\<^sub>r u)) * Var 3)] true_form)"

definition "contract_angles X i = (snd (bisect_form 30 (\<lambda>x. conefield_bounds_form x (89)) X 89 (-89) i),
                                   snd (bisect_form 30 (conefield_bounds_form (-89)) X (-89) 89 i))"

definition "approx_conefield_bounds (DX::(R3 \<times> (R3 \<Rightarrow>\<^sub>L R3)) set) l u =
  do {
    let DX = (cast_eucl1 ` DX::3 eucl1 set);
    DXo \<leftarrow> aform.vec1rep DX;
    DX \<leftarrow> (case DXo of None \<Rightarrow> do {
        let _ = aform.print_msg (''# approx_conefield_bounds failed DXo...'');
        SUCCEED
      }
    | Some DX \<Rightarrow> RETURN DX);
    let _ = aform.trace_set (''# approx_conefield_bounds DX: '') (Some DX);
    approx_form_spec (conefield_bounds_form l u) (list_of_eucl ` DX)
  }"

lemma [autoref_rules]:
  includes autoref_syntax
  shows "(conefield_bounds_form, conefield_bounds_form) \<in> Id \<rightarrow> Id \<rightarrow> Id "
  by auto

lemma [autoref_rules_raw]:
  "DIM_precond TYPE((real, 3) vec \<times> ((real, 3) vec, 3) vec) 12"
  "DIM_precond TYPE(R3) 3"
  "DIM_precond TYPE((real, 3) vec) 3"
  by auto

schematic_goal approx_conefield_bounds_impl:
  includes autoref_syntax
  fixes optns::"real aform numeric_options"
  assumes [autoref_rules]: "(DXi, DX) \<in> aform.appr1_rel"
  assumes [autoref_rules]: "(li, l) \<in> Id"
  assumes [autoref_rules]: "(ui, u) \<in> Id"
  notes [autoref_rules] =
      aform.print_msg_impl[where optns = optns]
      aform.ivl_rep_of_set_autoref[where optns = optns]
      aform.transfer_operations(12)[where optns = optns]
      aform.approx_euclarithform[where optns=optns]
      aform.trace_set_impl[of optns]
  shows "(nres_of ?r, approx_conefield_bounds $ DX $ l $ u) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding approx_conefield_bounds_def
  including art
  by autoref_monadic
concrete_definition approx_conefield_bounds_impl for optns li ui DXi uses
  approx_conefield_bounds_impl
lemmas [autoref_rules] = approx_conefield_bounds_impl.refine

context includes autoref_syntax begin
lemma [autoref_rules]:
  "(real_of_ereal, real_of_ereal) \<in> ereal_rel \<rightarrow> rnv_rel"
  "(\<infinity>, \<infinity>) \<in> ereal_rel"
  by auto
end

lemma interpret_form_true_form[simp]: "interpret_form true_form \<equiv> \<lambda>_. True"
  by (force simp: true_form_def intro!: eq_reflection)

lemma interpret_form_conefield_bounds_form_list:
  "interpret_form (conefield_bounds_form L U)
    [x, y, z, ux, vx, wx,
              uy, vy, wy,
              uz, vz, wz]
   \<longleftrightarrow>
    (0 < ux \<and> -90 < L \<and> L \<le> U \<and> U < 90 \<and> uz = 0 \<and>
    uy \<le> tan (rad_of U) * ux \<and>
    tan (rad_of L) * ux  \<le> uy)"
  if "U \<in> float" "L \<in> float" "e \<in> float" "em \<in> float"
  using that
  by (auto simp: conefield_bounds_form_def L2_set_def)

lemma list_of_eucl_eucl1_3:
  includes vec_syntax
  shows "(list_of_eucl (vec1_of_flow1 (xDX::(real^3) \<times> ((real^3)\<Rightarrow>\<^sub>L(real^3))))) =
  (let
    (x, DX) = xDX;
    DXu = DX (eucl_of_list [1, 0, 0]);
    DXv = DX (eucl_of_list [0, 1, 0]);
    DXw = DX (eucl_of_list [0, 0, 1])
  in [x $ 0, x $ 1, x $ 2, vec_nth DXu 0, vec_nth DXv 0, vec_nth DXw 0,
                           vec_nth DXu 1, vec_nth DXv 1, vec_nth DXw 1,
                           vec_nth DXu 2, vec_nth DXv 2, vec_nth DXw 2])"
  apply (auto simp: matrix_inner_Basis_list Let_def vec1_of_flow1_def
      concat_map_map_index less_Suc_eq_0_disj
      list_of_eucl_matrix eval_nat_numeral aform.inner_Basis_eq_vec_nth
      intro!: nth_equalityI
      split: prod.splits)
  by (auto simp: matrix_def axis_eq_eucl_of_list eucl_of_list_012)

lemma interpret_form_conefield_bounds_form:
  "interpret_form (conefield_bounds_form L U)
    (list_of_eucl (vec1_of_flow1 (xDX::(real^3) \<times> ((real^3)\<Rightarrow>\<^sub>L(real^3)))))
   =
  (let
    DX = snd xDX;
    DXu = DX (eucl_of_list [1, 0, 0]);
    DXv = DX (eucl_of_list [0, 1, 0]);
    uz = vec_nth DXu 2;
    uy = vec_nth DXu 1;
    ux = vec_nth DXu 0;
    vy = vec_nth DXv 1;
    vx = vec_nth DXv 0
  in
    ux > 0 \<and> -90 < L \<and> L \<le> U \<and> U < 90 \<and> uz = 0 \<and>
    (uy / ux) \<in> {tan (rad_of L) .. tan (rad_of U)}
  )"
  if "L \<in> float" "U \<in> float"
  using that
  unfolding list_of_eucl_eucl1_3 Let_def
  by (auto  split: prod.splits simp: interpret_form_conefield_bounds_form_list divide_simps)

lemma approx_conefield_bounds_cast:
  "approx_conefield_bounds DX L U \<le> SPEC (\<lambda>b. b \<longrightarrow>
    (\<forall>(x, dx) \<in> cast_eucl1 ` DX::3 eucl1 set.
      let
        u' = dx (eucl_of_list [1, 0, 0])
      in
        vec_nth u' 1 / vec_nth u' 0 \<in> {tan (rad_of L) .. tan (rad_of U)}
        \<and> vec_nth u' 2 = 0 \<and> vec_nth u' 0 > 0 \<and> -90 < L \<and> L \<le> U \<and> U < 90)
  )"
  if "L \<in> float" "U \<in> float"
  unfolding approx_conefield_bounds_def
  apply refine_vcg
   apply (auto simp: env_len_def )
  subgoal for a b c
    apply (drule bspec, assumption)
    unfolding interpret_form_conefield_bounds_form[OF that]
    by (auto simp: Let_def divide_simps)
  done


lemma approx_conefield_bounds[le, refine_vcg]:
  "approx_conefield_bounds DX l u \<le> SPEC (\<lambda>b. b \<longrightarrow>
    (\<forall>(x, dx) \<in> DX::R3 c1_info set.
      let
        (u'1, u'2, u'3) = dx ((1, 0, 0))
      in u'2 / u'1 \<in> {tan (rad_of l) .. tan (rad_of u)} \<and> u'3 = 0 \<and> u'1 > 0 \<and> -90 < l \<and> l \<le> u \<and> u < 90)
  )"
  if "l \<in> float" "u \<in> float"
  apply (rule approx_conefield_bounds_cast[le, OF that])
  apply (auto dest!: bspec simp: Let_def split: prod.splits)
  by (auto simp: cast_eucl1_def cast_def)

schematic_goal MU\<^sub>e: "-E2 / E1 = interpret_floatarith ?fas []"
  by (reify_floatariths)
concrete_definition MU\<^sub>e uses MU\<^sub>e
schematic_goal NU\<^sub>e: "-E3 / E1 = interpret_floatarith ?fas []"
  by (reify_floatariths)
concrete_definition NU\<^sub>e uses NU\<^sub>e

definition "approx_ivls p fas xs = do {
  let xs = ivls_of_aforms p xs;
  res \<leftarrow> those (map (\<lambda>f. approx p f xs) fas);
  Some (map (real_of_float o fst) res, map (real_of_float o snd) res)
}"
definition
  "deform p t exit XDX = (case XDX of (lu, (X, DX)) \<Rightarrow>
    let
      d = ldec 0.1;
      d = if exit then (1 - real_of_float (lb_sqrt 30 (1 - 2 * float_of (d)))) else d;
      sd = real_of_float ((float_of (d*d)));
      C0Deform = aforms_of_ivls [-sd,-sd,-sd] [sd, sd, sd];
      result = msum_aforms' X C0Deform
    in (lu,
      case DX of None \<Rightarrow> (result, None)
      | Some DX \<Rightarrow> let
        C1_norm = 2 * d;
        C1_norm = if exit then real_divr 30 C1_norm (1 - C1_norm) else C1_norm;
        l = -C1_norm;
        u = C1_norm;
        D_M = aforms_of_ivls [1 + l,0,0, 0,1 + l,0, 0,0,1 + l] [1 + u,0,0, 0,1 + u,0, 0,0,1 + u];
        (ri, ru) = the (approx_ivls p
          (mmult_fa 3 3 3 (map Var [0..<9]) (map Var [9..<18])) (D_M @ DX));
        Dresult = aforms_of_ivls ri ru;
        resultDresult = product_aforms result Dresult
      in (take 3 resultDresult, Some (drop 3 resultDresult))))"

definition "ivls_of_aforms' p r = (map (Inf_aform' p) r, map (Sup_aform' p) r)"

definition "compute_half_exit p t XDX = (case XDX of ((l, u::ereal), (X, DX)) \<Rightarrow>
   let
    \<comment> \<open>ASSERTING that \<open>Y\<close> straddles zero\<close>
    (x0, y0, _) = case map (Inf_aform' p) X of [x,y,z] \<Rightarrow> (x, y, z);
    (x1, y1, _) = case map (Sup_aform' p) X of [x,y,z] \<Rightarrow> (x, y, z);
    splitting = x0 = 0 \<or> x1 = 0;
    sign_x = if (x0 + x1) / 2 > 0 then 1 else -1;
    mag_x = max (abs x0) (abs x1);
    sign_x\<^sub>e = N\<^sub>r sign_x;
    exit_rad\<^sub>e = N\<^sub>r (ldec 0.1);
    X\<^sub>e = Var (0);
    Y\<^sub>e = Var (1);
    Z\<^sub>e = Var (2);
    max_x_over_r\<^sub>e = N\<^sub>r mag_x / exit_rad\<^sub>e;
    abs_x_over_r\<^sub>e = (Abs X\<^sub>e) / exit_rad\<^sub>e;
    result = (if splitting
      then let result = (the (approx_floatariths p [sign_x\<^sub>e * exit_rad\<^sub>e,
          Y\<^sub>e * Powr (max_x_over_r\<^sub>e) MU\<^sub>e,
          Z\<^sub>e * Powr (max_x_over_r\<^sub>e) NU\<^sub>e] X));
      (ir, sr) = ivls_of_aforms' p result
      in aforms_of_ivls (ir[1:=min 0 (ir!1), 2:=min 0 (ir!2)])
                              (sr[1:=max 0 (sr!1), 2:=max 0 (sr!2)])
      else the (approx_floatariths p [sign_x\<^sub>e * exit_rad\<^sub>e,
          Y\<^sub>e * Powr (abs_x_over_r\<^sub>e) MU\<^sub>e,
          Z\<^sub>e * Powr (abs_x_over_r\<^sub>e) NU\<^sub>e] X));
    _ = ()
    in ((l::ereal, \<infinity>::ereal), (case DX of None \<Rightarrow> (result, None)
    | Some DX \<Rightarrow>
      let
        ux\<^sub>e = Var (3);
        uy\<^sub>e = Var (6);
        P21\<^sub>e = if splitting
          then (MU\<^sub>e / exit_rad\<^sub>e) * Y\<^sub>e * sign_x\<^sub>e * Powr (max_x_over_r\<^sub>e) (MU\<^sub>e - 1) \<comment> \<open>No need for \<open>Hull(0)\<close> because \<open>y\<close> straddles zero\<close>
          else (MU\<^sub>e / exit_rad\<^sub>e) * Y\<^sub>e * sign_x\<^sub>e * Powr (abs_x_over_r\<^sub>e) (MU\<^sub>e - 1);
        P22\<^sub>e = if splitting
          then Powr (max_x_over_r\<^sub>e) MU\<^sub>e
          else Powr (abs_x_over_r\<^sub>e) MU\<^sub>e;
        P31\<^sub>e = if splitting
          then sign_x\<^sub>e * (NU\<^sub>e / exit_rad\<^sub>e) * Z\<^sub>e * Powr (max_x_over_r\<^sub>e) (NU\<^sub>e - 1) \<comment> \<open>No need for \<open>Hull(\<infinity>)\<close> because scaling afterwards\<close>
          else sign_x\<^sub>e * (NU\<^sub>e / exit_rad\<^sub>e) * Z\<^sub>e * Powr (abs_x_over_r\<^sub>e) (NU\<^sub>e - 1);
        ry = (P21\<^sub>e * ux\<^sub>e) + (P22\<^sub>e * uy\<^sub>e);
        rz = P31\<^sub>e * ux\<^sub>e;
        (iDr, sDr) = the (approx_ivls p ([0, 0, 0,
             ry,   0, 0,
             rz,   0, 0]) (X @ DX));
        Dresult = aforms_of_ivls (iDr[3:=min 0 (iDr!3)])
                              (sDr[3:=max 0 (sDr!3)]);
        resultDresult = product_aforms result Dresult
      in (take 3 resultDresult, Some (drop 3 resultDresult))
    )))"

fun list3 where "list3 [a,b,c] = (a, b, c)"

definition
  "split_x n x0 y0 z0 x1 y1 z1 =
    (let
      elem = (\<lambda>(x0, x1). aforms_of_ivls [x0, y0, z0] [x1, y1, z1]);
      coord = (\<lambda>x0 n i. i * x0 * FloatR 1 (-int n));
      us = map (coord x0 n) (rev [0..<(2^n)]) @ map (coord x1 n) [Suc 0..<Suc (2^n)];
      ls = map (coord x0 n) (rev [Suc 0..<Suc (2^n)]) @ map (coord x1 n) [0..<(2^n)]
    in map elem (zip ls us))"

definition "compute_cube_exit p t XDX =
  (let
    ((l, u), (X', DX')) = deform p t False XDX;
    ((x0, y0, z0), (x1, y1, z1)) = pairself list3 (ivls_of_aforms' p X');
    X's = [aforms_of_ivls [x0, y0, z0] [0, y1, z1], aforms_of_ivls [0, y0, z0] [x1, y1, z1]];
    XDX's = map (\<lambda>X'. ((l, u), (X', DX'))) X's;
    Xes = map (compute_half_exit p t) XDX's;
    Xlumpies = map (deform p t True) Xes
  in
    Xlumpies)"


definition "cube_enteri = (map ldec [-0.1, -0.00015, 0.1,   0.8,0,0,       0.0005,0,0,   0,0,0],
                             map udec [ 0.1,  0.00015,   0.1,   1.7,0,0,      0.002,0,0,   0,0,0])"
definition "cube_enter = set_of_ivl (pairself eucl_of_list cube_enteri)"

value [code] "println ((show) (map (ivls_of_aforms' 100 o list_of_appr1e_aform)
  (compute_cube_exit 30 (FloatR 1 (-10)) ((ereal 1, ereal 1),
    (aforms_of_ivls (take 3 (fst cube_enteri))
                    (take 3 (snd cube_enteri)),
      Some (aforms_of_ivls (drop 3 (fst cube_enteri))
                       (drop 3 (snd cube_enteri))))))))"

definition "cube_exiti =
  [(aforms_of_ivls (map ldec [-0.12,  -0.024, -0.012])
                   (map udec [-0.088,  0.024,  0.13]),
     Some (aforms_of_ivls (map ldec [0,0,0,  -0.56,0,0,  -0.6,0,0])
                          (map udec [0,0,0,   0.56,0,0,  -0.08,0,0]))),
  (aforms_of_ivls (map ldec [ 0.088,  -0.024, -0.012])
                  (map udec [ 0.12,   0.024,  0.13]),
     Some (aforms_of_ivls (map ldec [0,0,0,  -0.53,0,0,   0.08,0,0])
                          (map udec [0,0,0,   0.56,0,0,   0.6,0,0])))]"
definition "cube_exitv = aform.c1_info_of_apprs cube_exiti"

lemma cube_enteri[autoref_rules]: "(cube_enteri, cube_enter::'a set) \<in> lvivl_rel"
  if "DIM_precond TYPE('a::executable_euclidean_space) 12"
  using that
  by (auto simp: cube_enteri_def cube_enter_def set_of_ivl_def
      intro!: brI lv_relivl_relI)

lemma cube_exiti[autoref_rules]: "(cube_exiti, cube_exitv::'n eucl1 set) \<in> clw_rel aform.appr1_rel"
  if "DIM_precond TYPE('n::enum rvec) 3"
  unfolding cube_exitv_def cube_exiti_def
  apply (rule aform.clw_rel_appr1_relI)
  using that
  by (auto simp: aform.c1_info_invar_def power2_eq_square)

definition "lorenz_interrupt (optns::real aform numeric_options) b (eX::3 eucl1 set) =
  do {
    ((el, eu), X) \<leftarrow> scaleR2_rep eX;
    let fX = fst ` X;
    fentry \<leftarrow> op_image_fst_ivl (cube_enter::3 vec1 set);
    interrupt \<leftarrow> aform.op_subset (fX:::aform.appr_rel) fentry;
    (ol, ou) \<leftarrow> ivl_rep fentry;
    aform.CHECKs (ST ''asdf'') (0 < el \<and> ol \<le> ou);
    let _ = (if b then aform.trace_set (ST ''Potential Interrupt: '') (Some fX) else ());
    let _ = (if b then aform.trace_set (ST ''With: '') (Some ({ol .. ou::3 rvec}:::aform.appr_rel)) else ());
    if \<not>b \<or> \<not>interrupt then RETURN (op_empty_coll, mk_coll eX)
    else do {
      vX \<leftarrow> aform.vec1rep X;
      let _ = (if b then aform.trace_set1e (ST ''Actual Interrupt: '') (Some eX) else ());
      let l = (eucl_of_list [-1/2/2,-1/2/2,-1/2/2]::3 rvec);
      let u = eucl_of_list [1/2/2, 1/2/2, 1/2/2];
      ASSERT (l \<le> u);
      let CX = mk_coll ({l .. u}:::aform.appr_rel);
      (C0::3 eucl1 set) \<leftarrow> scaleRe_ivl_coll_spec el eu (fst ` cube_exitv \<times> UNIV);
      (C1::3 eucl1 set) \<leftarrow> scaleRe_ivl_coll_spec el eu (cube_exitv);
      case vX of None \<Rightarrow> RETURN (CX, C0)
      | Some vX \<Rightarrow> do {
        b \<leftarrow> aform.op_subset vX cube_enter;
        aform.CHECKs (ST ''FAILED: TANGENT VECTORs are not contained'') b;
        RETURN (CX, C1)
      }
    }
  }"
lemma [autoref_rules]:
  includes autoref_syntax
  shows
    "(real_of_int, real_of_int) \<in> int_rel \<rightarrow> rnv_rel"
    "(ldec, ldec) \<in> Id \<rightarrow> rnv_rel"
    "(udec, udec) \<in> Id \<rightarrow> rnv_rel"
  by auto

schematic_goal lorenz_interrupti:
  includes autoref_syntax
  assumes[autoref_rules]: "(bi, b) \<in> bool_rel" "(Xi, X::3 eucl1 set) \<in> aform.appr1e_rel"
    "(optnsi, optns) \<in> Id"
  shows
    "(nres_of ?r, lorenz_interrupt optns b X) \<in> \<langle>clw_rel aform.appr_rel \<times>\<^sub>r clw_rel aform.appr1e_rel\<rangle>nres_rel"
  unfolding lorenz_interrupt_def
  including art
  by autoref_monadic
concrete_definition lorenz_interrupti for optnsi1 bi Xi uses
  lorenz_interrupti[where optnsi = "optnsi"
       and optnsa = "\<lambda>_ _ _ _ _ _ _ _. optnsi"
         and optnsb = "\<lambda>_ _ _ _ _ _ _ _ _. optnsi"
       and optnsc = "\<lambda>_ _ _ _ _ _ _ _ _ _ _. optnsi"
       and optnsd = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. optnsi"
       and optnse = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. optnsi"
       and optnsf = "\<lambda>_ _ _ _ _ _ _ _ _. optnsi"
         and optns = "\<lambda>_ _ _ _ _. optnsi"
       for optnsi]
lemma lorenz_interrupti_refine[autoref_rules]:
  includes autoref_syntax
  shows
  "(\<lambda>optnsi bi Xi. (lorenz_interrupti optnsi bi Xi),
    lorenz_interrupt)
    \<in> num_optns_rel \<rightarrow> bool_rel \<rightarrow> aform.appr1e_rel \<rightarrow> \<langle>clw_rel aform.appr_rel \<times>\<^sub>r clw_rel aform.appr1e_rel\<rangle>dres_nres_rel"
  using lorenz_interrupti.refine
  by (auto simp: nres_rel_def dres_nres_rel_def)

definition "(large_cube::R3 set) = {-1/4 .. 1/4} \<times> {-1/4 .. 1/4} \<times> {-1/4 .. 1/4}"

definition "cube_entry = (cast_eucl1 ` (flow1_of_vec1 ` cube_enter::3 eucl1 set)::R3 c1_info set)"
definition "cube_exit = (cast_eucl1 ` (cube_exitv::3 eucl1 set)::R3 c1_info set)"

text \<open>protect locale parameters\<close>
lemma flow0_cong[cong]: "auto_ll_on_open.flow0 ode X = auto_ll_on_open.flow0 ode X"
  by (auto simp:)
lemma existence_ivl0_cong[cong]:
  "auto_ll_on_open.existence_ivl0 ode X = auto_ll_on_open.existence_ivl0 ode X"
  by (auto simp:)
lemma Dflow_cong[cong]: "c1_on_open_euclidean.Dflow ode ode_d X = c1_on_open_euclidean.Dflow ode ode_d X"
  by (auto simp:)
lemma flowsto_cong[cong]:
  "c1_on_open_euclidean.flowsto ode ode_d D = c1_on_open_euclidean.flowsto ode ode_d D"
  by (auto simp:)
lemma poincare_mapsto_cong[cong]:
  "c1_on_open_euclidean.poincare_mapsto ode X = c1_on_open_euclidean.poincare_mapsto ode X"
  by (auto simp:)
lemma returns_to_cong[cong]:
  "auto_ll_on_open.returns_to ode X = auto_ll_on_open.returns_to ode X"
  by (auto simp:)
lemma return_time_cong[cong]:
  "auto_ll_on_open.return_time ode X = auto_ll_on_open.return_time ode X"
  by (auto simp: )
lemma poincare_map_cong[cong]:
  "auto_ll_on_open.poincare_map ode X = auto_ll_on_open.poincare_map ode X"
  by (auto simp: )

lemma eq_nth_iff_index:
  "distinct xs \<Longrightarrow> n < length xs \<Longrightarrow> i = xs ! n  \<longleftrightarrow> index xs i = n"
  using index_nth_id by fastforce

lemma cast_in_BasisI: "(cast i::'a) \<in> Basis"
  if "(i::'c) \<in> Basis""DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  using that
  by (auto simp: cast_def eucl_of_list_nth inner_Basis if_distrib if_distribR
      eq_nth_iff_index
      cong: if_cong)

lemma cast_le_iff: "(cast (x::'a)::'c) \<le> y \<longleftrightarrow> x \<le> cast y"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  apply (auto simp: eucl_le[where 'a='a] eucl_le[where 'a='c]
      dest!: bspec intro!: )
     apply (rule cast_in_BasisI, assumption)
     apply (auto simp: that)
    apply (metis cast_eqI2 cast_inner that)
     apply (rule cast_in_BasisI, assumption)
     apply (auto simp: that)
  apply (metis cast_eqI2 cast_inner that)
  done

lemma cast_le_cast_iff: "(cast (x::'a)::'c) \<le> cast y \<longleftrightarrow> x \<le> y"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  apply (auto simp: eucl_le[where 'a='a] eucl_le[where 'a='c]
      dest!: bspec intro!: )
     apply (rule cast_in_BasisI, assumption)
     apply (auto simp: that)
     apply (rule cast_in_BasisI, assumption)
     apply (auto simp: that)
  by (metis cast_eqI2 cast_inner that)

lemma cast_image_Icc[simp]: "cast ` {a .. b::'c} = {cast a .. cast b::'a}"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  using that
  apply (auto simp:  cast_le_iff dest!:)
  subgoal for x
    apply (rule image_eqI[where x="cast x"])
    by (auto simp: cast_le_iff)
  done

lemma cast_eucl1_image_scaleR2:
  "cast_eucl1 ` scaleR2 l u X = scaleR2 l u (cast_eucl1 ` (X::'b c1_info set)::'a c1_info set)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  using that
  apply (auto simp: scaleR2_def image_def vimage_def cast_eucl1_def
      linear.scaleR linear_cast_bl)
   apply force+
  apply (rule exI conjI)+
    apply assumption
  apply (rule exI conjI)+
    apply assumption
   apply (rule bexI) prefer 2 apply assumption
   apply force
  by (auto simp: linear.scaleR linear_cast_bl)

lemma scaleR2_diff_prod2: "scaleR2 d e (X) - Y \<times> UNIV = scaleR2 d e (X - Y \<times> UNIV)"
  by (force simp: scaleR2_def vimage_def image_def)

end

lemma (in c1_on_open_euclidean) flowsto_scaleR2I:
  "flowsto (scaleR2 d e X0) T (CX \<times> UNIV) (scaleR2 d e Y)"
  if "flowsto (X0) T (CX \<times> UNIV) (Y)"
  using that
  apply (auto simp: flowsto_def scaleR2_def)
  apply (drule bspec, assumption)
  apply auto
  apply (rule bexI) prefer 2 apply assumption
  apply auto
  subgoal for x a b h
    by (auto intro!: image_eqI[where x="(x, (flow0 a h, Dflow a h o\<^sub>L b))"] blinfun_eqI
        simp: blinfun.bilinear_simps)
  done

definition "aforms_of_resultrect x0 x1 y0 y1 = aforms_of_ivl (ivl_of_resultrect x0 x1 y0 y1)"

definition "flatten_varveq x = fst x @ the_default [] (snd x)"

(*
LessEqual (N\<^sub>r e) (N\<^sub>r em *\<^sub>e floatarith.Min (norm\<^sub>e [(3)\<^sub>e, (6)\<^sub>e, (9)\<^sub>e])
  (norm\<^sub>e [(4)\<^sub>e, (7)\<^sub>e, (10)\<^sub>e]))
*)

derive "show" ereal

definition \<Sigma>::"(real*real*real) set" where
  "\<Sigma> = {(-6, -6, 27) .. (6, 6, 27)}"
definition \<Sigma>\<^sub>l\<^sub>e::"(real*real*real) set" where
  "\<Sigma>\<^sub>l\<^sub>e = {(x, y, z). z \<le> 27}"

definition "results = symmetrize coarse_results"
definition "results_at x = {res \<in> set results.  x \<in> source_of_res res}"

text \<open>a part of the stable manifold (up to the (backward) first intersection with \<open>\<Sigma>\<close>)\<close>
definition \<Gamma>::"(real*real*real) set" where
  "\<Gamma> = {x.
    {0..} \<subseteq> lorenz.existence_ivl0 x \<and>
    (\<forall>t>0. lorenz.flow0 x t \<notin> \<Sigma>) \<and>
    (lorenz.flow0 x \<longlongrightarrow> 0) at_top}"

definition "\<Gamma>\<^sub>i intr = (if intr then \<Gamma> else {})"
definition "\<Gamma>\<^sub>i\<^sub>v intr = cast ` (\<Gamma>\<^sub>i intr)"

definition "sourcei_of_res res = source_of_res res - (\<Gamma>\<^sub>i (invoke_nf res))"
definition "resultsi_at x = {res \<in> set results.  x \<in> sourcei_of_res res}"

definition "N = \<Union>(source_of_res ` (set results))"
definition "\<CC> x = \<Union>(conefield_of_res ` (results_at x))"
definition "R = lorenz.poincare_map \<Sigma>"
definition "DR x = frechet_derivative (lorenz.poincare_map \<Sigma>) (at x within \<Sigma>\<^sub>l\<^sub>e)"
definition "\<E> x = Min (expansion ` results_at x)"
definition "\<E>\<^sub>p x = Min (preexpansion ` results_at x)"

abbreviation returns_to (infixl "returns'_to" 50) where
  "(x returns_to P) \<equiv> lorenz.returns_to P x"

lemma closed_\<Sigma>[intro, simp]: "closed \<Sigma>"
  by (auto simp: \<Sigma>_def)

lemma \<Gamma>_stable: "lorenz.stable_on (- \<Sigma>) \<Gamma>"
  unfolding lorenz.stable_on_def
proof (intro allI impI)
  fix t x0
  assume outside: "\<forall>s\<in>{0<..t}. lorenz.flow0 x0 s \<in> - \<Sigma>"
  assume assms: "lorenz.flow0 x0 t \<in> \<Gamma>" "t \<in> lorenz.existence_ivl0 x0" "0 < t"
  from assms have *: "{0..} \<subseteq> lorenz.existence_ivl0 (lorenz.flow0 x0 t)"
    "(lorenz.flow0 (lorenz.flow0 x0 t) \<longlongrightarrow> 0) at_top"
    by (auto simp: \<Gamma>_def)
  have nonneg_exivl: "s \<in> lorenz.existence_ivl0 x0" if "s \<ge> 0" for s
  proof (cases "s \<le> t")
    case True
    then show ?thesis
      using \<open>0 \<le> s\<close> assms(2) lorenz.ivl_subset_existence_ivl[of t x0] by auto
  next
    case False
    define u where "u = s - t"
    with False have "u > 0" "s = t + u" by auto
    note this(2)
    also have "t + u \<in> lorenz.existence_ivl0 x0"
      apply (rule lorenz.existence_ivl_trans)
       apply fact
      using * \<open>u > 0\<close> by auto
    finally show ?thesis .
  qed
  show "x0 \<in> \<Gamma>"
    unfolding \<Gamma>_def
  proof (safe intro!: nonneg_exivl)
    have "\<forall>\<^sub>F s in at_top. (s::real) \<ge> 0"
      using eventually_ge_at_top by blast
    then have "\<forall>\<^sub>F s in at_top. lorenz.flow0 (lorenz.flow0 x0 t) s = lorenz.flow0 x0 (s + t)"
    proof eventually_elim
      case (elim s)
      then have "s \<in> lorenz.existence_ivl0 x0"
        using nonneg_exivl[OF \<open>0 \<le> s\<close>] by simp
      then have "lorenz.flow0 (lorenz.flow0 x0 t) s = lorenz.flow0 x0 (t + s)"
        apply (subst lorenz.flow_trans)
        using assms * elim by auto
      then show ?case by (simp add: ac_simps)
    qed
    from this *(2)
    have "((\<lambda>s. (lorenz.flow0 x0 (s + t))) \<longlongrightarrow> 0) at_top"
      by (rule Lim_transform_eventually)
    then show "(lorenz.flow0 x0 \<longlongrightarrow> 0) at_top"
      unfolding aform.tendsto_at_top_translate_iff .
  next
    fix s::real assume s: "0 < s" "lorenz.flow0 x0 s \<in> \<Sigma>"
    show False
    proof (cases "s \<le> t")
      case True
      then show ?thesis
        using outside s
        by (auto simp: \<Gamma>_def)
    next
      case False
      then obtain u where u: "u = s - t" "u > 0"
        by auto
      then have "lorenz.flow0 x0 (s) = lorenz.flow0 x0 (t + u)" by (simp add: algebra_simps)
      also have "\<dots> = lorenz.flow0 (lorenz.flow0 x0 t) u"
        apply (subst lorenz.flow_trans)
        subgoal by fact
        subgoal unfolding u
          apply (rule lorenz.diff_existence_ivl_trans) apply fact+
          apply (rule nonneg_exivl) using \<open>0 < s\<close> by simp
        subgoal by simp
        done
      also from assms(1) \<open>u > 0\<close> have "\<dots> \<notin> \<Sigma>"
        by (auto simp: \<Gamma>_def)
      finally show ?thesis using s
        by auto
    qed
  qed
qed

lemma (in auto_ll_on_open) stable_on_empty[intro, simp]: "stable_on asdf {}"
  by (auto simp: stable_on_def)

lemma \<Gamma>\<^sub>i_stable: "lorenz.stable_on (- \<Sigma>) (\<Gamma>\<^sub>i b)"
  using \<Gamma>_stable
  unfolding \<Gamma>\<^sub>i_def
  apply (cases b)
  subgoal by auto
  subgoal using lorenz.stable_on_empty
    by (auto simp: \<Gamma>\<^sub>i_def)
  done

definition "\<Gamma>\<^sub>v = (cast ` \<Gamma>)"

definition "NF = lorenz.flowsto (cube_entry - \<Gamma> \<times> UNIV) {0..} (large_cube \<times> UNIV) cube_exit"

lemma NF0: "lorenz.flowsto ((fst ` cube_entry - \<Gamma>) \<times> UNIV) {0..} (large_cube \<times> UNIV)
  (fst ` cube_exit \<times> UNIV)"
  if NF
  using that
  unfolding NF_def lorenz.flowsto_def
  apply (auto simp: NF_def)
  apply (drule bspec, force)
  by auto

lemma [autoref_rules]: includes autoref_syntax shows "(\<lambda>_. (), \<Gamma>\<^sub>i\<^sub>v) \<in> bool_rel \<rightarrow> ghost_rel"
  by (auto simp: ghost_rel_def)

lemma lorenz_interrupt[le, refine_vcg]:
  "lorenz_interrupt optns b X \<le> SPEC (\<lambda>(CX, R).
    lorenz.flowsto ((cast_eucl1 ` X::R3 c1_info set) - (\<Gamma>\<^sub>i b \<times> UNIV)) {0..} (cast ` CX \<times> UNIV) (cast_eucl1 ` R))"
  if NF
  unfolding lorenz_interrupt_def
  apply refine_vcg
  subgoal
    by (rule lorenz.flowsto_self) auto
  subgoal
    by (auto simp: eucl_le[where 'a="3 rvec"] eucl_of_list_inner Basis_list_vec_def Basis_list_real_def)
  subgoal for a b c d e f g h i j k l m n p
    apply (auto)
    apply (simp add: cast_eucl1_image_scaleR2 scaleR2_diff_prod2)
    apply (erule make_neg_goal)
    apply (rule lorenz.flowsto_scaleR2I)
    using NF0[OF that]
    apply (rule lorenz.flowsto_subset)
    subgoal for q
      apply (auto simp: scaleR2_def cast_eucl1_def)
      apply (auto simp: linear_cast_bl linear.scaleR cube_entry_def cast_eucl1_def image_image)
      subgoal premises prems for r s t u v
      proof -
        from prems have "fst ` c \<subseteq> fst ` (cube_enter::3 vec1 set)"
          by auto
        with \<open>(u, v) \<in> c\<close> obtain w where "((u, w)::3 vec1) \<in> cube_enter"
          by auto
        from _ this have "cast u \<in> (\<lambda>x. cast (fst (x::3 vec1))) ` cube_enter"
          by (rule image_eqI)  auto
        then show ?thesis using prems
          by blast
      qed
      subgoal by (auto simp: \<Gamma>\<^sub>i_def)
      done
    subgoal by simp
    subgoal premises _
      by (auto simp: eucl_le[where 'a="3 rvec"] eucl_of_list_inner Basis_list_vec_def Basis_list_real_def
          eucl_of_list_def
          large_cube_def)
    subgoal premises prems for x
      apply (auto simp:)
      subgoal for A B C D E
        apply (rule image_eqI[where x="cast_eucl1 (((B, C, D), A))"])
         apply (auto simp: cast_eucl1_def)
        subgoal premises prems
          using prems(1)
          apply (auto simp: cube_exit_def aform.c1_info_of_apprs_def cube_exiti_def
              cast_eucl1_def aform.c1_info_of_appr_def)
          done
        done
      done
    done
  subgoal for a b c d e f g h i j k l m n p
    apply (auto)
    apply (erule make_neg_goal, thin_tac "\<not> _")
    apply (simp add: cast_eucl1_image_scaleR2 scaleR2_diff_prod2)
    apply (rule lorenz.flowsto_scaleR2I)
    using that[unfolded NF_def]
    apply (rule lorenz.flowsto_subset)
    subgoal for q
      apply (auto simp: scaleR2_def cast_eucl1_def )
      apply (auto simp: linear_cast_bl linear.scaleR cube_entry_def cast_eucl1_def image_image)
      subgoal premises prems for r s t u v
      proof -
        from prems have \<open>vec1_of_flow1 (u, v) \<in> cube_enter\<close>
          by auto
        from _ this have "(cast u, cast_bl v) \<in> (\<lambda>x. (cast (fst (x::3 vec1)), cast_bl (snd (flow1_of_vec1 x)))) ` cube_enter"
          by (rule image_eqI) (auto simp: )
        then show ?thesis
          using prems by blast
      qed
      subgoal by (auto simp: \<Gamma>\<^sub>i_def)
      done
    subgoal by simp
    subgoal premises _
      by (auto simp: eucl_le[where 'a="3 rvec"] eucl_of_list_inner Basis_list_vec_def Basis_list_real_def
          eucl_of_list_def
          large_cube_def)
    subgoal by (simp add: cube_exit_def)
    done
  done


definition "lorenz_S X = (case X of (x, y, z) \<Rightarrow> (-x, -y, z))"

lemma lorenz_symI: "((\<lambda>t. lorenz_S (f t)) has_vderiv_on lf') T"
  if "(f has_vderiv_on f') T" "\<And>t. t \<in> T \<Longrightarrow> lf' t = lorenz_S (f' t)"
  using that
  by (auto simp: has_vderiv_on_def lorenz_S_def  split_beta' has_vector_derivative_def
      intro!: derivative_eq_intros)

lemma lorenz_S:
  "t \<in> lorenz.existence_ivl0 (lorenz_S X)" (is ?th1)
  "lorenz.flow0 (lorenz_S X) t = lorenz_S (lorenz.flow0 X t)" (is ?th2)
  if "t \<in> lorenz.existence_ivl0 X"
proof -
  have 1: "((\<lambda>t. lorenz_S (lorenz.flow0 X t)) solves_ode
     (\<lambda>_ (X0, X1, X2).
         (E1 * X0 - K1 * (X0 + X1) * X2,
          E2 * X1 + K1 * (X0 + X1) * X2,
          E3 * X2 + (X0 + X1) * (K2 * X0 + K3 * X1))))
     {0--t} UNIV"
    apply (rule solves_odeI)
     apply (rule lorenz_symI)
      apply (rule lorenz.flow_has_vderiv_on_compose)
          apply simp
         apply simp
        apply (rule derivative_intros)
        apply (rule refl)
    using that
       apply (rule lorenz.in_existence_between_zeroI)
       apply assumption
      apply (rule refl)
    unfolding lorenz_S_def
     apply (split prod.splits)+
     apply (simp add: field_simps)
    apply simp
    done
  have "lorenz.flow0 X 0 = X"
    unfolding lorenz.flow_initial_time_if
    by simp
  then have 2:
    "lorenz_S (lorenz.flow0 X 0) = lorenz_S X"
    "is_interval {0--t}"
    "0 \<in> {0--t}"
    "{0--t} \<subseteq> UNIV"
    by auto
  from lorenz.maximal_existence_flow[OF 1 2]
  show ?th1 ?th2 by fast+
qed

lemma \<Sigma>\<^sub>l\<^sub>e_impl[autoref_rules]: "(Sctn [0, 0, 1] 27, \<Sigma>\<^sub>l\<^sub>e) \<in> \<langle>lv_rel\<rangle>below_rel"
  apply (auto simp: below_rel_def \<Sigma>\<^sub>l\<^sub>e_def below_halfspace_def sctn_rel_def
      intro!: relcompI[where b="Sctn (0, 0, 1) 27"] brI lv_relI)
  subgoal
    unfolding lv_rel_def
    by (auto intro!: brI)
  unfolding le_halfspace_def
  by (auto intro!: brI)

lemma [autoref_rules]: "((), \<Gamma>\<^sub>v) \<in> ghost_rel"
  by (auto intro!: ghost_relI)

no_notation vec_nth (infixl "$" 90) and vec_lambda (binder "\<chi>" 10)

abbreviation "guards_rel \<equiv> \<langle>clw_rel (\<langle>\<langle>lv_rel\<rangle>ivl_rel, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel) \<times>\<^sub>r aform.reach_optns_rel\<rangle>list_rel"


definition "aform_poincare_onto_from optns = aform.poincare_onto_from"

lemma aform_poincare_onto_from[autoref_rules]:
  includes autoref_syntax
  shows
"DIM_precond TYPE('b rvec) E \<Longrightarrow>
    (XSi, XS::'b::enum eucl1 set) \<in> clw_rel aform.appr1e_rel \<Longrightarrow>
    (sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel \<Longrightarrow>
    (ivli, ivl) \<in> \<langle>lv_rel\<rangle>ivl_rel \<Longrightarrow>
    (Si, Sa) \<in> \<langle>lv_rel\<rangle>halfspaces_rel \<Longrightarrow>
    (guardsi, guards) \<in> guards_rel \<Longrightarrow>
    (symstartd, symstart) \<in> aform.appr1e_rel \<rightarrow> \<langle>clw_rel aform.appr_rel \<times>\<^sub>r clw_rel aform.appr1e_rel\<rangle>dres_nres_rel \<Longrightarrow>
    ((), trap) \<in> ghost_rel \<Longrightarrow>
    (roi, roptn) \<in> aform.reach_optns_rel \<Longrightarrow>
    (odoi, odo) \<in> ode_ops_rel \<Longrightarrow>
    (optnsi, optns) \<in> num_optns_rel \<Longrightarrow>
    (nres_of
      (solve_poincare_map_aform optnsi E odoi symstartd Si guardsi ivli
        sctni roi XSi),
     aform_poincare_onto_from $ optns $ odo $ symstart $ trap $ Sa $ guards $
     ivl $
     sctn $
     roptn $
     XS)
    \<in> \<langle>clw_rel aform.appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs aform_poincare_onto_from_def
  using aform.poincare_onto_from_impl.refine[OF _ aform_ncc aform_ncc,
      where 'a='b, of E odoi odo XSi XS Si Sa guardsi guards ivli ivl sctni sctn roi roptn
        "(\<lambda>x. nres_of (symstartd x))" symstart symstartd trap optnsi,
        unfolded autoref_tag_defs, OF _ _ _ _ _ _ _ _ _ order_refl]
  by (auto simp: dest!: aform.dres_nres_rel_nres_relD)

definition "lorenz_odo_impl = init_ode_ops True True lorenz.odo"
interpretation autoref_op_pat_def lorenz.odo .
lemma lorenz_odo_impl[autoref_rules]: "(lorenz_odo_impl, lorenz.odo) \<in> ode_ops_rel"
  by (auto simp: ode_ops_rel_def lorenz_odo_impl_def)

definition lorenz_poincare where
 "lorenz_poincare optns interrupt guards roptn XS0 =
    aform_poincare_onto_from optns lorenz.odo
      (lorenz_interrupt optns interrupt)
      (\<Gamma>\<^sub>i\<^sub>v interrupt:::ghost_rel)
      ((below_halfspaces {Sctn (eucl_of_list [0, 0, 1]) 27}::(real^3) set):::\<langle>lv_rel\<rangle>halfspaces_rel)
      guards
      (op_atLeastAtMost_ivl (eucl_of_list [-6, -6, 27]:::lv_rel) (eucl_of_list [6, 6, 27]:::lv_rel):::lvivl_rel::(real^3) set)
       (Sctn (eucl_of_list [0, 0, -1]) (- 27)::(real^3) sctn)
      roptn
      XS0"

lemma [autoref_rules_raw]:
  includes autoref_syntax
  shows "((),
     (OP \<Gamma>\<^sub>i\<^sub>v ::: bool_rel \<rightarrow> ghost_rel) $
     (OP intr ::: bool_rel))
    \<in> ghost_rel" by (auto simp: ghost_rel_def)

schematic_goal lorenz_poincare_impl[autoref_rules]:
  includes autoref_syntax
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel aform.appr1e_rel"
    "(intri, intr) \<in> bool_rel"
    "(guardsi, guards) \<in> guards_rel"
    "(roi, roptn) \<in> aform.reach_optns_rel"
    "(optnsi, optns) \<in> num_optns_rel"
  shows "(nres_of ?r, lorenz_poincare $ optns $ intr $ guards $ roptn $ XS) \<in>
    \<langle>clw_rel aform.appr1e_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding lorenz_poincare_def
  including art
  supply [autoref_rules_raw] = ghost_relI
  by autoref_monadic

lemma cast_image_eqI: "cast ` X = Y"
  if "DIM('a) = DIM('b)"
    "(X::'a::executable_euclidean_space set) = cast ` (Y::'b::executable_euclidean_space set)"
  using that
  by (auto simp: image_image)

lemma transfer_\<Gamma>[transfer_rule]: "(rel_set lorenz.rel_ve) \<Gamma>\<^sub>v \<Gamma>"
  unfolding \<Gamma>\<^sub>v_def
  by (auto simp: lorenz.rel_ve_cast' intro!: rel_setI)

lemma transfer_\<Sigma>\<^sub>l\<^sub>e[transfer_rule]: "(rel_set lorenz.rel_ve) (cast ` \<Sigma>\<^sub>l\<^sub>e) \<Sigma>\<^sub>l\<^sub>e"
  by (auto simp: lorenz.rel_ve_cast' intro!: rel_setI)

lemma transfer_\<Gamma>\<^sub>i[transfer_rule]: "(rel_fun (=) (rel_set lorenz.rel_ve)) \<Gamma>\<^sub>i\<^sub>v \<Gamma>\<^sub>i"
  unfolding \<Gamma>\<^sub>i\<^sub>v_def
  by (auto simp: lorenz.rel_ve_cast' intro!: rel_setI)

lemma transfer_\<Sigma>[transfer_rule]: "(rel_set lorenz.rel_ve) (cast ` \<Sigma>) \<Sigma>"
  by (auto simp: lorenz.rel_ve_cast' intro!: rel_setI)

lemma len_fas: "length lorenz_fas = 3"
  by (auto simp: lorenz_fas_def)

lemma lorenz_poincare[le, refine_vcg]:
  "lorenz_poincare optns intr guards roptn XS \<le> SPEC (\<lambda>R.
    aform.poincare_mapsto lorenz.odo (cast ` \<Sigma>) (XS - (\<Gamma>\<^sub>i\<^sub>v intr \<times> UNIV)) (cast ` \<Sigma>\<^sub>l\<^sub>e)
   UNIV R)"
  if [refine_vcg]: NF
  unfolding lorenz_poincare_def aform_poincare_onto_from_def
  apply (refine_vcg)
  subgoal  by (simp add: aform.wd_def aform.ode_e_def len_fas)
  subgoal for a b c d
    apply (auto simp: lorenz.flowsto_eq[symmetric])
  proof goal_cases
    case 1
    from 1(2)[unfolded lorenz.flowsto_eq[symmetric]]
    show ?case
      by transfer (simp add: lorenz.avflowsto_eq)
  qed
  subgoal
    unfolding aform.stable_on_def unfolding autoref_tag_defs
  proof (intro allI impI, goal_cases)
    case (1 t x0)
    from 1 have t: "t \<in> lorenz.v.existence_ivl0 x0"
      using lorenz.vex_ivl_eq by simp
    from 1 have f: "lorenz.v.flow0 x0 t \<in> \<Gamma>\<^sub>i\<^sub>v intr"
      using lorenz.vflow_eq[OF t] by simp
    from 1 have "lorenz.v.flow0 x0 s \<in> - cast ` \<Sigma>"
      if "s\<in>{0<..t}" for s
    proof -
      from that t have s: "s \<in> lorenz.v.existence_ivl0 x0"
        by (auto dest!: lorenz.a.v.closed_segment_subset_existence_ivl
            simp: closed_segment_eq_real_ivl)
      have "lorenz.v.flow0 x0 s
        \<in> aform.Csafe lorenz.odo -
           op_atLeastAtMost_ivl (eucl_of_list [- 6, - 6, 27]) (eucl_of_list [6, 6, 27]) \<inter>
           plane_of (Sctn (eucl_of_list [0, 0, - 1]) (- 27))"
        using 1(4)[rule_format, OF that]
        unfolding lorenz.vflow_eq[OF s] 
        by auto
      also have "\<dots> \<subseteq> - cast ` \<Sigma>"
        by (auto simp: eucl_le[where 'a="real^3"] eucl_of_list_inner axis_eq_axis
               cast_def Basis_list_real_def Basis_list_vec3 \<Sigma>_def plane_of_def
               eucl_of_list_inner_eq inner_lv_rel_def)
      finally show "lorenz.v.flow0 x0 s \<in> - cast ` \<Sigma>" .
    qed
    show "x0 \<in> \<Gamma>\<^sub>i\<^sub>v intr"
      by (rule \<Gamma>\<^sub>i_stable[Transfer.untransferred, unfolded lorenz.v.stable_on_def, rule_format])
        fact+
  qed
  subgoal for R
  proof (clarsimp, goal_cases)
    case 1
    note 1(2)
    also have "({eucl_of_list [- 6, - 6, 27]..eucl_of_list [6, 6, 27]::3 rvec} \<inter>
      plane_of (Sctn (eucl_of_list [0, 0, - 1]) (- 27))) = cast ` \<Sigma>"
      apply auto
      apply (auto simp: \<Sigma>_def  o_def plane_of_def 
          eucl_of_list_def Basis_list_R3 Basis_list_vec3)
      subgoal
        by (auto simp: cast_def eucl_of_list_def Basis_list_R3 Basis_list_vec3)
      subgoal
        by (auto simp: cast_def eucl_of_list_def Basis_list_R3 Basis_list_vec3)
      subgoal
        apply (auto simp: cast_le_iff[symmetric])
        by (auto simp: cast_def eucl_of_list_def Basis_list_R3 Basis_list_vec3 less_eq_prod_def
            list_of_eucl_def inner_simps inner_axis_axis)
      subgoal
        apply (auto simp: cast_le_iff)
        by (auto simp: cast_def eucl_of_list_def Basis_list_R3 Basis_list_vec3 less_eq_prod_def
            list_of_eucl_def inner_simps inner_axis_axis)
      subgoal
        by (auto simp: cast_def eucl_of_list_def Basis_list_R3 Basis_list_vec3 less_eq_prod_def
            list_of_eucl_def inner_simps inner_axis_axis)
      done
    also have "(below_halfspaces {Sctn (eucl_of_list [0, 0, 1]::3 rvec) 27}) = (cast ` \<Sigma>\<^sub>l\<^sub>e)"
      apply (auto simp: \<Sigma>\<^sub>l\<^sub>e_def below_halfspaces_def below_halfspace_def le_halfspace_def
                    eucl_of_list_def Basis_list_R3 Basis_list_vec3)
       apply (rule image_eqI)
        apply (rule cast_cast[symmetric])
      by (auto simp:  cast_def list_of_eucl_def o_def plane_of_def inner_simps inner_axis_axis
          eucl_of_list_def Basis_list_R3 Basis_list_vec3)
    finally
    show ?case
      by (rule aform.poincare_mapsto_subset) (force simp: lorenz.vX_def intro: cast_cast[symmetric])+
  qed
  done

context includes floatarith_notation begin

definition "mat1\<^sub>e =
  [Var 0, Var 1, Var 2,   Var 3, 0, 0,
                          Var 4, 0, 0,
                          Var 5, 0, 0]"

definition mat1_nres::"3 rvec set \<Rightarrow> 3 rvec set \<Rightarrow> 3 eucl1 set nres"
  where
"mat1_nres X v = do {
  Xv \<leftarrow> aform.approx_slp_appr mat1\<^sub>e (slp_of_fas mat1\<^sub>e) (concat ` listset [list_of_eucl ` X, list_of_eucl ` v]);
  RETURN (flow1_of_vec1 ` Xv)
}"
lemma [simp]: "(x, x') \<in> aform.appr_rel \<Longrightarrow> aform.ncc x'"
  using aform_ncc[where 'a='a]
  by (auto simp: aform.ncc_precond_def)
lemma mat1e_autoref[autoref_rules]: "(mat1\<^sub>e, mat1\<^sub>e) \<in> \<langle>Id\<rangle>list_rel"
  by auto
schematic_goal mat1_impl:
  includes autoref_syntax
  assumes [autoref_rules]: "(Xi, X) \<in> aform.appr_rel" "(vi, v) \<in> aform.appr_rel"
  shows "(nres_of ?r, mat1_nres $ X $ v) \<in> \<langle>aform.appr1_rel\<rangle>nres_rel"
  unfolding mat1_nres_def
  including art
  by autoref_monadic
concrete_definition mat1_impl for Xi vi uses mat1_impl
lemmas [autoref_rules] = mat1_impl.refine

lemma mat_nres[le, refine_vcg]:
  "mat1_nres X v \<le> SPEC (\<lambda>M. X \<times> v \<subseteq> (\<lambda>x. (fst x, blinfun_apply (snd x) (eucl_of_list [1, 0, 0]))) ` M)"
  unfolding mat1_nres_def
  apply refine_vcg
  apply (auto simp: dest!: bspec)
  apply (auto simp: mat1\<^sub>e_def image_image )
  subgoal for x a b
    apply (rule image_eqI[where x="eucl_of_list
     [(list_of_eucl a @ list_of_eucl b) ! 0, (list_of_eucl a @ list_of_eucl b) ! Suc 0,
      (list_of_eucl a @ list_of_eucl b) ! 2, (list_of_eucl a @ list_of_eucl b) ! 3, 0, 0,
      (list_of_eucl a @ list_of_eucl b) ! 4, 0, 0, (list_of_eucl a @ list_of_eucl b) ! 5, 0, 0]"])
     apply (auto simp: eucl_of_list_prod eucl_of_list_inner nth_append Basis_list_vec3
        intro!: euclidean_eqI[where 'a="3 rvec"])
    unfolding Basis_list[symmetric] Basis_list_vec3
    by (auto simp: flow1_of_vec1_def blinfun_of_vmatrix.rep_eq Basis_list_vec3 inner_simps
        matrix_vector_mult_eq_list_of_eucl_nth ll3 inner_axis_axis)
  done

definition [simp]: "op_image_cast_eucl1e = (`) cast_eucl1"
definition [simp]: "op_image_cast_eucl1e_coll = (`) cast_eucl1"

lemma prod_relI'': "\<lbrakk>(fst ab, a')\<in>R1; (snd ab, b')\<in>R2\<rbrakk> \<Longrightarrow> (ab,(a', b'))\<in>\<langle>R1,R2\<rangle>prod_rel"
  by  (auto simp: prod_rel_def)

lemma strange_aux_lemma:
  "(b, b') \<in> A \<Longrightarrow> (b, snd (a'a, b')) \<in> A"
  by auto

lemma [autoref_rules]:
  includes autoref_syntax
  assumes
    "DIM_precond TYPE('a::executable_euclidean_space) D"
    "DIM_precond TYPE('b::executable_euclidean_space) D"
  shows
    "(\<lambda>x. x, (op_image_cast_eucl1e::('a::executable_euclidean_space c1_info set \<Rightarrow> 'b::executable_euclidean_space c1_info set))) \<in> aform.appr1e_rel \<rightarrow> aform.appr1e_rel"
    (is ?th1)
    and "(\<lambda>x. x, op_image_cast_eucl1e_coll::'a::executable_euclidean_space c1_info set \<Rightarrow> 'b::executable_euclidean_space c1_info set) \<in> clw_rel aform.appr1e_rel \<rightarrow> clw_rel aform.appr1e_rel"
    (is ?th2)
proof -
  show 1: ?th1
    unfolding scaleR2_rel_def
    apply (rule subsetD)
     apply (rule fun_rel_comp_dist)
    apply (rule relcompI)
     apply (rule fun_relI)
     apply (erule prod_relE)
     apply simp
     apply (rule prod_relI)
      apply simp
      apply (rule fst_conv[symmetric])
     apply (rule op_cast_eucl1_image_impl[OF assms, param_fo])
     apply (rule strange_aux_lemma)
     apply (auto simp: br_def scaleR2_def image_def vimage_def
        cast_eucl1_def)
    subgoal for a b c d e f g
      apply (rule exI[where x=e] conjI)+
       apply assumption
      apply (rule exI conjI)+
       apply assumption
      apply (rule exI conjI)+
       apply (rule bexI) prefer 2 apply assumption
       apply (rule conjI) apply force
       apply (rule refl)
      using assms
      by (auto simp: blinfun.bilinear_simps linear_cast linear.scaleR
          intro!: blinfun_eqI)
    subgoal for a b c d e f g
      apply (rule exI[where x=e] exI conjI)+
        apply assumption
       apply (rule exI conjI)+
        apply assumption
       apply (rule bexI) prefer 2 apply assumption
       apply force
      using assms
      by (auto simp: blinfun.bilinear_simps linear_cast linear.scaleR
          intro!: blinfun_eqI)
    done
  have id_map: "(\<lambda>x. x) = (map (\<lambda>x. x))" by simp
  show ?th2
    apply (subst id_map)
    apply (rule lift_clw_rel_map)
       apply (rule relator_props)+
    subgoal using 1 by auto
    subgoal by auto
    done
qed

definition "lorenz_poincare_tangents optns interrupt guards roptn c1 (X0::R3 set) (tangents::R3 set) =
  do {
    X0tanmat \<leftarrow> (if c1 then
      do {
        R \<leftarrow> mat1_nres (cast ` X0) (cast ` tangents);
        RETURN (R::3 eucl1 set)
      } else RETURN (cast ` X0 \<times> UNIV));
    XDX0 \<leftarrow> scaleRe_ivl_spec 1 1 (X0tanmat);
    let _ = aform.trace_set1e ''START'' (Some XDX0);
    let _ = aform.print_set1e False (XDX0);
    P \<leftarrow> lorenz_poincare optns interrupt guards roptn ((mk_coll XDX0:::clw_rel aform.appr1e_rel));
    RETURN (op_image_cast_eucl1e_coll P::R3 c1_info set)
  }"
lemma [autoref_rules_raw]: "DIM(real \<times> real \<times> real) = DIM((real, 3) vec)"
  by auto

schematic_goal lorenz_poincare_tangents_impl:
  includes autoref_syntax
  assumes [autoref_rules]:
    "(optnsi, optns) \<in> Id"
    "(intrri, intr) \<in> bool_rel"
    "(guardsi, guards) \<in> guards_rel"
    "(roi, roptn) \<in> aform.reach_optns_rel"
    "(c1i, c1) \<in> bool_rel"
    "(X0i, X0) \<in> aform.appr_rel"
    "(tangentsi, tangents) \<in> aform.appr_rel"
  shows
  "(nres_of ?r, lorenz_poincare_tangents $ optns $ intr $ guards $ roptn $ c1 $ (X0::R3 set) $ tangents) \<in>
    \<langle>clw_rel aform.appr1e_rel\<rangle>nres_rel"
  unfolding lorenz_poincare_tangents_def
  including art
  by (autoref_monadic)

concrete_definition lorenz_poincare_tangents_impl uses
  lorenz_poincare_tangents_impl[where
     optnsa = "\<lambda>_ _ _ _ _ _ _ _. optns"
    and optnsb = "\<lambda>_ _ _ _ _ _ _ _ _. optns"
    and optnsi = "optns"
    and optnsc = "optns"
    and optns = "\<lambda>_ _ _ _ _ _ _. optns"
  for optns optnsc]
lemma lorenz_poincare_tangents_impl_refine[autoref_rules]:
  includes autoref_syntax
  shows
  "(\<lambda>optnsi intrri guardsi roi c1i X0i tangentsi. nres_of
    (lorenz_poincare_tangents_impl optnsi intrri guardsi roi c1i X0i tangentsi),
   lorenz_poincare_tangents)
  \<in> num_optns_rel \<rightarrow> bool_rel \<rightarrow> guards_rel \<rightarrow> aform.reach_optns_rel \<rightarrow> bool_rel \<rightarrow> aform.appr_rel \<rightarrow>
    aform.appr_rel \<rightarrow>
    \<langle>clw_rel aform.appr1e_rel\<rangle>nres_rel"
  using lorenz_poincare_tangents_impl.refine by force

lemma transfer_UNIV_rel_blinfun[transfer_rule]:
  "(rel_set (rel_blinfun lorenz.rel_ve lorenz.rel_ve)) UNIV UNIV"
  apply (auto intro!: rel_setI simp: rel_blinfun_def)
  subgoal for x
    apply (rule exI[where x="cast_bl x"])
    by (auto intro!: rel_funI simp: lorenz.rel_ve_cast)
  subgoal for x
    apply (rule exI[where x="cast_bl x"])
    by (auto intro!: rel_funI simp: lorenz.rel_ve_cast)
  done

lemma lorenz_vX[simp]: "lorenz.vX = (UNIV::3 rvec set)"
  by (force simp: lorenz.vX_def intro!: cast_cast[symmetric])

lemma closed_cast_\<Sigma>[intro, simp]: "closed (cast ` \<Sigma>::3 rvec set)"
  by (auto simp: \<Sigma>_def )
lemma blinfun_apply_transfer[transfer_rule]:
  "(rel_fun (rel_blinfun lorenz.rel_ve lorenz.rel_ve)
       (rel_fun (rel_prod (=) (rel_prod (=) (=))) lorenz.rel_ve))
     (blinfun_apply o cast_bl) blinfun_apply"
  by (auto intro!: rel_funI simp: rel_blinfun_def lorenz.rel_ve_cast
      dest!: rel_funD)

lemma lorenz_poincare_tangents[le, refine_vcg]:
  "lorenz_poincare_tangents optns intr guards roptn c1 (X0::R3 set) tangents \<le>
    SPEC (\<lambda>x.
      (if c1 then \<exists>tans. X0 \<times> tangents \<subseteq> (\<lambda>(x, y). (x, blinfun_apply y (1, 0, 0))) ` tans \<and> lorenz.poincare_mapsto \<Sigma> (tans - \<Gamma>\<^sub>i intr \<times> UNIV) (\<Sigma>\<^sub>l\<^sub>e) UNIV x
       else lorenz.poincare_mapsto \<Sigma> ((X0 - \<Gamma>\<^sub>i intr) \<times> UNIV) (\<Sigma>\<^sub>l\<^sub>e) UNIV x))"
  if [refine_vcg]: NF
  unfolding lorenz_poincare_tangents_def
  apply refine_vcg
   apply auto
   apply (subst lorenz.poincare_mapsto_eq[symmetric])
    apply simp
proof goal_cases
  case (2 R)
  then show ?case
    apply transfer
    apply (subst lorenz.vpoincare_mapsto_eq[symmetric])
     apply (auto simp: )
    apply (rule aform.poincare_mapsto_subset, assumption)
    by (force simp: scaleR2_def )+
next
  case (1 tans R)
  show ?case
    apply (rule exI[where x="cast_eucl1 ` tans"])
    apply (rule conjI)
    subgoal including lifting_syntax
      using 1(2)
      by transfer (force simp: cast_def o_def)
    subgoal
      using 1(3) apply transfer
      apply (subst lorenz.avpoincare_mapsto_eq[symmetric])
      by (auto simp: )
    done
qed

definition of_mat1_image::"R3 c1_info set \<Rightarrow> R3 set nres"
  where [refine_vcg_def]: "of_mat1_image X = SPEC (\<lambda>R. R = (\<lambda>x. blinfun_apply (snd x) (1, 0, 0)) ` X)"

lemma of_mat1_image_impl[autoref_rules]:
  "(\<lambda>x. (case x of (_, Some xs) \<Rightarrow> RETURN [xs ! 0, xs ! 3, xs ! 6]
          | (_, None) \<Rightarrow> SUCCEED), of_mat1_image) \<in> aform.appr1_rel \<rightarrow> \<langle>aform.appr_rel\<rangle>nres_rel"
  apply (auto simp: of_mat1_image_def RETURN_RES_refine_iff nres_rel_def
      aform.appr1_rel_internal aform.appr_rel_def
      intro!: relcompI
      split: option.splits)
  unfolding aforms_rel_def
   apply (rule brI)
    apply (auto simp: )
  unfolding lv_rel_def set_rel_br
  apply (rule brI)
   prefer 2 apply (force simp: Joints_imp_length_eq)
  apply (auto elim!: mem_Joints_appendE simp: flow1_of_list_def Joints_imp_length_eq)
  subgoal for a b c d e f g h i j
    apply (rule image_eqI[where x="[j ! 0, j ! 3, j! 6]"])
     apply (auto simp: blinfun_of_list_def blinfun_of_matrix_apply
        Basis_prod_def Basis_list_R3 Basis_list_vec3 eval_nat_numeral zero_prod_def)
    apply (rule map_nth_Joints'[of _ _ "[0, Suc (Suc (Suc 0)), Suc (Suc (Suc (Suc (Suc (Suc 0)))))]",
          simplified])
    apply auto
    done
  subgoal for a b c d e f
    unfolding image_image
    apply (auto simp: Joints_def valuate_def)
    subgoal for g
      apply (rule image_eqI)
      prefer 2
      apply (rule image_eqI[where x=g])
      apply (rule refl)
      apply (auto simp: )
      apply (auto simp: blinfun_of_list_def blinfun_of_matrix_apply flow1_of_list_def
          Basis_prod_def Basis_list_R3 Basis_list_vec3 eval_nat_numeral zero_prod_def)
      done
    done
  done

definition [refine_vcg_def]: "floatdegs res = SPEC (\<lambda>_::unit. min_deg res \<in> float \<and> max_deg res \<in> float)"
definition [simp]: "isinfloat x \<longleftrightarrow> x \<in> float"
lemma [code]: "isinfloat (real_of_float x) = True"
  by (auto)

lemma floatdegs_impl[autoref_rules]:
  includes autoref_syntax
  shows
  "(\<lambda>res. (if isinfloat (min_deg res) \<and> isinfloat (max_deg res) then RETURN () else SUCCEED), floatdegs)
    \<in> Id \<rightarrow> \<langle>unit_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def floatdegs_def)

definition "check_c1_entry optns em P (res0::result) (res::result) = do {
    uv_ret \<leftarrow> of_mat1_image P;
    nuv \<leftarrow> aform.mig_set 3 uv_ret;
    floatdegs res0;
    floatdegs res;
    let e' = em * ereal nuv;
    b1 \<leftarrow> approx_conefield_bounds P (min_deg res) (max_deg res);
    let b2 = e' \<ge> preexpansion res;
    let b3 = e' \<ge> expansion res0;
    let _ = aform.print_msg ((shows ''# check_c1_entry: '' o shows_list [b1, b2, b3] o shows_space o
      shows_list [e', preexpansion res, expansion res0]) '''');
    RETURN (em \<ge> 0 \<and> b1 \<and> b2 \<and> b3)
  }"

lemma [autoref_itype]:
  "shows_prec ::\<^sub>i i_nat \<rightarrow>\<^sub>i A \<rightarrow>\<^sub>i i_string \<rightarrow>\<^sub>i i_string"
  by auto

lemma [autoref_rules]:
  includes autoref_syntax
  shows
    "PREFER_id A \<Longrightarrow> (shows_list, shows_list) \<in> \<langle>A\<rangle>list_rel \<rightarrow> string_rel \<rightarrow> string_rel"
    "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel \<rightarrow> string_rel"
    "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> ereal_rel \<rightarrow> string_rel \<rightarrow> string_rel"
    "(shows_prec, shows_prec::_\<Rightarrow>result \<Rightarrow>_) \<in> nat_rel \<rightarrow> Id \<rightarrow> string_rel \<rightarrow> string_rel"
    "(shows_space, shows_space) \<in> string_rel \<rightarrow> string_rel"
  by (auto simp: string_rel_def)
lemma [autoref_rules]:
  includes autoref_syntax
  shows
    "(expansion, expansion) \<in> Id \<rightarrow> rnv_rel"
    "(preexpansion, preexpansion) \<in> Id \<rightarrow> rnv_rel"
    "(min_deg, min_deg) \<in> Id \<rightarrow> rnv_rel"
    "(max_deg, max_deg) \<in> Id \<rightarrow> rnv_rel"
  by auto
interpretation autoref_op_pat_def aform.mig_set .
lemma [autoref_rules_raw]: "DIM_precond TYPE(real \<times> real \<times> real) (OP 3 ::: nat_rel)"
  by simp
schematic_goal check_c1_entry_impl:
  includes autoref_syntax
  assumes [autoref_rules]:
    "(optnsi, optns) \<in> Id"
    "(res0i, res0) \<in> Id"
    "(resi, res) \<in> Id"
    "(emi, em) \<in> ereal_rel"
    "(Pei, P) \<in> aform.appr1_rel"
  shows
    "(nres_of ?r, check_c1_entry optns em P res0 res) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding check_c1_entry_def
  including art
  by autoref_monadic

concrete_definition check_c1_entry_impl uses check_c1_entry_impl[
    where optns = "\<lambda>_ . optnsi"
    and optnsi="optnsi"
    and optnsc=optns
    and optnsa="\<lambda>_ _ _ _ _. optnsi"
    and optnsb="\<lambda>_ _ _ _  _ _ _ _ . optnsi"
    and optns="\<lambda>_. optnsi"
    for optns optnsi]
lemmas check_c1_entry_impl_refine[autoref_rules] = check_c1_entry_impl.refine[autoref_higher_order_rule]

definition "c1_entry_correct (em::ereal) (P::R3 c1_info set) res0 res = (\<forall>(_, d)\<in>P. case (d (1, 0, 0)) of (dx, dy, dz) \<Rightarrow>
      dz = 0 \<and> dx > 0 \<and> -90 < min_deg res \<and> min_deg res \<le> max_deg res \<and> max_deg res < 90 \<and>
      ereal (preexpansion res) \<le> em * (norm (dx, dy, dz)) \<and>
      ereal (expansion res0) \<le> em * (norm (dx, dy, dz)) \<and>
      dy / dx \<in> {tan (rad_of (min_deg res)) .. tan (rad_of (max_deg res))})"

lemma check_c1_entry[le, refine_vcg]:
  "check_c1_entry optns em P res0 res \<le> SPEC (\<lambda>b. b \<longrightarrow> c1_entry_correct em P res0 res)"
  unfolding check_c1_entry_def c1_entry_correct_def
  apply refine_vcg
  apply (auto dest!: bspec simp:)
    apply (rule order_trans, assumption, rule ereal_mult_left_mono, force, force)
  apply (rule order_trans, assumption, rule ereal_mult_left_mono, force, force)
  done


subsection \<open>options for the lorenz system\<close>

definition aform_numeric_optns::"_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
    real aform numeric_options" where
  "aform_numeric_optns = numeric_options.fields"

fun zbucket::"real \<Rightarrow>  real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> ((real list \<times> real list) \<times> real list sctn) list"
  where "zbucket d (x0,x1) (y0, y1) (z0, z1) =
    [zsec' (x0 - d, x0 + d) (y0 - d, y1 + d) z0, \<comment> \<open>bottom\<close>
     xsec' x0 (y0 - d, y1 + d) (z0 - d, z1),     \<comment> \<open>left\<close>
     xsec x1 (y0 - d, y1 + d) (z0 - d, z1),      \<comment> \<open>right\<close>
     ysec' (x0 - d, x1 + d) y0 (z0 - d, z1),     \<comment> \<open>backno\<close>
     ysec (x0 - d, x1 + d) y1  (z0 - d, z1)]     \<comment> \<open>front\<close>"

subsubsection \<open>Hybridizations\<close>

definition "reduce_weak_params c1 = (if c1 then (12::nat, 0::nat) else (3, 0))"
definition "reduce_hard_params c1 = (if c1 then (0::nat, 100::nat) else (0, 100))"
definition "ro_split_weak   c1 w     = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro (w + 1) m n w w (-5))"
definition "ro_split_weak'  c1 w     = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro w m n w w (-5))"
definition "ro_split_weak'' c1 w     = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro (w + 2) m n w w (-5))"
definition "ro_split_weak4' c1 w     = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro (w + 4) m n w w (-5))"
definition "ro_split_weak2  c1 w w2  = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro (w + 1) m n w w2 (-5))"
definition "ro_split_weak2' c1 w w2  = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro (w) m n w w2 (-5))"
definition "ro_split_hard   c1 w0 w1 = (case reduce_hard_params c1 of (m, n) \<Rightarrow> ro (w0 + 1) m n w0 w1 (-5))"
definition "ro_split_hard'' c1 w0 w1 = (case reduce_hard_params c1 of (m, n) \<Rightarrow> ro (w0 + 2) m n w0 w1 (-5))"
definition "ro_split_not    c1 w     = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro       0 m n w w (-5))"
definition "ro_split_not2   c1 w w2  = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro       0 m n w w2 (-5))"

definition "xsecs x y z = [xsec' (-x) (-y, y) (0, z), xsec x (-y, y) (0, z)]"

type_synonym run_options = "(nat \<times> nat) \<times> int \<times>
  (((real list \<times> real list) \<times> real list sctn) list \<times> real aform reach_options) list \<times> real aform reach_options"

abbreviation "p1 \<equiv> ldec 0.1"

definition mode_middle::"_ \<Rightarrow> run_options" where "mode_middle c1 = (reduce_weak_params c1, -14,
  [([zsec' (-2, 2) (-1, 1) 10], ro_split_weak' c1 (-3)),
  (xsecs (5 * p1)  10    10 @
   xsecs p1      10  (6) @
   [zsec' (-p1, p1) (-p1, p1) p1],
      ro_split_hard c1 (-5) (-2)),
  (xsecs (3/2/2) 10 (10), ro_split_not2 c1 0 (-2)), \<comment> \<open>To collect after interrupt\<close>
    ([zsec (-30, -6) (-10, 10) 30, zsec (6, 30) (-10, 10) 30], ro_split_not2 c1 (-1) (-3))
  ], ro_split_weak4' c1 (-5))"

definition mode_inner3::"bool\<Rightarrow>bool\<Rightarrow>run_options" where "mode_inner3 c1 very_inner =
   (reduce_weak_params c1, -15,
    (if very_inner then [([zsec' (-2, 2) (-1, 1) 10], ro_split_weak' c1 (-2))] else [])@
    [(xsecs (3/2) 15 27@xsecs 1 (10) (11/2), ro_split_weak2 c1 (-2) (-1)),
     ([ zsec (-30, -6) (-10, 10) 30, zsec (6, 30) (-10, 10) 30], ro_split_not2 c1 (-1) (-3))
    ],
     if very_inner then ro_split_weak4' c1 (-5) else ro_split_weak'' c1 (-5))"

definition mode_inner2::"bool \<Rightarrow> real \<Rightarrow> run_options" where "mode_inner2 c1 x =
  (reduce_weak_params c1, -14,
    [(xsecs x 10 27, ro_split_weak2' c1 (-2) (-1)),
     ([zsec ( -30, -6) (-10, 10) 30, zsec (6, 30) (-10, 10) 30], ro_split_not2 c1 (-3) (-3))],
  ro_split_not c1 (-6))"

definition "ro_outer c1 w = (case reduce_weak_params c1 of (m, n) \<Rightarrow> ro w m n (-6) (-6) (-5))"
definition mode_outer::"bool\<Rightarrow>_\<Rightarrow>_\<Rightarrow>run_options" where
  "mode_outer c1 w i = (reduce_weak_params c1, (-i),
    [([zsec (-30, -6) (-10, 10) 27, zsec (6, 30) (-10, 10) 27], ro_split_not2 c1 (-3) (-4))], ro_outer c1 w)"

definition lookup_mode::"bool \<Rightarrow> result \<Rightarrow> _" where
"lookup_mode c1 i =
  (if     gridx0 i \<le> - 1024 then mode_outer  c1 (-3) 16
  else if gridx0 i \<le> - 120  then mode_outer  c1 (-3) 14
  else if gridx0 i \<le> 107    then mode_inner2 c1 (4)
  else if gridx0 i \<le> 169    then mode_inner3 c1 False
  else if gridx0 i \<le> 196    then mode_inner3 c1 True
  else if gridx0 i \<le> 201    then mode_middle c1
  else if gridx0 i \<le> 235    then mode_inner3 c1 True
  else if gridx0 i \<le> 290    then mode_inner3 c1 False
  else if gridx0 i \<le> 450    then mode_inner2 c1 4
  else                           mode_outer  c1 (-3) 14)"

definition mode_ro_spec::"bool \<Rightarrow> result \<Rightarrow> ((nat \<times> nat) \<times>
          int \<times> ((real, 3) vec set \<times> unit) list \<times>
          unit) nres"
where [refine_vcg_def]: "mode_ro_spec c1 res = SPEC (\<lambda>_. True)"

lemma reach_options_rel_br: "reach_options_rel TYPE('ty) = br (\<lambda>_. ()) (\<lambda>_. True)"
  by (auto simp: reach_options_rel_def br_def)

lemma mode_ro_spec_impl[autoref_rules]:
  includes autoref_syntax
  shows "(\<lambda>b x. RETURN (lookup_mode b x), mode_ro_spec) \<in> bool_rel \<rightarrow> Id \<rightarrow>
    \<langle>(nat_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r int_rel \<times>\<^sub>r guards_rel \<times>\<^sub>r aform.reach_optns_rel\<rangle>nres_rel"
  supply [simp del] = prod_rel_id_simp
  apply (rule fun_relI)
  apply (rule fun_relI)
  apply (rule nres_relI)
  unfolding mode_ro_spec_def
  apply (rule RETURN_SPEC_refine)
  apply (auto simp: mode_ro_spec_def nres_rel_def RETURN_RES_refine_iff)
  apply (rule exI)+
  apply (rule prod_relI'' IdI)+
  unfolding lv_rel_def ivl_rel_def br_rel_prod br_chain plane_rel_br inter_rel_br
    clw_rel_br br_list_rel Id_br prod_eq_iff reach_options_rel_br
   apply (rule brI refl)+
   defer apply (rule brI) apply (rule refl) apply auto
  apply (auto simp: lookup_mode_def mode_outer_def mode_inner2_def mode_inner3_def xsecs_def
      mode_middle_def)
  done

lemma [autoref_rules]: includes autoref_syntax shows
  "(ivl_of_res, ivl_of_res) \<in> Id \<rightarrow> \<langle>rnv_rel\<rangle>list_rel \<times>\<^sub>r \<langle>rnv_rel\<rangle>list_rel"
  by auto


lemma [autoref_rules]: includes autoref_syntax shows
  "(Polygon.pairself, Polygon.pairself) \<in> (A \<rightarrow> C) \<rightarrow> (A \<times>\<^sub>r A) \<rightarrow> (C \<times>\<^sub>r C)"
  by (auto dest: fun_relD)

lemma set_of_ivl_impl[autoref_rules]: includes autoref_syntax shows
  "(\<lambda>x. x, set_of_ivl) \<in> (A \<times>\<^sub>r A) \<rightarrow> \<langle>A\<rangle>ivl_rel"
  by (auto simp: ivl_rel_def br_def)
lemma eucl_of_list_pad: includes autoref_syntax shows
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
    (\<lambda>xs. take D xs @ replicate (D - length xs) 0, eucl_of_list::_\<Rightarrow>'a) \<in> rl_rel \<rightarrow> lv_rel"
  unfolding lv_rel_def
  by (auto simp: intro!: brI)
concrete_definition eucl_of_list_pad uses eucl_of_list_pad
lemmas [autoref_rules] = eucl_of_list_pad.refine

lemma source_of_res_impl[autoref_rules]: includes autoref_syntax shows
  "(ivl_of_res, source_of_res) \<in> Id \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel"
  unfolding source_of_res_def
  apply (auto simp: ivl_rel_def intro!: relcompI brI)
  subgoal for a
    apply (auto simp: ivl_of_res_def ivl_of_resultrect_def
        intro!: lv_relI)
    unfolding lv_rel_def
     apply (auto intro!: brI)
    done
  done

definition tangent_seg_of_res :: "real aform numeric_options \<Rightarrow> result \<Rightarrow> R3 set nres" where
"tangent_seg_of_res optns res0 = do {
  let fas = map (OP (nth matrix_of_degrees2\<^sub>e)) [0, 3, 6];
  let u = min_deg res0;
  let v = max_deg res0;
  aform.approx_slp_appr fas (slp_of_fas fas) (lv_ivl [u, v, 0] [u, v, 1])
}"
lemmas [refine_vcg_def] = tangent_seg_of_res_spec_def
lemma tangent_seg_of_res[le, refine_vcg]:
  "tangent_seg_of_res optns res \<le> tangent_seg_of_res_spec res"
  unfolding tangent_seg_of_res_def tangent_seg_of_res_spec_def
  apply refine_vcg
  apply (auto simp: matrix_of_degrees2\<^sub>e_def Let_def in_segment)
  subgoal for x a b c u
    by (drule bspec[where x="[min_deg res, max_deg res, u]"])
       (auto simp: tangent_of_deg_def lv_ivl_def algebra_simps intro!:)
  done
lemma [autoref_rules]: includes autoref_syntax shows
  "(nth matrix_of_degrees2\<^sub>e, nth matrix_of_degrees2\<^sub>e) \<in> nat_rel \<rightarrow> Id"
  by auto
schematic_goal tangent_seg_of_res_impl:
  includes autoref_syntax
  assumes [autoref_rules]: "(resi, res) \<in> Id"
    "(optnsi, optns) \<in> num_optns_rel"
  shows
  "(nres_of ?r, tangent_seg_of_res optns res) \<in> \<langle>aform.appr_rel\<rangle>nres_rel"
  unfolding tangent_seg_of_res_def
  including art
  by autoref_monadic
concrete_definition tangent_seg_of_res_impl uses tangent_seg_of_res_impl
lemmas [autoref_rules] = tangent_seg_of_res_impl.refine[where
    optnsi = optnsi and optnsa=optns and optns="\<lambda>_ _ _. optnsi" for optns optnsi, autoref_higher_order_rule]

lemma return_of_res_impl:
 includes autoref_syntax shows
  "(\<lambda>results res. (get_results (inf_retx res) (inf_rety res) (sup_retx res) (sup_rety res) results),
    return_of_res) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_wset_rel"
  by (auto simp: return_of_res_def list_wset_rel_def intro!: brI)
concrete_definition return_of_res_impl uses return_of_res_impl
lemmas [autoref_rules] = return_of_res_impl.refine

lemma lorenz_optns'_impl[autoref_rules]: includes autoref_syntax shows
  "(lorenz_optns', lorenz_optns') \<in>
    \<langle>Id \<rightarrow> unit_rel\<rangle>option_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> num_optns_rel"
  by auto
lemma [autoref_rules]:
  includes autoref_syntax shows
    "(results, results) \<in> \<langle>Id\<rangle>list_rel"
    "(invoke_nf, invoke_nf) \<in> Id \<rightarrow> bool_rel"
  by auto

definition "check_line_nres print_fun m0 n0 c1 res0 = do {
    let X0 = source_of_res res0;
    (X0l, X0u) \<leftarrow> ivl_rep X0;
    ((m::nat, n::nat), a::int, modes, ro) \<leftarrow> mode_ro_spec c1 res0;
    let interrupt = invoke_nf res0;
    let optns = lorenz_optns' print_fun (the_default m m0) (the_default n n0) 1 (FloatR 1 a);
    tangents \<leftarrow> tangent_seg_of_res optns res0;
    aform.CHECKs (ST ''check_line_nres le'') (X0l \<le> X0u);
    sp \<leftarrow> aform.subset_spec_plane X0 (Sctn (eucl_of_list [0, 0, 1]) 27);
    aform.CHECKs (ST ''check_line_nres le'') sp;
    ASSERT (X0l \<le> X0u);
    Pe \<leftarrow> lorenz_poincare_tangents optns interrupt modes ro c1 ({X0l .. X0u}) tangents;
    PeS \<leftarrow> sets_of_coll Pe;
    let RETs = (return_of_res results res0);
    let RET = \<Union>((mk_coll ` (source_of_res ` RETs:::\<langle>lvivl_rel\<rangle>list_wset_rel):::\<langle>clw_rel lvivl_rel\<rangle>list_wset_rel));
    every \<leftarrow> WEAK_ALL\<^bsup>\<lambda>Pe. \<exists>P em eM Rivls. em > 0 \<and> Pe = scaleR2 em eM P \<and> fst ` P \<subseteq> \<Union>Rivls \<and> (\<forall>Rivl \<in> Rivls. (\<exists>res\<in>RETs. Rivl \<subseteq> source_of_res res \<and> (c1 \<longrightarrow> c1_entry_correct em P res0 res)))\<^esup>
    PeS (\<lambda>Pe. do {
      let _ = aform.trace_set1e (ST ''# Return Element: '') (Some Pe);
      ((em, eM), P) \<leftarrow> scaleR2_rep Pe;
      aform.CHECKs (ST ''check_line_nres pos'') (0 < em);
      let R = (fst ` P:::aform.appr_rel);
      (Ri, Rs) \<leftarrow> op_ivl_rep_of_set R;
      let Rivl = (op_atLeastAtMost_ivl Ri Rs);
      Rivls \<leftarrow> aform.split_along_ivls2 3 (mk_coll Rivl) RET;
      Rivlss \<leftarrow> sets_of_coll Rivls;
      WEAK_ALL\<^bsup>\<lambda>Rivl. \<exists>res\<in>RETs. Rivl \<subseteq> source_of_res res \<and> (c1 \<longrightarrow> c1_entry_correct em P res0 res)\<^esup> Rivlss
      (\<lambda>Rivl. do {
        b \<leftarrow>
          WEAK_EX\<^bsup>\<lambda>res. Rivl \<subseteq> source_of_res res \<and> (c1 \<longrightarrow> c1_entry_correct em P res0 res)\<^esup> RETs
          (\<lambda>res. do {
            let src = (source_of_res res:::lvivl_rel);
            let subs = Rivl \<subseteq> src;
            cones \<leftarrow> if \<not>(c1 \<and> subs) then RETURN True else check_c1_entry optns em P res0 res;
            RETURN (subs \<and> cones)
          });
        let _ = aform.print_msg ((shows (ST ''# return of '') o shows res0 o
          shows (if b then ST '' OK'' else ST '' FAILED''))'''');
        RETURN b
      })
    });
    RETURN (every, Pe, RET)
  }"


definition "aform_subset_spec_plane optns = aform.subset_spec_plane"

lemma aform_subset_spec_plane_impl[autoref_rules]:  includes autoref_syntax shows
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (Xi, X::'a set) \<in> \<langle>lv_rel\<rangle>ivl_rel \<Longrightarrow>
  (sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel \<Longrightarrow>
  (optnsi, optns) \<in> num_optns_rel \<Longrightarrow>
  (nres_of (subset_spec_plane_impl_aform optnsi D Xi sctni),
   aform_subset_spec_plane $ optns $ X $ sctn)
  \<in> \<langle>bool_rel\<rangle>nres_rel"
  using aform.subset_spec_plane_impl.refine[where 'a='a, of D Xi X sctni sctn optnsi]
  by (force simp: aform_subset_spec_plane_def)

schematic_goal check_line_impl:
  includes autoref_syntax
  assumes [autoref_rules]: "(pfi, pf) \<in> \<langle>Id \<rightarrow> unit_rel\<rangle>option_rel"
    "(c1i, c1) \<in> bool_rel" "(res0i, res0) \<in> Id"
    "(m0i, m0) \<in> \<langle>nat_rel\<rangle>option_rel" "(n0i, n0) \<in> \<langle>nat_rel\<rangle>option_rel"
  shows
  "(nres_of ?r, check_line_nres $ pf $ m0 $ n0 $ c1 $ res0) \<in>
    \<langle>bool_rel \<times>\<^sub>r clw_rel aform.appr1e_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding check_line_nres_def
  including art
  by autoref_monadic

concrete_definition check_line_impl uses check_line_impl[where
     optns = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ . lorenz_optns pfi"
    and optnsa = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and optnsb = "\<lambda>_ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and optnsc = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and optnsd = "\<lambda>_ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and optnse = "\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and optnsf = "\<lambda> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. lorenz_optns pfi"
    and pfi = pfi
    for pfi]
lemmas [autoref_rules] = check_line_impl.refine


lemma check_line_nres:
  "check_line_nres pf m0 n0 c1 res0 \<le> SPEC (\<lambda>(every, Pe, RET). \<exists>P. Pe = \<Union>P \<and>
    (if c1
    then \<exists>tans. source_of_res res0 \<times> {tangent_of_deg (min_deg res0)--tangent_of_deg (max_deg res0)} \<subseteq> (\<lambda>(x, y). (x, blinfun_apply y (1, 0,  0))) ` tans \<and>
                lorenz.poincare_mapsto \<Sigma> (tans - \<Gamma>\<^sub>i (invoke_nf res0) \<times> UNIV) \<Sigma>\<^sub>l\<^sub>e UNIV (Pe)
    else lorenz.poincare_mapsto \<Sigma> ((sourcei_of_res res0) \<times> UNIV) \<Sigma>\<^sub>l\<^sub>e UNIV (\<Union>P)) \<and>
    source_of_res res0 \<subseteq> plane_of (Sctn (0, 0, 1) 27) \<and>
    (every \<longrightarrow>
    (\<forall>x\<in>P. \<exists>P em. em > 0 \<and> (\<exists>eM. x = scaleR2 em eM P) \<and>
                   (\<exists>Rivls. fst ` P \<subseteq> \<Union>Rivls \<and>
                            (\<forall>Rivl\<in>Rivls.
                                \<exists>res\<in>return_of_res results res0.
                                   Rivl \<subseteq> source_of_res res \<and> (c1 \<longrightarrow> c1_entry_correct em P res0 res))))))"
  if [refine_vcg]: NF
  unfolding check_line_nres_def sourcei_of_res_def
  apply (refine_vcg, clarsimp_all)
  using [[goals_limit=1]]
  subgoal for a0 a b c d e f g h i j k l m n p q r s t
    apply (rule exI[where x=i])
    apply (rule exI[where x=j])
    apply (rule conjI)
     apply force
    apply (rule conjI)
    apply (rule exI[where x=k])
     apply force
    apply (rule exI[where x=s])
    apply (rule conjI) defer apply force
    apply blast
    done
  subgoal for x0 y0 z0 x1 y1 z1 tangents s R every
    apply (rule exI[where x=R])
    apply auto
    subgoal for tans
      apply (rule exI[where x=tans])
      by auto
    subgoal for tans
      apply (rule exI[where x=tans])
      by auto
    done
  done

definition "print_sets_color (print_fun::String.literal \<Rightarrow> unit) (c::string) (X::'a::executable_euclidean_space set) = ()"

definition "print_lorenz_color print_fun cx cy cz ci cd1 cd2 P = ()"

definition "print_aforms print_fun c aforms =
  fold (\<lambda>a _.  print_fun (String.implode (shows_segments_of_aform 0 1 a c ''\<newline>''))) aforms ()"

lemma print_sets_color_impl[autoref_rules]: includes autoref_syntax shows
  "(\<lambda>print_fun c X. print_aforms print_fun c X, print_sets_color) \<in>
    (Id \<rightarrow> unit_rel) \<rightarrow> string_rel \<rightarrow> clw_rel aform.appr_rel \<rightarrow> unit_rel"
  by auto

lemma print_lorenz_color_impl[autoref_rules]: includes autoref_syntax shows
  "(\<lambda>print_fun cx cy cz ci cd1 cd2 P.
    fold (\<lambda>(_, x) b.
        print_lorenz_aform print_fun
          cx cy cz ci cd1 cd2
          False
          (fst x @ the_default [] (snd x))
        ) P (), print_lorenz_color) \<in>
    (Id \<rightarrow> unit_rel) \<rightarrow> string_rel \<rightarrow> string_rel \<rightarrow> string_rel \<rightarrow> string_rel \<rightarrow>
    \<langle>\<langle>string_rel\<rangle>list_rel, \<langle>\<langle>string_rel\<rangle>list_rel, (\<langle>clw_rel aform.appr1e_rel, unit_rel\<rangle>fun_rel)\<rangle>fun_rel\<rangle>fun_rel"
  by auto

definition check_line_core where
 "check_line_core print_funo m0 n0 c1 i =
  do {
      let print_fun = the_default (\<lambda>_. ()) print_funo;
      CHECK (\<lambda>_. print_fun (STR ''Hey, out of bounds!'')) (i < length results);
      let res = ((results:::\<langle>Id\<rangle>list_rel) ! (i:::nat_rel));
      (r, P, B) \<leftarrow> check_line_nres print_funo m0 n0 c1 res;
      let _ = print_sets_color print_fun (ST ''0x007f00'') (aform.sets_of_ivls B);
      (_, Pu) \<leftarrow> scaleR2_rep_coll P;
      let _ = print_sets_color print_fun (ST ''0x7f0000'')
          (aform.op_image_fst_coll (Pu:::clw_rel aform.appr1_rel):::clw_rel aform.appr_rel);
      let _ = print_lorenz_color print_fun
          (ST ''0x7f0000'') (ST ''0x7f0001'') (ST ''0x7f0002'') (ST ''0x7f0003'')
          [(ST ''0xc60000''), (ST ''0xc60000''), (ST ''0xc60000'')]
          [(ST ''0xf60000''), (ST ''0xf60000''), (ST ''0xf60000'')]
          P;
      let _ = (if r
        then print_fun
          (String.implode ((show (ST ''# VERIFIED '') @ show i @ show (ST ''\<newline>''))))
        else print_fun (String.implode ((show (ST ''# Failed to verify '') @ show i @ show (ST ''\<newline>'')) )));
      RETURN r
    }"
lemma [autoref_rules]: includes autoref_syntax shows
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(String.implode, String.implode) \<in> string_rel \<rightarrow> Id"
  by (auto simp: string_rel_def)
schematic_goal check_line_core_impl:
  includes autoref_syntax
  assumes [autoref_rules]: "(pfi, pf) \<in> \<langle>Id \<rightarrow> unit_rel\<rangle>option_rel"
    "(c1i, c1) \<in> bool_rel" "(ii, i) \<in> nat_rel"
    "(m0i, m0) \<in> \<langle>nat_rel\<rangle>option_rel" "(n0i, n0) \<in> \<langle>nat_rel\<rangle>option_rel"
  shows "(nres_of ?f, check_line_core $ pf $ m0 $ n0 $ c1 $ i) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding check_line_core_def
  including art
  by autoref_monadic
concrete_definition check_line_core_impl for pfi m0i n0i c1i ii uses check_line_core_impl
lemmas [autoref_rules] = check_line_core_impl.refine

definition "c1i_of_res res = sourcei_of_res res \<times> conefield_of_res res"

definition "correct_res res =
  ((\<forall>(x, dx) \<in> c1i_of_res res.
    x \<in> plane_of (Sctn (0, 0, 1) 27) \<and>
    dx \<in> plane_of (Sctn (0, 0, 1) 0) \<and>
    ((lorenz.returns_to \<Sigma> x \<and>
      lorenz.return_time \<Sigma> differentiable at x within \<Sigma>\<^sub>l\<^sub>e \<and>
      (\<exists>D. (lorenz.poincare_map \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e) \<and>
           norm (D dx) \<ge> expansion res * norm dx \<and>
           (\<exists>res2 \<in> return_of_res results res.
              (lorenz.poincare_map \<Sigma> x, D dx) \<in> c1_of_res res2 \<and>
              norm (D dx) \<ge> preexpansion res2 * norm dx))))))"

lemma check_line_nres_c0_correct:
  "check_line_nres pf m0 n0 c1 res \<le> SPEC (\<lambda>(every, Pe, RET). every \<longrightarrow>
    (\<forall>x \<in> sourcei_of_res res. lorenz.poincare_map \<Sigma> x \<in> \<Union>(source_of_res ` return_of_res results res)))"
  if NF
  apply (rule check_line_nres[OF \<open>NF\<close>, le])
  apply (auto simp: c1i_of_res_def lorenz.poincare_mapsto_def)
  subgoal
    apply (drule bspec, force)
    apply (auto dest!: spec[where x="1\<^sub>L"])
    apply (drule bspec, force)
    apply (force simp: scaleR2_def image_def vimage_def)
    done
  subgoal premises prems for a b c d e tans
  proof -
    obtain t where
      "((c, d, e), t) \<in> tans  - \<Gamma>\<^sub>i (invoke_nf res) \<times> UNIV"
      "((c, d, e), tangent_of_deg (min_deg res)) = (\<lambda>(x, y). (x, blinfun_apply y (1, 0, 0))) ((c, d, e), t)"
      using prems
      by (auto simp: sourcei_of_res_def)
    with prems(6)[rule_format, of "((c, d, e), t)"] prems(3)
    obtain D x where "tangent_of_deg (min_deg res) = blinfun_apply t (1, 0, 0)"
      "(c, d, e) returns_to \<Sigma>"
      "fst ` (tans - \<Gamma>\<^sub>i (invoke_nf res) \<times> UNIV) \<subseteq> \<Sigma>\<^sub>l\<^sub>e"
      "lorenz.return_time \<Sigma> differentiable at (c, d, e) within \<Sigma>\<^sub>l\<^sub>e"
      "(lorenz.poincare_map \<Sigma> has_derivative blinfun_apply D) (at (c, d, e) within \<Sigma>\<^sub>l\<^sub>e)"
      "x \<in> b" "(lorenz.poincare_map \<Sigma> (c, d, e), D o\<^sub>L t) \<in> x"
      by auto
    with prems
    show ?thesis
      subgoal
        apply (auto dest!: bspec[OF _ \<open>x \<in> b\<close>])
        apply (auto simp: scaleR2_def image_def vimage_def)
        apply (auto simp: subset_iff)
        by fastforce \<comment>\<open>slow\<close>
      done
  qed
  subgoal for a b c d e f
    apply (drule bspec[where A="sourcei_of_res res"]) apply force
    apply (auto dest!: spec[where x="1\<^sub>L"])
    apply (drule bspec, force)
    apply auto
    apply (auto simp: scaleR2_def image_def vimage_def)
    apply (auto simp: subset_iff)
    by fastforce\<comment> \<open>slow\<close>
  done

lemma cone_conefield[intro, simp]: "cone (conefield a b)"
  unfolding conefield_alt_def
  by (rule cone_cone_hull)

lemma in_segment_norm_bound: "c \<in> {a -- b} \<Longrightarrow> norm c \<le> max (norm a) (norm b)"
  apply (auto simp: in_segment max_def intro!: norm_triangle_le)
   apply (auto simp: algebra_simps intro: add_mono mult_left_mono
      mult_right_mono)
  using affine_ineq by blast

lemma norm_tangent_of_deg[simp]: "norm (tangent_of_deg d) = 1"
  by (auto simp: tangent_of_deg_def norm_prod_def)

lemma check_line_nres_c1_correct:
  "check_line_nres pf m0 n0 True res \<le> SPEC (\<lambda>(correct, Pe, RET). correct \<longrightarrow> correct_res res)"
  if NF
proof (rule check_line_nres[OF \<open>NF\<close>, le], clarsimp, goal_cases)
  case P: (1 a P tans)
  let ?tans = "{tangent_of_deg (min_deg res)--tangent_of_deg (max_deg res)}"
  have tans_plane: "?tans \<subseteq> UNIV \<times> UNIV \<times> {0}"
    by (auto simp: in_segment tangent_of_deg_def)
  from P have *: "x \<in> plane_of (Sctn (0, 0, 1) 27)" if "x \<in> sourcei_of_res res" for x
    using that
    by (auto simp: that sourcei_of_res_def)
  from tans_plane P have **: "dx \<in> plane_of (Sctn (0, 0, 1) 0)"
    if "x \<in> sourcei_of_res res" "dx \<in> conefield_of_res res" for x dx
  proof -
    from tans_plane that obtain c dx' dy' where
      c: "dx = c *\<^sub>R (dx', dy', 0)" "(dx', dy', 0) \<in> ?tans" "c \<ge> 0"
      unfolding conefield_of_res_def conefield_alt_def cone_hull_expl
      by auto
    then show ?thesis by (auto simp: plane_of_def)
  qed
  show ?case
    unfolding correct_res_def
  proof (intro ballI conjI, clarsimp_all simp add:
      * ** c1i_of_res_def c1_of_res_def sourcei_of_res_def, goal_cases)
    case source: (1 x y z dx dy dz)
    from tans_plane source obtain c dx' dy' where
      c: "(dx, dy, dz) = c *\<^sub>R (dx', dy', 0)" "(dx', dy', 0) \<in> ?tans" "c \<ge> 0"
      unfolding conefield_of_res_def conefield_alt_def cone_hull_expl
      by auto
    from c source P
    obtain t where tans: "((x, y, z), t) \<in> tans" "blinfun_apply t (1, 0, 0) = (dx', dy', 0)"
      by auto 
    from P(3) tans(1) source(3) obtain Re D where Re:
      "(x, y, z) returns_to \<Sigma>" "fst ` (tans - \<Gamma>\<^sub>i (invoke_nf res) \<times> UNIV) \<subseteq> \<Sigma>\<^sub>l\<^sub>e"
      "lorenz.return_time \<Sigma> differentiable at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e"
      "(lorenz.poincare_map \<Sigma> has_derivative blinfun_apply D) (at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e)"
      "Re \<in> P" "(lorenz.poincare_map \<Sigma> (x, y, z), D o\<^sub>L t) \<in> Re"
      by (auto simp: lorenz.poincare_mapsto_def dest!: bspec)
    from P(5)[rule_format, OF \<open>Re \<in> P\<close>]
    obtain R em eM Rivls
      where R: "Re = scaleR2 em eM R"
        "em > 0"
        "fst ` R \<subseteq> \<Union>Rivls"
        "\<And>Rivl. Rivl\<in>Rivls \<Longrightarrow>
          \<exists>resa\<in>return_of_res results res. Rivl \<subseteq> source_of_res resa \<and> c1_entry_correct em R res resa"
      by auto
    have "lorenz.poincare_map \<Sigma> (x, y, z) \<in> fst ` R"
      and s2: "(lorenz.poincare_map \<Sigma> (x, y, z), D o\<^sub>L t) \<in> scaleR2 em eM R"
      using Re R by (auto simp: scaleR2_def)
    then obtain Rivl res' where Rivl:
      "lorenz.poincare_map \<Sigma> (x, y, z) \<in> Rivl" "Rivl \<in> Rivls"
      "res' \<in> return_of_res results res" "Rivl \<subseteq> source_of_res res'"
      and c1: "c1_entry_correct em R res res'"
      using R
      by force
    from s2 obtain ed Dt where Dt:
      "em \<le> ereal ed" "ereal ed \<le> eM" "D o\<^sub>L t = ed *\<^sub>R Dt"
      "(lorenz.poincare_map \<Sigma> (x, y, z), Dt) \<in> R"
      by (force simp: scaleR2_def)
    then have Dt_simp[simp]: "Dt = inverse ed *\<^sub>R (D o\<^sub>L t)"
      using \<open>0 < em\<close>
      by (cases em) (auto simp: intro!:  simp: blinfun.bilinear_simps inverse_eq_divide)
    from c1[unfolded c1_entry_correct_def, rule_format, OF Dt(4)]
    obtain dxr dyr where dxrdyr: "blinfun_apply D (dx', dy', 0) /\<^sub>R ed = (dxr, dyr, 0)"
      "ereal (preexpansion res') \<le> em * ereal (norm (dxr, dyr, 0::real))"
      "ereal (expansion res) \<le> em * ereal (norm (dxr, dyr, 0::real))"
      "-90 < min_deg res'" "min_deg res' \<le> max_deg res'"
      "tan (rad_of (min_deg res')) \<le> (dyr / dxr)"
      "(dyr / dxr) \<le> tan (rad_of (max_deg res'))"
      "max_deg res' < 90"
      "0 < dxr"
      by (auto simp: blinfun.bilinear_simps tans)

    then obtain emr where emr: "em = ereal emr" "0 < emr" "emr \<le> ed"
      "(preexpansion res') \<le> emr * (norm (dxr, dyr, 0::real))"
      "(expansion res) \<le> emr * (norm (dxr, dyr, 0::real))"
      using \<open>0 < em\<close> Dt
      by (cases em) (auto simp: simp: blinfun.bilinear_simps divide_simps prod_eq_iff)
    from dxrdyr have Ddx'dy': "D (dx', dy', 0) = ed *\<^sub>R (dxr, dyr, 0)"
      using \<open>0 < em\<close> Dt
      by (cases em) (auto simp: simp: blinfun.bilinear_simps divide_simps prod_eq_iff)

    note \<open>(x, y, z) returns_to \<Sigma>\<close>
    moreover note \<open>lorenz.return_time \<Sigma> differentiable at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e\<close>
    moreover note \<open>(lorenz.poincare_map \<Sigma> has_derivative D) (at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e)\<close>
    moreover note \<open>res' \<in> return_of_res results res\<close>
    moreover have "lorenz.poincare_map \<Sigma> (x, y, z) \<in> source_of_res res'"
      using Rivl by force
    moreover
    have \<open>0 \<le> ed\<close> using Dt \<open>0 < em\<close> by (cases em) auto
    have \<open>D (dx, dy, dz) \<in> conefield_of_res res'\<close>
      unfolding c blinfun.bilinear_simps conefield_of_res_def Ddx'dy'
      apply (intro mem_cone, simp_all add: \<open>0 \<le> ed\<close> \<open>0 \<le> c\<close> tangent_of_deg_def)
      apply (rule conefield_prod3I)
      unfolding fun_cong[OF tan_def, symmetric]
      subgoal by fact
      subgoal using dxrdyr
        apply (intro cos_gt_zero_pi)
        unfolding rad_of_lt_iff rad_of_gt_iff
        by (auto simp: deg_of_def)
      subgoal using dxrdyr
        apply (intro cos_gt_zero_pi)
        unfolding rad_of_lt_iff rad_of_gt_iff
        by (auto simp: deg_of_def)
      subgoal by fact
      subgoal by fact
      done
    moreover
    have norms_le: "emr * norm (dx', dy', 0::real) * (\<bar>c\<bar> * norm (dxr, dyr, 0::real)) \<le> \<bar>ed\<bar> * (\<bar>c\<bar> * norm (dxr, dyr, 0::real))"
    proof -
      from c(2)[THEN in_segment_norm_bound] have "norm (dx', dy', 0::real) \<le> 1"
        by auto
      also have "\<dots> \<le> ed / emr"
        using dxrdyr emr
        unfolding Ddx'dy'
        by auto
      finally show ?thesis
        using emr
        by (intro mult_right_mono) (auto simp: divide_simps ac_simps)
    qed
    then have "expansion res * norm (dx, dy, dz) \<le> norm (D (dx, dy, dz))"
      unfolding c blinfun.bilinear_simps conefield_of_res_def Ddx'dy' norm_scaleR
      apply -
      apply (rule order_trans)
       apply (rule mult_right_mono)
        apply (rule emr)
      by (auto simp: ac_simps)
    moreover have "preexpansion res' * norm (dx, dy, dz) \<le> norm (D (dx, dy, dz))"
      using norms_le
      unfolding c blinfun.bilinear_simps conefield_of_res_def Ddx'dy' norm_scaleR
      apply -
      apply (rule order_trans)
       apply (rule mult_right_mono)
        apply (rule emr)
      by (auto simp: ac_simps)
    ultimately
    show ?case
      by blast
  qed
qed

lemma conefield_ne_empyt[simp]: "conefield a b \<noteq> {}"
  by (auto simp: conefield_def conesegment_def cone_hull_empty_iff[symmetric])

lemma in_return_of_resD: "res' \<in> return_of_res results res \<Longrightarrow> res' \<in> set results"
  by (auto simp: return_of_res_def get_results_def)
lemma finite_results_at[intro, simp]: "finite (results_at x)"
  by (auto simp: results_at_def)


lemma lorenz_bounds_lemma:
  "x returns_to \<Sigma>"
  "R x \<in> N"
  "(R has_derivative DR x) (at x within \<Sigma>\<^sub>l\<^sub>e)"
  "\<And>c. c \<in> \<CC> x \<Longrightarrow> DR x c \<in> \<CC> (R x)"
  "\<And>c. c \<in> \<CC> x \<Longrightarrow> norm (DR x c) \<ge> \<E> x      * norm c"
  "\<And>c. c \<in> \<CC> x \<Longrightarrow> norm (DR x c) \<ge> \<E>\<^sub>p (R x) * norm c"
  if "x \<in> N - \<Gamma>" NF "\<And>res. res \<in> set results \<Longrightarrow> correct_res res"
proof -
  from \<open>x \<in> N - \<Gamma>\<close> obtain res where res: "res \<in> set results" "x \<in> sourcei_of_res res"
    by (auto simp: N_def sourcei_of_res_def \<Gamma>\<^sub>i_def)
  then have ne: "c1i_of_res res \<noteq> {}"
    by (auto simp: c1i_of_res_def conefield_of_res_def)
  from res this obtain dx where dx: "(x, dx) \<in> c1i_of_res res"
    by (auto simp: c1i_of_res_def)
  from that(3)[OF \<open>res \<in> set _\<close>] have "correct_res res" by simp
  from this[unfolded correct_res_def, rule_format, OF dx] res
  obtain res' D where res': "x returns_to \<Sigma>"
    "lorenz.return_time \<Sigma> differentiable at x within \<Sigma>\<^sub>l\<^sub>e"
    "(lorenz.poincare_map \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    "expansion res * norm dx \<le> norm (D dx)"
    "res' \<in> return_of_res results res"
    "(lorenz.poincare_map \<Sigma> x, D dx) \<in> c1_of_res res'"
    "preexpansion res' * norm dx \<le> norm (D dx)"
    by auto
  show "x returns_to \<Sigma>" by fact
  show "R x \<in> N" using res'
    by (auto simp: R_def N_def N_def c1i_of_res_def c1_of_res_def in_return_of_resD
        sourcei_of_res_def)
  show "(R has_derivative DR x) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    apply (auto simp: R_def DR_def N_def c1_of_res_def in_return_of_resD)
    apply (subst frechet_derivative_works[symmetric])
    apply (rule differentiableI)
    by fact
next
  fix dx assume "dx \<in> \<CC> x"
  then obtain res where res: "res \<in> set results" and dx: "(x, dx) \<in> c1_of_res res"
    by (auto simp: \<CC>_def results_at_def c1_of_res_def )
  then have dx: "(x, dx) \<in> c1i_of_res res"
    using \<open>x \<in> N - _\<close>
    by (auto simp: c1i_of_res_def sourcei_of_res_def c1_of_res_def \<Gamma>\<^sub>i_def)
  from res dx have ne: "c1i_of_res res \<noteq> {}"
    by (auto simp: c1_of_res_def conefield_of_res_def)
  from that(3)[OF \<open>res \<in> set _\<close>] have "correct_res res" by simp
  from that this[unfolded correct_res_def, rule_format, OF dx] res
  obtain res' D where res': "x returns_to \<Sigma>" "x \<in> plane_of (Sctn (0, 0, 1) 27)"
    "lorenz.return_time \<Sigma> differentiable at x within \<Sigma>\<^sub>l\<^sub>e"
    "(lorenz.poincare_map \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    "expansion res * norm dx \<le> norm (D dx)"
    "res' \<in> return_of_res results res"
    "(lorenz.poincare_map \<Sigma> x, D dx) \<in> c1_of_res res'"
    "preexpansion res' * norm dx \<le> norm (D dx)"
    by auto
  have DRD: "DR x = D"
    unfolding DR_def
    apply (rule frechet_derivative_unique_within)
      apply (subst frechet_derivative_works[symmetric])
      apply (rule differentiableI)
      apply fact
     apply fact using \<open>x \<in> plane_of _\<close>
    apply safe
    subgoal for _ _ _ e
      by (auto simp: \<Sigma>\<^sub>l\<^sub>e_def Basis_prod_def prod_eq_iff plane_of_def prod_eq_iff
          inner_prod_def intro!: exI[where x="-e/2"])
    done
  have [intro, simp]: "res' \<in> results_at (lorenz.poincare_map \<Sigma> x)"
    using res'
    by (auto simp: c1_of_res_def results_at_def in_return_of_resD R_def
        intro!: exI[where x=res'])
  have [intro, simp]: "res \<in> results_at x"
    using res dx
    by (auto simp: c1i_of_res_def results_at_def sourcei_of_res_def)
  show "DR x dx \<in> \<CC> (R x)"
    unfolding DRD \<CC>_def
    using res'
    by (auto simp: c1_of_res_def R_def)
  have "\<E> x * norm dx \<le> expansion res * norm dx"
    by (rule mult_right_mono) (auto simp: \<E>_def)
  also have "\<dots> \<le> norm (DR x dx)" unfolding DRD by fact
  finally show "\<E> x * norm dx \<le> norm (DR x dx)" .

  have "\<E>\<^sub>p (R x) * norm dx \<le> preexpansion res' * norm dx"
    by (rule mult_right_mono) (auto simp: \<E>\<^sub>p_def R_def)
  also have "\<dots> \<le> norm (DR x dx)" unfolding DRD by fact
  finally show "\<E>\<^sub>p (R x) * norm dx \<le> norm (DR x dx)" .
qed


lemma check_line_core_correct:
  "check_line_core pf m0 n0 True i \<le> SPEC (\<lambda>correct. correct \<longrightarrow> correct_res (results ! i))"
  if [refine_vcg]: NF
  unfolding check_line_core_def
  supply [refine_vcg] = check_line_nres_c1_correct[le]
  by refine_vcg


text \<open>The symmetric reduction\<close>

lemma source_of_res_mirror: "(x, y, z) \<in> source_of_res (mirror_result res) \<longleftrightarrow>
    (-x, -y, z) \<in> source_of_res res"
  by (cases res)
     (auto simp: source_of_res_def ivl_of_res_def ivl_of_resultrect_def set_of_ivl_def)

lemma conefield_of_res_mirror[simp]: "(x, y, z) \<in> conefield_of_res (mirror_result res) \<longleftrightarrow>
    (x, y, z) \<in> conefield_of_res res"
  by (cases res) (auto simp: conefield_of_res_def ivl_of_res_def)

lemma c1_of_res_mirror: "((x, y, z), dx, dy, dz) \<in> c1_of_res (mirror_result res) \<longleftrightarrow>
  ((-x, -y, z), dx, dy, dz) \<in> c1_of_res res"
  by (auto simp: c1_of_res_def source_of_res_mirror)

lemmas [simp] = lorenz_S(2)
lemma lorenz_S_idem[simp]: "lorenz_S (lorenz_S x) = (x::R3)"
  by (auto simp: lorenz_S_def split_beta')
lemma lorenz_S_exivl[simp]:
  "lorenz.existence_ivl0 (lorenz_S X) = lorenz.existence_ivl0 X"
  using lorenz_S(1)[of _ X]
  using lorenz_S(1)[of _ "lorenz_S X"]
  by auto
lemma lorenz_S_zero[simp]: "lorenz_S x = 0 \<longleftrightarrow> (x::R3) = 0"
  by (auto simp: lorenz_S_def split_beta' prod_eq_iff)
lemma lorenz_S_returns_toI[simp]:
  "x returns_to (lorenz_S ` P) \<Longrightarrow> lorenz_S x returns_to P"
  apply (auto simp: lorenz.returns_to_def)
  subgoal premises prems for t
  proof -
    have " \<forall>\<^sub>F s in at_right 0. s < t"
      using tendsto_ident_at \<open>0 < t\<close>
      by (rule order_tendstoD)
    then have " \<forall>\<^sub>F s in at_right 0. s \<in> lorenz.existence_ivl0 x"
      unfolding eventually_at_filter
      apply eventually_elim
      using \<open>0 < t\<close> lorenz.closed_segment_subset_existence_ivl[OF prems(3)]
      by (auto simp: closed_segment_eq_real_ivl subset_iff)
    then show ?thesis using prems(1)
      by eventually_elim force
  qed
  done

lemma lorenz_S_returns_to[simp]:
  "lorenz_S x returns_to P \<longleftrightarrow> x returns_to (lorenz_S ` P)"
  using lorenz_S_returns_toI[of P x] lorenz_S_returns_toI[of "lorenz_S ` P" "lorenz_S x"]
  by (auto simp: image_image)
lemma lorenz_S_image_Sigma[simp]: "lorenz_S ` \<Sigma> = \<Sigma>"
  apply (auto simp: \<Sigma>_def lorenz_S_def)
  apply (rule image_eqI)
   apply (rule lorenz_S_idem[symmetric])
  apply (auto simp: \<Sigma>_def lorenz_S_def)
  done

lemma linear_lorenz_S: "linear lorenz_S"
  by unfold_locales (auto simp: lorenz_S_def)
lemma inj_lorenz_S: "inj_on (lorenz_S::R3 \<Rightarrow> _) G"
  by (rule inj_onI) (auto simp: lorenz_S_def prod_eq_iff)

lemma lorenz_S_return_time:
  "lorenz.return_time P (lorenz_S x) = lorenz.return_time (lorenz_S ` P) x"
  if "x returns_to (lorenz_S ` P)" "closed P"
proof -
  from lorenz.returns_toE[OF that(1)] obtain t0 t1
    where f: "0 < t0" "t0 \<le> t1" " t1 \<in> lorenz.existence_ivl0 x"
      "lorenz.flow0 x t1 \<in> lorenz_S ` P"
      "\<And>t. 0 < t \<Longrightarrow> t < t0 \<Longrightarrow> lorenz.flow0 x t \<notin> lorenz_S ` P"
    by auto
  have [simp]: "lorenz.return_time (lorenz_S ` P) x \<in> lorenz.existence_ivl0 x"
    by (auto intro!: that closed_injective_linear_image linear_lorenz_S
        lorenz.return_time_exivl
        inj_lorenz_S)
  have c': "closed (lorenz_S ` P)"
    by (auto intro!: that closed_injective_linear_image linear_lorenz_S
        lorenz.return_time_exivl lorenz.return_time_pos
        inj_lorenz_S)
  show ?thesis
    using f(1-4)
    using lorenz.return_time_returns[OF that(1) c']
    apply (intro lorenz.return_time_eqI)
       apply (auto intro!: that closed_injective_linear_image linear_lorenz_S
        lorenz.return_time_exivl lorenz.return_time_pos c'
        inj_lorenz_S)
    subgoal premises prems for a b c d e f g
    proof -
      have [simp]: "a \<in> lorenz.existence_ivl0 x"
        using _ that(1)
        apply (rule lorenz.less_return_time_imp_exivl)
        using prems that(2) c'
        by auto
      have "lorenz.return_time (lorenz_S ` P) x \<le> a"
        apply (rule lorenz.return_time_le)
        using prems
           apply (auto intro!: that closed_injective_linear_image linear_lorenz_S
            lorenz.return_time_exivl lorenz.return_time_pos c'
            inj_lorenz_S)
        apply (rule image_eqI)
         apply (rule lorenz_S_idem[symmetric])
        by auto
      then show ?thesis using prems
        by simp
    qed
    done
qed

lemma lorenz_S_poincare_map:
  "lorenz.poincare_map P (lorenz_S x) = lorenz_S (lorenz.poincare_map (lorenz_S ` P) x)"
  if "x returns_to (lorenz_S ` P)" "closed P"
  using that
  unfolding lorenz.poincare_map_def
  apply (auto simp: lorenz_S_return_time)
  apply (subst lorenz_S)
   by (auto intro!: lorenz.return_time_exivl that
      closed_injective_linear_image linear_lorenz_S inj_lorenz_S)

lemma [continuous_intros]: "isCont (lorenz_S::_\<Rightarrow>R3) x"
  "continuous_on (G::R3 set) lorenz_S"
  by (auto simp:lorenz_S_def[abs_def] split_beta' continuous_intros)

lemma filtermap_lorenz_S_le: "filtermap lorenz_S (at x within lorenz_S ` P) \<le>(at (lorenz_S x::R3) within P)"\<comment> \<open>TODO: generalize!\<close>
  unfolding at_within_def
  apply (auto simp: intro!: antisym filtermap_inf[le] filtermap_inf[ge])
    apply (rule inf.coboundedI1)
    apply (subst filtermap_nhds_open_map)
    apply (auto simp: intro!: invariance_of_domain inj_lorenz_S continuous_intros)
   apply (rule inf.coboundedI2)
   apply (auto simp: image_image )
  apply (auto simp: lorenz_S_def split_beta')[]
  done

lemma filtermap_lorenz_S_eq: "filtermap lorenz_S (at (x::R3) within lorenz_S ` P) = (at (lorenz_S x::R3) within P)"
  apply (rule antisym)
  using filtermap_lorenz_S_le[of "x" P]
   apply simp
  subgoal
  proof -
    have "filtermap lorenz_S (at (lorenz_S x) within P) \<le>
    filtermap lorenz_S (filtermap lorenz_S  (at x within lorenz_S ` P))"
      using filtermap_lorenz_S_le[of "lorenz_S x" "lorenz_S ` P"]
      by (auto simp: image_image filtermap_filtermap)
    then show ?thesis
      apply (subst (asm) filtermap_mono_strong)
      by (auto simp: inj_lorenz_S)
  qed
  done

lemma norm_lorenz_S[simp]: "norm (lorenz_S x) = norm x"
  by (auto simp: lorenz_S_def norm_prod_def split_beta')

lemma bl_lorenz_S: "bounded_linear (lorenz_S)"
  by unfold_locales (auto simp: lorenz_S_def norm_prod_def intro!: exI[where x=1])

lemma filtermap_lorenz_S_eq_bot[simp]:
  "filtermap (lorenz_S::R3\<Rightarrow>_) F = bot \<longleftrightarrow> F = bot"
  apply (auto simp: )
  apply (subst (asm) filtermap_bot[symmetric])
  apply (subst (asm) filtermap_eq_strong)
  by (auto simp: inj_lorenz_S)

lemma netlimit_filtermap[simp]:
  "at x within X \<noteq> bot \<Longrightarrow> netlimit (filtermap lorenz_S (at x within X)) = lorenz_S (x::R3)"
  apply (rule tendsto_Lim)
  unfolding filterlim_filtermap
   apply simp
  by (auto intro!: tendsto_eq_intros simp: split_beta' lorenz_S_def[abs_def])

lemma lorenz_S_halfspace [simp]: "lorenz_S ` \<Sigma>\<^sub>l\<^sub>e = \<Sigma>\<^sub>l\<^sub>e"
  apply (auto simp: \<Sigma>\<^sub>l\<^sub>e_def lorenz_S_def[abs_def])
  apply (rule image_eqI)
   apply auto
   apply (rule sym)
   apply (rule minus_minus)
  apply (rule minus_minus[symmetric])
  done

lemma closure_Sigma_le_eq: "closure \<Sigma>\<^sub>l\<^sub>e = \<Sigma>\<^sub>l\<^sub>e"
proof (rule closure_closed)
  have "\<Sigma>\<^sub>l\<^sub>e = {x. x \<bullet> (0, 0, 1) \<le> 27}"
    by (auto simp: \<Sigma>\<^sub>l\<^sub>e_def )
  also have "closed \<dots>"
    by (rule closed_halfspace_component_le)
  finally show "closed \<Sigma>\<^sub>l\<^sub>e" .
qed

lemma closure_Sigma_le[simp]: "closure (\<Sigma>\<^sub>l\<^sub>e - {x}) = \<Sigma>\<^sub>l\<^sub>e"
proof (cases "x \<in> \<Sigma>\<^sub>l\<^sub>e")
  case that: True
  have "closure \<Sigma>\<^sub>l\<^sub>e \<subseteq> closure (insert x (\<Sigma>\<^sub>l\<^sub>e - {x}))" by (rule closure_mono) auto
  also have "\<dots> = insert x (closure (\<Sigma>\<^sub>l\<^sub>e - {x}))"
    apply (subst closure_insert) by simp
  also
  have "x \<in> closure (\<Sigma>\<^sub>l\<^sub>e - {x})"
    apply (rule closed_sequentially[where f="\<lambda>n. x - (0, 0, inverse (Suc n))"])
      apply (rule closed_closure)
    subgoal
      apply (auto simp: ) apply (rule subsetD) apply (rule closure_subset)
      using that
      apply (auto simp: \<Sigma>\<^sub>l\<^sub>e_def prod_eq_iff)
      apply (rule order_trans)
       apply (rule diff_right_mono)
       apply (assumption)
      apply simp
      done
    subgoal
      apply (rule tendsto_eq_intros)
        apply (rule tendsto_intros)
        apply (rule tendsto_intros)
        apply (rule tendsto_intros)
        apply (rule tendsto_intros)
        apply (rule tendsto_intros)
      apply (rule LIMSEQ_inverse_real_of_nat)
      by (auto simp: prod_eq_iff)
    done
  then have "insert x (closure (\<Sigma>\<^sub>l\<^sub>e - {x})) \<subseteq> closure (\<Sigma>\<^sub>l\<^sub>e - {x})"
    by auto
  finally have "closure \<Sigma>\<^sub>l\<^sub>e \<subseteq> closure (\<Sigma>\<^sub>l\<^sub>e - {x})" .
  moreover
  have "closure (\<Sigma>\<^sub>l\<^sub>e - {x}) \<subseteq> closure (\<Sigma>\<^sub>l\<^sub>e)"
    by (rule closure_mono) auto
  ultimately have "closure (\<Sigma>\<^sub>l\<^sub>e - {x}) = closure (\<Sigma>\<^sub>l\<^sub>e)"
    by simp
  also have "\<dots> = \<Sigma>\<^sub>l\<^sub>e"
    by (rule closure_Sigma_le_eq)
  finally show ?thesis .
next
  case False
  then show ?thesis
    apply simp
    apply (rule closure_Sigma_le_eq)
    done
qed

lemma lorenz_S_return_time_has_derivative:
  assumes "(lorenz.return_time \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e)"
        "lorenz.returns_to \<Sigma> x" "x \<in> \<Sigma>\<^sub>l\<^sub>e"
  shows "(lorenz.return_time \<Sigma> has_derivative D o lorenz_S) (at (lorenz_S x) within \<Sigma>\<^sub>l\<^sub>e)"
proof -
  have [simp]: "\<not>trivial_limit (at x within \<Sigma>\<^sub>l\<^sub>e)"
    unfolding at_within_eq_bot_iff
    using assms
    by simp
  have evret: "\<forall>\<^sub>F x in at x within \<Sigma>\<^sub>l\<^sub>e. (x::R3) returns_to \<Sigma>"
    apply (rule lorenz.eventually_returns_to_continuousI[of \<Sigma> x \<Sigma>\<^sub>l\<^sub>e])
    apply fact
     apply (rule closed_\<Sigma>)
    apply (rule has_derivative_continuous)
    apply fact
    done
  interpret bounded_linear "lorenz_S::R3\<Rightarrow>_" by (rule bl_lorenz_S)
  show ?thesis
    using assms
    apply (subst filtermap_lorenz_S_eq[symmetric])
    apply (auto simp: has_derivative_def filterlim_filtermap)
    unfolding o_def
     apply (rule bounded_linear_compose, assumption, rule bl_lorenz_S)
    unfolding diff lorenz_S_idem
     apply (auto simp: Lim_ident_at)
    apply (rule Lim_transform_eventually) defer apply assumption
    subgoal premises prems
      using evret
      apply (eventually_elim)
      by (auto simp: lorenz_S_return_time assms diff[symmetric])
    done
qed

lemma lorenz_S_return_time_differentiable:
  "lorenz.return_time \<Sigma> differentiable at (lorenz_S x) within \<Sigma>\<^sub>l\<^sub>e"
  if "lorenz.return_time \<Sigma> differentiable at x within \<Sigma>\<^sub>l\<^sub>e"
    "lorenz.returns_to \<Sigma> x" "x \<in> \<Sigma>\<^sub>l\<^sub>e"
proof -
  from that obtain D where "(lorenz.return_time \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    by (auto simp: differentiable_def)
  then have "(lorenz.return_time \<Sigma> has_derivative D o lorenz_S) (at (lorenz_S x) within \<Sigma>\<^sub>l\<^sub>e)"
    by (rule lorenz_S_return_time_has_derivative) fact+
  then show ?thesis
    by (auto simp: differentiable_def)
qed

lemma lorenz_S_has_derivative:
  "(lorenz_S has_derivative lorenz_S) (at (x::R3) within X)"
  by (auto simp: lorenz_S_def[abs_def] split_beta' intro!: derivative_eq_intros)

lemma lorenz_S_poincare_map_has_derivative:
  assumes "(lorenz.poincare_map \<Sigma> has_derivative D) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    "(lorenz.return_time \<Sigma> has_derivative Dr) (at x within \<Sigma>\<^sub>l\<^sub>e)"
    "lorenz.returns_to \<Sigma> x" "x \<in> \<Sigma>\<^sub>l\<^sub>e"
  shows "(lorenz.poincare_map \<Sigma> has_derivative lorenz_S o D o lorenz_S) (at (lorenz_S x) within \<Sigma>\<^sub>l\<^sub>e)"
proof -
  have [simp]: "\<not>trivial_limit (at x within \<Sigma>\<^sub>l\<^sub>e)"
    unfolding at_within_eq_bot_iff
    using assms
    by simp
  have evret: "\<forall>\<^sub>F x in at x within \<Sigma>\<^sub>l\<^sub>e. (x::R3) returns_to \<Sigma>"
    apply (rule lorenz.eventually_returns_to_continuousI[of \<Sigma> x \<Sigma>\<^sub>l\<^sub>e])
    apply fact
     apply (rule closed_\<Sigma>)
    apply (rule has_derivative_continuous)
    apply fact
    done
  interpret bounded_linear "lorenz_S::R3\<Rightarrow>_" by (rule bl_lorenz_S)
  show ?thesis
    using has_derivative_compose[OF assms(1) lorenz_S_has_derivative] assms
    apply (subst filtermap_lorenz_S_eq[symmetric])
    apply (auto simp: has_derivative_def filterlim_filtermap)
    unfolding o_def
     apply (rule bounded_linear_compose, rule bl_lorenz_S)
     apply (rule bounded_linear_compose, assumption, rule bl_lorenz_S)
    unfolding diff lorenz_S_idem
     apply (auto simp: Lim_ident_at)
    apply (rule Lim_transform_eventually) defer apply assumption
    subgoal premises prems
      using evret
      apply (eventually_elim)
      apply (auto simp: lorenz_S_return_time lorenz_S_poincare_map assms diff[symmetric])
      done
    done
qed

lemma [simp]: "expansion (mirror_result res) = expansion res"
  by (cases res) auto

lemma lorenz_S_on_plane: "lorenz_S (dx, dy, 0::real) = - (dx, dy, 0)"
  by (auto simp: lorenz_S_def )

lemma mirror_result_idem[simp]: "mirror_result (mirror_result x) = x"
  by (cases x) (auto simp: mirror_result_def)

lemma mirror_in_set: "x \<in> set results \<Longrightarrow> mirror_result x \<in> set results"
  by (auto simp: results_def symmetrize_def)

lemma mirror_result_in:
  "mirror_result res2 \<in> return_of_res results (mirror_result res)"
  if "res2 \<in> return_of_res results res"
proof -
  from that have "res2 \<in> set results" by (rule in_return_of_resD)
  from mirror_in_set[OF this] have "mirror_result res2 \<in> set results" .
  then show ?thesis
    apply (cases res2; cases res)
    using that
    by (auto simp: return_of_res_def get_results_def)
qed

lemma in_source_of_res_mirrorI:
  "(x::R3) \<in> source_of_res (mirror_result (r))" if "lorenz_S x \<in> source_of_res r"
  using that
  apply (cases r; cases x)
  by (auto simp: source_of_res_def set_of_ivl_def ivl_of_res_def lorenz_S_def
      less_eq_prod_def ivl_of_resultrect_def)

lemma conefield_of_res_mirror_simp[simp]: "conefield_of_res (mirror_result res2) = conefield_of_res res2"
  by (cases res2) (auto simp: conefield_of_res_def)

lemma lorenz_minus_planeI: "lorenz_S (- x) = x" if "snd (snd (x::R3)) = 0"
  using that
  by (auto simp: lorenz_S_def split_beta' prod_eq_iff)

lemma preexpansion_mirror_result[simp]: "preexpansion (mirror_result res2) = preexpansion res2"
  by (cases res2) (auto simp: )

lemma lorenz_S_tendsto_0I: "(lorenz.flow0 (lorenz_S x) \<longlongrightarrow> 0) at_top"
  if "{0..} \<subseteq> lorenz.existence_ivl0 x"
    "(lorenz.flow0 x \<longlongrightarrow> 0) at_top"
proof -
  have "\<forall>\<^sub>F s in at_top. (s::real) \<ge> 0"
    using eventually_ge_at_top by blast
  then have "\<forall>\<^sub>F s in at_top. lorenz_S (lorenz.flow0 x s) = lorenz.flow0 (lorenz_S x) s"
    by eventually_elim (use that in auto)
  moreover have "((\<lambda>s. lorenz_S (lorenz.flow0 x s)) \<longlongrightarrow> 0) at_top"
    unfolding Zfun_def[symmetric]
      by (rule bounded_linear.tendsto_zero[OF bl_lorenz_S that(2)])
  ultimately show "(lorenz.flow0 (lorenz_S x) \<longlongrightarrow> 0) at_top"
    by (rule Lim_transform_eventually)
qed

lemma lorenz_S_tendsto_0_iff:
  "(lorenz.flow0 (lorenz_S x) \<longlongrightarrow> 0) at_top \<longleftrightarrow> (lorenz.flow0 x \<longlongrightarrow> 0) at_top"
  if "{0..} \<subseteq> lorenz.existence_ivl0 x"
  using lorenz_S_tendsto_0I[of x, OF that] lorenz_S_tendsto_0I[of "lorenz_S x"] that
  by auto

lemma lorenz_S_eq_iff[simp]: "lorenz_S y = lorenz_S x \<longleftrightarrow> y = x" for x y::"real*real*real"
  by (auto simp: lorenz_S_def split: prod.splits)

lemma lorenz_S_\<Gamma>: "lorenz_S x \<in> \<Gamma> \<longleftrightarrow> x \<in> \<Gamma>"
  apply (auto simp: \<Gamma>_def lorenz_S_tendsto_0_iff )
  subgoal for t
    apply (auto simp: dest!: spec[where x=t])
    apply (subst (asm) lorenz_S) apply auto
    apply (subst (asm) (2) lorenz_S_image_Sigma[symmetric])
    by (simp del: lorenz_S_image_Sigma)
  subgoal for t
    apply (auto simp: dest!: spec[where x=t])
    apply (subst (asm) lorenz_S) apply auto
    apply (subst (asm) lorenz_S_image_Sigma[symmetric])
    apply (auto simp del: lorenz_S_image_Sigma)
    done
  done

lemma sourcei_of_res_mirror: "(x, y, z) \<in> sourcei_of_res (mirror_result res) \<longleftrightarrow>
    (-x, -y, z) \<in> sourcei_of_res res"
  using lorenz_S_\<Gamma>[of "(x, y, z)"]
  by (cases res)
     (auto simp: source_of_res_def sourcei_of_res_def ivl_of_res_def ivl_of_resultrect_def
       set_of_ivl_def \<Gamma>\<^sub>i_def lorenz_S_def)

lemma c1i_of_res_mirror: "((x, y, z), dx, dy, dz) \<in> c1i_of_res (mirror_result res) \<longleftrightarrow>
  ((-x, -y, z), dx, dy, dz) \<in> c1i_of_res res"
  by (auto simp: c1i_of_res_def sourcei_of_res_mirror)

lemma correct_res_mirror_result:
  "correct_res (mirror_result res)" if "correct_res res"
  unfolding correct_res_def
proof (clarsimp simp add: c1i_of_res_mirror, goal_cases)
  case (1 x y z dx dy dz)
  then have 1: "(lorenz_S (x, y, z), dx, dy, dz) \<in> c1i_of_res res"
    by (auto simp: lorenz_S_def)
  from that[unfolded correct_res_def, rule_format, OF 1, simplified]
  have "(lorenz_S (x, y, z)) \<in> plane_of (Sctn (0, 0, 1) 27)"
    "(dx, dy, dz) \<in> plane_of (Sctn (0, 0, 1) 0)"
    by auto
  then have plane: "(x, y, z) \<in> plane_of (Sctn (0, 0, 1) 27)"
    "(dx, dy, dz) \<in> plane_of (Sctn (0, 0, 1) 0)"
    by (auto simp: plane_of_def lorenz_S_def)
  then show ?case
  proof (clarsimp, goal_cases)
    case mem: 1
    with that[unfolded correct_res_def, rule_format, OF 1, simplified]
    obtain D res2 where D:
      "lorenz_S (x, y, z) returns_to \<Sigma>"
      "lorenz.return_time \<Sigma> differentiable at (lorenz_S (x, y, z)) within \<Sigma>\<^sub>l\<^sub>e"
      "(lorenz.poincare_map \<Sigma> has_derivative D) (at (lorenz_S (x, y, z)) within \<Sigma>\<^sub>l\<^sub>e)"
      "expansion res * norm (dx, dy, dz) \<le> norm (D (dx, dy, dz))"
      "res2 \<in> return_of_res results res"
      "(lorenz.poincare_map \<Sigma> (lorenz_S (x, y, z)), D (dx, dy, dz)) \<in> c1_of_res res2"
      "preexpansion res2 * norm (dx, dy, dz) \<le> norm (D (dx, dy, dz))"
      by auto
    from plane have S_le: "lorenz_S (x, y, z) \<in> \<Sigma>\<^sub>l\<^sub>e"
      by (auto simp: \<Sigma>\<^sub>l\<^sub>e_def plane_of_def lorenz_S_def)
    interpret linear D by (rule has_derivative_linear; fact)

    have ret: "(x, y, z) returns_to \<Sigma>" using D(1) lorenz_S_returns_to by simp
    moreover have "lorenz.return_time \<Sigma> differentiable at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e"
      using lorenz_S_return_time_differentiable[OF D(2) D(1) S_le] by auto
    moreover from D obtain Dr where Dr: "(lorenz.return_time \<Sigma> has_derivative Dr) (at (lorenz_S (x, y, z)) within \<Sigma>\<^sub>l\<^sub>e)"
      by (auto simp: differentiable_def)
    let ?D = "lorenz_S \<circ> D \<circ> lorenz_S"
    have "(lorenz.poincare_map \<Sigma> has_derivative ?D) (at (x, y, z) within \<Sigma>\<^sub>l\<^sub>e)"
      using lorenz_S_poincare_map_has_derivative[OF D(3) Dr D(1) S_le]
      by auto
    moreover
    from plane have [simp]: "dz = 0" by (auto simp: plane_of_def)
    have "expansion (mirror_result res) * norm (dx, dy, dz) \<le> norm (?D (dx, dy, dz))"
      using D(4) apply (auto simp: )
      unfolding lorenz_S_on_plane neg
      by simp
    moreover have \<open>mirror_result res2 \<in> return_of_res results (mirror_result res)\<close>
      using D(5) by (rule mirror_result_in)
    moreover have "(lorenz.poincare_map \<Sigma> (x, y, z), ?D (dx, dy, dz)) \<in> c1_of_res (mirror_result res2)"
      using D(6) apply (subst (asm) lorenz_S_poincare_map)
        apply auto apply fact
      apply (auto simp: c1_of_res_def in_source_of_res_mirrorI)
      unfolding lorenz_S_on_plane neg
      apply (subst lorenz_minus_planeI)
       apply (auto simp: conefield_of_res_def conefield_alt_def cone_hull_expl
          in_segment tangent_of_deg_def)
      done
    moreover have "preexpansion (mirror_result res2) * norm (dx, dy, dz) \<le> norm (?D (dx, dy, dz))"
      using D(7) apply (auto simp: )
      unfolding lorenz_S_on_plane neg
      by simp
    ultimately show ?case
      by (force intro!: exI[where x = ?D] bexI[where x="mirror_result res2"])
  qed
qed

lemma reduce_lorenz_symmetry: "Ball (set results) correct_res"
  if "Ball (set coarse_results) correct_res"
  using that
  by (auto simp: results_def symmetrize_def intro!: correct_res_mirror_result)

end

subsection \<open>Code Generation\<close>

definition [code_abbrev]: "my_divide_integer (i::integer) (j::integer) = i div j"
code_printing constant my_divide_integer \<rightharpoonup> (SML) "IntInf.div/ (_,/ _)"

subsection \<open>Tuning code equations\<close>

definition mult_twopow_int::"int \<Rightarrow> int \<Rightarrow> int" where "mult_twopow_int x n = x * (power_int 2 n)"
definition div_twopow_int :: "int \<Rightarrow> int \<Rightarrow> int" where "div_twopow_int x n = x div (power_int 2 n)"

context includes integer.lifting begin

lift_definition mult_twopow_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is mult_twopow_int .
lift_definition div_twopow_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is div_twopow_int .

end

lemma compute_float_round_down[code]:
  "float_round_down prec (Float m e) =
    (let d = bitlen \<bar>m\<bar> - int prec - 1 in
      if 0 < d then Float (div_twopow_int m d) (e + d)
      else Float m e)"
  including float.lifting
  using Float.compute_float_down[of "Suc prec - bitlen \<bar>m\<bar> - e" m e, symmetric]
  by transfer
     (auto simp add: field_simps abs_mult log_mult bitlen_alt_def truncate_down_def
      div_twopow_int_def power_int_def
      cong del: if_weak_cong)

lemma compute_float_plus_down[code]:
  fixes p::nat and m1 e1 m2 e2::int
  shows "float_plus_down p (Float m1 e1) (Float m2 e2) =
    (if m1 = 0 then float_round_down p (Float m2 e2)
    else if m2 = 0 then float_round_down p (Float m1 e1)
    else
      (if e1 \<ge> e2 then
        (let k1 = Suc p - nat (bitlen \<bar>m1\<bar>) in
          if bitlen \<bar>m2\<bar> > e1 - e2 - k1 - 2
          then float_round_down p ((Float m1 e1) + (Float m2 e2))
          else float_round_down p (Float (mult_twopow_int m1 (int k1 + 2) + sgn m2) (e1 - int k1 - 2)))
    else float_plus_down p (Float m2 e2) (Float m1 e1)))"
  using Float.compute_float_plus_down[of p m1 e1 m2 e2]
  by (auto simp: mult_twopow_int_def Let_def power_int_def nat_add_distrib)

subsection \<open>Codegen\<close>

definition "is_dRETURN_True x = (case x of dRETURN b \<Rightarrow> b | _ \<Rightarrow> False)"
definition "file_output_option s f =
  (case s of None \<Rightarrow> f None
  | Some s \<Rightarrow> file_output (String.implode s) (\<lambda>pf. f (Some pf)))"

definition "check_line_lookup_out s m0 n0 c1 i =
  is_dRETURN_True (file_output_option s (\<lambda>pf. check_line_core_impl pf m0 n0 c1 i))"

fun alternating where "alternating [] xs = xs"
  | "alternating xs [] = xs"
  | "alternating (x#xs) (y#ys) = x#y#alternating xs ys"

definition "ordered_lines = alternating (rev [0..<222]) ([222..<400])"
  \<comment> \<open>the hard ones ``first'', potentially useless due to nondeterministic \<open>Parallel.map\<close>\<close>

definition "parallel_check filenameo m n c1 ns =
  Parallel.forall (\<lambda>i.
    let
      _ = print (String.implode (''# Starting '' @ show i @ ''\<newline>''));
      b =
      check_line_lookup_out (map_option (\<lambda>f. f @ show i) filenameo)
        (Some m) (Some n) c1 i;
      _ = if b
        then print (String.implode (''# Success: '' @ show i @ ''\<newline>''))
        else print (String.implode (''# Failed:  '' @ show i @ ''\<newline>''))
    in b
    ) ns"

ML \<open>val check_line = @{computation_check
  terms:
    Trueprop
    parallel_check
    ordered_lines
    check_line_core_impl
    check_line_lookup_out

    (* bool *)
    True False

    (* num *)
    Num.One Num.Bit0 Num.Bit1

    (* nat *)
    Suc "0::nat" "1::nat" "numeral::num\<Rightarrow>nat"

    (* int / integer*)
    "numeral::num\<Rightarrow>int"
    "numeral::num\<Rightarrow>integer"
    "uminus::_\<Rightarrow>int"
    "uminus::_\<Rightarrow>integer"
    int_of_integer integer_of_int
    "0::int"
    "1::int"

    (* Pairs *)
    "Pair::_ \<Rightarrow> _\<Rightarrow> (real list \<times> real list)"
    "Pair::_\<Rightarrow>_\<Rightarrow>(real list \<times> real list) \<times> real list sctn"
    "Pair::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list \<times> real aform reach_options"

    (* Option *)
    "None::nat option"
    "Some::_\<Rightarrow>nat option"
    "None::string option"
    "Some::_\<Rightarrow>string option"

    (* Lists *)
    "Nil::real list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real list"
    "Nil::nat list"
    "Cons::_\<Rightarrow>_\<Rightarrow>nat list"
    "Nil::real aform list"
    "Cons::_\<Rightarrow>_\<Rightarrow>real aform list"
    "Nil::((real list \<times> real list) \<times> real list sctn) list"
    "Cons::_\<Rightarrow>_\<Rightarrow>((real list \<times> real list) \<times> real list sctn) list"
    "Nil::(((real list \<times> real list) \<times> real list sctn) list \<times> real aform reach_options)list"
    "Cons::_\<Rightarrow>_\<Rightarrow>(((real list \<times> real list) \<times> real list sctn) list \<times> real aform  reach_options)list"

    (* String *)
    String.Char
    String.implode "Cons::char \<Rightarrow> char list \<Rightarrow> char list" "Nil::char list"

    (* float *)
    Float float_of_int float_of_nat

    (* real *)
    "numeral::num\<Rightarrow>real" "real_of_float" "(/)::real\<Rightarrow>real\<Rightarrow>real" "uminus::real\<Rightarrow>_"
    real_divl real_divr
    real_of_int

    (* section *)
    "Sctn::_\<Rightarrow>_\<Rightarrow>real list sctn"

    (* aform *)
    "aforms_of_ivls::_\<Rightarrow>_\<Rightarrow>real aform list"

    (* input *)
    coarse_results

    (* modes *)
    xsec xsec' ysec ysec' zsec zsec' zbucket
    lookup_mode
    ro
    ro_outer
    mode_outer

    (* unit *)
    "()"

  }\<close>


lemma is_dRETURN_True_iff[simp]: "is_dRETURN_True x \<longleftrightarrow> (x = dRETURN True)"
  by (auto simp: is_dRETURN_True_def split: dres.splits)

lemma check_line_core_impl_True:
  "check_line_core_impl pfo m n True i = dRETURN True \<Longrightarrow> NF \<Longrightarrow> correct_res (results ! i)"
  apply (cases "check_line_core_impl pfo m n True i")
  using check_line_core_correct[of pfo m n i]
    check_line_core_impl.refine[of pfo pfo True True i i m m n n]
    apply (auto simp: nres_rel_def)
  apply (drule order_trans[where y="check_line_core pfo m n True i"])
   apply assumption
  by auto

lemma check_line_lookup_out: "correct_res (results ! i)"
  if "\<exists>s m n. check_line_lookup_out s m n True i" NF
  using that
  by (auto simp: check_line_lookup_out_def file_output_iff check_line_core_impl_True
      file_output_option_def split: dres.splits option.splits)

definition "check_lines c1 ns = list_all (\<lambda>i. \<exists>s m n. check_line_lookup_out s m n c1 i) ns"

lemma check_linesI:
  "check_lines c1 ns"
  if "parallel_check s m n c1 ns"
  using that
  by (auto simp: parallel_check_def check_lines_def list_all_iff)

subsection \<open>Automate generation of lemmas\<close>

lemma length_coarse_results[simp]: "length coarse_results = 400"
  by (simp add: coarse_results_def)

lemma correct_res_coarse_resultsI:
  "correct_res (results ! i) \<Longrightarrow> i < 400 \<Longrightarrow> correct_res (coarse_results ! i)"
  by (auto simp: results_def symmetrize_def nth_append)

lemma Ball_coarseI: "Ball (set coarse_results) correct_res"
  if NF "check_lines True xs" "set xs = {..<400}"
  using that
  by (force simp: check_lines_def list_all_iff in_set_conv_nth
      intro!: correct_res_coarse_resultsI check_line_lookup_out)

ML \<open>map_option (using_master_directory_term @{context}) (SOME "a")\<close>
ML \<open>
fun mk_optionT ty = Type (@{type_name "option"}, [ty])
fun mk_None ty = Const (@{const_name "None"}, mk_optionT ty)
fun mk_Some ty x = Const (@{const_name "Some"}, ty --> mk_optionT ty) $ x
fun mk_option ty _ NONE = mk_None ty
  | mk_option ty f (SOME x) = mk_Some ty (f x)
fun check_lines_tac' s m n ctxt =
  resolve_tac ctxt
    [Thm.instantiate ([],
      [("s", @{typ "string option"}, mk_option @{typ string} (using_master_directory_term ctxt) s),
       ("m", @{typ nat}, HOLogic.mk_nat m),
       ("n", @{typ nat}, HOLogic.mk_nat n)]
        |> map (fn (s, ty, t) => (((s, 0), ty), Thm.cterm_of ctxt t)))
      @{thm check_linesI}]
  THEN' CONVERSION (check_line ctxt)
  THEN' resolve_tac ctxt @{thms TrueI}
\<close>

method_setup parallel_check = \<open>
  Scan.lift (Parse.maybe Parse.string) -- Scan.lift Parse.nat -- Scan.lift Parse.nat
  >> (fn ((s, m), n) => fn ctxt => SIMPLE_METHOD' (check_lines_tac' s m n ctxt))
\<close>

lemma lorenz_bounds_lemma_asym:
  "\<forall>x \<in> N - \<Gamma>. x returns_to \<Sigma>"
  "R ` (N - \<Gamma>) \<subseteq> N"
  "\<forall>x \<in> N - \<Gamma>. (R has_derivative DR x) (at x within \<Sigma>\<^sub>l\<^sub>e)"
  "\<forall>x \<in> N - \<Gamma>. DR x ` \<CC> x \<subseteq> \<CC> (R x)"
  "\<forall>x \<in> N - \<Gamma>. \<forall>c \<in> \<CC> x. norm (DR x c) \<ge> \<E> x      * norm c"
  "\<forall>x \<in> N - \<Gamma>. \<forall>c \<in> \<CC> x. norm (DR x c) \<ge> \<E>\<^sub>p (R x) * norm c"
  if NF "Ball (set results) correct_res"
  using that
  by (auto intro!: lorenz_bounds_lemma)

end
