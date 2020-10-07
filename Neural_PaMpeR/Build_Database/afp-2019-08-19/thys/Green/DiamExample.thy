section \<open>The Diamond Example\<close>

theory DiamExample
  imports Green SymmetricR2Shapes
begin

lemma abs_if':
  fixes a :: "'a :: {abs_if,ordered_ab_group_add}"
  shows "\<bar>a\<bar> = (if a \<le> 0 then - a else a)"
  by (simp add: abs_if dual_order.order_iff_strict)

locale diamond = R2 +
  fixes d::real
  assumes d_gt_0: "0 < d"
begin

definition diamond_y_gen :: "real \<Rightarrow> real" where
  "diamond_y_gen \<equiv>\<lambda>t.  1/2 - \<bar>t\<bar>"

definition diamond_cube_gen:: "((real * real) \<Rightarrow> (real * real))" where
  "diamond_cube_gen \<equiv> (\<lambda>(x,y). (d * x_coord x, (2 * y - 1) * (d * diamond_y_gen (x_coord x))))"

lemma diamond_y_gen_valid:
  assumes "a \<le> 0" "0 \<le> b"
  shows "diamond_y_gen piecewise_C1_differentiable_on {a..b}"
  unfolding piecewise_C1_differentiable_on_def diamond_y_gen_def
proof (intro conjI exI)
  show "continuous_on {a..b} (\<lambda>t. 1 / 2 - \<bar>t\<bar>)"
    by (intro continuous_intros)
  show "finite{0}"
    by simp
  show "(\<lambda>t. 1 / 2 - \<bar>t\<bar>) C1_differentiable_on {a..b} - {0}"
    by (intro derivative_intros) auto
qed

lemma diamond_cube_gen_boundary_valid:
  assumes "(k,\<gamma>)\<in>boundary (diamond_cube_gen)"
  shows "valid_path \<gamma>"
  using assms
proof (auto simp add: valid_path_def boundary_def horizontal_boundary_def vertical_boundary_def diamond_cube_gen_def)
  have rw2: "(\<lambda>x. diamond_y_gen (x_coord x)) = diamond_y_gen o x_coord" by auto
  note [derivative_intros] = C1_differentiable_on_pair pair_prod_smooth_pw_smooth scale_piecewise_C1_differentiable_on piecewise_C1_differentiable_neg piecewise_C1_differentiable_compose diamond_y_gen_valid
  show "(\<lambda>x. (d * x_coord x, - (d * diamond_y_gen (x_coord x)))) piecewise_C1_differentiable_on {0..1}"
    apply(auto intro!: derivative_intros)+
     apply (auto simp add: x_coord_smooth rw2)
    by(auto intro!: derivative_intros simp add: x_coord_img x_coord_back_img C1_differentiable_imp_piecewise[OF x_coord_smooth])+
  show "(\<lambda>x. (d * x_coord x, d * diamond_y_gen (x_coord x))) piecewise_C1_differentiable_on {0..1}"
    apply(auto intro!: derivative_intros)+
     apply (auto simp add: x_coord_smooth rw2)
    by(auto intro!: derivative_intros simp add: x_coord_img x_coord_back_img C1_differentiable_imp_piecewise[OF x_coord_smooth])+
qed

definition diamond_x where
  "diamond_x \<equiv> \<lambda>t. (t - 1/2) * d"

definition diamond_y where
  "diamond_y \<equiv> \<lambda>t. d/2 - \<bar>t\<bar>"

definition diamond_cube where
  "diamond_cube = (\<lambda>(x,y). (diamond_x x, (2 * y - 1) * (diamond_y (diamond_x x))))"

definition rot_diamond_cube where
  "rot_diamond_cube = prod.swap o (diamond_cube) o prod.swap"

lemma diamond_eq_characterisations:
  shows "diamond_cube (x,y)= diamond_cube_gen (x,y)"
  by(auto simp add: diamond_cube_def diamond_cube_gen_def diamond_x_def x_coord_def diamond_y_def diamond_y_gen_def d_gt_0 field_simps mult_le_0_iff abs_if split: if_split_asm)

lemma diamond_eq_characterisations_fun: "diamond_cube = diamond_cube_gen"
  using diamond_eq_characterisations by auto

lemma diamond_y_valid:
  shows "diamond_y piecewise_C1_differentiable_on {-d/2..d/2}"         (is ?P)
        "(\<lambda>x. diamond_y x) piecewise_C1_differentiable_on {-d/2..d/2}" (is ?Q)
proof -
  have f0: "finite {0}"
    by simp
  show ?P ?Q
    unfolding piecewise_C1_differentiable_on_def diamond_y_def
    by (fastforce intro!: f0 continuous_intros derivative_intros)+
qed

lemma diamond_cube_boundary_valid:
  assumes "(k,\<gamma>) \<in> boundary (diamond_cube)"
  shows "valid_path \<gamma>"
  using diamond_cube_gen_boundary_valid assms d_gt_0
  by(simp add: diamond_eq_characterisations_fun)

lemma diamond_cube_is_type_I:
  shows "typeI_twoCube (diamond_cube)"
  unfolding typeI_twoCube_def
proof (intro exI conjI ballI)
  show "-d/2 < d/2"
    using d_gt_0 by auto
  show "\<And>x. x \<in> {- d / 2..d / 2} \<Longrightarrow> - diamond_y x \<le> diamond_y x"
    using diamond_y_def by auto
  have f0: "finite {0}"
    by simp
  show "diamond_y piecewise_C1_differentiable_on {- d / 2..d / 2}"
       "(\<lambda>x. - diamond_y x) piecewise_C1_differentiable_on {- d / 2..d / 2}"
    unfolding diamond_y_def piecewise_C1_differentiable_on_def
    by (rule conjI exI f0 continuous_intros derivative_intros | force)+
  show "diamond_cube =
    (\<lambda>(x, y). ((1 - x) * (- d / 2) + x * (d / 2),
         (1 - y) * - diamond_y ((1 - x) * (- d / 2) + x * (d / 2)) +
         y * diamond_y ((1 - x) * (- d / 2) + x * (d / 2))))"
    by (auto simp: diamond_cube_def diamond_x_def diamond_y_def divide_simps algebra_simps)
qed

lemma diamond_cube_valid_two_cube:
  shows "valid_two_cube (diamond_cube)"
  apply (auto simp add: valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def diamond_cube_def 
      diamond_x_def card_insert_if)
   apply (metis (no_types, hide_lams) cancel_comm_monoid_add_class.diff_cancel d_gt_0 mult.commute mult_2 mult_zero_right order_less_irrefl prod.inject field_sum_of_halves)
  apply (metis (no_types, hide_lams) add_diff_cancel_right' d_gt_0 mult_cancel_left mult_zero_right order_less_irrefl prod.inject)
  done

lemma rot_diamond_cube_boundary_valid:
  assumes "(k,\<gamma>)\<in>boundary (rot_diamond_cube)"
  shows "valid_path \<gamma>"
  using d_gt_0 swap_valid_boundaries diamond_cube_boundary_valid
  using assms diamond_cube_is_type_I rot_diamond_cube_def by fastforce

lemma rot_diamond_cube_is_type_II:
  shows "typeII_twoCube (rot_diamond_cube)"
  using d_gt_0 swap_typeI_is_typeII diamond_cube_is_type_I
  by (auto simp add: rot_diamond_cube_def)

lemma rot_diamond_cube_valid_two_cube: "valid_two_cube (rot_diamond_cube)"
  using valid_cube_valid_swap diamond_cube_valid_two_cube d_gt_0 rot_diamond_cube_def
  by force

definition diamond_top_edges where
  "diamond_top_edges = (- 1::int, \<lambda>x. (diamond_x x, diamond_y (diamond_x x)))"

definition diamond_bot_edges where
  "diamond_bot_edges = (1::int,  \<lambda>x. (diamond_x x, - diamond_y (diamond_x x)))"

lemma diamond_cube_boundary_explicit:
    "boundary (diamond_cube ) =
           {diamond_top_edges,
           diamond_bot_edges,
    (- 1::int, \<lambda>y. (diamond_x 0, (2 * y - 1) * diamond_y (diamond_x 0))),
     (1::int, \<lambda>y. (diamond_x 1, (2 * y - 1) * diamond_y (diamond_x 1)))}"
  by (auto simp only: diamond_top_edges_def diamond_bot_edges_def valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def diamond_cube_def Un_iff algebra_simps)

definition diamond_top_left_edge where
  "diamond_top_left_edge = (- 1::int, (\<lambda>x. (diamond_x (1/2 * x),  (diamond_x (1/2 * x)) + d/2)))"

definition diamond_top_right_edge where
  "diamond_top_right_edge = (- 1::int, (\<lambda>x. (diamond_x (1/2 * x + 1/2),  (-(diamond_x (1/2 * x + 1/2)) + d/2))))"

definition diamond_bot_left_edge where
  "diamond_bot_left_edge = (1::int, (\<lambda>x. (diamond_x (1/2 * x), - (diamond_x (1/2 * x) + d/2))))"

definition diamond_bot_right_edge where
  "diamond_bot_right_edge = (1::int, (\<lambda>x. (diamond_x (1/2 * x + 1/2), - (-(diamond_x (1/2 * x + 1/2)) + d/2))))"

lemma diamond_edges_are_valid:
   "valid_path (snd (diamond_top_left_edge))"
    "valid_path (snd (diamond_top_right_edge))"
    "valid_path (snd (diamond_bot_left_edge))"
    "valid_path (snd (diamond_bot_right_edge))"
  by (auto simp add: valid_path_def diamond_top_left_edge_def diamond_bot_right_edge_def diamond_bot_left_edge_def diamond_top_right_edge_def diamond_x_def)

definition diamond_cube_boundary_to_subdiv where
  "diamond_cube_boundary_to_subdiv (gamma::(int \<times> (real \<Rightarrow> real \<times> real))) \<equiv>
 if (gamma = diamond_top_edges) then
       {diamond_top_left_edge, diamond_top_right_edge}
 else if (gamma = diamond_bot_edges) then
   {diamond_bot_left_edge, diamond_bot_right_edge}
 else {}"

lemma rot_diam_edge_1:
     "(1::int, \<lambda>x::real. ((x::real) * (2 * diamond_y (diamond_x 0)) - 1 * diamond_y (diamond_x 0), diamond_x 0)) =
      (1, \<lambda>x. (x * (2 * diamond_y (diamond_x 0)) -  (diamond_y (diamond_x 0)), diamond_x 0))"
  by (auto simp add: algebra_simps)

definition diamond_left_edges where
  "diamond_left_edges = (- 1, \<lambda>y. (- diamond_y (diamond_x y), diamond_x y))"

definition diamond_right_edges where
  "diamond_right_edges = (1, \<lambda>y. ( diamond_y (diamond_x y), diamond_x y))"

lemma rot_diamond_cube_boundary_explicit:
     "boundary (rot_diamond_cube) = {(1::int, \<lambda>x::real. ((2 * x - 1) * diamond_y (diamond_x 0), diamond_x 0)),
                                     (- 1, \<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 1), diamond_x 1)),
                                     diamond_left_edges, diamond_right_edges}"
proof -
  have "boundary (rot_diamond_cube) = { (1::int, \<lambda>x::real. ((2 * x - 1) * diamond_y (diamond_x 0), diamond_x 0)),
              (- 1, \<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 1), diamond_x 1)),
              (- 1, \<lambda>y. ((2 * 0 - 1) * diamond_y (diamond_x y), diamond_x y)),
              (1, \<lambda>y. ((2 * 1 - 1) * diamond_y (diamond_x y), diamond_x y))}"
    by (auto simp only: valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def rot_diamond_cube_def diamond_cube_def o_def swap_simp Un_iff)
  then show ?thesis
    by (auto simp add: diamond_left_edges_def diamond_right_edges_def)
qed

lemma rot_diamond_cube_vertical_boundary_explicit:
     "vertical_boundary (rot_diamond_cube) = {diamond_left_edges, diamond_right_edges}"
proof -
  have "vertical_boundary (rot_diamond_cube) = {(- 1::int, \<lambda>y. ((2 * 0 - 1) * diamond_y (diamond_x y), diamond_x y)),
                                                (1, \<lambda>y. ((2 * 1 - 1) * diamond_y (diamond_x y), diamond_x y))}"
    by (auto simp only: valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def rot_diamond_cube_def diamond_cube_def o_def swap_simp Un_iff)
  then show ?thesis
    by (auto simp add: diamond_left_edges_def diamond_right_edges_def)
qed

definition rot_diamond_cube_boundary_to_subdiv where
  "rot_diamond_cube_boundary_to_subdiv (gamma::(int \<times> (real \<Rightarrow> real \<times> real))) \<equiv>
     if (gamma = diamond_left_edges ) then {diamond_bot_left_edge , diamond_top_left_edge}
     else if (gamma = diamond_right_edges) then {diamond_bot_right_edge, diamond_top_right_edge}
     else {}"

definition diamond_boundaries_reparam_map where
  "diamond_boundaries_reparam_map \<equiv> id"

lemma diamond_boundaries_reparam_map_bij:
     "bij (diamond_boundaries_reparam_map)"
  by(auto simp add: bij_def full_SetCompr_eq[symmetric] diamond_boundaries_reparam_map_def)

lemma diamond_bot_edges_neq_diamond_top_edges:
     "diamond_bot_edges \<noteq>  diamond_top_edges"
  by(simp add: diamond_bot_edges_def diamond_top_edges_def)

lemma diamond_top_left_edge_neq_diamond_top_right_edge:
     "diamond_top_left_edge \<noteq> diamond_top_right_edge"
  apply (simp add: diamond_top_left_edge_def diamond_top_right_edge_def diamond_x_def diamond_y_def)
    using d_gt_0
    apply (auto simp add: algebra_simps divide_simps)
    by (metis (no_types, hide_lams) diff_zero div_0 divide_divide_eq_right order_less_irrefl prod.inject field_sum_of_halves)

lemma neqs1:
  shows "(\<lambda>x. (diamond_x x, diamond_y (diamond_x x))) \<noteq> (\<lambda>x. (diamond_x x, - diamond_y (diamond_x x)))"
  and "(\<lambda>y. (- diamond_y (diamond_x y), diamond_x y)) \<noteq> (\<lambda>y. (diamond_y (diamond_x y), diamond_x y))"
  and "(\<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2)) \<noteq> (\<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2))"
  and "(\<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2))) \<noteq> (\<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2))"
  and "(\<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2)) \<noteq> (\<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2))"
  and "(\<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2)) \<noteq> (\<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2)))"
  using d_gt_0 by (auto simp: diamond_x_def diamond_y_def dest: fun_cong [where x = "1/2"])

lemma neqs2:
  shows "(\<lambda>x. (diamond_x x, diamond_y (diamond_x x))) \<noteq> (\<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 1), diamond_x 1))"
  and "(\<lambda>x. (diamond_x x, - diamond_y (diamond_x x))) \<noteq> (\<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 0), diamond_x 0))"
  using d_gt_0 by (auto simp: diamond_x_def diamond_y_def dest: fun_cong [where x = "1"])

lemma diamond_cube_is_only_horizontal_div_of_rot:
  shows "only_horizontal_division (boundary (diamond_cube)) {rot_diamond_cube}"
  unfolding only_horizontal_division_def
proof (rule exI [of _ "{}"], simp, intro conjI ballI)
  show "finite (boundary diamond_cube)"
    by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  show "boundary_chain (boundary diamond_cube)"
    by (simp add: two_cube_boundary_is_boundary)
  show "\<And>x. x \<in> boundary diamond_cube \<Longrightarrow> case x of (k, x) \<Rightarrow> valid_path x"
    using diamond_cube_boundary_valid by blast
  let ?\<V> = "(boundary (diamond_cube))"
  have 0: "finite ?\<V>"
    by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  have 1: "boundary_chain ?\<V>" using two_cube_boundary_is_boundary by auto
  let ?subdiv = "{diamond_top_left_edge, diamond_top_right_edge, diamond_bot_left_edge, diamond_bot_right_edge}"
  let ?pi = "{(1::int, \<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 0), diamond_x 0)),
              (- 1, \<lambda>x. ((2 * x - 1) * diamond_y (diamond_x 1), diamond_x 1))}"
  let ?pj = "{(-1::int, \<lambda>y. (diamond_x 0, (2 * y - 1) * diamond_y (diamond_x 0))),
              (1, \<lambda>y. (diamond_x 1, (2 * y - 1) * diamond_y (diamond_x 1)))}"
  let ?f = "diamond_cube_boundary_to_subdiv"
  have 2: "common_sudiv_exists (two_chain_vertical_boundary {rot_diamond_cube}) ?\<V>"
    unfolding common_sudiv_exists_def
  proof (intro exI conjI)
    show "chain_subdiv_chain (boundary (diamond_cube) - ?pj) ?subdiv"
      unfolding chain_subdiv_chain_character
    proof (intro exI conjI)
      have 1: "(boundary (diamond_cube)) - ?pj = {diamond_top_edges, diamond_bot_edges}"
        apply (auto simp add: diamond_cube_boundary_explicit diamond_x_def diamond_top_edges_def diamond_bot_edges_def)
         apply (metis (no_types, hide_lams) abs_zero cancel_comm_monoid_add_class.diff_cancel diamond_x_def diamond_y_def diff_0 minus_diff_eq mult.commute mult_zero_right prod.inject neqs2)
        by (metis (no_types, hide_lams) cancel_comm_monoid_add_class.diff_cancel d_gt_0 divide_eq_0_iff linorder_not_le mult.commute mult_zero_right order_refl prod.sel(1) zero_neq_numeral)
      then show "\<Union> (?f ` (boundary (diamond_cube) - ?pj)) = ?subdiv"
        by (auto simp add: diamond_top_edges_def diamond_bot_edges_def diamond_cube_boundary_to_subdiv_def)
      have "chain_subdiv_path (reversepath (\<lambda>x. (diamond_x x, diamond_y (diamond_x x))))
                 {(- 1::int, \<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2)),
                  (- 1::int, \<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2)))}"
      proof -
        let ?F = "\<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2))"
        let ?G = "\<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2)"
        have dist: "distinct [(-1, ?F), (-1, ?G)]"
          using d_gt_0 by (auto simp: diamond_x_def diamond_y_def dest: fun_cong)
        have rj: "rec_join [(-1, ?F), (-1, ?G)] = reversepath (\<lambda>x. (diamond_x x, diamond_y (diamond_x x)))"
          using d_gt_0 by (auto simp add: subpath_def diamond_x_def diamond_y_def joinpaths_def reversepath_def algebra_simps divide_simps)
        have "pathstart ?F = pathfinish ?G"
          using d_gt_0 by(auto simp add: subpath_def diamond_x_def diamond_y_def pathfinish_def pathstart_def)
        then have val: "valid_chain_list [(-1, ?F), (-1, ?G)]"
          by (auto simp add:  join_subpaths_middle)
        show ?thesis
          using chain_subdiv_path.I [OF dist rj val]
          by (simp add: insert_commute)
      qed
      moreover have "chain_subdiv_path (\<lambda>x. (diamond_x x, - diamond_y (diamond_x x)))
                           {(1::int, \<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2)),
                            (1::int, \<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2))}"
      proof -
        let ?F = "\<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2)"
        let ?G = "\<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2)"
        have dist: "distinct [(1, ?F), (1, ?G)]"
          using d_gt_0 by (auto simp: diamond_x_def diamond_y_def dest: fun_cong)
        have rj: "rec_join [(1, ?F), (1, ?G)] = (\<lambda>x. (diamond_x x, - diamond_y (diamond_x x)))"
          using d_gt_0 by (auto simp add: subpath_def diamond_x_def diamond_y_def joinpaths_def algebra_simps divide_simps)
        have "pathfinish ?F = pathstart ?G"
          using d_gt_0 by(auto simp add: subpath_def diamond_x_def diamond_y_def pathfinish_def pathstart_def)
        then have val: "valid_chain_list [(1, ?F), (1, ?G)]"
          by (auto simp add:  join_subpaths_middle)
        show ?thesis
          using chain_subdiv_path.I [OF dist rj val] by simp
      qed
      ultimately show **:
        "\<forall>(k::int, \<gamma>)\<in>boundary (diamond_cube) - ?pj.
            if k = (1::int) then chain_subdiv_path \<gamma> (?f (k::int, \<gamma>))
            else chain_subdiv_path (reversepath \<gamma>) (?f (k::int, \<gamma>))"
        "\<forall>p\<in>boundary (diamond_cube) - ?pj. \<forall>p'\<in>boundary (diamond_cube) - ?pj.
                                      p \<noteq> p' \<longrightarrow> ?f p \<inter> ?f p' = {}"
        "\<forall>x\<in>boundary (diamond_cube) - ?pj. finite (?f x)"
        by(simp_all add: diamond_cube_boundary_to_subdiv_def UNION_eq 1 diamond_top_edges_def diamond_bot_edges_def diamond_bot_left_edge_def diamond_bot_right_edge_def diamond_top_left_edge_def diamond_top_right_edge_def neqs1)
    qed
    have *: "\<And>f. \<Union> (f ` {rot_diamond_cube}) = f (rot_diamond_cube)" by auto
    show "chain_subdiv_chain (two_chain_vertical_boundary {rot_diamond_cube} - ?pi) ?subdiv"
      unfolding chain_subdiv_chain_character two_chain_vertical_boundary_def *
    proof (intro exI conjI)
      let ?f = "rot_diamond_cube_boundary_to_subdiv"
      have 1: "(vertical_boundary (rot_diamond_cube) - ?pi) = {diamond_left_edges, diamond_right_edges}"
        apply (auto simp add: rot_diamond_cube_vertical_boundary_explicit  diamond_left_edges_def diamond_right_edges_def)
         apply (metis (no_types, hide_lams) add.inverse_inverse add_diff_cancel_right' diff_numeral_special(11) mult.left_neutral mult.right_neutral prod.inject neqs1(2) uminus_add_conv_diff)
        by (metis (no_types, hide_lams) diff_0 mult.left_neutral mult_minus_left mult_zero_right prod.inject neqs1(2))
      show "\<Union> (?f ` (vertical_boundary (rot_diamond_cube) - ?pi)) = ?subdiv"
        apply (simp add: rot_diamond_cube_boundary_to_subdiv_def 1 UNION_eq subpath_def)
        apply (auto simp add: set_eq_iff diamond_right_edges_def diamond_left_edges_def)
        done
      have "chain_subdiv_path (reversepath (\<lambda>y. (- diamond_y (diamond_x y), diamond_x y)))
                           {(1, \<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2)),
                            (-1, \<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2))}"
      proof -
        let ?F = "\<lambda>x. (diamond_x(x/2), - diamond_x(x/2) - d/2)"
        let ?G = "\<lambda>x. (diamond_x(x/2), diamond_x(x/2) + d/2)"
        have dist: "distinct [(-1, ?G), (1::int, ?F)]"
          using d_gt_0 by simp
        have rj: "rec_join [(-1, ?G), (1::int, ?F)] = reversepath (\<lambda>y. (- diamond_y (diamond_x y), diamond_x y))"
          using d_gt_0 by (auto simp add: subpath_def diamond_x_def diamond_y_def joinpaths_def reversepath_def algebra_simps divide_simps)
        have "pathstart ?G = pathstart ?F"
          using d_gt_0 by(auto simp add: subpath_def diamond_x_def diamond_y_def pathstart_def)
        then have val: "valid_chain_list [(-1, ?G), (1::int, ?F)]"
          by (auto simp add:  join_subpaths_middle)
        show ?thesis
          using chain_subdiv_path.I [OF dist rj val] by (simp add: insert_commute)
      qed
      moreover have "chain_subdiv_path (\<lambda>y. (diamond_y (diamond_x y), diamond_x y))
                           {(1, \<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2)),
                            (-1, \<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2)))}"
      proof -
        let ?F = "\<lambda>x. (diamond_x(x/2 + 1/2), d/2 - diamond_x(x/2 + 1/2))"
        let ?G = "\<lambda>x. (diamond_x(x/2 + 1/2), diamond_x(x/2 + 1/2) - d/2)"
        have dist: "distinct [(1::int, ?G), (-1, ?F)]"
          by simp
        have rj: "rec_join [(1::int, ?G), (-1, ?F)] = (\<lambda>y. (diamond_y (diamond_x y), diamond_x y))"
          using d_gt_0 by (auto simp add: subpath_def diamond_x_def diamond_y_def joinpaths_def reversepath_def algebra_simps divide_simps)
        have "pathfinish ?F = pathfinish ?G"
          using d_gt_0 by(auto simp add: subpath_def diamond_x_def diamond_y_def pathfinish_def pathstart_def)
        then have val: "valid_chain_list [(1::int, ?G), (-1, ?F)]"
          by (auto simp add:  join_subpaths_middle)
        show ?thesis
          using chain_subdiv_path.I [OF dist rj val] by simp
      qed
      ultimately show "\<forall>(k, \<gamma>)\<in>vertical_boundary (rot_diamond_cube) - ?pi.
                           if k = 1 then chain_subdiv_path \<gamma> (?f (k, \<gamma>))
                           else chain_subdiv_path (reversepath \<gamma>) (?f (k, \<gamma>))"
        "\<forall>p\<in>vertical_boundary (rot_diamond_cube) - ?pi.
                         \<forall>p'\<in>vertical_boundary (rot_diamond_cube) - ?pi.
                              p \<noteq> p' \<longrightarrow> ?f p \<inter> ?f p' = {}"
        "\<forall>x\<in>vertical_boundary (rot_diamond_cube) - ?pi. finite (?f x)"
        by(auto simp add: rot_diamond_cube_boundary_to_subdiv_def 1 diamond_left_edges_def 
            diamond_right_edges_def diamond_bot_left_edge_def diamond_bot_right_edge_def 
            diamond_top_left_edge_def diamond_top_right_edge_def neqs1)
    qed
    show "(\<forall>(k::int, \<gamma>)\<in>?subdiv. valid_path \<gamma>)"
      by (simp add: diamond_edges_are_valid prod.case_eq_if set_eq_iff)
    show "boundary_chain ?subdiv"
      by (auto simp add: boundary_chain_def diamond_top_left_edge_def diamond_top_right_edge_def diamond_bot_left_edge_def diamond_bot_right_edge_def)
    show "(\<forall>(k, \<gamma>)\<in>?pi. point_path \<gamma>)"
      using d_gt_0 by (auto simp add: point_path_def diamond_x_def diamond_y_def)
    show "(\<forall>(k, \<gamma>)\<in>?pj. point_path \<gamma>)"
      using d_gt_0 by (auto simp add: point_path_def diamond_x_def diamond_y_def)
  qed
  show "common_sudiv_exists (two_chain_vertical_boundary {rot_diamond_cube}) (boundary diamond_cube) \<or>
        common_reparam_exists (boundary diamond_cube) (two_chain_vertical_boundary {rot_diamond_cube})"
    using 0 1 2 diamond_cube_boundary_valid by auto
qed

abbreviation "rot_y t1 t2 \<equiv> (t1 - 1/2) / (2* diamond_y_gen (x_coord (rot_x t1 t2))) + 1/2"

lemma rot_y_ivl:
  assumes "(0::real) \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "0 \<le> rot_y x y \<and> rot_y x y \<le> 1"
  using assms
  apply(auto simp add: x_coord_def diamond_y_gen_def algebra_simps divide_simps linorder_class.not_le abs_if)
  using mult_nonneg_nonneg apply fastforce
  using dual_order.order_iff_strict apply fastforce
  apply (sos "(((((A<0 * A<1) * R<1) + (((A<=4 * (A<1 * R<1)) * (R<1/2 * [1]^2)) + (((A<=3 * (A<0 * R<1)) * (R<1/2 * [1]^2)) + ((A<=0 * (A<=2 * (A<=3 * R<1))) * (R<1 * [1]^2)))))) & ((((A<0 * A<1) * R<1) + (((A<=4 * (A<1 * R<1)) * (R<1/3 * [1]^2)) + (((A<=4 * (A<0 * R<1)) * (R<1/3 * [1]^2)) + ((A<=3 * (A<=4 * R<1)) * (R<1/3 * [1]^2)))))))")
  using assms(1) mult_left_le_one_le apply blast
  using affine_ineq apply fastforce+
  done

lemma diamond_gen_eq_rot_diamond:
  assumes"0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "(diamond_cube_gen (x, y)) = (rot_diamond_cube (rot_y x y, rot_x x y))"
proof
  show "snd (diamond_cube_gen (x, y)) = snd (rot_diamond_cube (rot_y x y, rot_x x y))"
    apply(simp only: rot_diamond_cube_def diamond_eq_characterisations_fun)
    by(auto simp add:  diamond_cube_gen_def x_coord_def diamond_y_gen_def algebra_simps divide_simps)
  show "fst (diamond_cube_gen (x, y)) = fst (rot_diamond_cube (rot_y x y, rot_x x y))"
    using assms
    apply(auto simp add: diamond_cube_gen_def rot_diamond_cube_def diamond_eq_characterisations_fun)
    apply(auto simp add: x_coord_def diamond_y_gen_def algebra_simps divide_simps abs_if split: if_split_asm)
    apply sos+
    done
qed

lemma rot_diamond_eq_diamond_gen:
  assumes "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "rot_diamond_cube (x, y) = diamond_cube_gen (rot_x y x, rot_y y x)"
proof
  show "fst (rot_diamond_cube (x, y)) = fst (diamond_cube_gen (rot_x y x, rot_y y x))"
    apply(simp only: rot_diamond_cube_def diamond_eq_characterisations_fun)
    by(auto simp add:  diamond_cube_gen_def x_coord_def diamond_y_gen_def algebra_simps divide_simps)
  show "snd (rot_diamond_cube (x, y)) = snd (diamond_cube_gen (rot_x y x, rot_y y x))"
    using assms
    apply(auto simp add: diamond_cube_gen_def rot_diamond_cube_def diamond_eq_characterisations_fun)
    apply(auto simp add: x_coord_def diamond_y_gen_def algebra_simps divide_simps abs_if split: if_split_asm)
    apply sos+
    done
qed

lemma rot_img_eq: "cubeImage (diamond_cube_gen) = cubeImage (rot_diamond_cube)"
proof(auto simp add: cubeImage_def image_def cbox_def real_pair_basis)
  show "\<exists>a\<ge>0. a \<le> 1 \<and> (\<exists>b\<ge>0. b \<le> 1 \<and> diamond_cube_gen (x, y) = rot_diamond_cube (a, b))"
    if "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" "(a, b) = diamond_cube_gen (x, y)"
    for a b x y
  proof (intro exI conjI)
    let ?a = "rot_y x y"
    let ?b = "rot_x x y"
    show "0 \<le> ?a" "?a \<le> 1"
      using rot_y_ivl that by blast+
    show "0 \<le> ?b" "?b \<le> 1"
      using rot_x_ivl that by blast+
    show "diamond_cube_gen (x, y) = rot_diamond_cube (?a, ?b)"
      using that d_gt_0 diamond_gen_eq_rot_diamond by auto
  qed
  show "\<exists>a\<ge>0. a \<le> 1 \<and> (\<exists>b\<ge>0. b \<le> 1 \<and> rot_diamond_cube (x, y) = diamond_cube_gen (a, b))"
    if "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" "(a, b) = rot_diamond_cube (x, y)" for a b x y
  proof (intro exI conjI)
    let ?a = "rot_x y x"
    let ?b = "rot_y y x"
    show "0 \<le> ?a" "?a \<le> 1"
      using rot_x_ivl that by blast+
    show "0 \<le> ?b" "?b \<le> 1"
      using rot_y_ivl that by blast+
    show "rot_diamond_cube (x, y) = diamond_cube_gen (?a, ?b)"
      using that d_gt_0 rot_diamond_eq_diamond_gen by auto
  qed
qed

lemma rot_diamond_gen_div_diamond_gen:
  shows "gen_division (cubeImage (diamond_cube_gen)) (cubeImage ` {rot_diamond_cube})"
  using rot_img_eq by(auto simp add: gen_division_def)

lemma rot_diamond_gen_div_diamond:
  shows "gen_division (cubeImage (diamond_cube)) (cubeImage ` {rot_diamond_cube})"
  using rot_diamond_gen_div_diamond_gen
  by(simp only: diamond_eq_characterisations_fun)

lemma GreenThm_diamond:
  assumes "analytically_valid (cubeImage (diamond_cube)) (\<lambda>x. F x \<bullet> i) j"
    "analytically_valid (cubeImage (diamond_cube)) (\<lambda>x. F x \<bullet> j) i"
  shows "integral (cubeImage (diamond_cube)) (\<lambda>x. partial_vector_derivative (\<lambda>x. F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. F x \<bullet> i) j x) =
         one_chain_line_integral F {i, j} (boundary (diamond_cube))"
proof -
  have 0: "\<forall>(k, \<gamma>)\<in>boundary (diamond_cube). valid_path \<gamma>" 
    using diamond_cube_boundary_valid d_gt_0 by auto
  have "\<And>twoCube. twoCube \<in> {diamond_cube} \<Longrightarrow> typeI_twoCube twoCube" 
    using assms diamond_cube_is_type_I by auto
  moreover have "valid_two_chain {diamond_cube}"
    using assms(1) diamond_cube_valid_two_cube valid_two_chain_def by auto
  moreover have "gen_division (cubeImage (diamond_cube)) (cubeImage ` {diamond_cube})"
    by (simp add: gen_division_def)
  moreover have "(\<forall>twoCube\<in>({rot_diamond_cube}). typeII_twoCube twoCube)" 
    using assms rot_diamond_cube_is_type_II by auto
  moreover have "valid_two_chain {rot_diamond_cube}"
      using assms(1) rot_diamond_cube_valid_two_cube valid_two_chain_def by auto
  moreover have "gen_division (cubeImage (diamond_cube)) (cubeImage ` {rot_diamond_cube})"
      using rot_diamond_gen_div_diamond by auto
  moreover have 3: "only_vertical_division (boundary (diamond_cube)) {diamond_cube}"
    using twoChainVertDiv_of_itself[of "{diamond_cube}"] diamond_cube_boundary_valid assms
    by(auto simp add: two_chain_boundary_def)                                      
  moreover have 4: "\<forall>twoC\<in>{diamond_cube}. analytically_valid (cubeImage twoC) (\<lambda>x. F x \<bullet> i) j"
    using assms 
    by fastforce
  moreover have 5: "\<forall>twoC\<in>{rot_diamond_cube}. analytically_valid (cubeImage twoC) (\<lambda>x. F x \<bullet> j) i"
    using assms diamond_eq_characterisations_fun rot_img_eq by auto
  ultimately show ?thesis 
    using green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_finite_holes[of "(cubeImage (diamond_cube))" i j F "{diamond_cube}" "{rot_diamond_cube}", OF _ 0 3 diamond_cube_is_only_horizontal_div_of_rot _]
      R2_axioms 
    by(auto simp add: green_typeI_typeII_chain_def green_typeI_chain_def green_typeII_chain_def green_typeI_chain_axioms_def green_typeII_chain_axioms_def)
qed
end
end
