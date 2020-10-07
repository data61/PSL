theory SymmetricR2Shapes
  imports Green
begin 

context R2
begin

lemma valid_path_valid_swap:
  assumes "valid_path (\<lambda>x::real. ((f x)::real, (g x)::real))"
  shows "valid_path (prod.swap o (\<lambda>x. (f x, g x)))"
  unfolding o_def valid_path_def piecewise_C1_differentiable_on_def swap_simp
proof (intro conjI)
  show "continuous_on {0..1} (\<lambda>x. (g x, f x))"
    using assms
    using continuous_on_Pair continuous_on_componentwise[where f = "(\<lambda>x. (f x, g x))"]
    by (auto simp add: real_pair_basis valid_path_def piecewise_C1_differentiable_on_def)
  show "\<exists>S. finite S \<and> (\<lambda>x. (g x, f x)) C1_differentiable_on {0..1} - S"
  proof -
    obtain S where "finite S" and S: "(\<lambda>x. (f x, g x)) C1_differentiable_on {0..1} - S"
      using assms
      by (auto simp add: real_pair_basis valid_path_def piecewise_C1_differentiable_on_def)
    have 0: "f C1_differentiable_on {0..1} - S" using S assms
      using C1_diff_components_2[of "(1,0)" "(\<lambda>x. (f x, g x))"] 
      by (auto simp add: real_pair_basis algebra_simps)
    have 1: "g C1_differentiable_on {0..1} - S" using S assms
      using C1_diff_components_2 [of "(0,1)", OF _ S] real_pair_basis by fastforce
    have *: "(\<lambda>x. (g x, f x)) C1_differentiable_on {0..1} - S"
      using 0 1 C1_differentiable_on_components[where f = "(\<lambda>x. (g x, f x))"]
      by (auto simp add: real_pair_basis valid_path_def piecewise_C1_differentiable_on_def)
    then show ?thesis using \<open>finite S\<close> by auto
  qed
qed

lemma pair_fun_components: "C = (\<lambda>x. (C x \<bullet> i, C x \<bullet> j))"
  by (simp add: i_is_x_axis inner_Pair_0 j_is_y_axis)

lemma swap_pair_fun: "(\<lambda>y. prod.swap (C (y, 0))) =  (\<lambda>x. (C (x, 0) \<bullet> j, C (x, 0) \<bullet> i))"
  by (simp add: prod.swap_def i_is_x_axis inner_Pair_0 j_is_y_axis)

lemma swap_pair_fun': "(\<lambda>y. prod.swap (C (y, 1))) =  (\<lambda>x. (C (x, 1) \<bullet> j, C (x, 1) \<bullet> i))"
  by (simp add: prod.swap_def i_is_x_axis inner_Pair_0 j_is_y_axis)

lemma swap_pair_fun'': "(\<lambda>y. prod.swap (C (0, y))) =  (\<lambda>x. (C (0,x) \<bullet> j, C (0,x) \<bullet> i))"
  by (simp add: prod.swap_def i_is_x_axis inner_Pair_0 j_is_y_axis)

lemma swap_pair_fun''': "(\<lambda>y. prod.swap (C (1, y))) =  (\<lambda>x. (C (1,x) \<bullet> j, C (1,x) \<bullet> i))"
  by (simp add: prod.swap_def i_is_x_axis inner_Pair_0 j_is_y_axis)

lemma swap_valid_boundaries:
  assumes "\<forall>(k,\<gamma>)\<in>boundary C. valid_path \<gamma>"
  assumes "(k,\<gamma>)\<in>boundary (prod.swap o C o prod.swap)"
  shows "valid_path \<gamma>"
  using assms
    valid_path_valid_swap[of "\<lambda>x. (\<lambda>x. C (x, 0)) x \<bullet> i" "\<lambda>x. (\<lambda>x. C (x, 0)) x \<bullet> j"] pair_fun_components[of "(\<lambda>x. C (x, 0))"]
    pair_fun_components[of "(\<lambda>y. C (y, 0))"]           
    valid_path_valid_swap[of "\<lambda>x. (\<lambda>y. C (y, 1)) x \<bullet> i" "\<lambda>x. (\<lambda>y. C (y, 1)) x \<bullet> j"] pair_fun_components[of "(\<lambda>y. C (y, 1))"]
    pair_fun_components[of "(\<lambda>x. C (x, 1))"]           
    valid_path_valid_swap[of "\<lambda>x. (\<lambda>y. C (1,y)) x \<bullet> i" "\<lambda>x. (\<lambda>y. C (1,y)) x \<bullet> j"] pair_fun_components[of "(\<lambda>y. C (1,y))"]
    pair_fun_components[of "(\<lambda>x. C (1,x))"]           
    valid_path_valid_swap[of "\<lambda>x. (\<lambda>y. C (0,y)) x \<bullet> i" "\<lambda>x. (\<lambda>y. C (0,y)) x \<bullet> j"] pair_fun_components[of "(\<lambda>y. C (0,y))"]
    pair_fun_components[of "(\<lambda>x. C (0,x))"]           
  by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def
       o_def real_pair_basis swap_pair_fun swap_pair_fun' swap_pair_fun'' swap_pair_fun''')

lemma prod_comp_eq: 
  assumes "f = prod.swap o g"
  shows "prod.swap o f  = g"
  using swap_comp_swap assms
  by fastforce

lemma swap_typeI_is_typeII:
  assumes "typeI_twoCube C"
  shows "typeII_twoCube (prod.swap o C o prod.swap)"
proof (simp add: typeI_twoCube_def typeII_twoCube_def)
  obtain a b g1 g2 where C: " a < b "
    "(\<forall>x\<in>{a..b}. g2 x \<le> g1 x) "
    "cubeImage C = {(x, y). x \<in> {a..b} \<and> y \<in> {g2 x..g1 x}} "
    "C = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b))) "
    "g1 piecewise_C1_differentiable_on {a..b} "
    "g2 piecewise_C1_differentiable_on {a..b}"
    using typeI_cube_explicit_spec[OF assms]
    by blast
  show "\<exists>a b. a < b \<and>
              (\<exists>g1 g2. (\<forall>x\<in>{a..b}. g2 x \<le> g1 x) \<and>
                  prod.swap \<circ> C \<circ> prod.swap =
                  (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b)) \<and>
                  g1 piecewise_C1_differentiable_on {a..b} \<and> g2 piecewise_C1_differentiable_on {a..b})"
    using C by (fastforce simp add: prod.swap_def o_def)
qed

lemma valid_cube_valid_swap:
  assumes "valid_two_cube C"
  shows "valid_two_cube (prod.swap o C o prod.swap)"
  using assms unfolding valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def
  apply (auto simp: card_insert_if  split: if_split_asm)
   apply (metis swap_swap)+
  done

lemma twoChainVertDiv_of_itself:
  assumes "finite C"
    "\<forall>(k, \<gamma>)\<in>(two_chain_boundary C). valid_path \<gamma>"
  shows "only_vertical_division (two_chain_boundary C) C"
proof(clarsimp simp add: only_vertical_division_def)
  show "\<exists>\<V> \<H>. finite \<H> \<and> finite \<V> \<and>
              (\<forall>x\<in>\<V>. case x of (k, \<gamma>) \<Rightarrow> \<exists>x\<in>two_chain_vertical_boundary C. case x of (k', \<gamma>') \<Rightarrow> \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<and>
              (common_sudiv_exists (two_chain_horizontal_boundary C) \<H> \<or>
               common_reparam_exists \<H> (two_chain_horizontal_boundary C)) \<and>
              boundary_chain \<H> \<and> two_chain_boundary C = \<V> \<union> \<H> \<and> (\<forall>(k,\<gamma>)\<in>\<H>. valid_path \<gamma>)"
  proof (intro exI)
    let ?\<H> = "two_chain_horizontal_boundary C"
    have 0: "\<forall>(k,\<gamma>)\<in>?\<H>. valid_path \<gamma>" using assms(2)
      by (auto simp add: two_chain_horizontal_boundary_def two_chain_boundary_def boundary_def)
    have "\<And>a b. (a, b) \<in> two_chain_vertical_boundary C \<Longrightarrow>
                  \<exists>x\<in>two_chain_vertical_boundary C. case x of (k', \<gamma>') \<Rightarrow> \<exists>a\<in>{0..1}. \<exists>c\<in>{0..1}. a \<le> c \<and> subpath a c \<gamma>' = b"
      by (metis (mono_tags, lifting) atLeastAtMost_iff case_prod_conv le_numeral_extra(1) order_refl subpath_trivial)
    moreover have "common_sudiv_exists ?\<H> ?\<H>"
      using gen_common_boundary_subdiv_exists_refl_twochain_boundary[OF 0 two_chain_horizontal_boundary_is_boundary_chain]
      by auto
    moreover have "boundary_chain ?\<H>"
      using two_chain_horizontal_boundary_is_boundary_chain by auto
    moreover have "\<And>a b. (a, b) \<in> two_chain_boundary C \<Longrightarrow> (a, b) \<notin> ?\<H> \<Longrightarrow> (a, b) \<in> two_chain_vertical_boundary C"
      by (auto simp add: two_chain_boundary_def two_chain_horizontal_boundary_def two_chain_vertical_boundary_def boundary_def)
    moreover have "\<And>a b. (a, b) \<in> two_chain_vertical_boundary C \<Longrightarrow> (a, b) \<in> two_chain_boundary C"
      "\<And>a b. (a, b) \<in> ?\<H> \<Longrightarrow> (a, b) \<in> two_chain_boundary C"
      by (auto simp add: two_chain_boundary_def two_chain_horizontal_boundary_def two_chain_vertical_boundary_def boundary_def)
    moreover have "\<And>a b. (a, b) \<in> ?\<H> \<Longrightarrow> valid_path b"
      using 0 by blast 
    ultimately show "finite ?\<H> \<and>
           finite (two_chain_vertical_boundary C) \<and>
           (\<forall>x\<in>two_chain_vertical_boundary C.
               case x of (k, \<gamma>) \<Rightarrow> \<exists>x\<in>two_chain_vertical_boundary C. case x of (k', \<gamma>') \<Rightarrow> \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<and>
           (common_sudiv_exists ?\<H> ?\<H> \<or>
            common_reparam_exists ?\<H> ?\<H>) \<and>
           boundary_chain ?\<H> \<and> two_chain_boundary C = two_chain_vertical_boundary C \<union> ?\<H> \<and> (\<forall>(k,\<gamma>)\<in>?\<H>. valid_path \<gamma>)"
      by (auto simp add: finite_two_chain_horizontal_boundary[OF assms(1)] finite_two_chain_vertical_boundary[OF assms(1)])
  qed
qed


end

definition x_coord where "x_coord \<equiv> (\<lambda>t::real. t - 1/2)"

lemma x_coord_smooth: "x_coord C1_differentiable_on {a..b}"
  by (simp add: x_coord_def)

lemma x_coord_bounds:
  assumes "(0::real) \<le> x" "x \<le> 1"
  shows "-1/2 \<le> x_coord x \<and> x_coord x \<le> 1/2"
  using assms by(auto simp add: x_coord_def)

lemma x_coord_img: "x_coord ` {(0::real)..1} = {-1/2 .. 1/2}"
  by (auto simp add: x_coord_def image_def algebra_simps)

lemma x_coord_back_img: "finite ({0..1} \<inter> x_coord -` {x::real})"
  by (simp add: finite_vimageI inj_on_def x_coord_def)


abbreviation "rot_x t1 t2 \<equiv> (if (t1 - 1/2) \<le> 0 then (2 * t2 - 1) * t1 + 1/2 ::real else 2 * t2 - 2 * t1 * t2 +t1 -1/2::real)"

lemma rot_x_ivl:
  assumes "0 \<le> x"
    "x \<le> 1"
    "0 \<le> y"
    "y \<le> 1" 
  shows "0 \<le> rot_x x y \<and> rot_x x y \<le> 1"
proof - 
  have i: "\<And>a::real. a \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1  \<Longrightarrow> -1/2 < a \<Longrightarrow> (a * (1 - 2*y) \<le> 1/2)"
  proof -
    have 0: "\<And>a::real. a \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1  \<Longrightarrow> -1/2 < a \<Longrightarrow> (-a \<le> 1/2)"
      by (sos "((((A<0 * A<1) * R<1) + (R<1 * (R<1/4 * [2*a + 1]^2))))")
    have 1: "\<And>a. a \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1  \<Longrightarrow> -1/2 < a \<Longrightarrow> (a * (1 - 2*y) \<le> -a)"
      by (sos "((((A<0 * A<1) * R<1) + (((A<=0 * (A<1 * R<1)) * (R<2/3 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<2/3 * [1]^2)) + ((A<=0 * (A<=2 * (A<0 * R<1))) * (R<2/3 * [1]^2))))))")
    show "\<And>a::real. a \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> -1/2 < a \<Longrightarrow> (a * (1 - 2*y) \<le> 1/2)" using 0 1 by force
  qed
  have *: "(x * 2 + y * 4 \<le> 3 + x * (y * 4)) =  ( (x-1) \<le> 1/2+ (x-1) * (y * 2))"
    by (sos "((((A<0 * R<1) + ((A<=0 * R<1) * (R<2 * [1]^2)))) & (((A<0 * R<1) + ((A<=0 * R<1) * (R<1/2 * [1]^2)))))")
  show ?thesis
    using assms
    apply(auto simp add: algebra_simps divide_simps linorder_class.not_le)
       apply (sos "(((A<0 * R<1) + (((A<=2 * (A<=3 * R<1)) * (R<1 * [1]^2)) + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<2 * [1]^2))))))")
      apply (sos "(((A<0 * R<1) + (((A<=2 * R<1) * (R<1 * [1]^2)) + (((A<=1 * (A<=3 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=2 * R<1)) * (R<2 * [1]^2))))))")
    using i[of "(x::real) - 1"] affine_ineq
     apply (fastforce simp: algebra_simps *)+
    done
qed

end
