theory Green
  imports Paths Derivs Integrals General_Utils
begin

lemma frontier_Un_subset_Un_frontier:
     "frontier (s \<union> t) \<subseteq> (frontier s) \<union> (frontier t)"
  by (simp add: frontier_def Un_Diff) (auto simp add: closure_def interior_def islimpt_def)

definition has_partial_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a) \<Rightarrow> bool" where
  "has_partial_derivative F base_vec F' a
        \<equiv> ((\<lambda>x::'a::euclidean_space. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + (x \<bullet> base_vec) *\<^sub>R base_vec ))
                has_derivative F') (at a)"

definition has_partial_vector_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> ( 'b) \<Rightarrow> ('a) \<Rightarrow> bool" where
  "has_partial_vector_derivative F base_vec F' a
        \<equiv> ((\<lambda>x. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + x *\<^sub>R base_vec ))
                has_vector_derivative F') (at (a \<bullet> base_vec))"

definition partially_vector_differentiable where
  "partially_vector_differentiable F base_vec p \<equiv> (\<exists>F'. has_partial_vector_derivative F base_vec F' p)"

definition partial_vector_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "partial_vector_derivative F base_vec a
        \<equiv> (vector_derivative (\<lambda>x. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + x *\<^sub>R base_vec)) (at (a \<bullet> base_vec)))"

lemma partial_vector_derivative_works:
  assumes "partially_vector_differentiable F base_vec a"
  shows "has_partial_vector_derivative F base_vec (partial_vector_derivative F base_vec a) a"
proof -
  obtain F' where F'_prop: "((\<lambda>x. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + x *\<^sub>R base_vec ))
                            has_vector_derivative F') (at (a \<bullet> base_vec))"
    using assms partially_vector_differentiable_def has_partial_vector_derivative_def
    by blast
  show ?thesis
    using Derivative.differentiableI_vector[OF F'_prop]
    by(simp add: vector_derivative_works partial_vector_derivative_def[symmetric]
        has_partial_vector_derivative_def[symmetric])
qed

lemma fundamental_theorem_of_calculus_partial_vector:
  fixes a b:: "real" and
    F:: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space)" and
    i:: "'a" and
    j:: "'b" and
    F_j_i:: "('a::euclidean_space \<Rightarrow> real)"
  assumes a_leq_b: "a \<le> b" and
    Base_vecs: "i \<in> Basis" "j \<in> Basis" and
    no_i_component: "c \<bullet> i = 0 " and
    has_partial_deriv: "\<forall>p \<in> D. has_partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i (F_j_i p) p" and
    domain_subset_of_D: "{x *\<^sub>R i + c |x. a \<le> x \<and> x \<le> b} \<subseteq> D"
  shows "((\<lambda>x. F_j_i( x *\<^sub>R i + c)) has_integral
          F(b *\<^sub>R i + c) \<bullet> j - F(a *\<^sub>R i + c) \<bullet> j) (cbox a b)"
proof -
  let ?domain = "{v. \<exists>x. a \<le> x \<and> x \<le> b \<and> v = x *\<^sub>R i + c}"
  have "\<forall>x\<in> ?domain.  has_partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i (F_j_i x) x"
    using has_partial_deriv domain_subset_of_D
    by auto
  then have "\<forall>x\<in> (cbox a b).  ((\<lambda>x. F(x *\<^sub>R i + c) \<bullet> j) has_vector_derivative (F_j_i( x *\<^sub>R i + c))) (at x)"
  proof(clarsimp simp add: has_partial_vector_derivative_def)
    fix x::real
    assume range_of_x: "a \<le> x" "x \<le> b"
    assume ass2: "\<forall>x. (\<exists>z\<ge>a. z \<le> b \<and> x = z *\<^sub>R i + c) \<longrightarrow>
                     ((\<lambda>z. F(x - (x \<bullet> i) *\<^sub>R i + z *\<^sub>R i) \<bullet> j) has_vector_derivative F_j_i x) (at (x \<bullet> i))"
    have "((\<lambda>z. F((x *\<^sub>R i + c) - ((x *\<^sub>R i + c) \<bullet> i) *\<^sub>R i + z *\<^sub>R i) \<bullet> j) has_vector_derivative F_j_i (x *\<^sub>R i + c)) (at ((x *\<^sub>R i + c) \<bullet> i)) "
      using range_of_x ass2 by auto
    then have 0: "((\<lambda>x. F( c + x *\<^sub>R i) \<bullet> j) has_vector_derivative F_j_i (x *\<^sub>R i + c)) (at x)"
      by (simp add: assms(2) inner_left_distrib no_i_component)
    have 1: "(\<lambda>x. F(x *\<^sub>R i + c) \<bullet> j) = (\<lambda>x. F(c + x *\<^sub>R i) \<bullet> j)"
      by (simp add: add.commute)
    then show "((\<lambda>x. F(x *\<^sub>R i + c) \<bullet> j) has_vector_derivative F_j_i (x *\<^sub>R i + c)) (at x)" 
      using 0 and 1 by auto
  qed
  then have "\<forall>x\<in> (cbox a b).  ((\<lambda>x. F(x *\<^sub>R i + c) \<bullet> j) has_vector_derivative (F_j_i( x *\<^sub>R i + c))) (at_within x (cbox a b))"
    using has_vector_derivative_at_within
    by blast
  then show "( (\<lambda>x. F_j_i( x *\<^sub>R i + c)) has_integral
             F(b *\<^sub>R i + c) \<bullet> j - F(a *\<^sub>R i + c) \<bullet> j) (cbox a b)"
    using fundamental_theorem_of_calculus[of "a" "b" "(\<lambda>x::real.  F(x *\<^sub>R i + c) \<bullet> j)" "(\<lambda>x::real. F_j_i( x *\<^sub>R i + c))"] and
      a_leq_b
    by auto
qed

lemma fundamental_theorem_of_calculus_partial_vector_gen:
  fixes k1 k2:: "real" and
    F:: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space)" and
    i:: "'a" and
    F_i:: "('a::euclidean_space \<Rightarrow> 'b)"
  assumes a_leq_b: "k1 \<le> k2" and
    unit_len: "i \<bullet> i = 1" and
    no_i_component: "c \<bullet> i = 0 " and
    has_partial_deriv: "\<forall>p \<in> D. has_partial_vector_derivative F i (F_i p) p" and
    domain_subset_of_D: "{v. \<exists>x. k1 \<le> x \<and> x \<le> k2 \<and> v = x *\<^sub>R i + c} \<subseteq> D"
  shows "( (\<lambda>x. F_i( x *\<^sub>R i + c)) has_integral
                                        F(k2 *\<^sub>R i + c) - F(k1 *\<^sub>R i + c)) (cbox k1 k2)"
proof -
  let ?domain = "{v. \<exists>x. k1 \<le> x \<and> x \<le> k2 \<and> v = x *\<^sub>R i + c}"
  have "\<forall>x\<in> ?domain.  has_partial_vector_derivative F i (F_i x) x"
    using has_partial_deriv domain_subset_of_D
    by auto
  then have "\<forall>x\<in> (cbox k1 k2).  ((\<lambda>x. F(x *\<^sub>R i + c)) has_vector_derivative (F_i( x *\<^sub>R i + c))) (at x)"
  proof (clarsimp simp add: has_partial_vector_derivative_def)
    fix x::real
    assume range_of_x: "k1 \<le> x" "x \<le> k2"
    assume ass2: "\<forall>x. (\<exists>z\<ge>k1. z \<le> k2 \<and> x = z *\<^sub>R i + c) \<longrightarrow>
                     ((\<lambda>z. F(x - (x \<bullet> i) *\<^sub>R i + z *\<^sub>R i)) has_vector_derivative F_i x) (at (x \<bullet> i))"
    have "((\<lambda>z. F((x *\<^sub>R i + c) - ((x *\<^sub>R i + c) \<bullet> i) *\<^sub>R i + z *\<^sub>R i)) has_vector_derivative F_i (x *\<^sub>R i + c)) (at ((x *\<^sub>R i + c) \<bullet> i)) "
      using range_of_x ass2 by auto
    then have 0: "((\<lambda>x. F( c + x *\<^sub>R i)) has_vector_derivative F_i (x *\<^sub>R i + c)) (at x)"
      by (simp add: inner_commute inner_right_distrib no_i_component unit_len)
    have 1: "(\<lambda>x. F(x *\<^sub>R i + c)) = (\<lambda>x. F(c + x *\<^sub>R i))"
      by (simp add: add.commute)
    then show "((\<lambda>x. F(x *\<^sub>R i + c)) has_vector_derivative F_i (x *\<^sub>R i + c)) (at x)" using 0 and 1 by auto
  qed
  then have "\<forall>x\<in> (cbox k1 k2).  ((\<lambda>x. F(x *\<^sub>R i + c) ) has_vector_derivative (F_i( x *\<^sub>R i + c))) (at_within x (cbox k1 k2))"
    using has_vector_derivative_at_within
    by blast
  then show "( (\<lambda>x. F_i( x *\<^sub>R i + c)) has_integral
                                        F(k2 *\<^sub>R i + c) - F(k1 *\<^sub>R i + c)) (cbox k1 k2)"
    using fundamental_theorem_of_calculus[of "k1" "k2" "(\<lambda>x::real.  F(x *\<^sub>R i + c))" "(\<lambda>x::real. F_i( x *\<^sub>R i + c))"] and
      a_leq_b
    by auto
qed

lemma add_scale_img:
  assumes "a < b" shows "(\<lambda>x::real. a + (b - a) * x) ` {0 .. 1} = {a .. b}"
  using assms 
  apply (auto simp: algebra_simps affine_ineq image_iff)
  using less_eq_real_def apply force
  apply (rule_tac x="(x-a)/(b-a)" in bexI)
   apply (auto simp: field_simps)
  done

lemma add_scale_img':
  assumes "a \<le> b"
  shows "(\<lambda>x::real. a + (b - a) * x) ` {0 .. 1} = {a .. b}"
proof (cases "a = b")
  case True
  then show ?thesis by force
next
  case False
  then show ?thesis
    using add_scale_img assms by auto
qed

definition analytically_valid:: "'a::euclidean_space set \<Rightarrow> ('a \<Rightarrow> 'b::{euclidean_space,times,one}) \<Rightarrow> 'a \<Rightarrow> bool" where
  "analytically_valid s F i \<equiv>
       (\<forall>a \<in> s. partially_vector_differentiable F i a) \<and>
       continuous_on s F \<and> \<comment> \<open>TODO: should we replace this with saying that \<open>F\<close> is partially diffrerentiable on \<open>Dy\<close>,\<close>
                           \<comment> \<open>i.e. there is a partial derivative on every dimension\<close>
       integrable lborel (\<lambda>p. (partial_vector_derivative F i) p * indicator s p) \<and>
       (\<lambda>x. integral UNIV (\<lambda>y. (partial_vector_derivative F i (y *\<^sub>R i + x *\<^sub>R (\<Sum> b \<in>(Basis - {i}). b)))
            * (indicator s (y *\<^sub>R i + x *\<^sub>R (\<Sum>b \<in> Basis - {i}. b)) ))) \<in> borel_measurable lborel"
  (*(\<lambda>x. integral UNIV (\<lambda>y. ((partial_vector_derivative F i) (y, x)) * (indicator s (y, x)))) \<in> borel_measurable lborel)"*)


lemma analytically_valid_imp_part_deriv_integrable_on:
  assumes "analytically_valid (s::(real*real) set) (f::(real*real)\<Rightarrow> real) i"
  shows "(partial_vector_derivative f i) integrable_on s"
proof -
  have "integrable lborel (\<lambda>p. partial_vector_derivative f i p * indicator s p)"
    using assms
    by(simp add:  analytically_valid_def indic_ident)
  then have "integrable lborel (\<lambda>p::(real*real). if p \<in> s then partial_vector_derivative f i p else 0)"
    using indic_ident[of "partial_vector_derivative f i"]
    by (simp add: indic_ident)
  then have "(\<lambda>x. if x \<in> s then partial_vector_derivative f i x else 0) integrable_on UNIV"
    using Equivalence_Lebesgue_Henstock_Integration.integrable_on_lborel
    by auto
  then show "(partial_vector_derivative f i) integrable_on s"
    using integrable_restrict_UNIV
    by auto
qed

(*******************************************************************************)

definition typeII_twoCube :: "((real * real) \<Rightarrow> (real * real)) \<Rightarrow> bool" where
  "typeII_twoCube twoC
         \<equiv> \<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a..b}. g2 x \<le> g1 x) \<and>
                       twoC = (\<lambda>(y, x). ((1 - y) * (g2 ((1-x)*a + x*b)) + y * (g1 ((1-x)*a + x*b)),
                                        (1-x)*a + x*b)) \<and>
                       g1 piecewise_C1_differentiable_on {a .. b} \<and>
                       g2 piecewise_C1_differentiable_on {a .. b}"

abbreviation unit_cube where "unit_cube \<equiv> cbox (0,0) (1::real,1::real)" 

definition cubeImage:: "two_cube \<Rightarrow> ((real*real) set)" where
  "cubeImage twoC \<equiv> (twoC ` unit_cube)"

lemma typeII_twoCubeImg:
  assumes "typeII_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(y,x). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                      \<and> twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))
                      \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b} "
  using assms
proof (simp add: typeII_twoCube_def cubeImage_def image_def)
  assume " \<exists>a b. a < b \<and> (\<exists>g1 g2. (\<forall>x\<in>{a..b}. g2 x \<le> g1 x) \<and>
                            twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b)) \<and>
                            g1 piecewise_C1_differentiable_on {a..b} \<and> g2 piecewise_C1_differentiable_on {a..b})"
  then obtain a b g1 g2 where
    twoCisTypeII: "a < b"
    "(\<forall>x\<in>{a..b}. g2 x \<le> g1 x)"
    "twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    by auto
  have ab1: "a - x * a + x * b \<le> b" if a1: "0 \<le> x" "x \<le> 1" for x
    using that apply (simp add: algebra_simps)
    by (metis affine_ineq less_eq_real_def mult.commute twoCisTypeII(1))
  have ex: "\<exists>z\<in>Green.unit_cube.
               (d, c) =
               (case z of
                (y, x) \<Rightarrow>
                  (g2 (a - x * a + x * b) - y * g2 (a - x * a + x * b) + y * g1 (a - x * a + x * b),
                   a - x * a + x * b))" 
    if c_bounds: "a \<le> c" "c \<le> b" and d_bounds: "g2 c \<le> d" "d \<le> g1 c" for c d
  proof -
    have b_minus_a_nzero: "b - a \<noteq> 0" using twoCisTypeII(1) by auto
    have x_witness: "\<exists>k1. c = (1 - k1)*a + k1 * b \<and> 0 \<le> k1 \<and> k1 \<le> 1"
      apply (rule_tac x="(c - a)/(b - a)" in exI)
      using c_bounds \<open>a < b\<close> apply (simp add: divide_simps algebra_simps)
      using sum_sqs_eq by blast
    have y_witness: "\<exists>k2. d = (1 - k2)*(g2 c) + k2 * (g1 c) \<and> 0 \<le> k2 \<and> k2 \<le> 1"
    proof (cases "g1 c - g2 c = 0")
      case True
      with d_bounds show ?thesis by (fastforce simp add: algebra_simps)
    next
      case False
      let ?k2 = "(d - g2 c)/(g1 c - g2 c)"
      have k2_in_bounds: "0 \<le> ?k2 \<and> ?k2 \<le> 1" 
        using twoCisTypeII(2) c_bounds d_bounds False by simp
      have "d = (1 - ?k2) * g2 c + ?k2 * g1 c" 
        using False sum_sqs_eq by (fastforce simp add: divide_simps algebra_simps)
      with k2_in_bounds show ?thesis 
        by fastforce
    qed
    show "\<exists>x\<in>unit_cube. (d, c) = (case x of (y, x) \<Rightarrow> (g2 (a - x * a + x * b) - y * g2 (a - x * a + x * b) + y * g1 (a - x * a + x * b), a - x * a + x * b))"
      using x_witness y_witness by (force simp add: left_diff_distrib)
  qed
  have "{y. \<exists>x\<in>unit_cube. y = twoC x} = {(y, x). a \<le> x \<and> x \<le> b \<and> g2 x \<le> y \<and> y \<le> g1 x}"
    apply (auto simp add: twoCisTypeII ab1 left_diff_distrib ex)
    using order.order_iff_strict twoCisTypeII(1) apply fastforce
     apply (smt affine_ineq atLeastAtMost_iff mult_left_mono twoCisTypeII)+
    done
  then show "\<exists>a b. a < b \<and> (\<exists>g1 g2. (\<forall>x\<in>{a..b}. g2 x \<le> g1 x) \<and>
                            {y. \<exists>x\<in>unit_cube. y = twoC x} = {(y, x). a \<le> x \<and> x \<le> b \<and> g2 x \<le> y \<and> y \<le> g1 x} \<and>
                            twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b)) \<and>
                            g1 piecewise_C1_differentiable_on {a..b} \<and> g2 piecewise_C1_differentiable_on {a..b})"
    using twoCisTypeII by blast
qed

definition horizontal_boundary :: "two_cube \<Rightarrow> one_chain" where
  "horizontal_boundary twoC \<equiv> {(1, (\<lambda>x. twoC(x,0))), (-1, (\<lambda>x. twoC(x,1)))}"

definition vertical_boundary :: "two_cube \<Rightarrow> one_chain" where
  "vertical_boundary twoC \<equiv> {(-1, (\<lambda>y. twoC(0,y))), (1, (\<lambda>y. twoC(1,y)))}"

definition boundary :: "two_cube \<Rightarrow> one_chain" where
  "boundary twoC \<equiv> horizontal_boundary twoC \<union> vertical_boundary twoC"

definition valid_two_cube where
  "valid_two_cube twoC \<equiv> card (boundary twoC) = 4"

definition two_chain_integral:: "two_chain \<Rightarrow> ((real*real)\<Rightarrow>(real)) \<Rightarrow> real" where
  "two_chain_integral twoChain F \<equiv> \<Sum>C\<in>twoChain. (integral (cubeImage C) F)"

definition valid_two_chain where
  "valid_two_chain twoChain \<equiv> (\<forall>twoCube \<in> twoChain. valid_two_cube twoCube) \<and> pairwise (\<lambda>c1 c2. ((boundary c1) \<inter> (boundary c2)) = {}) twoChain \<and> inj_on cubeImage twoChain"

definition two_chain_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_boundary twoChain == \<Union>(boundary ` twoChain)"

definition gen_division where
  "gen_division s S \<equiv> (finite S \<and> (\<Union>S = s) \<and> pairwise (\<lambda>X Y. negligible (X \<inter> Y)) S)"


definition two_chain_horizontal_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_horizontal_boundary twoChain  \<equiv> \<Union>(horizontal_boundary ` twoChain)"

definition two_chain_vertical_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_vertical_boundary twoChain  \<equiv> \<Union>(vertical_boundary ` twoChain)"

definition only_horizontal_division where
  "only_horizontal_division one_chain two_chain 
      \<equiv> \<exists>\<H> \<V>. finite \<H> \<and> finite \<V> \<and>
               (\<forall>(k,\<gamma>) \<in> \<H>.
                 (\<exists>(k', \<gamma>') \<in> two_chain_horizontal_boundary two_chain.
                     (\<exists>a \<in> {0..1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>))) \<and>
               (common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>
                \<or> common_reparam_exists \<V> (two_chain_vertical_boundary two_chain)) \<and>
               boundary_chain \<V> \<and>
               one_chain = \<H> \<union> \<V> \<and> (\<forall>(k,\<gamma>)\<in>\<V>. valid_path \<gamma>)"

lemma sum_zero_set:
  assumes "\<forall>x \<in> s. f x = 0" "finite s" "finite t"
  shows "sum f (s \<union> t) = sum f t"
  using assms
  by (simp add: IntE sum.union_inter_neutral sup_commute)

abbreviation "valid_typeII_division s twoChain \<equiv> ((\<forall>twoCube \<in> twoChain. typeII_twoCube twoCube) \<and>
                                                (gen_division s (cubeImage ` twoChain)) \<and>
                                                (valid_two_chain twoChain))"

lemma two_chain_vertical_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_vertical_boundary twoChain)"
  by(simp add: boundary_chain_def two_chain_vertical_boundary_def vertical_boundary_def)

lemma two_chain_horizontal_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_horizontal_boundary twoChain)"
  by(simp add: boundary_chain_def two_chain_horizontal_boundary_def horizontal_boundary_def)

definition typeI_twoCube :: "two_cube \<Rightarrow> bool" where
  "typeI_twoCube (twoC::two_cube)
        \<equiv> \<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a..b}. g2 x \<le> g1 x) \<and>
                       twoC = (\<lambda>(x,y). ((1-x)*a + x*b,
                                        (1 - y) * (g2 ((1-x)*a + x*b)) + y * (g1 ((1-x)*a + x*b)))) \<and>
                       g1 piecewise_C1_differentiable_on {a..b} \<and>
                       g2 piecewise_C1_differentiable_on {a..b}"

lemma typeI_twoCubeImg:
  assumes "typeI_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(x,y). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}} \<and>
                      twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b))) \<and>
                      g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b} "
proof -
  have "\<exists>a b. a < b \<and>
          (\<exists>g1 g2. (\<forall>x\<in>{a..b}. g2 x \<le> g1 x) \<and>
                   twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))\<and>
                   g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b})"
    using assms by (simp add: typeI_twoCube_def)
  then obtain a b g1 g2 where
    twoCisTypeI: "a < b"
        "(\<forall>x\<in>{a..b}. g2 x \<le> g1 x)"
        "twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))"
        "g1 piecewise_C1_differentiable_on {a .. b}"
        "g2 piecewise_C1_differentiable_on {a .. b}"
    by auto
  have ex: "\<exists>z\<in>Green.unit_cube.
               (c, d) =
               (case z of
                (x, y) \<Rightarrow>
                  (a - x * a + x * b,
                   g2 (a - x * a + x * b) - y * g2 (a - x * a + x * b) + y * g1 (a - x * a + x * b)))"
    if c_bounds: "a \<le> c" "c \<le> b" and  d_bounds: "g2 c \<le> d" "d \<le> g1 c" for c d
  proof -
    have x_witness: "\<exists>k1. c = (1 - k1)*a + k1 * b \<and> 0 \<le> k1 \<and> k1 \<le> 1"
    proof -
      let ?k1 = "(c - a)/(b - a)"
      have k1_in_bounds: "0 \<le> (c - a)/(b - a) \<and> (c - a)/(b - a) \<le> 1" 
        using twoCisTypeI(1) c_bounds by simp
      have "c = (1 - ?k1)*a + ?k1 * b" 
        using twoCisTypeI(1) sum_sqs_eq
        by (auto simp add: divide_simps algebra_simps)
      then show ?thesis
        using twoCisTypeI k1_in_bounds by fastforce
    qed
    have y_witness: "\<exists>k2. d = (1 - k2)*(g2 c) + k2 * (g1 c) \<and> 0 \<le> k2 \<and> k2 \<le> 1"
    proof (cases "g1 c - g2 c = 0")
      case True
      with d_bounds show ?thesis
        by force
    next
      case False
      let ?k2 = "(d - g2 c)/(g1 c - g2 c)"
      have k2_in_bounds: "0 \<le> ?k2 \<and> ?k2 \<le> 1" using twoCisTypeI(2) c_bounds d_bounds False by simp
      have "d = (1 - ?k2) * g2 c + ?k2 * g1 c"
        using False apply (simp add: divide_simps algebra_simps)
        using sum_sqs_eq by fastforce        
      then show ?thesis using k2_in_bounds by fastforce
    qed
    show "\<exists>x\<in>unit_cube. (c, d) =
            (case x of (x, y) \<Rightarrow> (a - x * a + x * b, g2 (a - x * a + x * b) - y * g2 (a - x * a + x * b) + y * g1 (a - x * a + x * b)))"
      using x_witness y_witness by (force simp add: left_diff_distrib)
  qed
  have "{y. \<exists>x\<in>unit_cube. y = twoC x} = {(x, y). a \<le> x \<and> x \<le> b \<and> g2 x \<le> y \<and> y \<le> g1 x}"
    apply (auto simp add: twoCisTypeI left_diff_distrib ex)
    using less_eq_real_def twoCisTypeI(1) apply auto[1]
       apply (smt affine_ineq twoCisTypeI)
      apply (smt affine_ineq atLeastAtMost_iff mult_left_mono twoCisTypeI)+
    done
  then show ?thesis
    unfolding cubeImage_def image_def using twoCisTypeI by auto
qed

lemma typeI_cube_explicit_spec:
  assumes "typeI_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(x,y). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                      \<and> twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))
                      \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b}
                      \<and> (\<lambda>x. twoC(x, 0)) = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))
                      \<and> (\<lambda>y. twoC(1, y)) = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))
                      \<and> (\<lambda>x. twoC(x, 1)) = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))
                      \<and> (\<lambda>y. twoC(0, y)) = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(x, 0))"
  let ?right_edge = "(\<lambda>y. twoC(1, y))"
  let ?top_edge = "(\<lambda>x. twoC(x, 1))"
  let ?left_edge = "(\<lambda>y. twoC(0, y))"
  obtain a b g1 g2 where
    twoCisTypeI: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(x,y). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    using assms and typeI_twoCubeImg[of"twoC"] by auto
  have bottom_edge_explicit: "?bottom_edge = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))"
    by (simp add: twoCisTypeI(4) algebra_simps)
  have right_edge_explicit: "?right_edge = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))"
    by (simp add: twoCisTypeI(4) algebra_simps)
  have top_edge_explicit: "?top_edge = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))"
    by (simp add: twoCisTypeI(4) algebra_simps)
  have left_edge_explicit: "?left_edge = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
    by (simp add: twoCisTypeI(4) algebra_simps)
  show ?thesis
    using bottom_edge_explicit right_edge_explicit top_edge_explicit left_edge_explicit twoCisTypeI
    by auto
qed

lemma typeI_twoCube_smooth_edges:
  assumes "typeI_twoCube twoC"
    "(k,\<gamma>) \<in> boundary twoC"
  shows "\<gamma> piecewise_C1_differentiable_on {0..1}"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(x, 0))"
  let ?right_edge = "(\<lambda>y. twoC(1, y))"
  let ?top_edge = "(\<lambda>x. twoC(x, 1))"
  let ?left_edge = "(\<lambda>y. twoC(0, y))"
  obtain a b g1 g2 where
    twoCisTypeI: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(x,y). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    "(\<lambda>x. twoC(x, 0)) = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(1, y)) = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))"
    "(\<lambda>x. twoC(x, 1)) = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(0, y)) = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
    using assms and typeI_cube_explicit_spec[of"twoC"]
    by auto
  have bottom_edge_smooth: "(\<lambda>x. twoC (x, 0)) piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x))-` {x} = {(x - a)/(b -a)}"
      using twoCisTypeI(1)
      by(auto simp add: Set.vimage_def)
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    have scale_shif_smth: "(\<lambda>x. (a + (b - a) * x)) C1_differentiable_on {0..1}" using scale_shift_smooth by auto
    then have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" using C1_differentiable_imp_piecewise by blast
    have g2_smooth: "g2 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeI(1)] twoCisTypeI(6) by auto
    have "(\<lambda>x. g2 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g2_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x::real. (a + (b - a) * x, g2 (a + (b - a) * x))) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x::real. (a + (b - a) * x, g2 (a + (b - a) * x)))"]
      apply (simp only: real_pair_basis)
      by fastforce
    then show ?thesis using twoCisTypeI(7) by auto
  qed
  have top_edge_smooth: "?top_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x))-` {x} = {(x - a)/(b -a)}"
      using twoCisTypeI(1)
      by(auto simp add: Set.vimage_def)
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    have scale_shif_smth: "(\<lambda>x. (a + (b - a) * x)) C1_differentiable_on {0..1}" using scale_shift_smooth by auto
    then have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" using C1_differentiable_imp_piecewise by blast
    have g1_smooth: "g1 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeI(1)] twoCisTypeI(5) by auto
    have "(\<lambda>x. g1 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g1_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x))) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))"]
      apply (simp only: real_pair_basis)
      by fastforce
    then show ?thesis using twoCisTypeI(9) by auto
  qed
  have right_edge_smooth: "?right_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "(\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b))) C1_differentiable_on {0..1}"
      using scale_shift_smooth C1_differentiable_imp_piecewise by auto
    then have "(\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b))) piecewise_C1_differentiable_on {0..1}"
      using C1_differentiable_imp_piecewise by fastforce
    then have "(\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b))) piecewise_C1_differentiable_on {0..1}"
      using pair_prod_smooth_pw_smooth by auto
    then show ?thesis
      using twoCisTypeI(8) by auto
  qed
  have left_edge_smooth: "?left_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "(\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a))) C1_differentiable_on {0..1}"
      using scale_shift_smooth by auto
    then have "(\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a))) piecewise_C1_differentiable_on {0..1}"
      using C1_differentiable_imp_piecewise by fastforce
    then have "(\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a))) piecewise_C1_differentiable_on {0..1}"
      using pair_prod_smooth_pw_smooth by auto
    then show ?thesis
      using twoCisTypeI(10) by auto
  qed
  have "\<gamma> = ?bottom_edge \<or> \<gamma> = ?right_edge \<or> \<gamma> = ?top_edge \<or> \<gamma> = ?left_edge"
    using assms by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  then show ?thesis
    using left_edge_smooth right_edge_smooth top_edge_smooth bottom_edge_smooth by auto
qed

lemma two_chain_integral_eq_integral_divisable:
  assumes f_integrable: "\<forall>twoCube \<in> twoChain. F integrable_on cubeImage twoCube" and
    gen_division: "gen_division s (cubeImage ` twoChain)" and
    valid_two_chain: "valid_two_chain twoChain"
  shows "integral s F = two_chain_integral twoChain F"
proof -
  show "integral s F = two_chain_integral twoChain F"
  proof (simp add: two_chain_integral_def)
    have partial_deriv_integrable:
      "\<forall>twoCube \<in> twoChain. ((F) has_integral (integral (cubeImage twoCube) (F))) (cubeImage twoCube)"
      using f_integrable by auto
    then have partial_deriv_integrable:
      "\<And>twoCubeImg. twoCubeImg \<in> cubeImage ` twoChain \<Longrightarrow> (F has_integral (integral (twoCubeImg) F)) (twoCubeImg)"
      using Henstock_Kurzweil_Integration.integrable_neg by force
    have finite_images: "finite (cubeImage ` twoChain)"
      using gen_division gen_division_def by auto
    have negligible_images: "pairwise (\<lambda>S S'. negligible (S \<inter> S')) (cubeImage ` twoChain)"
      using gen_division  by (auto simp add: gen_division_def pairwise_def)
    have inj: "inj_on cubeImage twoChain"
      using valid_two_chain by (simp add: inj_on_def valid_two_chain_def)
    have "integral s F = (\<Sum>twoCubeImg\<in>cubeImage ` twoChain. integral twoCubeImg F)"
      using has_integral_Union[OF finite_images partial_deriv_integrable negligible_images] gen_division
      by (auto simp add: gen_division_def)
    also have "\<dots> = (\<Sum>C\<in>twoChain. integral (cubeImage C) F)"
      using sum.reindex inj by auto
    finally show "integral s F = (\<Sum>C\<in>twoChain. integral (cubeImage C) F)" .
  qed
qed

definition only_vertical_division where
  "only_vertical_division one_chain two_chain \<equiv>
       \<exists>\<V> \<H>. finite \<H> \<and> finite \<V> \<and>
               (\<forall>(k,\<gamma>) \<in> \<V>.
                 (\<exists>(k',\<gamma>') \<in> two_chain_vertical_boundary two_chain.
                     (\<exists>a \<in> {0..1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>))) \<and>
               (common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>
                \<or> common_reparam_exists \<H> (two_chain_horizontal_boundary two_chain)) \<and>
               boundary_chain \<H> \<and> one_chain = \<V> \<union> \<H> \<and>
               (\<forall>(k,\<gamma>)\<in>\<H>. valid_path \<gamma>)"

abbreviation "valid_typeI_division s twoChain 
   \<equiv> (\<forall>twoCube \<in> twoChain. typeI_twoCube twoCube) \<and>
      gen_division s (cubeImage ` twoChain) \<and> valid_two_chain twoChain"


lemma field_cont_on_typeI_region_cont_on_edges:
  assumes typeI_twoC: "typeI_twoCube twoC" 
    and field_cont: "continuous_on (cubeImage twoC) F" 
    and member_of_boundary: "(k,\<gamma>) \<in> boundary twoC"
  shows "continuous_on (\<gamma> ` {0 .. 1}) F"
proof -
  obtain a b g1 g2 where
    twoCisTypeI: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(x,y). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    "(\<lambda>x. twoC(x, 0)) = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(1, y)) = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))"
    "(\<lambda>x. twoC(x, 1)) = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(0, y)) = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
    using typeI_twoC and typeI_cube_explicit_spec[of"twoC"]
    by auto
  let ?bottom_edge = "(\<lambda>x. twoC(x, 0))"
  let ?right_edge = "(\<lambda>y. twoC(1, y))"
  let ?top_edge = "(\<lambda>x. twoC(x, 1))"
  let ?left_edge = "(\<lambda>y. twoC(0, y))"
  let ?Dg1 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (x, g1(x))}"
  have line_is_pair_img: "?Dg1 = (\<lambda>x. (x, g1(x))) ` (cbox a b)"
    using image_def by auto
  have field_cont_on_top_edge_image: "continuous_on ?Dg1  F"
    by (rule continuous_on_subset [OF field_cont]) (auto simp: twoCisTypeI(2) twoCisTypeI(3))
  have top_edge_is_compos_of_scal_and_g1:
    "(\<lambda>x. twoC(x, 1)) = (\<lambda>x. (x, g1(x))) \<circ> (\<lambda>x. a + (b - a) * x)"
    using twoCisTypeI  by auto
  have Dg1_is_bot_edge_pathimg: "path_image (\<lambda>x. twoC(x, 1)) = ?Dg1"
    using line_is_pair_img and top_edge_is_compos_of_scal_and_g1 image_comp path_image_def add_scale_img and twoCisTypeI(1)
    by (metis (no_types, lifting) cbox_interval)
  then have cont_on_top: "continuous_on (path_image ?top_edge) F"
    using field_cont_on_top_edge_image by auto
  let ?Dg2 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (x, g2(x))}"
  have line_is_pair_img: "?Dg2 = (\<lambda>x. (x, g2(x))) ` (cbox a b)"
    using image_def by auto
  have field_cont_on_bot_edge_image: "continuous_on ?Dg2 F"
    apply (rule continuous_on_subset [OF field_cont])
    using twoCisTypeI(2) twoCisTypeI(3) by auto
  have bot_edge_is_compos_of_scal_and_g2: "(\<lambda>x. twoC(x, 0)) = (\<lambda>x. (x, g2(x))) \<circ> (\<lambda>x. a + (b - a) * x)"
    using twoCisTypeI by auto
  have Dg2_is_bot_edge_pathimg:
    "path_image (\<lambda>x. twoC(x, 0)) = ?Dg2"
    using line_is_pair_img and bot_edge_is_compos_of_scal_and_g2 image_comp path_image_def add_scale_img and twoCisTypeI(1)
    by (metis (no_types, lifting) cbox_interval)
  then have cont_on_bot: "continuous_on (path_image ?bottom_edge) F"
    using field_cont_on_bot_edge_image by auto
  let ?D_left_edge = "{p. \<exists>y. y \<in> cbox (g2 a) (g1 a) \<and> p = (a, y)}"
  have field_cont_on_left_edge_image: "continuous_on ?D_left_edge  F"
    apply (rule continuous_on_subset [OF field_cont])
    using twoCisTypeI(1) twoCisTypeI(3) by auto
  have "g2 a \<le> g1 a" using twoCisTypeI(1) twoCisTypeI(2) by auto
  then have "(\<lambda>x. g2 a + (g1 a - g2 a) * x) ` {(0::real)..1} = {g2 a .. g1 a}"
    using add_scale_img'[of "g2 a" "g1 a"] by blast
  then have left_eq: "?D_left_edge = ?left_edge ` {0..1}"
    unfolding twoCisTypeI(10)
    by(auto simp add: subset_iff image_def set_eq_iff Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(7))
  then have cont_on_left: "continuous_on (path_image ?left_edge) F"
    using field_cont_on_left_edge_image path_image_def
    by (metis left_eq field_cont_on_left_edge_image path_image_def)
  let ?D_right_edge =  "{p. \<exists>y. y \<in> cbox (g2 b) (g1 b) \<and> p = (b, y)}"
  have field_cont_on_left_edge_image: "continuous_on ?D_right_edge F"
    apply (rule continuous_on_subset [OF field_cont])
    using twoCisTypeI(1) twoCisTypeI(3) by auto
  have "g2 b \<le> g1 b" using twoCisTypeI(1)  twoCisTypeI(2) by auto
  then have "(\<lambda>x. g2 b + (g1 b - g2 b) * x) ` {(0::real)..1} = {g2 b .. g1 b}"
    using add_scale_img'[of "g2 b" "g1 b"] by blast
  then have right_eq: "?D_right_edge = ?right_edge ` {0..1}"
    unfolding twoCisTypeI(8) 
    by(auto simp add: subset_iff image_def set_eq_iff Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(7))
  then have cont_on_right:
    "continuous_on (path_image ?right_edge) F"
    using field_cont_on_left_edge_image path_image_def
    by (metis right_eq field_cont_on_left_edge_image path_image_def)
  have all_edge_cases:
    "(\<gamma> = ?bottom_edge \<or> \<gamma> = ?right_edge \<or> \<gamma> = ?top_edge \<or> \<gamma> = ?left_edge)"
    using assms by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  show ?thesis
    apply (simp add: path_image_def[symmetric])
    using cont_on_top cont_on_bot cont_on_right cont_on_left all_edge_cases
    by blast
qed

lemma typeII_cube_explicit_spec:
  assumes "typeII_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                     cubeImage twoC = {(y, x). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                  \<and> twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))
                  \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b}
                  \<and> (\<lambda>x. twoC(0, x)) = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))
                  \<and> (\<lambda>y. twoC(y, 1)) = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))
                  \<and> (\<lambda>x. twoC(1, x)) = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))
                  \<and> (\<lambda>y. twoC(y, 0)) = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(0, x))"
  let ?right_edge = "(\<lambda>y. twoC(y, 1))"
  let ?top_edge = "(\<lambda>x. twoC(1, x))"
  let ?left_edge = "(\<lambda>y. twoC(y, 0))"
  obtain a b g1 g2 where
    twoCisTypeII: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(y, x). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    using assms and typeII_twoCubeImg[of"twoC"] by auto
  have bottom_edge_explicit: "?bottom_edge = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  have right_edge_explicit: "?right_edge = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  have top_edge_explicit: "?top_edge = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  have left_edge_explicit: "?left_edge = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  show ?thesis
    using bottom_edge_explicit right_edge_explicit top_edge_explicit left_edge_explicit twoCisTypeII
    by auto
qed

lemma typeII_twoCube_smooth_edges:
  assumes "typeII_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "\<gamma> piecewise_C1_differentiable_on {0..1}"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(0, x))"
  let ?right_edge = "(\<lambda>y. twoC(y, 1))"
  let ?top_edge = "(\<lambda>x. twoC(1, x))"
  let ?left_edge = "(\<lambda>y. twoC(y, 0))"
  obtain a b g1 g2 where
    twoCisTypeII: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(y, x). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    "(\<lambda>x. twoC(0, x)) = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))"
    "(\<lambda>y. twoC(y, 1)) = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))"
    "(\<lambda>x. twoC(1, x)) = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))"
    "(\<lambda>y. twoC(y, 0)) = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
    using assms and typeII_cube_explicit_spec[of"twoC"]
    by auto
  have bottom_edge_smooth: "?bottom_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x)) -` {x} = {(x - a)/(b -a)}"
      using twoCisTypeII(1)  by auto
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" 
      using scale_shift_smooth C1_differentiable_imp_piecewise by blast
    have g2_smooth: "g2 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeII(1)] twoCisTypeII(6) by auto
    have "(\<lambda>x. g2 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g2_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x::real. (g2 (a + (b - a) * x), a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x::real. (g2 (a + (b - a) * x), a + (b - a) * x))"]
      by (fastforce simp add: real_pair_basis)
    then show ?thesis using twoCisTypeII(7) by auto
  qed
  have top_edge_smooth: "?top_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x))-` {x} = {(x - a)/(b -a)}"
      using twoCisTypeII(1) by auto
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" 
      using scale_shift_smooth C1_differentiable_imp_piecewise by blast
    have g1_smooth: "g1 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeII(1)] twoCisTypeII(5) by auto
    have "(\<lambda>x. g1 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g1_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x::real. (g1 (a + (b - a) * x), a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x::real. (g1 (a + (b - a) * x), a + (b - a) * x))"]
      by (fastforce simp add: real_pair_basis)
    then show ?thesis using twoCisTypeII(9) by auto
  qed
  have right_edge_smooth: "?right_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "(\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b))) piecewise_C1_differentiable_on {0..1}"
      by (simp add: C1_differentiable_imp_piecewise)
    then have "(\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b)) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[of "(1,0)" "(\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))"]
      by (auto simp add: real_pair_basis)
    then show ?thesis
      using twoCisTypeII(8) by auto
  qed
  have left_edge_smooth: "?left_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have 0: "(\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a))) C1_differentiable_on {0..1}"
      using C1_differentiable_imp_piecewise by fastforce
    have "(\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a)) piecewise_C1_differentiable_on {0..1}"
      using C1_differentiable_imp_piecewise[OF C1_differentiable_on_pair[OF 0 C1_differentiable_on_const[of "a" "{0..1}"]]]
      by force
    then show ?thesis
      using twoCisTypeII(10) by auto
  qed
  have "\<gamma> = ?bottom_edge \<or> \<gamma> = ?right_edge \<or> \<gamma> = ?top_edge \<or> \<gamma> = ?left_edge"
    using assms by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  then show ?thesis
    using left_edge_smooth right_edge_smooth top_edge_smooth bottom_edge_smooth by auto
qed

lemma field_cont_on_typeII_region_cont_on_edges:
  assumes typeII_twoC:
    "typeII_twoCube twoC" and
    field_cont:
    "continuous_on (cubeImage twoC) F" and
    member_of_boundary:
    "(k,\<gamma>) \<in> boundary twoC"
  shows "continuous_on (\<gamma> ` {0 .. 1}) F"
proof -
  obtain a b g1 g2 where
    twoCisTypeII: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(y, x). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    "(\<lambda>x. twoC(0, x)) = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))"
    "(\<lambda>y. twoC(y, 1)) = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))"
    "(\<lambda>x. twoC(1, x)) = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))"
    "(\<lambda>y. twoC(y, 0)) = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
    using typeII_twoC and typeII_cube_explicit_spec[of"twoC"]
    by auto
  let ?bottom_edge = "(\<lambda>x. twoC(0, x))"
  let ?right_edge = "(\<lambda>y. twoC(y, 1))"
  let ?top_edge = "(\<lambda>x. twoC(1, x))"
  let ?left_edge = "(\<lambda>y. twoC(y, 0))"
  let ?Dg1 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (g1(x), x)}"
  have line_is_pair_img: "?Dg1 = (\<lambda>x. (g1(x), x)) ` (cbox a b)"
    using image_def by auto
  have field_cont_on_top_edge_image: "continuous_on ?Dg1 F"
    by (rule continuous_on_subset [OF field_cont]) (auto simp: twoCisTypeII(2) twoCisTypeII(3))
  have top_edge_is_compos_of_scal_and_g1:
    "(\<lambda>x. twoC(1, x)) = (\<lambda>x. (g1(x), x)) \<circ> (\<lambda>x. a + (b - a) * x)"
    using twoCisTypeII by auto
  have Dg1_is_bot_edge_pathimg:
    "path_image (\<lambda>x. twoC(1, x)) = ?Dg1"
    using line_is_pair_img and top_edge_is_compos_of_scal_and_g1 image_comp path_image_def add_scale_img and twoCisTypeII(1)
    by (metis (no_types, lifting) cbox_interval)
  then have cont_on_top: "continuous_on (path_image ?top_edge) F"
    using field_cont_on_top_edge_image by auto
  let ?Dg2 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (g2(x), x)}"
  have line_is_pair_img: "?Dg2 = (\<lambda>x. (g2(x), x)) ` (cbox a b)"
    using image_def by auto
  have field_cont_on_bot_edge_image: "continuous_on ?Dg2 F"
    by (rule continuous_on_subset [OF field_cont]) (auto simp add: twoCisTypeII(2) twoCisTypeII(3))
  have bot_edge_is_compos_of_scal_and_g2:
    "(\<lambda>x. twoC(0, x)) = (\<lambda>x. (g2(x), x)) \<circ> (\<lambda>x. a + (b - a) * x)"
    using twoCisTypeII by auto
  have Dg2_is_bot_edge_pathimg: "path_image (\<lambda>x. twoC(0, x)) = ?Dg2"
    unfolding path_image_def
    using line_is_pair_img and bot_edge_is_compos_of_scal_and_g2 image_comp  add_scale_img [OF \<open>a < b\<close>]
    by (metis (no_types, lifting) box_real(2))
  then have cont_on_bot: "continuous_on (path_image ?bottom_edge) F"
    using field_cont_on_bot_edge_image
    by auto
  let ?D_left_edge =  "{p. \<exists>y. y \<in> cbox (g2 a) (g1 a) \<and> p = (y, a)}"
  have field_cont_on_left_edge_image: "continuous_on ?D_left_edge F"
    apply (rule continuous_on_subset [OF field_cont])
    using twoCisTypeII(1) twoCisTypeII(3) by auto
  have "g2 a \<le> g1 a" using twoCisTypeII(1) twoCisTypeII(2) by auto
  then have "(\<lambda>x. g2 a + x * (g1 a - g2 a)) ` {(0::real)..1} = {g2 a .. g1 a}"
    using add_scale_img'[of "g2 a" "g1 a"] by (auto simp add: ac_simps)
  with \<open>g2 a \<le> g1 a\<close> have left_eq: "?D_left_edge = ?left_edge ` {0..1}"
    by (simp only: twoCisTypeII(10)) auto
  then have cont_on_left: "continuous_on (path_image ?left_edge) F"
    using field_cont_on_left_edge_image path_image_def
    by (metis left_eq field_cont_on_left_edge_image path_image_def)
  let ?D_right_edge = "{p. \<exists>y. y \<in> cbox (g2 b) (g1 b) \<and> p = (y, b)}"
  have field_cont_on_left_edge_image: "continuous_on ?D_right_edge F"
    apply (rule continuous_on_subset [OF field_cont])
    using twoCisTypeII(1) twoCisTypeII(3) by auto
  have "g2 b \<le> g1 b" using twoCisTypeII(1) twoCisTypeII(2) by auto
  then have "(\<lambda>x. g2 b + x * (g1 b - g2 b)) ` {(0::real)..1} = {g2 b .. g1 b}"
    using add_scale_img'[of "g2 b" "g1 b"] by (auto simp add: ac_simps)
  with \<open>g2 b \<le> g1 b\<close> have right_eq: "?D_right_edge = ?right_edge ` {0..1}"
    by (simp only: twoCisTypeII(8)) auto
  then have cont_on_right:
    "continuous_on (path_image ?right_edge) F"
    using field_cont_on_left_edge_image path_image_def
    by (metis right_eq field_cont_on_left_edge_image path_image_def)
  have all_edge_cases:
    "(\<gamma> = ?bottom_edge \<or> \<gamma> = ?right_edge \<or> \<gamma> = ?top_edge \<or> \<gamma> = ?left_edge)"
    using assms unfolding boundary_def horizontal_boundary_def vertical_boundary_def by blast
  show ?thesis
    apply (simp add: path_image_def[symmetric])
    using cont_on_top cont_on_bot cont_on_right cont_on_left all_edge_cases
    by blast
qed

lemma two_cube_boundary_is_boundary: "boundary_chain (boundary C)"
  by (auto simp add: boundary_chain_def boundary_def horizontal_boundary_def vertical_boundary_def)

lemma common_boundary_subdiv_exists_refl:
  assumes "\<forall>(k,\<gamma>)\<in>boundary twoC. valid_path \<gamma>"
  shows "common_boundary_sudivision_exists (boundary twoC) (boundary twoC)"
  using assms chain_subdiv_chain_refl common_boundary_sudivision_exists_def two_cube_boundary_is_boundary by blast

lemma common_boundary_subdiv_exists_refl':
  assumes "\<forall>(k,\<gamma>)\<in>C. valid_path \<gamma>"
    "boundary_chain (C::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
  shows "common_boundary_sudivision_exists (C) (C)"
  using assms chain_subdiv_chain_refl common_boundary_sudivision_exists_def by blast

lemma gen_common_boundary_subdiv_exists_refl_twochain_boundary:
  assumes "\<forall>(k,\<gamma>)\<in>C. valid_path \<gamma>"
    "boundary_chain (C::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
  shows "common_sudiv_exists (C) (C)"
  using assms chain_subdiv_chain_refl common_boundary_sudivision_exists_def common_subdiv_imp_gen_common_subdiv by blast

lemma two_chain_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_boundary twoChain)"
  by (simp add: boundary_chain_def two_chain_boundary_def boundary_def horizontal_boundary_def vertical_boundary_def)

lemma typeI_edges_are_valid_paths:
  assumes "typeI_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "valid_path \<gamma>"
  using typeI_twoCube_smooth_edges[OF assms] C1_differentiable_imp_piecewise
  by (auto simp: valid_path_def)

lemma typeII_edges_are_valid_paths:
  assumes "typeII_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "valid_path \<gamma>"
  using typeII_twoCube_smooth_edges[OF assms] C1_differentiable_imp_piecewise
  by (auto simp: valid_path_def)

lemma finite_two_chain_vertical_boundary:
  assumes "finite two_chain"
  shows "finite (two_chain_vertical_boundary two_chain)"
  using assms  by (simp add: two_chain_vertical_boundary_def vertical_boundary_def)

lemma finite_two_chain_horizontal_boundary:
  assumes "finite two_chain"
  shows "finite (two_chain_horizontal_boundary two_chain)"
  using assms  by (simp add: two_chain_horizontal_boundary_def horizontal_boundary_def)

locale R2 =
  fixes i j
  assumes i_is_x_axis: "i = (1::real,0::real)" and
    j_is_y_axis: "j = (0::real, 1::real)"
begin

lemma analytically_valid_y:
  assumes "analytically_valid s F i"
  shows "(\<lambda>x. integral UNIV (\<lambda>y. (partial_vector_derivative F i) (y, x) * (indicator s (y, x)))) \<in> borel_measurable lborel"
proof -
  have "{(1::real, 0::real), (0, 1)} - {(1, 0)} = {(0::real,1::real)}"
    by force
  with assms show ?thesis
    using assms  by(simp add: real_pair_basis analytically_valid_def i_is_x_axis j_is_y_axis)
qed

lemma analytically_valid_x:
  assumes "analytically_valid s F j"
  shows "(\<lambda>x. integral UNIV (\<lambda>y. ((partial_vector_derivative F j) (x, y)) * (indicator s (x, y)))) \<in> borel_measurable lborel"
proof -
  have "{(1::real, 0::real), (0, 1)} - {(0, 1)} = {(1::real, 0::real)}"
    by force
  with assms show ?thesis
    by(simp add: real_pair_basis analytically_valid_def i_is_x_axis j_is_y_axis)
qed

lemma Greens_thm_type_I:
  fixes F:: "((real*real) \<Rightarrow> (real * real))" and
    gamma1 gamma2 gamma3 gamma4 :: "(real \<Rightarrow> (real * real))" and
    a:: "real" and b:: "real" and
    g1:: "(real \<Rightarrow> real)" and g2:: "(real \<Rightarrow> real)"
  assumes Dy_def: "Dy_pair = {(x::real,y) . x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}" and
    gamma1_def: "gamma1 = (\<lambda>x. (a + (b - a) * x, g2(a + (b - a) * x)))" and
    gamma1_smooth: "gamma1 piecewise_C1_differentiable_on {0..1}" and (*TODO: This should be piecewise smooth*)
    gamma2_def: "gamma2 = (\<lambda>x. (b, g2(b) + x  *\<^sub>R (g1(b) - g2(b))))" and
    gamma3_def: "gamma3 = (\<lambda>x. (a + (b - a) * x, g1(a + (b - a) * x)))" and
    gamma3_smooth: "gamma3 piecewise_C1_differentiable_on {0..1}" and
    gamma4_def: "gamma4 = (\<lambda>x. (a,  g2(a) + x *\<^sub>R (g1(a) - g2(a))))" and
    F_i_analytically_valid: "analytically_valid Dy_pair (\<lambda>p. F(p) \<bullet> i) j" and
    g2_leq_g1: "\<forall>x \<in> cbox a b. (g2 x) \<le> (g1 x)" and (*This is needed otherwise what would Dy be?*)
    a_lt_b: "a < b"
  shows "(line_integral F {i} gamma1) +
         (line_integral F {i} gamma2) -
         (line_integral F {i} gamma3) -
         (line_integral F {i} gamma4)
                 = (integral Dy_pair (\<lambda>a. - (partial_vector_derivative (\<lambda>p. F(p) \<bullet> i) j a)))"
    "line_integral_exists F {i} gamma4"
    "line_integral_exists F {i} gamma3"
    "line_integral_exists F {i} gamma2"
    "line_integral_exists F {i} gamma1"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>a. (F a) \<bullet> i)  j"
  have F_first_is_continuous: "continuous_on Dy_pair (\<lambda>a. F(a) \<bullet> i)"
    using F_i_analytically_valid
    by (auto simp add: analytically_valid_def)
  let ?f = "(\<lambda>x. if x \<in> (Dy_pair) then (partial_vector_derivative (\<lambda>a. (F a) \<bullet> i)  j) x else 0)"
  have f_lesbegue_integrable: "integrable lborel ?f"
    using F_i_analytically_valid
    by (auto simp add: analytically_valid_def indic_ident)
  have partially_vec_diff: "\<forall>a \<in> Dy_pair. partially_vector_differentiable (\<lambda>a. (F a) \<bullet> i) j a"
    using F_i_analytically_valid
    by (auto simp add: analytically_valid_def indicator_def)
  have x_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. ?f(x, y))) \<in> borel_measurable lborel"
  proof -
    have "(\<lambda>p. (?F_b' p) * indicator (Dy_pair) p) = (\<lambda>x. if x \<in> (Dy_pair) then (?F_b') x else 0)"
      using indic_ident[of "?F_b'"] by auto
    then have "\<And>x y. ?F_b' (x,y) * indicator (Dy_pair) (x,y) = (\<lambda>x. if x \<in> (Dy_pair) then (?F_b') x else 0) (x,y)"
      by auto
    then show ?thesis
      using analytically_valid_x[OF F_i_analytically_valid]
      by (auto simp add: indicator_def)
  qed
  have F_partially_differentiable: "\<forall>a\<in>Dy_pair. has_partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j (?F_b' a) a"
    using partial_vector_derivative_works partially_vec_diff
    by fastforce
  have g1_g2_continuous: "continuous_on (cbox a b) g1"
    "continuous_on (cbox a b) g2"
  proof -
    have shift_scale_cont: "continuous_on {a..b} (\<lambda>x. (x - a)*(1/(b-a)))"
      by (intro continuous_intros)
    have shift_scale_inv: "(\<lambda>x. a + (b - a) * x) \<circ> (\<lambda>x. (x - a)*(1/(b-a))) = id"
      using a_lt_b by (auto simp add: o_def)
    have img_shift_scale: "(\<lambda>x. (x - a)*(1/(b-a)))`{a..b} = {0..1}"
      using a_lt_b apply (auto simp: divide_simps image_iff)
      apply (rule_tac x="x * (b - a) + a" in bexI)
      using le_diff_eq by fastforce+
    have gamma1_y_component: "(\<lambda>x. g2(a + (b - a) * x)) = g2 \<circ> (\<lambda>x.(a + (b - a) * x))"
      by auto
    have "continuous_on {0..1} (\<lambda>x. g2(a + (b - a) * x))"
      using continuous_on_inner[OF piecewise_C1_differentiable_on_imp_continuous_on[OF gamma1_smooth], of "(\<lambda>x. j)", OF continuous_on_const]
      by (simp add: gamma1_def j_is_y_axis)
    then have "continuous_on {a..b} ((\<lambda>x. g2(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using img_shift_scale continuous_on_compose shift_scale_cont
      by force
    then have "continuous_on {a..b} (g2 \<circ> (\<lambda>x.(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using gamma1_y_component by auto
    then show "continuous_on (cbox a b) g2"
      using a_lt_b by (simp add: shift_scale_inv)
    have gamma3_y_component: "(\<lambda>x. g1(a + (b - a) * x)) = g1 \<circ> (\<lambda>x.(a + (b - a) * x))"
      by auto
    have "continuous_on {0..1} (\<lambda>x. g1(a + (b - a) * x))"
      using continuous_on_inner[OF piecewise_C1_differentiable_on_imp_continuous_on[OF gamma3_smooth], of "(\<lambda>x. j)", OF continuous_on_const]
      by (simp add: gamma3_def j_is_y_axis)
    then have "continuous_on {a..b} ((\<lambda>x. g1(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using img_shift_scale continuous_on_compose shift_scale_cont
      by force
    then have "continuous_on {a..b} (g1 \<circ> (\<lambda>x.(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using gamma3_y_component by auto
    then show "continuous_on (cbox a b) g1"
      using a_lt_b by (simp add: shift_scale_inv)
  qed
  have g2_scale_j_contin: "continuous_on (cbox a b) (\<lambda>x. (0, g2 x))"
    by (intro continuous_intros g1_g2_continuous)
  let ?Dg2 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (x, g2(x))}"
  have line_is_pair_img: "?Dg2 = (\<lambda>x. (x, g2(x))) ` (cbox a b)"
    using image_def by auto
  have g2_path_continuous: "continuous_on (cbox a b) (\<lambda>x. (x, g2(x)))"
    by (intro continuous_intros g1_g2_continuous)
  have field_cont_on_gamma1_image: "continuous_on ?Dg2  (\<lambda>a. F(a) \<bullet> i)"
    apply (rule continuous_on_subset [OF F_first_is_continuous])
    by (auto simp add: Dy_def g2_leq_g1)
  have gamma1_is_compos_of_scal_and_g2:
    "gamma1 = (\<lambda>x. (x, g2(x))) \<circ> (\<lambda>x. a + (b - a) * x)"
    using gamma1_def by auto
  have add_scale_img:
    "(\<lambda>x. a + (b - a) * x) ` {0 .. 1} = {a .. b}" using add_scale_img and a_lt_b by auto
  then have Dg2_is_gamma1_pathimg: "path_image gamma1 = ?Dg2"
    by (metis (no_types, lifting) box_real(2) gamma1_is_compos_of_scal_and_g2 image_comp line_is_pair_img path_image_def)
  have Base_vecs: "i \<in> Basis" "j \<in> Basis" "i \<noteq> j"
    using real_pair_basis and i_is_x_axis and j_is_y_axis by auto
  have gamma1_as_euclid_space_fun: "gamma1 = (\<lambda>x. (a + (b - a) * x) *\<^sub>R i + (0, g2 (a + (b - a) * x)))"
    using i_is_x_axis gamma1_def by auto
  have 0: "line_integral F {i} gamma1 = integral (cbox a b) (\<lambda>x. F(x, g2(x)) \<bullet> i )"
          "line_integral_exists F {i} gamma1"
    using line_integral_on_pair_path_strong [OF norm_Basis[OF Base_vecs(1)] _ gamma1_as_euclid_space_fun, of "F"] 
      gamma1_def gamma1_smooth g2_scale_j_contin a_lt_b add_scale_img
      Dg2_is_gamma1_pathimg and field_cont_on_gamma1_image
    by (auto simp: pathstart_def pathfinish_def i_is_x_axis)
  then show "(line_integral_exists F {i} gamma1)" by metis
  have gamma2_x_const: "\<forall>x. gamma2 x \<bullet> i = b"
    by (simp add: i_is_x_axis gamma2_def)
  have 1: "(line_integral F {i} gamma2) = 0" "(line_integral_exists F {i} gamma2)"
      using line_integral_on_pair_straight_path[OF gamma2_x_const] straight_path_diffrentiable_x gamma2_def
      by (auto simp add: mult.commute)
  then show "(line_integral_exists F {i} gamma2)" by metis
  have "continuous_on (cbox a b) (\<lambda>x. F(x, g2(x))  \<bullet> i)"
    using line_is_pair_img and g2_path_continuous and field_cont_on_gamma1_image
      Topological_Spaces.continuous_on_compose i_is_x_axis j_is_y_axis
    by auto
  then have 6: "(\<lambda>x. F(x, g2(x))  \<bullet> i) integrable_on (cbox a b)"
    using integrable_continuous [of "a" "b" "(\<lambda>x. F(x, g2(x))  \<bullet> i)"] by auto
  have g1_scale_j_contin: "continuous_on (cbox a b) (\<lambda>x. (0, g1 x))"
    by (intro continuous_intros g1_g2_continuous)
  let ?Dg1 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (x, g1(x))}"
  have line_is_pair_img: "?Dg1 = (\<lambda>x. (x, g1(x)) ) ` (cbox a b)"
    using image_def  by auto
  have g1_path_continuous: "continuous_on (cbox a b) (\<lambda>x. (x, g1(x)))"
    by (intro continuous_intros g1_g2_continuous)
  have field_cont_on_gamma3_image: "continuous_on ?Dg1  (\<lambda>a. F(a)  \<bullet> i)"
    apply (rule continuous_on_subset [OF F_first_is_continuous])
    by (auto simp add: Dy_def g2_leq_g1)
  have gamma3_is_compos_of_scal_and_g1:
    "gamma3 = (\<lambda>x. (x, g1(x))) \<circ> (\<lambda>x. a + (b - a) * x)"
    using gamma3_def by auto
  then have Dg1_is_gamma3_pathimg: "path_image gamma3 = ?Dg1"
    by (metis (no_types, lifting) box_real(2) image_comp line_is_pair_img local.add_scale_img path_image_def)
  have Base_vecs: "i \<in> Basis" "j \<in> Basis" "i \<noteq> j"
    using real_pair_basis and i_is_x_axis and j_is_y_axis by auto
  have gamma3_as_euclid_space_fun: "gamma3 = (\<lambda>x. (a + (b - a) * x) *\<^sub>R i + (0, g1 (a + (b - a) * x)))"
    using i_is_x_axis gamma3_def by auto
  have 2: "line_integral F {i} gamma3 = integral (cbox a b) (\<lambda>x. F(x, g1(x)) \<bullet> i )"
         "line_integral_exists F {i} gamma3"
    using line_integral_on_pair_path_strong [OF norm_Basis[OF Base_vecs(1)] _ gamma3_as_euclid_space_fun, of "F"]
      gamma3_def and gamma3_smooth and g1_scale_j_contin and a_lt_b and add_scale_img
      Dg1_is_gamma3_pathimg and field_cont_on_gamma3_image
    by (auto simp: pathstart_def pathfinish_def i_is_x_axis)
  then show "(line_integral_exists F {i} gamma3)" by metis
  have gamma4_x_const: "\<forall>x. gamma4 x \<bullet> i = a"
    using gamma4_def
    by (auto simp add: real_inner_class.inner_add_left inner_not_same_Basis  i_is_x_axis)
  have 3: "(line_integral F {i} gamma4) = 0" "(line_integral_exists F {i} gamma4)"
    using line_integral_on_pair_straight_path[OF gamma4_x_const] straight_path_diffrentiable_x gamma4_def
    by (auto simp add: mult.commute)
  then show "(line_integral_exists F {i} gamma4)" 
    by metis
  have "continuous_on (cbox a b) (\<lambda>x. F(x, g1(x)) \<bullet> i)"
    using line_is_pair_img and g1_path_continuous and field_cont_on_gamma3_image
      continuous_on_compose i_is_x_axis j_is_y_axis
    by auto
  then have 7: "(\<lambda>x. F(x, g1(x))  \<bullet> i) integrable_on (cbox a b)"
    using integrable_continuous [of "a" "b" "(\<lambda>x. F(x, g1(x))  \<bullet> i)"]
    by auto
  have partial_deriv_one_d_integrable:
    "((\<lambda>y. ?F_b'(xc, y)) has_integral 
        F(xc,g1(xc)) \<bullet> i - F(xc, g2(xc)) \<bullet> i) (cbox (g2 xc) (g1 xc))" 
     if "xc \<in> cbox a b" for xc
  proof -
    have "{(xc', y).  y \<in> cbox (g2 xc) (g1 xc) \<and> xc' = xc} \<subseteq> Dy_pair"
      using that by (auto simp add: Dy_def)
    then show "((\<lambda>y. ?F_b' (xc, y)) has_integral F(xc, g1 xc) \<bullet> i - F(xc, g2 xc) \<bullet> i) (cbox (g2 xc) (g1 xc))"
      using that and Base_vecs and F_partially_differentiable
        and Dy_def [symmetric] and g2_leq_g1
        and fundamental_theorem_of_calculus_partial_vector
        [of "g2 xc" "g1 xc" "j" "i" "xc *\<^sub>R i" "Dy_pair" "F" "?F_b'" ]
      by (auto simp add:  Groups.ab_semigroup_add_class.add.commute i_is_x_axis j_is_y_axis)
  qed
  have partial_deriv_integrable: "(?F_b') integrable_on Dy_pair"
    by (simp add: F_i_analytically_valid analytically_valid_imp_part_deriv_integrable_on)
  have 4: "integral Dy_pair ?F_b'
           = integral (cbox a b) (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. ?F_b' (x, y)))"
  proof -
    have x_axis_gauge_integrable:
      "\<And>x. (\<lambda>y. ?f(x,y)) integrable_on UNIV"
    proof -
      fix x::real
      have "\<forall>x. x \<notin> cbox a b \<longrightarrow>  (\<lambda>y. ?f (x, y)) = (\<lambda>y. 0)"
        by (auto simp add: Dy_def)
      then have f_integrable_x_not_in_range:
        "\<forall>x. x \<notin> cbox a b \<longrightarrow>  (\<lambda>y. ?f (x, y)) integrable_on UNIV"
        by (simp add: integrable_0)
      let ?F_b'_oneD = "(\<lambda>x. (\<lambda>y. if y \<in> (cbox (g2 x) ( g1 x)) then ?F_b' (x,y) else 0))"
      have f_value_x_in_range: "\<forall>x \<in> cbox a b. ?F_b'_oneD x = (\<lambda>y. ?f(x,y))"
        by (auto simp add: Dy_def)
      have "\<forall>x \<in> cbox a b. ?F_b'_oneD x integrable_on UNIV"
        using has_integral_integrable integrable_restrict_UNIV partial_deriv_one_d_integrable by blast
      then have f_integrable_x_in_range:
        "\<forall>x. x \<in> cbox a b \<longrightarrow>  (\<lambda>y. ?f (x, y)) integrable_on UNIV"
        using f_value_x_in_range by auto
      show "(\<lambda>y. ?f (x, y)) integrable_on UNIV"
        using f_integrable_x_not_in_range and f_integrable_x_in_range by auto
    qed
    have arg: "(\<lambda>a. if a \<in> Dy_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> i) j a else 0) =
               (\<lambda>x. if x \<in> Dy_pair then if x \<in> Dy_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x else 0 else 0)"
      by auto
    have arg2: "Dy_pair = {(x, y). (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and> (\<forall>i\<in>Basis. g2 x \<bullet> i \<le> y \<bullet> i \<and> y \<bullet> i \<le> g1 x \<bullet> i)}"
      using Dy_def  by auto
    have arg3: "\<And> x. x \<in> Dy_pair \<Longrightarrow> (\<lambda>x. if x \<in> Dy_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x else 0) x
                           = (\<lambda>x. partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x) x"
      by auto
    have arg4: "\<And>x. x \<in> (cbox a b) \<Longrightarrow>
                            (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. if (x, y) \<in> Dy_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> i) j (x, y) else 0)) x =
                                      (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. partial_vector_derivative (\<lambda>a. F a \<bullet> i) j (x, y))) x"
      apply (simp add: Dy_def)
      by (smt Henstock_Kurzweil_Integration.integral_cong atLeastAtMost_iff)
    show ?thesis
      using gauge_integral_Fubini_curve_bounded_region_x
        [OF f_lesbegue_integrable x_axis_gauge_integrable x_axis_integral_measurable arg arg2]
        Henstock_Kurzweil_Integration.integral_cong[OF arg3, of "Dy_pair" "(\<lambda>x. x)"]
        Henstock_Kurzweil_Integration.integral_cong[OF arg4, of "cbox a b" "(\<lambda>x. x)"]
      by auto
  qed
  have 5: "(integral Dy_pair (\<lambda>a. (?F_b' a))
        = integral (cbox a b) (\<lambda>x. F(x, g1(x))  \<bullet> i - F(x, g2(x))  \<bullet> i))"
    using 4 Henstock_Kurzweil_Integration.integral_cong partial_deriv_one_d_integrable integrable_def
    by (smt integral_unique)
  show "(line_integral F {i} gamma1) + (line_integral F {i} gamma2) -
          (line_integral F {i} gamma3) - (line_integral F {i} gamma4)
        = (integral Dy_pair (\<lambda>a. - (?F_b' a)))"
    using "0"(1) "1"(1) "2"(1) "3"(1) 5 "6" "7" 
    by (simp add: Henstock_Kurzweil_Integration.integral_diff)    
qed

theorem Greens_thm_type_II:
  fixes F:: "((real*real) \<Rightarrow> (real * real))" and
    gamma4 gamma3 gamma2 gamma1 :: "(real \<Rightarrow> (real * real))" and
    a:: "real" and b:: "real" and
    g1:: "(real \<Rightarrow> real)" and g2:: "(real \<Rightarrow> real)"
  assumes Dx_def: "Dx_pair = {(x::real,y) . y \<in> cbox a b \<and> x \<in> cbox (g2 y) (g1 y)}" and
    gamma4_def: "gamma4 = (\<lambda>x. (g2(a + (b - a) * x), a + (b - a) * x))" and
    gamma4_smooth: "gamma4 piecewise_C1_differentiable_on {0..1}" and (*TODO: This should be piecewise smooth*)
    gamma3_def: "gamma3 = (\<lambda>x. (g2(b) + x  *\<^sub>R (g1(b) - g2(b)), b))" and
    gamma2_def: "gamma2 = (\<lambda>x. (g1(a + (b - a) * x), a + (b - a) * x))" and
    gamma2_smooth: "gamma2 piecewise_C1_differentiable_on {0..1}" and
    gamma1_def: "gamma1 = (\<lambda>x. (g2(a) + x *\<^sub>R (g1(a) - g2(a)), a))" and
    F_j_analytically_valid: "analytically_valid Dx_pair (\<lambda>p. F(p) \<bullet> j) i" and
    g2_leq_g1: "\<forall>x \<in> cbox a b. (g2 x) \<le> (g1 x)" and (*This is needed otherwise what would Dy be?*)
    a_lt_b: "a < b"
  shows "-(line_integral F {j} gamma4) -
         (line_integral F {j} gamma3) +
         (line_integral F {j} gamma2) +
         (line_integral F {j} gamma1)
                 = (integral Dx_pair (\<lambda>a. (partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i a)))"
    "line_integral_exists F {j} gamma4"
    "line_integral_exists F {j} gamma3"
    "line_integral_exists F {j} gamma2"
    "line_integral_exists F {j} gamma1"
proof -
  let ?F_a' = "partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i"
  have F_first_is_continuous: "continuous_on Dx_pair (\<lambda>a. F(a) \<bullet> j)"
    using F_j_analytically_valid
    by (auto simp add: analytically_valid_def)
  let ?f = "(\<lambda>x. if x \<in> (Dx_pair) then (partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i) x else 0)"
  have f_lesbegue_integrable: "integrable lborel ?f"
    using F_j_analytically_valid
    by (auto simp add: analytically_valid_def indic_ident)
  have partially_vec_diff: "\<forall>a \<in> Dx_pair. partially_vector_differentiable (\<lambda>a. (F a) \<bullet> j) i a"
    using F_j_analytically_valid
    by (auto simp add: analytically_valid_def indicator_def)
  have "\<And>x y. ?F_a' (x,y) * indicator (Dx_pair) (x,y) = (\<lambda>x. if x \<in> (Dx_pair) then ?F_a' x else 0) (x,y)"
    using indic_ident[of "?F_a'"] by auto
  then have y_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. ?f(y, x))) \<in> borel_measurable lborel"
    using analytically_valid_y[OF F_j_analytically_valid]
    by (auto simp add: indicator_def)
  have F_partially_differentiable: "\<forall>a\<in>Dx_pair. has_partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i (?F_a' a) a"
    using partial_vector_derivative_works partially_vec_diff by fastforce
  have g1_g2_continuous: "continuous_on (cbox a b) g1" "continuous_on (cbox a b) g2"
  proof -
    have shift_scale_cont: "continuous_on {a..b} (\<lambda>x. (x - a)*(1/(b-a)))"
      by (intro continuous_intros)
    have shift_scale_inv: "(\<lambda>x. a + (b - a) * x) \<circ> (\<lambda>x. (x - a)*(1/(b-a))) = id"
      using a_lt_b by (auto simp add: o_def)
    have img_shift_scale:
      "(\<lambda>x. (x - a)*(1/(b-a)))`{a..b} = {0..1}"
      apply (auto simp: divide_simps image_iff)
       apply (rule_tac x="x * (b - a) + a" in bexI)
      using a_lt_b by (auto simp: algebra_simps mult_le_cancel_left affine_ineq)
    have "continuous_on {0..1} (\<lambda>x. g2(a + (b - a) * x))"
      using continuous_on_inner[OF piecewise_C1_differentiable_on_imp_continuous_on[OF gamma4_smooth], of "(\<lambda>x. i)", OF continuous_on_const]
      by (simp add: gamma4_def i_is_x_axis)
    then have "continuous_on {a..b} ((\<lambda>x. g2(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using img_shift_scale continuous_on_compose shift_scale_cont by force
    then show "continuous_on (cbox a b) g2"
      using a_lt_b by (simp add: shift_scale_inv)
    have "continuous_on {0..1} (\<lambda>x. g1(a + (b - a) * x))"
      using continuous_on_inner[OF piecewise_C1_differentiable_on_imp_continuous_on[OF gamma2_smooth], of "(\<lambda>x. i)", OF continuous_on_const]
      by (simp add: gamma2_def i_is_x_axis)
    then have "continuous_on {a..b} ((\<lambda>x. g1(a + (b - a) * x)) \<circ> (\<lambda>x. (x - a)*(1/(b-a))))"
      using img_shift_scale continuous_on_compose shift_scale_cont by force
    then show "continuous_on (cbox a b) g1"
      using a_lt_b by (simp add: shift_scale_inv)
  qed
  have g2_scale_i_contin: "continuous_on (cbox a b) (\<lambda>x. (g2 x, 0))"
    by (intro continuous_intros g1_g2_continuous)
  let ?Dg2 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (g2(x), x)}"
  have line_is_pair_img: "?Dg2 = (\<lambda>x. (g2(x), x) ) ` (cbox a b)"
    using image_def  by auto
  have g2_path_continuous: "continuous_on (cbox a b) (\<lambda>x. (g2(x), x))"
    by (intro continuous_intros g1_g2_continuous)
  have field_cont_on_gamma4_image: "continuous_on ?Dg2 (\<lambda>a. F(a) \<bullet> j)"
    by (rule continuous_on_subset [OF F_first_is_continuous]) (auto simp: Dx_def g2_leq_g1)
  have gamma4_is_compos_of_scal_and_g2: "gamma4 = (\<lambda>x. (g2(x), x)) \<circ> (\<lambda>x. a + (b - a) * x)"
    using gamma4_def  by auto
  have add_scale_img:
    "(\<lambda>x. a + (b - a) * x) ` {0 .. 1} = {a .. b}" using add_scale_img and a_lt_b by auto
  then have Dg2_is_gamma4_pathimg: "path_image gamma4 = ?Dg2"
    using line_is_pair_img and gamma4_is_compos_of_scal_and_g2 image_comp path_image_def
    by (metis (no_types, lifting) cbox_interval)
  have Base_vecs: "i \<in> Basis" "j \<in> Basis" "i \<noteq> j"
    using real_pair_basis and i_is_x_axis and j_is_y_axis by auto
  have gamma4_as_euclid_space_fun: "gamma4 = (\<lambda>x. (a + (b - a) * x) *\<^sub>R j + (g2 (a + (b - a) * x), 0))"
    using j_is_y_axis gamma4_def
    by auto
  have 0: "(line_integral F {j} gamma4) = integral (cbox a b) (\<lambda>x. F(g2(x), x) \<bullet> j)"
          "line_integral_exists F {j} gamma4"
    using line_integral_on_pair_path_strong [OF norm_Basis[OF Base_vecs(2)] _ gamma4_as_euclid_space_fun]
      gamma4_def gamma4_smooth g2_scale_i_contin a_lt_b add_scale_img
      Dg2_is_gamma4_pathimg and field_cont_on_gamma4_image
    by (auto simp: pathstart_def pathfinish_def j_is_y_axis)
  then show "line_integral_exists F {j} gamma4" by metis
  have gamma3_y_const: "\<forall>x. gamma3 x \<bullet> j = b"
    by (simp add: gamma3_def j_is_y_axis)
  have 1: "(line_integral F {j} gamma3) = 0" "(line_integral_exists F {j} gamma3)"
    using line_integral_on_pair_straight_path[OF gamma3_y_const] straight_path_diffrentiable_y gamma3_def
    by (auto simp add: mult.commute)
  then show "line_integral_exists F {j} gamma3" by auto
  have "continuous_on (cbox a b) (\<lambda>x. F(g2(x), x) \<bullet> j)"
    by (smt Collect_mono_iff continuous_on_compose2 continuous_on_eq field_cont_on_gamma4_image g2_path_continuous line_is_pair_img)
  then have 6: "(\<lambda>x. F(g2(x), x)  \<bullet> j) integrable_on (cbox a b)"
    using integrable_continuous by blast
  have g1_scale_i_contin: "continuous_on (cbox a b) (\<lambda>x. (g1 x, 0))"
    by (intro continuous_intros g1_g2_continuous)
  let ?Dg1 =  "{p. \<exists>x. x \<in> cbox a b \<and> p = (g1(x), x)}"
  have line_is_pair_img: "?Dg1 = (\<lambda>x. (g1(x), x) ) ` (cbox a b)"
    using image_def by auto
  have g1_path_continuous: "continuous_on (cbox a b) (\<lambda>x. (g1(x), x))"
    by (intro continuous_intros g1_g2_continuous)
  have field_cont_on_gamma2_image: "continuous_on ?Dg1  (\<lambda>a. F(a) \<bullet> j)"
    by (rule continuous_on_subset [OF F_first_is_continuous]) (auto simp: Dx_def g2_leq_g1)
  have "gamma2 = (\<lambda>x. (g1(x), x)) \<circ> (\<lambda>x. a + (b - a) * x)"
    using gamma2_def by auto
  then have Dg1_is_gamma2_pathimg: "path_image gamma2 = ?Dg1"
    using line_is_pair_img image_comp path_image_def add_scale_img
    by (metis (no_types, lifting) cbox_interval)
  have Base_vecs: "i \<in> Basis" "j \<in> Basis" "i \<noteq> j"
    using real_pair_basis and i_is_x_axis and j_is_y_axis by auto
  have gamma2_as_euclid_space_fun: "gamma2 = (\<lambda>x. (a + (b - a) * x) *\<^sub>R j + (g1 (a + (b - a) * x), 0))"
    using j_is_y_axis gamma2_def by auto
  have 2: "(line_integral F {j} gamma2) = integral (cbox a b) (\<lambda>x. F(g1(x), x) \<bullet> j)"
    "(line_integral_exists F {j} gamma2)"
    using line_integral_on_pair_path_strong [OF norm_Basis[OF Base_vecs(2)] _ gamma2_as_euclid_space_fun]
      gamma2_def and gamma2_smooth and g1_scale_i_contin and a_lt_b and add_scale_img
      Dg1_is_gamma2_pathimg and field_cont_on_gamma2_image
    by (auto simp: pathstart_def pathfinish_def j_is_y_axis)
  then show "line_integral_exists F {j} gamma2" by metis
  have gamma1_y_const: "\<forall>x. gamma1 x \<bullet> j = a"
    using gamma1_def
    by (auto simp add: real_inner_class.inner_add_left
        euclidean_space_class.inner_not_same_Basis j_is_y_axis)
  have 3: "(line_integral F {j} gamma1) = 0" "(line_integral_exists F {j} gamma1)"
    using line_integral_on_pair_straight_path[OF gamma1_y_const] straight_path_diffrentiable_y gamma1_def
    by (auto simp add: mult.commute)
  then show "line_integral_exists F {j} gamma1" by auto
  have "continuous_on (cbox a b) (\<lambda>x. F(g1(x), x) \<bullet> j)"
    by (smt Collect_mono_iff continuous_on_compose2 continuous_on_eq field_cont_on_gamma2_image g1_path_continuous line_is_pair_img)
  then have 7: "(\<lambda>x. F(g1(x), x) \<bullet> j) integrable_on (cbox a b)"
    using integrable_continuous [of "a" "b" "(\<lambda>x. F(g1(x), x) \<bullet> j)"]
    by auto
  have partial_deriv_one_d_integrable:
    "((\<lambda>y. ?F_a'(y, xc)) has_integral F(g1(xc), xc) \<bullet> j - F(g2(xc), xc) \<bullet> j) (cbox (g2 xc) (g1 xc))"
    if "xc \<in> cbox a b" for xc::real
  proof -
    have "{(y, xc').  y \<in> cbox (g2 xc) (g1 xc) \<and> xc' = xc} \<subseteq> Dx_pair"
      using that by (auto simp add: Dx_def)
    then show ?thesis
      using that and Base_vecs and F_partially_differentiable
        and Dx_def [symmetric] and g2_leq_g1
        and fundamental_theorem_of_calculus_partial_vector
        [of "g2 xc" "g1 xc" "i" "j" "xc *\<^sub>R j" "Dx_pair" "F" "?F_a'" ]
      by (auto simp add:  Groups.ab_semigroup_add_class.add.commute i_is_x_axis j_is_y_axis)
  qed
  have "?f integrable_on UNIV"
    by (simp add: f_lesbegue_integrable integrable_on_lborel)
  then have partial_deriv_integrable: "?F_a' integrable_on Dx_pair"
    using integrable_restrict_UNIV by auto
  have 4: "integral Dx_pair ?F_a' = integral (cbox a b) (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. ?F_a' (y, x)))"
  proof -
    have y_axis_gauge_integrable: "(\<lambda>y. ?f(y, x)) integrable_on UNIV" for x
    proof -
      let ?F_a'_oneD = "(\<lambda>x. (\<lambda>y. if y \<in> (cbox (g2 x) ( g1 x)) then ?F_a' (y, x) else 0))"
      have "\<forall>x. x \<notin> cbox a b \<longrightarrow>  (\<lambda>y. ?f (y, x)) = (\<lambda>y. 0)"
        by (auto simp add: Dx_def)
      then have f_integrable_x_not_in_range:
        "\<forall>x. x \<notin> cbox a b \<longrightarrow>  (\<lambda>y. ?f (y, x)) integrable_on UNIV"
        by (simp add: integrable_0)
      have "\<forall>x \<in> cbox a b. ?F_a'_oneD x = (\<lambda>y. ?f(y, x))"
        using g2_leq_g1 by (auto simp add: Dx_def)
      moreover have "\<forall>x \<in> cbox a b. ?F_a'_oneD x integrable_on UNIV"
        using has_integral_integrable integrable_restrict_UNIV partial_deriv_one_d_integrable by blast
      ultimately have "\<forall>x. x \<in> cbox a b \<longrightarrow>  (\<lambda>y. ?f (y, x)) integrable_on UNIV"
        by auto
      then show "(\<lambda>y. ?f (y, x)) integrable_on UNIV"
        using f_integrable_x_not_in_range by auto
    qed
    have arg: "(\<lambda>a. if a \<in> Dx_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> j) i a else 0) =
               (\<lambda>x. if x \<in> Dx_pair then if x \<in> Dx_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> j) i x else 0 else 0)"
      by auto
    have arg2: "Dx_pair = {(y, x). (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and> (\<forall>i\<in>Basis. g2 x \<bullet> i \<le> y \<bullet> i \<and> y \<bullet> i \<le> g1 x \<bullet> i)}"
      using Dx_def by auto
    have arg3: "\<And> x. x \<in> Dx_pair \<Longrightarrow> (\<lambda>x. if x \<in> Dx_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> j) i x else 0) x
                           = (\<lambda>x. partial_vector_derivative (\<lambda>a. F a \<bullet> j) i x) x"
      by auto
    have arg4: "\<And>x. x \<in> (cbox a b) \<Longrightarrow>
                      (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. if (y, x) \<in> Dx_pair then partial_vector_derivative (\<lambda>a. F a \<bullet> j) i (y, x) else 0)) x =
                      (\<lambda>x. integral (cbox (g2 x) (g1 x)) (\<lambda>y. partial_vector_derivative (\<lambda>a. F a \<bullet> j) i (y, x))) x"
      apply (clarsimp simp: Dx_def)
      by (smt Henstock_Kurzweil_Integration.integral_cong atLeastAtMost_iff)
    show ?thesis
      using gauge_integral_Fubini_curve_bounded_region_y
        [OF f_lesbegue_integrable y_axis_gauge_integrable y_axis_integral_measurable arg arg2]
        Henstock_Kurzweil_Integration.integral_cong[OF arg3, of "Dx_pair" "(\<lambda>x. x)"]
        Henstock_Kurzweil_Integration.integral_cong[OF arg4, of "cbox a b" "(\<lambda>x. x)"]
      by auto
  qed
  have "((integral Dx_pair (\<lambda>a. (?F_a' a)))
        = integral (cbox a b) (\<lambda>x. F(g1(x), x) \<bullet> j - F(g2(x), x) \<bullet> j))"
    using 4 Henstock_Kurzweil_Integration.integral_cong partial_deriv_one_d_integrable integrable_def
    by (smt integral_unique)
  then have "integral Dx_pair (\<lambda>a. - (?F_a' a))
              = - integral (cbox a b) (\<lambda>x. F(g1(x), x) \<bullet> j - F(g2(x), x) \<bullet> j)"
    using partial_deriv_integrable and integral_neg by auto
  then have 5: "integral Dx_pair (\<lambda>a. - (?F_a' a))
                = integral (cbox a b) (\<lambda>x. ( F(g2(x), x) \<bullet> j - F(g1(x), x) \<bullet> j))"
    using 6 7  
      and integral_neg [of _ "(\<lambda>x. F(g1 x, x) \<bullet> j - F(g2 x, x) \<bullet> j)"] by auto
  have "(line_integral F {j} gamma4) + (line_integral F {j} gamma3) -
        (line_integral F {j} gamma2) - (line_integral F {j} gamma1)
        = (integral Dx_pair (\<lambda>a. -(?F_a' a)))"
    using 0 1 2 3 5 6 7
      Henstock_Kurzweil_Integration.integral_diff[of "(\<lambda>x. F(g2(x), x)  \<bullet> j)"
        "cbox a b" "(\<lambda>x. F(g1(x), x) \<bullet> j)"] by (auto)
  then show "-(line_integral F {j} gamma4) -
         (line_integral F {j} gamma3) +
         (line_integral F {j} gamma2) +
         (line_integral F {j} gamma1)
                 = (integral Dx_pair (\<lambda>a. (?F_a' a)))"
    by (simp add: \<open>integral Dx_pair (\<lambda>a. - ?F_a' a) = - integral (cbox a b) (\<lambda>x. F(g1 x, x) \<bullet> j - F(g2 x, x) \<bullet> j)\<close> \<open>integral Dx_pair ?F_a' = integral (cbox a b) (\<lambda>x. F(g1 x, x) \<bullet> j - F(g2 x, x) \<bullet> j)\<close>)
qed

end

locale green_typeII_cube =  R2 + 
  fixes twoC F
  assumes 
    two_cube: "typeII_twoCube twoC" and
    valid_two_cube: "valid_two_cube twoC" and
    f_analytically_valid: "analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> j) i"
begin

lemma GreenThm_typeII_twoCube:
  shows "integral (cubeImage twoC) (\<lambda>a. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i  a) = one_chain_line_integral F {j} (boundary twoC)"
    "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {j} \<gamma>"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(x, 0))"
  let ?right_edge = "(\<lambda>y. twoC(1, y))"
  let ?top_edge = "(\<lambda>x. twoC(x, 1))"
  let ?left_edge = "(\<lambda>y. twoC(0, y))"
  have line_integral_around_boundary: 
      "one_chain_line_integral F {j} (boundary twoC) =  
         line_integral F {j} ?bottom_edge + line_integral F {j} ?right_edge
         - line_integral F {j} ?top_edge - line_integral F {j} ?left_edge"
  proof (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def)
    have finite1: "finite {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))}" by auto
    then have sum_step1: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (1, \<lambda>x. twoC (x, 0)), (- 1, \<lambda>x. twoC (x, 1))}. k * line_integral F {j} g) =
                       line_integral F {j} (\<lambda>x. twoC (x, 0)) + (\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))}. k * line_integral F {j} g)"
      using sum.insert_remove [OF finite1]
      using valid_two_cube
      apply (simp only: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def valid_two_cube_def)
      by (auto simp: card_insert_if split: if_split_asm)
    have three_distinct_edges: "card {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))} = 3"
      using valid_two_cube
      apply (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def valid_two_cube_def)
      by (auto simp: card_insert_if split: if_split_asm)
    have finite2: "finite {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}" by auto
    then have sum_step2: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (-1, \<lambda>x. twoC (x, 1))}. k * line_integral F {j} g) =
                       (- line_integral F {j} (\<lambda>x. twoC (x, 1))) + (\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}. k * line_integral F {j} g)"
      using sum.insert_remove [OF finite2] three_distinct_edges
      by (auto simp: card_insert_if split: if_split_asm)
    have two_distinct_edges: "card {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))} = 2"
      using three_distinct_edges
      by (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def)
    have finite3: "finite {(- 1::int, \<lambda>y. twoC (0, y))}" by auto
    then have sum_step3: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}. k * line_integral F {j} g) =
                       ( line_integral F {j} (\<lambda>y. twoC (1, y))) + (\<Sum>(k, g)\<in>{(- (1::real), \<lambda>y. twoC (0, y))}. k * line_integral F {j} g)"
      using sum.insert_remove [OF finite2] three_distinct_edges
      by (auto simp: card_insert_if split: if_split_asm)
    show "(\<Sum>x\<in>{(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (1, \<lambda>x. twoC (x, 0)), (- 1, \<lambda>x. twoC (x, 1))}. case x of (k, g) \<Rightarrow> k * line_integral F {j} g) =
                  line_integral F {j} (\<lambda>x. twoC (x, 0)) + line_integral F {j} (\<lambda>y. twoC (1, y)) - line_integral F {j} (\<lambda>x. twoC (x, 1)) - line_integral F {j} (\<lambda>y. twoC (0, y))"
      using sum_step1 sum_step2 sum_step3  by auto
  qed
  obtain a b g1 g2 where
    twoCisTypeII: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(y, x). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    using two_cube and typeII_twoCubeImg[of"twoC"]
    by auto
  have left_edge_explicit: "?left_edge = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  have left_edge_smooth: "?left_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x))-` {x} = {(x - a)/(b -a)}"
      using twoCisTypeII(1) by(auto simp add: Set.vimage_def)
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    have scale_shif_smth: "(\<lambda>x. (a + (b - a) * x)) C1_differentiable_on {0..1}" using scale_shift_smooth by auto
    then have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" using C1_differentiable_imp_piecewise by blast
    have g2_smooth: "g2 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeII(1)] twoCisTypeII(6) by auto
    have "(\<lambda>x. g2 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g2_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x::real. (g2 (a + (b - a) * x), a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x::real. (g2 (a + (b - a) * x), a + (b - a) * x))"]
      by (fastforce simp add: real_pair_basis)
    then show ?thesis using left_edge_explicit by auto
  qed
  have top_edge_explicit: "?top_edge = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))"
   and right_edge_explicit: "?right_edge = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))"
    by (simp_all add: twoCisTypeII(4) algebra_simps)
  have right_edge_smooth: "?right_edge piecewise_C1_differentiable_on {0..1}"
  proof -
    have "\<forall>x. (\<lambda>x. (a + (b - a) * x))-` {x} = {(x - a)/(b -a)}"
      using twoCisTypeII(1) by(auto simp add: Set.vimage_def)
    then have finite_vimg: "\<And>x. finite({0..1} \<inter> (\<lambda>x. (a + (b - a) * x))-` {x})" by auto
    then have scale_shif_pw_smth: "(\<lambda>x. (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}" 
      using C1_differentiable_imp_piecewise [OF scale_shift_smooth] by auto
    have g1_smooth: "g1 piecewise_C1_differentiable_on (\<lambda>x. a + (b - a) * x) ` {0..1}" using add_scale_img[OF twoCisTypeII(1)] twoCisTypeII(5) by auto
    have "(\<lambda>x. g1 (a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using piecewise_C1_differentiable_compose[OF scale_shif_pw_smth g1_smooth finite_vimg]
      by (auto simp add: o_def)
    then have "(\<lambda>x::real. (g1 (a + (b - a) * x), a + (b - a) * x)) piecewise_C1_differentiable_on {0..1}"
      using all_components_smooth_one_pw_smooth_is_pw_smooth[where f = "(\<lambda>x::real. (g1 (a + (b - a) * x), a + (b - a) * x))"]
      by (fastforce simp add: real_pair_basis)
    then show ?thesis using right_edge_explicit by auto
  qed
  have bottom_edge_explicit: "?bottom_edge = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
    by (simp add: twoCisTypeII(4) algebra_simps)
  show "integral (cubeImage twoC) (\<lambda>a. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i  a) = one_chain_line_integral F {j} (boundary twoC)"
    using Greens_thm_type_II[OF twoCisTypeII(3) left_edge_explicit left_edge_smooth
        top_edge_explicit right_edge_explicit right_edge_smooth
        bottom_edge_explicit f_analytically_valid
        twoCisTypeII(2) twoCisTypeII(1)]
      line_integral_around_boundary
    by auto
  have "line_integral_exists F {j} \<gamma>" if "(k,\<gamma>) \<in> boundary twoC" for k \<gamma>
  proof -
    have "line_integral_exists F {j} (\<lambda>y. twoC (0, y))"
         "line_integral_exists F {j} (\<lambda>x. twoC (x, 1))"
         "line_integral_exists F {j} (\<lambda>y. twoC (1, y))"
         "line_integral_exists F {j} (\<lambda>x. twoC (x, 0))"
      using Greens_thm_type_II[OF twoCisTypeII(3) left_edge_explicit left_edge_smooth
          top_edge_explicit right_edge_explicit right_edge_smooth
          bottom_edge_explicit f_analytically_valid
          twoCisTypeII(2) twoCisTypeII(1)] line_integral_around_boundary
      by auto
    then show "line_integral_exists F {j} \<gamma>"
      using that by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  qed
  then show "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {j} \<gamma>" by auto
qed

lemma line_integral_exists_on_typeII_Cube_boundaries':
  assumes "(k,\<gamma>) \<in> boundary twoC"
  shows "line_integral_exists F {j} \<gamma>"
  using assms GreenThm_typeII_twoCube(2) by blast

end

locale green_typeII_chain =  R2 + 
  fixes F two_chain s
  assumes valid_typeII_div: "valid_typeII_division s two_chain" and
          F_anal_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> j) i"
begin

lemma two_chain_valid_valid_cubes: "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube" using valid_typeII_div
  by (auto simp add: valid_two_chain_def)

lemma typeII_chain_line_integral_exists_boundary':
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {j} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
    using green_typeII_cube.line_integral_exists_on_typeII_Cube_boundaries'[of i j] F_anal_valid valid_typeII_div 
    apply(auto simp add:  two_chain_boundary_def)
    using R2_axioms green_typeII_cube_axioms_def green_typeII_cube_def two_chain_valid_valid_cubes by blast
  then show integ_exis_vert:
    "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {j} \<gamma>"
    by (simp add: two_chain_boundary_def two_chain_vertical_boundary_def boundary_def)
qed

lemma typeII_chain_line_integral_exists_boundary'':
     "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {j} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
    using green_typeII_cube.line_integral_exists_on_typeII_Cube_boundaries'[of i j] valid_typeII_div
    apply (simp add: two_chain_boundary_def boundary_def)
    using F_anal_valid R2_axioms green_typeII_cube_axioms_def green_typeII_cube_def two_chain_valid_valid_cubes by fastforce
  then show integ_exis_vert:
    "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {j} \<gamma>"
    by (simp add: two_chain_boundary_def two_chain_horizontal_boundary_def boundary_def)
qed

lemma typeII_cube_line_integral_exists_boundary:
     "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
  using valid_typeII_div typeII_chain_line_integral_exists_boundary' typeII_chain_line_integral_exists_boundary''
  apply (auto simp add: two_chain_boundary_def two_chain_horizontal_boundary_def two_chain_vertical_boundary_def)
  using boundary_def by auto

lemma type_II_chain_horiz_bound_valid:
     "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. valid_path \<gamma>"
  using valid_typeII_div typeII_edges_are_valid_paths
  by (force simp add: two_chain_boundary_def two_chain_horizontal_boundary_def boundary_def)

lemma type_II_chain_vert_bound_valid: (*This and the previous one need to be used in all proofs*)
     "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
  using typeII_edges_are_valid_paths valid_typeII_div
  by (force simp add: two_chain_boundary_def two_chain_vertical_boundary_def boundary_def)

lemma members_of_only_horiz_div_line_integrable':
  assumes "only_horizontal_division one_chain two_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "finite two_chain"
    "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube"
  shows "line_integral_exists F {j} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
    using typeII_cube_line_integral_exists_boundary by blast
  have integ_exis_vert:
    "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {j} \<gamma>"
    using typeII_chain_line_integral_exists_boundary' assms by auto
  have integ_exis_horiz:
    "(\<And>k \<gamma>. (\<exists>(k', \<gamma>') \<in> two_chain_horizontal_boundary two_chain. \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<Longrightarrow>
                            line_integral_exists F {j} \<gamma>)"
    using integ_exis type_II_chain_horiz_bound_valid
    using line_integral_exists_subpath[of "F" "{j}"]
    by (fastforce simp add: two_chain_boundary_def two_chain_horizontal_boundary_def
        two_chain_vertical_boundary_def boundary_def)
  obtain \<H> \<V> where hv_props: "finite \<H>"
        "(\<forall>(k,\<gamma>) \<in> \<H>. (\<exists>(k', \<gamma>') \<in> two_chain_horizontal_boundary two_chain.
            (\<exists>a \<in> {0 .. 1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>)))"
        "one_chain = \<H> \<union> \<V>"
        "((common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>)
          \<or> common_reparam_exists \<V> (two_chain_vertical_boundary two_chain))"
    "finite \<V>"
    "boundary_chain \<V>"
    "\<forall>(k,\<gamma>)\<in>\<V>. valid_path \<gamma>"
    using assms(1) unfolding only_horizontal_division_def  by blast
  have finite_j: "finite {j}" by auto
  show "line_integral_exists F {j} \<gamma>"
  proof(cases "common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>")
    case True
    show ?thesis
      using gen_common_subdivision_imp_eq_line_integral(2)[OF True two_chain_vertical_boundary_is_boundary_chain hv_props(6) integ_exis_vert finite_two_chain_vertical_boundary[OF assms(4)] hv_props(5) finite_j]
        integ_exis_horiz[of "\<gamma>"] assms(3) case_prod_conv hv_props(2) hv_props(3)
      by fastforce
  next
    case False
    have i: "{j} \<subseteq> Basis" using j_is_y_axis real_pair_basis by auto
    have ii: " \<forall>(k2, \<gamma>2)\<in>two_chain_vertical_boundary two_chain. \<forall>b\<in>{j}. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
      using F_anal_valid field_cont_on_typeII_region_cont_on_edges valid_typeII_div
      by (fastforce simp add: analytically_valid_def two_chain_vertical_boundary_def boundary_def path_image_def)
    show "line_integral_exists F {j} \<gamma>"
      using common_reparam_exists_imp_eq_line_integral(2)[OF finite_j hv_props(5) 
           finite_two_chain_vertical_boundary[OF assms(4)] hv_props(6) two_chain_vertical_boundary_is_boundary_chain ii _ hv_props(7) type_II_chain_vert_bound_valid]
        integ_exis_horiz[of "\<gamma>"] assms(3) hv_props False 
      by fastforce
  qed
qed

lemma GreenThm_typeII_twoChain:
  shows "two_chain_integral two_chain (partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i) = one_chain_line_integral F {j} (two_chain_boundary two_chain)"
proof (simp add: two_chain_boundary_def one_chain_line_integral_def two_chain_integral_def)
  let ?F_a' = "partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i"
  have "(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {j} g) = integral (cubeImage twoCube) (\<lambda>a. ?F_a' a)"
    if "twoCube \<in> two_chain" for twoCube
    using green_typeII_cube.GreenThm_typeII_twoCube(1) valid_typeII_div F_anal_valid one_chain_line_integral_def valid_two_chain_def
    by (simp add: R2_axioms green_typeII_cube_axioms_def green_typeII_cube_def that)
  then have double_sum_eq_sum:
    "(\<Sum>twoCube\<in>(two_chain).(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {j} g))
                     =  (\<Sum>twoCube\<in>(two_chain). integral (cubeImage twoCube) (\<lambda>a. ?F_a' a))"
    using Finite_Cartesian_Product.sum_cong_aux by auto
  have pairwise_disjoint_boundaries: "\<forall>x\<in> (boundary ` two_chain). (\<forall>y\<in> (boundary ` two_chain). (x \<noteq> y \<longrightarrow> (x \<inter> y = {})))"
    using valid_typeII_div by (fastforce simp add:  image_def valid_two_chain_def pairwise_def)
  have finite_boundaries: "\<forall>B \<in> (boundary` two_chain). finite B"
    using valid_typeII_div image_iff by (fastforce simp add: valid_two_cube_def valid_two_chain_def)
  have boundary_inj: "inj_on boundary two_chain"
    using valid_typeII_div by (force simp add: valid_two_cube_def valid_two_chain_def pairwise_def inj_on_def)
  have "(\<Sum>x\<in>(\<Union>x\<in>two_chain. boundary x). case x of (k, g) \<Rightarrow> k * line_integral F {j} g) =
                      (\<Sum>twoCube\<in>(two_chain).(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {j} g))"
    using sum.reindex[OF boundary_inj,  of "\<lambda>x. (\<Sum>(k,g)\<in> x. k * line_integral F {j} g)"]
    using sum.Union_disjoint[OF finite_boundaries
        pairwise_disjoint_boundaries,
        of "\<lambda>x. case x of (k, g) \<Rightarrow> (k::int) * line_integral F {j} g"]
    by auto
  then show "(\<Sum>C\<in>two_chain. integral (cubeImage C) (\<lambda>a. ?F_a' a)) = (\<Sum>x\<in>(\<Union>x\<in>two_chain. boundary x). case x of (k, g) \<Rightarrow> k * line_integral F {j} g)"
    using double_sum_eq_sum  by auto
qed

lemma GreenThm_typeII_divisible:
  assumes 
    gen_division: "gen_division s (cubeImage ` two_chain)"    (*This should follow from the assumption that images are not negligible*)
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} (two_chain_boundary two_chain)"
proof -
  let ?F_a' = "(partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i)"
  have "integral s (\<lambda>x. ?F_a' x) = two_chain_integral two_chain (\<lambda>a. ?F_a' a)"
  proof (simp add: two_chain_integral_def)
    have partial_deriv_integrable:
      "(?F_a' has_integral (integral (cubeImage twoCube) ?F_a')) (cubeImage twoCube)"
      if "twoCube \<in> two_chain" for twoCube
      by (simp add: analytically_valid_imp_part_deriv_integrable_on F_anal_valid integrable_integral that)
    then have partial_deriv_integrable:
      "\<And>twoCubeImg. twoCubeImg \<in> cubeImage ` two_chain \<Longrightarrow> ((\<lambda>x. ?F_a' x) has_integral (integral (twoCubeImg) (\<lambda>x. ?F_a' x))) (twoCubeImg)"
      using integrable_neg by force
    have finite_images: "finite (cubeImage ` two_chain)"
      using gen_division gen_division_def by auto
    have negligible_images: "pairwise (\<lambda>S S'. negligible (S \<inter> S')) (cubeImage ` two_chain)"
      using gen_division by (auto simp add: gen_division_def pairwise_def)
    have "inj_on cubeImage two_chain" using valid_typeII_div valid_two_chain_def by auto
    then have "(\<Sum>twoCubeImg\<in>cubeImage ` two_chain. integral twoCubeImg (\<lambda>x. ?F_a' x))
             = (\<Sum>C\<in>two_chain. integral (cubeImage C) (\<lambda>a. ?F_a' a))"
      using sum.reindex by auto
    then show "integral s (\<lambda>x. ?F_a' x) = (\<Sum>C\<in>two_chain. integral (cubeImage C) (\<lambda>a. ?F_a' a))"
      using has_integral_Union[OF finite_images partial_deriv_integrable negligible_images] gen_division
      by (auto simp add: gen_division_def)
  qed
  then show ?thesis
    using GreenThm_typeII_twoChain F_anal_valid
    by auto
qed

lemma GreenThm_typeII_divisible_region_boundary_gen:
  assumes only_horizontal_division: "only_horizontal_division \<gamma> two_chain"
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} \<gamma>"
proof -
  let ?F_a' = "(partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i)"
    (*Proving that line_integral on the x axis is 0 for the vertical 1-cubes*)
  have horiz_line_integral_zero:
    "one_chain_line_integral F {j} (two_chain_horizontal_boundary two_chain) = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {j} (snd oneCube) = 0"
      if "oneCube \<in> two_chain_horizontal_boundary(two_chain)" for oneCube
    proof -
      from that obtain x y1 y2 k 
        where horiz_edge_def: "oneCube = (k, (\<lambda>t::real. ((1 - t) * (y2) + t * y1, x::real)))"
        using valid_typeII_div
        by (auto simp add: typeII_twoCube_def two_chain_horizontal_boundary_def horizontal_boundary_def)
      let ?horiz_edge = "(snd oneCube)"
      have horiz_edge_y_const: "\<forall>t. (?horiz_edge t) \<bullet> j = x"
        by (auto simp add: horiz_edge_def real_inner_class.inner_add_left
            euclidean_space_class.inner_not_same_Basis j_is_y_axis)
      have horiz_edge_is_straight_path: "?horiz_edge = (\<lambda>t. (y2 + t * (y1 - y2), x))"
        by (auto simp: horiz_edge_def algebra_simps)
      have "\<forall>x. ?horiz_edge differentiable at x"
        using horiz_edge_is_straight_path straight_path_diffrentiable_y
        by (metis mult_commute_abs)
      then show "line_integral F {j} (snd oneCube) = 0"
        using line_integral_on_pair_straight_path(1) j_is_y_axis real_pair_basis horiz_edge_y_const
        by blast
    qed
    then show "(\<Sum>x\<in>two_chain_horizontal_boundary two_chain. case x of (k, g) \<Rightarrow> k * line_integral F {j} g) = 0"
      by (force intro: sum.neutral)
  qed
    (*then, the x axis line_integral on the boundaries of the twoCube is equal to the line_integral on the horizontal boundaries of the twoCube \<longrightarrow> 1*)
  have boundary_is_finite: "finite (two_chain_boundary two_chain)"
    unfolding two_chain_boundary_def
  proof (rule finite_UN_I)
    show "finite two_chain"
      using valid_typeII_div finite_image_iff gen_division_def valid_two_chain_def by auto
    show "\<And>a. a \<in> two_chain \<Longrightarrow> finite (boundary a)"
      by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  qed
  have boundary_is_vert_hor:
     "two_chain_boundary two_chain =
      (two_chain_vertical_boundary two_chain) \<union>
      (two_chain_horizontal_boundary two_chain)"
    by(auto simp add: two_chain_boundary_def two_chain_vertical_boundary_def two_chain_horizontal_boundary_def
        boundary_def)
  then have hor_vert_finite:
    "finite (two_chain_vertical_boundary two_chain)"
    "finite (two_chain_horizontal_boundary two_chain)"
    using boundary_is_finite by auto
  have horiz_verti_disjoint:
    "(two_chain_vertical_boundary two_chain) \<inter>
     (two_chain_horizontal_boundary two_chain) = {}"
  proof (simp add: two_chain_vertical_boundary_def two_chain_horizontal_boundary_def horizontal_boundary_def
        vertical_boundary_def)
    show "(\<Union>x\<in>two_chain. {(- 1, \<lambda>y. x (0, y)), (1::int, \<lambda>y. x (1::real, y))}) \<inter> (\<Union>x\<in>two_chain. {(1, \<lambda>z. x (z, 0)), (- 1, \<lambda>z. x (z, 1))}) = {}"
    proof -
      have "{(- 1, \<lambda>y. twoCube (0, y)), (1::int, \<lambda>y. twoCube (1, y))} \<inter>
            {(1, \<lambda>z. twoCube2 (z, 0)), (- 1, \<lambda>z. twoCube2 (z, 1))} = {}"
        if "twoCube\<in>two_chain" "twoCube2\<in>two_chain" for twoCube twoCube2
      proof (cases "twoCube = twoCube2")
        case True
        have card_4: "card {(- 1, \<lambda>y. twoCube2 (0::real, y)), (1::int, \<lambda>y. twoCube2 (1, y)), (1, \<lambda>x. twoCube2 (x, 0)), (- 1, \<lambda>x. twoCube2 (x, 1))} = 4"
          using valid_typeII_div valid_two_chain_def that(2)
          by (auto simp add: boundary_def vertical_boundary_def horizontal_boundary_def valid_two_cube_def)
        show ?thesis
          using card_4 by (auto simp: True card_insert_if split: if_split_asm)
      next
        case False
        show ?thesis
          using valid_typeII_div valid_two_chain_def
          by (simp add: boundary_def vertical_boundary_def horizontal_boundary_def pairwise_def \<open>twoCube \<noteq> twoCube2\<close> that)
      qed
      then have "\<Union> ((\<lambda>twoCube. {(- 1, \<lambda>y. twoCube (0::real, y)), (1::real, \<lambda>y. twoCube (1::real, y))}) ` two_chain)
                                          \<inter> \<Union> ((\<lambda>twoCube. {(1::int, \<lambda>z. twoCube (z, 0::real)), (- 1, \<lambda>z. twoCube (z, 1::real))}) ` two_chain)
                                              = {}"
        by (fastforce simp add: Union_disjoint)
      then show ?thesis by force
    qed
  qed
  have "one_chain_line_integral F {j} (two_chain_boundary two_chain)
       = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain) +
         one_chain_line_integral F {j} (two_chain_horizontal_boundary two_chain)"
    using boundary_is_vert_hor horiz_verti_disjoint
    by (simp add: hor_vert_finite sum.union_disjoint one_chain_line_integral_def)
  then have y_axis_line_integral_is_only_vertical:
    "one_chain_line_integral F {j} (two_chain_boundary two_chain)
                         = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
    using horiz_line_integral_zero
    by auto
      (*Since \<gamma> \<subseteq> the boundary of the 2-chain and the horizontal boundaries are \<subseteq> \<gamma>, then there is some \<H> \<subseteq> \<partial>\<^sub>H(2-\<C>) such that \<gamma> = \<H> \<union> \<partial>\<^sub>v(2-\<C>)*)
  obtain \<H> \<V> where hv_props: "finite \<H>"
    "(\<forall>(k,\<gamma>) \<in> \<H>. (\<exists>(k', \<gamma>') \<in> two_chain_horizontal_boundary two_chain.
                      (\<exists>a \<in> {0 .. 1}.
                            \<exists>b \<in> {0..1}.
                                a \<le> b \<and> subpath a b \<gamma>' = \<gamma>)))"
    "\<gamma> = \<H> \<union> \<V>"
    "(common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>
      \<or> common_reparam_exists \<V> (two_chain_vertical_boundary two_chain))"
    "finite \<V>"
    "boundary_chain \<V>"
    "\<forall>(k,\<gamma>)\<in>\<V>. valid_path \<gamma>"
    using only_horizontal_division
    by(fastforce simp add:  only_horizontal_division_def)
  have "finite {j}" by auto
  then have eq_integrals: " one_chain_line_integral F {j} \<V> = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
  proof(cases "common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>")
    case True then show ?thesis
      using gen_common_subdivision_imp_eq_line_integral(1)[OF True two_chain_vertical_boundary_is_boundary_chain hv_props(6) _ hor_vert_finite(1) hv_props(5)]
        typeII_chain_line_integral_exists_boundary'
      by force
  next
    case False
    have integ_exis_vert:
      "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {j} \<gamma>"
      using typeII_chain_line_integral_exists_boundary' assms
      by (fastforce simp add: valid_two_chain_def)
    have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
      using typeII_cube_line_integral_exists_boundary by blast
    have valid_paths: "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. valid_path \<gamma>"
      using typeII_edges_are_valid_paths valid_typeII_div
      by (fastforce simp add: two_chain_boundary_def two_chain_horizontal_boundary_def boundary_def)
    have integ_exis_horiz:
      "(\<And>k \<gamma>. (\<exists>(k', \<gamma>')\<in>two_chain_horizontal_boundary two_chain. \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<Longrightarrow>
                line_integral_exists F {j} \<gamma>)"
      using integ_exis valid_paths line_integral_exists_subpath[of "F" "{j}"]
      by (fastforce simp add: two_chain_boundary_def two_chain_horizontal_boundary_def
          two_chain_vertical_boundary_def boundary_def)
    have finite_j: "finite {j}" by auto
    have i: "{j} \<subseteq> Basis" using j_is_y_axis real_pair_basis by auto
    have ii: " \<forall>(k2, \<gamma>2)\<in>two_chain_vertical_boundary two_chain. \<forall>b\<in>{j}. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
      using valid_typeII_div field_cont_on_typeII_region_cont_on_edges F_anal_valid
      by (fastforce simp add: analytically_valid_def two_chain_vertical_boundary_def boundary_def path_image_def)
    show "one_chain_line_integral F {j} \<V> = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
      using hv_props(4) False common_reparam_exists_imp_eq_line_integral(1)[OF finite_j hv_props(5) hor_vert_finite(1) hv_props(6) two_chain_vertical_boundary_is_boundary_chain ii 
          _ hv_props(7) type_II_chain_vert_bound_valid] 
      by fastforce
  qed
    (*Since \<H> \<subseteq> \<partial>\<^sub>H(2-\<C>), then the line_integral on the x axis along \<H> is 0, and from 1 Q.E.D. *)
  have line_integral_on_path:
    "one_chain_line_integral F {j} \<gamma> =
     one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
  proof (simp only: one_chain_line_integral_def)
    have "line_integral F {j} (snd oneCube) = 0" if oneCube: "oneCube \<in> \<H>" for oneCube
    proof -
      obtain k \<gamma> where k_gamma: "(k,\<gamma>) = oneCube"
        using prod.collapse by blast
      then obtain k' \<gamma>' a b where kp_gammap:
        "(k'::int, \<gamma>') \<in> two_chain_horizontal_boundary two_chain"
        "a \<in> {0 .. 1}"
        "b \<in> {0..1}"
        "subpath a b \<gamma>' = \<gamma>"
        using hv_props oneCube
        by (smt case_prodE split_conv)
      obtain x y1 y2 where horiz_edge_def: "(k',\<gamma>') = (k', (\<lambda>t::real. ((1 - t) * (y2) + t * y1, x::real)))"
        using valid_typeII_div kp_gammap
        by (auto simp add: typeII_twoCube_def two_chain_horizontal_boundary_def horizontal_boundary_def)
      have horiz_edge_y_const: "\<forall>t. \<gamma> (t) \<bullet> j = x"
        using horiz_edge_def kp_gammap(4)
        by (auto simp add: real_inner_class.inner_add_left
            euclidean_space_class.inner_not_same_Basis j_is_y_axis subpath_def)
      have horiz_edge_is_straight_path:
        "\<gamma> = (\<lambda>t::real. ((1*y2 - a*y2) +  a*y1 + ((b-a)*y1 - (b - a)*y2)*t, x::real))"
      proof -
        fix t::real
        have "(1 - (b - a)*t + a) * (y2) + ((b-a)*t + a) * y1 = (1 - (b - a)*t + a) * (y2) + ((b-a)*t + a) * y1"
          by auto
        then have "\<gamma> = (\<lambda>t::real. ((1 - (b - a)*t - a) * (y2) + ((b-a)*t + a) * y1, x::real))"
          using horiz_edge_def Product_Type.snd_conv Product_Type.fst_conv kp_gammap(4)
          by (simp add: subpath_def diff_diff_eq[symmetric])
        also have "\<dots> = (\<lambda>t::real. ((1*y2 - (b - a)*y2*t - a*y2) + ((b-a)*y1*t + a*y1), x::real))"
          by(auto simp add: ring_class.ring_distribs(2) Groups.diff_diff_eq left_diff_distrib)
        also have "... = (\<lambda>t::real. ((1*y2 - a*y2) +  a*y1 + ((b-a)*y1 - (b - a)*y2)*t, x::real))"
          by (force simp add: left_diff_distrib)
        finally show "\<gamma> = (\<lambda>t::real. ((1*y2 - a*y2) +  a*y1 + ((b-a)*y1 - (b - a)*y2)*t, x::real))" .
      qed
      show "line_integral F {j} (snd oneCube) = 0"
      proof -
        have "\<forall>x. \<gamma> differentiable at x"
          by (simp add: horiz_edge_is_straight_path straight_path_diffrentiable_y)
        then have "line_integral F {j} \<gamma> = 0"
          by (simp add: horiz_edge_y_const line_integral_on_pair_straight_path(1))
        then show ?thesis
          using Product_Type.snd_conv k_gamma by auto
      qed
    qed
    then have "\<forall>x\<in>\<H>. (case x of (k, g) \<Rightarrow> (k::int) * line_integral F {j} g) = 0"
      by auto
    then show "(\<Sum>x\<in>\<gamma>. case x of (k, g) \<Rightarrow> real_of_int k * line_integral F {j} g) =
               (\<Sum>x\<in>two_chain_vertical_boundary two_chain. case x of (k, g) \<Rightarrow> real_of_int k * line_integral F {j} g)"
      using hv_props(1) hv_props(3) hv_props(5) sum_zero_set hor_vert_finite(1) eq_integrals
      by (clarsimp simp add: one_chain_line_integral_def sum_zero_set)
  qed
  then have "one_chain_line_integral F {j} \<gamma> =
                           one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
    using line_integral_on_path by auto
  then have "one_chain_line_integral F {j} \<gamma> =
                           one_chain_line_integral F {j} (two_chain_boundary two_chain)"
    using y_axis_line_integral_is_only_vertical by auto
  then show ?thesis
    using valid_typeII_div GreenThm_typeII_divisible by auto
qed

lemma GreenThm_typeII_divisible_region_boundary:
  assumes
    two_cubes_trace_vertical_boundaries: 
    "two_chain_vertical_boundary two_chain \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundary:
    "\<gamma> \<subseteq> two_chain_boundary two_chain"
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} \<gamma>"
proof -
  let ?F_a' = "(partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i)"
    (*Proving that line_integral on the x axis is 0 for the vertical 1-cubes*)
  have horiz_line_integral_zero:
    "one_chain_line_integral F {j} (two_chain_horizontal_boundary two_chain) = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {j} (snd oneCube) = 0"
      if one: "oneCube \<in> two_chain_horizontal_boundary(two_chain)" for oneCube
    proof -
      obtain x y1 y2 k where horiz_edge_def: "oneCube = (k, (\<lambda>t::real. ((1 - t) * (y2) + t * y1, x::real)))"
        using valid_typeII_div one
        by (auto simp add: typeII_twoCube_def two_chain_horizontal_boundary_def horizontal_boundary_def)
      let ?horiz_edge = "(snd oneCube)"
      have horiz_edge_y_const: "\<forall>t. (?horiz_edge t) \<bullet> j = x"
        using horiz_edge_def
        by (auto simp add: real_inner_class.inner_add_left
            euclidean_space_class.inner_not_same_Basis j_is_y_axis)
      have horiz_edge_is_straight_path:
        "?horiz_edge = (\<lambda>t. (y2 + t * (y1 - y2), x))"
        by (simp add: add_diff_eq diff_add_eq mult.commute right_diff_distrib horiz_edge_def)
      show "line_integral F {j} (snd oneCube) = 0"
        by (metis horiz_edge_is_straight_path horiz_edge_y_const line_integral_on_pair_straight_path(1) mult.commute straight_path_diffrentiable_y)
    qed
    then show "(\<Sum>x\<in>two_chain_horizontal_boundary two_chain. case x of (k, g) \<Rightarrow> k * line_integral F {j} g) = 0"
      by (simp add: prod.case_eq_if)
  qed
    (*then, the x axis line_integral on the boundaries of the twoCube is equal to the line_integral on the horizontal boundaries of the twoCube \<longrightarrow> 1*)
  have boundary_is_finite: "finite (two_chain_boundary two_chain)"
    unfolding two_chain_boundary_def
  proof (rule finite_UN_I)
    show "finite two_chain"
      using valid_typeII_div finite_image_iff gen_division_def valid_two_chain_def by auto
    show "\<And>a. a \<in> two_chain \<Longrightarrow> finite (boundary a)"
      by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  qed
  have boundary_is_vert_hor:
    "two_chain_boundary two_chain = (two_chain_vertical_boundary two_chain) \<union> (two_chain_horizontal_boundary two_chain)"
    by(auto simp add: two_chain_boundary_def two_chain_vertical_boundary_def two_chain_horizontal_boundary_def boundary_def)
  then have hor_vert_finite:
    "finite (two_chain_vertical_boundary two_chain)"
    "finite (two_chain_horizontal_boundary two_chain)"
    using boundary_is_finite by auto
  have horiz_verti_disjoint:
    "(two_chain_vertical_boundary two_chain) \<inter> (two_chain_horizontal_boundary two_chain) = {}"
  proof (simp add: two_chain_vertical_boundary_def two_chain_horizontal_boundary_def horizontal_boundary_def
        vertical_boundary_def)
    show "(\<Union>x\<in>two_chain. {(- 1, \<lambda>y. x (0, y)), (1::int, \<lambda>y. x (1::real, y))}) \<inter> (\<Union>x\<in>two_chain. {(1, \<lambda>z. x (z, 0)), (- 1, \<lambda>z. x (z, 1))}) = {}"
    proof -
      have "{(- 1, \<lambda>y. twoCube (0, y)), (1::int, \<lambda>y. twoCube (1, y))} \<inter>
            {(1, \<lambda>y. twoCube2 (y, 0)), (- 1, \<lambda>y. twoCube2 (y, 1))} = {}"
        if  "twoCube\<in>two_chain" "twoCube2\<in>two_chain" for twoCube twoCube2
      proof (cases "twoCube = twoCube2")
        case True
        have "card {(- 1, \<lambda>y. twoCube2 (0::real, y)), (1::int, \<lambda>y. twoCube2 (1, y)), (1, \<lambda>x. twoCube2 (x, 0)), (- 1, \<lambda>x. twoCube2 (x, 1))} = 4"
          using valid_typeII_div valid_two_chain_def that(2)
          by (auto simp add: boundary_def vertical_boundary_def horizontal_boundary_def valid_two_cube_def)
        then show ?thesis
          by (auto simp: True card_insert_if split: if_split_asm)
      next
        case False show ?thesis
          using valid_typeII_div valid_two_chain_def
          by (simp add: boundary_def vertical_boundary_def horizontal_boundary_def pairwise_def \<open>twoCube \<noteq> twoCube2\<close> that(1) that(2))
      qed
      then have "\<Union> ((\<lambda>twoCube. {(- 1, \<lambda>y. twoCube (0::real, y)), (1::real, \<lambda>y. twoCube (1::real, y))}) ` two_chain)
                                          \<inter> \<Union> ((\<lambda>twoCube. {(1::int, \<lambda>z. twoCube (z, 0::real)), (- 1, \<lambda>z. twoCube (z, 1::real))}) ` two_chain)
                                              = {}"
        by (force simp add: Complete_Lattices.Union_disjoint)
      then show ?thesis by force
    qed
  qed
  have "one_chain_line_integral F {j} (two_chain_boundary two_chain)
        = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain) +
          one_chain_line_integral F {j} (two_chain_horizontal_boundary two_chain)"
    using boundary_is_vert_hor horiz_verti_disjoint
    by (auto simp add: one_chain_line_integral_def hor_vert_finite sum.union_disjoint)
  then have y_axis_line_integral_is_only_vertical:
    "one_chain_line_integral F {j} (two_chain_boundary two_chain)
     = one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
    using horiz_line_integral_zero by auto
      (*Since \<gamma> \<subseteq> the boundary of the 2-chain and the horizontal boundaries are \<subseteq> \<gamma>, then there is some \<H> \<subseteq> \<partial>\<^sub>H(2-\<C>) such that \<gamma> = \<H> \<union> \<partial>\<^sub>v(2-\<C>)*)
  have "\<exists>\<H>. \<H> \<subseteq> (two_chain_horizontal_boundary two_chain) \<and>
             \<gamma> = \<H> \<union> (two_chain_vertical_boundary two_chain)"
  proof
    let ?\<H> = "\<gamma> - (two_chain_vertical_boundary two_chain)"
    show "?\<H> \<subseteq> two_chain_horizontal_boundary two_chain \<and> \<gamma> = ?\<H> \<union> two_chain_vertical_boundary two_chain"
      using two_cubes_trace_vertical_boundaries
        boundary_of_region_is_subset_of_partition_boundary boundary_is_vert_hor
      by blast
  qed
  then obtain \<H> where
    h_props: "\<H> \<subseteq> (two_chain_horizontal_boundary two_chain)"
    "\<gamma> = \<H> \<union> (two_chain_vertical_boundary two_chain)"
    by auto
  have h_vert_disj: "\<H> \<inter> (two_chain_vertical_boundary two_chain) = {}"
    using horiz_verti_disjoint h_props(1) by auto
  have h_finite: "finite \<H>"
    using hor_vert_finite h_props(1) Finite_Set.rev_finite_subset by force
  have line_integral_on_path:
    "one_chain_line_integral F {j} \<gamma> =
     one_chain_line_integral F {j} \<H> + one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
    by (auto simp add: one_chain_line_integral_def  h_props sum.union_disjoint[OF h_finite hor_vert_finite(1) h_vert_disj])
      (*Since \<H> \<subseteq> \<partial>\<^sub>H(2-\<C>), then the line_integral on the x axis along \<H> is 0, and from 1 Q.E.D. *)
  have "one_chain_line_integral F {j} \<H> = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {j} (snd oneCube) = 0"
      if oneCube: "oneCube \<in> two_chain_horizontal_boundary(two_chain)" for oneCube
    proof -
      obtain x y1 y2 k where horiz_edge_def: "oneCube = (k, (\<lambda>t::real. ((1 - t) * (y2) + t * y1, x::real)))"
        using valid_typeII_div oneCube
        by (auto simp add: typeII_twoCube_def two_chain_horizontal_boundary_def horizontal_boundary_def)
      let ?horiz_edge = "(snd oneCube)"
      have horiz_edge_y_const: "\<forall>t. (?horiz_edge t) \<bullet> j = x"
        by (simp add: j_is_y_axis horiz_edge_def)
      have horiz_edge_is_straight_path:
        "?horiz_edge = (\<lambda>t. (y2 + t * (y1 - y2), x))"
        by (simp add: add_diff_eq diff_add_eq mult.commute right_diff_distrib horiz_edge_def)
      show "line_integral F {j} (snd oneCube) = 0"
        by (simp add: horiz_edge_is_straight_path j_is_y_axis line_integral_on_pair_straight_path(1) mult.commute straight_path_diffrentiable_y)
    qed
    then have "\<forall>oneCube \<in> \<H>. line_integral F {j} (snd oneCube) = 0"
      using h_props by auto
    then have "\<forall>x\<in>\<H>. (case x of (k, g) \<Rightarrow> (k::int) * line_integral F {j} g) = 0"
      by auto
    then show "(\<Sum>x\<in>\<H>. case x of (k, g) \<Rightarrow> k * line_integral F {j} g) = 0"
      by simp
  qed
  then have "one_chain_line_integral F {j} \<gamma> =
                           one_chain_line_integral F {j} (two_chain_vertical_boundary two_chain)"
    using line_integral_on_path by auto
  then have "one_chain_line_integral F {j} \<gamma> =
             one_chain_line_integral F {j} (two_chain_boundary two_chain)"
    using y_axis_line_integral_is_only_vertical by auto
  then show ?thesis
    using valid_typeII_div GreenThm_typeII_divisible by auto
qed

end

locale green_typeI_cube =  R2 +
  fixes twoC F
  assumes 
    two_cube: "typeI_twoCube twoC" and
    valid_two_cube: "valid_two_cube twoC" and
    f_analytically_valid: "analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
begin

lemma GreenThm_typeI_twoCube:
  shows "integral (cubeImage twoC) (\<lambda>a. - partial_vector_derivative (\<lambda>p. F p \<bullet> i) j  a) = one_chain_line_integral F {i} (boundary twoC)"
    "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {i} \<gamma>"
proof -
  let ?bottom_edge = "(\<lambda>x. twoC(x, 0))"
  let ?right_edge = "(\<lambda>y. twoC(1, y))"
  let ?top_edge = "(\<lambda>x. twoC(x, 1))"
  let ?left_edge = "(\<lambda>y. twoC(0, y))"
  have line_integral_around_boundary:
    "one_chain_line_integral F {i} (boundary twoC) = 
     line_integral F {i} ?bottom_edge + line_integral F {i} ?right_edge
     -  line_integral F {i} ?top_edge - line_integral F {i} ?left_edge"
  proof (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def)
    have finite1: "finite {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))}" by auto
    have sum_step1: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (1, \<lambda>x. twoC (x, 0)), (- 1, \<lambda>x. twoC (x, 1))}. k * line_integral F {i} g) =
                       line_integral F {i} (\<lambda>x. twoC (x, 0)) + (\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))}. k * line_integral F {i} g)"
      using sum.insert_remove [OF finite1] valid_two_cube
      by (auto simp: horizontal_boundary_def vertical_boundary_def boundary_def valid_two_cube_def card_insert_if split: if_split_asm)
    have three_distinct_edges: "card {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (- 1, \<lambda>x. twoC (x, 1))} = 3"
      using valid_two_cube
      apply (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def valid_two_cube_def)
      by (auto simp: card_insert_if split: if_split_asm)
    have finite2: "finite {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}" by auto
    have sum_step2: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (-1, \<lambda>x. twoC (x, 1))}. k * line_integral F {i} g) =
                          (- line_integral F {i} (\<lambda>x. twoC (x, 1))) + (\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}. k * line_integral F {i} g)"
      using sum.insert_remove [OF finite2] three_distinct_edges
      by (auto simp: card_insert_if split: if_split_asm)
    have two_distinct_edges: "card {(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))} = 2"
      using three_distinct_edges
      by (simp add: one_chain_line_integral_def horizontal_boundary_def vertical_boundary_def boundary_def)
    have finite3: "finite {(- 1::int, \<lambda>y. twoC (0, y))}" by auto
    have sum_step3: "(\<Sum>(k, g)\<in>{(- (1::int), \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y))}. k * line_integral F {i} g) =
                          (line_integral F {i} (\<lambda>y. twoC (1, y))) + (\<Sum>(k, g)\<in>{(- (1::real), \<lambda>y. twoC (0, y))}. k * line_integral F {i} g)"
      using sum.insert_remove [OF finite2] three_distinct_edges 
      by (auto simp: card_insert_if split: if_split_asm)
    show "(\<Sum>x\<in>{(- 1::int, \<lambda>y. twoC (0, y)), (1, \<lambda>y. twoC (1, y)), (1, \<lambda>x. twoC (x, 0)), (- 1, \<lambda>x. twoC (x, 1))}. case x of (k, g) \<Rightarrow> k * line_integral F {i} g) =
                               line_integral F {i} (\<lambda>x. twoC (x, 0)) + line_integral F {i} (\<lambda>y. twoC (1, y)) - line_integral F {i} (\<lambda>x. twoC (x, 1)) - line_integral F {i} (\<lambda>y. twoC (0, y))"
      using sum_step1 sum_step2 sum_step3 by auto
  qed
  obtain a b g1 g2 where
    twoCisTypeI: "a < b"
    "(\<forall>x \<in> cbox a b. g2 x \<le> g1 x)"
    "cubeImage twoC = {(x,y). x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}"
    "twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))"
    "g1 piecewise_C1_differentiable_on {a .. b}"
    "g2 piecewise_C1_differentiable_on {a .. b}"
    "(\<lambda>x. twoC(x, 0)) = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(1, y)) = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))"
    "(\<lambda>x. twoC(x, 1)) = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))"
    "(\<lambda>y. twoC(0, y)) = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
    using two_cube and typeI_cube_explicit_spec[of"twoC"]  by auto
  have bottom_edge_smooth: "(\<lambda>x. twoC (x, 0)) piecewise_C1_differentiable_on {0..1}"
    using typeI_twoCube_smooth_edges two_cube boundary_def vertical_boundary_def horizontal_boundary_def
    by auto
  have top_edge_smooth: "?top_edge piecewise_C1_differentiable_on {0..1}"
    using typeI_twoCube_smooth_edges two_cube boundary_def vertical_boundary_def horizontal_boundary_def
    by auto
  show "integral (cubeImage twoC) (\<lambda>a. - partial_vector_derivative (\<lambda>p. F p \<bullet> i) j  a) = one_chain_line_integral F {i} (boundary twoC)"
    using Greens_thm_type_I[OF twoCisTypeI(3) twoCisTypeI(7) bottom_edge_smooth
        twoCisTypeI(8) twoCisTypeI(9) top_edge_smooth
        twoCisTypeI(10) f_analytically_valid twoCisTypeI(2) twoCisTypeI(1)]
        line_integral_around_boundary
    by auto
  have "line_integral_exists F {i} (\<lambda>y. twoC (0, y))"
       "line_integral_exists F {i} (\<lambda>x. twoC (x, 1))"
       "line_integral_exists F {i} (\<lambda>y. twoC (1, y))"
       "line_integral_exists F {i} (\<lambda>x. twoC (x, 0))"
    using Greens_thm_type_I[OF twoCisTypeI(3) twoCisTypeI(7) bottom_edge_smooth
        twoCisTypeI(8) twoCisTypeI(9) top_edge_smooth
        twoCisTypeI(10) f_analytically_valid twoCisTypeI(2) twoCisTypeI(1)]
      line_integral_around_boundary
    by auto
  then have "line_integral_exists F {i} \<gamma>" if "(k,\<gamma>) \<in> boundary twoC" for k \<gamma>
    using that  by (auto simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  then show "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {i} \<gamma>" by auto
qed

lemma line_integral_exists_on_typeI_Cube_boundaries':
  assumes "(k,\<gamma>) \<in> boundary twoC"
  shows "line_integral_exists F {i} \<gamma>"
  using assms two_cube valid_two_cube f_analytically_valid GreenThm_typeI_twoCube(2) by blast

end

locale green_typeI_chain = R2 + 
  fixes F two_chain s
  assumes valid_typeI_div: "valid_typeI_division s two_chain" and
          F_anal_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
begin

lemma two_chain_valid_valid_cubes: "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube" using valid_typeI_div
      by (auto simp add: valid_two_chain_def)

lemma typeI_cube_line_integral_exists_boundary':
  assumes "\<forall>two_cube \<in> two_chain. typeI_twoCube two_cube"
  assumes "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
  assumes "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube"
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {i} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
    using green_typeI_cube.line_integral_exists_on_typeI_Cube_boundaries'[of i j] assms
    using R2_axioms green_typeI_cube_axioms_def green_typeI_cube_def two_chain_boundary_def by fastforce
  then show integ_exis_vert:
    "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {i} \<gamma>"
    by (simp add: two_chain_boundary_def two_chain_vertical_boundary_def boundary_def)
qed

lemma typeI_cube_line_integral_exists_boundary'':
  "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {i} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
    using green_typeI_cube.line_integral_exists_on_typeI_Cube_boundaries'[of i j] valid_typeI_div
    apply (simp add: two_chain_boundary_def boundary_def)
    using F_anal_valid R2_axioms green_typeI_cube_axioms_def green_typeI_cube_def two_chain_valid_valid_cubes by fastforce
  then show integ_exis_horiz:
    "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {i} \<gamma>"
    by (simp add: two_chain_boundary_def two_chain_horizontal_boundary_def boundary_def)
qed

lemma typeI_cube_line_integral_exists_boundary:
  "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
  using  typeI_cube_line_integral_exists_boundary' typeI_cube_line_integral_exists_boundary''
  apply (auto simp add: two_chain_boundary_def two_chain_horizontal_boundary_def two_chain_vertical_boundary_def)
  by (meson R2_axioms green_typeI_chain.F_anal_valid green_typeI_chain_axioms green_typeI_cube.line_integral_exists_on_typeI_Cube_boundaries' green_typeI_cube_axioms_def green_typeI_cube_def two_chain_valid_valid_cubes valid_typeI_div)

lemma type_I_chain_horiz_bound_valid:
  "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. valid_path \<gamma>"
  using typeI_edges_are_valid_paths valid_typeI_div
  by (force simp add: two_chain_boundary_def two_chain_horizontal_boundary_def boundary_def)

lemma type_I_chain_vert_bound_valid: (*This and the previous one need to be used in all proofs*)
  assumes "\<forall>two_cube \<in> two_chain. typeI_twoCube two_cube"
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
  using typeI_edges_are_valid_paths assms(1)
  by (force simp add: two_chain_boundary_def two_chain_vertical_boundary_def boundary_def)

lemma members_of_only_vertical_div_line_integrable':
  assumes "only_vertical_division one_chain two_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "finite two_chain"
  shows "line_integral_exists F {i} \<gamma>"
proof -
  have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
    using typeI_cube_line_integral_exists_boundary by blast
  have integ_exis_horiz:
    "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {i} \<gamma>"
    using typeI_cube_line_integral_exists_boundary'' assms by auto
  have valid_paths: "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
    using type_I_chain_vert_bound_valid valid_typeI_div by linarith
  have integ_exis_vert:
    "(\<And>k \<gamma>. (\<exists>(k', \<gamma>')\<in>two_chain_vertical_boundary two_chain. \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<Longrightarrow>
                            line_integral_exists F {i} \<gamma>)"
    using integ_exis valid_paths line_integral_exists_subpath[of "F" "{i}"]
    by (fastforce simp add: two_chain_boundary_def two_chain_horizontal_boundary_def
        two_chain_vertical_boundary_def boundary_def)
  obtain \<H> \<V> where hv_props: "finite \<V>"
        "(\<forall>(k,\<gamma>) \<in> \<V>. (\<exists>(k', \<gamma>') \<in> two_chain_vertical_boundary two_chain.
                        (\<exists>a \<in> {0 .. 1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>)))"
        "one_chain = \<H> \<union> \<V>"
        "(common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>)
         \<or> common_reparam_exists \<H> (two_chain_horizontal_boundary two_chain)"
        "finite \<H>"
        "boundary_chain \<H>"
        "\<forall>(k,\<gamma>)\<in>\<H>. valid_path \<gamma>"
    using assms(1) unfolding only_vertical_division_def by blast
  have finite_i: "finite {i}" by auto
  show "line_integral_exists F {i} \<gamma>"
  proof(cases "common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>")
    case True
    show ?thesis
      using gen_common_subdivision_imp_eq_line_integral(2)[OF True two_chain_horizontal_boundary_is_boundary_chain hv_props(6) integ_exis_horiz finite_two_chain_horizontal_boundary[OF assms(4)] hv_props(5) finite_i]
        integ_exis_vert[of "\<gamma>"] assms(3) case_prod_conv hv_props(2) hv_props(3)
      by fastforce
  next
    case False
    have i: "{i} \<subseteq> Basis" using i_is_x_axis real_pair_basis by auto
    have ii: " \<forall>(k2, \<gamma>2)\<in>two_chain_horizontal_boundary two_chain. \<forall>b\<in>{i}. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
      using assms field_cont_on_typeI_region_cont_on_edges F_anal_valid valid_typeI_div
      by (fastforce simp add: analytically_valid_def two_chain_horizontal_boundary_def boundary_def path_image_def)
    show "line_integral_exists F {i} \<gamma>"
      using common_reparam_exists_imp_eq_line_integral(2)[OF finite_i hv_props(5) finite_two_chain_horizontal_boundary[OF assms(4)] hv_props(6) two_chain_horizontal_boundary_is_boundary_chain ii 
            _ hv_props(7) type_I_chain_horiz_bound_valid]
        integ_exis_vert[of "\<gamma>"] False
        assms(3) hv_props(2-4) by fastforce
  qed
qed

lemma GreenThm_typeI_two_chain:
   "two_chain_integral two_chain (\<lambda>a. - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j a) = one_chain_line_integral F {i} (two_chain_boundary two_chain)"
proof (simp add: two_chain_boundary_def one_chain_line_integral_def two_chain_integral_def)
  let ?F_b' = "partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j"
  have all_two_cubes_have_four_distict_edges: "\<forall>twoCube \<in> two_chain. card (boundary twoCube) = 4"
    using valid_typeI_div valid_two_chain_def valid_two_cube_def by auto
  have no_shared_edges_have_similar_orientations:
    "\<forall>twoCube1 \<in> two_chain. \<forall>twoCube2 \<in> two_chain.  twoCube1 \<noteq> twoCube2 \<longrightarrow>
                          boundary twoCube1 \<inter> boundary twoCube2 = {}"
    using valid_typeI_div valid_two_chain_def
    by (auto simp add: pairwise_def)
  have "(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {i} g) = integral (cubeImage twoCube) (\<lambda>a. - ?F_b' a)"
        if "twoCube \<in> two_chain" for twoCube
  proof -
    have analytically_val: " analytically_valid (cubeImage twoCube) (\<lambda>x. F x \<bullet> i) j"
      using that F_anal_valid by auto
    show "(\<Sum>(k, g)\<in>boundary twoCube. k * line_integral F {i} g) = integral (cubeImage twoCube) (\<lambda>a. - ?F_b' a)"
      using green_typeI_cube.GreenThm_typeI_twoCube
      apply (simp add: one_chain_line_integral_def)
      by (simp add: R2_axioms analytically_val green_typeI_cube_axioms_def green_typeI_cube_def that two_chain_valid_valid_cubes valid_typeI_div)
  qed
  then have double_sum_eq_sum:
    "(\<Sum>twoCube\<in>(two_chain).(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {i} g))
                     =  (\<Sum>twoCube\<in>(two_chain). integral (cubeImage twoCube) (\<lambda>a. - ?F_b' a))"
    using Finite_Cartesian_Product.sum_cong_aux by auto
  have pairwise_disjoint_boundaries: "\<forall>x\<in> (boundary ` two_chain). (\<forall>y\<in> (boundary ` two_chain). (x \<noteq> y \<longrightarrow> (x \<inter> y = {})))"
    using no_shared_edges_have_similar_orientations
    by (force simp add: image_def disjoint_iff_not_equal)
  have finite_boundaries: "\<forall>B \<in> (boundary` two_chain). finite B"
    using all_two_cubes_have_four_distict_edges
    using image_iff by fastforce
  have boundary_inj: "inj_on boundary two_chain"
    using  all_two_cubes_have_four_distict_edges and no_shared_edges_have_similar_orientations
    by (force simp add: inj_on_def)
  have "(\<Sum>x\<in>(\<Union>(boundary` two_chain)). case x of (k, g) \<Rightarrow> k * line_integral F {i} g) 
        = (sum \<circ> sum) (\<lambda>x. case x of (k, g) \<Rightarrow> (k::int) * line_integral F {i} g) (boundary ` two_chain)"
    using sum.Union_disjoint[OF finite_boundaries pairwise_disjoint_boundaries]
    by simp
  also have "... = (\<Sum>twoCube\<in>(two_chain).(\<Sum>(k,g)\<in> boundary twoCube. k * line_integral F {i} g))"
    using sum.reindex[OF boundary_inj, of "\<lambda>x. (\<Sum>(k,g)\<in> x. k * line_integral F {i} g)"]
    by auto
  finally show "(\<Sum>C\<in>two_chain. - integral (cubeImage C) (partial_vector_derivative (\<lambda>x. F x \<bullet> i) j)) = (\<Sum>x\<in>(\<Union>x\<in>two_chain. boundary x). case x of (k, g) \<Rightarrow> real_of_int k * line_integral F {i} g)"
    using double_sum_eq_sum by auto
qed

lemma GreenThm_typeI_divisible:
  assumes gen_division: "gen_division s (cubeImage ` two_chain)"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} (two_chain_boundary two_chain)"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j"
  have "integral s (\<lambda>x. - ?F_b' x) = two_chain_integral two_chain (\<lambda>a. - ?F_b' a)"
  proof (simp add: two_chain_integral_def)
    have "(\<Sum>f\<in>two_chain. integral (cubeImage f) (partial_vector_derivative (\<lambda>p. F p \<bullet> i) j)) = integral s (partial_vector_derivative (\<lambda>p. F p \<bullet> i) j)"
      by (metis analytically_valid_imp_part_deriv_integrable_on F_anal_valid gen_division two_chain_integral_def two_chain_integral_eq_integral_divisable valid_typeI_div)
    then show "- integral s (partial_vector_derivative (\<lambda>a. F a \<bullet> i) j) = (\<Sum>C\<in>two_chain. - integral (cubeImage C) (partial_vector_derivative (\<lambda>a. F a \<bullet> i) j))"
      by (simp add: sum_negf)
  qed
  then show ?thesis
    using GreenThm_typeI_two_chain assms by auto
qed

lemma GreenThm_typeI_divisible_region_boundary:
  assumes 
    gen_division: "gen_division s (cubeImage ` two_chain)" and
    two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundary:
    "\<gamma> \<subseteq> two_chain_boundary two_chain"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} \<gamma>"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>a. F(a) \<bullet> i)"
  have all_two_cubes_have_four_distict_edges: "\<forall>twoCube \<in> two_chain. card (boundary twoCube) = 4"
    using valid_typeI_div valid_two_chain_def valid_two_cube_def by auto
  have no_shared_edges_have_similar_orientations:
    "\<forall>twoCube1 \<in> two_chain. \<forall>twoCube2 \<in> two_chain.
        twoCube1 \<noteq> twoCube2 \<longrightarrow> boundary twoCube1 \<inter> boundary twoCube2 = {}"
    using valid_typeI_div valid_two_chain_def by (auto simp add: pairwise_def)
      (*Proving that line_integral on the x axis is 0 for the vertical 1-cubes*)
  have vert_line_integral_zero:
    "one_chain_line_integral F {i} (two_chain_vertical_boundary two_chain) = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {i} (snd oneCube) = 0"
      if oneCube: "oneCube \<in> two_chain_vertical_boundary(two_chain)" for oneCube
    proof -
      obtain x y1 y2 k where vert_edge_def: "oneCube = (k, (\<lambda>t::real. (x::real, (1 - t) * (y2) + t * y1)))"
        using valid_typeI_div oneCube
        by (auto simp add: typeI_twoCube_def two_chain_vertical_boundary_def vertical_boundary_def)
      let ?vert_edge = "(snd oneCube)"
      have vert_edge_x_const: "\<forall>t. (?vert_edge t) \<bullet> i = x"
        by (simp add: i_is_x_axis vert_edge_def)
      have vert_edge_is_straight_path: "?vert_edge = (\<lambda>t. (x, y2 + t * (y1 - y2)))"
        using vert_edge_def Product_Type.snd_conv
        by (auto simp add: mult.commute right_diff_distrib')
      show ?thesis
        by (simp add: i_is_x_axis line_integral_on_pair_straight_path(1) mult.commute straight_path_diffrentiable_x vert_edge_is_straight_path)
    qed
    then show "(\<Sum>x\<in>two_chain_vertical_boundary two_chain. case x of (k, g) \<Rightarrow> k * line_integral F {i} g) = 0"
      using comm_monoid_add_class.sum.neutral by (simp add: prod.case_eq_if)
  qed
    (*then, the x axis line_integral on the boundaries of the twoCube is equal to the line_integral on the horizontal boundaries of the twoCube \<longrightarrow> 1*)
  have boundary_is_finite: "finite (two_chain_boundary two_chain)"
    unfolding two_chain_boundary_def
    by (metis all_two_cubes_have_four_distict_edges card.infinite finite_UN_I finite_imageD 
              gen_division gen_division_def zero_neq_numeral valid_typeI_div valid_two_chain_def)
  have boundary_is_vert_hor: "(two_chain_boundary two_chain) =
                              (two_chain_vertical_boundary two_chain) \<union>
                              (two_chain_horizontal_boundary two_chain)"
  by(auto simp add: two_chain_boundary_def two_chain_vertical_boundary_def two_chain_horizontal_boundary_def
        boundary_def)
  then have hor_vert_finite:
    "finite (two_chain_vertical_boundary two_chain)"
    "finite (two_chain_horizontal_boundary two_chain)"
    using boundary_is_finite by auto
  have horiz_verti_disjoint:
    "(two_chain_vertical_boundary two_chain) \<inter> (two_chain_horizontal_boundary two_chain) = {}"
  proof (simp add: two_chain_vertical_boundary_def two_chain_horizontal_boundary_def horizontal_boundary_def
        vertical_boundary_def)
    show "(\<Union>x\<in>two_chain. {(- 1, \<lambda>y. x (0, y)), (1::int, \<lambda>y. x (1::real, y))}) \<inter> (\<Union>x\<in>two_chain. {(1, \<lambda>z. x (z, 0)), (- 1, \<lambda>z. x (z, 1))}) = {}"
    proof -
      have "{(- 1, \<lambda>y. twoCube (0, y)), (1::int, \<lambda>y. twoCube (1, y))} \<inter>
            {(1, \<lambda>z. twoCube2 (z, 0)), (- 1, \<lambda>z. twoCube2 (z, 1))} = {}"
        if "twoCube\<in>two_chain" "twoCube2\<in>two_chain" for twoCube twoCube2
      proof (cases "twoCube = twoCube2")
        case True
        have "card {(- 1::int, \<lambda>y. twoCube2 (0::real, y)), (1::int, \<lambda>y. twoCube2 (1, y)), (1, \<lambda>x. twoCube2 (x, 0)), (- 1, \<lambda>x. twoCube2 (x, 1))} = 4"
          using all_two_cubes_have_four_distict_edges that(2)
          by (auto simp add: boundary_def vertical_boundary_def horizontal_boundary_def)
        then show ?thesis
          by (auto simp: True card_insert_if split: if_split_asm)
      next
        case False
        then show ?thesis
          using no_shared_edges_have_similar_orientations
          by (simp add: that boundary_def vertical_boundary_def horizontal_boundary_def)
      qed
      then have "\<Union> ((\<lambda>twoCube. {(-1::int, \<lambda>y. twoCube (0,y)), (1, \<lambda>y. twoCube (1, y))}) ` two_chain)
               \<inter> \<Union> ((\<lambda>twoCube. {(1, \<lambda>y. twoCube (y, 0)), (-1, \<lambda>z. twoCube (z, 1))}) ` two_chain) = {}"
        using Complete_Lattices.Union_disjoint by force
      then show ?thesis by force
    qed
  qed
  have "one_chain_line_integral F {i} (two_chain_boundary two_chain)
        = one_chain_line_integral F {i} (two_chain_vertical_boundary two_chain) +
          one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
    using boundary_is_vert_hor horiz_verti_disjoint
    by (auto simp add: one_chain_line_integral_def hor_vert_finite sum.union_disjoint)
  then have x_axis_line_integral_is_only_horizontal:
    "one_chain_line_integral F {i} (two_chain_boundary two_chain)
     = one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
    using vert_line_integral_zero by auto
      (*Since \<gamma> \<subseteq> the boundary of the 2-chain and the horizontal boundaries are \<subseteq> \<gamma>, then there is some \<V> \<subseteq> \<partial>\<^sub>V(2-\<C>) such that \<gamma> = \<V> \<union> \<partial>\<^sub>H(2-\<C>)*)
  have "\<exists>\<V>. \<V> \<subseteq> (two_chain_vertical_boundary two_chain) \<and> \<gamma> = \<V> \<union> (two_chain_horizontal_boundary two_chain)"
  proof
    let ?\<V> = "\<gamma> - (two_chain_horizontal_boundary two_chain)"
    show "?\<V> \<subseteq> two_chain_vertical_boundary two_chain \<and> \<gamma> = ?\<V> \<union> two_chain_horizontal_boundary two_chain"
      using two_cubes_trace_horizontal_boundaries
        boundary_of_region_is_subset_of_partition_boundary boundary_is_vert_hor
      by blast
  qed
  then obtain \<V> where
    v_props: "\<V> \<subseteq> (two_chain_vertical_boundary two_chain)" "\<gamma> = \<V> \<union> (two_chain_horizontal_boundary two_chain)"
    by auto
  have v_horiz_disj: "\<V> \<inter> (two_chain_horizontal_boundary two_chain) = {}"
    using horiz_verti_disjoint v_props(1) by auto
  have v_finite: "finite \<V>"
    using hor_vert_finite v_props(1) Finite_Set.rev_finite_subset by force
  have line_integral_on_path: "one_chain_line_integral F {i} \<gamma> =
                               one_chain_line_integral F {i} \<V> + one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
    by(auto simp add: one_chain_line_integral_def v_props sum.union_disjoint[OF v_finite hor_vert_finite(2) v_horiz_disj])
      (*Since \<V> \<subseteq> \<partial>\<^sub>V(2-\<C>), then the line_integral on the x axis along \<H> is 0, and from 1 Q.E.D. *)
  have "one_chain_line_integral F {i} \<V> = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {i} (snd oneCube) = 0"
      if oneCube: "oneCube \<in> two_chain_vertical_boundary(two_chain)" for oneCube
    proof -
      obtain x y1 y2 k where vert_edge_def: "oneCube = (k, (\<lambda>t::real. (x::real, (1 - t) * (y2) + t * y1)))"
        using valid_typeI_div oneCube
        by (auto simp add: typeI_twoCube_def two_chain_vertical_boundary_def vertical_boundary_def)
      let ?vert_edge = "(snd oneCube)"
      have vert_edge_x_const: "\<forall>t. (?vert_edge t) \<bullet> i = x"
        by (simp add: i_is_x_axis vert_edge_def)
      have vert_edge_is_straight_path:
        "?vert_edge = (\<lambda>t. (x, y2 + t * (y1 - y2)))"
        by (auto simp: vert_edge_def algebra_simps)
      have "\<forall>x. ?vert_edge differentiable at x"
        by (metis mult.commute vert_edge_is_straight_path straight_path_diffrentiable_x)
      then show "line_integral F {i} (snd oneCube) = 0"
        using line_integral_on_pair_straight_path(1) vert_edge_x_const by blast
    qed
    then have "\<forall>oneCube \<in> \<V>. line_integral F {i} (snd oneCube) = 0"
      using v_props by auto
    then show "(\<Sum>x\<in>\<V>. case x of (k, g) \<Rightarrow> k * line_integral F {i} g) = 0"
      using comm_monoid_add_class.sum.neutral by (simp add: prod.case_eq_if) 
  qed
  then have "one_chain_line_integral F {i} \<gamma> =
             one_chain_line_integral F {i} (two_chain_boundary two_chain)"
    using x_axis_line_integral_is_only_horizontal by (simp add: line_integral_on_path)
  then show ?thesis
    using assms and GreenThm_typeI_divisible by auto
qed

lemma GreenThm_typeI_divisible_region_boundary_gen:
  assumes valid_typeI_div: "valid_typeI_division s two_chain" and
    f_analytically_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>a. F(a) \<bullet> i) j" and
    only_vertical_division:
    "only_vertical_division \<gamma> two_chain"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} \<gamma>"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>a. F(a) \<bullet> i)"
  have all_two_cubes_have_four_distict_edges: "\<forall>twoCube \<in> two_chain. card (boundary twoCube) = 4"
    using valid_typeI_div valid_two_chain_def valid_two_cube_def
    by auto
  have no_shared_edges_have_similar_orientations:
    "\<forall>twoCube1 \<in> two_chain. \<forall>twoCube2 \<in> two_chain.
         twoCube1 \<noteq> twoCube2 \<longrightarrow> boundary twoCube1 \<inter> boundary twoCube2 = {}"
    using valid_typeI_div valid_two_chain_def by (auto simp add: pairwise_def)
      (*Proving that line_integral on the x axis is 0 for the vertical 1-cubes*)
  have vert_line_integral_zero:
    "one_chain_line_integral F {i} (two_chain_vertical_boundary two_chain) = 0"
  proof (simp add: one_chain_line_integral_def)
    have "line_integral F {i} (snd oneCube) = 0"
      if oneCube: "oneCube \<in> two_chain_vertical_boundary(two_chain)" for oneCube
    proof -
      obtain x y1 y2 k where vert_edge_def: "oneCube = (k, (\<lambda>t::real. (x::real, (1 - t) * (y2) + t * y1)))"
        using valid_typeI_div oneCube
        by (auto simp add: typeI_twoCube_def two_chain_vertical_boundary_def vertical_boundary_def)
      let ?vert_edge = "(snd oneCube)"
      have vert_edge_x_const: "\<forall>t. (?vert_edge t) \<bullet> i = x"
        by (simp add: i_is_x_axis vert_edge_def)
      have vert_edge_is_straight_path: "?vert_edge = (\<lambda>t. (x, y2 + t * (y1 - y2)))"
        by (auto simp: vert_edge_def algebra_simps)
      show ?thesis
        by (simp add: i_is_x_axis line_integral_on_pair_straight_path(1) mult.commute straight_path_diffrentiable_x vert_edge_is_straight_path)
    qed
    then show "(\<Sum>x\<in>two_chain_vertical_boundary two_chain. case x of (k, g) \<Rightarrow> k * line_integral F {i} g) = 0"
      using comm_monoid_add_class.sum.neutral by (simp add: prod.case_eq_if)
  qed
    (*then, the x axis line_integral on the boundaries of the twoCube is equal to the line_integral on the horizontal boundaries of the twoCube \<longrightarrow> 1*)
  have boundary_is_finite: "finite (two_chain_boundary two_chain)"
    unfolding two_chain_boundary_def
  proof (rule finite_UN_I)
    show "finite two_chain"
      using assms(1) finite_imageD gen_division_def valid_two_chain_def by auto
    show "\<And>a. a \<in> two_chain \<Longrightarrow> finite (boundary a)"
      by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
  qed
  have boundary_is_vert_hor: "two_chain_boundary two_chain =
                              (two_chain_vertical_boundary two_chain) \<union> (two_chain_horizontal_boundary two_chain)"
    by (auto simp add: two_chain_boundary_def two_chain_vertical_boundary_def two_chain_horizontal_boundary_def boundary_def)
  then have hor_vert_finite:
    "finite (two_chain_vertical_boundary two_chain)"
    "finite (two_chain_horizontal_boundary two_chain)"
    using boundary_is_finite by auto
  have horiz_verti_disjoint:
    "(two_chain_vertical_boundary two_chain) \<inter> (two_chain_horizontal_boundary two_chain) = {}"
  proof (simp add: two_chain_vertical_boundary_def two_chain_horizontal_boundary_def horizontal_boundary_def
        vertical_boundary_def)
    show "(\<Union>x\<in>two_chain. {(- 1, \<lambda>y. x (0, y)), (1::int, \<lambda>y. x (1::real, y))}) 
        \<inter> (\<Union>x\<in>two_chain. {(1, \<lambda>y. x (y, 0)), (- 1, \<lambda>y. x (y, 1))}) = {}"
    proof -
      have "{(- 1, \<lambda>y. twoCube (0, y)), (1::int, \<lambda>y. twoCube (1, y))} \<inter>
            {(1, \<lambda>y. twoCube2 (y, 0)), (- 1, \<lambda>y. twoCube2 (y, 1))} = {}"
        if "twoCube \<in> two_chain" "twoCube2 \<in> two_chain" for twoCube twoCube2
      proof (cases "twoCube = twoCube2")
        case True
        have "card {(- 1::int, \<lambda>y. twoCube2 (0, y)), (1::int, \<lambda>y. twoCube2 (1, y)), (1, \<lambda>x. twoCube2 (x, 0)), (- 1, \<lambda>x. twoCube2 (x, 1))} = 4"
          using all_two_cubes_have_four_distict_edges that(2)
          by (auto simp add: boundary_def vertical_boundary_def horizontal_boundary_def)
        then show ?thesis
          by (auto simp: card_insert_if True split: if_split_asm)
      next
        case False
        then show ?thesis
          using no_shared_edges_have_similar_orientations
          by (simp add: that boundary_def vertical_boundary_def horizontal_boundary_def)
      qed
      then have "\<Union> ((\<lambda>twoCube. {(- 1, \<lambda>y. twoCube (0, y)), (1, \<lambda>y. twoCube (1, y))}) ` two_chain)
               \<inter> \<Union> ((\<lambda>twoCube. {(1::int, \<lambda>y. twoCube (y, 0)), (- 1, \<lambda>y. twoCube (y, 1))}) ` two_chain)
                 = {}"
        using Complete_Lattices.Union_disjoint by force
      then show ?thesis by force
    qed
  qed
  have "one_chain_line_integral F {i} (two_chain_boundary two_chain)
         = one_chain_line_integral F {i} (two_chain_vertical_boundary two_chain) +
           one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
    using boundary_is_vert_hor horiz_verti_disjoint
    by (auto simp add: one_chain_line_integral_def hor_vert_finite sum.union_disjoint)
  then have x_axis_line_integral_is_only_horizontal:
    "one_chain_line_integral F {i} (two_chain_boundary two_chain)
     = one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
    using vert_line_integral_zero by auto
      (*Since \<gamma> \<subseteq> the boundary of the 2-chain and the horizontal boundaries are \<subseteq> \<gamma>, then there is some \<V> \<subseteq> \<partial>\<^sub>V(2-\<C>) such that \<gamma> = \<V> \<union> \<partial>\<^sub>H(2-\<C>)*)
  obtain \<H> \<V> where hv_props: "finite \<V>"
    "(\<forall>(k,\<gamma>) \<in> \<V>. (\<exists>(k', \<gamma>') \<in> two_chain_vertical_boundary two_chain.
        (\<exists>a \<in> {0 .. 1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>)))" "\<gamma> = \<H> \<union> \<V>"
    "(common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>)
     \<or> common_reparam_exists \<H> (two_chain_horizontal_boundary two_chain)"
    "finite \<H>"
    "boundary_chain \<H>"
    "\<forall>(k,\<gamma>)\<in>\<H>. valid_path \<gamma>"
    using only_vertical_division by (auto simp add:  only_vertical_division_def)
  have "finite {i}" by auto
  then have eq_integrals: " one_chain_line_integral F {i} \<H> = one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
  proof(cases "common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>")
    case True
    then show ?thesis
      using gen_common_subdivision_imp_eq_line_integral(1)[OF True two_chain_horizontal_boundary_is_boundary_chain hv_props(6) _ hor_vert_finite(2) hv_props(5)]
        typeI_cube_line_integral_exists_boundary''
      by force
  next
    case False
    have integ_exis_horiz:
      "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {i} \<gamma>"
      using typeI_cube_line_integral_exists_boundary'' assms
      by (fastforce simp add: valid_two_chain_def)
    have integ_exis: "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
      using typeI_cube_line_integral_exists_boundary by blast
    have valid_paths: "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
      using typeI_edges_are_valid_paths assms
      by (fastforce simp add: two_chain_boundary_def two_chain_vertical_boundary_def boundary_def)
    have integ_exis_vert:
      "(\<And>k \<gamma>. (\<exists>(k', \<gamma>') \<in> two_chain_vertical_boundary two_chain. \<exists>a\<in>{0..1}. \<exists>b\<in>{0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>) \<Longrightarrow>
                                    line_integral_exists F {i} \<gamma>)"
      using integ_exis valid_paths line_integral_exists_subpath[of "F" "{i}"]
      by (fastforce simp add: two_chain_boundary_def two_chain_vertical_boundary_def
          two_chain_horizontal_boundary_def boundary_def)
    have finite_i: "finite {i}" by auto
    have i: "{i} \<subseteq> Basis" using i_is_x_axis real_pair_basis by auto
    have ii: " \<forall>(k2, \<gamma>2)\<in>two_chain_horizontal_boundary two_chain. \<forall>b\<in>{i}. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
      using assms(1) field_cont_on_typeI_region_cont_on_edges assms(2)
      by (fastforce simp add: analytically_valid_def two_chain_horizontal_boundary_def boundary_def path_image_def)
    have *: "common_reparam_exists \<H> (two_chain_horizontal_boundary two_chain)"
      using hv_props(4) False by auto
    show "one_chain_line_integral F {i} \<H> = one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
      using common_reparam_exists_imp_eq_line_integral(1)[OF finite_i hv_props(5) hor_vert_finite(2) hv_props(6) two_chain_horizontal_boundary_is_boundary_chain ii * hv_props(7) type_I_chain_horiz_bound_valid]
      by fastforce
  qed
    (*Since \<V> \<subseteq> \<partial>\<^sub>H(2-\<C>), then the line_integral on the x axis along \<V> is 0, and from 1 Q.E.D. *)
  have line_integral_on_path:
    "one_chain_line_integral F {i} \<gamma> =
     one_chain_line_integral F {i} (two_chain_horizontal_boundary two_chain)"
  proof (auto simp add: one_chain_line_integral_def)
    have "line_integral F {i} (snd oneCube) = 0" if oneCube: "oneCube \<in> \<V>" for oneCube
    proof -
      obtain k \<gamma> where k_gamma: "(k,\<gamma>) = oneCube"
        by (metis coeff_cube_to_path.cases)
      then obtain k' \<gamma>' a b where kp_gammap:
        "(k'::int, \<gamma>') \<in> two_chain_vertical_boundary two_chain"
        "a \<in> {0 .. 1}"
        "b \<in> {0..1}"
        "subpath a b \<gamma>' = \<gamma>"
        using hv_props oneCube
        by (smt case_prodE split_conv)
      obtain x y1 y2 where vert_edge_def: "(k',\<gamma>') = (k', (\<lambda>t::real. (x::real, (1 - t) * (y2) + t * y1)))"
        using valid_typeI_div kp_gammap
        by (auto simp add: typeI_twoCube_def two_chain_vertical_boundary_def vertical_boundary_def)
      have vert_edge_x_const: "\<forall>t. \<gamma> (t) \<bullet> i = x"
        by (metis (no_types, lifting) Pair_inject fstI i_is_x_axis inner_Pair_0(2) kp_gammap(4) real_inner_1_right subpath_def vert_edge_def)
      have "\<gamma> = (\<lambda>t::real. (x::real, (1 - (b - a)*t - a) * (y2) + ((b-a)*t + a) * y1))"
        using vert_edge_def Product_Type.snd_conv Product_Type.fst_conv kp_gammap(4)
        by (simp add: subpath_def diff_diff_eq[symmetric])
      also have "... = (\<lambda>t::real. (x::real, (1*y2 - a*y2) +  a*y1 + ((b-a)*y1 - (b - a)*y2)*t))"
        by (simp add: algebra_simps)
      finally have vert_edge_is_straight_path:
        "\<gamma> = (\<lambda>t::real. (x::real, (1*y2 - a*y2) +  a*y1 + ((b-a)*y1 - (b - a)*y2)*t))" .
      show "line_integral F {i} (snd oneCube) = 0"
      proof -
        have "\<forall>x. \<gamma> differentiable at x"
          by (simp add: straight_path_diffrentiable_x vert_edge_is_straight_path)
        then have "line_integral F {i} \<gamma> = 0"
          using line_integral_on_pair_straight_path(1) vert_edge_x_const by blast
        then show ?thesis
          using Product_Type.snd_conv k_gamma by auto
      qed
    qed
    then have "\<forall>x\<in>\<V>. (case x of (k, g) \<Rightarrow> (k::int) * line_integral F {i} g) = 0"
      by auto
    then show "(\<Sum>x\<in>\<gamma>. case x of (k, g) \<Rightarrow> real_of_int k * line_integral F {i} g) =
               (\<Sum>x\<in>two_chain_horizontal_boundary two_chain. case x of (k, g) \<Rightarrow> of_int k * line_integral F {i} g)"
      using hv_props(1) hv_props(3) hv_props(5) sum_zero_set hor_vert_finite(2) eq_integrals
      apply(auto simp add: one_chain_line_integral_def)
      by (smt Un_commute sum_zero_set)
  qed
  then have "one_chain_line_integral F {i} \<gamma> =
             one_chain_line_integral F {i} (two_chain_boundary two_chain)"
    using x_axis_line_integral_is_only_horizontal line_integral_on_path by auto
  then show ?thesis
    using assms GreenThm_typeI_divisible by auto
qed

end

locale green_typeI_typeII_chain = R2: R2 i j + T1: green_typeI_chain i j F two_chain_typeI + T2: green_typeII_chain i j F two_chain_typeII for i j F two_chain_typeI two_chain_typeII
begin

lemma GreenThm_typeI_typeII_divisible_region_boundary:
  assumes 
    gen_divisions: "gen_division s (cubeImage ` two_chain_typeI)"
    "gen_division s (cubeImage ` two_chain_typeII)" and
    typeI_two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain_typeI \<subseteq> \<gamma>" and
    typeII_two_cubes_trace_vertical_boundaries:
    "two_chain_vertical_boundary two_chain_typeII \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundaries:
    "\<gamma> \<subseteq> two_chain_boundary two_chain_typeI"
    "\<gamma> \<subseteq> two_chain_boundary two_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>a. F a \<bullet> j) i x - partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x)
         = one_chain_line_integral F {i, j} \<gamma>"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>a. F a \<bullet> i) j"
  let ?F_a' = "partial_vector_derivative (\<lambda>a. F a \<bullet> j) i"
  have typeI_regions_integral: "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x) = one_chain_line_integral F {i} \<gamma>"
    using T1.GreenThm_typeI_divisible_region_boundary
        gen_divisions(1) typeI_two_cubes_trace_horizontal_boundaries
        boundary_of_region_is_subset_of_partition_boundaries(1)
    by blast
  have typeII_regions_integral: "integral s (partial_vector_derivative (\<lambda>x. F x \<bullet> j) i) = one_chain_line_integral F {j} \<gamma>"
    using T2.GreenThm_typeII_divisible_region_boundary gen_divisions(2)
         typeII_two_cubes_trace_vertical_boundaries
        boundary_of_region_is_subset_of_partition_boundaries(2)
    by auto
  have integral_dis: "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = integral s (\<lambda>x. ?F_a' x) + integral s (\<lambda>x. - ?F_b' x)"
  proof -
    have "\<forall>twoCube \<in> two_chain_typeII. (?F_a' has_integral integral (cubeImage twoCube) ?F_a') (cubeImage twoCube)"
      by (simp add: analytically_valid_imp_part_deriv_integrable_on T2.F_anal_valid has_integral_iff)
    then have "\<And>u. u \<in> (cubeImage ` two_chain_typeII) \<Longrightarrow> (?F_a' has_integral integral u ?F_a') u"
      by auto
    then have "(?F_a' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeII. integral img ?F_a')) s"
      using gen_divisions(2) unfolding gen_division_def
      by (metis has_integral_Union)
    then have F_a'_integrable: "(?F_a' integrable_on s)" by auto
    have "\<forall>twoCube \<in> two_chain_typeI. (?F_b' has_integral integral (cubeImage twoCube) ?F_b') (cubeImage twoCube)"
      using analytically_valid_imp_part_deriv_integrable_on T1.F_anal_valid by blast
    then have "\<And>u. u \<in> (cubeImage ` two_chain_typeI) \<Longrightarrow> (?F_b' has_integral integral u ?F_b') u"
      by auto
    then have "(?F_b' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeI. integral img ?F_b')) s"
      using gen_divisions(1) unfolding gen_division_def
      by (metis has_integral_Union)
    then show ?thesis
      by (simp add: F_a'_integrable Henstock_Kurzweil_Integration.integral_diff has_integral_iff)
  qed
  have line_integral_dist: "one_chain_line_integral F {i, j} \<gamma> = one_chain_line_integral F {i} \<gamma> + one_chain_line_integral F {j} \<gamma>"
  proof (simp add: one_chain_line_integral_def)
    have "k * line_integral F {i, j} g = k * line_integral F {i} g +  k * line_integral F {j} g"
      if kg: "(k,g) \<in> \<gamma>" for k g
    proof -
      obtain twoCube_typeI where twoCube_typeI_props:
        "twoCube_typeI \<in> two_chain_typeI"
        "(k, g) \<in> boundary twoCube_typeI"
        "typeI_twoCube twoCube_typeI"
        "continuous_on (cubeImage twoCube_typeI) (\<lambda>x. F(x) \<bullet> i)"
        using boundary_of_region_is_subset_of_partition_boundaries(1) two_chain_boundary_def T1.valid_typeI_div
          T1.F_anal_valid kg
        by (auto simp add: analytically_valid_def)
      obtain twoCube_typeII where twoCube_typeII_props:
        "twoCube_typeII \<in> two_chain_typeII"
        "(k, g) \<in> boundary twoCube_typeII"
        "typeII_twoCube twoCube_typeII"
        "continuous_on (cubeImage twoCube_typeII) (\<lambda>x. F(x) \<bullet> j)"
        using boundary_of_region_is_subset_of_partition_boundaries(2) two_chain_boundary_def T2.valid_typeII_div
          kg T2.F_anal_valid
        by (auto simp add: analytically_valid_def)
      have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
      proof -
        have int_exists_i: "line_integral_exists F {i} g"
          using T1.typeI_cube_line_integral_exists_boundary assms kg
          by (auto simp add: valid_two_chain_def)
        have int_exists_j: "line_integral_exists F {j} g"
          using T2.typeII_cube_line_integral_exists_boundary assms kg
          by (auto simp add: valid_two_chain_def)
        have finite: "finite {i, j}" by auto
        show ?thesis
          using line_integral_sum_gen[OF finite int_exists_i int_exists_j] R2.i_is_x_axis R2.j_is_y_axis
          by auto
      qed
      then show "k * line_integral F {i, j} g = k * line_integral F {i} g + k * line_integral F {j} g"
        by (simp add: distrib_left)
    qed
    then have line_integral_distrib: 
          "(\<Sum>(k,g)\<in>\<gamma>. k * line_integral F {i, j} g) =
           (\<Sum>(k,g)\<in>\<gamma>. k * line_integral F {i} g +  k * line_integral F {j} g)"
      by (force intro: sum.cong split_cong)
    have "(\<lambda>x. (case x of (k, g) \<Rightarrow> (k::int) * line_integral F {i} g) + (case x of (k, g) \<Rightarrow> (k::int) * line_integral F {j} g)) =
                                     (\<lambda>x. (case x of (k, g) \<Rightarrow> (k * line_integral F {i} g) +  (k::int) * line_integral F {j} g))"
      using comm_monoid_add_class.sum.distrib by auto
    then show "(\<Sum>(k, g)\<in>\<gamma>. k * line_integral F {i, j} g) =
          (\<Sum>(k, g)\<in>\<gamma>. (k::int) * line_integral F {i} g) + (\<Sum>(k, g)\<in>\<gamma>. (k::int) * line_integral F {j} g)"
      using comm_monoid_add_class.sum.distrib[of "(\<lambda>(k, g).  k * line_integral F {i} g)" "(\<lambda>(k, g).  k * line_integral F {j} g)" \<gamma>]
        line_integral_distrib
      by presburger
  qed
  show ?thesis
    using integral_dis line_integral_dist typeI_regions_integral typeII_regions_integral
    by auto
qed

lemma GreenThm_typeI_typeII_divisible_region':
  assumes 
    only_vertical_division:
    "only_vertical_division one_chain_typeI two_chain_typeI"
    "boundary_chain one_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division one_chain_typeII two_chain_typeII"
    "boundary_chain one_chain_typeII" and
    typeI_and_typII_one_chains_have_gen_common_subdiv:
    "common_sudiv_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j"
  let ?F_a' = "partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i"
  have one_chain_i_integrals:
    "one_chain_line_integral F {i} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeII \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>) \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>)"
  proof (intro conjI)
    have "finite two_chain_typeI"
      using T1.valid_typeI_div finite_image_iff
      by (auto simp add: gen_division_def valid_two_chain_def)
    then show ii: "\<forall>(k, \<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>"
      using T1.members_of_only_vertical_div_line_integrable' assms 
      by fastforce
    have "finite (two_chain_horizontal_boundary two_chain_typeI)"
      by (meson T1.valid_typeI_div finite_imageD finite_two_chain_horizontal_boundary gen_division_def valid_two_chain_def)
    then have "finite one_chain_typeI"
      using only_vertical_division(1) only_vertical_division_def by auto
    moreover have "finite one_chain_typeII"
      using only_horizontal_division(1) only_horizontal_division_def by auto
    ultimately show "one_chain_line_integral F {i} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeII"
               and "\<forall>(k, \<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>"
      using gen_common_subdivision_imp_eq_line_integral[OF typeI_and_typII_one_chains_have_gen_common_subdiv
          only_vertical_division(2) only_horizontal_division(2)] ii 
      by auto
  qed
  have one_chain_j_integrals:
    "one_chain_line_integral F {j} one_chain_typeII = one_chain_line_integral F {j} one_chain_typeI \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>) \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>)"
  proof (intro conjI)
    have "finite two_chain_typeII"
      using T2.valid_typeII_div finite_image_iff
      by (auto simp add: gen_division_def valid_two_chain_def)
    then show ii: "\<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>"
      using T2.members_of_only_horiz_div_line_integrable' assms T2.two_chain_valid_valid_cubes by blast
    have typeII_and_typI_one_chains_have_common_subdiv: "common_sudiv_exists one_chain_typeII one_chain_typeI"
      by (simp add: common_sudiv_exists_comm typeI_and_typII_one_chains_have_gen_common_subdiv)
    have iv: "finite one_chain_typeI"
      using only_vertical_division(1) only_vertical_division_def by auto
    moreover have iv': "finite one_chain_typeII"
      using only_horizontal_division(1) only_horizontal_division_def by auto
    ultimately show "one_chain_line_integral F {j} one_chain_typeII =
                     one_chain_line_integral F {j} one_chain_typeI"
                    "\<forall>(k, \<gamma>)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>"
      using gen_common_subdivision_imp_eq_line_integral[OF typeII_and_typI_one_chains_have_common_subdiv
          only_horizontal_division(2) only_vertical_division(2) ii] ii 
      by auto
  qed
  have typeI_regions_integral:
    "integral s (\<lambda>x. - ?F_b' x) = one_chain_line_integral F {i} one_chain_typeI"
    using T1.GreenThm_typeI_divisible_region_boundary_gen T1.valid_typeI_div
          T1.F_anal_valid  only_vertical_division(1)
    by auto
  have typeII_regions_integral:
    "integral s ?F_a' = one_chain_line_integral F {j} one_chain_typeII"
    using T2.GreenThm_typeII_divisible_region_boundary_gen T2.valid_typeII_div
        T2.F_anal_valid  only_horizontal_division(1)
    by auto
  have line_integral_dist:
    "one_chain_line_integral F {i, j} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeI + one_chain_line_integral F {j} one_chain_typeI \<and>
     one_chain_line_integral F {i, j} one_chain_typeII = one_chain_line_integral F {i} one_chain_typeII + one_chain_line_integral F {j} one_chain_typeII"
  proof (simp add: one_chain_line_integral_def)
    have line_integral_distrib:
      "(\<Sum>(k,g)\<in>one_chain_typeI. k * line_integral F {i, j} g) =
       (\<Sum>(k,g)\<in>one_chain_typeI. k * line_integral F {i} g +  k * line_integral F {j} g) \<and>
       (\<Sum>(k,g)\<in>one_chain_typeII. k * line_integral F {i, j} g) =
       (\<Sum>(k,g)\<in>one_chain_typeII. k * line_integral F {i} g +  k * line_integral F {j} g)"
    proof -
      have 0: "k * line_integral F {i, j} g = k * line_integral F {i} g +  k * line_integral F {j} g"
        if  "(k,g) \<in> one_chain_typeII" for k g
      proof -
        have "line_integral_exists F {i} g" "line_integral_exists F {j} g" "finite {i, j}"
          using one_chain_i_integrals one_chain_j_integrals that by fastforce+
        moreover have "{i} \<inter> {j} = {}"
          by (simp add: R2.i_is_x_axis R2.j_is_y_axis)
        ultimately have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
          by (metis insert_is_Un line_integral_sum_gen(1))
        then show "k * line_integral F {i, j} g = k * line_integral F {i} g + k * line_integral F {j} g"
          by (simp add: distrib_left)
      qed
      have "k * line_integral F {i, j} g = k * line_integral F {i} g +  k * line_integral F {j} g"
        if "(k,g) \<in> one_chain_typeI" for k g
      proof -
        have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
          by (smt that disjoint_insert(2) finite.emptyI finite.insertI R2.i_is_x_axis inf_bot_right insert_absorb insert_commute insert_is_Un R2.j_is_y_axis line_integral_sum_gen(1) one_chain_i_integrals one_chain_j_integrals prod.case_eq_if singleton_inject snd_conv)
        then show "k * line_integral F {i, j} g = k * line_integral F {i} g + k * line_integral F {j} g"
          by (simp add: distrib_left)
      qed
      then show ?thesis
        using 0 by (smt sum.cong split_cong)
    qed
    show "(\<Sum>(k::int, g)\<in>one_chain_typeI. k * line_integral F {i, j} g) =
          (\<Sum>(k, g)\<in>one_chain_typeI. k * line_integral F {i} g) + (\<Sum>(k::int, g)\<in>one_chain_typeI. k * line_integral F {j} g) \<and>
          (\<Sum>(k::int, g)\<in>one_chain_typeII. k * line_integral F {i, j} g) =
          (\<Sum>(k, g)\<in>one_chain_typeII. k * line_integral F {i} g) + (\<Sum>(k::int, g)\<in>one_chain_typeII. k * line_integral F {j} g)"
    proof -
      have 0: "(\<lambda>x. (case x of (k::int, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k::int, g) \<Rightarrow> k * line_integral F {j} g)) =
                                  (\<lambda>x. (case x of (k::int, g) \<Rightarrow> (k * line_integral F {i} g) +  k * line_integral F {j} g))"
        using comm_monoid_add_class.sum.distrib by auto
      then have 1: "(\<Sum>x\<in>one_chain_typeI. (case x of (k::int, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k::int, g) \<Rightarrow> k * line_integral F {j} g)) =
                    (\<Sum>x\<in>one_chain_typeI. (case x of (k::int, g) \<Rightarrow>( k * line_integral F {i} g + k * line_integral F {j} g)))"
        by presburger
      have "(\<Sum>x\<in>one_chain_typeII. (case x of (k, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k, g) \<Rightarrow> k * line_integral F {j} g)) =
            (\<Sum>x\<in>one_chain_typeII. (case x of (k, g) \<Rightarrow>( k * line_integral F {i} g + k * line_integral F {j} g)))"
        using 0 by presburger
      then show ?thesis
        using sum.distrib[of "(\<lambda>(k, g).  k * line_integral F {i} g)" "(\<lambda>(k, g).  k * line_integral F {j} g)" "one_chain_typeI"]
          sum.distrib[of "(\<lambda>(k, g).  k * line_integral F {i} g)" "(\<lambda>(k, g).  k * line_integral F {j} g)" "one_chain_typeII"]
          line_integral_distrib 1
        by auto
    qed
  qed
  have integral_dis: "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = integral s (\<lambda>x. ?F_a' x) + integral s (\<lambda>x. - ?F_b' x)"
  proof -
    have "(?F_a' has_integral integral (cubeImage twoCube) ?F_a') (cubeImage twoCube)"
      if "twoCube \<in> two_chain_typeII" for twoCube
      by (simp add: analytically_valid_imp_part_deriv_integrable_on T2.F_anal_valid has_integral_integrable_integral that)
    then have "\<And>u. u \<in> (cubeImage ` two_chain_typeII) \<Longrightarrow> (?F_a' has_integral integral u ?F_a') u"
      by auto
    then have "(?F_a' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeII. integral img ?F_a')) s"
      using T2.valid_typeII_div unfolding gen_division_def
      by (metis has_integral_Union)
    then have F_a'_integrable:
      "(?F_a' integrable_on s)" by auto
    have "\<forall>twoCube \<in> two_chain_typeI. (?F_b' has_integral integral (cubeImage twoCube) ?F_b') (cubeImage twoCube)"
      using analytically_valid_imp_part_deriv_integrable_on T1.F_anal_valid by blast
    then have "\<And>u. u \<in> (cubeImage ` two_chain_typeI) \<Longrightarrow> (?F_b' has_integral integral u ?F_b') u"
      by auto
    then have "(?F_b' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeI. integral img ?F_b')) s"
      using T1.valid_typeI_div unfolding gen_division_def
      by (metis has_integral_Union)
    then show ?thesis
      by (simp add: F_a'_integrable Henstock_Kurzweil_Integration.integral_diff has_integral_iff)
  qed
  show "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = one_chain_line_integral F {i, j} one_chain_typeI"
    using one_chain_j_integrals integral_dis line_integral_dist typeI_regions_integral typeII_regions_integral
    by auto
  show "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = one_chain_line_integral F {i, j} one_chain_typeII"
    using one_chain_i_integrals integral_dis line_integral_dist typeI_regions_integral typeII_regions_integral
    by auto
qed

lemma GreenThm_typeI_typeII_divisible_region:
  assumes only_vertical_division:
    "only_vertical_division one_chain_typeI two_chain_typeI"
    "boundary_chain one_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division one_chain_typeII two_chain_typeII"
    "boundary_chain one_chain_typeII" and
    typeI_and_typII_one_chains_have_common_subdiv:
    "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
  using GreenThm_typeI_typeII_divisible_region' only_vertical_division only_horizontal_division common_subdiv_imp_gen_common_subdiv[OF typeI_and_typII_one_chains_have_common_subdiv]
  by auto

lemma GreenThm_typeI_typeII_divisible_region_finite_holes:
  assumes valid_cube_boundary: "\<forall>(k,\<gamma>)\<in>boundary C. valid_path \<gamma>" and
    only_vertical_division:
    "only_vertical_division (boundary C) two_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division (boundary C) two_chain_typeII" and
    s_is_oneCube: "s = cubeImage C"
  shows "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. F x \<bullet> i) j x) =
                     one_chain_line_integral F {i, j} (boundary C)"
  using GreenThm_typeI_typeII_divisible_region[OF only_vertical_division
      two_cube_boundary_is_boundary only_horizontal_division two_cube_boundary_is_boundary
      common_boundary_subdiv_exists_refl[OF assms(1)]] s_is_oneCube
  by auto

lemma GreenThm_typeI_typeII_divisible_region_equivallent_boundary:
  assumes 
    gen_divisions: "gen_division s (cubeImage ` two_chain_typeI)"
    "gen_division s (cubeImage ` two_chain_typeII)" and
    typeI_two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain_typeI \<subseteq> one_chain_typeI" and
    typeII_two_cubes_trace_vertical_boundaries:
    "two_chain_vertical_boundary two_chain_typeII \<subseteq> one_chain_typeII" and
    boundary_of_region_is_subset_of_partition_boundaries:
    "one_chain_typeI \<subseteq> two_chain_boundary two_chain_typeI"
    "one_chain_typeII \<subseteq> two_chain_boundary two_chain_typeII" and
    typeI_and_typII_one_chains_have_common_subdiv:
    "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
proof -
  let ?F_b' = "partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j"
  let ?F_a' = "partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i"
  have one_chain_i_integrals:
    "one_chain_line_integral F {i} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeII \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>) \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>)"
  proof (intro conjI)
    have i: "boundary_chain one_chain_typeI"
      using two_chain_boundary_is_boundary_chain boundary_chain_def
        boundary_of_region_is_subset_of_partition_boundaries(1)
      by blast
    have i': "boundary_chain one_chain_typeII"
      using two_chain_boundary_is_boundary_chain boundary_chain_def
        boundary_of_region_is_subset_of_partition_boundaries(2)
      by blast
    have "\<And>k \<gamma>. (k,\<gamma>)\<in>one_chain_typeI \<Longrightarrow> line_integral_exists F {i} \<gamma>"
      using T1.typeI_cube_line_integral_exists_boundary assms
      by (fastforce simp add: valid_two_chain_def)
    then show ii: "\<forall>(k,\<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>" by auto
    have "finite (two_chain_boundary two_chain_typeI)"
      unfolding two_chain_boundary_def
    proof (rule finite_UN_I)
      show "finite two_chain_typeI"
        using T1.valid_typeI_div finite_imageD gen_division_def valid_two_chain_def by auto
      show "\<And>a. a \<in> two_chain_typeI \<Longrightarrow> finite (boundary a)"
        by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
    qed
    then have "finite one_chain_typeI"
      using boundary_of_region_is_subset_of_partition_boundaries(1) finite_subset by fastforce
    moreover have "finite (two_chain_boundary two_chain_typeII)"
      unfolding two_chain_boundary_def
    proof (rule finite_UN_I)
      show "finite two_chain_typeII"
        using T2.valid_typeII_div finite_imageD gen_division_def valid_two_chain_def by auto
      show "\<And>a. a \<in> two_chain_typeII \<Longrightarrow> finite (boundary a)"
        by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
    qed
    then have "finite one_chain_typeII"
      using boundary_of_region_is_subset_of_partition_boundaries(2) finite_subset by fastforce
    ultimately show "one_chain_line_integral F {i} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeII"
      "\<forall>(k, \<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>"
      using ii common_subdivision_imp_eq_line_integral[OF typeI_and_typII_one_chains_have_common_subdiv
          i i' ii]
      by auto
  qed
  have one_chain_j_integrals:
    "one_chain_line_integral F {j} one_chain_typeI = one_chain_line_integral F {j} one_chain_typeII \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>) \<and>
              (\<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>)"
  proof (intro conjI)
    have i: "boundary_chain one_chain_typeI" and i': "boundary_chain one_chain_typeII"
      using two_chain_boundary_is_boundary_chain boundary_of_region_is_subset_of_partition_boundaries
      unfolding boundary_chain_def by blast+
    have "line_integral_exists F {j} \<gamma>" if "(k,\<gamma>)\<in>one_chain_typeII" for k \<gamma>
    proof -
      have F_is_continuous: "\<forall>twoC \<in> two_chain_typeII. continuous_on (cubeImage twoC) (\<lambda>a. F(a) \<bullet> j)"
        using T2.F_anal_valid by(simp add: analytically_valid_def)
      show "line_integral_exists F {j} \<gamma>"
        using that T2.valid_typeII_div
          boundary_of_region_is_subset_of_partition_boundaries(2)
        using green_typeII_cube.line_integral_exists_on_typeII_Cube_boundaries' assms valid_two_chain_def
        apply (simp add: two_chain_boundary_def)
        by (metis T2.typeII_cube_line_integral_exists_boundary case_prodD subset_iff that two_chain_boundary_def)
    qed
    then show ii: " \<forall>(k,\<gamma>)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>" by auto
    have "finite (two_chain_boundary two_chain_typeI)"
      unfolding two_chain_boundary_def
    proof (rule finite_UN_I)
      show "finite two_chain_typeI"
        using T1.valid_typeI_div finite_imageD gen_division_def valid_two_chain_def by auto
      show "\<And>a. a \<in> two_chain_typeI \<Longrightarrow> finite (boundary a)"
        by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
    qed
    then have iv: "finite one_chain_typeI"
      using boundary_of_region_is_subset_of_partition_boundaries(1) finite_subset
      by fastforce
    have "finite (two_chain_boundary two_chain_typeII)"
      unfolding two_chain_boundary_def
    proof (rule finite_UN_I)
      show "finite two_chain_typeII"
        using T2.valid_typeII_div finite_imageD gen_division_def valid_two_chain_def by auto
      show "\<And>a. a \<in> two_chain_typeII \<Longrightarrow> finite (boundary a)"
        by (simp add: boundary_def horizontal_boundary_def vertical_boundary_def)
    qed
    then have iv': "finite one_chain_typeII"
      using boundary_of_region_is_subset_of_partition_boundaries(2) finite_subset
      by fastforce
    have typeII_and_typI_one_chains_have_common_subdiv:
      "common_boundary_sudivision_exists one_chain_typeII one_chain_typeI"
      using typeI_and_typII_one_chains_have_common_subdiv
        common_boundary_sudivision_commutative
      by auto
    show "one_chain_line_integral F {j} one_chain_typeI = one_chain_line_integral F {j} one_chain_typeII" 
          "\<forall>(k, \<gamma>)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>"
      using common_subdivision_imp_eq_line_integral[OF typeII_and_typI_one_chains_have_common_subdiv
          i' i ii iv' iv] ii
      by auto
  qed
  have typeI_regions_integral:
    "integral s (\<lambda>x. - ?F_b' x) = one_chain_line_integral F {i} one_chain_typeI"
    using T1.GreenThm_typeI_divisible_region_boundary gen_divisions(1)
         typeI_two_cubes_trace_horizontal_boundaries
        boundary_of_region_is_subset_of_partition_boundaries(1)
    by auto
  have typeII_regions_integral:
    "integral s ?F_a' = one_chain_line_integral F {j} one_chain_typeII"
    using T2.GreenThm_typeII_divisible_region_boundary gen_divisions(2) 
        typeII_two_cubes_trace_vertical_boundaries
        boundary_of_region_is_subset_of_partition_boundaries(2)
    by auto
  have line_integral_dist:
    "one_chain_line_integral F {i, j} one_chain_typeI = one_chain_line_integral F {i} one_chain_typeI + one_chain_line_integral F {j} one_chain_typeI \<and>
     one_chain_line_integral F {i, j} one_chain_typeII = one_chain_line_integral F {i} one_chain_typeII + one_chain_line_integral F {j} one_chain_typeII"
  proof (simp add: one_chain_line_integral_def)
    have line_integral_distrib:
      "(\<Sum>(k,g)\<in>one_chain_typeI. k * line_integral F {i, j} g) =
       (\<Sum>(k,g)\<in>one_chain_typeI. k * line_integral F {i} g +  k * line_integral F {j} g) \<and>
       (\<Sum>(k,g)\<in>one_chain_typeII. k * line_integral F {i, j} g) =
       (\<Sum>(k,g)\<in>one_chain_typeII. k * line_integral F {i} g +  k * line_integral F {j} g)"
    proof -
      have 0: "k * line_integral F {i, j} g = k * line_integral F {i} g +  k * line_integral F {j} g"
        if "(k,g) \<in> one_chain_typeII" for k g
      proof -
        have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
        proof -
          have finite: "finite {i, j}" by auto
          have line_integral_all: "\<forall>i\<in>{i, j}. line_integral_exists F {i} g"
            using one_chain_i_integrals one_chain_j_integrals that by auto
          show ?thesis
            using line_integral_sum_gen[OF finite] R2.i_is_x_axis R2.j_is_y_axis line_integral_all by auto
        qed
        then show "k * line_integral F {i, j} g = k * line_integral F {i} g + k * line_integral F {j} g"
          by (simp add: distrib_left)
      qed
      have "k * line_integral F {i, j} g = k * line_integral F {i} g +  k * line_integral F {j} g"
        if "(k,g) \<in> one_chain_typeI" for k g
      proof -
        have finite: "finite {i, j}" by auto
        have line_integral_all: "\<forall>i\<in>{i, j}. line_integral_exists F {i} g"
          using one_chain_i_integrals one_chain_j_integrals that by auto
        have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
          using line_integral_sum_gen[OF finite] R2.i_is_x_axis R2.j_is_y_axis line_integral_all by auto
        then show "k * line_integral F {i, j} g = k * line_integral F {i} g + k * line_integral F {j} g"
          by (simp add: distrib_left)
      qed
      then show ?thesis
        using 0  by (smt sum.cong split_cong)
    qed
    show "(\<Sum>(k::int, g)\<in>one_chain_typeI. k * line_integral F {i, j} g) =
          (\<Sum>(k, g)\<in>one_chain_typeI. k * line_integral F {i} g) + (\<Sum>(k::int, g)\<in>one_chain_typeI. k * line_integral F {j} g) \<and>
          (\<Sum>(k::int, g)\<in>one_chain_typeII. k * line_integral F {i, j} g) =
          (\<Sum>(k, g)\<in>one_chain_typeII. k * line_integral F {i} g) + (\<Sum>(k::int, g)\<in>one_chain_typeII. k * line_integral F {j} g)"
    proof -
      have 0: "(\<lambda>x. (case x of (k::int, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k::int, g) \<Rightarrow> k * line_integral F {j} g)) =
                                  (\<lambda>x. (case x of (k::int, g) \<Rightarrow> (k * line_integral F {i} g) +  k * line_integral F {j} g))"
        using comm_monoid_add_class.sum.distrib by auto
      then have 1: "(\<Sum>x\<in>one_chain_typeI. (case x of (k::int, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k::int, g) \<Rightarrow> k * line_integral F {j} g)) =
                    (\<Sum>x\<in>one_chain_typeI. (case x of (k::int, g) \<Rightarrow>( k * line_integral F {i} g + k * line_integral F {j} g)))"
        by presburger
      have "(\<Sum>x\<in>one_chain_typeII. (case x of (k, g) \<Rightarrow> k * line_integral F {i} g) + (case x of (k, g) \<Rightarrow> k * line_integral F {j} g)) =
            (\<Sum>x\<in>one_chain_typeII. (case x of (k, g) \<Rightarrow>( k * line_integral F {i} g + k * line_integral F {j} g)))"
        using 0 by presburger
      then show ?thesis
        using sum.distrib[of "(\<lambda>(k, g).  k * line_integral F {i} g)" "(\<lambda>(k, g).  k * line_integral F {j} g)" "one_chain_typeI"]
          sum.distrib[of "(\<lambda>(k, g).  k * line_integral F {i} g)" "(\<lambda>(k, g).  k * line_integral F {j} g)" "one_chain_typeII"]
          line_integral_distrib
          1
        by auto
    qed
  qed
  have integral_dis: "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = integral s (\<lambda>x. ?F_a' x) + integral s (\<lambda>x. - ?F_b' x)"
  proof -
    have "(?F_a' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeII. integral img ?F_a')) s"
    proof -
      have "(?F_a' has_integral integral (cubeImage twoCube) ?F_a') (cubeImage twoCube)"
        if "twoCube \<in> two_chain_typeII" for twoCube
        by (simp add: analytically_valid_imp_part_deriv_integrable_on T2.F_anal_valid has_integral_integrable_integral that) 
      then have  "\<And>u. u \<in> (cubeImage ` two_chain_typeII) \<Longrightarrow> (?F_a' has_integral integral u ?F_a') u"
        by auto
      then show ?thesis
      using gen_divisions(2) unfolding gen_division_def
      by (metis has_integral_Union)
    qed
    then have F_a'_integrable:
      "(?F_a' integrable_on s)" by auto
    have "(?F_b' has_integral (\<Sum>img\<in>cubeImage ` two_chain_typeI. integral img ?F_b')) s"
    proof -
      have "\<forall>twoCube \<in> two_chain_typeI. (?F_b' has_integral integral (cubeImage twoCube) ?F_b') (cubeImage twoCube)"
        by (simp add: analytically_valid_imp_part_deriv_integrable_on T1.F_anal_valid has_integral_integrable_integral) 
      then have "\<And>u. u \<in> (cubeImage ` two_chain_typeI) \<Longrightarrow> (?F_b' has_integral integral u ?F_b') u"
        by auto
      then show ?thesis
      using gen_divisions(1) unfolding gen_division_def
      by (metis has_integral_Union)
    qed
    then show ?thesis
      using F_a'_integrable Henstock_Kurzweil_Integration.integral_diff by auto
  qed
  show "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = one_chain_line_integral F {i, j} one_chain_typeI"
    using one_chain_j_integrals integral_dis line_integral_dist typeI_regions_integral typeII_regions_integral
    by auto
  show "integral s (\<lambda>x. ?F_a' x - ?F_b' x) = one_chain_line_integral F {i, j} one_chain_typeII"
    using one_chain_i_integrals integral_dis line_integral_dist typeI_regions_integral typeII_regions_integral
    by auto
qed

end
end
