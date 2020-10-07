section \<open>Cotangent Space\<close>
theory Cotangent_Space
  imports Tangent_Space
begin

subsection \<open>Dual of a vector space\<close>

abbreviation "linear_fun_on S \<equiv> linear_on S (UNIV::real set) scaleR scaleR"

definition dual_space :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) set" where
  "dual_space S = {E. linear_fun_on S E \<and> extensional0 S E}"

lemma dual_space_eq:
  "dual_space S = {E. linear_fun_on S E} \<inter> {E. extensional0 S E}"
  by (auto simp: dual_space_def)

lemma mem_dual_space:
  "E \<in> dual_space S \<longleftrightarrow> linear_fun_on S E \<and> extensional0 S E"
  by (auto simp: dual_space_def)

lemma dual_spaceI:
  "E \<in> dual_space S"
  if "extensional0 S E" "linear_fun_on S E"
  using that
  by (auto simp: dual_space_def)

lemma dual_spaceD:
  assumes "E \<in> dual_space S"
  shows dual_space_linear_on: "linear_fun_on S E"
    and dual_space_restrict[simp]: "extensional0 S E"
  using assms by (auto simp: dual_space_def)

lemma linear_fun_on_zero:
  "linear_fun_on S 0"
  if "subspace S"
  by (unfold_locales, auto simp add: algebra_simps that[unfolded subspace_def])

lemma "linear_fun_on S x \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> x (a + b) = x a + x b"
  using linear_on.axioms module_hom_on.add by blast

lemma linear_fun_on_add:
  "linear_fun_on S (x + y)"
  if x: "linear_fun_on S x" and y: "linear_fun_on S y" and S: "subspace S"
  using x that
  by (unfold_locales, auto dest!: linear_on.axioms
      simp add: algebra_simps module_hom_on.add module_hom_on.scale subspace_def)

lemma linear_fun_on_scaleR:
  "linear_fun_on S (c *\<^sub>R x)"
  if x: "linear_fun_on S x" and S: "subspace S"
  using x that
  by (unfold_locales, auto dest!: linear_on.axioms
      simp add: module_hom_on.add module_hom_on.scale algebra_simps subspace_def)

lemma subspace_linear_fun_on:
  "subspace {E. linear_fun_on S E}"
  if "subspace S"
  by (auto simp: subspace_def linear_fun_on_zero[OF that]
      linear_fun_on_add[OF _ _ that] linear_fun_on_scaleR[OF _ that])

lemma subspace_dual_space:
  "subspace (dual_space S)"
  if "subspace S"
  unfolding dual_space_eq
  apply (rule subspace_inter)
   apply (rule subspace_linear_fun_on[OF that])
  apply (rule subspace_extensional0)
  done

subsection \<open>Dimension of dual space\<close>

text \<open>Mapping from S to the dual of S\<close>

context fixes B S assumes B: "independent B" "span B = S"
begin

definition "inner_Basis a b = (\<Sum>i\<in>B. representation B a i * representation B b i)"
  \<comment> \<open>TODO: move to library\<close>

definition std_dual :: "'a::real_vector \<Rightarrow> ('a \<Rightarrow> real)" where
  "std_dual a = restrict0 S (restrict0 S (\<lambda>b. inner_Basis a b))"

lemma inner_Basis_add:
  "b1 \<in> S \<Longrightarrow> b2 \<in> S \<Longrightarrow> inner_Basis (b1 + b2) v = inner_Basis b1 v + inner_Basis b2 v"
  by (auto simp: std_dual_def restrict0_def algebra_simps representation_add representation_scale
      B inner_Basis_def
      sum.distrib sum_distrib_left)

lemma inner_Basis_add2:
  "b1 \<in> S \<Longrightarrow> b2 \<in> S \<Longrightarrow> inner_Basis v (b1 + b2) = inner_Basis v b1 + inner_Basis v b2"
  by (auto simp: std_dual_def restrict0_def algebra_simps representation_add representation_scale
      B inner_Basis_def
      sum.distrib sum_distrib_left)
  
lemma inner_Basis_scale:
  "b1 \<in> S \<Longrightarrow> inner_Basis (c *\<^sub>R b1) v = c * inner_Basis b1 v"
  by (auto simp: std_dual_def restrict0_def algebra_simps representation_add representation_scale
      B inner_Basis_def sum.distrib sum_distrib_left)

lemma inner_Basis_scale2:
  "b1 \<in> S \<Longrightarrow> inner_Basis v (c *\<^sub>R b1) = c * inner_Basis v b1"
  by (auto simp: std_dual_def restrict0_def algebra_simps representation_add representation_scale
      B inner_Basis_def sum.distrib sum_distrib_left)

lemma inner_Basis_minus:
  "b1 \<in> S \<Longrightarrow> b2 \<in> S \<Longrightarrow> inner_Basis (b1 - b2) v = inner_Basis b1 v - inner_Basis b2 v"
  and inner_Basis_minus2:
  "b1 \<in> S \<Longrightarrow> b2 \<in> S \<Longrightarrow> inner_Basis v (b1 - b2) = inner_Basis v b1 - inner_Basis v b2"
  by (auto simp: std_dual_def restrict0_def algebra_simps representation_diff representation_scale
      B inner_Basis_def
      sum_subtractf sum_distrib_left)

lemma sum_zero_representation:
  "v = 0"
  if "\<And>b. b \<in> B \<Longrightarrow> representation B v b = 0" and v: "v \<in> S"
proof -
  have empty: "{b. representation B v b \<noteq> 0} = {}"
    using that(1) representation_ne_zero by auto
  have "v \<in> span B" using B v by simp
  from sum_nonzero_representation_eq[OF B(1) this]
  show ?thesis
    by (simp add: empty)
qed

lemma inner_Basis_0[simp]: "inner_Basis 0 a = 0" "inner_Basis a 0 = 0"
  by (auto simp: inner_Basis_def representation_zero)

lemma inner_Basis_eq_zeroI: "a = 0" if "inner_Basis a a = 0"
  and "finite B" "a \<in> S"
  by (rule sum_zero_representation)
    (use that in \<open>auto simp: inner_Basis_def that sum_nonneg_eq_0_iff\<close>)

lemma inner_Basis_zero: "inner_Basis a a = 0 \<longleftrightarrow> a = 0"
  if "finite B" "a \<in> S"
  by (auto simp: inner_Basis_eq_zeroI that)

lemma subspace_S: "subspace S"
  using B by auto

interpretation S: real_vector_space_on S
  using subspace_S
  by unfold_locales

interpretation dual: real_vector_space_on "dual_space S"
  using subspace_dual_space[OF subspace_S]
  by unfold_locales

lemma std_dual_linear:
  "linear_on S (dual_space S) scaleR scaleR std_dual"
  by unfold_locales
    (auto simp add: subspace_S[unfolded subspace_def] subspace_dual_space[unfolded subspace_def] algebra_simps
      std_dual_def inner_Basis_scale inner_Basis_add restrict0_def)
  
lemma image_std_dual:
  "std_dual ` S \<subseteq> dual_space S"
  if "subspace S"
proof safe
  fix y assume "y \<in> S"
  show "std_dual y \<in> dual_space S"
  proof (rule dual_spaceI)
    show "extensional0 S (std_dual y)"
      by (auto simp: std_dual_def)
    show "linear_fun_on S (std_dual y)"
      by (unfold_locales, auto simp: std_dual_def algebra_simps that[unfolded subspace_def]
        inner_Basis_add2 inner_Basis_scale2 B)
  qed
qed

lemma inj_std_dual:
  "inj_on std_dual S"
  if "subspace S" "finite B"
proof (intro inj_onI)
  fix x y assume x: "x \<in> S" and y: "y \<in> S" and eq: "std_dual x = std_dual y"
  have 1: "inner_Basis x b = inner_Basis y b" if b: "b \<in> S" for b
  proof -
    have "std_dual x b = inner_Basis x b" "std_dual y b = inner_Basis y b"
      unfolding std_dual_def restrict0_def
      using b by auto
    then show ?thesis using eq by auto
  qed
  have 2: "x - y \<in> S" using that(1) x y by (rule subspace_diff)
  have "inner_Basis x (x - y) - inner_Basis y (x - y) = 0" using 1 2 by auto
  then have "inner_Basis (x - y) (x - y) = 0"
    by (auto simp: inner_Basis_minus inner_Basis_minus2 2 B x y algebra_simps)
  then show "x = y" 
    by (auto simp: inner_Basis_zero B that 2)
qed

lemma inner_Basis_sum:
  "(\<And>i. i \<in> I \<Longrightarrow> x i \<in> S) \<Longrightarrow> inner_Basis (\<Sum>i\<in>I. x i) v = (\<Sum>i\<in>I. inner_Basis (x i) v)"
  apply (induction I rule: infinite_finite_induct)
    apply (auto simp: )
  apply (subst inner_Basis_add)
  apply auto
  by (metis B(2) subspace_span subspace_sum)

lemma inner_Basis_sum2:
  "(\<And>i. i \<in> I \<Longrightarrow> x i \<in> S) \<Longrightarrow> inner_Basis v (\<Sum>i\<in>I. x i) = (\<Sum>i\<in>I. inner_Basis v (x i))"
  apply (induction I rule: infinite_finite_induct)
    apply (auto simp: )
  apply (subst inner_Basis_add2)
  apply auto
  by (metis B(2) subspace_span subspace_sum)

lemma B_sub_S: "B \<subseteq> S"
  using B(2) span_eq by auto

lemma inner_Basis_eq_representation:
  "inner_Basis i x = representation B x i"
  if "i \<in> B" "finite B"
  unfolding inner_Basis_def
  by (simp add: B that representation_basis if_distrib if_distribR cong: if_cong)

lemma surj_std_dual:
  "std_dual ` S \<supseteq> dual_space S" if "subspace S" "finite B"
proof safe
  fix y
  assume y: "y \<in> dual_space S"
  show "y \<in> std_dual ` S"
  proof -
    (* Basic idea: let v_i be a basis of S. Let x be the sum of (y v_i) * v_i.
       Then y should be equal to std_dual S ` x. *)
    let ?x = "\<Sum>i\<in>B. (y i) *\<^sub>R i"
    have x: "?x \<in> S"
      using that(1) apply (rule subspace_sum) using that(1) apply (rule subspace_scale)
      using B span_superset
      by auto
    from dual_space_linear_on[OF y]
    have linear_y: "linear_fun_on S y" .
    then interpret linear_on S UNIV scaleR scaleR y .
    interpret vector_space_pair_on S "UNIV::real set" scaleR scaleR by unfold_locales
    have "y = std_dual ?x"
      apply (rule ext_extensional0[of S])
      subgoal using y dual_space_def by auto
      subgoal by (auto simp: std_dual_def)
      unfolding std_dual_def restrict0_def apply auto
      apply (subst inner_Basis_sum) subgoal
        using B(2) span_base subspace_scale by blast
      subgoal for x
      proof goal_cases
        case 1
        have "(\<Sum>i\<in>B. inner_Basis (y i *\<^sub>R i) x) = (\<Sum>i\<in>B. y (inner_Basis i x *\<^sub>R i))"
        proof (rule sum.cong[OF refl])
          fix i assume i: "i \<in> B"
          then have "i : S" using B_sub_S by auto
          have "inner_Basis (y i *\<^sub>R i) x = y i * inner_Basis i x"
            apply (subst inner_Basis_scale)
            subgoal using B_sub_S i by auto
            apply (rule refl)
            done
          also have "\<dots> = y i *\<^sub>R inner_Basis i x" by simp
          also have "\<dots> = y (inner_Basis i x *\<^sub>R i)"
            by (auto simp: \<open>i \<in> S\<close> scale)
          finally show "inner_Basis (y i *\<^sub>R i) x = y (inner_Basis i x *\<^sub>R i)" .
        qed
        also have "\<dots> = y (\<Sum>i\<in>B. (inner_Basis i x *\<^sub>R i))" (is "_ = y ?sum")
          apply (subst linear_sum'[OF _ _ linear_y])
            apply (auto simp: inner_Basis_eq_representation)
          using B(2) S.mem_scale span_base by blast
        also have "?sum = x"
          apply (subst sum.cong[OF refl])
           apply (subst inner_Basis_eq_representation, assumption, rule that, rule refl)
          apply (subst sum_representation_eq)
          by (auto simp: that B \<open>x : S\<close>)
        finally show ?thesis by simp
      qed
      done
    then show ?thesis
      using x by auto
  qed
qed

lemma std_dual_bij_betw:
  "bij_betw (std_dual) S (dual_space S)"
  if "finite B"
  unfolding bij_betw_def
  using subspace_S inj_std_dual image_std_dual surj_std_dual that by blast

lemma std_dual_eq_dual_space: "finite B \<Longrightarrow> std_dual ` S = dual_space S"
  using image_std_dual surj_std_dual subspace_S by auto

lemma dim_dual_space:
  assumes "finite B"
  shows "dim (dual_space S) = dim S"
proof -
  interpret finite_dimensional_real_vector_space_pair_1_on S "dual_space S" B
    using B assms span_superset
    by unfold_locales auto
  have *: "span S = S" using subspace_S by auto
  then have "dual.dim (std_dual ` S) = S.dim S"
    apply (intro dim_image_eq[OF _ order_refl std_dual_linear])
    using std_dual_bij_betw[OF assms]
    by (auto simp: bij_betw_def *)
  also have "S.dim S = dim S"
    unfolding S.dim_eq[OF order_refl] ..
  also have "dual.dim (std_dual ` S) = dim (std_dual ` S)"
    using image_std_dual[OF subspace_S]  
    by (rule dual.dim_eq)
  also have "std_dual ` S = dual_space S"
    using assms
    by (rule std_dual_eq_dual_space)
  finally show ?thesis .
qed

end

subsection \<open>Dual map\<close>

context real_vector_space_pair_on begin

definition dual_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where
  "dual_map f y = restrict0 S (\<lambda>x. y (f x))"

lemma subspace_dual_S: "subspace (dual_space S)"
  apply (rule subspace_dual_space)
  apply (rule local.vs1.subspace)
  done

lemma subspace_dual_T: "subspace (dual_space T)"
  apply (rule subspace_dual_space)
  apply (rule local.vs2.subspace)
  done

lemma dual_map_linear:
  "linear_on (dual_space T) (dual_space S) scaleR scaleR (dual_map f)"
  apply unfold_locales
  by (auto simp add: dual_map_def restrict0_def subspace_dual_S[unfolded subspace_def]
                     subspace_dual_T[unfolded subspace_def] algebra_simps)

lemma image_dual_map:
  "dual_map f ` (dual_space T) \<subseteq> dual_space S"
  if f: "linear_on S T scaleR scaleR f" and
  defined: "f ` S \<subseteq> T"
proof safe
  fix x assume x: "x \<in> dual_space T"
  show "dual_map f x \<in> dual_space S"
  proof (rule dual_spaceI)
    have 1: "linear_fun_on T x"
      using x by (rule dual_space_linear_on)
    show "extensional0 S (dual_map f x)" by (auto simp: dual_map_def)
    show "linear_fun_on S (dual_map f x)"
      apply (unfold_locales, auto simp: dual_map_def restrict0_def linear_on_def algebra_simps 
             local.vs1.subspace[unfolded subspace_def])
    proof -
      show "x (f (b1 + b2)) = x (f b1) + x (f b2)" if "b1 \<in> S" "b2 \<in> S" for b1 b2
      proof -
        have "f b1 \<in> T" using \<open>b1 \<in> S\<close> defined by auto
        have "f b2 \<in> T" using \<open>b2 \<in> S\<close> defined by auto
        have "x (f (b1 + b2)) = x (f b1 + f b2)"
          by (auto simp: f[THEN linear_on.axioms, THEN module_hom_on.add] that)
        also have "x (f b1 + f b2) = x (f b1) + x (f b2)"
          by (auto simp: 1[THEN linear_on.axioms, THEN module_hom_on.add] \<open>f b1 \<in> T\<close> \<open>f b2 \<in> T\<close>)
        finally show ?thesis .
      qed
      show "x (f (r *\<^sub>R b)) = r * x (f b)" if "b \<in> S" for r b
      proof -
        have "f b \<in> T" using \<open>b \<in> S\<close> defined by auto
        have "x (f (r *\<^sub>R b)) = x (r *\<^sub>R f b)"
          by (auto simp: f[THEN linear_on.axioms, THEN module_hom_on.scale] that)
        also have "x (r *\<^sub>R f b) = r * x (f b)"
          by (auto simp: 1[THEN linear_on.axioms, THEN module_hom_on.scale] \<open>f b \<in> T\<close>)
        finally show ?thesis .
      qed
    qed
  qed
qed

end

text \<open>Functoriality of dual map: identity\<close>

context real_vector_space_on begin

lemma dual_map_id:
  "real_vector_space_pair_on.dual_map S f y = y"
  if f: "\<And>x. x \<in> S \<Longrightarrow> f x = x" and y: "y \<in> dual_space S"
proof (rule ext_extensional0[of S])
  have 1: "real_vector_space_pair_on S S" ..
  show "extensional0 S (real_vector_space_pair_on.dual_map S f y)"
    unfolding real_vector_space_pair_on.dual_map_def[OF 1] by auto
  show "extensional0 S y"
    using y by auto
  fix x assume x: "x \<in> S"
  show "real_vector_space_pair_on.dual_map S f y x = y x"
  proof -
    have "real_vector_space_pair_on.dual_map S f y x = y (f x)"
      by (auto simp: real_vector_space_pair_on.dual_map_def[OF 1] restrict0_def x)
    also have "y (f x) = y x"
      using f x by auto
    finally show ?thesis .
  qed
qed

end

abbreviation "dual_map \<equiv> real_vector_space_pair_on.dual_map"
lemmas dual_map_def = real_vector_space_pair_on.dual_map_def

text \<open>Functoriality of dual map: composition\<close>

lemma dual_map_compose:
  "dual_map S f (dual_map T g x) = dual_map S (g \<circ> f) x"
  if "x \<in> dual_space U" and "linear_on T U scaleR scaleR g"
  and f: "linear_on S T scaleR scaleR f"
  and defined: "f ` S \<subseteq> T"
  and ST: "real_vector_space_pair_on S T"
  and TU: "real_vector_space_pair_on T U"
proof (rule ext)
  have SU: "real_vector_space_pair_on S U"
    using ST TU by (auto simp add: real_vector_space_pair_on_def)
  fix v show "dual_map S f (dual_map T g x) v = dual_map S (g \<circ> f) x v"    
  unfolding dual_map_def[OF ST] dual_map_def[OF TU] dual_map_def[OF SU] restrict0_def
  using defined by auto
qed

subsection \<open>Definition of cotangent space\<close>

context c_manifold begin

definition cotangent_space :: "'a \<Rightarrow> ((('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real) set" where
  "cotangent_space p = dual_space (tangent_space p)"

lemma subspace_cotangent_space:
  "subspace (cotangent_space p)"
  unfolding cotangent_space_def
  apply (rule subspace_dual_space)
  apply (rule subspace_tangent_space)
  done

sublocale cotangent_space: real_vector_space_on "cotangent_space p"
  by unfold_locales (rule subspace_cotangent_space)

(* Shouldn't there be a general theorem for this, instead of repeating the proof
   for tangent_space_dim_eq?
*)
lemma cotangent_space_dim_eq: "cotangent_space.dim p X = dim X"
  if "X \<subseteq> cotangent_space p"
proof -
  have *: "b \<subseteq> cotangent_space p \<and> independent b \<and> span b = span X \<longleftrightarrow> independent b \<and> span b = span X"
    for b
    using that
    by auto (metis (no_types, lifting) c_manifold.subspace_cotangent_space c_manifold_axioms span_base span_eq_iff span_mono subsetCE)  
  show ?thesis
    using that
    unfolding cotangent_space.dim_def dim_def *
    by auto
qed

lemma dim_cotangent_space:
  "dim (cotangent_space p) = DIM('b)" if "p \<in> carrier" and "k = \<infinity>"
proof -
  from basis_exists[of "tangent_space p"]
  obtain B where B: "B \<subseteq> tangent_space p" "independent B" "tangent_space p \<subseteq> span B"
    "card B = dim (tangent_space p)"
    by auto
  have "finite B"
    apply (rule card_ge_0_finite)
    unfolding B
    apply (subst dim_tangent_space[OF that])
    by simp
  have "dim (cotangent_space p) = dim (tangent_space p)"
    unfolding cotangent_space_def
    apply (rule dim_dual_space[of B])
    apply fact
    using B span_minimal[OF B(1) subspace_tangent_space] \<open>finite B\<close>
    by auto
  also have "dim (tangent_space p) = DIM('b)"
    by (rule dim_tangent_space[OF that])
  finally show ?thesis .
qed

end

subsection \<open>Pullback of cotangent space\<close>

context diff begin

definition pull_back :: "'a \<Rightarrow> ((('b \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real" where
  "pull_back p = dual_map (src.tangent_space p) push_forward"

lemma
  linear_pullback: "linear_on (dest.cotangent_space (f p)) (src.cotangent_space p) scaleR scaleR (pull_back p)" and
  image_pullback: "pull_back p ` (dest.cotangent_space (f p)) \<subseteq> src.cotangent_space p"
  if "p \<in> src.carrier"
proof -
  interpret a: real_vector_space_pair_on "src.tangent_space p" "dest.tangent_space (f p)" ..
  show "linear_on (dest.cotangent_space (f p)) (src.cotangent_space p) (*\<^sub>R) (*\<^sub>R) (pull_back p)"
    unfolding dest.cotangent_space_def src.cotangent_space_def pull_back_def
    by (rule a.dual_map_linear)
  show "pull_back p ` (dest.cotangent_space (f p)) \<subseteq> src.cotangent_space p"
    unfolding dest.cotangent_space_def src.cotangent_space_def pull_back_def
    apply (rule a.image_dual_map)
    apply (rule linear_imp_linear_on)
      apply (rule local.linear_push_forward)
      apply (rule local.src.subspace_tangent_space)
     apply (rule local.dest.subspace_tangent_space)
    apply (rule local.push_forward_in_tangent_space)
    by fact
qed

end

subsection \<open>Cotangent field of a function\<close>

context c_manifold begin

text \<open>Given a function f, the cotangent vector of f at a point p is defined
  as follows: given a tangent vector X at p, considered as a functional, evaluate
  X on f.\<close>

definition cotangent_field :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ((('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> real)" where
  "cotangent_field f p = restrict0 (tangent_space p) (\<lambda>X. X f)"

lemma cotangent_field_is_cotangent:
  "cotangent_field f p \<in> cotangent_space p"
  unfolding cotangent_space_def
proof (rule dual_spaceI)
  show "extensional0 (tangent_space p) (cotangent_field f p)"
    unfolding cotangent_field_def by auto
  show "linear_fun_on (tangent_space p) (cotangent_field f p)"
    apply unfold_locales unfolding cotangent_field_def apply auto
  proof -
    show "restrict0 (tangent_space p) (\<lambda>X. X f) (b1 + b2) = b1 f + b2 f"
      if b1: "b1 \<in> tangent_space p" and b2: "b2 \<in> tangent_space p" for b1 b2
    proof -
      have "b1 + b2 \<in> tangent_space p" using b1 b2 subspace_tangent_space subspace_add by auto
      then show ?thesis by auto
    qed
    show "restrict0 (tangent_space p) (\<lambda>X. X f) (r *\<^sub>R b) = r * b f"
      if b: "b \<in> tangent_space p" for r b
    proof -
      have "r *\<^sub>R b \<in> tangent_space p" using b subspace_tangent_space subspace_scale by auto
      then show ?thesis by auto
    qed
  qed
qed

subsection \<open>Tangent field of a path\<close>

(* Note: an alternative definition is as follows: consider the path as
   a smooth map from the manifold with boundary [a,b], then take the
   push-forward of the trivial tangent field on [a,b]. In this case,
   showing this is a tangent vector would be trivial. *)

text \<open>Given a path \<open>c\<close>, the tangent vector of \<open>c\<close> at real number \<open>x\<close> (or at point \<open>c(x)\<close>)
  is defined as follows: given a function f, take the derivative of the
  real-valued function \<open>f \<circ> c\<close>.\<close>

definition tangent_field :: "(real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real)" where
  "tangent_field c x = restrict0 diff_fun_space (\<lambda>f. frechet_derivative (f \<circ> c) (at x) 1)"

lemma tangent_field_is_tangent:
  "tangent_field c x \<in> tangent_space (c x)"
  if c_smooth: "diff k charts_eucl charts c" and smooth: "k > 0"
proof (rule tangent_spaceI)
  show "extensional0 diff_fun_space (tangent_field c x)"
    unfolding tangent_field_def by auto
  have diff_fun_c_diff: "(\<lambda>x. b (c x)) differentiable at x"
    if b: "b \<in> diff_fun_space"
    for b::"'a \<Rightarrow> real" and x
  proof -
    have diff_b: "diff_fun k charts_eucl (b o c)"
      unfolding diff_fun_def
      using c_smooth diff_fun_spaceD[OF b, THEN diff_fun.axioms]
      by (rule diff_compose)
    from diff_fun_charts_euclD[OF this] smooth
    have "(b o c) differentiable_on UNIV"
      by (rule smooth_on_imp_differentiable_on)
    then show ?thesis by (auto simp: differentiable_on_def o_def)
  qed
  show "linear_fun_on diff_fun_space (tangent_field c x)"
    apply unfold_locales unfolding cotangent_field_def apply auto
  proof -
    show "tangent_field c x (b1 + b2) = tangent_field c x b1 + tangent_field c x b2"
      if b1: "b1 \<in> diff_fun_space" and b2: "b2 \<in> diff_fun_space" for b1 b2
      unfolding tangent_field_def restrict0_def
      by (auto simp: diff_fun_space_add o_def diff_fun_c_diff b1 b2 frechet_derivative_plus)
    show "tangent_field c x (r *\<^sub>R b) = r * tangent_field c x b"
      if b: "b \<in> diff_fun_space" for r b
      unfolding tangent_field_def restrict0_def
      by (auto simp: diff_fun_space.m1.mem_scale o_def diff_fun_c_diff b frechet_derivative_times
          frechet_derivative_const)
  qed
  show "tangent_field c x (f * g) = f (c x) * tangent_field c x g + g (c x) * tangent_field c x f"
    if f: "f \<in> diff_fun_space" and g: "g \<in> diff_fun_space" for f g
    unfolding tangent_field_def restrict0_def
    by (auto simp: f g diff_fun_space_times diff_fun_space_add o_def diff_fun_c_diff
        frechet_derivative_plus frechet_derivative_times)
qed

subsection \<open>Integral along a path\<close>

lemma fundamental_theorem_of_path_integral:
  "((\<lambda>x. (cotangent_field f (c x)) (tangent_field c x)) has_integral f (c b) - f (c a)) {a..b}"
  if ab: "a \<le> b" and f: "f \<in> diff_fun_space" and c: "diff k charts_eucl charts c" and k: "k \<noteq> 0"
proof -
  from f have "diff k charts charts_eucl f"
    by (auto simp: diff_fun_space_def diff_fun_def)
  then have "(diff_fun k charts_eucl (f o c))"
    unfolding diff_fun_def
    apply (intro diff_compose)
     apply (rule c)
    apply assumption
    done
  then have "k-smooth_on UNIV (f o c)"
    by (rule diff_fun_charts_euclD)
  then have "(f o c) differentiable_on UNIV"
    by (rule smooth_on_imp_differentiable_on) (use k in simp)
  then have fc: "(\<lambda>a. f (c a)) differentiable at x" for x
    by (auto simp: differentiable_on_def o_def)
  then show ?thesis
    using ab
    unfolding cotangent_field_def
    apply (auto simp: tangent_field_is_tangent c k)
    unfolding tangent_field_def
    apply (auto simp: f)
    apply (rule fundamental_theorem_of_calculus)
     apply assumption
     apply (rule has_vector_derivative_at_within)
    unfolding o_def has_vector_derivative_def
    apply (subst frechet_derivative_at_real_eq_scaleR[symmetric])
    apply simp
    apply (rule frechet_derivative_worksI)
    apply simp
    done
qed

end

end
