section \<open>Projective Space\<close>
theory Projective_Space
  imports Differentiable_Manifold "HOL-Library.Quotient_Set"
begin

text \<open>Some of the main things to note here: double transfer (-> nonzero -> quotient)\<close>

subsection \<open>Subtype of nonzero elements\<close>

lemma open_ne_zero: "open {x::'a::t1_space. x \<noteq> c}"
proof -
  have "{x::'a. x \<noteq> c} = UNIV - {c}" by auto
  also have "open \<dots>" by (rule open_delete; rule open_UNIV)
  finally show ?thesis .
qed

typedef (overloaded) 'a::euclidean_space nonzero = "UNIV - {0::'a::euclidean_space}" by auto

setup_lifting type_definition_nonzero

instantiation nonzero :: (euclidean_space) topological_space
begin

lift_definition open_nonzero::"'a nonzero set \<Rightarrow> bool" is "open::'a set \<Rightarrow> bool" .

instance
  apply standard
  subgoal by transfer (auto simp: open_ne_zero)
  subgoal by transfer auto
  subgoal by transfer auto
  done

end

lemma open_nonzero_openin_transfer:
  "(rel_set (pcr_nonzero A) ===> (=)) (openin (top_of_set (Collect (Domainp (pcr_nonzero A))))) open"
  if "is_equality A"
  unfolding is_equality_def[THEN iffD1, OF that]
proof
  fix X::"'a set" and Y::"'a nonzero set"
  assume t[transfer_rule]: "rel_set (pcr_nonzero (=)) X Y"
  show "openin (top_of_set (Collect (Domainp (pcr_nonzero (=))))) X = open Y"
    apply (auto simp: openin_subtopology)
    subgoal by transfer (auto simp: nonzero.domain_eq open_ne_zero)
    subgoal
      apply transfer
      apply (rule exI[where x=X])
      using t
      by (auto simp: rel_set_def)
    done
qed

instantiation nonzero :: (euclidean_space) scaleR
begin
lift_definition scaleR_nonzero::"real \<Rightarrow> 'a nonzero \<Rightarrow> 'a nonzero" is "\<lambda>c x. if c = 0 then One else c *\<^sub>R x"
  by auto
instance ..

end

instantiation nonzero :: (euclidean_space) plus
begin
lift_definition plus_nonzero::"'a nonzero \<Rightarrow> 'a nonzero \<Rightarrow> 'a nonzero" is "\<lambda>x y. if x + y = 0 then One else x + y"
  by auto
instance ..
end

instantiation nonzero :: (euclidean_space) minus
begin
lift_definition minus_nonzero::"'a nonzero \<Rightarrow> 'a nonzero \<Rightarrow> 'a nonzero" is "\<lambda>x y. if x = y then One else x - y"
  by auto
instance ..
end

instantiation nonzero :: (euclidean_space) dist
begin
lift_definition dist_nonzero::"'a nonzero \<Rightarrow> 'a nonzero \<Rightarrow> real" is dist .
instance ..
end

instantiation nonzero :: (euclidean_space) norm
begin
lift_definition norm_nonzero::"'a nonzero \<Rightarrow> real" is norm .
instance ..
end

instance nonzero :: (euclidean_space) t2_space
  apply standard
  apply transfer
  subgoal for x y
    using hausdorff[of x y]
    apply clarsimp
    subgoal for U V
      apply (rule exI[where x="U - {0}"])
      apply clarsimp
      apply (rule conjI) defer
       apply (rule exI[where x="V - {0}"])
      by auto
    done
  done

lemma scaleR_one_nonzero[simp]: "1 *\<^sub>R x = (x::_ nonzero)"
  by transfer auto

lemma scaleR_scaleR_nonzero[simp]: "b \<noteq> 0 \<Longrightarrow> scaleR a (scaleR b x) = scaleR (a * b) (x::_ nonzero)"
  by transfer auto

instance nonzero :: (euclidean_space) second_countable_topology
proof standard
  from ex_countable_basis[where 'a='a] obtain A::"'a set set" where "countable A" "topological_basis A"
    by auto
  define B where "B = (\<lambda>X. Abs_nonzero ` (X - {0})) ` A"
  have [transfer_rule]: "rel_set (rel_set (pcr_nonzero (=))) ((\<lambda>X. X - {0})`A) B"
    by (clarsimp simp: B_def rel_set_def pcr_nonzero_def OO_def cr_nonzero_def)
      (metis Abs_nonzero_inverse Diff_iff UNIV_I singleton_iff)
  from \<open>topological_basis A\<close>
  have "topological_basis B"
    unfolding topological_basis_def
    apply transfer
    apply safe
     apply force
    subgoal for X
      apply (drule spec[where x=X])
      apply clarsimp
      subgoal for B'
        apply (rule exI[where x=B'])
        by auto
      done
    done
  then show "\<exists>B::'a nonzero set set. countable B \<and> open = generate_topology B"
    apply (intro exI[where x=B])
    by (auto simp add: B_def \<open>countable A\<close> topological_basis_imp_subbasis)
qed


subsection \<open>Quotient\<close>

inductive proj_rel :: "'a::euclidean_space nonzero \<Rightarrow> 'a nonzero \<Rightarrow> bool" for x where
  "c \<noteq> 0 \<Longrightarrow> proj_rel x (c *\<^sub>R x)"

lemma proj_rel_parametric: "(pcr_nonzero A ===> pcr_nonzero A ===> (=)) proj_rel proj_rel"
  if [transfer_rule]: " ((=) ===> pcr_nonzero A ===> pcr_nonzero A) (*\<^sub>R) (*\<^sub>R)"
    "bi_unique A"
  unfolding proj_rel.simps
  by transfer_prover

quotient_type (overloaded) 'a proj_space = "('a::euclidean_space \<times> real) nonzero" /  proj_rel
  morphisms rep_proj Proj
    parametric proj_rel_parametric
proof (rule equivpI)
  show "reflp proj_rel"
    using proj_rel.intros[where c=1, simplified] by (auto simp: reflp_def)
  show "symp proj_rel"
    unfolding symp_def
    apply (auto elim!: proj_rel.cases)
    subgoal for x c
      by (rule proj_rel.intros[of "inverse c" "c *\<^sub>R x", simplified])
    done
  show "transp proj_rel"
    unfolding transp_def
    by (auto elim!: proj_rel.cases intro!: proj_rel.intros)
qed

lemma surj_Proj: "surj Proj"
  apply safe
  subgoal by force
  subgoal for x by (induct x) auto
  done

definition proj_topology :: "'a::euclidean_space proj_space topology" where
  "proj_topology = map_topology Proj euclidean"

instantiation proj_space :: (euclidean_space) topological_space
begin

definition open_proj_space :: "'a proj_space set \<Rightarrow> bool" where
  "open_proj_space = openin (map_topology Proj euclidean)"

lemma topspace_map_Proj: "topspace (map_topology Proj euclidean) = UNIV"
  using surj_Proj by auto

instance
  apply (rule class.Topological_Spaces.topological_space.of_class.intro)
  unfolding open_proj_space_def
  using surj_Proj
  by (rule topological_space_quotient)

end

lemma open_vimage_ProjI: "open T \<Longrightarrow> open (Proj -` T)"
  by (metis inf_top.right_neutral open_openin open_proj_space_def openin_map_topology topspace_euclidean)
lemma open_vimage_ProjD: "open (Proj -` T) \<Longrightarrow> open T"
  by (metis inf_top.right_neutral open_openin open_proj_space_def openin_map_topology top.extremum topspace_euclidean topspace_map_Proj topspace_map_topology)
lemma open_vimage_Proj_iff[simp]: "open (Proj -` T) = open T"
  by (auto simp: open_vimage_ProjI open_vimage_ProjD)

lemma euclidean_proj_space_def: "euclidean = map_topology Proj euclidean"
  apply (auto simp: topology_eq_iff openin_map_topology)
  subgoal for x by (induction x) auto
  subgoal for _ x by (induction x) auto
  done

lemma continuous_on_proj_spaceI: "continuous_on (S) f" if "continuous_on (Proj -` S) (f o Proj)" "open (S)"
  for f::"_ proj_space \<Rightarrow> _"
 by (metis (no_types, hide_lams) continuous_on_open_vimage open_vimage_Proj_iff that vimage_Int vimage_comp) 

lemma saturate_eq: "Proj -` Proj ` X = (\<Union>c\<in>UNIV-{0}. (*\<^sub>R) c ` X)"
  apply (auto simp: )
  subgoal for x y
  proof -
    assume "Proj x = Proj y" "y \<in> X"
    then have "proj_rel x y" using proj_space.abs_eq_iff by auto
    then show ?thesis using \<open>y \<in> X\<close>
      by (force elim!: proj_rel.cases intro!: bexI[where x="inverse c" for c])
  qed
  subgoal for c x
    using proj_rel.intros[of c x]
    by (metis imageI proj_space.abs_eq_iff)
  done

lemma open_scaling_nonzero: "c \<noteq> 0 \<Longrightarrow> open s \<Longrightarrow> open ((*\<^sub>R) c ` s::'a::euclidean_space nonzero set)"
  by transfer auto

subsection \<open>Proof of Hausdorff property\<close>

lemma Proj_open_map: "open (Proj ` X)" if "open X"
proof -
  note saturate_eq[of X]
  also have "open ((\<Union>c\<in>UNIV - {0}. (*\<^sub>R) c ` X))"
    apply (rule open_Union)
    apply (rule)
    apply (erule imageE)
    apply simp
    apply (rule open_scaling_nonzero)
     apply (simp)
    apply (rule that)
    done
  finally show ?thesis by simp
qed

lemma proj_rel_transfer[transfer_rule]:
  "(pcr_nonzero A ===> pcr_nonzero A ===> (=))  (\<lambda>x a. \<exists>c. a = sr c x \<and> c \<noteq> 0) proj_rel"
  if [transfer_rule]: "((=) ===> pcr_nonzero A ===> pcr_nonzero A) sr (*\<^sub>R)"
    "bi_unique A"
  unfolding proj_rel.simps
  by (transfer_prover)

lemma bool_aux: "a \<and> (a \<longrightarrow> b) \<longleftrightarrow> a \<and> b" by auto

lemma closed_proj_rel: "closed {(x::'a::euclidean_space nonzero, y::'a nonzero). proj_rel x y}"
proof -
  have closed_proj_rel_euclidean:
    "\<exists>A B. 0 \<notin> A \<and> 0 \<notin> B \<and> open A \<and> open B \<and> a \<in> A \<and> b \<in> B \<and>
      A \<times> B \<subseteq> - {(x, y). (x, y) \<noteq> 0 \<and> (\<exists>c. c \<noteq> 0 \<and> y = c *\<^sub>R x)}"
    if "\<And>c. c \<noteq> 0 \<Longrightarrow> b \<noteq> c *\<^sub>R a" "a \<noteq> 0" "b \<noteq> 0"
    for a b::'a
  proof -\<comment> \<open>explicitly constructing open ``cones'' that are disjoint\<close>
    define a1 where "a1 = a /\<^sub>R norm a"
    define b1 where "b1 = b /\<^sub>R norm b"
    have norm_a1[simp]: "norm a1 = 1" and norm_b1[simp]: "norm b1 = 1"
      using that
      by (auto simp: a1_def b1_def divide_simps)
    have a_alt_def: "a = norm a *\<^sub>R a1" and b_alt_def: "b = norm b *\<^sub>R b1"
      using that
      by (auto simp: a1_def b1_def)
    have a1_neq_b1: "a1 \<noteq> b1" "a1 \<noteq> -b1"
      using that(1)[of "norm b / norm a"] that(2-)
       apply (auto simp: a1_def b1_def divide_simps)
       apply (metis divideR_right divide_inverse inverse_eq_divide norm_eq_zero scaleR_scaleR)
      by (metis (no_types, lifting) add.inverse_inverse b1_def b_alt_def inverse_eq_divide
            scaleR_scaleR scale_eq_0_iff scale_minus_left that(1))
    define e where "e = (1/2) * (min 1 (min (dist a1 b1) (dist (-a1) b1)))"
    have e_less: "2 * e \<le> dist a1 b1" "2 * e \<le> dist (-a1) b1" "e < 1"
      and e_pos: "0 < e"
      using that a1_neq_b1
      by (auto simp: e_def min_def)
    define A1 where "A1 = ball a1 e \<inter> {x. norm x = 1}"
    define B1 where "B1 = ball b1 e \<inter> {x. norm x = 1}"
    have disjoint: "A1 \<inter> B1 = {}" "uminus ` A1 \<inter> B1 = {}"
      using e_less
      apply (auto simp: A1_def B1_def mem_ball)
      apply (smt dist_commute dist_triangle)
      by (smt add_uminus_conv_diff diff_self dist_0_norm dist_add_cancel dist_commute dist_norm dist_triangle)
    have norm_1: "x \<in> A1 \<Longrightarrow> norm x = 1"
      "x \<in> B1 \<Longrightarrow> norm x = 1"
      for x
      by (auto simp: A1_def B1_def)
    define scales where "scales X = {c *\<^sub>R x |c x. c \<noteq> 0 \<and> x \<in> X}" for X::"'a set"
    have scales_mem: "c *\<^sub>R x \<in> (scales X) \<longleftrightarrow> x \<in> (scales X)" if "c \<noteq> 0" for c x X
      apply (auto simp: scales_def)
      apply (metis eq_vector_fraction_iff that)
      apply (metis divisors_zero that)
      done
    define A where "A = scales A1"
    define B where "B = scales B1"

    from disjoint have "A \<inter> B = {}"
      apply (auto simp: A_def B_def mem_ball scales_def, goal_cases)
      by (smt disjoint_iff_not_equal imageI mult_cancel_right norm_1(1) norm_1(2) norm_scaleR
          scaleR_left.minus scale_left_imp_eq scale_minus_right)
    have "0 \<notin> A" "0 \<notin> B" using e_less \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>
      by (auto simp: A_def B_def A1_def B1_def mem_ball a1_def b1_def scales_def)
    moreover
    let ?S = "top_of_set {x. norm x = 1}"
    have open_scales: "open (scales X)" if "openin ?S X" for X
    proof -
      have X1: "x \<in> X \<Longrightarrow> norm x = 1" for x using that by (auto simp: openin_subtopology)
      have "0 \<notin> X" using that by (auto simp: openin_subtopology)
      have "scales X = (\<lambda>x. x /\<^sub>R norm x) -` (X \<union> uminus ` X) \<inter> (topspace (top_of_set (UNIV - {0})))"
        apply (auto simp: scales_def)
        subgoal for c x using \<open>0 \<notin> X\<close>
          apply (cases "c > 0")
          by (auto simp: X1)
        subgoal by (metis X1 norm_zero zero_neq_one)
        subgoal for x
          apply (rule exI[where x="norm x"])
          apply (rule exI[where x="x /\<^sub>R norm x"])
          by auto
        subgoal for x y apply (rule exI[where x="- norm x"]) apply (rule exI[where x=y])
          apply auto
          by (metis divideR_right norm_eq_zero scale_minus_right)
        done
      also have "openin (top_of_set (UNIV - {0})) \<dots>"
      proof -
        have *: " {y. inverse (norm y) * norm y = 1} = UNIV - {0}"
          by auto
        from that have "openin ?S (uminus ` X)"
          apply (clarsimp simp: openin_subtopology)
          by (auto simp: open_negations intro!: exI[where x="uminus ` T" for T])
        then have "openin ?S (X \<union> uminus ` X)"
          using \<open>openin _ X\<close> by auto
        from _ this show ?thesis
          apply (rule continuous_map_open)
          apply (auto simp: continuous_map_def)
          apply (subst(asm) openin_subtopology)
          apply (auto simp: *)
          apply (subst openin_subtopology)
          apply clarsimp
          subgoal for T
            apply (rule exI[where x="(\<lambda>x. x /\<^sub>R norm x) -` T \<inter> UNIV - {0}"])
            apply (auto simp: Diff_eq)
            apply (rule open_continuous_vimage)
            by (auto intro!: continuous_intros)
          done
      qed
      finally show ?thesis
        apply (subst (asm) openin_subtopology)
        by clarsimp auto
    qed
    have "openin ?S A1" "openin ?S B1"
      by (auto simp: openin_subtopology A1_def B1_def)
    from open_scales[OF this(1)] open_scales[OF this(2)]
    have "open A" "open B" by (simp_all add: A_def B_def)
    moreover
    have "a \<in> A" "b \<in> B"
      by (force simp: A_def B_def A1_def B1_def that e_pos scales_def intro: a_alt_def b_alt_def)+
    moreover
    have False if "c *\<^sub>R p \<in> B" "p \<in> A" "c \<noteq> 0" for p c
      using that \<open>0 \<notin> A\<close> \<open>0 \<notin> B\<close> \<open>A \<inter> B = {}\<close>
      by (auto simp: A_def B_def scales_mem)
    then have "A \<times> B \<subseteq> - {(x, y). (x, y) \<noteq> 0 \<and> (\<exists>c. c \<noteq> 0 \<and> y = c *\<^sub>R x)}"
      by (auto simp: prod_eq_iff)
    ultimately show ?thesis by blast
  qed
  show ?thesis
    unfolding closed_def open_prod_def
    apply transfer
    apply (simp add: split_beta' bool_aux pred_prod.simps)
    apply (rule ballI)
    apply (clarsimp simp: pred_prod.simps[abs_def])
    subgoal for a b
      apply (subgoal_tac "(\<And>c. c \<noteq> 0 \<Longrightarrow> b \<noteq> c *\<^sub>R a)")
      using closed_proj_rel_euclidean[of b a]
       apply clarsimp
      subgoal for A B
        apply (rule exI[where x=A])
        apply (auto intro!: exI[where x=B])
        apply (auto simp: subset_iff prod_eq_iff)
        by blast
      subgoal by auto
      done
    done
qed

lemma closed_Proj_rel: "closed {(x, y). Proj x = Proj y}"
  using closed_proj_rel
  by (smt Collect_cong case_prodE case_prodI2 prod.inject proj_space.abs_eq_iff)

instance proj_space :: (euclidean_space) t2_space
  apply (rule class.Topological_Spaces.t2_space.of_class.intro)
  using open_proj_space_def surj_Proj Proj_open_map closed_Proj_rel
  by (rule t2_space_quotient)

instance proj_space :: (euclidean_space) second_countable_topology
  apply (rule class.Elementary_Topology.second_countable_topology.of_class.intro)
  using open_proj_space_def surj_Proj Proj_open_map
  by (rule second_countable_topology_quotient)


subsection \<open>Charts\<close>


subsubsection \<open>Chart for last coordinate\<close>

lift_definition chart_last_nonzero :: "('a::euclidean_space \<times> real) nonzero \<Rightarrow> 'a" is "\<lambda>(x,c). x /\<^sub>R c" .

lemma chart_last_nonzero_scaleR[simp]: "c \<noteq> 0 \<Longrightarrow> chart_last_nonzero (c *\<^sub>R n) = chart_last_nonzero n"
  by (transfer) auto

lift_definition chart_last :: "'a::euclidean_space proj_space \<Rightarrow> 'a" is chart_last_nonzero
  by (erule proj_rel.cases) auto

lift_definition chart_last_inv_nonzero :: "'a \<Rightarrow> ('a::euclidean_space\<times>real) nonzero" is
  "\<lambda>x. (x, 1)"
  by (auto simp: zero_prod_def)

lift_definition chart_last_inv :: "'a \<Rightarrow> 'a::euclidean_space proj_space" is chart_last_inv_nonzero .

lift_definition chart_last_domain_nonzeroP :: "('a::euclidean_space\<times>real) nonzero \<Rightarrow> bool" is
  "\<lambda>x. snd x \<noteq> 0" .

lift_definition chart_last_domainP :: "'a::euclidean_space proj_space \<Rightarrow> bool" is chart_last_domain_nonzeroP
  unfolding rel_set_def
  by (safe elim!: proj_rel.cases; (transfer,simp))

lemma open_chart_last_domain: "open (Collect chart_last_domainP)"
  unfolding open_proj_space_def
  unfolding openin_map_topology 
  apply auto subgoal for x apply (induction x) by auto
  subgoal
    apply transfer
    apply transfer
    unfolding Collect_conj_eq
    apply (rule open_Int)
    by (auto intro!: open_Collect_neq continuous_on_snd)
  done

lemma Proj_vimage_chart_last_domainP: "Proj -` Collect chart_last_domainP = Collect (chart_last_domain_nonzeroP)"
  apply safe
  subgoal by transfer'
  subgoal for x
    by auto transfer
  done

lemma chart_last_continuous:
  notes [transfer_rule] = open_nonzero_openin_transfer
  shows "continuous_on (Collect chart_last_domainP) chart_last"
  apply (rule continuous_on_proj_spaceI)
  unfolding o_def chart_last.abs_eq Proj_vimage_chart_last_domainP
  apply transfer
  subgoal by (auto intro!: continuous_intros simp: split_beta)
  subgoal by (rule open_chart_last_domain)
  done

lemma chart_last_inv_continuous:
  notes [transfer_rule] = open_nonzero_openin_transfer
  shows "continuous_on UNIV chart_last_inv"
  unfolding chart_last_inv_def map_fun_def comp_id
  apply (rule continuous_on_compose)
  subgoal by transfer (auto intro!: continuous_intros)
  subgoal
    by (metis continuous_on_open_vimage continuous_on_subset inf_top.right_neutral open_UNIV open_vimage_Proj_iff top_greatest)
  done

lemma proj_rel_iff: "proj_rel a b \<longleftrightarrow> (\<exists>c\<noteq>0. b = c *\<^sub>R a)"
  by (auto elim!: proj_rel.cases intro!: proj_rel.intros)

lemma chart_last_inverse: "chart_last_inv (chart_last x) = x" if "chart_last_domainP x"
  using that
  apply -
  apply transfer
  unfolding proj_rel_iff
  apply transfer
  apply (simp add: split_beta prod_eq_iff)
  subgoal for x
    by (rule exI[where x="snd x"]) auto
  done

lemma chart_last_inv_inverse: "chart_last (chart_last_inv x) = x"
  apply transfer
  apply transfer
  by auto

lemma chart_last_domainP_chart_last_inv: "chart_last_domainP (chart_last_inv x)"
  apply transfer apply transfer by auto

lemma homeomorphism_chart_last:
  "homeomorphism (Collect chart_last_domainP) UNIV chart_last chart_last_inv"
  apply (auto simp: homeomorphism_def chart_last_inverse chart_last_inv_inverse
      chart_last_continuous chart_last_inv_continuous)
  subgoal
    apply transfer apply transfer apply (auto simp: split_beta')
    subgoal for x by (rule image_eqI[where x="(x, 1)"]) (auto simp: prod_eq_iff)
    done
  subgoal
    apply transfer apply transfer by (auto simp: split_beta')
  subgoal for x
    by (rule image_eqI[where x="chart_last x"]) (auto simp: chart_last_inverse)
  done

lift_definition last_chart::"('a::euclidean_space proj_space, 'a) chart" is
  "(Collect chart_last_domainP, UNIV, chart_last, chart_last_inv)"
  using homeomorphism_chart_last open_chart_last_domain by auto


subsubsection \<open>Charts for first \<open>DIM('a)\<close> coordinates\<close>

lift_definition chart_basis_nonzero :: "'a \<Rightarrow> ('a::euclidean_space\<times>real)nonzero \<Rightarrow> 'a" is
  "\<lambda>b. \<lambda>(x,c). (x + (c - x \<bullet> b) *\<^sub>R b) /\<^sub>R (x \<bullet> b)" .

lift_definition chart_basis :: "'a \<Rightarrow> 'a::euclidean_space proj_space \<Rightarrow> 'a" is
  chart_basis_nonzero
  apply (erule proj_rel.cases)
  apply transfer
  by (auto simp add: divide_simps algebra_simps)

lift_definition chart_basis_domain_nonzeroP :: "'a \<Rightarrow> ('a::euclidean_space\<times>real) nonzero \<Rightarrow> bool" is
  "\<lambda>b (x, _). (x \<bullet> b) \<noteq> 0" .

lift_definition chart_basis_domainP :: "'a \<Rightarrow> 'a::euclidean_space proj_space \<Rightarrow> bool" is chart_basis_domain_nonzeroP
  unfolding rel_set_def
  apply (safe elim!: proj_rel.cases)
  subgoal by transfer auto
  subgoal by transfer auto
  done

lemma Proj_vimage_chart_basis_domainP:
  "Proj -` Collect (chart_basis_domainP b) = Collect (chart_basis_domain_nonzeroP b)"
  apply safe
  subgoal by transfer'
  subgoal for x
    by auto transfer
  done


lemma open_chart_basis_domain: "open (Collect (chart_basis_domainP b))"
  unfolding open_proj_space_def
  unfolding openin_map_topology 
  apply auto subgoal for x apply (induction x) by auto
  subgoal
    apply transfer
    apply transfer
    unfolding Collect_conj_eq
    apply (rule open_Int)
     apply (auto intro!: open_Collect_neq continuous_on_fst continuous_on_inner simp: split_beta)
    done
  done

lemma chart_basis_continuous:
  notes [transfer_rule] = open_nonzero_openin_transfer
  shows "continuous_on (Collect (chart_basis_domainP b)) (chart_basis b)"
  apply (rule continuous_on_proj_spaceI)
  unfolding o_def chart_basis.abs_eq Proj_vimage_chart_basis_domainP
   apply transfer
  subgoal by (auto intro!: continuous_intros simp: split_beta)
  subgoal by (rule open_chart_basis_domain)
  done


context
  fixes b::"'a::euclidean_space"
  assumes b: "b \<in> Basis"
begin

lemma b_neq0: "b \<noteq> 0" using b by auto

lift_definition chart_basis_inv_nonzero :: "'a \<Rightarrow> ('a::euclidean_space \<times> real) nonzero" is
  "\<lambda>x. (x + (1 - x \<bullet> b) *\<^sub>R b, x \<bullet> b)"
  apply (auto simp: zero_prod_def)
  using b_neq0 using eq_neg_iff_add_eq_0 by force

lift_definition chart_basis_inv :: "'a \<Rightarrow> 'a::euclidean_space proj_space" is
  chart_basis_inv_nonzero .

lemma chart_basis_inv_continuous:
  notes [transfer_rule] = open_nonzero_openin_transfer
  shows "continuous_on UNIV chart_basis_inv"
  unfolding chart_basis_inv_def map_fun_def comp_id
  apply (rule continuous_on_compose)
  subgoal by transfer (auto intro!: continuous_intros)
  subgoal
    unfolding continuous_map_iff_continuous euclidean_proj_space_def
    using continuous_on_open_invariant open_vimage_Proj_iff by blast
  done

lemma chart_basis_inv_inverse: "chart_basis b (chart_basis_inv x) = x"
  apply transfer
  apply transfer
  using b_neq0 b
  by (auto simp: algebra_simps divide_simps)

lemma chart_basis_inverse: "chart_basis_inv (chart_basis b x) = x" if "chart_basis_domainP b x"
  using that
  apply transfer
  unfolding proj_rel_iff
  apply transfer
  apply (simp add: split_beta prod_eq_iff)
  subgoal for x
    apply (rule exI[where x="fst x \<bullet> b"])
    using b
    by (simp add: algebra_simps)
  done

lemma chart_basis_domainP_chart_basis_inv: "chart_basis_domainP b (chart_basis_inv x)"
  apply transfer apply transfer by (use b in \<open>auto simp: algebra_simps\<close>)

lemma homeomorphism_chart_basis:
  "homeomorphism (Collect (chart_basis_domainP b)) UNIV (chart_basis b) chart_basis_inv"
  apply (auto simp: homeomorphism_def chart_basis_inverse chart_basis_inv_inverse
      chart_basis_continuous chart_basis_inv_continuous)
  subgoal
    apply transfer apply transfer apply (auto simp: split_beta')
    subgoal for x
      apply (rule image_eqI[where x="(x + (1 - (x \<bullet> b)) *\<^sub>R b, x \<bullet> b)"])
      using b
      apply (auto simp add: algebra_simps divide_simps prod_eq_iff)
      by (metis add.right_neutral b_neq0 inner_commute inner_eq_zero_iff inner_right_distrib inner_zero_right)
    done
  subgoal
    apply transfer apply transfer using b by (auto simp: split_beta' algebra_simps)
  subgoal for x
    by (rule image_eqI[where x="chart_basis b x"]) (auto simp: chart_basis_inverse)
  done

lift_definition basis_chart::"('a proj_space, 'a) chart"
  is "(Collect (chart_basis_domainP b), UNIV, chart_basis b, chart_basis_inv)"
  using homeomorphism_chart_basis by (auto simp: open_chart_basis_domain)

end

subsubsection \<open>Atlas\<close>

definition "charts_proj_space = insert last_chart (basis_chart ` Basis)"

lemma chart_last_basis_defined:
  "chart_last_domainP xa \<Longrightarrow> chart_basis_domainP b xa \<Longrightarrow> chart_last xa \<bullet> b \<noteq> 0"
  apply transfer apply transfer by (auto simp: prod_eq_iff)

lemma chart_basis_last_defined:
  "b \<in> Basis \<Longrightarrow> chart_last_domainP xa \<Longrightarrow> chart_basis_domainP b xa \<Longrightarrow> chart_basis b xa \<bullet> b \<noteq> 0"
  apply transfer apply transfer
  by (auto simp: prod_eq_iff algebra_simps)

lemma compat_last_chart: "\<infinity>-smooth_compat last_chart (basis_chart b)"
  if [transfer_rule]: "b \<in> Basis"
  unfolding smooth_compat_def
proof (transfer; auto)
  have "smooth_on {x. x \<bullet> b \<noteq> 0} (chart_basis b \<circ> chart_last_inv)"
    apply transfer
    apply transfer
    by (auto simp: o_def intro!: smooth_on_inverse smooth_on_scaleR smooth_on_inner smooth_on_add
        smooth_on_minus open_Collect_neq continuous_intros)
  then show "smooth_on (chart_last ` (Collect chart_last_domainP \<inter> Collect (chart_basis_domainP b))) (chart_basis b \<circ> chart_last_inv)"
    by (rule smooth_on_subset) (auto simp: chart_last_basis_defined)
next
  have "smooth_on {x. x \<bullet> b \<noteq> 0}  (chart_last \<circ> chart_basis_inv b)"
    apply transfer
    apply transfer
    by (auto simp: o_def intro!: smooth_on_add smooth_on_scaleR smooth_on_minus smooth_on_inverse 
        smooth_on_inner open_Collect_neq continuous_intros)
  then show "smooth_on (chart_basis b ` (Collect chart_last_domainP \<inter> Collect (chart_basis_domainP b))) (chart_last \<circ> chart_basis_inv b)"
    by (rule smooth_on_subset) (auto simp: chart_basis_last_defined that)
qed

lemma smooth_on_basis_comp_inv: "smooth_on {x. (x + (1 - x \<bullet> a) *\<^sub>R a) \<bullet> b \<noteq> 0} (chart_basis b \<circ> chart_basis_inv a)"
  if [transfer_rule]: "a \<in> Basis" "b \<in> Basis"
  apply transfer
  apply transfer
  by (auto intro!: smooth_on_add smooth_on_scaleR smooth_on_minus smooth_on_inner smooth_on_inverse
    smooth_on_mult open_Collect_neq continuous_intros simp: o_def algebra_simps inner_Basis)

lemma chart_basis_basis_defined:
  "a \<noteq> b \<Longrightarrow> chart_basis_domainP a xa \<Longrightarrow> chart_basis_domainP b xa \<Longrightarrow> chart_basis a xa \<bullet> b \<noteq> 0"
  if "a \<in> Basis" "b \<in> Basis"
  using that
  apply transfer
  apply transfer
  by (auto simp: algebra_simps inner_Basis prod_eq_iff)

lemma compat_basis_chart: "\<infinity>-smooth_compat (basis_chart a) (basis_chart b)"
  if [transfer_rule]: "a \<in> Basis" "b \<in> Basis"
  apply (cases "a = b")
  subgoal by (auto simp: smooth_compat_refl)
  subgoal
    unfolding smooth_compat_def
    apply (transfer; auto)
    subgoal
      using smooth_on_basis_comp_inv[OF that]
      apply (rule smooth_on_subset)
      by (auto simp: algebra_simps inner_Basis chart_basis_basis_defined that)
    subgoal
      using smooth_on_basis_comp_inv[OF that(2,1)]
      apply (rule smooth_on_subset)
      by (auto simp: algebra_simps inner_Basis chart_basis_basis_defined that)
    done
  done

lemma c_manifold_proj_space: "c_manifold charts_proj_space \<infinity>"
  by standard
    (auto simp: charts_proj_space_def smooth_compat_refl smooth_compat_commute compat_last_chart
      compat_basis_chart)


end
