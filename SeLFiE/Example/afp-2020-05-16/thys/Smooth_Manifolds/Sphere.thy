section \<open>Sphere\<close>
theory Sphere
  imports Differentiable_Manifold
begin

typedef (overloaded) ('a::real_normed_vector) sphere =
  "{a::'a\<times>real. norm a = 1}"
proof -
  have "norm (0::'a,1::real) = 1" by simp
  then show ?thesis by blast
qed

setup_lifting type_definition_sphere

(* First stereographic projection: between S^n - (0,1) and R^n. *)
lift_definition top_sphere :: "('a::real_normed_vector) sphere" is "(0, 1)" by simp

lift_definition st_proj1 :: "('a::real_normed_vector) sphere \<Rightarrow> 'a" is
  "\<lambda>(x,z). x /\<^sub>R (1 - z)" .

lift_definition st_proj1_inv :: "('a::real_normed_vector) \<Rightarrow> 'a sphere" is
  "\<lambda>x. ((2 / ((norm x) ^ 2 + 1)) *\<^sub>R x, ((norm x) ^ 2 - 1) / ((norm x) ^ 2 + 1))"
  apply (auto simp: norm_prod_def divide_simps algebra_simps)
   apply (auto simp: add_nonneg_eq_0_iff)
  by (auto simp: power2_eq_square algebra_simps)

(* Second stereographic projection: between S^n - (0,-1) and R^n. *)
lift_definition bot_sphere :: "('a::real_normed_vector) sphere" is "(0, -1)" by simp

lift_definition st_proj2 :: "('a::real_normed_vector) sphere \<Rightarrow> 'a" is
  "\<lambda>(x,z). x /\<^sub>R (1 + z)" .

lift_definition st_proj2_inv :: "('a::real_normed_vector) \<Rightarrow> 'a sphere" is
  "\<lambda>x. ((2 / ((norm x) ^ 2 + 1)) *\<^sub>R x, (1 - (norm x) ^ 2) / ((norm x) ^ 2 + 1))"
  apply (auto simp: norm_prod_def divide_simps algebra_simps)
   apply (auto simp: add_nonneg_eq_0_iff)
  by (auto simp: power2_eq_square algebra_simps)

instantiation sphere :: (real_normed_vector) topological_space
begin

lift_definition open_sphere :: "'a sphere set \<Rightarrow> bool" is
  "openin (subtopology (euclidean::('a\<times>real) topology) {a. norm a = 1})" .

instance
  apply standard
  apply (transfer; auto)
  apply (transfer; auto)
  apply (transfer; auto)
  done

end

instance sphere :: (real_normed_vector) t2_space
  apply standard
  apply transfer
  subgoal for x y
    apply (drule hausdorff[of x y])
    apply clarsimp
    subgoal for U V
      apply (rule exI[where x="U \<inter> {a. norm a = 1}"])
      apply clarsimp
      apply (rule conjI) defer
       apply (rule exI[where x="V \<inter> {a. norm a = 1}"])
      by auto
    done
  done

instance sphere :: (euclidean_space) second_countable_topology
proof standard
  obtain BB::"('a\<times>real) set set" where BB: "countable BB" "open = generate_topology BB"
    by (metis ex_countable_subbasis)
  let ?B = "(\<lambda>B. B \<inter> {x. norm x = 1}) ` BB"
  show "\<exists>B::'a sphere set set. countable B \<and> open = generate_topology B"
    apply transfer
    apply (rule bexI[where x = ?B])
    apply (rule conjI)
    subgoal using BB by force
    subgoal using BB apply clarsimp
      apply (subst openin_subtopology_eq_generate_topology[where BB=BB])
      by (auto )
    subgoal by auto
    done
qed

lemma transfer_continuous_on1[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (=) ===> ((=) ===> pcr_sphere (=)) ===> (=)) (\<lambda>X::'a::t2_space set. continuous_on X) continuous_on"
  apply (rule continuous_on_transfer_right_total2)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done

lemma transfer_continuous_on2[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (pcr_sphere (=)) ===> (pcr_sphere (=) ===> (=)) ===> (=)) (\<lambda>X. continuous_on (X \<inter> {x. norm x = 1})) (\<lambda>X. continuous_on X)"
  apply (rule continuous_on_transfer_right_total)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done

lemma st_proj1_inv_continuous:
  "continuous_on UNIV st_proj1_inv"
  by transfer (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff)

lemma st_proj1_continuous:
  "continuous_on (UNIV - {top_sphere}) st_proj1"
  by transfer (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff split_beta' norm_prod_def)

lemma st_proj1_inv: "st_proj1_inv (st_proj1 x) = x"
  if "x \<noteq> top_sphere"
  using that
  apply transfer
proof (clarsimp, rule conjI)
  fix a::'a and b::real
  assume *: "norm (a, b) = 1" and ab: "a = 0 \<longrightarrow> b \<noteq> 1"
  then have "b \<noteq> 1" by (auto simp: norm_prod_def)
  have na: "(norm a)\<^sup>2 = 1 - b\<^sup>2"
    using *
    unfolding norm_prod_def
    by (auto simp: algebra_simps)
  define S where "S = norm (a /\<^sub>R (1 - b))"
  have "b = (S\<^sup>2 - 1) / (S\<^sup>2 + 1)"
    by (auto simp: S_def divide_simps \<open>b \<noteq> 1\<close> na)
       (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> 1\<close>)
  then show "((inverse \<bar>1 - b\<bar> * norm a)\<^sup>2 - 1) / ((inverse \<bar>1 - b\<bar> * norm a)\<^sup>2 + 1) = b"
    by (simp add: S_def)

  have "1 = (2 / (1 - b) / (S\<^sup>2 + 1))"
    by (auto simp: S_def divide_simps \<open>b \<noteq> 1\<close> na) (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> 1\<close>)
  then have "a = (2 / (1 - b) / (S\<^sup>2 + 1)) *\<^sub>R a"
    by simp 
  then show "(2 * inverse (1 - b) / ((inverse \<bar>1 - b\<bar> * norm a)\<^sup>2 + 1)) *\<^sub>R a = a"
    by (auto simp: S_def divide_simps)
qed

lemma st_proj1_inv_inv: "st_proj1 (st_proj1_inv x) = x"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma st_proj1_inv_ne_top: "st_proj1_inv xa \<noteq> top_sphere"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma homeomorphism_st_proj1: "homeomorphism (UNIV - {top_sphere}) UNIV st_proj1 st_proj1_inv"
  apply (auto simp: homeomorphism_def st_proj1_continuous st_proj1_inv_continuous st_proj1_inv_inv
      st_proj1_inv st_proj1_inv_ne_top)
  subgoal for x
    by (rule image_eqI[where x="st_proj1_inv x"]) (auto simp: st_proj1_inv_inv st_proj1_inv_ne_top)
  by (metis rangeI st_proj1_inv)

lemma st_proj2_inv_continuous:
  "continuous_on UNIV st_proj2_inv"
  by transfer (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff)

lemma st_proj2_continuous:
  "continuous_on (UNIV - {bot_sphere}) st_proj2"
  apply (transfer; auto intro!: continuous_intros simp: add_nonneg_eq_0_iff split_beta' norm_prod_def)
proof -
  fix a b assume 1: "(norm a)^2 + b^2 = 1" and 2: "1 + b = 0"
  have "b = -1" using 2 by auto
  then show "a = 0"
    using 1 by auto
qed

lemma st_proj2_inv: "st_proj2_inv (st_proj2 x) = x"
  if "x \<noteq> bot_sphere"
  using that
  apply transfer
proof (clarsimp, rule conjI)
  fix a::'a and b::real
  assume *: "norm (a, b) = 1" and ab: "a = 0 \<longrightarrow> b \<noteq> -1"
  then have "b \<noteq> -1" by (auto simp: norm_prod_def)
  then have "1 + b \<noteq> 0" by auto
  then have "2 + b * 2 \<noteq> 0" by auto
  have na: "(norm a)\<^sup>2 = 1 - b\<^sup>2"
    using *
    unfolding norm_prod_def
    by (auto simp: algebra_simps)
  define S where "S = norm (a /\<^sub>R (1 + b))"
  have "b = (1 - S\<^sup>2) / (S\<^sup>2 + 1)"
    by (auto simp: S_def divide_simps \<open>b \<noteq> -1\<close> na)
       (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> -1\<close> \<open>1 + b \<noteq> 0\<close> \<open>2 + b * 2 \<noteq> 0\<close>)
  then show "(1 - (inverse \<bar>1 + b\<bar> * norm a)\<^sup>2) / ((inverse \<bar>1 + b\<bar> * norm a)\<^sup>2 + 1) = b"
    by (simp add: S_def)
  have "1 = (2 / (1 + b) / (S\<^sup>2 + 1))"
    by (auto simp: S_def divide_simps \<open>b \<noteq> -1\<close> na)
       (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> -1\<close> \<open>1 + b \<noteq> 0\<close> \<open>2 + b * 2 \<noteq> 0\<close>)
  then have "a = (2 / (1 + b) / (S\<^sup>2 + 1)) *\<^sub>R a"
    by simp 
  then show "(2 * inverse (1 + b) / ((inverse \<bar>1 + b\<bar> * norm a)\<^sup>2 + 1)) *\<^sub>R a = a"
    by (auto simp: S_def divide_simps)
qed

lemma st_proj2_inv_inv: "st_proj2 (st_proj2_inv x) = x"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma st_proj2_inv_ne_top: "st_proj2_inv xa \<noteq> bot_sphere"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma homeomorphism_st_proj2: "homeomorphism (UNIV - {bot_sphere}) UNIV st_proj2 st_proj2_inv"
  apply (auto simp: homeomorphism_def st_proj2_continuous st_proj2_inv_continuous st_proj2_inv_inv
      st_proj2_inv st_proj2_inv_ne_top)
  subgoal for x
    by (rule image_eqI[where x="st_proj2_inv x"]) (auto simp: st_proj2_inv_inv st_proj2_inv_ne_top)
  by (metis rangeI st_proj2_inv)

lift_definition st_proj1_chart :: "('a sphere, 'a::euclidean_space) chart"
  is "(UNIV - {top_sphere::'a sphere}, UNIV::'a set, st_proj1, st_proj1_inv)"
  using homeomorphism_st_proj1 by blast
  
lift_definition st_proj2_chart :: "('a sphere, 'a::euclidean_space) chart"
  is "(UNIV - {bot_sphere::'a sphere}, UNIV::'a set, st_proj2, st_proj2_inv)"
  using homeomorphism_st_proj2 by blast

lemma st_projs_compat:
  includes lifting_syntax
  shows "\<infinity>-smooth_compat st_proj1_chart st_proj2_chart"
  unfolding smooth_compat_def
  apply (transfer; auto)
proof goal_cases
  case 1
  have *: "smooth_on ((\<lambda>(x::'a, z). x /\<^sub>R (1 - z)) ` (({a. norm a = 1} - {(0, 1)}) \<inter> ({a. norm a = 1} - {(0, - 1)})))
     ((\<lambda>(x, z). x /\<^sub>R (1 + z)) \<circ> (\<lambda>x. ((2 / ((norm x)\<^sup>2 + 1)) *\<^sub>R x, ((norm x)\<^sup>2 - 1) / ((norm x)\<^sup>2 + 1))))"
    apply (rule smooth_on_subset[where T="UNIV - {0}"])
    subgoal
      by (auto intro!: smooth_on_divide smooth_on_inverse smooth_on_scaleR smooth_on_mult smooth_on_add
          smooth_on_minus smooth_on_norm simp: o_def power2_eq_square add_nonneg_eq_0_iff divide_simps)
    apply (auto simp: norm_prod_def power2_eq_square) apply sos
    done
  show ?case
    by transfer (rule *)
next
  case 2
  have *: "smooth_on ((\<lambda>(x::'a, z). x /\<^sub>R (1 + z)) ` (({a. norm a = 1} - {(0, 1)}) \<inter> ({a. norm a = 1} - {(0, - 1)})))
     ((\<lambda>(x, z). x /\<^sub>R (1 - z)) \<circ> (\<lambda>x. ((2 / ((norm x)\<^sup>2 + 1)) *\<^sub>R x, (1 - (norm x)\<^sup>2) / ((norm x)\<^sup>2 + 1))))"
    apply (rule smooth_on_subset[where T="UNIV - {0}"])
    subgoal
      by (auto intro!: smooth_on_divide smooth_on_inverse smooth_on_scaleR smooth_on_mult smooth_on_add
          smooth_on_minus smooth_on_norm simp: o_def power2_eq_square add_nonneg_eq_0_iff divide_simps)
    apply (auto simp: norm_prod_def add_eq_0_iff) apply sos
    done
  show ?case
    by transfer (rule *)
qed

definition charts_sphere :: "('a::euclidean_space sphere, 'a) chart set" where
  "charts_sphere \<equiv> {st_proj1_chart, st_proj2_chart}"

lemma c_manifold_atlas_sphere: "c_manifold charts_sphere \<infinity>"
  apply (unfold_locales)
  unfolding charts_sphere_def
  using smooth_compat_commute smooth_compat_refl st_projs_compat by fastforce

end
