section \<open>Auxiliary Lemmas\<close>
theory ODE_Auxiliarities
imports
  "HOL-Analysis.Analysis"
  "HOL-Library.Float"
  "List-Index.List_Index"
  Affine_Arithmetic.Affine_Arithmetic_Auxiliarities
  Affine_Arithmetic.Executable_Euclidean_Space
begin

instantiation prod :: (zero_neq_one, zero_neq_one) zero_neq_one
begin

definition "1 = (1, 1)"

instance by standard (simp add: zero_prod_def one_prod_def)
end

subsection \<open>there is no inner product for type @{typ "'a \<Rightarrow>\<^sub>L 'b"}\<close>

lemma (in real_inner) parallelogram_law: "(norm (x + y))\<^sup>2 + (norm (x - y))\<^sup>2 = 2 * (norm x)\<^sup>2 + 2 * (norm y)\<^sup>2"
proof -
  have "(norm (x + y))\<^sup>2 + (norm (x - y))\<^sup>2 = inner (x + y) (x + y) + inner (x - y) (x - y)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = 2 * (norm x)\<^sup>2 + 2 * (norm y)\<^sup>2"
    by (simp add: algebra_simps norm_eq_sqrt_inner)
  finally show ?thesis .
qed

locale no_real_inner
begin

lift_definition fstzero::"(real*real) \<Rightarrow>\<^sub>L (real*real)" is "\<lambda>(x, y). (x, 0)"
  by (auto intro!: bounded_linearI')

lemma [simp]: "fstzero (a, b) = (a, 0)"
  by transfer simp

lift_definition zerosnd::"(real*real) \<Rightarrow>\<^sub>L (real*real)" is "\<lambda>(x, y). (0, y)"
  by (auto intro!: bounded_linearI')

lemma [simp]: "zerosnd (a, b) = (0, b)"
  by transfer simp

lemma fstzero_add_zerosnd: "fstzero + zerosnd = id_blinfun"
  by transfer auto

lemma norm_fstzero_zerosnd: "norm fstzero = 1" "norm zerosnd = 1" "norm (fstzero - zerosnd) = 1"
  by (rule norm_blinfun_eqI[where x="(1, 0)"]) (auto simp: norm_Pair blinfun.bilinear_simps
    intro: norm_blinfun_eqI[where x="(0, 1)"] norm_blinfun_eqI[where x="(1, 0)"])

text \<open>compare with @{thm parallelogram_law}\<close>

lemma "(norm (fstzero + zerosnd))\<^sup>2 + (norm (fstzero - zerosnd))\<^sup>2 \<noteq>
    2 * (norm fstzero)\<^sup>2 + 2 * (norm zerosnd)\<^sup>2"
  by (simp add: fstzero_add_zerosnd norm_fstzero_zerosnd)

end

subsection \<open>Topology\<close>

subsection \<open>Vector Spaces\<close>

lemma ex_norm_eq_1: "\<exists>x. norm (x::'a::{real_normed_vector, perfect_space}) = 1"
  by (metis vector_choose_size zero_le_one)

subsection \<open>Reals\<close>

subsection \<open>Balls\<close>

text \<open>sometimes @{thm mem_ball} etc. are not good \<open>[simp]\<close> rules (although they are often useful):
  not sure that inequalities are ``simpler'' than set membership (distorts automatic reasoning
  when only sets are involved)\<close>
lemmas [simp del] = mem_ball mem_cball mem_sphere mem_ball_0 mem_cball_0


subsection \<open>Boundedness\<close>

lemma bounded_subset_cboxE:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> bounded ((\<lambda>x. x \<bullet> i) ` X)"
  obtains a b where "X \<subseteq> cbox a b"
proof -
  have "\<And>i. i \<in> Basis \<Longrightarrow> \<exists>a b. ((\<lambda>x. x \<bullet> i) ` X) \<subseteq> {a..b}"
    by (metis box_real(2) box_subset_cbox subset_trans bounded_subset_box_symmetric[OF assms] )
  then obtain a b where bnds: "\<And>i. i \<in> Basis \<Longrightarrow> ((\<lambda>x. x \<bullet> i) ` X) \<subseteq> {a i .. b i}" 
    by metis
  then have "X \<subseteq> {x. \<forall>i\<in>Basis. x \<bullet> i \<in> {a i .. b i}}"
    by force
  also have "\<dots> = cbox (\<Sum>i\<in>Basis. a i *\<^sub>R i) (\<Sum>i\<in>Basis. b i *\<^sub>R i)"
    by (auto simp: cbox_def)
  finally show ?thesis ..
qed

lemma
  bounded_euclideanI:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> bounded ((\<lambda>x. x \<bullet> i) ` X)"
  shows "bounded X"
proof -
  from bounded_subset_cboxE[OF assms] obtain a b where "X \<subseteq> cbox a b" .
  with bounded_cbox show ?thesis by (rule bounded_subset)
qed

subsection \<open>Intervals\<close>

notation closed_segment ("(1{_--_})")
notation open_segment ("(1{_<--<_})")

lemma min_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> min 0 (h * k::real) \<le> h' * k"
  by (metis dual_order.antisym le_cases min_le_iff_disj mult_eq_0_iff mult_le_0_iff
      mult_right_mono_neg)

lemma max_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> h' * k \<le> max 0 (h * k::real)"
  by (metis dual_order.antisym le_cases le_max_iff_disj mult_eq_0_iff mult_right_mono
      zero_le_mult_iff)

lemmas closed_segment_eq_real_ivl = closed_segment_eq_real_ivl

lemma bdd_above_is_intervalI: "bdd_above I" if "is_interval I" "a \<le> b" "a \<in> I" "b \<notin> I" for I::"real set"
  by (meson bdd_above_def is_interval_1 le_cases that)

lemma bdd_below_is_intervalI: "bdd_below I" if "is_interval I" "a \<le> b" "a \<notin> I" "b \<in> I" for I::"real set"
  by (meson bdd_below_def is_interval_1 le_cases that)


subsection \<open>Extended Real Intervals\<close>

subsection \<open>Euclidean Components\<close>

subsection \<open>Operator Norm\<close>

subsection \<open>Limits\<close>

lemma eventually_open_cball:
  assumes "open X"
  assumes "x \<in> X"
  shows "eventually (\<lambda>e. cball x e \<subseteq> X) (at_right 0)"
proof -
  from open_contains_cball_eq[OF assms(1)] assms(2)
  obtain e where "e > 0" "cball x e \<subseteq> X" by auto
  thus ?thesis
    by (auto simp: eventually_at dist_real_def mem_cball intro!: exI[where x=e])
qed

subsection \<open>Continuity\<close>

subsection \<open>Derivatives\<close>

lemma
  if_eventually_has_derivative:
  assumes "(f has_derivative F') (at x within S)"
  assumes "\<forall>\<^sub>F x in at x within S. P x" "P x" "x \<in> S"
  shows "((\<lambda>x. if P x then f x else g x) has_derivative F') (at x within S)"
  using assms(1)
  apply (rule has_derivative_transform_eventually)
  subgoal using assms(2) by eventually_elim auto
  by (auto simp: assms)


lemma norm_le_in_cubeI: "norm x \<le> norm y"
  if "\<And>i. i \<in> Basis \<Longrightarrow> abs (x \<bullet> i) \<le> abs (y \<bullet> i)" for x y
  unfolding norm_eq_sqrt_inner
  apply (subst euclidean_inner)
  apply (subst (3) euclidean_inner)
  using that
  by (auto intro!: sum_mono simp: abs_le_square_iff power2_eq_square[symmetric])

lemma has_derivative_partials_euclidean_convexI:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes f': "\<And>i x xi. i \<in> Basis \<Longrightarrow> (\<forall>j\<in>Basis. x \<bullet> j \<in> X j) \<Longrightarrow> xi = x \<bullet> i \<Longrightarrow>
    ((\<lambda>p. f (x + (p - x \<bullet> i) *\<^sub>R i)) has_vector_derivative f' i x) (at xi within X i)"
  assumes df_cont: "\<And>i. i \<in> Basis \<Longrightarrow> (f' i \<longlongrightarrow> (f' i x)) (at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j})"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> X i"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> convex (X i)"
  shows "(f has_derivative (\<lambda>h. \<Sum>j\<in>Basis. (h \<bullet> j) *\<^sub>R f' j x)) (at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j})"
    (is "_ (at x within ?S)")
proof (rule has_derivativeI)
  show "bounded_linear (\<lambda>h. \<Sum>j\<in>Basis. (h \<bullet> j) *\<^sub>R f' j x)"
    by (auto intro!: bounded_linear_intros)

  obtain E where [simp]: "set E = (Basis::'a set)" "distinct E"
    using finite_distinct_list[OF finite_Basis] by blast

  have [simp]: "length E = DIM('a)"
    using \<open>distinct E\<close> distinct_card by fastforce
  have [simp]: "E ! j \<in> Basis" if "j < DIM('a)" for j
    by (metis \<open>length E = DIM('a)\<close> \<open>set E = Basis\<close> nth_mem that)
  have "convex ?S"
    by (rule convex_prod) (use assms in auto)

  have sum_Basis_E: "sum g Basis = (\<Sum>j<DIM('a). g (E ! j))" for g
    apply (rule sum.reindex_cong[OF _ _ refl])
    apply (auto simp: inj_on_nth)
    by (metis \<open>distinct E\<close> \<open>length E = DIM('a)\<close> \<open>set E = Basis\<close> bij_betw_def bij_betw_nth)

  have segment: "\<forall>\<^sub>F x' in at x within ?S. x' \<in> ?S" "\<forall>\<^sub>F x' in at x within ?S. x' \<noteq> x"
    unfolding eventually_at_filter by auto


  show "((\<lambda>y. (f y - f x - (\<Sum>j\<in>Basis. ((y - x) \<bullet> j) *\<^sub>R f' j x)) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j})"
    apply (rule tendstoI)
    unfolding norm_conv_dist[symmetric]
  proof -
    fix e::real
    assume "e > 0"
    define B where "B = e / norm (2*DIM('a) + 1)"
    with \<open>e > 0\<close> have B_thms: "B > 0" "2 * DIM('a) * B < e" "B \<ge> 0"
      by (auto simp: divide_simps algebra_simps B_def)
    define B' where "B' = B / 2"
    have "B' > 0" by (simp add: B'_def \<open>0 < B\<close>)
    have "\<forall>i \<in> Basis. \<forall>\<^sub>F xa in at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j}. dist (f' i xa) (f' i x) < B'"
      apply (rule ballI)
      subgoal premises prems using df_cont[OF prems, THEN tendstoD, OF \<open>0 < B'\<close>] .
      done
    from eventually_ball_finite[OF finite_Basis this]
    have "\<forall>\<^sub>F x' in at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j}. \<forall>j\<in>Basis. dist (f' j x') (f' j x) < B'" .
    then obtain d where "d > 0"
      and "\<And>x' j. x' \<in> {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j} \<Longrightarrow> x' \<noteq> x \<Longrightarrow> dist x' x < d \<Longrightarrow> j \<in> Basis \<Longrightarrow> dist (f' j x') (f' j x) < B'"
      using \<open>0 < B'\<close>
      by (auto simp: eventually_at)
    then have B': "x' \<in> {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j} \<Longrightarrow> dist x' x < d \<Longrightarrow> j \<in> Basis \<Longrightarrow> dist (f' j x') (f' j x) < B'" for x' j
      by (cases "x' = x", auto simp add: \<open>0 < B'\<close>)
    then have B: "norm (f' j x' - f' j y) < B" if
      "(\<And>j. j \<in> Basis \<Longrightarrow> x' \<bullet> j \<in> X j)"
      "(\<And>j. j \<in> Basis \<Longrightarrow> y \<bullet> j \<in> X j)"
      "dist x' x < d"
      "dist y x < d"
      "j \<in> Basis"
      for x' y j
    proof -
      have "dist (f' j x') (f' j x) < B'" "dist (f' j y) (f' j x) < B'"
        using that
        by (auto intro!: B')
      then have "dist (f' j x') (f' j y) < B' + B'" by norm
      also have "\<dots> = B" by (simp add: B'_def)
      finally show ?thesis by (simp add: dist_norm)
    qed
    have "\<forall>\<^sub>F x' in at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j}. dist x' x < d"
      by (rule tendstoD[OF tendsto_ident_at \<open>d > 0\<close>])
    with segment
    show "\<forall>\<^sub>F x' in at x within {x. \<forall>j\<in>Basis. x \<bullet> j \<in> X j}.
      norm ((f x' - f x - (\<Sum>j\<in>Basis. ((x' - x) \<bullet> j) *\<^sub>R f' j x)) /\<^sub>R norm (x' - x)) < e"
    proof eventually_elim
      case (elim x')
      then have os_subset: "open_segment x x' \<subseteq> ?S"
        using \<open>convex ?S\<close> assms(3)
        unfolding convex_contains_open_segment
        by auto
      then have cs_subset: "closed_segment x x' \<subseteq> ?S"
        using elim assms(3) by (auto simp add: open_segment_def)
      have csc_subset: "closed_segment (x' \<bullet> i) (x \<bullet> i) \<subseteq> X i" if i: "i \<in> Basis" for i
        apply (rule closed_segment_subset)
        using cs_subset elim assms(3,4) that
        by (auto )
      have osc_subset: "open_segment (x' \<bullet> i) (x \<bullet> i) \<subseteq> X i" if i: "i \<in> Basis" for i
        using segment_open_subset_closed csc_subset[OF i]
        by (rule order_trans)

      define h where "h = x' - x"
      define z where "z j = (\<Sum>k<j. (h \<bullet> E ! k) *\<^sub>R (E ! k))" for j
      define g where "g j t = (f (x + z j + (t - x \<bullet> E ! j) *\<^sub>R E ! j))" for j t
      have z: "z j \<bullet> E ! j = 0" if "j < DIM('a)" for j
        using that
        by (auto simp: z_def h_def algebra_simps inner_sum_left inner_Basis if_distrib
            nth_eq_iff_index_eq
            sum.delta
            intro!: euclidean_eqI[where 'a='a]
            cong: if_cong)
      from distinct_Ex1[OF \<open>distinct E\<close>, unfolded \<open>set E = Basis\<close> Ex1_def \<open>length E = _\<close>]
      obtain index where
        index: "\<And>i. i \<in> Basis \<Longrightarrow> i = E ! index i" "\<And>i. i \<in> Basis \<Longrightarrow> index i < DIM('a)"
        and unique: "\<And>i j. i \<in> Basis \<Longrightarrow> j < DIM('a) \<Longrightarrow> E ! j = i \<Longrightarrow> j = index i"
        by metis
      have nth_eq_iff_index: "E ! k = i \<longleftrightarrow> index i = k" if "i \<in> Basis" "k < DIM('a)" for k i
        using unique[OF that] index[OF \<open>i \<in> Basis\<close>]
        by auto
      have z_inner: "z j \<bullet> i = (if j \<le> index i then 0 else h \<bullet> i)" if "j < DIM('a)" "i \<in> Basis" for j i
        using that index[of i]
        by (auto simp: z_def h_def algebra_simps inner_sum_left inner_Basis if_distrib
            sum.delta nth_eq_iff_index
            intro!: euclidean_eqI[where 'a='a]
            cong: if_cong)
      have z_mem: "j < DIM('a) \<Longrightarrow> ja \<in> Basis \<Longrightarrow> x \<bullet> ja + z j \<bullet> ja \<in> X ja" for j ja
        using csc_subset
        by (auto simp: z_inner h_def algebra_simps)
      have "norm (x' - x) < d"
        using elim by (simp add: dist_norm)
      have norm_z': "y \<in> closed_segment (x \<bullet> E ! j) (x' \<bullet> E ! j) \<Longrightarrow> norm (z j + y *\<^sub>R E ! j - (x \<bullet> E ! j) *\<^sub>R E ! j) < d"
        if "j < DIM('a)"
        for j y
        apply (rule le_less_trans[OF _ \<open>norm (x' - x) < d\<close>])
        apply (rule norm_le_in_cubeI)
        apply (auto simp: inner_diff_left inner_add_left inner_Basis that z)
        subgoal by (auto simp: closed_segment_eq_real_ivl split: if_splits)
        subgoal for i
          using that
          by (auto simp: z_inner h_def algebra_simps)
        done
      have norm_z: "norm (z j) < d" if "j < DIM('a)" for j
        using norm_z'[OF that ends_in_segment(1)]
        by (auto simp: z_def)
      {
        fix j
        assume j: "j < DIM('a)"
        have eq: "(x + z j + ((y - (x + z j)) \<bullet> E ! j) *\<^sub>R E ! j +
          (p - (x + z j + ((y - (x + z j)) \<bullet> E ! j) *\<^sub>R E ! j) \<bullet> E ! j) *\<^sub>R
          E ! j) = (x + z j + (p - (x \<bullet> E ! j)) *\<^sub>R E ! j)" for y p
          by (auto simp: algebra_simps j z)
        have f_has_derivative: "((\<lambda>p. f (x + z j + (p - x \<bullet> E ! j) *\<^sub>R E ! j)) has_derivative (\<lambda>xa. xa *\<^sub>R f' (E ! j) (x + z j + ((y *\<^sub>R E ! j - (x + z j)) \<bullet> E ! j) *\<^sub>R E ! j)))
            (at y within closed_segment (x \<bullet> E ! j) (x' \<bullet> E ! j))"
          if "y \<in> closed_segment (x \<bullet> E ! j) (x' \<bullet> E ! j)"
          for y
          apply (rule has_derivative_within_subset)
           apply (rule f'[unfolded has_vector_derivative_def,
                where x= "x + z j + ((y *\<^sub>R E!j - (x + z j))\<bullet> E!j) *\<^sub>R E ! j" and i="E ! j", unfolded eq])
          subgoal by (simp add: j)
          subgoal
            using that
            apply (auto simp: algebra_simps z j inner_Basis)
            using closed_segment_commute \<open>E ! j \<in> Basis\<close> csc_subset apply blast
            by (simp add: z_mem j)
          subgoal by (auto simp: algebra_simps z j inner_Basis)
          subgoal
            apply (auto simp: algebra_simps z j inner_Basis)
            using closed_segment_commute \<open>\<And>j. j < DIM('a) \<Longrightarrow> E ! j \<in> Basis\<close> csc_subset j apply blast
            done
          done
        have *: "((xa *\<^sub>R E ! j - (x + z j)) \<bullet> E ! j) = xa - x \<bullet> E ! j" for xa
          by (auto simp: algebra_simps z j)
        have g': "(g j has_vector_derivative (f' (E ! j) (x + z j + (xa - x \<bullet> E ! j) *\<^sub>R E ! j)))
          (at xa within (closed_segment (x\<bullet>E!j) (x'\<bullet>E!j)))"
          (is "(_ has_vector_derivative ?g' j xa) _")
          if "xa \<in> closed_segment (x\<bullet>E!j) (x'\<bullet>E!j)" for xa
          using that
          by (auto simp: has_vector_derivative_def g_def[abs_def] *
              intro!: derivative_eq_intros f_has_derivative[THEN has_derivative_eq_rhs])
        define g' where "g' j = ?g' j" for j
        with g' have g': "(g j has_vector_derivative g' j t) (at t within closed_segment (x\<bullet>E!j) (x'\<bullet>E!j))"
          if "t \<in> closed_segment (x\<bullet>E!j) (x'\<bullet>E!j)"
          for t
          by (simp add: that)
        have cont_bound: "\<And>y. y\<in>closed_segment (x \<bullet> E ! j) (x' \<bullet> E ! j) \<Longrightarrow> norm (g' j y - g' j (x \<bullet> E ! j)) \<le> B"
          apply (auto simp add: g'_def j algebra_simps inner_Basis z dist_norm
              intro!: less_imp_le B z_mem norm_z norm_z')
          using closed_segment_commute \<open>\<And>j. j < DIM('a) \<Longrightarrow> E ! j \<in> Basis\<close> csc_subset j apply blast
          done
        from vector_differentiable_bound_linearization[OF g' order_refl cont_bound ends_in_segment(1)]
        have n: "norm (g j (x' \<bullet> E ! j) - g j (x \<bullet> E ! j) - (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R g' j (x \<bullet> E ! j)) \<le> norm (x' \<bullet> E ! j - x \<bullet> E ! j) * B"
          .
        have "z (Suc j) = z j + (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R E ! j"
          by (auto simp: z_def h_def algebra_simps)
        then have "f (x + z (Suc j)) = f (x + z j + (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R E ! j) "
          by (simp add: ac_simps)
        with n have "norm (f (x + z (Suc j)) - f (x + z j) - (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R f' (E ! j) (x + z j)) \<le> \<bar>x' \<bullet> E ! j - x \<bullet> E ! j\<bar> * B"
          by (simp add: g_def g'_def)
      } note B_le = this
      have B': "norm (f' (E ! j) (x + z j) - f' (E ! j) x) \<le> B" if "j < DIM('a)" for j
        using that assms(3)
        by (auto simp add: algebra_simps inner_Basis z dist_norm \<open>0 < d\<close>
            intro!: less_imp_le B z_mem norm_z)
      have "(\<Sum>j\<le>DIM('a) - 1. f (x + z j) - f (x + z (Suc j))) = f (x + z 0) - f (x + z (Suc (DIM('a) - 1)))"
        by (rule sum_telescope)
      moreover have "z DIM('a) = h"
        using index
        by (auto simp: z_def h_def algebra_simps inner_sum_left inner_Basis if_distrib
            nth_eq_iff_index 
            sum.delta 
            intro!: euclidean_eqI[where 'a='a]
            cong: if_cong)
      moreover have "z 0 = 0"
        by (auto simp: z_def)
      moreover have "{..DIM('a) - 1} = {..<DIM('a)}"
        using le_imp_less_Suc by fastforce
      ultimately have "f x - f (x + h) = (\<Sum>j<DIM('a). f (x + z j) - f (x + z (Suc j)))"
        by (auto simp: )
      then have "norm (f (x + h) - f x - (\<Sum>j\<in>Basis. ((x' - x) \<bullet> j) *\<^sub>R f' j x)) =
        norm(
          (\<Sum>j<DIM('a). f (x + z (Suc j)) - f (x + z j) - (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R f' (E ! j) (x + z j)) +
          (\<Sum>j<DIM('a). (x' \<bullet> E ! j - x \<bullet> E ! j) *\<^sub>R (f' (E ! j) (x + z j) - f' (E ! j) x)))"
        (is "_ = norm (sum ?a ?E + sum ?b ?E)")
        by (intro arg_cong[where f=norm]) (simp add: sum_negf sum_subtractf sum.distrib algebra_simps sum_Basis_E)
      also have "\<dots> \<le> norm (sum ?a ?E) + norm (sum ?b ?E)" by (norm)
      also have "norm (sum ?a ?E) \<le> sum (\<lambda>x. norm (?a x)) ?E"
        by (rule norm_sum)
      also have "\<dots> \<le> sum (\<lambda>j. norm \<bar>x' \<bullet> E ! j - x \<bullet> E ! j\<bar> * B) ?E"
        by (auto intro!: sum_mono B_le)
      also have "\<dots> \<le> sum (\<lambda>j. norm (x' - x) * B) ?E"
        apply (rule sum_mono)
        apply (auto intro!: mult_right_mono \<open>0 \<le> B\<close>)
        by (metis (full_types) \<open>\<And>j. j < DIM('a) \<Longrightarrow> E ! j \<in> Basis\<close> inner_diff_left norm_bound_Basis_le order_refl)
      also have "\<dots> = norm (x' - x) * DIM('a) * B"
        by simp
      also have "norm (sum ?b ?E) \<le> sum (\<lambda>x. norm (?b x)) ?E"
        by (rule norm_sum)
      also have "\<dots> \<le> sum (\<lambda>j. norm (x' - x) * B) ?E"
        apply (intro sum_mono)
        apply (auto intro!: mult_mono B')
         apply (metis (full_types) \<open>\<And>j. j < DIM('a) \<Longrightarrow> E ! j \<in> Basis\<close> inner_diff_left norm_bound_Basis_le order_refl)
        done
      also have "\<dots> = norm (x' - x) * DIM('a) * B"
        by simp
      finally have "norm (f (x + h) - f x - (\<Sum>j\<in>Basis. ((x' - x) \<bullet> j) *\<^sub>R f' j x)) \<le>
          norm (x' - x) * real DIM('a) * B + norm (x' - x) * real DIM('a) * B"
        by arith
      also have "\<dots> /\<^sub>R norm (x' - x) \<le> norm (2 * DIM('a) * B)"
        using \<open>B \<ge> 0\<close>
        by (simp add: divide_simps abs_mult)
      also have "\<dots> < e" using B_thms by simp
      finally show ?case by (auto simp: divide_simps abs_mult h_def)
    qed
  qed
qed

lemma
  frechet_derivative_equals_partial_derivative:
  fixes f::"'a::euclidean_space \<Rightarrow> 'a"
  assumes Df: "\<And>x. (f has_derivative Df x) (at x)"
  assumes f': "((\<lambda>p. f (x + (p - x \<bullet> i) *\<^sub>R i) \<bullet> b) has_real_derivative f' x i b) (at (x \<bullet> i))"
  shows "Df x i \<bullet> b = f' x i b"
proof -
  define Dfb where "Dfb x = Blinfun (Df x)" for x
  have Dfb_apply: "blinfun_apply (Dfb x) = Df x" for x
    unfolding Dfb_def
    apply (rule bounded_linear_Blinfun_apply)
    apply (rule has_derivative_bounded_linear)
    apply (rule assms)
    done
  have "Dfb x = blinfun_of_matrix (\<lambda>i b. Dfb x b \<bullet> i)" for x
    using blinfun_of_matrix_works[of "Dfb x"] by auto
  have Dfb: "\<And>x. (f has_derivative Dfb x) (at x)"
    by (auto simp: Dfb_apply Df)
  note [derivative_intros] = diff_chain_at[OF _ Dfb, unfolded o_def]
  have "((\<lambda>p. f (x + (p - x \<bullet> i) *\<^sub>R i) \<bullet> b) has_real_derivative Dfb x i \<bullet> b) (at (x \<bullet> i))"
    by (auto intro!: derivative_eq_intros ext simp: has_field_derivative_def blinfun.bilinear_simps)
  from DERIV_unique[OF f' this]
  show ?thesis by (simp add: Dfb_apply)
qed


subsection \<open>Integration\<close>

lemmas content_real[simp]
lemmas integrable_continuous[intro, simp]
  and integrable_continuous_real[intro, simp]


lemma integral_eucl_le:
  fixes f g::"'a::euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<And>x. x \<in> s \<Longrightarrow> f x \<le> g x"
  shows "integral s f \<le> integral s g"
  using assms
  by (auto intro!: integral_component_le simp: eucl_le[where 'a='b])

lemma
  integral_ivl_bound:
  fixes l u::"'a::ordered_euclidean_space"
  assumes "\<And>x h'. h' \<in> {t0 .. h} \<Longrightarrow> x \<in> {t0 .. h} \<Longrightarrow> (h' - t0) *\<^sub>R f x \<in> {l .. u}"
  assumes "t0 \<le> h"
  assumes f_int: "f integrable_on {t0 .. h}"
  shows "integral {t0 .. h} f \<in> {l .. u}"
proof -
  from assms(1)[of t0 t0] assms(2) have "0 \<in> {l .. u}" by auto
  have "integral {t0 .. h} f = integral {t0 .. h} (\<lambda>t. if t \<in> {t0, h} then 0 else f t)"
    by (rule integral_spike[where S="{t0, h}"]) auto
  also
  {
    fix x
    assume 1: "x \<in> {t0 <..< h}"
    with assms have "(h - t0) *\<^sub>R f x \<in> {l .. u}" by auto
    then have "(if x \<in> {t0, h} then 0 else f x) \<in> {l /\<^sub>R (h - t0) .. u /\<^sub>R (h - t0)}"
      using \<open>x \<in> _\<close>
      by (auto simp: inverse_eq_divide
        simp: eucl_le[where 'a='a] field_simps algebra_simps)
  }
  then have "\<dots> \<in> {integral {t0..h} (\<lambda>_. l /\<^sub>R (h - t0)) .. integral {t0..h} (\<lambda>_. u /\<^sub>R (h - t0))}"
    unfolding atLeastAtMost_iff
    apply (safe intro!: integral_eucl_le)
    using \<open>0 \<in> {l .. u}\<close>
    apply (auto intro!: assms
      intro: integrable_continuous_real  integrable_spike[where S="{t0, h}", OF f_int]
      simp: eucl_le[where 'a='a] divide_simps
      split: if_split_asm)
    done
  also have "\<dots> \<subseteq> {l .. u}"
    using assms \<open>0 \<in> {l .. u}\<close>
    by (auto simp: inverse_eq_divide)
  finally show ?thesis .
qed

lemma
  add_integral_ivl_bound:
  fixes l u::"'a::ordered_euclidean_space"
  assumes "\<And>x h'. h' \<in> {t0 .. h} \<Longrightarrow> x \<in> {t0 .. h} \<Longrightarrow> (h' - t0) *\<^sub>R f x \<in> {l - x0 .. u - x0}"
  assumes "t0 \<le> h"
  assumes f_int: "f integrable_on {t0 .. h}"
  shows "x0 + integral {t0 .. h} f \<in> {l .. u}"
  using integral_ivl_bound[OF assms]
  by (auto simp: algebra_simps)

subsection \<open>conditionally complete lattice\<close>


subsection \<open>Lists\<close>

lemma
  Ball_set_Cons[simp]: "(\<forall>a\<in>set_Cons x y. P a) \<longleftrightarrow> (\<forall>a\<in>x. \<forall>b\<in>y. P (a#b))"
  by (auto simp: set_Cons_def)

lemma set_cons_eq_empty[iff]: "set_Cons a b = {} \<longleftrightarrow> a = {} \<or> b = {}"
  by (auto simp: set_Cons_def)

lemma listset_eq_empty_iff[iff]: "listset XS = {} \<longleftrightarrow> {} \<in> set XS"
  by (induction XS) auto

lemma sing_in_sings[simp]: "[x] \<in> (\<lambda>x. [x]) ` xd \<longleftrightarrow> x \<in> xd"
  by auto

lemma those_eq_None_set_iff: "those xs = None \<longleftrightarrow> None \<in> set xs"
  by (induction xs) (auto split: option.split)

lemma those_eq_Some_lengthD: "those xs = Some ys \<Longrightarrow> length xs = length ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_eq_Some_map_Some_iff: "those xs = Some ys \<longleftrightarrow> (xs = map Some ys)" (is "?l \<longleftrightarrow> ?r")
proof safe
  assume ?l
  then have "length xs = length ys"
    by (rule those_eq_Some_lengthD)
  then show ?r using \<open>?l\<close>
    by (induction xs ys rule: list_induct2) (auto split: option.splits)
next
  assume ?r
  then have "length xs = length ys"
    by simp
  then show "those (map Some ys) = Some ys" using \<open>?r\<close>
    by (induction xs ys rule: list_induct2) (auto split: option.splits)
qed


subsection \<open>Set(sum)\<close>

subsection \<open>Max\<close>

subsection \<open>Uniform Limit\<close>

subsection \<open>Bounded Linear Functions\<close>

lift_definition comp3::\<comment> \<open>TODO: name?\<close>
  "('c::real_normed_vector \<Rightarrow>\<^sub>L 'd::real_normed_vector) \<Rightarrow> ('b::real_normed_vector \<Rightarrow>\<^sub>L 'c) \<Rightarrow>\<^sub>L 'b \<Rightarrow>\<^sub>L 'd" is
  "\<lambda>(cd::('c \<Rightarrow>\<^sub>L 'd)) (bc::'b \<Rightarrow>\<^sub>L 'c). (cd o\<^sub>L bc)"
  by (rule bounded_bilinear.bounded_linear_right[OF bounded_bilinear_blinfun_compose])

lemma blinfun_apply_comp3[simp]: "blinfun_apply (comp3 a) b = (a o\<^sub>L b)"
  by (simp add: comp3.rep_eq)

lemma bounded_linear_comp3[bounded_linear]: "bounded_linear comp3"
  by transfer (rule bounded_bilinear_blinfun_compose)

lift_definition comp12::\<comment> \<open>TODO: name?\<close>
  "('a::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector) \<Rightarrow> ('b::real_normed_vector \<Rightarrow>\<^sub>L 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow>\<^sub>L 'c"
  is "\<lambda>f g (a, b). f a + g b"
  by (auto intro!: bounded_linear_intros
    intro: bounded_linear_compose
    simp: split_beta')

lemma blinfun_apply_comp12[simp]: "blinfun_apply (comp12 f g) b = f (fst b) + g (snd b)"
  by (simp add: comp12.rep_eq split_beta)


subsection \<open>Order Transitivity Attributes\<close>

attribute_setup le = \<open>Scan.succeed (Thm.rule_attribute [] (fn context => fn thm => thm RS @{thm order_trans}))\<close>
  "transitive version of inequality (useful for intro)"
attribute_setup ge = \<open>Scan.succeed (Thm.rule_attribute [] (fn context => fn thm => thm RS @{thm order_trans[rotated]}))\<close>
  "transitive version of inequality (useful for intro)"


subsection \<open>point reflection\<close>

definition preflect::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a" where "preflect \<equiv> \<lambda>t0 t. 2 *\<^sub>R t0 - t"

lemma preflect_preflect[simp]: "preflect t0 (preflect t0 t) = t"
  by (simp add: preflect_def algebra_simps)

lemma preflect_preflect_image[simp]: "preflect t0 ` preflect t0 ` S = S"
  by (simp add: image_image)

lemma is_interval_preflect[simp]: "is_interval (preflect t0 ` S) \<longleftrightarrow> is_interval S"
  by (auto simp: preflect_def[abs_def])

lemma iv_in_preflect_image[intro, simp]: "t0 \<in> T \<Longrightarrow> t0 \<in> preflect t0 ` T"
  by (auto intro!: image_eqI simp: preflect_def algebra_simps scaleR_2)

lemma preflect_tendsto[tendsto_intros]:
  fixes l::"'a::real_normed_vector"
  shows "(g \<longlongrightarrow> l) F \<Longrightarrow> (h \<longlongrightarrow> m) F \<Longrightarrow> ((\<lambda>x. preflect (g x) (h x)) \<longlongrightarrow> preflect l m) F"
  by (auto intro!: tendsto_eq_intros simp: preflect_def)

lemma continuous_preflect[continuous_intros]:
  fixes a::"'a::real_normed_vector"
  shows "continuous (at a within A) (preflect t0)"
  by (auto simp: continuous_within intro!: tendsto_intros)

lemma
  fixes t0::"'a::ordered_real_vector"
  shows preflect_le[simp]: "t0 \<le> preflect t0 b \<longleftrightarrow> b \<le> t0"
    and le_preflect[simp]: "preflect t0 b \<le> t0 \<longleftrightarrow> t0 \<le> b"
    and antimono_preflect: "antimono (preflect t0)"
    and preflect_le_preflect[simp]: "preflect t0 a \<le> preflect t0 b \<longleftrightarrow> b \<le> a"
    and preflect_eq_cancel[simp]: "preflect t0 a = preflect t0 b \<longleftrightarrow> a = b"
  by (auto intro!: antimonoI simp: preflect_def scaleR_2)

lemma preflect_eq_point_iff[simp]: "t0 = preflect t0 s \<longleftrightarrow> t0 = s" "preflect t0 s = t0 \<longleftrightarrow> t0 = s"
  by (auto simp: preflect_def algebra_simps scaleR_2)

lemma preflect_minus_self[simp]: "preflect t0 s - t0 = t0 - s"
  by (simp add: preflect_def scaleR_2)

end
