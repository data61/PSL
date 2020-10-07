section \<open>Topological Manifolds\<close>
theory Topological_Manifold
  imports Chart
begin

text \<open>Definition of topological manifolds. Existence of locally finite cover.\<close>

subsection \<open>Defintition\<close>

text \<open>We define topological manifolds as a second-countable Hausdorff space, where
  every point in the carrier set has a neighborhood that is homeomorphic to an open
  subset of the Euclidean space. Here topological manifolds are specified by a set
  of charts, and the carrier set is simply defined to be the union of the domain of
  the charts.\<close>
locale manifold =
  fixes charts::"('a::{second_countable_topology, t2_space}, 'e::euclidean_space) chart set"
begin

definition "carrier = (\<Union>(domain ` charts))"

lemma open_carrier[intro, simp]: "open carrier"
  by (auto simp: carrier_def)

lemma carrierE:
  assumes "x \<in> carrier"
  obtains c where "c \<in> charts" "x \<in> domain c"
  using assms by (auto simp: carrier_def)

lemma domain_subset_carrier[simp]: "domain c \<subseteq> carrier" if "c \<in> charts"
  using that
  by (auto simp: carrier_def)

lemma in_domain_in_carrier[intro, simp]: "c \<in> charts \<Longrightarrow> x \<in> domain c \<Longrightarrow> x \<in> carrier"
  by (auto simp: carrier_def)


subsection \<open>Existence of locally finite cover\<close>

text \<open>Every point has a precompact neighborhood.\<close>
lemma precompact_neighborhoodE:
  assumes "x \<in> carrier"
  obtains C where "x \<in> C" "open C" "compact (closure C)" "closure C \<subseteq> carrier"
proof -
  from carrierE[OF assms] obtain c where c: "c \<in> charts" "x \<in> domain c" by auto
  then have "c x \<in> codomain c" by auto
  with open_contains_cball[of "codomain c"]
  obtain e where e: "0 < e" "cball (apply_chart c x) e \<subseteq> codomain c"
    by auto
  then have e': "ball (apply_chart c x) e \<subseteq> codomain c"
    by (auto simp: mem_ball)
  define C where "C = inv_chart c ` ball (c x) e"
  have "x \<in> C"
    using c \<open>e > 0\<close>
    unfolding C_def
    by (auto intro!: image_eqI[where x="apply_chart c x"])
  moreover have "open C"
    using e'
    by (auto simp: C_def)
  moreover
  have compact: "compact (inv_chart c ` cball (apply_chart c x) e)"
    using e
    by (intro compact_continuous_image continuous_on_chart) auto
  have closure_subset: "closure C \<subseteq> inv_chart c ` cball (apply_chart c x) e"
    apply (rule closure_minimal)
    subgoal by (auto simp: C_def mem_ball)
    subgoal by (rule compact_imp_closed) (rule compact)
    done
  have "compact (closure C)"
    apply (rule compact_if_closed_subset_of_compact[where T="inv_chart c ` cball (c x) e"])
    subgoal by simp
    subgoal by (rule compact)
    subgoal by (rule closure_subset)
    done
  moreover have "closure C \<subseteq> carrier"
    using closure_subset c e
    by force
  ultimately show ?thesis ..
qed

text \<open>There exists a covering of the carrier by precompact sets.\<close>
lemma precompact_open_coverE:
  obtains U::"nat\<Rightarrow>'a set"
  where "(\<Union>i. U i) = carrier" "\<And>i. open (U i)" "\<And>i. compact (closure (U i))"
    "\<And>i. closure (U i) \<subseteq> carrier"
proof cases
  assume "carrier = {}"
  then have "(\<Union>i. {}) = carrier" "open {}" "compact (closure {})" "closure {} \<subseteq> carrier"
    by auto
  then show ?thesis ..
next
  assume "carrier \<noteq> {}"
  have "\<exists>b. x \<in> b \<and> open b \<and> compact (closure b) \<and> closure b \<subseteq> carrier" if "x \<in> carrier" for x
    using that
    by (rule precompact_neighborhoodE) auto
  then obtain balls where balls:
    "\<And>x. x \<in> carrier \<Longrightarrow> x \<in> balls x"
    "\<And>x. x \<in> carrier \<Longrightarrow> open (balls x)"
    "\<And>x. x \<in> carrier \<Longrightarrow> compact (closure (balls x))"
    "\<And>x. x \<in> carrier \<Longrightarrow> closure (balls x) \<subseteq> carrier"
    by metis
  let ?balls = "balls ` carrier"
  have *: "\<And>x::'a set. x \<in> ?balls \<Longrightarrow> open x" by (auto simp: balls)
  from Lindelof[of "?balls", OF this]
  obtain \<F>' where \<F>': "\<F>' \<subseteq> ?balls" "countable \<F>'" "\<Union>\<F>' = \<Union>?balls"
    by auto
  have "\<F>' \<noteq> {}" using \<F>' balls \<open>carrier \<noteq> {}\<close>
    by auto
  define U where "U = from_nat_into \<F>'"
  have into_range_balls: "U i \<in> ?balls" for i
  proof -
    have "from_nat_into \<F>' i \<in> \<F>'" for i
      by (rule from_nat_into) fact
    also have "\<F>' \<subseteq> ?balls" by fact
    finally show ?thesis by (simp add: U_def)
  qed
  have U: "open (U i)" "compact (closure (U i))" "closure (U i) \<subseteq> carrier" for i
    using balls into_range_balls[of i]
    by force+
  then have "U i \<subseteq> carrier" for i using closure_subset by force
  have "(\<Union>i. U i) = carrier"
  proof (rule antisym)
    show "(\<Union>i. U i) \<subseteq> carrier" using \<open>U _ \<subseteq> carrier\<close> by force
  next
    show "carrier \<subseteq> (\<Union>i. U i)"
    proof safe
      fix x::'a
      assume "x \<in> carrier"
      then have "x \<in> balls x" by fact
      with \<open>x \<in> carrier\<close> \<F>' obtain F where "x \<in> F" "F \<in> \<F>'" by blast
      with from_nat_into_surj[OF \<open>countable \<F>'\<close> \<open>F \<in> \<F>'\<close>]
      obtain i where "x \<in> U i" by (auto simp: U_def)
      then show "x \<in> (\<Union>i. U i)" by auto
    qed
  qed
  then show ?thesis using U ..
qed

text \<open>There exists a locally finite covering of the carrier by precompact sets.\<close>
lemma precompact_locally_finite_open_coverE:
  obtains W::"nat\<Rightarrow>'a set"
  where "carrier = (\<Union>i. W i)" "\<And>i. open (W i)" "\<And>i. compact (closure (W i))"
    "\<And>i. closure (W i) \<subseteq> carrier"
    "locally_finite_on carrier UNIV W"
proof -
  from precompact_open_coverE obtain U
    where U: "(\<Union>i::nat. U i) = carrier" "\<And>i. open (U i)" "\<And>i. compact (closure (U i))"
      "\<And>i. closure (U i) \<subseteq> carrier"
    by auto
  have "\<exists>V. \<forall>j.
    (open (V j) \<and>
    compact (closure (V j)) \<and>
    U j \<subseteq> V j \<and>
    closure (V j) \<subseteq> carrier) \<and>
    closure (V j) \<subseteq> V (Suc j)"
    (is "\<exists>V. \<forall>j. ?P j (V j) \<and> ?Q j (V j) (V (Suc j))")
  proof (rule dependent_nat_choice)
    show "\<exists>x. ?P 0 x" using U by (force intro!: exI[where x="U 0"])
  next
    fix X n
    assume P: "?P n X"
    have "closure X \<subseteq> (\<Union>c. U c)"
      unfolding U using P by auto
    have "compact (closure X)" using P by auto
    from compactE_image[OF this, of UNIV U, OF \<open>open (U _)\<close> \<open>closure X \<subseteq> _\<close>]
    obtain M where M: "M \<subseteq> UNIV" "finite M" "closure X \<subseteq> (\<Union>c\<in>M. U c)"
      by auto
    show "\<exists>y. ?P (Suc n) y \<and> ?Q n X y"
    proof (intro exI[where x="U (Suc n) \<union> (\<Union>c\<in>M. U c)"] impI conjI)
      show "open (U (Suc n) \<union> \<Union>(U ` M))"
        by (auto intro!: U)
      show "compact (closure (U (Suc n) \<union> \<Union>(U ` M)))"
        using \<open>finite M\<close>
        by (auto simp add: closure_Union intro!: U)
      show "U (Suc n) \<subseteq> U (Suc n) \<union> \<Union>(U ` M)" by auto
      show "closure (U (Suc n) \<union> \<Union>(U ` M)) \<subseteq> carrier"
        using U \<open>finite M\<close>
        by (force simp: closure_Union)
      show "closure X \<subseteq> U (Suc n) \<union> (\<Union>c\<in>M. U c)"
        using M by auto
    qed
  qed
  then obtain V where V:
    "\<And>j. closure (V j) \<subseteq> V (Suc j)"
    "\<And>j. open (V j)"
    "\<And>j. compact (closure (V j))"
    "\<And>j. U j \<subseteq> V j"
    "\<And>j. closure (V j) \<subseteq> carrier"
    by metis
  have V_mono_Suc: "\<And>j. V j \<subseteq> V (Suc j)"
    using V by auto
  have V_mono: "V l \<subseteq> V m" if "l \<le> m" for l m
    using V_mono_Suc that
    by (rule lift_Suc_mono_le[of V])
  have V_cover: "carrier = \<Union>(V ` UNIV)"
  proof (rule antisym)
    show "carrier \<subseteq> \<Union>(V ` UNIV)"
      unfolding U(1)[symmetric]
      using V(4)
      by auto
    show "\<Union>(V ` UNIV) \<subseteq> carrier"
      using V(5) by force
  qed
  define W where "W j = (if j < 2 then V j else V j - closure (V (j - 2)))" for j
  have "compact (closure (W j))" for j
    apply (rule compact_if_closed_subset_of_compact[where T="closure (V j)"])
    subgoal by simp
    subgoal by (simp add: V)
    subgoal
      apply (rule closure_mono)
      using V(1)[of j] V(1)[of "Suc j"]
      by (auto simp: W_def)
    done
  have open_W: "open (W j)" for j
    by (auto simp: W_def V)
  have W_cover: "p \<in> \<Union>(W ` UNIV)" if "p \<in> carrier" for p
  proof -
    have "p \<in> \<Union>(V ` UNIV)" using that V_cover
      by auto
    then have ex: "\<exists>i. p \<in> V i" by auto
    define k where "k = (LEAST i. p \<in> V i)"
    from LeastI_ex[OF ex]
    have k: "p \<in> V k" by (auto simp: k_def)
    have "p \<in> W k"
    proof cases
      assume "k < 2"
      then show ?thesis using k
        by (auto simp: W_def)
    next
      assume k2: "\<not>k < 2"
      have False if "p \<in> closure (V (k - 2))"
      proof -
        have "Suc (k - 2) = k - 1" using k2 by arith
        then have "p \<in> V (k - 1)"
          using k2 that V(1)[of "k - 2"]
          by auto
        moreover
        have "k - 1 < k" using k2 by arith
        from not_less_Least[OF this[unfolded k_def], folded k_def]
        have "p \<notin> V (k - 1)" .
        ultimately show ?thesis by simp
      qed
      then show ?thesis
        using k
        by (auto simp: W_def)
    qed
    then show ?thesis by auto
  qed
  have W_eq_carrier: "carrier = (\<Union>i. W i)"
  proof (rule antisym)
    show "carrier \<subseteq> (\<Union>i. W i)"
      using W_cover by auto
    have "(\<Union>i. W i) \<subseteq> (\<Union>i. V i)"
      by (auto simp: W_def split: if_splits)
    also have "\<dots> = carrier" by (simp add: V_cover)
    finally show "(\<Union>i. W i) \<subseteq> carrier" .
  qed
  have W_disjoint: "W k \<inter> W l = {}" if less: "l < k - 1" for l k
  proof -
    from less have "k \<ge> 2" by arith
    then have "W k = V k - closure (V (k - 2))"
      by (auto simp: W_def)
    moreover have "W l \<subseteq> V (k - 2)"
    proof -
      have "W l \<subseteq> V l"
        by (auto simp: W_def)
      also have "\<dots> \<subseteq> V (k - 2)"
        by (rule V_mono) (use less in arith)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by auto
  qed
  have "locally_finite_on carrier UNIV W"
  proof (rule locally_finite_on_open_coverI)
    show "carrier \<subseteq> \<Union>(W ` UNIV)" unfolding W_eq_carrier by simp
    show "open (W i)" for i by (auto simp: open_W)
    fix k
    have "{i. W i \<inter> W k \<noteq> {}} \<subseteq> {(k - 1) .. (k + 1)}"
    proof (rule subsetI)
      fix l
      assume "l \<in> {i. W i \<inter> W k \<noteq> {}} "
      then have l: "W l \<inter> W k \<noteq> {}"
        by auto
      consider "l < k - 1" | "l > k + 1" | "k-1 \<le> l" "l \<le> k+1" by arith
      then show "l \<in> {(k - 1) .. (k + 1)}"
      proof cases
        case 1
        from W_disjoint[OF this] l
        show ?thesis by auto
      next
        case 2
        then have "k < l - 1" by arith
        from W_disjoint[OF this] l
        show ?thesis by auto
      next
        case 3
        then show ?thesis
          by (auto simp: l)
      qed
    qed
    also have "finite \<dots>" by simp
    finally (finite_subset)
    show "finite {i\<in>UNIV . W i \<inter> W k \<noteq> {}}" by simp
  qed
  have "closure (W i) \<subseteq> carrier" for i
    using V closure_mono
    apply (auto simp: W_def)
    using Diff_subset subsetD by blast
  have "carrier = (\<Union>i. W i)" "\<And>i. open (W i)" "\<And>i. compact (closure (W i))"
    "\<And>i. closure (W i) \<subseteq> carrier"
    "locally_finite_on carrier UNIV W"
    by fact+
  then show ?thesis ..
qed

end

end
