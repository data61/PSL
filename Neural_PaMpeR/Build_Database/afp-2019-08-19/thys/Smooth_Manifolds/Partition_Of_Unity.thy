section \<open>Partitions Of Unity\<close>
theory Partition_Of_Unity
  imports Bump_Function Differentiable_Manifold
begin


subsection \<open>Regular cover\<close>

context c_manifold begin

text \<open>A cover is regular if, in addition to being countable and locally finite,
  the codomain of every chart is the open ball of radius 3, such that the
  inverse image of open balls of radius 1 also cover the manifold.\<close>
definition "regular_cover I (\<psi>::'i\<Rightarrow>('a, 'b) chart) \<longleftrightarrow>
  countable I \<and>
  carrier = (\<Union>i\<in>I. domain (\<psi> i)) \<and>
  locally_finite_on carrier I (domain o \<psi>) \<and>
  (\<forall>i\<in>I. codomain (\<psi> i) = ball 0 3) \<and>
  carrier = (\<Union>i\<in>I. inv_chart (\<psi> i) ` ball 0 1)"

text \<open>Every covering has a refinement that is a regular cover.\<close>
lemma reguler_refinementE:
  fixes \<X>::"'i \<Rightarrow> 'a set"
  assumes cover: "carrier \<subseteq> (\<Union>i\<in>I. \<X> i)" and open_cover: "\<And>i. i \<in> I \<Longrightarrow> open (\<X> i)"
  obtains N::"nat set" and \<psi>::"nat \<Rightarrow> ('a, 'b) chart"
  where "\<And>i. i \<in> N \<Longrightarrow> \<psi> i \<in> atlas" "(domain o \<psi>) ` N refines \<X> ` I" "regular_cover N \<psi>"
proof -
  from precompact_locally_finite_open_coverE
  obtain V::"nat\<Rightarrow>_" where V:
    "carrier = (\<Union>i. V i)"
    "\<And>i. open (V i)"
    "\<And>i. compact (closure (V i))"
    "\<And>i. closure (V i) \<subseteq> carrier"
    "locally_finite_on carrier UNIV V"
    by auto

  define intersecting where "intersecting v = {i. V i \<inter> v \<noteq> {}}" for v
  have intersecting_closure: "intersecting (closure x) = intersecting x" for x
    using open_Int_closure_eq_empty[OF V(2), of _ x]
    by (auto simp: intersecting_def)
  from locally_finite_compactD[OF V(5) V(3) V(4)]
  have "finite (intersecting (closure (V x)))" for x
    by (simp add: intersecting_def)
  then have finite_intersecting: "finite (intersecting (V x))" for x
    by (simp add: intersecting_closure)

  have "\<exists>\<psi>::('a, 'b) chart.
    \<psi> \<in> atlas \<and>
    codomain \<psi> = ball 0 3 \<and>
    (\<exists>c\<in>I. domain \<psi> \<subseteq> \<X> c) \<and>
     (\<forall>j. p \<in> V j \<longrightarrow> domain \<psi> \<subseteq> V j) \<and>
      p \<in> domain \<psi> \<and>
      \<psi> p = 0"
    if "p \<in> carrier" for p
  proof -
    from cover that open_cover obtain c where c: "p \<in> \<X> c" "open (\<X> c)" "c \<in> I"
      by force
    define VS where "VS = {U. p \<in> V U}"
    have open_VS: "\<And>T. T \<in> VS \<Longrightarrow> open (V T)"
      by (auto simp: VS_def V)
    from locally_finite_onD[OF V(5) that]
    have "finite VS" by (simp add: VS_def)
    from atlasE[OF that] obtain \<psi>' where \<psi>': "\<psi>' \<in> atlas" "p \<in> domain \<psi>'" .
    define W where  "W = (\<Inter>i\<in>VS. V i) \<inter> domain \<psi>' \<inter> \<X> c"
    have "open W"
      by (force simp: W_def open_VS intro!: c \<open>finite VS\<close>)
    have "p \<in> W" by (auto simp: W_def c \<psi>' VS_def)
    have "W \<subseteq> carrier"
      using \<psi>'
      by (auto simp: W_def)
    have "0 < (3::real)" by auto
    from open_centered_ball_chartE[OF \<open>p \<in> W\<close> \<open>open W\<close> \<open>W \<subseteq> carrier\<close> \<open>0 < 3\<close>]
    obtain \<psi> where \<psi>: "\<psi> \<in> atlas" "p \<in> domain \<psi>" "\<psi> p = 0" "domain \<psi> \<subseteq> W" "codomain \<psi> = ball 0 3"
      by auto
    moreover have "\<exists>x\<in>I. domain \<psi> \<subseteq> \<X> x"
      using c \<psi> by (auto simp: W_def)
    moreover have "p \<in> V j \<Longrightarrow> domain \<psi> \<subseteq> V j" for j
      using c \<psi> by (auto simp: W_def VS_def)
    ultimately show ?thesis
      by (intro exI[where x=\<psi>]) auto
  qed
  then have "\<forall>p2 \<in> carrier.
    \<exists>\<psi>::('a, 'b) chart. \<psi> \<in> atlas \<and> codomain \<psi> = ball 0 3 \<and>
         (\<exists>c\<in>I. domain \<psi> \<subseteq> \<X> c) \<and> (\<forall>j. p2 \<in> V j \<longrightarrow> domain \<psi> \<subseteq> V j) \<and> p2 \<in> domain \<psi> \<and>
         apply_chart \<psi> p2 = 0"
    by blast
  then obtain \<psi>::"'a \<Rightarrow> ('a, 'b) chart" where \<psi>:
    "\<And>p. p \<in> carrier \<Longrightarrow> codomain (\<psi> p) = ball 0 3"
    "\<And>p. p \<in> carrier \<Longrightarrow> (\<exists>c\<in>I. domain (\<psi> p) \<subseteq> \<X> c)"
    "\<And>p j. p \<in> V j \<Longrightarrow> domain (\<psi> p) \<subseteq> V j"
    "\<And>p j. p \<in> carrier \<Longrightarrow> p \<in> domain (\<psi> p)"
    "\<And>p. p \<in> carrier \<Longrightarrow> (\<psi> p) p = 0"
    "\<And>p. p \<in> carrier \<Longrightarrow> \<psi> p \<in> atlas"
    unfolding bchoice_iff
    apply atomize_elim
    apply auto
    subgoal for f
      apply (rule exI[where x=f])
      using V
      by auto
    done

  define U where "U p = inv_chart (\<psi> p) ` ball 0 1" for p
  have U_open: "open (U p)" if "p \<in> carrier" for p
    using that \<psi>
    by (auto simp: U_def)
  have U_subset_domain: "x \<in> U p \<Longrightarrow> x \<in> domain (\<psi> p)" if "p \<in> carrier" for x p
    using \<psi>(1) that
    by (auto simp: U_def)

  have "\<exists>M. M \<subseteq> closure (V l) \<and> finite M \<and> closure (V l) \<subseteq> \<Union>(U ` M)" for l
  proof -
    have clcover: "closure (V l) \<subseteq> \<Union>(U ` closure (V l))"
      using \<psi>
      apply (auto simp: U_def)
      apply (rule bexI)
       prefer 2 apply assumption
      apply (rule image_eqI)
       apply (rule inv_chart_inverse[symmetric])
       apply (rule \<psi>)
       apply auto
      using V(4) apply force
      by (metis V(4) less_irrefl norm_numeral norm_one norm_zero one_less_numeral_iff subsetCE
          zero_less_norm_iff zero_neq_numeral)
    have "B \<in> U ` closure (V l) \<Longrightarrow> open B" for B
      using V(4) by (auto intro!: U_open)
    from compactE[OF V(3) clcover this]
    obtain Um where Um: "Um \<subseteq> U ` closure (V l)" "finite Um" "closure (V l) \<subseteq> \<Union>Um"
      by auto
    from Um(1) have "\<forall>t\<in>Um. \<exists>p\<in>closure (V l). t = U p"
      by auto
    then obtain p_of where p_of: "\<And>t. t \<in> Um \<Longrightarrow> p_of t \<in> closure (V l)"
      "\<And>t. t \<in> Um \<Longrightarrow> t = U (p_of t)"
      by metis
    have "p_of ` Um \<subseteq> closure (V l)"
      using p_of
      by auto
    moreover have "finite (p_of ` Um)" using \<open>finite Um\<close> by auto
    moreover have "closure (V l) \<subseteq> \<Union>(U ` p_of ` Um)"
      using Um p_of by auto
    ultimately show ?thesis by blast
  qed
  then obtain M' where M': "\<And>l. M' l \<subseteq> closure (V l)" "\<And>l. finite (M' l)" "\<And>l. closure (V l) \<subseteq> \<Union>(U ` M' l)"
    by metis
  define M where "M v = M' (LEAST l. V l = v)" for v
  have V_Least: "V (LEAST la. V la = V l) = V l" for l
    by (rule LeastI_ex) auto
  have M: "M (V l) \<subseteq> closure (V l)" "finite (M v)" "closure (V l) \<subseteq> \<Union>(U ` M (V l))" for v l
    subgoal
      unfolding M_def
      apply (rule order_trans)
       apply (rule M')
      by (auto simp: V_Least)
    subgoal using M' by (auto simp: M_def)
    subgoal
      unfolding M_def
      apply (subst V_Least[symmetric])
      by (rule M')
    done

  from M(1) V(4) have M_carrier: "x \<in> M (V l) \<Longrightarrow> x \<in> carrier" for x l by auto

  have "countable (\<Union>l. M (V l))"
    using M(2) by (auto simp: countable_finite)
  from countableE_bij[OF this]
  obtain m and N::"nat set" where n: "bij_betw m N (\<Union>l. M (V l))" .
  define m' where "m' = the_inv_into N m"
  have m_inverse[simp]: "\<And>i. i \<in> N \<Longrightarrow> m' (m i) = i"
    and m'_inverse[simp]: "\<And>x l. x \<in> M (V l) \<Longrightarrow> m (m' x) = x"
    using n
    by (force simp: bij_betw_def m'_def the_inv_into_f_f)+

  have m_in: "m i \<in> (\<Union>l. M (V l))" if "i \<in> N" for i
    using n that
    by (auto dest!: bij_betwE)
  have m'_in: "m' x \<in> N" if "x \<in> M (V l)" for x l
    using that n
    by (auto simp: m'_def bij_betw_def intro!: the_inv_into_into)

  from m_in have m_in_carrier: "m i \<in> carrier" if "i \<in> N" for i
    using that M_carrier
    by auto
  then have "\<And>i. i \<in> N \<Longrightarrow> \<psi> (m i) \<in> atlas"
    by (rule \<psi>(6))
  moreover
  have "(domain o (\<lambda>i. (\<psi> (m i)))) ` N refines \<X> ` I"
    by (auto simp: refines_def dest!: m_in_carrier \<psi>(2))
  moreover
  have "regular_cover N (\<lambda>i. \<psi> (m i))"
  proof -
    have "countable N" by simp
    moreover
    have carrier_subset: "carrier \<subseteq> (\<Union>i \<in> N. inv_chart (\<psi> (m i)) ` ball 0 1)"
      unfolding V
    proof safe
      fix x i
      assume "x \<in> V i"
      with M obtain p where p: "p \<in> M (V i)" "x \<in> U p" by blast
      from p show "x \<in> (\<Union>i\<in>N. inv_chart (\<psi> (m i)) ` ball 0 1)"
        by (auto simp: U_def intro!: bexI[where x="m' p"] m'_in)
    qed
    have carrier_eq_W:  "carrier = (\<Union>i\<in>N. domain (\<psi> (m i)))" (is "_ = ?W")
    proof (rule antisym)
      note carrier_subset
      also have "\<dots> \<subseteq> ?W"
        using U_subset_domain \<psi>(1) M_carrier m_in
        by (force simp: V)
      finally show "carrier \<subseteq> ?W"
        by auto
      show "?W \<subseteq> carrier" using M_carrier \<psi>(6)  
        by (auto dest!: m_in)
    qed
    moreover have "locally_finite_on carrier N (\<lambda>i. domain (\<psi> (m i)))"
    proof (rule locally_finite_on_open_coverI)
      show "open (domain (\<psi> (m i)))" for i by auto
      show "carrier \<subseteq> (\<Union>i\<in>N. domain (\<psi> (m i)))"
        unfolding carrier_eq_W by auto
      fix ki
      assume "ki \<in> N"
      from m_in[OF this]
      obtain k where k: "m ki \<in> M (V k)" by auto
      have pkc: "m ki \<in> closure (V k)"
        using k M(1) by force
      obtain j where j: "m ki \<in> V j"
        using M_carrier[of "m ki" k] V(1) k by force
      have kj: "V k \<inter> V j \<noteq> {}"
        using open_Int_closure_eq_empty[OF V(2)]
        using pkc j by auto
      then have jinterk: "j \<in> intersecting (V k)" by (auto simp: intersecting_def)

      have 1: "compact (closure (V k))" by (rule V)
      have 2: "closure (V k) \<subseteq> \<Union>(range V)" unfolding V(1)[symmetric] by (rule V)
      have 3: "B \<in> range V \<Longrightarrow> open B" for B by (auto simp: V)
      from compactE[OF 1 2 3]
      obtain Vj where "Vj \<subseteq> range V" "finite Vj" "closure (V k) \<subseteq> \<Union>Vj" by auto
      then obtain J where "finite J" "closure (V k) \<subseteq> \<Union>(V ` J)"
        apply atomize_elim
        by (metis finite_subset_image)

      {
        fix ki' assume "ki' \<in> N"
        assume H: "domain (\<psi> (m ki')) \<inter> domain (\<psi> (m ki)) \<noteq> {}"
        obtain k' where ki': "m ki' \<in> M (V k')" using m_in[OF \<open>ki' \<in> N\<close>] by auto
        have k': "domain (\<psi> (m ki')) \<inter> domain (\<psi> (m ki)) \<noteq> {}" "m ki' \<in> M (V k')"
          using ki'  H by auto
        have pkc': "m ki' \<in> closure (V k')"
          using k' M(1) by force
        obtain j' where j': "m ki' \<in> V j'"
          using M_carrier V(1) k' by force
        have kj': "(V k') \<inter> V j' \<noteq> {}"
          using open_Int_closure_eq_empty[OF V(2)]
          using pkc' j' by auto
        then have j'interk': "k' \<in> intersecting (V j')" by (auto simp: intersecting_def)

        have j'interj: "j' \<in> intersecting (V j)"
          using k' \<psi>(3)[OF j'] \<psi>(3)[OF j]
          by (auto simp: intersecting_def)
        have "k' \<in> \<Union>(intersecting ` V ` \<Union>(intersecting ` V ` intersecting (V k)))"
          using jinterk j'interk' j'interj
          by blast
        then have "m ki' \<in> \<Union>((\<lambda>x. M (V x)) ` \<Union>(intersecting ` V ` \<Union>(intersecting ` V ` intersecting (V k))))"
          using ki'
          by auto
        from m_inverse[symmetric] this have "ki' \<in> m' ` \<Union>((\<lambda>x. M (V x)) ` \<Union>(intersecting ` V ` \<Union>(intersecting ` V ` intersecting (V k))))"
          by (rule image_eqI) fact
      } note * = this
      show "finite {i \<in> N. domain (\<psi> (m i)) \<inter> domain (\<psi> (m ki)) \<noteq> {}}"
        apply (rule finite_subset[where B="m' ` \<Union>((\<lambda>x. M (V x)) ` \<Union>(intersecting ` V ` \<Union>(intersecting ` V ` intersecting (V k))))"])
         apply clarsimp
        subgoal by (drule *, assumption, force)
        using finite_intersecting intersecting_def M by auto
    qed
    moreover have "(\<forall>i \<in> N. codomain (\<psi> (m i)) = ball 0 3)"
      using \<psi>(1) M_carrier m_in
      by force
    moreover have "carrier = (\<Union>i \<in> N. inv_chart (\<psi> (m i)) ` ball 0 1)"
    proof (rule antisym)
      show "(\<Union>i\<in>N. inv_chart (\<psi> (m i)) ` ball 0 1) \<subseteq> carrier"
        using \<psi>(6)[OF M_carrier] M_carrier m_in
        by (force simp: \<psi>(1))
    qed (rule carrier_subset)
    ultimately show ?thesis
      by (auto simp: regular_cover_def o_def)
  qed
  ultimately
  show ?thesis ..
qed

lemma diff_apply_chart:
  "diff k (charts_submanifold (domain \<psi>)) charts_eucl \<psi>" if "\<psi> \<in> atlas"
proof -
  interpret submanifold charts k "domain \<psi>"
    by unfold_locales auto
  show ?thesis
  proof (unfold_locales)
    fix x assume x: "x \<in> sub.carrier"
    show "\<exists>c1\<in>sub.atlas.
            \<exists>c2\<in>manifold_eucl.dest.atlas.
               x \<in> domain c1 \<and> \<psi> ` domain c1 \<subseteq> domain c2 \<and> k-smooth_on (codomain c1) (c2 \<circ> \<psi> \<circ> inv_chart c1)"
      apply (rule bexI[where x = "restrict_chart (domain \<psi>) \<psi>"])
       apply (rule bexI[where x = "chart_eucl"])
      subgoal
      proof safe
        show "x \<in> domain (restrict_chart (domain \<psi>) \<psi>)"
          using x \<open>\<psi> \<in> atlas\<close>
          by auto
        show "k-smooth_on (codomain (restrict_chart (domain \<psi>) \<psi>)) (chart_eucl \<circ> \<psi> \<circ> inv_chart (restrict_chart (domain \<psi>) \<psi>))"
          apply (auto simp: o_def)
          apply (rule smooth_on_cong[where g="\<lambda>x. x"])
          by (auto intro!: open_continuous_vimage' continuous_on_codomain)
      qed simp
      subgoal by auto
      subgoal by (rule submanifold_atlasI) fact
      done
  qed
qed

lemma diff_inv_chart:
  "diff k (manifold_eucl.charts_submanifold (codomain c)) charts (inv_chart c)" if "c \<in> atlas"
proof -
  interpret submanifold charts_eucl k "codomain c"
    by unfold_locales auto
  show ?thesis
  proof (unfold_locales)
    fix x assume x: "x \<in> sub.carrier"
    show "\<exists>c1\<in>sub.atlas.
            \<exists>c2\<in>atlas.
               x \<in> domain c1 \<and> inv_chart c ` domain c1 \<subseteq> domain c2 \<and>
               k-smooth_on (codomain c1) (c2 \<circ> inv_chart c \<circ> inv_chart c1)"
      apply (rule bexI[where x = "restrict_chart (codomain c) chart_eucl"])
       apply (rule bexI[where x = c])
      subgoal
      proof safe
        show "x \<in> domain (restrict_chart (codomain c) chart_eucl)"
          using x \<open>c \<in> atlas\<close>
          by auto
        show "k-smooth_on (codomain (restrict_chart (codomain c) chart_eucl)) (c \<circ> inv_chart c \<circ> inv_chart (restrict_chart (codomain c) chart_eucl))"
          apply (auto simp: o_def)
          apply (rule smooth_on_cong[where g="\<lambda>x. x"])
          by (auto intro!: open_continuous_vimage' continuous_on_codomain)
      qed simp
      subgoal using that by simp
      subgoal
        by (rule submanifold_atlasI) auto
      done
  qed
qed

lemma chart_inj_on [simp]:
  fixes c :: "('a, 'b) chart"
  assumes "x \<in> domain c" "y \<in> domain c"
  shows "c x = c y \<longleftrightarrow> x = y"
proof -
  have "inj_on c (domain c)" by (rule inj_on_apply_chart)
  with assms show ?thesis by (auto simp: inj_on_def)
qed

subsection \<open>Partition of unity by smooth functions\<close>

text\<open>
  Given any open cover \<open>X\<close> indexed by a set \<open>A\<close>, there exists a family of
  smooth functions \<open>\<phi>\<close> indexed by \<open>A\<close>, such that \<open>0 \<le> \<phi> \<le> 1\<close>, the (closed) support
  of each \<open>\<phi> i\<close> is contained in \<open>X i\<close>, the supports are locally finite, and the
  sum of \<open>\<phi> i\<close> is the constant function \<open>1\<close>.\<close>
theorem partitions_of_unityE:
  fixes A::"'i set" and X::"'i \<Rightarrow> 'a set"
  assumes "carrier \<subseteq> (\<Union>i\<in>A. X i)"
  assumes "\<And>i. i \<in> A \<Longrightarrow> open (X i)"
  obtains \<phi>::"'i \<Rightarrow> 'a \<Rightarrow> real"
  where "\<And>i. i \<in> A \<Longrightarrow> diff_fun k charts (\<phi> i)"
    and "\<And>i x. i \<in> A \<Longrightarrow> x \<in> carrier \<Longrightarrow> 0 \<le> \<phi> i x"
    and "\<And>i x. i \<in> A \<Longrightarrow> x \<in> carrier \<Longrightarrow> \<phi> i x \<le> 1"
    and "\<And>x. x \<in> carrier \<Longrightarrow> (\<Sum>i\<in>{i\<in>A. \<phi> i x \<noteq> 0}. \<phi> i x) = 1"
    and "\<And>i. i \<in> A \<Longrightarrow> csupport_on carrier (\<phi> i) \<inter> carrier \<subseteq> X i"
    and "locally_finite_on carrier A (\<lambda>i. csupport_on carrier (\<phi> i))"
proof -
  from reguler_refinementE[OF assms]
  obtain N and \<psi>::"nat \<Rightarrow> ('a, 'b) chart" where \<psi>:
    "\<And>i. i \<in> N \<Longrightarrow> \<psi> i \<in> atlas"
    "(domain o \<psi>) ` N refines X ` A"
    "regular_cover N \<psi>" by blast

  define U where "U i = inv_chart (\<psi> i) ` ball 0 1" for i::nat
  define V where "V i = inv_chart (\<psi> i) ` ball 0 2" for i::nat
  define W where "W i = inv_chart (\<psi> i) ` ball 0 3" for i::nat
  
  from \<open>regular_cover N \<psi>\<close> have regular_cover:
    "countable N"
    "(\<Union>i\<in>N. U i) = (\<Union>i\<in>N. domain (\<psi> i))"
    "locally_finite_on carrier N (domain \<circ> \<psi>)"
    "\<And>i. i \<in> N \<Longrightarrow> codomain (\<psi> i) = ball 0 3"
    "carrier = (\<Union>i\<in>N. U i)"
    by (auto simp: regular_cover_def U_def)

  have open_W: "open (W i)" if "i \<in> N" for i
    using that
    by (auto simp: W_def regular_cover)
  have W_eq: "domain (\<psi> i) = W i" if "i \<in> N" for i
    using W_def regular_cover(4) that by force

  have carrier_W: "carrier = (\<Union>i\<in>N. W i)"
    by (auto simp: regular_cover W_eq)

  have V_subset_W: "closure (V i) \<subseteq> W i" if "i \<in> N" for i
  proof -
    have "closure (V i) \<subseteq> closure (inv_chart (\<psi> i) ` cball 0 2)"
      unfolding V_def
      by (rule closure_mono) auto
    also have "\<dots> = inv_chart (\<psi> i) ` cball 0 2"
      apply (rule closure_closed)
      apply (rule compact_imp_closed)
      apply (rule compact_continuous_image)
      by (auto intro!: continuous_intros simp: regular_cover that)
    also have "\<dots> \<subseteq> W i"
      by (auto simp: W_def)
    finally show ?thesis .
  qed

  have carrier_V: "carrier = (\<Union>i\<in>N. V i)"
    apply (rule antisym)
    subgoal unfolding regular_cover(5) by (auto simp: U_def V_def)
    subgoal unfolding carrier_W using V_subset_W by auto
    done

  define f where "f i x = (if x \<in> W i then H (\<psi> i x) else 0)" for i x
  have f_simps: "x \<in> W i \<Longrightarrow> f i x = H (\<psi> i x)"
    "x \<notin> W i \<Longrightarrow> f i x = 0"
    for i x
    by (auto simp: f_def)

  have f_eq_one: "f j y = 1" if "j \<in> N" "y \<in> U j" for j y
  proof -
    from that have "y \<in> W j" by (auto simp: U_def W_def)
    from \<open>y \<in> U j\<close> have "norm (\<psi> j y) \<le> 1"
      by (auto simp: U_def W_eq[symmetric] \<open>j \<in> N\<close> regular_cover(4))
    then show ?thesis
      by (auto simp: f_def \<open>y \<in> W j\<close> intro!: H_eq_one)
  qed

  have f_diff: "diff_fun k charts (f i)" if i: "i \<in> N" for i
  proof (rule manifold_eucl.diff_open_Un, unfold diff_fun_def[symmetric])
    note W_eq = W_eq[OF that]
    have "W i \<subseteq> carrier" 
      unfolding W_eq[symmetric] regular_cover using that by auto
    interpret W: submanifold _ _ "W i"
      by unfold_locales (auto simp: open_W i)
    
    have "diff_fun k (charts_submanifold (W i)) (H \<circ> (\<psi> i))"
      apply (rule diff_fun_compose[where ?M2.0 = charts_eucl])
       apply (rule diff_apply_chart[of "\<psi> i", unfolded W_eq])
      subgoal using \<psi> \<open>i \<in> N\<close> by auto
      apply (rule diff_fun_charts_euclI)
      by (rule H_smooth_on)
    then show "diff_fun k (charts_submanifold (W i)) (f i)"
      by (rule diff_fun.diff_fun_cong) (auto simp: f_def)

    interpret V': submanifold _ _ "carrier - closure (V i)"
      by unfold_locales auto

    have "diff_fun k (charts_submanifold (carrier - closure (V i))) 0"
      by (rule V'.sub.diff_fun_zero)
    then show "diff_fun k (charts_submanifold (carrier - closure (V i))) (f i)"
      apply (rule diff_fun.diff_fun_cong)
      unfolding f_def
      apply auto
      apply (rule H_eq_zero)
      unfolding V_def by (metis W_eq image_eqI in_closureI inv_chart_inverse)
    show "open (W i)" by (auto simp: W_def regular_cover i)
    show "open (carrier - closure (V i))" by auto
    show "carrier \<subseteq> W i \<union> (carrier - closure (V i))"
      using V_subset_W[OF i] by auto
  qed

  define g where "g \<psi> x = f \<psi> x / (\<Sum>i\<in>{j\<in>N. x \<in> W j}. f i x)" for \<psi> x

  have "\<forall>p\<in>carrier. \<exists>I. p \<in> I \<and> open I \<and>finite {i \<in> N. W i \<inter> I \<noteq> {}}"
    (is "\<forall>p\<in>carrier. ?P p")
  proof (rule ballI)
    fix p assume "p \<in> carrier"
    from locally_finite_onE[OF regular_cover(3) this]
    obtain I where "p \<in> I" "open I" "finite {i \<in> N. (domain \<circ> \<psi>) i \<inter> I \<noteq> {}}".
    moreover have "{i \<in> N. (domain \<circ> \<psi>) i \<inter> I \<noteq> {}} = {i \<in> N. W i \<inter> I \<noteq> {}}"
      by (auto simp: W_eq)
    ultimately show "?P p" by auto
  qed
  from bchoice[OF this] obtain I where I:
    "\<And>x. x \<in> carrier \<Longrightarrow> x \<in> I x"
    "\<And>x. x \<in> carrier \<Longrightarrow> open (I x)"
    "\<And>x. x \<in> carrier \<Longrightarrow> finite {i \<in> N. W i \<inter> I x \<noteq> {}}"
    by blast

  have subset_W: "{j \<in> N. y \<in> W j} \<subseteq> {j \<in> N. W j \<inter> I x \<noteq> {}}" if "y \<in> I x" "x \<in> carrier" for x y
    by (auto simp: that W_eq)
  have finite_W: "finite {j \<in> N. y \<in> W j}" if "y \<in> carrier" for y
    apply (rule finite_subset)
     apply (rule subset_W[OF _ that])
     apply (rule I[OF that])
    apply (rule I[unfolded o_def, OF that])
    done

  have g: "diff_fun k charts (g i)" if i: "i \<in> N" for i
  proof (rule manifold_eucl.diff_localI, unfold diff_fun_def[symmetric])
    fix x assume x: "x \<in> carrier"
    show "open (I x)" "x \<in> I x" using I x by auto
    then interpret submanifold _ _ "I x"
      by unfold_locales
    interpret df: diff_fun k charts "f i" by (rule f_diff) fact
    have "diff_fun k (charts_submanifold (I x)) (\<lambda>y. f i y / (\<Sum>j\<in>{j\<in>N. W j \<inter> I x \<noteq> {}}. f j y))"
      apply (rule sub.diff_fun_divide)
      subgoal
        apply (rule df.diff_submanifold[folded diff_fun_def])
        by (rule I) fact
      subgoal
      proof (rule sub.diff_fun_sum, clarsimp)
        fix j assume "j \<in> N" "W j \<inter> I x \<noteq> {}"
        interpret df': diff_fun k charts "f j" by (rule f_diff) fact
        show "diff_fun k (charts_submanifold (I x)) (f j)"
          apply (rule df'.diff_fun_submanifold)
          by (rule I) fact
      qed
      subgoal for y
        apply (subst sum_nonneg_eq_0_iff)
        subgoal using I(3)[OF x] by auto
        subgoal using H_range by (auto simp: f_def)
        subgoal
        proof clarsimp
          assume y: "y \<in> I x" "y \<in> carrier"
          then obtain j where "j \<in> N" "y \<in> U j"
            unfolding regular_cover(5) by auto
          then have "y \<in> W j"
            by (auto simp: U_def W_def)
          moreover
          have "W j \<inter> I x \<noteq> {}"
            using W_eq \<open>j \<in> N\<close> \<open>open (I x)\<close> \<open>y \<in> W j\<close> \<open>y \<in> carrier\<close> \<open>y \<in> I x\<close>
            by auto
          moreover
          note f_eq_one[OF \<open>j \<in> N\<close> \<open>y \<in> U j\<close>]
          ultimately show "\<exists>xa. xa \<in> N \<and> W xa \<inter> I x \<noteq> {} \<and> f xa y \<noteq> 0"
            by (intro exI[where x=j]) (auto simp: \<open>j \<in> N\<close>)
        qed
        done
      done
    then show "diff_fun k (charts_submanifold (I x)) (g i)"
      apply (rule diff_fun.diff_fun_cong)
      unfolding g_def
      apply simp
      apply (rule disjI2)
      apply (rule sum.mono_neutral_right)
      subgoal using I[OF \<open>x \<in> carrier\<close>] unfolding o_def by simp
      subgoal for y
        apply (rule subset_W)
        using carrier_submanifold I \<open>x \<in> carrier\<close> by auto
      subgoal by (auto simp: f_def)
      done
  qed

  have f_nonneg: "0 \<le> f i x" for i x
    by (auto simp: f_def H_range intro!: sum_nonneg)

  have U_sub_W: "x \<in> U i \<Longrightarrow> x \<in> W i" for x i
    by (auto simp: U_def W_def)

  have sumf_pos: "(\<Sum>i\<in>{j \<in> N. x \<in> W j}. f i x) > 0" if "x \<in> carrier" for x
    (* and this sum is smooth, use to simplify earlier reasoning! *)
    using that
    apply (auto simp: regular_cover(5))
    subgoal for i
      apply (rule sum_pos2[where i=i])
      using finite_W[OF that]
      by (auto simp: f_nonneg f_eq_one U_sub_W )
    done

  have sumf_nonneg: "(\<Sum>i\<in>{j \<in> N. x \<in> W j}. f i x) \<ge> 0" for x
    by (auto simp: f_nonneg intro!: sum_nonneg)

  have g_nonneg: "0 \<le> g i x" if "i \<in> N" "x \<in> carrier" for i x
    by (auto simp: g_def intro!: divide_nonneg_nonneg sumf_nonneg f_nonneg)

  have g_le_one: "g i x \<le> 1" if "i \<in> N" "x \<in> carrier" for i x
    apply (auto simp add: g_def) (*sumf is positive*)
    apply (cases "(\<Sum>i\<in>{j \<in> N. x \<in> W j}. f i x) = 0")
    subgoal by simp
    apply (subst divide_le_eq_1_pos)
    subgoal using sumf_nonneg[of x] by auto
    apply (cases "x \<in> W i")
    subgoal
      apply (rule member_le_sum)
      subgoal using \<open>i \<in> N\<close> by simp
      subgoal by (rule f_nonneg)
      using sum.infinite by blast
    subgoal by (simp add: f_simps sum_nonneg H_range)
    done
  have sum_g: "(\<Sum>i | i \<in> N \<and> x \<in> W i. g i x) = 1" if "x \<in> carrier" for x
    unfolding g_def
    apply (subst sum_divide_distrib[symmetric])
    using sumf_pos[OF that]
    by auto

  have "\<exists>a. \<forall>i\<in>N. W i \<subseteq> X (a i) \<and> a i \<in> A"
    using \<psi>(2) by (intro bchoice) (auto simp: refines_def W_eq)
  then obtain a where a: "\<And>i. i \<in> N \<Longrightarrow> W i \<subseteq> X (a i)" "\<And>i. i \<in> N \<Longrightarrow> a i \<in> A"
    by force

  define \<phi> where "\<phi> \<alpha> x = (\<Sum>i | i \<in> N \<and> a i = \<alpha> \<and> x \<in> W i. g i x)" for \<alpha> x

  have "diff_fun k charts (\<phi> \<alpha>)" if "\<alpha> \<in> A" for \<alpha>
  proof (rule manifold_eucl.diff_localI, unfold diff_fun_def[symmetric])
    (* extract the lemma here?! *)
    fix x assume x: "x \<in> carrier"
    show "open (I x)" "x \<in> I x" using I x by auto
    then interpret submanifold _ _ "I x"
      by unfold_locales
    have "diff_fun k (charts_submanifold (I x)) (\<lambda>y. (\<Sum>i | i \<in> N \<and> a i = \<alpha> \<and> W i \<inter> I x \<noteq> {}. g i y))"
      apply (rule sub.diff_fun_sum, clarsimp)
      subgoal premises prems for i
      proof -
        interpret dg: diff_fun k charts "g i" by (rule g) fact
        show ?thesis
          apply (rule dg.diff_fun_submanifold)
          by (rule I) fact
      qed
      done
    then show "diff_fun k (charts_submanifold (I x)) (\<phi> \<alpha>)"
      apply (rule diff_fun.diff_fun_cong)
      unfolding \<phi>_def
      apply (rule sum.mono_neutral_right)
      subgoal using _ I(3)[OF \<open>x \<in> carrier\<close>] by (rule finite_subset) (auto simp:)
      subgoal using \<open>open (I x)\<close> carrier_submanifold by auto
      subgoal by (auto simp: g_def f_def)
      done
  qed
  moreover
  have "0 \<le> \<phi> \<alpha> x" if "x \<in> carrier" for \<alpha> x
    by (auto simp: \<phi>_def intro!: sum_nonneg g_nonneg that)
  moreover
  have "\<phi> \<alpha> x \<le> 1" if "\<alpha> \<in> A" "x \<in> carrier" for \<alpha> x
  proof -
    have "\<phi> \<alpha> x \<le> (\<Sum>i | i \<in> N \<and> x \<in> W i. g i x)"
      unfolding \<phi>_def
      by (rule sum_mono2[OF finite_W]) (auto simp: intro!: g_nonneg \<open>x \<in> carrier\<close>)
    also have "\<dots> = 1"
      by (rule sum_g) fact
    finally show ?thesis .
  qed
  moreover
  have "(\<Sum>\<alpha>\<in>{\<alpha>\<in>A. \<phi> \<alpha> x \<noteq> 0}. \<phi> \<alpha> x) = 1" if "x \<in> carrier" for x
  proof -
    have "(\<Sum>\<alpha> | \<alpha> \<in> A \<and> \<phi> \<alpha> x \<noteq> 0. \<phi> \<alpha> x) =
      (\<Sum>\<alpha> | \<alpha> \<in> A \<and> \<phi> \<alpha> x \<noteq> 0. \<Sum>i | i \<in> N \<and> a i = \<alpha> \<and> x \<in> W i. g i x)"
      unfolding \<phi>_def ..
    also have "\<dots> = (\<Sum>(\<alpha>, i)\<in>(SIGMA xa:{\<alpha> \<in> A. \<phi> \<alpha> x \<noteq> 0}. {i \<in> N. a i = xa \<and> x \<in> W i}). g i x)"
      apply (rule sum.Sigma)
      subgoal
        apply (rule finite_subset[where B="a ` {j \<in> N. x \<in> W j}"])
        subgoal
          apply (auto simp: \<phi>_def)
          apply (subst (asm) sum_nonneg_eq_0_iff)
          subgoal using _ finite_W[OF \<open>x \<in> carrier\<close>] by (rule finite_subset) auto
          subgoal by (rule g_nonneg[OF _ \<open>x \<in> carrier\<close>]) auto
          subgoal by auto
          done
        subgoal
          using finite_W[OF \<open>x \<in> carrier\<close>] by (rule finite_imageI)
        done
      subgoal
        apply (auto)
        using _ finite_W[OF \<open>x \<in> carrier\<close>]
        by (rule finite_subset) auto
      done
    also have "\<dots> = (\<Sum>i\<in>snd ` (SIGMA xa:{\<alpha> \<in> A. \<phi> \<alpha> x \<noteq> 0}. {i \<in> N. a i = xa \<and> x \<in> W i}). g i x)"
      apply (rule sum.reindex_cong[where l="\<lambda>i. (a i, i)"])
      subgoal by (auto simp: inj_on_def)
      subgoal
        apply (auto simp: a)
        apply (auto simp: \<phi>_def)
        apply (subst (asm) sum_nonneg_eq_0_iff)
        subgoal
          using _ finite_W[OF \<open>x \<in> carrier\<close>]
          by (rule finite_subset) auto
        subgoal by (auto intro!: g_nonneg \<open>x \<in> carrier\<close>)
        subgoal for i
          apply auto
          subgoal for yy
            apply (rule imageI)
            apply (rule image_eqI[where x="(a i, i)"])
             apply (auto intro!: a)
            apply (subst (asm) sum_nonneg_eq_0_iff)
            subgoal using _ finite_W[OF \<open>x \<in> carrier\<close>] by (rule finite_subset) auto
            subgoal by (rule g_nonneg[OF _ \<open>x \<in> carrier\<close>]) auto
            subgoal by auto
            done
          done
        done
      subgoal by auto
      done
    also have "\<dots> = (\<Sum>i | i \<in> N \<and> x \<in> W i. g i x)"
      apply (rule sum.mono_neutral_left)
      subgoal by (rule finite_W) fact
      subgoal by auto
      subgoal
        apply (auto simp: Sigma_def image_iff a)
        apply (auto simp: \<phi>_def)
        subgoal
          apply (subst (asm) sum_nonneg_eq_0_iff)
          subgoal using _ finite_W[OF \<open>x \<in> carrier\<close>] by (rule finite_subset) auto
          subgoal by (rule g_nonneg[OF _ \<open>x \<in> carrier\<close>]) auto
          subgoal by auto
          done
        done
      done
    also have "\<dots> = 1" by (rule sum_g) fact
    finally show ?thesis .
  qed
  moreover
  have g_supp_le_V: "support_on carrier (g i) \<subseteq> V i" if "i \<in> N" for i
    apply (auto simp: support_on_def g_def f_def V_def dest!: H_neq_zeroD)
    apply (rule image_eqI[OF ])
     apply (rule inv_chart_inverse[symmetric])
     apply (simp add: W_eq that)
    apply simp
    done
  then have clsupp_g_le_W: "closure (support_on carrier (g i)) \<subseteq> W i" if "i \<in> N" for i
    unfolding csupport_on_def
    using V_subset_W closure_mono that
    by blast
  then have csupp_g_le_W: "csupport_on carrier (g i) \<subseteq> W i" if "i \<in> N" for i
    using that
    by (auto simp: csupport_on_def)
  have *: "{i \<in> N. domain (\<psi> i) \<inter> Na \<noteq> {}} = {i \<in> N. W i \<inter> Na \<noteq> {}}" for Na
    by (auto simp: W_eq)
  then have lfW: "locally_finite_on carrier N W"
    using regular_cover(3) by (simp add: locally_finite_on_def)
  then have lf_supp_g: "locally_finite_on carrier {i \<in> N. a i = \<alpha>} (\<lambda>i. support_on carrier (g i))" if "\<alpha> \<in> A" for \<alpha>
    apply (rule locally_finite_on_subset)
    using g_supp_le_V V_subset_W
    by force+
  have "csupport_on carrier (\<phi> \<alpha>) \<inter> carrier \<subseteq> X \<alpha>" if "\<alpha> \<in> A" for \<alpha>
  proof -
    have *: "closure (\<Union>i\<in>{i \<in> N. a i = \<alpha>}. support_on carrier (g i)) \<subseteq> closure (\<Union>i\<in>N. V i)"
      by (rule closure_mono) (use g_supp_le_V in auto)
    have "support_on carrier (\<phi> \<alpha>) \<subseteq> (\<Union>i\<in>{i \<in> N. a i = \<alpha>}. support_on carrier (g i))"
      unfolding \<phi>_def[abs_def]
      apply (rule order_trans)
       apply (rule support_on_nonneg_sum_subset')
      using g_supp_le_V
      by (auto simp: carrier_V)
    then have "csupport_on carrier (\<phi> \<alpha>) \<inter> carrier \<subseteq> closure \<dots> \<inter> carrier"
      unfolding csupport_on_def using closure_mono by auto
    also have "\<dots> = (\<Union>i\<in>{i \<in> N. a i = \<alpha>}. closure (support_on carrier (g i)))"
      apply (rule locally_finite_on_closure_Union[OF lf_supp_g[OF that], symmetric])
      using closure_mono[OF g_supp_le_V] V_subset_W
      by (force simp: carrier_W)
    also have "\<dots> \<subseteq> (\<Union>i\<in>{i \<in> N. a i = \<alpha>}. W i)"
      apply (rule UN_mono)
      using clsupp_g_le_W
      by auto
    also have "\<dots> \<subseteq> X \<alpha>"
      using a
      by auto
    finally show ?thesis .
  qed
  moreover
  have "locally_finite_on carrier A (\<lambda>i. support_on carrier (\<phi> i))"
  proof (rule locally_finite_onI)
    fix p assume "p \<in> carrier"
    from locally_finite_onE[OF lfW this] obtain Nhd where Nhd: "p \<in> Nhd" "open Nhd" "finite {i \<in> N. W i \<inter> Nhd \<noteq> {}}" .
    show "\<exists>Nhd. p \<in> Nhd \<and> open Nhd \<and> finite {i \<in> A. support_on carrier (\<phi> i) \<inter> Nhd \<noteq> {}}"
      apply (rule exI[where x=Nhd])
      apply (auto simp: Nhd)
      apply (rule finite_subset[where B="a ` {i \<in> N. W i \<inter> Nhd \<noteq> {}}"])
      subgoal
        apply (auto simp: support_on_def \<phi>_def)
        apply (subst (asm) sum_nonneg_eq_0_iff)
          apply (auto simp: intro!: g_nonneg)
        using _ finite_W by (rule finite_subset) auto
      by (rule finite_imageI) fact
  qed
  then have "locally_finite_on carrier A (\<lambda>i. csupport_on carrier (\<phi> i))"
    unfolding csupport_on_def
    by (rule locally_finite_on_closure)
  ultimately show ?thesis ..
qed

text \<open>Given \<open>A \<subseteq> U \<subseteq> carrier\<close>, where \<open>A\<close> is closed and \<open>U\<close> is open, there exists
  a differentiable function \<open>\<psi>\<close> such that \<open>0 \<le> \<psi> \<le> 1\<close>, \<open>\<psi> = 1\<close> on \<open>A\<close>, and the
  support of \<open>\<psi>\<close> is contained in \<open>U\<close>.\<close>
lemma smooth_bump_functionE:
  assumes "closedin (top_of_set carrier) A"
    and "A \<subseteq> U" "U \<subseteq> carrier" "open U"
  obtains \<psi>::"'a \<Rightarrow> real" where
    "diff_fun k charts \<psi>"
    "\<And>x. x \<in> carrier \<Longrightarrow> 0 \<le> \<psi> x"
    "\<And>x. x \<in> carrier \<Longrightarrow> \<psi> x \<le> 1"
    "\<And>x. x \<in> A \<Longrightarrow> \<psi> x = 1"
    "csupport_on carrier \<psi> \<inter> carrier \<subseteq> U"
proof -
  define V where "V x = (if x = 0 then U else carrier - A)" for x::nat
  have "open (carrier - A)"
    using assms
    by (metis closedin_def open_Int open_carrier openin_open topspace_euclidean_subtopology)
  then have V: "carrier \<subseteq> (\<Union>i\<in>{0, 1}. V i)" "i \<in> {0, 1} \<Longrightarrow> open (V i)" for i
    using assms
    by (auto simp: V_def)
  obtain \<phi>::"nat \<Rightarrow> 'a \<Rightarrow> real" where \<phi>:
    "(\<And>i. i \<in> {0, 1} \<Longrightarrow> diff_fun k charts (\<phi> i))"
    "(\<And>i x. i \<in> {0, 1} \<Longrightarrow> x \<in> carrier \<Longrightarrow> 0 \<le> \<phi> i x)"
    "(\<And>i x. i \<in> {0, 1} \<Longrightarrow> x \<in> carrier \<Longrightarrow> \<phi> i x \<le> 1)"
    "(\<And>x. x \<in> carrier \<Longrightarrow> (\<Sum>i | i \<in> {0, 1} \<and> \<phi> i x \<noteq> 0. \<phi> i x) = 1)"
    "(\<And>i. i \<in> {0, 1} \<Longrightarrow> csupport_on carrier (\<phi> i) \<inter> carrier \<subseteq> V i)"
    "locally_finite_on carrier {0, 1} (\<lambda>i. csupport_on carrier (\<phi> i))"
    by (rule partitions_of_unityE[OF V]) auto
  from this(1-3,5)[of 0] this(6)
  have "diff_fun k charts (\<phi> 0)"
    "\<And>x. x \<in> carrier \<Longrightarrow> 0 \<le> \<phi> 0 x"
    "\<And>x. x \<in> carrier \<Longrightarrow> \<phi> 0 x \<le> 1"
    "csupport_on carrier (\<phi> 0) \<inter> carrier \<subseteq> U"
    by (auto simp: V_def)
  moreover have "\<phi> 0 x = 1" if "x \<in> A" for x
  proof -
    from that have "x \<in> carrier" using assms by auto
    from \<phi>(4)[OF this]
    have "1 = (\<Sum>i | i \<in> {0, 1} \<and> \<phi> i x \<noteq> 0. \<phi> i x)"
      by auto
    moreover have "{i. i \<in> {0, 1} \<and> \<phi> i x \<noteq> 0} =
      (if \<phi> 0 x \<noteq> 0 then {0} else {}) \<union> (if \<phi> 1 x \<noteq> 0 then {1} else {})"
      apply auto
      using neq0_conv by blast
    moreover have "x \<notin> V 1"
      using that
      by (auto simp: V_def)
    then have "\<phi> (Suc 0) x = 0"
      using \<phi>(5)[of 1] assms that
      by (auto simp: support_on_def csupport_on_def)
    ultimately show ?thesis by (auto split: if_splits)
  qed
  ultimately show ?thesis by (blast intro: that)
qed

definition "diff_fun_on A f \<longleftrightarrow>
  (\<exists>W. A \<subseteq> W \<and> W \<subseteq> carrier \<and> open W \<and>
    (\<exists>f'. diff_fun k (charts_submanifold W) f' \<and> (\<forall>x\<in>A. f x = f' x)))"

lemma diff_fun_onE:
  assumes "diff_fun_on A f"
  obtains W f' where
    "A \<subseteq> W" "W \<subseteq> carrier" "open W" "diff_fun k (charts_submanifold W) f'"
    "\<And>x. x \<in> A \<Longrightarrow> f x = f' x"
  using assms by (auto simp: diff_fun_on_def)

lemma diff_fun_onI:
  assumes  "A \<subseteq> W" "W \<subseteq> carrier" "open W" "diff_fun k (charts_submanifold W) f'"
    "\<And>x. x \<in> A \<Longrightarrow> f x = f' x"
  shows "diff_fun_on A f"
  using assms by (auto simp: diff_fun_on_def)

text \<open>Extension lemma:

  Given \<open>A \<subseteq> U \<subseteq> carrier\<close>, where \<open>A\<close> is closed and \<open>U\<close> is open, and a differentiable
  function \<open>f\<close> on \<open>A\<close>, there exists a differentiable function \<open>f'\<close> agreeing with \<open>f\<close>
  on \<open>A\<close>, and where the support of \<open>f'\<close> is contained in \<open>U\<close>.\<close>
lemma extension_lemmaE:
  fixes f::"'a \<Rightarrow> 'e::euclidean_space"
  assumes "closedin (top_of_set carrier) A"
  assumes "diff_fun_on A f" "A \<subseteq> U" "U \<subseteq> carrier" "open U"
  obtains f' where
    "diff_fun k charts f'"
    "\<And>x. x \<in> A \<Longrightarrow> f' x = f x"
    "csupport_on carrier f' \<inter> carrier \<subseteq> U"
proof -
  from diff_fun_onE[OF assms(2)]
  obtain W' f' where W': "A \<subseteq> W'" "W' \<subseteq> carrier" "open W'" "diff_fun k (charts_submanifold W') f'"
    "(\<And>x. x \<in> A \<Longrightarrow> f x = f' x)"
    by blast
  define W where "W = W' \<inter> U"

  interpret W': diff_fun k "charts_submanifold W'" f' using W' by auto
  have *: "open (W' \<inter> U)"
    using W' assms by auto
  with W'.diff_fun_submanifold[of W] 
  have "diff_fun k (W'.src.charts_submanifold (W' \<inter> U)) f'"
    by (auto simp: W_def)
  also have "W'.src.charts_submanifold (W' \<inter> U) = charts_submanifold (W' \<inter> U)"
    unfolding W'.src.charts_submanifold_def
    unfolding charts_submanifold_def
    using W' *
    by (auto simp: image_image restrict_chart_restrict_chart ac_simps)
  finally have "diff_fun k (charts_submanifold (W' \<inter> U)) f'" .
  with W' assms
  have W: "A \<subseteq> W" "W \<subseteq> carrier" "open W" "diff_fun k (charts_submanifold W) f'"
    "(\<And>x. x \<in> A \<Longrightarrow> f x = f' x)"
    by (auto simp: W_def)

  interpret submanifold _ _ W by unfold_locales fact
  interpret W: diff_fun k "(charts_submanifold W)" f' using W by auto
  have [simp]: "sub.carrier = W" using \<open>W \<subseteq> carrier\<close> by auto
  have "W \<subseteq> U" by (auto simp: W_def)

  from smooth_bump_functionE[OF assms(1) \<open>A \<subseteq> W\<close> \<open>W \<subseteq> carrier\<close> \<open>open W\<close>]
  obtain \<phi>::"'a\<Rightarrow>real" where \<phi>: "diff_fun k charts \<phi>"
    "(\<And>x. x \<in> carrier \<Longrightarrow> 0 \<le> \<phi> x)" "(\<And>x. x \<in> carrier \<Longrightarrow> \<phi> x \<le> 1)" "(\<And>x. x \<in> A \<Longrightarrow> \<phi> x = 1)"
    "csupport_on carrier \<phi> \<inter> carrier \<subseteq> W" by blast

  interpret \<phi>: diff_fun k charts \<phi> by fact

  define g where "g p = (if p \<in> W then \<phi> p *\<^sub>R f' p else 0)" for p

  thm sub.diff_fun_scaleR
  have "diff_fun k charts g"
  proof (rule manifold_eucl.diff_open_Un, unfold diff_fun_def[symmetric])
    have "diff_fun k (charts_submanifold W) (\<lambda>p. \<phi> p *\<^sub>R f' p)"
      by (auto intro!: sub.diff_fun_scaleR \<phi>.diff_fun_submanifold W)
    then show "diff_fun k (charts_submanifold W) g"
      by (rule diff_fun.diff_fun_cong) (auto simp: g_def)
    interpret C: submanifold _ _ "carrier - csupport_on carrier \<phi>"
      by unfold_locales auto

    have sub_carrier[simp]: "C.sub.carrier = carrier - csupport_on carrier \<phi>"
      by auto

    have "diff_fun k (charts_submanifold (carrier - csupport_on carrier \<phi>)) 0"
      by (rule C.sub.diff_fun_zero)
    then show "diff_fun k (charts_submanifold (carrier - csupport_on carrier \<phi>)) g"
      by (rule diff_fun.diff_fun_cong) (auto simp: g_def not_in_csupportD)
    show "open W" by fact
    show "open (carrier - csupport_on carrier \<phi>)"
      by (auto)
    show "carrier \<subseteq> W \<union> (carrier - csupport_on carrier \<phi>)"
      using \<phi>
      by auto
  qed
  moreover have "\<And>x. x \<in> A \<Longrightarrow> g x = f x"
    using \<open>A \<subseteq> W\<close>
    by (auto simp: g_def \<phi> W')
  moreover have "csupport_on carrier g \<inter> carrier  \<subseteq> U"
  proof -
    have "csupport_on carrier g \<subseteq> csupport_on carrier \<phi>"
      by (rule csupport_on_mono) (auto simp: g_def[abs_def] split: if_splits)
    also have "\<dots>  \<inter> carrier \<subseteq> U"
      using \<phi>(5) \<open>W \<subseteq> U\<close> \<open>W \<subseteq> carrier\<close> \<open>U \<subseteq> carrier\<close>
      by auto
    finally show ?thesis by auto
  qed
  ultimately show ?thesis ..
qed

end

end
