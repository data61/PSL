section \<open>Topology for Floating Point Numbers\<close>
theory Float_Topology
  imports
    "HOL-Analysis.Analysis"
    "HOL-Library.Float"
begin

text \<open>
This topology is totally disconnected and not complete, in which sense is it useful?
Perhaps for convergence of intervals?\<close>

unbundle float.lifting

instantiation float :: dist
begin

lift_definition dist_float :: "float \<Rightarrow> float \<Rightarrow> real" is dist .

lemma dist_float_eq_0_iff: "(dist x y = 0) = (x = y)" for x y::float
  by transfer simp

lemma dist_float_triangle2: "dist x y \<le> dist x z + dist y z" for x y z::float
  by transfer (rule dist_triangle2)

instance ..
end

instantiation float :: uniformity
begin

definition uniformity_float :: "(float \<times> float) filter"
  where "uniformity_float = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})"

instance ..
end

lemma float_dense_in_real:
  fixes x :: real
  assumes "x < y"
  shows "\<exists>r\<in>float. x < r \<and> r < y"
proof -
  from \<open>x < y\<close> have "0 < y - x" by simp
  with reals_Archimedean obtain q' :: nat where q': "inverse (real q') < y - x" and "0 < q'"
    by blast
  define q::nat where "q \<equiv> 2 ^ nat \<bar>bitlen q'\<bar>"
  from bitlen_bounds[of q'] \<open>0 < q'\<close> have "q' < q"
    by (auto simp: q_def)
  then have "inverse q < inverse q'"
    using \<open>0 < q'\<close>
    by (auto simp: divide_simps)
  with \<open>q' < q\<close> q' have q: "inverse (real q) < y - x" and "0 < q"
    by (auto simp: split: if_splits)
  define p where "p = \<lceil>y * real q\<rceil> - 1"
  define r where "r = of_int p / real q"
  from q have "x < y - inverse (real q)"
    by simp
  also from \<open>0 < q\<close> have "y - inverse (real q) \<le> r"
    by (simp add: r_def p_def le_divide_eq left_diff_distrib)
  finally have "x < r" .
  moreover from \<open>0 < q\<close> have "r < y"
    by (simp add: r_def p_def divide_less_eq diff_less_eq less_ceiling_iff [symmetric])
  moreover have "r \<in> float"
    by (simp add: r_def q_def)
  ultimately show ?thesis by blast
qed

lemma real_of_float_dense:
  fixes x y :: real
  assumes "x < y"
  shows "\<exists>q :: float. x < real_of_float q \<and> real_of_float q < y"
  using float_dense_in_real [OF \<open>x < y\<close>]
  by (auto elim: real_of_float_cases)

instantiation float :: linorder_topology
begin

definition open_float::"float set \<Rightarrow> bool" where
  "open_float S = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

instance
proof (standard, intro ext iffI)
  fix U::"float set"
  assume "generate_topology (range lessThan \<union> range greaterThan) U"
  then show "open U"
    unfolding open_float_def uniformity_float_def
  proof (induction U)
    case UNIV
    then show ?case by (auto intro!: zero_less_one)
  next
    case (Int a b)
    show ?case
    proof safe
      fix x assume "x \<in> a" "x \<in> b"
      with Int(3,4) obtain e1 e2
        where "dist (y) (x) < e1 \<Longrightarrow> y \<in> a"
          and "dist (y) (x) < e2 \<Longrightarrow> y \<in> b"
          and "0 < e1" "0 < e2"
        for y
        by (auto dest!: bspec)
      then show "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> a \<inter> b"
        by (auto intro!: exI[where x="min e1 e2"])
    qed
  next
    case (UN K)
    show ?case
    proof safe
      fix x X assume x: "x \<in> X" and X: "X \<in> K"
      from UN[OF X] x obtain e where
        "dist (y) (x) < e \<Longrightarrow> y \<in> X" "e > 0" for y
        by auto
      then show "\<exists>e>0. \<forall>y. dist (real_of_float y) (real_of_float x) < e \<longrightarrow> y \<in> \<Union>K"
        using x X
        by (auto intro!: exI[where x=e])
    qed
  next
    case (Basis s)
    then show ?case
    proof safe
      fix x u::float
      assume "x < u"
      then show "\<exists>e>0. \<forall>y. dist (real_of_float y) (real_of_float x) < e \<longrightarrow> y \<in> {..<u}"
        by (force simp add: eventually_principal dist_float_def
            dist_real_def abs_real_def
            intro!: exI[where x="(u - x)/2"])
    next
      fix x l::float
      assume "l < x"
      then show "\<exists>e>0. \<forall>y. dist (real_of_float y) (real_of_float x) < e \<longrightarrow> y \<in> {l<..}"
        by (force simp add: eventually_principal dist_float_def
            dist_real_def abs_real_def
            intro!: exI[where x="(x - l)/2"])
    qed
  qed
next
  fix U::"float set"
  assume "open U"
  then obtain e where e:
    "x \<in> U \<Longrightarrow> e x > 0"
    "x \<in> U \<Longrightarrow> dist ( y) ( x) < e x \<Longrightarrow> y \<in> U" for x y
    unfolding open_float_def uniformity_float_def
    by metis
  {
    fix x
    assume x: "x \<in> U"
    obtain e' where e': "e' > 0" "real_of_float e' < e x"
      using real_of_float_dense[of 0 "e x"]
      using e(1)[OF x]
      by auto
    then have "dist (y) ( x) < e' \<Longrightarrow> y \<in> U" for y
      by (intro e[OF x]) auto
    then have "\<exists>e'>0. \<forall>y. dist (y) ( x) < real_of_float e' \<longrightarrow> y \<in> U"
      using e'
      by auto
  } then
  obtain e' where e':
    "x \<in> U \<Longrightarrow> 0 < e' x"
    "x \<in> U \<Longrightarrow> dist y x < real_of_float (e' x) \<Longrightarrow> y \<in> U" for x y
    by metis
  then have "U = (\<Union>x\<in>U. greaterThan (x - e' x) \<inter> lessThan (x + e' x))"
    by (auto simp: dist_float_def dist_commute dist_real_def)
  also have "generate_topology (range lessThan \<union> range greaterThan) \<dots>"
    by (intro generate_topology_Union generate_topology.Int generate_topology.Basis) auto
  finally show "generate_topology (range lessThan \<union> range greaterThan) U" .
qed

end

instance float :: metric_space
proof standard
  fix U::"float set"
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    unfolding open_float_def open_dist uniformity_float_def uniformity_real_def
  proof safe
    fix x
    assume "\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist (real_of_float y) (real_of_float x) < e \<longrightarrow> y \<in> U" "x \<in> U"
    then obtain e where "e > 0" "dist (y) (x) < e \<Longrightarrow> y \<in> U" for y
      by auto
    then show "\<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U"
      by (intro eventually_INF1[where i=e])
        (auto simp: eventually_principal dist_commute dist_float_def)
  next
    fix u
    assume "\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U"
      "u \<in> U"
    from this obtain E where E: "E \<subseteq> {0<..}" "finite E"
      "\<forall>(x', y)\<in>\<Inter>x\<in>E. {(y', y). dist y' y < x}. x' = u \<longrightarrow> y \<in> U"
      by (subst (asm) eventually_INF) (auto simp: INF_principal_finite eventually_principal)
    then show "\<exists>e>0. \<forall>y. dist (real_of_float y) (real_of_float u) < e \<longrightarrow> y \<in> U"
      by (intro exI[where x="if E = {} then 1 else Min E"])
        (auto simp: dist_commute dist_float_def)
  qed
qed (use dist_float_eq_0_iff dist_float_triangle2 in
    \<open>auto simp add: uniformity_float_def dist_float_def\<close>)

instance float::topological_ab_group_add
proof
  fix a b::float
  show "((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)"
  proof (rule tendstoI)
    fix e::real
    assume "e > 0"
    have 1: "(fst \<longlongrightarrow> a) (nhds a \<times>\<^sub>F nhds b)"
      and 2: "(snd \<longlongrightarrow> b) (nhds a \<times>\<^sub>F nhds b)"
      by (auto intro!: tendsto_eq_intros filterlim_ident simp: nhds_prod[symmetric])
    have "\<forall>\<^sub>F x in nhds a \<times>\<^sub>F nhds b. dist (fst x) (a) < e/2"
      by (rule tendstoD[OF 1]) (use \<open>e > 0\<close> in auto)
    moreover have "\<forall>\<^sub>F x in nhds a \<times>\<^sub>F nhds b. dist (snd x) (b) < e/2"
      by (rule tendstoD[OF 2]) (use \<open>e > 0\<close> in auto)
    ultimately show "\<forall>\<^sub>F x in nhds a \<times>\<^sub>F nhds b. dist (fst x + snd x) (a + b) < e"
    proof eventually_elim
      case (elim x)
      then show ?case
        by (auto simp: dist_float_def) norm
    qed
  qed
  show "(uminus \<longlongrightarrow> - a) (nhds a)"
    using filterlim_ident[of "nhds a"]
    by (auto intro!: tendstoI dest!: tendstoD simp: dist_float_def dist_minus)
qed

lifting_update float.lifting
lifting_forget float.lifting

end
