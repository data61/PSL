section \<open> Sparse Grids \<close>

theory Grid
imports Grid_Point
begin

subsection "Vectors"

type_synonym vector = "grid_point \<Rightarrow> real"

definition null_vector :: "vector"
where "null_vector \<equiv> \<lambda> p. 0"

definition sum_vector :: "vector \<Rightarrow> vector \<Rightarrow> vector"
where "sum_vector \<alpha> \<beta> \<equiv> \<lambda> p. \<alpha> p + \<beta> p"

subsection \<open> Inductive enumeration of all grid points \<close>

inductive_set
  grid :: "grid_point \<Rightarrow> nat set \<Rightarrow> grid_point set"
  for b :: "grid_point" and ds :: "nat set"
where
    Start[intro!]: "b \<in> grid b ds"
  | Child[intro!]: "\<lbrakk> p \<in> grid b ds ; d \<in> ds \<rbrakk> \<Longrightarrow> child p dir d \<in> grid b ds"

lemma grid_length[simp]: "p' \<in> grid p ds \<Longrightarrow> length p' = length p"
  by (erule grid.induct, auto)

lemma grid_union_dims: "\<lbrakk> ds \<subseteq> ds' ; p \<in> grid b ds \<rbrakk> \<Longrightarrow> p \<in> grid b ds'"
  by (erule grid.induct, auto)

lemma grid_transitive: "\<lbrakk> a \<in> grid b ds ; b \<in> grid c ds' ; ds' \<subseteq> ds'' ; ds \<subseteq> ds'' \<rbrakk> \<Longrightarrow> a \<in> grid c ds''"
  by (erule grid.induct, auto simp add: grid_union_dims)

lemma grid_child[intro?]: assumes "d \<in> ds" and p_grid: "p \<in> grid (child b dir d) ds"
  shows "p \<in> grid b ds"
  using \<open>d \<in> ds\<close> grid_transitive[OF p_grid] by auto

lemma grid_single_level[simp]: assumes "p \<in> grid b ds" and "d < length b"
  shows "lv b d \<le> lv p d"
  using assms
proof induct
  case (Child p' d' dir)
  thus ?case by (cases "d' = d", auto simp add: child_def ix_def lv_def)
qed auto

lemma grid_child_level:
  assumes "d < length b"
  and p_grid: "p \<in> grid (child b dir d) ds"
  shows "lv b d < lv p d"
proof -
  have "lv b d < lv (child b dir d) d" using child_lv[OF \<open>d < length b\<close>] by auto
  also have "\<dots> \<le> lv p d" using p_grid assms by (intro grid_single_level) auto
  finally show ?thesis .
qed

lemma child_out: "length p \<le> d \<Longrightarrow> child p dir d = p"
  unfolding child_def by auto

lemma grid_dim_remove:
  assumes inset: "p \<in> grid b ({d} \<union> ds)"
  and eq: "d < length b \<Longrightarrow> p ! d = b ! d"
  shows "p \<in> grid b ds"
  using inset eq
proof induct
  case (Child p' d' dir)
  show ?case
  proof (cases "d' \<ge> length p'")
    case True with child_out[OF this]
    show ?thesis using Child by auto
  next
    case False hence "d' < length p'" by simp
    show ?thesis
    proof (cases "d' = d")
      case True
      hence "lv b d \<le> lv p' d" and "lv p' d < lv (child p' dir d) d"
        using child_single_level Child \<open>d' < length p'\<close> by auto
      hence False using Child and \<open>d' = d\<close> and lv_def and \<open>\<not> d' \<ge> length p'\<close> by auto
      thus ?thesis ..
    next
      case False
      hence "d' \<in> ds" using Child by auto
      moreover have "d < length b \<Longrightarrow> p' ! d = b ! d"
      proof -
        assume "d < length b"
        hence "d < length p'" using Child by auto
        hence "child p' dir d' ! d = p' ! d" using child_invariant and False by auto
        thus ?thesis using Child and \<open>d < length b\<close> by auto
      qed
      hence "p' \<in> grid b ds" using Child by auto
      ultimately show ?thesis using grid.Child by auto
    qed
  qed
qed auto

lemma gridgen_dim_restrict:
  assumes inset: "p \<in> grid b (ds' \<union> ds)"
  and eq: "\<forall> d \<in> ds'. d \<ge> length b"
  shows "p \<in> grid b ds"
  using inset eq
proof induct
  case (Child p' d dir)
  thus ?case
  proof (cases "d \<in> ds")
    case False thus ?thesis using Child and child_def by auto
  qed auto
qed auto

lemma grid_dim_remove_outer: "grid b ds = grid b {d \<in> ds. d < length b}"
proof
  have "{d \<in> ds. d < length b} \<subseteq> ds" by auto
  from grid_union_dims[OF this]
  show "grid b {d \<in> ds. d < length b} \<subseteq> grid b ds" by auto

  have "ds = (ds - {d \<in> ds. d < length b}) \<union> {d \<in> ds. d < length b}" by auto
  moreover
  have "grid b ((ds - {d \<in> ds. d < length b}) \<union> {d \<in> ds. d < length b}) \<subseteq> grid b {d \<in> ds. d < length b}"
  proof
    fix p
    assume "p \<in> grid b (ds - {d \<in> ds. d < length b} \<union> {d \<in> ds. d < length b})"
    moreover have "\<forall> d \<in> (ds - {d \<in> ds. d < length b}). d \<ge> length b" by auto
    ultimately show "p \<in> grid b {d \<in> ds. d < length b}" by (rule gridgen_dim_restrict)
  qed
  ultimately show "grid b ds \<subseteq> grid b {d \<in> ds. d < length b}" by auto
qed

lemma grid_level[intro]: assumes "p \<in> grid b ds" shows "level b \<le> level p"
proof -
  have *: "length p = length b" using grid_length assms by auto
  { fix i assume "i \<in> {0 ..< length p}"
    hence "lv b i \<le> lv p i" using \<open>p \<in> grid b ds\<close> and grid_single_level * by auto
  } thus ?thesis unfolding level_def * by (auto intro!: sum_mono)
qed
lemma grid_empty_ds[simp]: "grid b {} = { b }"
proof -
  have "!! z. z \<in> grid b {} \<Longrightarrow> z = b"
    by (erule grid.induct, auto)
  thus ?thesis by auto
qed
lemma grid_Start: assumes inset: "p \<in> grid b ds" and eq: "level p = level b" shows "p = b"
  using inset eq
proof induct
  case (Child p d dir)
  show ?case
  proof (cases "d < length b")
    case True
    from Child
    have "level p \<ge> level b" by auto
    moreover
    have "level p \<le> level (child p dir d)" by (rule child_level_gt)
    hence "level p \<le> level b" using Child by auto
    ultimately have "level p = level b" by auto
    hence "p = b " using Child(2) by auto
    with Child(4) have "level (child b dir d) = level b" by auto
    moreover have "level (child b dir d) \<noteq>  level b" using child_level and \<open>d < length b\<close> by auto
    ultimately show ?thesis by auto
  next
    case False
    with Child have "length p = length b" by auto
    with False have "child p dir d = p" using child_def by auto
    moreover with Child have "level p = level b" by auto
    with Child(2) have "p = b" by auto
    ultimately show ?thesis by auto
  qed
qed auto
lemma grid_estimate:
  assumes "d < length b" and p_grid: "p \<in> grid b ds"
  shows "ix p d < (ix b d + 1) * 2^(lv p d - lv b d) \<and> ix p d > (ix b d - 1) * 2^(lv p d - lv b d)"
  using p_grid
proof induct
  case (Child p d' dir)
  show ?case
  proof (cases "d = d'")
    case False with Child show ?thesis unfolding child_def lv_def ix_def by auto
  next
    case True with child_estimate_child and Child and \<open>d < length b\<close>
    show ?thesis using grid_single_level by auto
  qed
qed auto
lemma grid_odd: assumes "d < length b" and p_diff: "p ! d \<noteq> b ! d" and p_grid: "p \<in> grid b ds"
  shows "odd (ix p d)"
  using p_grid and p_diff
proof induct
  case (Child p d' dir)
  show ?case
  proof (cases "d = d'")
    case True with child_odd and \<open>d < length b\<close> and Child show ?thesis by auto
  next
    case False with Child and \<open>d < length b\<close> show ?thesis using child_def and ix_def and lv_def by auto
  qed
qed auto
lemma grid_invariant: assumes "d < length b" and "d \<notin> ds" and p_grid: "p \<in> grid b ds"
  shows "p ! d = b ! d"
  using p_grid
proof (induct)
  case (Child p d' dir) hence "d' \<noteq> d" using \<open>d \<notin> ds\<close> by auto
  thus ?case using child_def and Child by auto
qed auto
lemma grid_part: assumes "d < length b" and p_valid: "p \<in> grid b {d}" and p'_valid: "p' \<in> grid b {d}"
  and level: "lv p' d \<ge> lv p d"
  and right: "ix p' d \<le> (ix p d + 1) * 2^(lv p' d - lv p d)" (is "?right p p' d")
  and left: "ix p' d \<ge> (ix p d - 1) * 2^(lv p' d - lv p d)" (is "?left p p' d")
  shows "p' \<in> grid p {d}"
  using p'_valid left right level and p_valid
proof induct
  case (Child p' d' dir)
  hence "d = d'" by auto
  let ?child = "child p' dir d'"

  show ?case
  proof (cases "lv p d = lv ?child d")
    case False
    moreover have "lv ?child d = lv p' d + 1" using child_lv and \<open>d < length b\<close> and Child and \<open>d = d'\<close> by auto
    ultimately have "lv p d < lv p' d + 1" using Child by auto
    hence lv: "Suc (lv p' d) - lv p d = Suc (lv p' d - lv p d)" by auto

    have "?left p p' d \<and> ?right p p' d"
    proof (cases dir)
      case left
      with Child have "2 * ix p' d - 1 \<le> (ix p d + 1) * 2^(Suc (lv p' d) - lv p d)"
        using \<open>d = d'\<close> and \<open>d < length b\<close> by (auto simp add: child_def ix_def lv_def)
      also have "\<dots> = 2 * (ix p d + 1) * 2^(lv p' d - lv p d)" using lv by auto
      finally have "2 * ix p' d - 2 < 2 * (ix p d + 1) * 2^(lv p' d - lv p d)" by auto
      also have "\<dots> = 2 * ((ix p d + 1) * 2^(lv p' d - lv p d))" by auto
      finally have left_r: "ix p' d \<le> (ix p d + 1) * 2^(lv p' d - lv p d)" by auto

      have "2 * ((ix p d - 1) * 2^(lv p' d - lv p d)) = 2 * (ix p d - 1) * 2^(lv p' d - lv p d)" by auto
      also have "\<dots> = (ix p d - 1) * 2^(Suc (lv p' d) - lv p d)" using lv by auto
      also have "\<dots> \<le> 2 * ix p' d - 1"
        using left and Child and \<open>d = d'\<close> and \<open>d < length b\<close> by (auto simp add: child_def ix_def lv_def)
      finally have right_r: "((ix p d - 1) * 2^(lv p' d - lv p d)) \<le> ix p' d" by auto

      show ?thesis using left_r and right_r by auto
    next
      case right
      with Child have "2 * ix p' d + 1 \<le> (ix p d + 1) * 2^(Suc (lv p' d) - lv p d)"
        using \<open>d = d'\<close> and \<open>d < length b\<close> by (auto simp add: child_def ix_def lv_def)
      also have "\<dots> = 2 * (ix p d + 1) * 2^(lv p' d - lv p d)" using lv by auto
      finally have "2 * ix p' d < 2 * (ix p d + 1) * 2^(lv p' d - lv p d)" by auto
      also have "\<dots> = 2 * ((ix p d + 1) * 2^(lv p' d - lv p d))" by auto
      finally have left_r: "ix p' d \<le> (ix p d + 1) * 2^(lv p' d - lv p d)" by auto

      have "2 * ((ix p d - 1) * 2^(lv p' d - lv p d)) = 2 * (ix p d - 1) * 2^(lv p' d - lv p d)" by auto
      also have "\<dots> = (ix p d - 1) * 2^(Suc (lv p' d) - lv p d)" using lv by auto
      also have "\<dots> \<le> 2 * ix p' d + 1"
        using right and Child and \<open>d = d'\<close> and \<open>d < length b\<close> by (auto simp add: child_def ix_def lv_def)
      also have "\<dots> < 2 * (ix p' d + 1)" by auto
      finally have right_r: "((ix p d - 1) * 2^(lv p' d - lv p d)) \<le> ix p' d" by auto

      show ?thesis using left_r and right_r by auto
    qed
    with Child and lv have "p' \<in> grid p {d}" by auto
    thus ?thesis using \<open>d = d'\<close> by auto
  next
    case True
    moreover with Child have "?left p ?child d \<and> ?right p ?child d" by auto
    ultimately have range: "ix p d - 1 \<le> ix ?child d \<and> ix ?child d \<le> ix p d + 1" by auto

    have "p ! d \<noteq> b ! d"
    proof (rule ccontr)
      assume "\<not> (p ! d \<noteq> b ! d)"
      with \<open>lv p d = lv ?child d\<close> have "lv b d = lv ?child d" by (auto simp add: lv_def)
      hence "lv b d = lv p' d + 1" using \<open>d = d'\<close> and Child and \<open>d < length b\<close> and child_lv by auto
      moreover have "lv b d \<le> lv p' d" using \<open>d = d'\<close> and Child and \<open>d < length b\<close> and grid_single_level by auto
      ultimately show False by auto
    qed
    hence "odd (ix p d)" using grid_odd and \<open>p \<in> grid b {d}\<close> and \<open>d < length b\<close> by auto
    hence "\<not> odd (ix p d + 1)" and "\<not> odd (ix p d - 1)" by auto

    have "d < length p'" using \<open>p' \<in> grid b {d}\<close> and \<open>d < length b\<close> by auto
    hence odd_child: "odd (ix ?child d)" using child_odd and \<open>d = d'\<close> by auto

    have "ix p d - 1 \<noteq> ix ?child d"
    proof (rule ccontr)
      assume "\<not> (ix p d - 1 \<noteq> ix ?child d)"
      hence "odd (ix p d - 1)" using odd_child by auto
      thus False using \<open>\<not> odd (ix p d - 1)\<close> by auto
    qed
    moreover
    have "ix p d + 1 \<noteq> ix ?child d"
    proof (rule ccontr)
      assume "\<not> (ix p d + 1 \<noteq> ix ?child d)"
      hence "odd (ix p d + 1)" using odd_child by auto
      thus False using \<open>\<not> odd (ix p d + 1)\<close> by auto
    qed
    ultimately have "ix p d = ix ?child d" using range by auto
    with True have d_eq: "p ! d = (?child) ! d" by (auto simp add: prod_eqI ix_def lv_def)

    have "length p = length ?child" using \<open>p \<in> grid b {d}\<close> and \<open>p' \<in> grid b {d}\<close> by auto
    moreover have "p ! d'' = ?child ! d''" if "d'' < length p" for d''
    proof -
      have "d'' < length b" using that \<open>p \<in> grid b {d}\<close> by auto
      show "p ! d'' = ?child ! d''"
      proof (cases "d = d''")
        case True with d_eq show ?thesis by auto
      next
        case False hence "d'' \<notin> {d}" by auto
        from \<open>d'' < length b\<close> and this and \<open>p \<in> grid b {d}\<close>
        have "p ! d'' = b ! d''" by (rule grid_invariant)
        also have "\<dots> = p' ! d''" using \<open>d'' < length b\<close> and \<open>d'' \<notin> {d}\<close> and \<open>p' \<in> grid b {d}\<close>
          by (rule grid_invariant[symmetric])
        also have "\<dots> = ?child ! d''"
        proof -
          have "d'' < length p'" using \<open>d'' < length b\<close> and \<open>p' \<in> grid b {d}\<close> by auto
          hence "?child ! d'' = p' ! d''" using child_invariant and \<open>d \<noteq> d''\<close> and \<open>d = d'\<close> by auto
          thus ?thesis by auto
        qed
        finally show ?thesis .
      qed
    qed
    ultimately have "p = ?child" by (rule nth_equalityI)
    thus "?child \<in> grid p {d}" by auto
  qed
next
  case Start
  moreover hence "lv b d \<le> lv p d" using grid_single_level and \<open>d < length b\<close> by auto
  ultimately have "lv b d = lv p d" by auto

  have "level p = level b"
  proof -
    { fix d'
      assume "d' < length b"
      have "lv b d' = lv p d'"
      proof (cases "d = d'")
        case True with \<open>lv b d = lv p d\<close> show ?thesis by auto
      next
        case False hence "d' \<notin> {d}" by auto
        from \<open>d' < length b\<close> and this and \<open>p \<in> grid b {d}\<close>
        have "p ! d' = b ! d'" by (rule grid_invariant)
        thus ?thesis by (auto simp add: lv_def)
      qed }
    moreover have "length b = length p" using \<open>p \<in> grid b {d}\<close> by auto
    ultimately show ?thesis by (rule level_all_eq)
  qed
  hence "p = b" using grid_Start and \<open>p \<in> grid b {d}\<close> by auto
  thus ?case by auto
qed
lemma grid_disjunct: assumes "d < length p"
  shows "grid (child p left d) ds \<inter> grid (child p right d) ds = {}"
  (is "grid ?l ds \<inter> grid ?r ds = {}")
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> grid ?l ds \<inter> grid ?r ds"
  hence "ix x d < (ix ?l d + 1) * 2^(lv x d - lv ?l d)"
    and "ix x d > (ix ?r d - 1) * 2^(lv x d - lv ?r d)"
    using grid_estimate \<open>d < length p\<close> by auto
  thus "x \<in> {}" using \<open>d < length p\<close> and child_lv and child_ix by auto
qed auto

lemma grid_level_eq: assumes eq: "\<forall> d \<in> ds. lv p d = lv b d" and grid: "p \<in> grid b ds"
  shows "level p = level b"
proof (rule level_all_eq)
  { fix i assume "i < length b"
    show "lv b i = lv p i"
    proof (cases "i \<in> ds")
      case True with eq show ?thesis by auto
    next case False with \<open>i < length b\<close> and grid show ?thesis
        using lv_def ix_def grid_invariant by auto
    qed }
  show "length b = length p" using grid by auto
qed

lemma grid_partition:
  "grid p {d} = {p} \<union> grid (child p left d) {d} \<union> grid (child p right d) {d}"
  (is "_ = _ \<union> grid ?l {d} \<union> grid ?r {d}")
proof -
  have "!! x. \<lbrakk> x \<in> grid p {d} ; x \<noteq> p ; x \<notin> grid ?r {d} \<rbrakk> \<Longrightarrow> x \<in> grid ?l {d}"
  proof (cases "d < length p")
    case True
    fix x

    let "?nr_r p" = "ix x d > (ix p d + 1) * 2 ^ (lv x d - lv p d)"
    let "?nr_l p" = "(ix p d - 1) * 2 ^ (lv x d - lv p d) > ix x d"

    have ix_r_eq: "ix ?r d = 2 * ix p d + 1" using \<open>d < length p\<close> and child_ix by auto
    have lv_r_eq: "lv ?r d = lv p d + 1" using \<open>d < length p\<close> and child_lv by auto

    have ix_l_eq: "ix ?l d = 2 * ix p d - 1" using \<open>d < length p\<close> and child_ix by auto
    have lv_l_eq: "lv ?l d = lv p d + 1" using \<open>d < length p\<close> and child_lv by auto

    assume "x \<in> grid p {d}" and "x \<noteq> p" and "x \<notin> grid ?r {d}"
    hence "lv p d \<le> lv x d" using grid_single_level and \<open>d < length p\<close> by auto
    moreover have "lv p d \<noteq> lv x d"
    proof (rule ccontr)
      assume "\<not> lv p d \<noteq> lv x d"
      hence "level x = level p" using \<open>x \<in> grid p {d}\<close> and grid_level_eq[where ds="{d}"] by auto
      hence "x = p" using grid_Start and \<open>x \<in> grid p {d}\<close> by auto
      thus False using \<open>x \<noteq> p\<close> by auto
    qed
    ultimately have "lv p d < lv x d" by auto
    hence "lv ?r d \<le> lv x d" and "?r \<in> grid p {d}" using child_lv and \<open>d < length p\<close> by auto
    with \<open>d < length p\<close> and \<open>x \<in> grid p {d}\<close>
    have r_range: "\<not> ?nr_r ?r \<and> \<not> ?nr_l ?r \<Longrightarrow> x \<in> grid ?r {d}"
      using grid_part[where p="?r" and p'=x and b=p and d=d] by auto
    have "x \<notin> grid ?r {d} \<Longrightarrow> ?nr_l ?r \<or> ?nr_r ?r" by (rule ccontr, auto simp add: r_range)
    hence "?nr_l ?r \<or> ?nr_r ?r" using \<open>x \<notin> grid ?r {d}\<close> by auto

    have gt0: "lv x d - lv p d > 0" using \<open>lv p d < lv x d\<close> by auto

    have ix_shift: "ix ?r d = ix ?l d + 2" and lv_lr: "lv ?r d = lv ?l d" and right1: "!! x :: int. x + 2 - 1 = x + 1"
      using \<open>d < length p\<close> and child_ix and child_lv by auto

    have "lv x d - lv p d = Suc (lv x d - (lv p d + 1))"
      using gt0 by auto
    hence lv_shift: "!! y :: int. y * 2 ^ (lv x d - lv p d) = y * 2 * 2 ^ (lv x d - (lv p d + 1))"
      by auto

    have "ix x d < (ix p d + 1) * 2 ^ (lv x d - lv p d)"
      using \<open>x \<in> grid p {d}\<close> grid_estimate and \<open>d < length p\<close> by auto
    also have "\<dots> = (ix ?r d + 1) * 2 ^ (lv x d - lv ?r d)"
      using \<open>lv p d < lv x d\<close> and ix_r_eq and lv_r_eq lv_shift[where y="ix p d + 1"] by auto
    finally have "?nr_l ?r" using \<open>?nr_l ?r \<or> ?nr_r ?r\<close> by auto
    hence r_bound: "(ix ?l d + 1) * 2 ^ (lv x d - lv ?l d) > ix x d"
      unfolding ix_shift lv_lr using right1 by auto

    have "(ix ?l d - 1) * 2 ^ (lv x d - lv ?l d) = (ix p d - 1) * 2 * 2 ^ (lv x d - (lv p d + 1))"
      unfolding ix_l_eq lv_l_eq by auto
    also have "\<dots> = (ix p d - 1) * 2 ^ (lv x d - lv p d)"
      using lv_shift[where y="ix p d - 1"] by auto
    also have " \<dots> < ix x d"
      using \<open>x \<in> grid p {d}\<close> grid_estimate and \<open>d < length p\<close> by auto
    finally have l_bound: "(ix ?l d - 1) * 2 ^ (lv x d - lv ?l d) < ix x d" .

    from l_bound r_bound \<open>d < length p\<close> and \<open>x \<in> grid p {d}\<close> \<open>lv ?r d \<le> lv x d\<close> and lv_lr
    show "x \<in> grid ?l {d}" using grid_part[where p="?l" and p'=x and d=d] by auto
  qed (auto simp add: child_def)
  thus ?thesis by (auto intro: grid_child)
qed
lemma grid_change_dim: assumes grid: "p \<in> grid b ds"
  shows "p[d := X] \<in> grid (b[d := X]) ds"
  using grid
proof induct
  case (Child p d' dir)
  show ?case
  proof (cases "d \<noteq> d'")
    case True
    have "(child p dir d')[d := X] = child (p[d := X]) dir d'"
      unfolding child_def and ix_def and lv_def
      unfolding list_update_swap[OF \<open>d \<noteq> d'\<close>] and nth_list_update_neq[OF \<open>d \<noteq> d'\<close>] ..
    thus ?thesis using Child by auto
  next
    case False hence "d = d'" by auto
    with Child show ?thesis unfolding child_def \<open>d = d'\<close> list_update_overwrite by auto
  qed
qed auto
lemma grid_change_dim_child: assumes grid: "p \<in> grid b ds" and "d \<notin> ds"
  shows "child p dir d \<in> grid (child b dir d) ds"
proof (cases "d < length b")
  case True thus ?thesis using grid_change_dim[OF grid]
    unfolding child_def lv_def ix_def grid_invariant[OF True \<open>d \<notin> ds\<close> grid] by auto
next
  case False hence "length b \<le> d" and "length p \<le> d" using grid by auto
  thus ?thesis unfolding child_def using list_update_beyond assms by auto
qed
lemma grid_split: assumes grid: "p \<in> grid b (ds' \<union> ds)" shows "\<exists> x \<in> grid b ds. p \<in> grid x ds'"
  using grid
proof induct
  case (Child p d dir)
  show ?case
  proof (cases "d \<in> ds'")
    case True with Child show ?thesis by auto
  next
    case False
    hence "d \<in> ds" using Child by auto
    obtain x where "x \<in> grid b ds" and "p \<in> grid x ds'" using Child by auto
    hence "child x dir d \<in> grid b ds" using \<open>d \<in> ds\<close> by auto
    moreover have "child p dir d \<in> grid (child x dir d) ds'"
      using \<open>p \<in> grid x ds'\<close> False and grid_change_dim_child by auto
    ultimately show ?thesis by auto
  qed
qed auto
lemma grid_union_eq: "(\<Union> p \<in> grid b ds. grid p ds') = grid b (ds' \<union> ds)"
  using grid_split and grid_transitive[where ds''="ds' \<union> ds" and ds=ds' and ds'=ds, OF _ _ Un_upper2 Un_upper1] by auto
lemma grid_onedim_split:
  "grid b (ds \<union> {d}) = grid b ds \<union> grid (child b left d) (ds \<union> {d}) \<union> grid (child b right d) (ds \<union> {d})"
  (is "_ = ?g \<union> ?l (ds \<union> {d}) \<union> ?r (ds \<union> {d})")
proof -
  have "?g \<union> ?l (ds \<union> {d}) \<union> ?r (ds \<union> {d}) = ?g \<union> (\<Union> p \<in> ?l {d}. grid p ds) \<union> (\<Union> p \<in> ?r {d}. grid p ds)"
    unfolding grid_union_eq ..
  also have "\<dots> = (\<Union> p \<in> ({b} \<union> ?l {d} \<union> ?r {d}). grid p ds)" by auto
  also have "\<dots> = (\<Union> p \<in> grid b {d}. grid p ds)" unfolding grid_partition[where p=b] ..
  finally show ?thesis unfolding grid_union_eq by auto
qed
lemma grid_child_without_parent: assumes grid: "p \<in> grid (child b dir d) ds" (is "p \<in> grid ?c ds") and "d < length b"
  shows "p \<noteq> b"
proof -
  have "level ?c \<le> level p" using grid by (rule grid_level)
  hence "level b < level p" using child_level and \<open>d < length b\<close> by auto
  thus ?thesis by auto
qed
lemma grid_disjunct':
  assumes "p \<in> grid b ds" and "p' \<in> grid b ds" and "x \<in> grid p ds'" and "p \<noteq> p'" and "ds \<inter> ds' = {}"
  shows "x \<notin> grid p' ds'"
proof (rule ccontr)
  assume "\<not> x \<notin> grid p' ds'" hence "x \<in> grid p' ds'" by auto
  have l: "length b = length p" and l': "length b = length p'" using \<open>p \<in> grid b ds\<close> and \<open>p' \<in> grid b ds\<close> by auto
  hence "length p' = length p" by auto
  moreover have "\<forall> d < length p'. p' ! d = p ! d"
  proof (rule allI, rule impI)
    fix d assume dl': "d < length p'" hence "d < length b" using l' by auto
    hence dl: "d < length p" using l by auto
    show "p' ! d = p ! d"
    proof (cases "d \<in> ds'")
      case True with \<open>ds \<inter> ds' = {}\<close> have "d \<notin> ds" by auto
      hence "p' ! d = b ! d" and "p ! d = b ! d"
        using \<open>d < length b\<close> \<open>p' \<in> grid b ds\<close> and \<open>p \<in> grid b ds\<close> and grid_invariant by auto
      thus ?thesis by auto
    next
      case False
      show ?thesis
        using grid_invariant[OF dl' False \<open>x \<in> grid p' ds'\<close>]
          and grid_invariant[OF dl False \<open>x \<in> grid p ds'\<close>] by auto
    qed
  qed
  ultimately have "p' = p" by (metis nth_equalityI)
  thus False using \<open>p \<noteq> p'\<close> by auto
qed
lemma grid_split1: assumes grid: "p \<in> grid b (ds' \<union> ds)" and "ds \<inter> ds' = {}"
  shows "\<exists>! x \<in> grid b ds. p \<in> grid x ds'"
proof (rule ex_ex1I)
  obtain x where "x \<in> grid b ds" and "p \<in> grid x ds'" using grid_split[OF grid] by auto
  thus "\<exists> x. x \<in> grid b ds \<and> p \<in> grid x ds'" by auto
next
  fix x y
  assume "x \<in> grid b ds \<and> p \<in> grid x ds'" and "y \<in> grid b ds \<and> p \<in> grid y ds'"
  hence "x \<in> grid b ds" and "p \<in> grid x ds'" and "y \<in> grid b ds" and "p \<in> grid y ds'" by auto
  show "x = y"
  proof (rule ccontr)
    assume "x \<noteq> y"
    from grid_disjunct'[OF \<open>x \<in> grid b ds\<close> \<open>y \<in> grid b ds\<close> \<open>p \<in> grid x ds'\<close> this \<open>ds \<inter> ds' = {}\<close>]
    show False using \<open>p \<in> grid y ds'\<close> by auto
  qed
qed

subsection \<open> Grid Restricted to a Level \<close>

definition lgrid :: "grid_point \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> grid_point set"
where "lgrid b ds lm = { p \<in> grid b ds. level p < lm }"

lemma lgridI[intro]:
  "\<lbrakk> p \<in> grid b ds ; level p < lm \<rbrakk> \<Longrightarrow> p \<in> lgrid b ds lm"
  unfolding lgrid_def by simp

lemma lgridE[elim]:
  assumes "p \<in> lgrid b ds lm"
  assumes "\<lbrakk> p \<in> grid b ds ; level p < lm \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms unfolding lgrid_def by auto

lemma lgridI_child[intro]:
  "d \<in> ds \<Longrightarrow> p \<in> lgrid (child b dir d) ds lm \<Longrightarrow> p \<in> lgrid b ds lm"
  by (auto intro: grid_child)

lemma lgrid_empty[simp]: "lgrid p ds (level p) = {}"
proof (rule equals0I)
  fix p' assume "p' \<in> lgrid p ds (level p)"
  hence "level p' < level p" and "level p \<le> level p'" by auto
  thus False by auto
qed

lemma lgrid_empty': assumes "lm \<le> level p" shows "lgrid p ds lm = {}"
proof (rule equals0I)
  fix p' assume "p' \<in> lgrid p ds lm"
  hence "level p' < lm" and "level p \<le> level p'" by auto
  thus False using \<open>lm \<le> level p\<close> by auto
qed

lemma grid_not_child:
  assumes [simp]: "d < length p"
  shows "p \<notin> grid (child p dir d) ds"
proof (rule ccontr)
  assume "\<not> ?thesis"
  have "level p < level (child p dir d)" by auto
  with grid_level[OF \<open>\<not> ?thesis\<close>[unfolded not_not]]
  show False by auto
qed

subsection \<open> Unbounded Sparse Grid \<close>

definition sparsegrid' :: "nat \<Rightarrow> grid_point set"
where
  "sparsegrid' dm = grid (start dm) { 0 ..< dm }"

lemma grid_subset_alldim:
  assumes p: "p \<in> grid b ds"
  defines "dm \<equiv> length b"
  shows "p \<in> grid b {0..<dm}"
proof -
  have "ds \<inter> {dm..} \<union> ds \<inter> {0..<dm} = ds" by auto
  from gridgen_dim_restrict[where ds="ds \<inter> {0..<dm}" and ds'="ds \<inter> {dm..}"] this
  have "ds \<inter> {0..<dm} \<subseteq> {0..<dm}"
    and "p \<in> grid b (ds \<inter> {0..<dm})" using p unfolding dm_def by auto
  thus ?thesis by (rule grid_union_dims)
qed

lemma sparsegrid'_length[simp]:
  "b \<in> sparsegrid' dm \<Longrightarrow> length b = dm" unfolding sparsegrid'_def by auto

lemma sparsegrid'I[intro]:
  assumes b: "b \<in> sparsegrid' dm" and p: "p \<in> grid b ds"
  shows "p \<in> sparsegrid' dm"
  using sparsegrid'_length[OF b] b
       grid_transitive[OF grid_subset_alldim[OF p], where c="start dm" and ds''="{0..<dm}"]
  unfolding sparsegrid'_def by auto

lemma sparsegrid'_start:
  assumes "b \<in> grid (start dm) ds"
  shows "b \<in> sparsegrid' dm"
  unfolding sparsegrid'_def
  using grid_subset_alldim[OF assms] by simp

subsection \<open> Sparse Grid \<close>

definition sparsegrid :: "nat \<Rightarrow> nat \<Rightarrow> grid_point set"
where
  "sparsegrid dm lm = lgrid (start dm) { 0 ..< dm } lm"

lemma sparsegrid_length: "p \<in> sparsegrid dm lm \<Longrightarrow> length p = dm"
  by (auto simp: sparsegrid_def)

lemma sparsegrid_subset[intro]: "p \<in> sparsegrid dm lm \<Longrightarrow> p \<in> sparsegrid' dm"
  unfolding sparsegrid_def sparsegrid'_def lgrid_def by auto

lemma sparsegridI[intro]:
  assumes "p \<in> sparsegrid' dm" and "level p < lm"
  shows "p \<in> sparsegrid dm lm"
  using assms unfolding sparsegrid'_def sparsegrid_def lgrid_def by auto

lemma sparsegrid_start:
  assumes "b \<in> lgrid (start dm) ds lm"
  shows "b \<in> sparsegrid dm lm"
proof
  have "b \<in> grid (start dm) ds" using assms by auto
  thus "b \<in> sparsegrid' dm" by (rule sparsegrid'_start)
qed (insert assms, auto)

lemma sparsegridE[elim]:
  assumes "p \<in> sparsegrid dm lm"
  shows "p \<in> sparsegrid' dm" and "level p < lm"
  using assms unfolding sparsegrid'_def sparsegrid_def lgrid_def by auto

subsection \<open> Compute Sparse Grid Points \<close>

fun gridgen :: "grid_point \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> grid_point list"
where
  "gridgen p ds 0 = []"
| "gridgen p ds (Suc l) = (let
      sub = \<lambda> d. gridgen (child p left d) { d' \<in> ds . d' \<le> d } l @
                 gridgen (child p right d) { d' \<in> ds . d' \<le> d } l
      in p # concat (map sub [ d \<leftarrow> [0 ..< length p]. d \<in> ds]))"

lemma gridgen_lgrid_eq: "set (gridgen p ds l) = lgrid p ds (level p + l)"
proof (induct l arbitrary: p ds)
  case (Suc l)
  let "?subg dir d" = "set (gridgen (child p dir d) { d' \<in> ds . d' \<le>  d } l)"
  let "?sub dir d" = "lgrid (child p dir d) { d' \<in> ds . d' \<le>  d } (level p + Suc l)"
  let "?union F dm" = "{p} \<union> (\<Union> d \<in> { d \<in> ds. d < dm }. F left d \<union> F right d)"

  have hyp: "!! dir d. d < length p \<Longrightarrow> ?subg dir d = ?sub dir d"
    using Suc.hyps using child_level by auto

  { fix dm assume "dm \<le> length p"
    hence "?union ?sub dm = lgrid p {d \<in> ds. d < dm} (level p + Suc l)"
    proof (induct dm)
      case (Suc dm)
      hence "dm \<le> length p" by auto

      let ?l = "child p left dm" and ?r = "child p right dm"

      have p_lgrid: "p \<in> lgrid p {d \<in> ds. d < dm} (level p + Suc l)" by auto

      show ?case
      proof (cases "dm \<in> ds")
        case True
        let ?ds = "{d \<in> ds. d < dm} \<union> {dm}"
        have ds_eq: "{d' \<in> ds. d' \<le> dm} = ?ds" using True by auto
        have ds_eq': "{d \<in> ds. d < Suc dm} = {d \<in> ds. d < dm } \<union> {dm}" using True by auto

        have "?union ?sub (Suc dm) = ?union ?sub dm \<union> ({p} \<union> ?sub left dm \<union> ?sub right dm)"
          unfolding ds_eq' by auto
        also have "\<dots> = lgrid p {d \<in> ds. d < dm} (level p + Suc l) \<union> ?sub left dm \<union> ?sub right dm"
          unfolding Suc.hyps[OF \<open>dm \<le> length p\<close>] using p_lgrid by auto
        also have "\<dots> = {p' \<in> grid p {d \<in> ds. d<dm} \<union> (grid ?l ?ds) \<union> (grid ?r ?ds).
          level p' < level p + Suc l}" unfolding lgrid_def ds_eq by auto
        also have "\<dots> = lgrid p {d \<in> ds. d < Suc dm} (level p + Suc l)"
          unfolding lgrid_def ds_eq' unfolding grid_onedim_split[where b=p] ..
        finally show ?thesis .
      next
        case False hence "{d \<in> ds. d < Suc dm} = {d \<in> ds. d < dm \<or> d = dm}" by auto
        hence ds_eq: "{d \<in> ds. d < Suc dm} = {d \<in> ds. d < dm}" using \<open>dm \<notin> ds\<close> by auto
        show ?thesis unfolding ds_eq Suc.hyps[OF \<open>dm \<le> length p\<close>] ..
      qed
    next case 0 thus ?case unfolding lgrid_def by auto
    qed }
  hence "?union ?sub (length p) = lgrid p {d \<in> ds. d < length p} (level p + Suc l)" by auto
  hence union_lgrid_eq: "?union ?sub (length p) = lgrid p ds (level p + Suc l)"
    unfolding lgrid_def using grid_dim_remove_outer by auto

  have "set (gridgen p ds (Suc l)) = ?union ?subg (length p)"
    unfolding gridgen.simps and Let_def by auto
  hence "set (gridgen p ds (Suc l)) = ?union ?sub (length p)"
    using hyp by auto
  also have "\<dots> = lgrid p ds (level p + Suc l)"
    using union_lgrid_eq .
  finally show ?case .
qed auto

lemma gridgen_distinct: "distinct (gridgen p ds l)"
proof (induct l arbitrary: p ds)
  case (Suc l)
  let ?ds = "[d \<leftarrow> [0..<length p]. d \<in> ds]"
  let "?left d" = "gridgen (child p left d) { d' \<in> ds . d' \<le> d } l"
  and "?right d" = "gridgen (child p right d) { d' \<in> ds . d' \<le> d } l"
  let "?sub d" = "?left d @ ?right d"

  have "distinct (concat (map ?sub ?ds))"
  proof (cases l)
    case (Suc l')

    have inj_on: "inj_on ?sub (set ?ds)"
    proof (rule inj_onI, rule ccontr)
      fix d d' assume "d \<in> set ?ds" and "d' \<in> set ?ds"
      hence "d < length p" and "d \<in> set ?ds" and "d' < length p" by auto
      assume *: "?sub d = ?sub d'"
      have in_d: "child p left d \<in> set (?sub d)"
        using \<open>d \<in> set ?ds\<close> Suc
        by (auto simp add: gridgen_lgrid_eq lgrid_def grid_Start)

      have in_d': "child p left d' \<in> set (?sub d')"
        using \<open>d \<in> set ?ds\<close> Suc
        by (auto simp add: gridgen_lgrid_eq lgrid_def grid_Start)

      { fix p' d assume "d \<in> set ?ds" and "p' \<in> set (?sub d)"
        hence "lv p d < lv p' d"
          using grid_child_level
          by (auto simp add: gridgen_lgrid_eq lgrid_def grid_child_level) }
      note level_less = this

      assume "d \<noteq> d'"
      show False
      proof (cases "d' < d")
        case True
        with in_d' \<open>?sub d = ?sub d'\<close> level_less[OF \<open>d \<in> set ?ds\<close>]
        have "lv p d < lv (child p left d') d" by simp
        thus False unfolding lv_def
          using child_invariant[OF \<open>d < length p\<close>, of left d'] \<open>d \<noteq> d'\<close>
          by auto
      next
        case False hence "d < d'" using \<open>d \<noteq> d'\<close> by auto
        with in_d \<open>?sub d = ?sub d'\<close> level_less[OF \<open>d' \<in> set ?ds\<close>]
        have "lv p d' < lv (child p left d) d'" by simp
        thus False unfolding lv_def
          using child_invariant[OF \<open>d' < length p\<close>, of left d] \<open>d \<noteq> d'\<close>
          by auto
      qed
    qed

    show ?thesis
    proof (rule distinct_concat)
      show "distinct (map ?sub ?ds)"
        unfolding distinct_map using inj_on by simp
    next
      fix ys assume "ys \<in> set (map ?sub ?ds)"
      then obtain d where "d \<in> ds" and "d < length p"
        and *: "ys = ?sub d" by auto

      show "distinct ys" unfolding *
        using grid_disjunct[OF \<open>d < length p\<close>, of "{d' \<in> ds. d' \<le> d}"]
          gridgen_lgrid_eq lgrid_def \<open>distinct (?left d)\<close> \<open>distinct (?right d)\<close>
        by auto
    next
      fix ys zs
      assume "ys \<in> set (map ?sub ?ds)"
      then obtain d where ys: "ys = ?sub d" and "d \<in> set ?ds" by auto
      hence "d < length p" by auto

      assume "zs \<in> set (map ?sub ?ds)"
      then obtain d' where zs: "zs = ?sub d'" and "d' \<in> set ?ds" by auto
      hence "d' < length p" by auto

      assume "ys \<noteq> zs"
      hence "d' \<noteq> d" unfolding ys zs by auto

      show "set ys \<inter> set zs = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain p' where "p' \<in> set (?sub d)" and "p' \<in> set (?sub d')"
          unfolding ys zs by auto

        hence "lv p d < lv p' d" "lv p d' < lv p' d'"
          using grid_child_level \<open>d \<in> set ?ds\<close> \<open>d' \<in> set ?ds\<close>
          by (auto simp add: gridgen_lgrid_eq lgrid_def grid_child_level)

        show False
        proof (cases "d < d'")
          case True
          from \<open>p' \<in> set (?sub d)\<close>
          have "p ! d' = p' ! d'"
            using grid_invariant[of d' "child p right d" "{d' \<in> ds. d' \<le> d}"]
            using grid_invariant[of d' "child p left d" "{d' \<in> ds. d' \<le> d}"]
            using child_invariant[of d' _ _ d] \<open>d < d'\<close> \<open>d' < length p\<close>
            using gridgen_lgrid_eq lgrid_def by auto
          thus False using \<open>lv p d' < lv p' d'\<close> unfolding lv_def by auto
        next
          case False hence "d' < d" using \<open>d' \<noteq> d\<close> by simp
          from \<open>p' \<in> set (?sub d')\<close>
          have "p ! d = p' ! d"
            using grid_invariant[of d "child p right d'" "{d \<in> ds. d \<le> d'}"]
            using grid_invariant[of d "child p left d'" "{d \<in> ds. d \<le> d'}"]
            using child_invariant[of d _ _ d'] \<open>d' < d\<close> \<open>d < length p\<close>
            using gridgen_lgrid_eq lgrid_def by auto
          thus False using \<open>lv p d < lv p' d\<close> unfolding lv_def by auto
        qed
      qed
    qed
  qed (simp add: map_replicate_const)
  moreover
  have "p \<notin> set (concat (map ?sub ?ds))"
    using gridgen_lgrid_eq lgrid_def grid_not_child[of _ p] by simp
  ultimately show ?case
    unfolding gridgen.simps Let_def distinct.simps by simp
qed auto

lemma lgrid_finite: "finite (lgrid b ds lm)"
proof (cases "level b \<le> lm")
  case True from iffD1[OF le_iff_add True]
  obtain l where l: "lm = level b + l" by auto
  show ?thesis unfolding l gridgen_lgrid_eq[symmetric] by auto
next
  case False hence "!! x. x \<in> grid b ds \<Longrightarrow> (\<not> level x < lm)"
  proof -
    fix x assume "x \<in> grid b ds"
    from grid_level[OF this] show "\<not> level x < lm" using False by auto
  qed
  hence "lgrid b ds lm = {}" unfolding lgrid_def by auto
  thus ?thesis by auto
qed

lemma lgrid_sum:
  fixes F :: "grid_point \<Rightarrow> real"
  assumes "d < length b" and "level b < lm"
  shows "(\<Sum> p \<in> lgrid b {d} lm. F p) =
          (\<Sum> p \<in> lgrid (child b left d) {d} lm. F p) + (\<Sum> p \<in> lgrid (child b right d) {d} lm. F p) + F b"
  (is "(\<Sum> p \<in> ?grid b. F p) = (\<Sum> p \<in> ?grid ?l . F p) + (?sum (?grid ?r)) + F b")
proof -
  have "!! dir. b \<notin> ?grid (child b dir d)"
    using grid_child_without_parent[where ds="{d}"] and \<open>d < length b\<close> and lgrid_def by auto
  hence b_distinct: "b \<notin> (?grid ?l \<union> ?grid ?r)" by auto

  have "?grid ?l \<inter> ?grid ?r = {}"
    unfolding lgrid_def using grid_disjunct and \<open>d < length b\<close> by auto
  from lgrid_finite lgrid_finite and this
  have child_eq: "?sum ((?grid ?l) \<union> (?grid ?r)) = ?sum (?grid ?l) + ?sum (?grid ?r)"
    by (rule sum.union_disjoint)

  have "?grid b = {b} \<union> (?grid ?l) \<union> (?grid ?r)" unfolding lgrid_def grid_partition[where p=b] using assms by auto
  hence "?sum (?grid b) = F b + ?sum ((?grid ?l) \<union> (?grid ?r))" using b_distinct and lgrid_finite by auto
  thus ?thesis using child_eq by auto
qed

subsection \<open> Base Points \<close>

definition base :: "nat set \<Rightarrow> grid_point \<Rightarrow> grid_point"
where "base ds p = (THE b. b \<in> grid (start (length p)) ({0 ..< length p} - ds) \<and> p \<in> grid b ds)"

lemma baseE: assumes p_grid: "p \<in> sparsegrid' dm"
  shows "base ds p \<in> grid (start dm) ({0..<dm} - ds)"
  and "p \<in> grid (base ds p) ds"
proof -
  from p_grid[unfolded sparsegrid'_def]
  have *: "\<exists>! x \<in> grid (start dm) ({0..<dm} - ds). p \<in> grid x ds"
    by (intro grid_split1) (auto intro: grid_union_dims)
  then obtain x where x_eq: "x \<in> grid (start dm) ({0..<dm} - ds) \<and> p \<in> grid x ds"
    by auto
  with * have "base ds p = x" unfolding base_def by auto
  thus "base ds p \<in> grid (start dm) ({0..<dm} - ds)" and "p \<in> grid (base ds p) ds"
    using x_eq by auto
qed

lemma baseI: assumes x_grid: "x \<in> grid (start dm) ({0..<dm} - ds)" and p_xgrid: "p \<in> grid x ds"
  shows "base ds p = x"
proof -
  have "p \<in> grid (start dm) (ds \<union> ({0..<dm} - ds))"
    using grid_transitive[OF p_xgrid x_grid, where ds''="ds \<union> ({0..<dm} - ds)"] by auto
  moreover have "ds \<inter> ({0..<dm} - ds) = {}" by auto
  ultimately have "\<exists>! x \<in> grid (start dm) ({0..<dm} - ds). p \<in> grid x ds"
    using grid_split1[where p=p and b="start dm" and ds'=ds and ds="{0..<dm} - ds"] by auto
  thus "base ds p = x" using x_grid p_xgrid unfolding base_def by auto
qed

lemma base_empty: assumes p_grid: "p \<in> sparsegrid' dm" shows "base {} p = p"
  using grid_empty_ds and p_grid and grid_split1[where ds="{0..<dm}" and ds'="{}"] unfolding base_def sparsegrid'_def by auto

lemma base_start_eq: assumes p_spg: "p \<in> sparsegrid dm lm"
  shows "start dm = base {0..<dm} p"
proof -
  from p_spg
  have "start dm \<in> grid (start dm) ({0..<dm} - {0..<dm})"
    and "p \<in> grid (start dm) {0..<dm}" using sparsegrid'_def by auto
  from baseI[OF this(1) this(2)] show ?thesis by auto
qed

lemma base_in_grid: assumes p_grid: "p \<in> sparsegrid' dm" shows "base ds p \<in> grid (start dm) {0..<dm}"
proof -
  let ?ds = "ds \<union> {0..<dm}"
  have ds_eq: "{ d \<in> ?ds. d < length (start dm) } = { 0..< dm}"
    unfolding start_def by auto
  have "base ds p \<in> grid (start dm) ?ds"
    using grid_union_dims[OF _ baseE(1)[OF p_grid, where ds=ds], where ds'="?ds"] by auto
  thus ?thesis using grid_dim_remove_outer[where b="start dm" and ds="?ds"] unfolding ds_eq by auto
qed

lemma base_grid: assumes p_grid: "p \<in> sparsegrid' dm" shows "grid (base ds p) ds \<subseteq> sparsegrid' dm"
proof
  fix x assume xgrid: "x \<in> grid (base ds p) ds"
  have ds_eq: "{ d \<in> {0..<dm} \<union> ds. d < length (start dm) } = {0..<dm}" by auto
  from grid_transitive[OF xgrid base_in_grid[OF p_grid], where ds''="{0..<dm} \<union> ds"]
  show "x \<in> sparsegrid' dm" unfolding sparsegrid'_def
    using grid_dim_remove_outer[where b="start dm" and ds="{0..<dm} \<union> ds"] unfolding ds_eq unfolding Un_ac(3)[of "{0..<dm}"]
    by auto
qed
lemma base_length[simp]: assumes p_grid: "p \<in> sparsegrid' dm" shows "length (base ds p) = dm"
proof -
  from baseE[OF p_grid] have "base ds p \<in> grid (start dm) ({0..<dm} - ds)" by auto
  thus ?thesis by auto
qed
lemma base_in[simp]: assumes "d < dm" and "d \<in> ds" and p_grid: "p \<in> sparsegrid' dm" shows "base ds p ! d = start dm ! d"
proof -
  have ds: "d \<notin> {0..<dm} - ds" using \<open>d \<in> ds\<close> by auto
  have "d < length (start dm)" using \<open>d < dm\<close> by auto
  with grid_invariant[OF this ds] baseE(1)[OF p_grid] show ?thesis by auto
qed
lemma base_out[simp]: assumes "d < dm" and "d \<notin> ds" and p_grid: "p \<in> sparsegrid' dm" shows "base ds p ! d = p ! d"
proof -
  have "d < length (base ds p)" using base_length[OF p_grid] \<open>d < dm\<close> by auto
  with grid_invariant[OF this \<open>d \<notin> ds\<close>] baseE(2)[OF p_grid] show ?thesis by auto
qed
lemma base_base: assumes p_grid: "p \<in> sparsegrid' dm" shows "base ds (base ds' p) = base (ds \<union> ds') p"
proof (rule nth_equalityI)
  have b_spg: "base ds' p \<in> sparsegrid' dm" unfolding sparsegrid'_def
    using grid_union_dims[OF Diff_subset[where A="{0..<dm}" and B="ds'"] baseE(1)[OF p_grid]] .
  from base_length[OF b_spg] base_length[OF p_grid] show "length (base ds (base ds' p)) = length (base (ds \<union> ds') p)" by auto

  show "base ds (base ds' p) ! i = base (ds \<union> ds') p ! i" if "i < length (base ds (base ds' p))" for i
  proof -
    have "i < dm" using that base_length[OF b_spg] by auto
    show "base ds (base ds' p) ! i = base (ds \<union> ds') p ! i"
    proof (cases "i \<in> ds \<union> ds'")
      case True
      show ?thesis
      proof (cases "i \<in> ds")
        case True from base_in[OF \<open>i < dm\<close> \<open>i \<in> ds \<union> ds'\<close> p_grid] base_in[OF \<open>i < dm\<close> this b_spg] show ?thesis by auto
      next
        case False hence "i \<in> ds'" using \<open>i \<in> ds \<union> ds'\<close> by auto
        from base_in[OF \<open>i < dm\<close> \<open>i \<in> ds \<union> ds'\<close> p_grid] base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds\<close> b_spg] base_in[OF \<open>i < dm\<close> \<open>i \<in> ds'\<close> p_grid] show ?thesis by auto
      qed
    next
      case False hence "i \<notin> ds" and "i \<notin> ds'" by auto
      from base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds \<union> ds'\<close> p_grid] base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds\<close> b_spg] base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds'\<close> p_grid] show ?thesis by auto
    qed
  qed
qed
lemma grid_base_out: assumes "d < dm" and "d \<notin> ds" and p_grid: "b \<in> sparsegrid' dm" and "p \<in> grid (base ds b) ds"
  shows "p ! d = b ! d"
proof -
  have "base ds b ! d = b ! d" using assms by auto
  moreover have "d < length (base ds b)" using assms by auto
  from grid_invariant[OF this]
  have "p ! d = base ds b ! d" using assms by auto
  ultimately show ?thesis by auto
qed

lemma grid_grid_inj_on: assumes "ds \<inter> ds' = {}" shows "inj_on snd (\<Union>p'\<in>grid b ds. \<Union>p''\<in>grid p' ds'. {(p', p'')})"
proof (rule inj_onI)
  fix x y
  assume "x \<in> (\<Union>p'\<in>grid b ds. \<Union>p''\<in>grid p' ds'. {(p', p'')})"
  hence "snd x \<in> grid (fst x) ds'" and "fst x \<in> grid b ds" by auto

  assume "y \<in> (\<Union>p'\<in>grid b ds. \<Union>p''\<in>grid p' ds'. {(p', p'')})"
  hence "snd y \<in> grid (fst y) ds'" and "fst y \<in> grid b ds" by auto

  assume "snd x = snd y"
  have "fst x = fst y"
  proof (rule ccontr)
    assume "fst x \<noteq> fst y"
    from grid_disjunct'[OF \<open>fst x \<in> grid b ds\<close> \<open>fst y \<in> grid b ds\<close> \<open>snd x \<in> grid (fst x) ds'\<close> this \<open>ds \<inter> ds' = {}\<close>]
    show False using \<open>snd y \<in> grid (fst y) ds'\<close> unfolding \<open>snd x = snd y\<close> by auto
  qed
  show "x = y" using prod_eqI[OF \<open>fst x = fst y\<close> \<open>snd x = snd y\<close>] .
qed

lemma grid_level_d: assumes "d < length b" and p_grid: "p \<in> grid b {d}" and "p \<noteq> b" shows "lv p d > lv b d"
proof -
  from p_grid[unfolded grid_partition[where p=b]]
  show ?thesis using grid_child_level using assms by auto
qed

lemma grid_base_base: assumes "b \<in> sparsegrid' dm"
  shows "base ds' b \<in> grid (base ds (base ds' b)) (ds \<union> ds')"
proof -
  from base_grid[OF \<open>b \<in> sparsegrid' dm\<close>] have "base ds' b \<in> sparsegrid' dm" by auto
  from grid_union_dims[OF _ baseE(2)[OF this], of ds "ds \<union> ds'"] show ?thesis by auto
qed

lemma grid_base_union: assumes b_spg: "b \<in> sparsegrid' dm" and p_grid: "p \<in> grid (base ds b) ds" and x_grid: "x \<in> grid (base ds' p) ds'"
  shows "x \<in> grid (base (ds \<union> ds') b) (ds \<union> ds')"
proof -
  have ds_union: "ds \<union> ds' = ds' \<union> (ds \<union> ds')" by auto

  from base_grid[OF b_spg] p_grid have p_spg: "p \<in> sparsegrid' dm"  by auto
  with assms and grid_base_base have base_b': "base ds' p \<in> grid (base ds (base ds' p)) (ds \<union> ds')" by auto
  moreover have "base ds' (base ds b) = base ds' (base ds p)" (is "?b = ?p")
  proof (rule nth_equalityI)
    have bb_spg: "base ds b \<in> sparsegrid' dm" using base_grid[OF b_spg] grid.Start by auto
    hence "dm = length (base ds b)" by auto
    have bp_spg: "base ds p \<in> sparsegrid' dm" using base_grid[OF p_spg] grid.Start by auto

    show "length ?b = length ?p" using base_length[OF bp_spg] base_length[OF bb_spg] by auto
    show "?b ! i = ?p ! i" if "i < length ?b" for i
    proof -
      have "i < dm" and "i < length (base ds b)" using that base_length[OF bb_spg] \<open>dm = length (base ds b)\<close> by auto
      show "?b ! i = ?p ! i"
      proof (cases "i \<in> ds \<union> ds'")
        case True
        hence "!! x. base ds x \<in> sparsegrid' dm \<Longrightarrow> x \<in> sparsegrid' dm \<Longrightarrow> base ds' (base ds x) ! i = (start dm) ! i"
        proof - fix x assume x_spg: "x \<in> sparsegrid' dm" and xb_spg: "base ds x \<in> sparsegrid' dm"
          show "base ds' (base ds x) ! i = (start dm) ! i"
          proof (cases "i \<in> ds'")
            case True from base_in[OF \<open>i < dm\<close> this xb_spg] show ?thesis .
          next
            case False hence "i \<in> ds" using \<open>i \<in> ds \<union> ds'\<close> by auto
            from base_out[OF \<open>i < dm\<close> False xb_spg] base_in[OF \<open>i < dm\<close> this x_spg] show ?thesis by auto
          qed
        qed
        from this[OF bp_spg p_spg] this[OF bb_spg b_spg] show ?thesis by auto
      next
        case False hence "i \<notin> ds" and "i \<notin> ds'" by auto
        from grid_invariant[OF \<open>i < length (base ds b)\<close> \<open>i \<notin> ds\<close> p_grid]
          base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds'\<close> bp_spg] base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds\<close> p_spg] base_out[OF \<open>i < dm\<close> \<open>i \<notin> ds'\<close> bb_spg]
        show ?thesis by auto
      qed
    qed
  qed
  ultimately have "base ds' p \<in> grid (base (ds \<union> ds') b) (ds \<union> ds')"
    by (simp only: base_base[OF p_spg] base_base[OF b_spg] Un_ac(3))
  from grid_transitive[OF x_grid this] show ?thesis using ds_union by auto
qed
lemma grid_base_dim_add: assumes "ds' \<subseteq> ds" and b_spg: "b \<in> sparsegrid' dm" and p_grid: "p \<in> grid (base ds' b) ds'"
  shows "p \<in> grid (base ds b) ds"
proof -
  have ds_eq: "ds' \<union> ds = ds" using assms by auto

  have "p \<in> sparsegrid' dm" using base_grid[OF b_spg] p_grid by auto
  hence "p \<in> grid (base ds p) ds" using baseE by auto
  from grid_base_union[OF b_spg p_grid this]
  show ?thesis using ds_eq by auto
qed
lemma grid_replace_dim: assumes "d < length b'" and "d < length b" and p_grid: "p \<in> grid b ds" and p'_grid: "p' \<in> grid b' ds"
  shows "p[d := p' ! d] \<in> grid (b[d := b' ! d]) ds" (is "_ \<in> grid ?b ds")
  using p'_grid and p_grid
proof induct
  case (Child p'' d' dir)
  hence p''_grid: "p[d := p'' ! d] \<in> grid ?b ds" and "d < length p''" using assms by auto
  have "d < length p" using p_grid assms by auto
  thus ?case
  proof (cases "d' = d")
    case True
    from grid.Child[OF p''_grid \<open>d' \<in> ds\<close>]
    show ?thesis unfolding child_def ix_def lv_def list_update_overwrite \<open>d' = d\<close> nth_list_update_eq[OF \<open>d < length p''\<close>] nth_list_update_eq[OF \<open>d < length p\<close>] .
  next
    case False
    show ?thesis unfolding child_def nth_list_update_neq[OF False] using Child by auto
  qed
qed (rule grid_change_dim)
lemma grid_shift_base:
  assumes ds_dj: "ds \<inter> ds' = {}" and b_spg: "b \<in> sparsegrid' dm" and p_grid: "p \<in> grid (base (ds' \<union> ds) b) (ds' \<union> ds)"
  shows "base ds' p \<in> grid (base (ds \<union> ds') b) ds"
proof -
  from grid_split[OF p_grid]
  obtain x where x_grid: "x \<in> grid (base (ds' \<union> ds) b) ds" and p_xgrid: "p \<in> grid x ds'" by auto
  from grid_union_dims[OF _ this(1)]
  have x_spg: "x \<in> sparsegrid' dm" using base_grid[OF b_spg] by auto

  have b_len: "length (base (ds' \<union> ds) b) = dm" using base_length[OF b_spg] by auto

  define d' where "d' = dm"
  moreover have "d' \<le> dm \<Longrightarrow> x \<in> grid (start dm) ({0..<dm} - {d \<in> ds'. d < d'})"
  proof (induct d')
    case (Suc d')
    with b_len have d'_b: "d' < length (base (ds' \<union> ds) b)" by auto
    show ?case
    proof (cases "d' \<in> ds'")
      case True hence "d' \<notin> ds" and "d' \<in> ds' \<union> ds" using ds_dj by auto
      have "{0..<dm} - {d \<in> ds'. d < d'} = ({0..<dm} - {d \<in> ds'. d < d'}) - {d'} \<union> {d'}" using \<open>Suc d' \<le> dm\<close> by auto
      also have "\<dots> = ({0..<dm} - {d \<in> ds'. d < Suc d'}) \<union> {d'}" by auto
      finally have x_g: "x \<in> grid (start dm) ({d'} \<union> ({0..<dm} - {d \<in> ds'. d < Suc d'}))" using Suc by auto
      from grid_invariant[OF d'_b \<open>d' \<notin> ds\<close> x_grid] base_in[OF _ \<open>d' \<in> ds' \<union> ds\<close> b_spg] \<open>Suc d' \<le> dm\<close>
      have "x ! d' = start dm ! d'" by auto
      from grid_dim_remove[OF x_g this] show ?thesis .
    next
      case False
      hence "{d \<in> ds'. d < Suc d'} = {d \<in> ds'. d < d' \<or> d = d'}" by auto
      also have "\<dots> = {d \<in> ds'. d < d'}" using False by auto
      finally show ?thesis using Suc by auto
    qed
  next
    case 0 show ?case using x_spg[unfolded sparsegrid'_def] by auto
  qed
  moreover have "{0..<dm} - ds' = {0..<dm} - {d \<in> ds'. d < dm}" by auto
  ultimately have "x \<in> grid (start dm) ({0..<dm} - ds')" by auto
  from baseI[OF this p_xgrid] and x_grid
  show ?thesis by (auto simp: Un_ac(3))
qed

subsection \<open> Lift Operation over all Grid Points \<close>

definition lift :: "(nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> vector \<Rightarrow> vector) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vector \<Rightarrow> vector"
where "lift f dm lm d = foldr (\<lambda> p. f d (lm - level p) p) (gridgen (start dm) ({ 0 ..< dm } - { d }) lm)"

lemma lift:
  assumes "d < dm" and "p \<in> sparsegrid dm lm"
  and Fintro: "\<And> l b p \<alpha>. \<lbrakk> b \<in> lgrid (start dm) ({0..<dm} - {d}) lm ;
                          l + level b = lm ; p \<in> sparsegrid dm lm \<rbrakk>
             \<Longrightarrow> F d l b \<alpha> p = (if b = base {d} p
                               then (\<Sum> p' \<in> lgrid b {d} lm. S (\<alpha> p') p p')
                               else \<alpha> p)"
  shows "lift F dm lm d \<alpha> p = (\<Sum> p' \<in> lgrid (base {d} p) {d} lm. S (\<alpha> p') p p')"
        (is "?lift = ?S p \<alpha>")
proof -
  let ?gridgen = "gridgen (start dm) ({0..<dm} - {d}) lm"
  let "?f p" = "F d (lm - level p) p"

  { fix bs \<beta> b
    assume "set bs \<subseteq> set ?gridgen" and "distinct bs" and "p \<in> sparsegrid dm lm"
    hence "foldr ?f bs \<beta> p = (if base {d} p \<in> set bs then ?S p \<beta> else \<beta> p)"
    proof (induct bs arbitrary: p)
      case (Cons b bs)
      hence "b \<in> lgrid (start dm) ({0..<dm} - {d}) lm"
        and "(lm - level b) + level b = lm"
        and b_grid: "b \<in> grid (start dm) ({0..<dm} - {d})"
        using lgrid_def gridgen_lgrid_eq by auto
      note F = Fintro[OF this(1,2) \<open>p \<in> sparsegrid dm lm\<close>]

      have "b \<notin> set bs" using \<open>distinct (b#bs)\<close> by auto

      show ?case
      proof (cases "base {d} p \<in> set (b#bs)")
        case True note base_in_set = this

        show ?thesis
        proof (cases "b = base {d} p")
          case True
          moreover
          { fix p' assume "p' \<in> lgrid b {d} lm"
            hence "p' \<in> grid b {d}" and "level p' < lm" unfolding lgrid_def by auto
            from grid_transitive[OF this(1) b_grid, of "{0..<dm}"] \<open>d < dm\<close>
              baseI[OF b_grid \<open>p' \<in> grid b {d}\<close>] \<open>b \<notin> set bs\<close>
              Cons.prems Cons.hyps[of p'] this(2)
            have "foldr ?f bs \<beta> p' = \<beta> p'" unfolding sparsegrid_def lgrid_def by auto }
          ultimately show ?thesis
            using F base_in_set by auto
        next
          case False
          with base_in_set have "base {d} p \<in> set bs" by auto
          with Cons.hyps[of p] Cons.prems
          have "foldr ?f bs \<beta> p = ?S p \<beta>" by auto
          thus ?thesis using F base_in_set False by auto
        qed
      next
        case False
        hence "b \<noteq> base {d} p" by auto
        from False Cons.hyps[of p] Cons.prems
        have "foldr ?f bs \<beta> p = \<beta> p" by auto
        thus ?thesis using False F \<open>b \<noteq> base {d} p\<close> by auto
      qed
    qed auto
  }
  moreover have "base {d} p \<in> set ?gridgen"
  proof -
    have "p \<in> grid (base {d} p) {d}"
      using \<open>p \<in> sparsegrid dm lm\<close>[THEN sparsegrid_subset] by (rule baseE)
    from grid_level[OF this] baseE(1)[OF sparsegrid_subset[OF \<open>p \<in> sparsegrid dm lm\<close>]]
    show ?thesis using \<open>p \<in> sparsegrid dm lm\<close>
      unfolding gridgen_lgrid_eq sparsegrid'_def lgrid_def sparsegrid_def
      by auto
  qed
  ultimately show ?thesis unfolding lift_def
    using gridgen_distinct \<open>p \<in> sparsegrid dm lm\<close> by auto
qed

subsection \<open> Parent Points \<close>

definition parents :: "nat \<Rightarrow> grid_point \<Rightarrow> grid_point \<Rightarrow> grid_point set"
where "parents d b p = { x \<in> grid b {d}. p \<in> grid x {d} }"

lemma parents_split: assumes p_grid: "p \<in> grid (child b dir d) {d}"
  shows "parents d b p = { b } \<union> parents d (child b dir d) p"
proof (intro set_eqI iffI)
  let ?chd = "child b dir d" and ?chid = "child b (inv dir) d"
  fix x assume "x \<in> parents d b p"
  hence "x \<in> grid b {d}" and "p \<in> grid x {d}" unfolding parents_def by auto
  hence x_split: "x \<in> {b} \<union> grid ?chd {d} \<union> grid ?chid {d}" using grid_onedim_split[where ds="{}" and b=b] and grid_empty_ds
    by (cases dir, auto)
  thus "x \<in> {b} \<union> parents d (child b dir d) p"
  proof (cases "x = b")
    case False
    have "d < length b"
    proof (rule ccontr)
      assume "\<not> d < length b" hence empty: "{d' \<in> {d}. d' < length b} = {}" by auto
      have "x = b" using \<open>x \<in> grid b {d}\<close>
        unfolding grid_dim_remove_outer[where ds="{d}" and b=b] empty
        using grid_empty_ds by auto
      thus False using \<open>\<not> x = b\<close> by auto
    qed
    have "x \<notin> grid ?chid {d}"
    proof (rule ccontr)
      assume "\<not> x \<notin> grid ?chid {d}"
      hence "p \<in> grid ?chid {d}" using grid_transitive[OF \<open>p \<in> grid x {d}\<close>, where ds'="{d}"]
        by auto
      hence "p \<notin> grid ?chd {d}" using grid_disjunct[OF \<open>d < length b\<close>] by (cases dir, auto)
      thus False using \<open>p \<in> grid ?chd {d}\<close> ..
    qed
    with False and x_split
    have "x \<in> grid ?chd {d}" by auto
    thus ?thesis unfolding parents_def using \<open>p \<in> grid x {d}\<close> by auto
  qed auto
next
  let ?chd = "child b dir d" and ?chid = "child b (inv dir) d"
  fix x assume x_in: "x \<in> {b} \<union> parents d ?chd p"
  thus "x \<in> parents d b p"
  proof (cases "x = b")
    case False
    hence "x \<in> parents d ?chd p" using x_in by auto
    thus ?thesis unfolding parents_def using grid_child[where b=b] by auto
  next
    from p_grid have "p \<in> grid b {d}" using grid_child[where b=b] by auto
    case True thus ?thesis unfolding parents_def using \<open>p \<in> grid b {d}\<close> by auto
  qed
qed

lemma parents_no_parent: assumes "d < length b" shows "b \<notin> parents d (child b dir d) p" (is "_ \<notin> parents _ ?ch _")
proof
  assume "b \<in> parents d ?ch p" hence "b \<in> grid ?ch {d}" unfolding parents_def by auto
  from grid_level[OF this]
  have "level b + 1 \<le> level b" unfolding child_level[OF \<open>d < length b\<close>] .
  thus False by auto
qed

lemma parents_subset_lgrid: "parents d b p \<subseteq> lgrid b {d} (level p + 1)"
proof
  fix x assume "x \<in> parents d b p"
  hence "x \<in> grid b {d}" and "p \<in> grid x {d}" unfolding parents_def by auto
  moreover hence "level x \<le> level p" using grid_level by auto
  hence "level x < level p + 1" by auto
  ultimately show "x \<in> lgrid b {d} (level p + 1)" unfolding lgrid_def by auto
qed

lemma parents_finite: "finite (parents d b p)"
  using finite_subset[OF parents_subset_lgrid lgrid_finite] .

lemma parent_sum: assumes p_grid: "p \<in> grid (child b dir d) {d}" and "d < length b"
  shows "(\<Sum> x \<in> parents d b p. F x) = F b + (\<Sum> x \<in> parents d (child b dir d) p. F x)"
  unfolding parents_split[OF p_grid] using parents_no_parent[OF \<open>d < length b\<close>, where dir=dir and p=p] using parents_finite
  by auto

lemma parents_single: "parents d b b = { b }"
proof
  have "parents d b b \<subseteq> lgrid b {d} (level b + (Suc 0))" using parents_subset_lgrid by auto
  also have "\<dots> = {b}" unfolding gridgen_lgrid_eq[symmetric] gridgen.simps Let_def by auto
  finally show "parents d b b \<subseteq> { b }" .
next
  have "b \<in> parents d b b" unfolding parents_def by auto
  thus "{ b } \<subseteq> parents d b b" by auto
qed

lemma grid_single_dimensional_specification:
  assumes "d < length b"
  and "odd i"
  and "lv b d + l' = l"
  and "i < (ix b d + 1) * 2^l'"
  and "i > (ix b d - 1) * 2^l'"
  shows "b[d := (l,i)] \<in> grid b {d}"
using assms proof (induct l' arbitrary: b)
  case 0
  hence "i = ix b d" and "l = lv b d" by auto
  thus ?case unfolding ix_def lv_def by auto
next
  case (Suc l')

  have "d \<in> {d}" by auto

  show ?case
  proof (rule linorder_cases)
    assume "i = ix b d * 2^(Suc l')"
    hence "even i" by auto
    thus ?thesis using \<open>odd i\<close> by blast
  next
    assume *: "i < ix b d * 2^(Suc l')"

    let ?b = "child b left d"

    have "d < length ?b" using Suc by auto
    moreover note \<open>odd i\<close>
    moreover have "lv ?b d + l' = l"
      and "i < (ix ?b d + 1) * 2^l'"
      and "(ix ?b d - 1) * 2^l' < i"
      unfolding child_ix_left[OF Suc.prems(1)]
      using Suc.prems * child_lv by (auto simp add: field_simps)
    ultimately have "?b[d := (l,i)] \<in> grid ?b {d}"
      by (rule Suc.hyps)
    thus ?thesis
      by (auto intro!: grid_child[OF \<open>d \<in> {d}\<close>, of _ b left]
        simp add: child_def)
  next
    assume *: "ix b d * 2^(Suc l') < i"

    let ?b = "child b right d"

    have "d < length ?b" using Suc by auto
    moreover note \<open>odd i\<close>
    moreover have "lv ?b d + l' = l"
      and "i < (ix ?b d + 1) * 2^l'"
      and "(ix ?b d - 1) * 2^l' < i"
      unfolding child_ix_right[OF Suc.prems(1)]
      using Suc.prems * child_lv by (auto simp add: field_simps)
    ultimately have "?b[d := (l,i)] \<in> grid ?b {d}"
      by (rule Suc.hyps)
    thus ?thesis
      by (auto intro!: grid_child[OF \<open>d \<in> {d}\<close>, of _ b right]
        simp add: child_def)
  qed
qed

lemma grid_multi_dimensional_specification:
  assumes "dm \<le> length b" and "length p = length b"
  and "\<And> d. d < dm \<Longrightarrow>
    odd (ix p d) \<and>
    lv b d \<le> lv p d \<and>
    ix p d < (ix b d + 1) * 2^(lv p d - lv b d) \<and>
    ix p d > (ix b d - 1) * 2^(lv p d - lv b d)"
    (is "\<And> d. d < dm \<Longrightarrow> ?bounded p d")
  and "\<And> d. \<lbrakk> dm \<le> d ; d < length b \<rbrakk> \<Longrightarrow> p ! d = b ! d"
  shows "p \<in> grid b {0..<dm}"
using assms proof (induct dm arbitrary: p)
  case 0
  hence "p = b" by (auto intro!: nth_equalityI)
  thus ?case by auto
next
  case (Suc dm)
  hence "dm \<le> length b"
    and "dm < length p" by auto

  let ?p = "p[dm := b ! dm]"

  note \<open>dm \<le> length b\<close>
  moreover have "length ?p = length b" using \<open>length p = length b\<close> by simp
  moreover
  {
    fix d assume "d < dm"
    hence *: "d < Suc dm" and "dm \<noteq> d" by auto
    have "?p ! d = p ! d"
      by (rule nth_list_update_neq[OF \<open>dm \<noteq> d\<close>])
    hence "?bounded ?p d"
      using Suc.prems(3)[OF *] lv_def ix_def
      by simp
  }
  moreover
  {
    fix d assume "dm \<le> d" and "d < length b"
    have "?p ! d = b ! d"
    proof (cases "d = dm")
      case True thus ?thesis using \<open>d < length b\<close> \<open>length p = length b\<close> by auto
    next
      case False
      hence "Suc dm \<le> d" using \<open>dm \<le> d\<close> by auto
      thus ?thesis using Suc.prems(4) \<open>d < length b\<close> by auto
    qed
  }
  ultimately
  have *: "?p \<in> grid b {0..<dm}"
    by (auto intro!: Suc.hyps)

  have "lv b dm \<le> lv p dm" using Suc.prems(3)[OF lessI] by simp

  have [simp]: "lv ?p dm = lv b dm" using lv_def \<open>dm < length p\<close> by auto
  have [simp]: "ix ?p dm = ix b dm" using ix_def \<open>dm < length p\<close> by auto
  have [simp]: "p[dm := (lv p dm, ix p dm)] = p"
    using lv_def ix_def \<open>dm < length p\<close> by auto
  have "dm < length ?p" and
    [simp]: "lv b dm + (lv p dm - lv b dm) = lv p dm"
    using \<open>dm < length p\<close> \<open>lv b dm \<le> lv p dm\<close> by auto
  from grid_single_dimensional_specification[OF this(1),
    where l="lv p dm" and i="ix p dm" and l'="lv p dm - lv b dm", simplified]
  have "p \<in> grid ?p {dm}"
    using Suc.prems(3)[OF lessI] by blast
  from grid_transitive[OF this *]
  show ?case by auto
qed

lemma sparsegrid:
  "sparsegrid dm lm = {p.
    length p = dm \<and> level p < lm \<and>
    (\<forall> d < dm. odd (ix p d) \<and> 0 < ix p d \<and> ix p d < 2^(lv p d + 1))}"
  (is "_ = ?set")
proof (rule equalityI[OF subsetI subsetI])
  fix p
  assume *: "p \<in> sparsegrid dm lm"
  hence "length p = dm" and "level p < lm" unfolding sparsegrid_def by auto
  moreover
  { fix d assume "d < dm"
    hence **: "p \<in> grid (start dm) {0..<dm}" and "d < length (start dm)"
      using * unfolding sparsegrid_def by auto
    have "odd (ix p d)"
    proof (cases "p ! d = start dm ! d")
      case True
      thus ?thesis unfolding start_def using \<open>d < dm\<close> ix_def by auto
    next
      case False
      from grid_odd[OF _ this **]
      show ?thesis using \<open>d < dm\<close> by auto
    qed
    hence "odd (ix p d) \<and> 0 < ix p d \<and> ix p d < 2^(lv p d + 1)"
      using grid_estimate[OF \<open>d < length (start dm)\<close> **]
      unfolding ix_def lv_def start_def using \<open>d < dm\<close> by auto
  }
  ultimately show "p \<in> ?set"
    using sparsegrid_def lgrid_def by auto
next
  fix p
  assume "p \<in> ?set"
  with grid_multi_dimensional_specification[of dm "start dm" p]
  have "p \<in> grid (start dm) {0..<dm}" and "level p < lm"
    by auto
  thus "p \<in> sparsegrid dm lm"
    unfolding sparsegrid_def lgrid_def by auto
qed

end
