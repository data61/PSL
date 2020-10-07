section \<open> UpDown  \<close>

(* Definition of sparse grids, hierarchical bases and the up-down algorithm.
 *
 * Based on "updown_L2-Skalarprodukt.mws" from Dirk Pflüger <pflueged@in.tum.de>
 *
 * Author: Johannes Hölzl <hoelzl@in.tum.de>
 *)
theory Up_Down
imports Up Down
begin

lemma updown': "\<lbrakk> d \<le> dm; p \<in> sparsegrid dm lm \<rbrakk>
  \<Longrightarrow> (updown' dm lm d \<alpha>) p = (\<Sum> p' \<in> lgrid (base {0 ..< d} p) {0 ..< d} lm. \<alpha> p' * (\<Prod> d' \<in> {0 ..< d}. l2_\<phi> (p' ! d') (p ! d')))"
  (is "\<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> _ = (\<Sum> p' \<in> ?subgrid d p. \<alpha> p' * ?prod d p' p)")
proof (induct d arbitrary: \<alpha> p)
  case 0 hence "?subgrid 0 p = {p}" using base_empty unfolding lgrid_def and sparsegrid_def sparsegrid'_def by auto
  thus ?case unfolding updown'.simps by auto
next
  case (Suc d)
  let "?leafs p" = "(lgrid p {d} lm) - {p}"
  let "?parents" = "parents d (base {d} p) p"
  let ?b = "base {0..<d} p"
  have "d < dm" using \<open>Suc d \<le> dm\<close> by auto

  have p_spg: "p \<in> grid (start dm) {0..<dm}" and p_spg': "p \<in> sparsegrid' dm" and "level p < lm" using \<open>p \<in> sparsegrid dm lm\<close>
    unfolding sparsegrid_def and sparsegrid'_def and lgrid_def by auto
  have p'_in_spg: "!! p'. p' \<in> ?subgrid d p \<Longrightarrow> p' \<in> sparsegrid dm lm"
    using base_grid[OF p_spg'] unfolding sparsegrid'_def sparsegrid_def lgrid_def by auto

  from baseE[OF p_spg', where ds="{0..<d}"]
  have "?b \<in> grid (start dm) {d..<dm}" and p_bgrid: "p \<in> grid ?b {0..<d}" by auto
  hence "d < length ?b" using \<open>Suc d \<le> dm\<close> by auto
  have "p ! d = ?b ! d" using base_out[OF _ _ p_spg'] \<open>Suc d \<le> dm\<close> by auto

  have "length p = dm" using \<open>p \<in> sparsegrid dm lm\<close> unfolding sparsegrid_def lgrid_def by auto
  hence "d < length p" using \<open>d < dm\<close> by auto

  have "updown' dm lm d (up dm lm d \<alpha>) p =
    (\<Sum> p' \<in> ?subgrid d p. (up dm lm d \<alpha>) p' * (?prod d p' p))"
    using Suc by auto
  also have "\<dots> = (\<Sum> p' \<in> ?subgrid d p. (\<Sum> p'' \<in> ?leafs p'. \<alpha> p'' * ?prod (Suc d) p'' p))"
  proof (intro sum.cong refl)
    fix p' assume "p' \<in> ?subgrid d p"
    hence "d < length p'" unfolding lgrid_def using base_length[OF p_spg'] \<open>Suc d \<le> dm\<close> by auto

    have "up dm lm d \<alpha> p' * ?prod d p' p =
      (\<Sum> p'' \<in> ?leafs p'. \<alpha> p'' * l2_\<phi> (p'' ! d) (p' ! d)) * ?prod d p' p"
      using \<open>p' \<in> ?subgrid d p\<close> up \<open>Suc d \<le> dm\<close> p'_in_spg by auto
    also have "\<dots> = (\<Sum> p'' \<in> ?leafs p'. \<alpha> p'' * l2_\<phi> (p'' ! d) (p' ! d) * ?prod d p' p)"
      using sum_distrib_right by auto
    also have "\<dots> = (\<Sum> p'' \<in> ?leafs p'. \<alpha> p'' * ?prod (Suc d) p'' p)"
    proof (intro sum.cong refl)
      fix p'' assume "p'' \<in> ?leafs p'"
      have "?prod d p' p = ?prod d p'' p"
      proof (intro prod.cong refl)
        fix d' assume "d' \<in> {0..<d}"
        hence d_lt_p: "d' < length p'" and d'_not_d: "d' \<notin> {d}" using \<open>d < length p'\<close> by auto
        hence "p' ! d' = p'' ! d'" using \<open>p'' \<in> ?leafs p'\<close> grid_invariant[OF d_lt_p d'_not_d] unfolding lgrid_def by auto
        thus "l2_\<phi> (p'!d') (p!d') = l2_\<phi> (p''!d') (p!d')" by auto
      qed
      moreover have "p' ! d = p ! d"
        using \<open>p' \<in> ?subgrid d p\<close> and grid_invariant[OF \<open>d < length ?b\<close>, where p=p' and ds="{0..<d}"] unfolding lgrid_def \<open>p ! d = ?b ! d\<close> by auto
      ultimately have "l2_\<phi> (p'' ! d) (p' ! d) * ?prod d p' p =
        l2_\<phi> (p'' ! d) (p ! d) * ?prod d p'' p" by auto
      also have "\<dots> = ?prod (Suc d) p'' p"
      proof -
        have "insert d {0..<d} = {0..<Suc d}" by auto
        moreover from prod.insert
        have "prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) (insert d {0..<d}) =
          (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) d * prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) {0..<d}"
          by auto
        ultimately show ?thesis by auto
      qed
      finally show "\<alpha> p'' * l2_\<phi> (p'' ! d) (p' ! d) * ?prod d p' p = \<alpha> p'' * ?prod (Suc d) p'' p" by auto
    qed
    finally show "(up dm lm d \<alpha>) p' * (?prod d p' p) = (\<Sum> p'' \<in> ?leafs p'. \<alpha> p'' * ?prod (Suc d) p'' p)" by auto
  qed
  also have "\<dots> = (\<Sum> (p', p'') \<in> Sigma (?subgrid d p) (\<lambda>p'. (?leafs p')). (\<alpha> p'') * (?prod (Suc d) p'' p))"
    by (rule sum.Sigma, auto simp add: lgrid_finite)
  also have "\<dots> = (\<Sum> p''' \<in> (\<Union> p' \<in> ?subgrid d p. (\<Union> p'' \<in> ?leafs p'. { (p', p'') })).
    (((\<lambda> p''. \<alpha> p'' * ?prod (Suc d) p'' p) o snd) p''') )" unfolding Sigma_def by (rule sum.cong[OF refl], auto)
  also have "\<dots> = (\<Sum> p'' \<in> snd ` (\<Union> p' \<in> ?subgrid d p. (\<Union> p'' \<in> ?leafs p'. { (p', p'') })).
    \<alpha> p'' * (?prod (Suc d) p'' p))" unfolding lgrid_def
    by (rule sum.reindex[symmetric],
        rule subset_inj_on[OF grid_grid_inj_on[OF ivl_disj_int(15)[where l=0 and m="d" and u="d"], where b="?b"]])
       auto
  also have "\<dots> = (\<Sum> p'' \<in> (\<Union> p' \<in> ?subgrid d p. (\<Union> p'' \<in> ?leafs p'. snd ` { (p', p'') })).
    \<alpha> p'' * (?prod (Suc d) p'' p))" by (auto simp only: image_UN)
  also have "\<dots> = (\<Sum> p'' \<in> (\<Union> p' \<in> ?subgrid d p. ?leafs p'). \<alpha> p'' * (?prod (Suc d) p'' p))" by auto
  finally have up_part: "updown' dm lm d (up dm lm d \<alpha>) p = (\<Sum> p'' \<in> (\<Union> p' \<in> ?subgrid d p. ?leafs p'). \<alpha> p'' * (?prod (Suc d) p'' p))" .

  have "down dm lm d (updown' dm lm d \<alpha>) p = (\<Sum> p' \<in> ?parents. (updown' dm lm d \<alpha> p') * l2_\<phi> (p ! d) (p' ! d))"
    using \<open>Suc d \<le> dm\<close> and down and \<open>p \<in> sparsegrid dm lm\<close> by auto
  also have "\<dots> = (\<Sum> p' \<in> ?parents. \<Sum> p'' \<in> ?subgrid d p'. \<alpha> p'' * ?prod (Suc d) p'' p)"
  proof (rule sum.cong[OF refl])
    fix p' let ?b' = "base {d} p"
    assume "p' \<in> ?parents"
    hence p_lgrid: "p' \<in> lgrid ?b' {d} (level p + 1)" using parents_subset_lgrid by auto
    hence "p' \<in> sparsegrid dm lm" and p'_spg': "p' \<in> sparsegrid' dm" using \<open>level p < lm\<close> base_grid[OF p_spg'] unfolding sparsegrid_def lgrid_def sparsegrid'_def by auto
    hence "length p' = dm" unfolding sparsegrid_def lgrid_def by auto
    hence "d < length p'" using \<open>Suc d \<le> dm\<close> by auto

    from p_lgrid have p'_grid: "p' \<in> grid ?b' {d}" unfolding lgrid_def by auto

    have "(updown' dm lm d \<alpha> p') * l2_\<phi> (p ! d) (p' !  d) = (\<Sum> p'' \<in> ?subgrid d p'. \<alpha> p'' * ?prod d p'' p') * l2_\<phi> (p ! d) (p' ! d)"
      using \<open>p' \<in> sparsegrid dm lm\<close> Suc by auto
    also have "\<dots> = (\<Sum> p'' \<in> ?subgrid d p'. \<alpha> p'' * ?prod d p'' p' * l2_\<phi> (p ! d) (p' ! d))"
      using sum_distrib_right by auto
    also have "\<dots> = (\<Sum> p'' \<in> ?subgrid d p'. \<alpha> p'' * ?prod (Suc d) p'' p)"
    proof (rule sum.cong[OF refl])
      fix p'' assume "p'' \<in> ?subgrid d p'"

      have "?prod d p'' p' = ?prod d p'' p"
      proof (rule prod.cong, rule refl)
        fix d' assume "d' \<in> {0..<d}"
        hence "d' < dm" and "d' \<notin> {d}" using \<open>Suc d \<le> dm\<close> by auto
        from grid_base_out[OF this p_spg' p'_grid]
        show "l2_\<phi> (p''!d') (p'!d') = l2_\<phi> (p''!d') (p!d')" by auto
      qed
      moreover
      have "l2_\<phi> (p ! d) (p' ! d) = l2_\<phi> (p'' ! d) (p ! d)"
      proof -
        have "d < dm" and "d \<notin> {0..<d}" using \<open>Suc d \<le> dm\<close> base_length p'_spg' by auto
        from grid_base_out[OF this p'_spg'] \<open>p'' \<in> ?subgrid d p'\<close>[unfolded lgrid_def]
        show ?thesis using l2_commutative by auto
      qed
      moreover have "?prod d p'' p * l2_\<phi> (p'' ! d) (p ! d) = ?prod (Suc d) p'' p"
      proof -
        have "insert d {0..<d} = {0..<Suc d}" by auto
        moreover from prod.insert
        have "(\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) d * prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) {0..<d} =
          prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) (insert d {0..<d})"
          by auto
        hence "(prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) {0..<d}) * (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) d =
          prod (\<lambda> d'. l2_\<phi> (p'' ! d') (p ! d')) (insert d {0..<d})"
          by auto
        ultimately show ?thesis by auto
      qed
      ultimately show "\<alpha> p'' * ?prod d p'' p' * l2_\<phi> (p ! d) (p' ! d) = \<alpha> p'' * ?prod (Suc d) p'' p" by auto
    qed
    finally show "(updown' dm lm d \<alpha> p') * l2_\<phi> (p ! d) (p' ! d) = (\<Sum> p'' \<in> ?subgrid d p'. \<alpha> p'' * ?prod (Suc d) p'' p)" by auto
  qed
  also have "\<dots> = (\<Sum> (p', p'') \<in> (Sigma ?parents (?subgrid d)). \<alpha> p'' * ?prod (Suc d) p'' p)"
    by (rule sum.Sigma, auto simp add: parents_finite lgrid_finite)
  also have "\<dots> = (\<Sum> p''' \<in> (\<Union> p' \<in> ?parents. (\<Union> p'' \<in> ?subgrid d p'. { (p', p'') })).
    ( ((\<lambda> p''. \<alpha> p'' * ?prod (Suc d) p'' p) o snd) p''') )" unfolding Sigma_def by (rule sum.cong[OF refl], auto)
  also have "\<dots> = (\<Sum> p'' \<in> snd ` (\<Union> p' \<in> ?parents. (\<Union> p'' \<in> ?subgrid d p'. { (p', p'') })). \<alpha> p'' * (?prod (Suc d) p'' p))"
  proof (rule sum.reindex[symmetric], rule inj_onI)
    fix x y
    assume "x \<in> (\<Union>p'\<in>parents d (base {d} p) p. \<Union>p''\<in>lgrid (base {0..<d} p') {0..<d} lm. {(p', p'')})"
    hence x_snd: "snd x \<in> grid (base {0..<d} (fst x)) {0..<d}" and "fst x \<in> grid (base {d} p) {d}" and "p \<in> grid (fst x) {d}"
      unfolding parents_def lgrid_def by auto
    hence x_spg: "fst x \<in> sparsegrid' dm" using base_grid[OF p_spg'] by auto

    assume "y \<in> (\<Union>p'\<in>parents d (base {d} p) p. \<Union>p''\<in>lgrid (base {0..<d} p') {0..<d} lm. {(p', p'')})"
    hence y_snd: "snd y \<in> grid (base {0..<d} (fst y)) {0..<d}" and "fst y \<in> grid (base {d} p) {d}" and "p \<in> grid (fst y) {d}"
      unfolding parents_def lgrid_def by auto
    hence y_spg: "fst y \<in> sparsegrid' dm" using base_grid[OF p_spg'] by auto
    hence "length (fst y) = dm" unfolding sparsegrid'_def by auto

    assume "snd x = snd y"
    have "fst x = fst y"
    proof (rule nth_equalityI)
      show l_eq: "length (fst x) = length (fst y)" using grid_length[OF \<open>p \<in> grid (fst y) {d}\<close>] grid_length[OF \<open>p \<in> grid (fst x) {d}\<close>]
        by auto
      show "fst x ! i = fst y ! i" if "i < length (fst x)" for i
      proof -
        have "i < length (fst y)" and "i < dm" using that l_eq and \<open>length (fst y) = dm\<close> by auto
        show "fst x ! i = fst y ! i"
        proof (cases "i = d")
          case False hence "i \<notin> {d}" by auto
          with grid_invariant[OF \<open>i < length (fst x)\<close> this \<open>p \<in> grid (fst x) {d}\<close>]
            grid_invariant[OF \<open>i < length (fst y)\<close> this \<open>p \<in> grid (fst y) {d}\<close>]
          show ?thesis by auto
        next
          case True with grid_base_out[OF \<open>i < dm\<close> _ y_spg y_snd] grid_base_out[OF \<open>i < dm\<close> _ x_spg x_snd]
          show ?thesis using \<open>snd x = snd y\<close> by auto
        qed
      qed
    qed
    show "x = y" using prod_eqI[OF \<open>fst x = fst y\<close> \<open>snd x = snd y\<close>] .
  qed
  also have "\<dots> = (\<Sum> p'' \<in> (\<Union> p' \<in> ?parents. (\<Union> p'' \<in> ?subgrid d p'. snd ` { (p', p'') })).
    \<alpha> p'' * (?prod (Suc d) p'' p))" by (auto simp only: image_UN)
  also have "\<dots> = (\<Sum> p'' \<in> (\<Union> p' \<in> ?parents. ?subgrid d p'). \<alpha> p'' * ?prod (Suc d) p'' p)" by auto
  finally have down_part: "down dm lm d (updown' dm lm d \<alpha>) p =
    (\<Sum> p'' \<in> (\<Union> p' \<in> ?parents. ?subgrid d p'). \<alpha> p'' * ?prod (Suc d) p'' p)" .

  have "updown' dm lm (Suc d) \<alpha> p =
    (\<Sum> p'' \<in> (\<Union> p' \<in> ?subgrid d p. ?leafs p'). \<alpha> p'' * ?prod (Suc d) p'' p) +
    (\<Sum> p'' \<in> (\<Union> p' \<in> ?parents. ?subgrid d p'). \<alpha> p'' * ?prod (Suc d) p'' p)"
    unfolding sum_vector_def updown'.simps down_part and up_part ..
  also have "\<dots> = (\<Sum> p'' \<in> (\<Union> p' \<in> ?subgrid d p. ?leafs p') \<union> (\<Union> p' \<in> ?parents. ?subgrid d p'). \<alpha> p'' * ?prod (Suc d) p'' p)"
  proof (rule sum.union_disjoint[symmetric], simp add: lgrid_finite, simp add: lgrid_finite parents_finite,
         rule iffD2[OF disjoint_iff_not_equal], rule ballI, rule ballI)
    fix x y
    assume "x \<in> (\<Union> p' \<in> ?subgrid d p. ?leafs p')"
    then obtain px where "px \<in> grid (base {0..<d} p) {0..<d}" and "x \<in> grid px {d}" and "x \<noteq> px" unfolding lgrid_def by auto
    with grid_base_out[OF _ _ p_spg' this(1)] \<open>Suc d \<le> dm\<close> base_length[OF p_spg'] grid_level_d
    have "lv px d < lv x d" and "px ! d = p ! d" by auto
    hence "lv p d < lv x d" unfolding lv_def by auto
    moreover
    assume "y \<in> (\<Union> p' \<in> ?parents. ?subgrid d p')"
    then obtain py where y_grid: "y \<in> grid (base {0..<d} py) {0..<d}" and "py \<in> ?parents" unfolding lgrid_def by auto
    hence "py \<in> grid (base {d} p) {d}" and "p \<in> grid py {d}" unfolding parents_def by auto
    hence py_spg: "py \<in> sparsegrid' dm" using base_grid[OF p_spg'] by auto
    have "y ! d = py ! d" using grid_base_out[OF _ _ py_spg y_grid] \<open>Suc d \<le> dm\<close> by auto
    hence "lv y d \<le> lv p d" using grid_single_level[OF \<open>p \<in> grid py {d}\<close>] \<open>Suc d \<le> dm\<close> and sparsegrid'_length[OF py_spg] unfolding lv_def by auto
    ultimately
    show "x \<noteq> y" by auto
  qed
  also have "\<dots> = (\<Sum> p' \<in> ?subgrid (Suc d) p. \<alpha> p' * ?prod (Suc d) p' p)" (is "(\<Sum> x \<in> ?in. ?F x) = (\<Sum> x \<in> ?out. ?F x)")
  proof (rule sum.mono_neutral_left, simp add: lgrid_finite)
    show "?in \<subseteq> ?out" (is "?children \<union> ?siblings \<subseteq> _")
    proof (rule subsetI)
      fix x assume "x \<in> ?in"
      show "x \<in> ?out"
      proof (cases "x \<in> ?children")
        case False hence "x \<in> ?siblings" using \<open>x \<in> ?in\<close> by auto
        then obtain px where "px \<in> parents d (base {d} p) p" and "x \<in> lgrid (base {0..<d} px) {0..<d} lm" by auto
        hence "level x < lm" and "px \<in> grid (base {d} p) {d}" and "x \<in> grid (base {0..<d} px) {0..<d}" and "{d} \<union> {0..<d} = {0..<Suc d}" unfolding lgrid_def parents_def by auto
        with grid_base_union[OF p_spg' this(2) this(3)] show ?thesis unfolding lgrid_def by auto
      next
        have d_eq: "{0..<Suc d} \<union> {d} = {0..<Suc d}" by auto
        case True
        then obtain px where "px \<in> ?subgrid d p" and "x \<in> lgrid px {d} lm" and "x \<noteq> px" by auto
        hence "px \<in> grid (base {0..<d} p) {0..<d}" and "x \<in> grid px {d}" and "level x < lm" and "{d} \<union> {0..<d} = {0..<Suc d}" unfolding lgrid_def by auto
        from grid_base_dim_add[OF _ p_spg' this(1)]
        have "px \<in> grid (base {0..<Suc d} p) {0..<Suc d}" by auto
        from grid_transitive[OF \<open>x \<in> grid px {d}\<close> this]
        show ?thesis unfolding lgrid_def using \<open>level x < lm\<close> d_eq by auto
      qed
    qed

    show "\<forall> x \<in> ?out - ?in. ?F x = 0"
    proof
      fix x assume "x \<in> ?out - ?in"

      hence "x \<in> ?out" and up_ps': "!! p'. p' \<in> ?subgrid d p \<Longrightarrow> x \<notin> lgrid p' {d} lm - {p'}"
        and down_ps': "!! p'. p' \<in> ?parents \<Longrightarrow> x \<notin> ?subgrid d p'" by auto
      hence x_eq: "x \<in> grid (base {0..<Suc d} p) {0..<Suc d}" and "level x < lm" unfolding lgrid_def by auto
      hence up_ps: "!! p'. p' \<in> ?subgrid d p \<Longrightarrow> x \<notin> grid p' {d} - {p'}" and
        down_ps: "!! p'. p' \<in> ?parents \<Longrightarrow> x \<notin> grid (base {0..<d} p') {0..<d}"
        using up_ps' down_ps' unfolding lgrid_def by auto

      have ds_eq: "{0..<Suc d} = {0..<d} \<union> {d}" by auto
      have "x \<notin> grid (base {0..<d} p) {0..<Suc d} - grid (base {0..<d} p) {0..<d}"
      proof
        assume "x \<in> grid (base {0..<d} p) {0..<Suc d} - grid (base {0..<d} p) {0..<d}"
        hence "x \<in> grid (base {0..<d} p) ({d} \<union> {0..<d})" and x_ngrid: "x \<notin> grid (base {0..<d} p) {0..<d}" using ds_eq by auto
        from grid_split[OF this(1)] obtain px where px_grid: "px \<in> grid (base {0..<d} p) {0..<d}" and "x \<in> grid px {d}" by auto
        from grid_level[OF this(2)] \<open>level x < lm\<close> have "level px < lm" by auto
        hence "px \<in> ?subgrid d p" using px_grid unfolding lgrid_def by auto
        hence "x \<notin> grid px {d} - {px}" using up_ps by auto
        moreover have "x \<noteq> px" proof (rule ccontr) assume "\<not> x \<noteq> px" with px_grid and x_ngrid show False by auto qed
        ultimately show False using \<open>x \<in> grid px {d}\<close> by auto
      qed
      moreover have "p \<in> ?parents" unfolding parents_def using baseE(2)[OF p_spg'] by auto
      hence "x \<notin> grid (base {0..<d} p) {0..<d}" by (rule down_ps)
      ultimately have x_ngrid: "x \<notin> grid (base {0..<d} p) {0..<Suc d}" by auto

      have x_spg: "x \<in> sparsegrid' dm" using base_grid[OF p_spg'] x_eq by auto
      hence "length x = dm" using grid_length by auto

      let ?bx = "base {0..<d} x" and ?bp = "base {0..<d} p" and ?bx1 = "base {d} x" and ?bp1 = "base {d} p" and ?px = "p[d := x ! d]"

      have x_nochild_p: "?bx \<notin> grid ?bp {d}"
      proof (rule ccontr)
        assume "\<not> base {0..<d} x \<notin> grid (base {0..<d} p) {d}"
        hence "base {0..<d} x \<in> grid (base {0..<d} p) {d}" by auto
        from grid_transitive[OF baseE(2)[OF x_spg] this]
        have "x \<in> grid (base {0..<d} p) {0..<Suc d}" using ds_eq by auto
        thus False using x_ngrid by auto
      qed

      have "d < length ?bx" and "d < length ?bp" and "d < length ?bx1" and "d < length ?bp1" using base_length[OF x_spg] base_length[OF p_spg'] and \<open>d < dm\<close> by auto
      have p_nochild_x: "?bp \<notin> grid ?bx {d}" (is "?assm")
      proof (rule ccontr)
        have ds: "{0..<d} \<union> {0..<Suc d} = {d} \<union> {0..<d}" by auto
        have d_sub: "{d} \<subseteq> {0..<Suc d}" by auto
        assume "\<not> ?assm" hence b_in_bx: "base {0..<d} p \<in> grid ?bx {d}" by auto

        have "d \<notin> {0..<d}" and "d \<in> {d}" by auto
        from grid_replace_dim[OF \<open>d < length ?bx\<close> \<open>d < length p\<close> grid.Start[where b=p and ds="{d}"] b_in_bx]
        have "p \<in> grid ?px {d}" unfolding base_out[OF \<open>d < dm\<close> \<open>d \<notin> {0..<d}\<close> x_spg] base_out[OF \<open>d < dm\<close> \<open>d \<notin> {0..<d}\<close> p_spg'] list_update_id .
        moreover
        from grid_replace_dim[OF \<open>d < length ?bx1\<close> \<open>d < length ?bp1\<close> baseE(2)[OF p_spg', where ds="{d}"] baseE(2)[OF x_spg, where ds="{d}"]]
        have "?px \<in> grid ?bp1 {d}" unfolding base_in[OF \<open>d < dm\<close> \<open>d \<in> {d}\<close> x_spg] unfolding base_in[OF \<open>d < dm\<close> \<open>d \<in> {d}\<close> p_spg', symmetric] list_update_id .
        ultimately
        have "x \<notin> grid (base {0..<d} ?px) {0..<d}" using down_ps[unfolded parents_def, where p'="?px"] by (auto simp only:)
        moreover
        have "base {0..<d} ?px = ?bx"
        proof (rule nth_equalityI)
          from \<open>?px \<in> grid ?bp1 {d}\<close> have px_spg: "?px \<in> sparsegrid' dm" using base_grid[OF p_spg'] by auto
          from base_length[OF this] base_length[OF x_spg] show l_eq: "length (base {0..<d} ?px) = length ?bx"  by auto
          show "base {0..<d} ?px ! i = ?bx ! i" if "i < length (base {0..<d} ?px)" for i
          proof -
            have "i < length ?bx" and "i < dm" using that l_eq and base_length[OF px_spg] by auto
            show "base {0..<d} ?px ! i = ?bx ! i"
            proof (cases "i < d")
              case True hence "i \<in> {0..<d}" by auto
              from base_in[OF \<open>i < dm\<close> this] show ?thesis using px_spg x_spg by auto
            next
              case False hence "i \<notin> {0..<d}" by auto
              have "?px ! i = x ! i"
              proof (cases "i > d")
                have i_le: "i < length (base {0..<Suc d} p)" using base_length[OF p_spg'] and \<open>i < dm\<close> by auto
                case True hence "i \<notin> {0..<Suc d}" by auto
                from grid_invariant[OF i_le this x_eq] base_out[OF \<open>i < dm\<close> this p_spg']
                show ?thesis using list_update_id and True by auto
              next
                case False hence "d = i" using \<open>\<not> i < d\<close> by auto
                thus ?thesis unfolding \<open>d = i\<close> using \<open>i < dm\<close> \<open>length p = dm\<close> nth_list_update_eq by auto
              qed
              thus ?thesis using base_out[OF \<open>i < dm\<close> \<open>i \<notin> {0..<d}\<close> px_spg] base_out[OF \<open>i < dm\<close> \<open>i \<notin> {0..<d}\<close> x_spg] by auto
            qed
          qed
        qed
        ultimately have "x \<notin> grid ?bx {0..<d}" by auto
        thus False using baseE(2)[OF x_spg] by auto
      qed

      have x_grid: "?bx \<in> grid (base {0..<Suc d} p) {d}" using grid_shift_base[OF _ p_spg' x_eq[unfolded ds_eq]] unfolding ds_eq by auto

      have p_grid: "?bp \<in> grid (base {0..<Suc d} p) {d}" using grid_shift_base[OF _ p_spg' baseE(2)[OF p_spg', where ds="{0..<d} \<union> {d}"]] unfolding ds_eq by auto

      have "l2_\<phi> (?bp ! d) (?bx ! d) = 0"
      proof (cases "lv ?bx d \<le> lv ?bp d")
        case True from l2_disjoint[OF _ x_grid p_grid p_nochild_x this] \<open>d < dm\<close> and base_length[OF p_spg']
        show ?thesis by auto
      next
        case False hence "lv ?bx d \<ge> lv ?bp d" by auto
        from l2_disjoint[OF _ p_grid x_grid x_nochild_p this] \<open>d < dm\<close> and base_length[OF p_spg']
        show ?thesis by (auto simp: l2_commutative)
      qed
      hence "l2_\<phi> (p ! d) (x ! d) = 0" using base_out[OF \<open>d < dm\<close>] p_spg' x_spg by auto
      hence "\<exists> d \<in> {0..<Suc d}. l2_\<phi> (p ! d) (x ! d) = 0" by auto
      from prod_zero[OF _ this]
      show "?F x = 0" by (auto simp: l2_commutative)
    qed
  qed
  finally show ?case .
qed

theorem updown:
  assumes p_spg: "p \<in> sparsegrid dm lm"
  shows "updown dm lm \<alpha> p = (\<Sum> p' \<in> sparsegrid dm lm. \<alpha> p' * l2 p' p)"
proof -
  have "p \<in> sparsegrid' dm" using p_spg unfolding sparsegrid_def sparsegrid'_def lgrid_def by auto
  have "!!p'. p' \<in> lgrid (base {0..<dm} p) {0..<dm} lm \<Longrightarrow> length p' = dm"
  proof -
    fix p' assume "p' \<in> lgrid (base {0..<dm} p) {0..<dm} lm"
    with base_grid[OF \<open>p \<in> sparsegrid' dm\<close>] have "p' \<in> sparsegrid' dm" unfolding lgrid_def by auto
    thus "length p' = dm"  by auto
  qed
  thus ?thesis
    unfolding updown_def sparsegrid_def base_start_eq[OF p_spg]
    using updown'[OF _ p_spg, where d=dm] p_spg[unfolded sparsegrid_def lgrid_def]
    by (auto simp: atLeast0LessThan p_spg[THEN sparsegrid_length] l2_eq)
qed

corollary
  fixes \<alpha>
  assumes p: "p \<in> sparsegrid dm lm"
  defines "f\<^sub>\<alpha> \<equiv> \<lambda>x. (\<Sum>p\<in>sparsegrid dm lm. \<alpha> p * \<Phi> p x)"
  shows "updown dm lm \<alpha> p = (\<integral>x. f\<^sub>\<alpha> x * \<Phi> p x \<partial>(\<Pi>\<^sub>M d\<in>{..<dm}. lborel))"
  unfolding updown[OF p] l2_def f\<^sub>\<alpha>_def sum_distrib_right
  apply (intro has_bochner_integral_integral_eq[symmetric] has_bochner_integral_sum)
  apply (subst mult.assoc)
  apply (intro has_bochner_integral_mult_right)
  apply (simp add: sparsegrid_length)
  apply (rule has_bochner_integral_integrable)
  using p
  apply (simp add: sparsegrid_length \<Phi>_def prod.distrib[symmetric])
proof (rule product_sigma_finite.product_integrable_prod)
  show "product_sigma_finite (\<lambda>d. lborel)" ..
qed (auto intro: integrable_\<phi>2)

end

