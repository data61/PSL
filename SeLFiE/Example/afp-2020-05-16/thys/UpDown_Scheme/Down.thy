section \<open> Down part \<close>

theory Down
imports Triangular_Function UpDown_Scheme
begin

lemma sparsegrid'_parents:
  assumes b: "b \<in> sparsegrid' dm" and p': "p' \<in> parents d b p"
  shows "p' \<in> sparsegrid' dm"
  using assms parents_def sparsegrid'I by auto

lemma down'_\<beta>: "\<lbrakk> d < length b ; l + level b = lm ; b \<in> sparsegrid' dm ; p \<in> sparsegrid' dm \<rbrakk> \<Longrightarrow>
  down' d l b fl fr \<alpha> p = (if p \<in> lgrid b {d} lm
  then
    (fl + (fr - fl) / 2 * (real_of_int (ix p d) / 2^(lv p d - lv b d) - real_of_int (ix b d) + 1)) / 2 ^ (lv p d + 1) +
    (\<Sum> p' \<in> parents d b p. (\<alpha> p') * l2_\<phi> (p ! d) (p' ! d))
  else \<alpha> p)"
proof (induct l arbitrary: b \<alpha> fl fr p)
  case (Suc l)

  let ?l = "child b left d" and ?r = "child b right d"
  let ?result = "((fl + fr) / 4 + (1 / 3) * (\<alpha> b)) / 2 ^ (lv b d)"
  let ?fm = "(fl + fr) / 2 + (\<alpha> b)"
  let ?down_l = "down' d l (child b left d) fl ?fm (\<alpha>(b := ?result))"

  have "length b = dm" using \<open>b \<in> sparsegrid' dm\<close>
    unfolding sparsegrid'_def start_def by auto
  hence "d < dm" using \<open>d < length b\<close> by auto

  have "!!dir. d < length (child b dir d)" using \<open>d < length b\<close> by auto
  have "!!dir. l + level (child b dir d) = lm"
    using \<open>d < length b\<close> and \<open>Suc l + level b = lm\<close> and child_level by auto
  have "!!dir. (child b dir d) \<in> sparsegrid' dm"
    using \<open>b \<in> sparsegrid' dm\<close> and \<open>d < dm\<close> and sparsegrid'_def by auto
  note hyps = Suc.hyps[OF \<open>!! dir. d < length (child b dir d)\<close>
    \<open>!!dir. l + level (child b dir d) = lm\<close>
    \<open>!!dir. (child b dir d) \<in> sparsegrid' dm\<close>]

  show ?case
  proof (cases "p \<in> lgrid b {d} lm")
    case False
    moreover hence "p \<noteq> b" and "p \<notin> lgrid ?l {d} lm"
       and "p \<notin> lgrid ?r {d} lm" unfolding lgrid_def
      unfolding grid_partition[where p=b] using \<open>Suc l + level b = lm\<close> by auto
    ultimately show ?thesis
      unfolding down'.simps Let_def fun_upd_def hyps[OF \<open>p \<in> sparsegrid' dm\<close>]
      by auto
  next
    case True hence "level p < lm" and "p \<in> grid b {d}" unfolding lgrid_def by auto
    let ?lb = "lv b d"   and ?ib = "real_of_int (ix b d)"
    let ?lp   = "lv p d"  and ?ip   = "real_of_int (ix p d)"
    show ?thesis
    proof (cases "\<exists> dir. p \<in> grid (child b dir d){d}")
      case True
      obtain dir where p_grid: "p \<in> grid (child b dir d) {d}" using True by auto
      hence "p \<in> lgrid (child b dir d) {d} lm" using \<open>level p < lm\<close> unfolding lgrid_def by auto
      have "lv b d < lv p d" using child_lv[OF \<open>d < length b\<close>] and grid_single_level[OF p_grid \<open>d < length (child b dir d)\<close>] by auto

      let ?ch = "child b dir d"
      let ?ich = "child b (inv dir) d"

      show ?thesis
      proof (cases dir)
        case right
        hence "p \<in> lgrid ?r {d} lm" and "p \<in> grid ?r {d}"
          using \<open>p \<in> grid ?ch {d}\<close> and \<open>level p < lm\<close> unfolding lgrid_def by auto

        { fix p' fix fl fr x assume p': "p' \<in> parents d (child b right d) p"
          hence "p' \<in> grid (child b right d) {d}" unfolding parents_def by simp
          hence "p' \<notin> lgrid (child b left d) {d} lm" and "p' \<noteq> b"
            unfolding lgrid_def
            using grid_disjunct[OF \<open>d < length b\<close>] grid_not_child by auto

          from hyps[OF sparsegrid'_parents[OF \<open>child b right d \<in> sparsegrid' dm\<close>
                       p']] this
          have "down' d l (child b left d) fl fr (\<alpha>(b := x)) p' = \<alpha> p'" by auto }
        thus  ?thesis
          unfolding down'.simps Let_def hyps[OF \<open>p \<in> sparsegrid' dm\<close>]
            parent_sum[OF \<open>p \<in> grid ?r {d}\<close> \<open>d < length b\<close>]
            l2_child[OF \<open>d < length b\<close> \<open>p \<in> grid ?r {d}\<close>]
          using child_ix child_lv \<open>d < length b\<close> level_shift[OF \<open>lv b d < lv p d\<close>]
                sgn.simps \<open>p \<in> lgrid b {d} lm\<close> \<open>p \<in> lgrid ?r {d} lm\<close>
          by (auto simp add: algebra_simps diff_divide_distrib add_divide_distrib)
      next
        case left
        hence "p \<in> lgrid ?l {d} lm" and "p \<in> grid ?l {d}"
          using \<open>p \<in> grid ?ch {d}\<close> and \<open>level p < lm\<close> unfolding lgrid_def by auto
        hence "\<not> p \<in> lgrid ?r {d} lm"
          using grid_disjunct[OF \<open>d < length b\<close>] unfolding lgrid_def by auto
        { fix p' assume p': "p' \<in> parents d (child b left d) p"
          hence "p' \<in> grid (child b left d) {d}" unfolding parents_def by simp
          hence "p' \<noteq> b" using grid_not_child[OF \<open>d < length b\<close>] by auto }
        thus ?thesis
          unfolding down'.simps Let_def hyps[OF \<open>p \<in> sparsegrid' dm\<close>]
                    parent_sum[OF \<open>p \<in> grid ?l {d}\<close> \<open>d < length b\<close>]
                    l2_child[OF \<open>d < length b\<close> \<open>p \<in> grid ?l {d}\<close>] sgn.simps
                    if_P[OF \<open>p \<in> lgrid b {d} lm\<close>] if_P[OF \<open>p \<in> lgrid ?l {d} lm\<close>]
                    if_not_P[OF \<open>p \<notin> lgrid ?r {d} lm\<close>]
          using child_ix child_lv \<open>d < length b\<close> level_shift[OF \<open>lv b d < lv p d\<close>]
          by (auto simp add: algebra_simps diff_divide_distrib add_divide_distrib)
      qed
    next
      case False hence not_child: "!! dir. \<not> p \<in> grid (child b dir d) {d}" by auto
      hence "p = b" using grid_onedim_split[where ds="{}" and d=d and b=b] \<open>p \<in> grid b {d}\<close> unfolding grid_empty_ds[where b=b] by auto
      from not_child have lnot_child: "!! dir. \<not> p \<in> lgrid (child b dir d) {d} lm" unfolding lgrid_def by auto
      have result: "((fl + fr) / 4 + 1 / 3 * \<alpha> b) / 2 ^ lv b d = (fl + (fr - fl) / 2) / 2 ^ (lv b d + 1) + \<alpha> b * l2_\<phi> (b ! d) (b ! d)"
        by (auto simp: l2_same diff_divide_distrib add_divide_distrib times_divide_eq_left[symmetric] algebra_simps)
      show ?thesis
        unfolding down'.simps Let_def fun_upd_def hyps[OF \<open>p \<in> sparsegrid' dm\<close>] if_P[OF \<open>p \<in> lgrid b {d} lm\<close>] if_not_P[OF lnot_child] if_P[OF \<open>p = b\<close>]
        unfolding \<open>p = b\<close> parents_single unfolding result by auto
    qed
  qed
next
  case 0
  have "p \<notin> lgrid b {d} lm"
  proof (rule ccontr)
    assume "\<not> p \<notin> lgrid b {d} lm"
    hence "p \<in> grid b {d}" and "level p < lm" unfolding lgrid_def by auto
    moreover from grid_level[OF \<open>p \<in> grid b {d}\<close>] and \<open>0 + level b = lm\<close> have "lm \<le> level p" by auto
    ultimately show False by auto
  qed
  thus ?case unfolding down'.simps by auto
qed

lemma down: assumes "d < dm" and p: "p \<in> sparsegrid dm lm"
  shows "(down dm lm d \<alpha>) p = (\<Sum> p' \<in> parents d (base {d} p) p. (\<alpha> p') * l2_\<phi> (p ! d) (p' ! d))"
proof -
  let "?F d l p" = "down' d l p 0 0"
  let "?S x p p'" = "if p' \<in> parents d (base {d} p) p then x * l2_\<phi> (p ! d) (p' ! d) else 0"

  { fix p \<alpha> assume "p \<in> sparsegrid dm lm"
    from le_less_trans[OF grid_level sparsegridE(2)[OF this]]
    have "parents d (base {d} p) p \<subseteq>  lgrid (base {d} p) {d} lm"
      unfolding lgrid_def parents_def by auto
    hence "(\<Sum>p'\<in>lgrid (base {d} p) {d} lm. ?S (\<alpha> p') p p') =
      (\<Sum>p'\<in>parents d (base {d} p) p. \<alpha> p' * l2_\<phi> (p ! d) (p' ! d))"
      using lgrid_finite by (intro sum.mono_neutral_cong_right) auto
  } note sum_eq = this

  { fix l p b \<alpha>
    assume b: "b \<in> lgrid (start dm) ({0..<dm} - {d}) lm" and "l + level b = lm"
      and "p \<in> sparsegrid dm lm"
    hence b_spg: "b \<in> sparsegrid' dm" and p_spg: "p \<in> sparsegrid' dm" and
      "d < length b" and "level p < lm"
      using sparsegrid'_start sparsegrid_subset \<open>d < dm\<close> by auto
    have "?F d l b \<alpha> p = (if b = base {d} p then \<Sum>p'\<in>lgrid b {d} lm. ?S (\<alpha> p') p p' else \<alpha> p)"
    proof (cases "b = base {d} p")
      case True
      have "p \<in> lgrid (base {d} p) {d} lm"
        using baseE(2)[OF p_spg] and \<open>level p < lm\<close>
        unfolding lgrid_def by auto
      thus ?thesis unfolding if_P[OF True]
        unfolding True sum_eq[OF \<open>p \<in> sparsegrid dm lm\<close>]
        unfolding down'_\<beta>[OF \<open>d < length b\<close> \<open>l + level b = lm\<close> b_spg p_spg,
          unfolded True] by auto
    next
      case False
      have "p \<notin> lgrid b {d} lm"
      proof (rule ccontr)
        assume "\<not> ?thesis" hence "p \<in> grid b {d}" by auto
        from b this have "b = base {d} p" using baseI by auto
        thus False using False by simp
      qed
      thus ?thesis
        unfolding if_not_P[OF False]
        unfolding down'_\<beta>[OF \<open>d < length b\<close> \<open>l + level b = lm\<close> b_spg p_spg]
        by auto
    qed }
  from lift[OF \<open>d < dm\<close> \<open>p \<in> sparsegrid dm lm\<close>, where F = ?F and S = ?S, OF this]
  show ?thesis
    unfolding down_def
    unfolding sum_eq[OF p] by simp
qed

end
