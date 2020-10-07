section \<open> Up Part \<close>

theory Up
imports UpDown_Scheme Triangular_Function
begin

lemma up'_inplace:
  assumes p'_in: "p' \<notin> grid p ds" and "d \<in> ds"
  shows "snd (up' d l p \<alpha>) p' = \<alpha> p'"
  using p'_in
proof (induct l arbitrary: p \<alpha>)
  case (Suc l)
  let "?ch dir" = "child p dir d"
  let "?up dir \<alpha>" = "up' d l (?ch dir) \<alpha>"
  let "?upl" = "snd (?up left \<alpha>)"

  from contrapos_nn[OF \<open>p' \<notin> grid p ds\<close> grid_child[OF \<open>d \<in> ds\<close>]]
  have left: "p' \<notin> grid (?ch left) ds" and
       right: "p' \<notin> grid (?ch right) ds" by auto

  have "p \<noteq> p'" using grid.Start Suc.prems by auto
  with Suc.hyps[OF left, of \<alpha>] Suc.hyps[OF right, of ?upl]
  show ?case
    by (cases "?up left \<alpha>", cases "?up right ?upl", auto simp add: Let_def)
qed auto

lemma up'_fl_fr:
      "\<lbrakk> d < length p ; p = (child p_r right d) ; p = (child p_l left d) \<rbrakk>
       \<Longrightarrow> fst (up' d lm p \<alpha>) =
              (\<Sum> p' \<in> lgrid p {d} (lm + level p). (\<alpha> p') * l2_\<phi> (p' ! d) (p_r ! d),
               \<Sum> p' \<in> lgrid p {d} (lm + level p). (\<alpha> p') * l2_\<phi> (p' ! d) (p_l ! d))"
proof (induct lm arbitrary: p p_l p_r \<alpha>)
  case (Suc lm)
  note \<open>d < length p\<close>[simp]

  from child_ex_neighbour
  obtain pc_r pc_l
    where pc_r_def: "child p right d = child pc_r (inv right) d"
    and pc_l_def: "child p left d = child pc_l (inv left) d" by blast

  define pc where "pc dir = (case dir of right \<Rightarrow> pc_r | left \<Rightarrow> pc_l)" for dir
  { fix dir have "child p (inv dir) d = child (pc (inv dir)) dir d"
      by (cases dir, auto simp add: pc_def pc_r_def pc_l_def) } note pc_child = this
  { fix dir have "child p dir d = child (pc dir) (inv dir) d"
      by (cases dir, auto simp add: pc_def pc_r_def pc_l_def) } note pc_child_inv = this
  hence "!! dir. length (child p dir d) = length (child (pc dir) (inv dir) d)" by auto
  hence "!! dir. length p = length (pc dir)" by auto
  hence [simp]: "!! dir. d < length (pc dir)" by auto

  let ?l = "\<lambda>s. lm + level s"
  let ?C = "\<lambda>p p'. (\<alpha> p) * l2_\<phi> (p ! d) (p' ! d)"
  let ?sum' = "\<lambda>s p''. \<Sum> p' \<in> lgrid s {d} (Suc lm + level p). ?C p' p''"
  let ?sum = "\<lambda>s dir p. \<Sum> p' \<in> lgrid (child s dir d) {d} (?l (child s dir d)). ?C p' p"
  let ?ch = "\<lambda>dir. child p dir d"
  let ?f = "\<lambda>dir. ?sum p dir (pc dir)"
  let ?fm = "\<lambda>dir. ?sum p dir p"
  let ?result = "(?fm left + ?fm right + (\<alpha> p) / 2 ^ (lv p d) / 2) / 2"
  let ?up = "\<lambda>lm p \<alpha>. up' d lm p \<alpha>"

  define \<beta>l where "\<beta>l = snd (?up lm (?ch left) \<alpha>)"
  define \<beta>r where "\<beta>r = snd (?up lm (?ch right) \<beta>l)"

  define p_d where "p_d dir = (case dir of right \<Rightarrow> p_r | left \<Rightarrow> p_l)" for dir
  have p_d_child: "p = child (p_d dir) dir d" for dir
    using Suc.prems p_d_def by (cases dir) auto
  hence "\<And> dir. length p = length (child (p_d dir) dir d)" by auto
  hence "\<And> dir. d < length (p_d dir)" by auto

  { fix dir

    { fix p' assume "p' \<in> lgrid (?ch (inv dir)) {d} (?l (?ch (inv dir))) "
      hence "?C p' (pc (inv dir)) + (?C p' p) / 2 = ?C p' (p_d dir)"
        using l2_zigzag[OF _ p_d_child[of dir] _ pc_child[of dir]]
        by (cases dir) (auto simp add: algebra_simps) }
    hence inv_dir_sum: "?sum p (inv dir) (pc (inv dir)) + (?sum p (inv dir) p) / 2
      = ?sum p (inv dir) (p_d dir)"
      by (auto simp add: sum.distrib[symmetric] sum_divide_distrib)

    have "?sum p dir p / 2 = ?sum p dir (p_d dir)"
      using l2_down2[OF _ _ \<open>p = child (p_d dir) dir d\<close>]
      by (force intro!: sum.cong simp add: sum_divide_distrib)
    moreover
    have "?C p (p_d dir) = (\<alpha> p) / 2 ^ (lv p d) / 4"
      using l2_child[OF \<open>d < length (p_d dir)\<close>, of p dir "{d}"] p_d_child[of dir]
      \<open>d < length (p_d dir)\<close> child_lv child_ix grid.Start[of p "{d}"]
      by (cases dir) (auto simp add: add_divide_distrib field_simps)
    ultimately
    have "?sum' p (p_d dir) =
      ?sum p (inv dir) (pc (inv dir)) +
      (?sum p (inv dir) p) / 2 + ?sum p dir p / 2 + (\<alpha> p) / 2 ^ (lv p d) / 4"
      using lgrid_sum[where b=p] and child_level and inv_dir_sum
      by (cases dir) auto
    hence "?sum p (inv dir) (pc (inv dir)) + ?result = ?sum' p (p_d dir)"
      by (cases dir) auto }
  note this[of left] this[of right]
  moreover
  note eq = up'_inplace[OF grid_not_child[OF \<open>d < length p\<close>], of d "{d}" lm]
  { fix p' assume "p' \<in> lgrid (?ch right) {d} (lm + level (?ch right))"
    with grid_disjunct[of d p] up'_inplace[of p' "?ch left" "{d}" d lm \<alpha>] \<beta>l_def
    have "\<beta>l p' = \<alpha> p'" by auto }
  hence "fst (?up (Suc lm) p \<alpha>) = (?f left + ?result, ?f right + ?result)"
    using \<beta>l_def pc_child_inv[of left] pc_child_inv[of right]
      Suc.hyps[of "?ch left" "pc left" p \<alpha>] eq[of left \<alpha>]
      Suc.hyps[of "?ch right" p "pc right" \<beta>l] eq[of right \<beta>l]
    by (cases "?up lm (?ch left) \<alpha>", cases "?up lm (?ch right) \<beta>l") (simp add: Let_def)
  ultimately show ?case by (auto simp add: p_d_def)
next
  case 0
  show ?case by simp
qed

lemma up'_\<beta>:
  "\<lbrakk> d < length b ; l + level b = lm ; b \<in> sparsegrid' dm ; p \<in> sparsegrid' dm \<rbrakk>
   \<Longrightarrow>
   (snd (up' d l b \<alpha>)) p =
     (if p \<in> lgrid b {d} lm
      then \<Sum> p' \<in> (lgrid p {d} lm) - {p}. \<alpha> p' * l2_\<phi> (p' ! d) (p ! d)
      else \<alpha> p)"
  (is "\<lbrakk> _ ; _ ; _ ; _ \<rbrakk> \<Longrightarrow> (?goal l b p \<alpha>)")
proof (induct l arbitrary: b p \<alpha>)
  case (Suc l)

  let ?l = "child b left d" and ?r = "child b right d"
  obtain p_l where p_l_def: "?r = child p_l left d" using child_ex_neighbour[where dir=right] by auto
  obtain p_r where p_r_def: "?l = child p_r right d" using child_ex_neighbour[where dir=left] by auto

  let ?ul = "up' d l ?l \<alpha>"
  let ?ur = "up' d l ?r (snd ?ul)"

  let "?C p'" = "\<alpha> p' * l2_\<phi> (p' ! d) (p ! d)"
  let "?s s" = "\<Sum> p' \<in> (lgrid s {d} lm). ?C p'"

  from \<open>b \<in> sparsegrid' dm\<close> have "length b = dm" unfolding sparsegrid'_def start_def
    by auto
  hence "d < dm" using \<open>d < length b\<close> by auto

  { fix p' assume "p' \<in> grid ?r {d}"
    hence "p' \<notin> grid ?l {d}"
      using grid_disjunct[OF \<open>d < length b\<close>] by auto
    hence "snd ?ul p' = \<alpha> p'" using up'_inplace by auto
  } note eq = this

  show "?goal (Suc l) b p \<alpha>"
  proof (cases "p = b")
    case True

    let "?C p'" = "\<alpha> p' * l2_\<phi> (p' ! d) (b ! d)"
    let "?s s" = "\<Sum> p' \<in> (lgrid s {d} lm). ?C p'"

    have "d < length ?l" using \<open>d < length b\<close> by auto
    from up'_fl_fr[OF this p_r_def]
    have fml: "snd (fst ?ul) = (\<Sum> p' \<in> lgrid ?l {d} (l + level ?l). ?C p')" by simp

    have "d < length ?r" using \<open>d < length b\<close> by auto
    from up'_fl_fr[OF this _ p_l_def, where \<alpha>="snd ?ul"]
    have fmr: "fst (fst ?ur) = (\<Sum> p' \<in> lgrid ?r {d} (l + level ?r).
                                ((snd ?ul) p') * l2_\<phi> (p' ! d) (b ! d))" by simp

    have "level b < lm" using \<open>Suc l + level b = lm\<close> by auto
    hence "{ b } \<subseteq> lgrid b {d} lm" unfolding lgrid_def by auto
    from sum_diff[OF lgrid_finite this]
    have "(\<Sum> p' \<in> (lgrid b {d} lm) - {b}. ?C p') = ?s b - ?C b" by simp
    also have "\<dots> = ?s ?l + ?s ?r"
      using lgrid_sum and \<open>level b < lm\<close> and \<open>d < length b\<close> by auto
    also have "\<dots> = snd (fst ?ul) + fst (fst ?ur)" using fml and fmr
      and \<open>Suc l + level b = lm\<close> and child_level[OF \<open>d < length b\<close>]
      using eq unfolding True lgrid_def by auto

    finally show ?thesis unfolding up'.simps Let_def and fun_upd_def lgrid_def
      using \<open>p = b\<close> and \<open>level b < lm\<close>
      by (cases ?ul, cases ?ur, auto)
  next
    case False

    have "?r \<in> sparsegrid' dm" and "?l \<in> sparsegrid' dm"
      using \<open>b \<in> sparsegrid' dm\<close> and \<open>d < dm\<close> unfolding sparsegrid'_def by auto
    from Suc.hyps[OF _ _ this(1)] Suc.hyps[OF _ _ this(2)]
    have "?goal l ?l p \<alpha>" and "?goal l ?r p (snd ?ul)"
      using \<open>d < length b\<close> and \<open>Suc l + level b = lm\<close> and \<open>p \<in> sparsegrid' dm\<close> by auto

    show ?thesis
    proof (cases "p \<in> lgrid b {d} lm")
      case True
      hence "level p < lm" and "p \<in> grid b {d}" unfolding lgrid_def by auto
      hence "p \<in> grid ?l {d} \<or> p \<in> grid ?r {d}"
        unfolding grid_partition[of b] using \<open>p \<noteq> b\<close> by auto
      thus ?thesis
      proof (rule disjE)
        assume "p \<in> grid (child b left d) {d}"
        hence "p \<notin> grid (child b right d) {d}"
          using grid_disjunct[OF \<open>d < length b\<close>] by auto
        thus ?thesis
          using \<open>?goal l ?l p \<alpha>\<close> and \<open>?goal l ?r p (snd ?ul)\<close>
          using \<open>p \<noteq> b\<close> \<open>p \<in> lgrid b {d} lm\<close>
          unfolding lgrid_def grid_partition[of b]
          by (cases ?ul, cases ?ur, auto simp add: Let_def)
      next
        assume *: "p \<in> grid (child b right d) {d}"
        hence "p \<notin> grid (child b left d) {d}"
          using grid_disjunct[OF \<open>d < length b\<close>] by auto
        moreover
        { fix p' assume "p' \<in> grid p {d}"
          from grid_transitive[OF this *] eq[of p']
          have "snd ?ul p' = \<alpha> p'" by simp
        }
        ultimately show ?thesis
          using \<open>?goal l ?l p \<alpha>\<close> and \<open>?goal l ?r p (snd ?ul)\<close>
          using \<open>p \<noteq> b\<close> \<open>p \<in> lgrid b {d} lm\<close> *
          unfolding lgrid_def
          by (cases ?ul, cases ?ur, auto simp add: Let_def)
  qed
next
      case False
      then have "p \<notin> lgrid ?l {d} lm" and "p \<notin> lgrid ?r {d} lm"
        unfolding lgrid_def and grid_partition[where p=b] by auto
      with False show ?thesis using \<open>?goal l ?l p \<alpha>\<close> and \<open>?goal l ?r p (snd ?ul)\<close>
        using \<open>p \<noteq> b\<close> \<open>p \<notin> lgrid b {d} lm\<close>
        unfolding lgrid_def
        by (cases ?ul, cases ?ur, auto simp add: Let_def)
    qed
  qed
next
  case 0
  then have "lgrid b {d} lm = {}"
    using lgrid_empty'[where p=b and lm=lm and ds="{d}"] by auto
  with 0 show ?case unfolding up'.simps by auto
qed

lemma up:
  assumes "d < dm" and "p \<in> sparsegrid dm lm"
  shows "(up dm lm d \<alpha>) p = (\<Sum> p' \<in> (lgrid p {d} lm) - {p}. \<alpha> p' * l2_\<phi> (p' ! d) (p ! d))"
proof -
  let ?S = "\<lambda> x p p'. if p' \<in> grid p {d} - {p} then x * l2_\<phi> (p'!d) (p!d) else 0"
  let ?F = "\<lambda> d lm p \<alpha>. snd (up' d lm p \<alpha>)"

  { fix p b assume "p \<in> grid b {d}"
    from grid_transitive[OF _ this subset_refl subset_refl]
    have "lgrid b {d} lm \<inter> (grid p {d} - {p}) = lgrid p {d} lm - {p}"
      unfolding lgrid_def by auto
  } note lgrid_eq = this

  { fix l b p \<alpha>
    assume b: "b \<in> lgrid (start dm) ({0..<dm} - {d}) lm"
    hence "b \<in> sparsegrid' dm" and "d < length b" using sparsegrid'_start \<open>d < dm\<close> by auto
    assume l: "l + level b = lm" and p: "p \<in> sparsegrid dm lm"
    note sparsegridE[OF p]

    note up' = up'_\<beta>[OF \<open>d < length b\<close> l \<open>b \<in> sparsegrid' dm\<close> \<open>p \<in> sparsegrid' dm\<close>]

    have "?F d l b \<alpha> p =
          (if b = base {d} p then (\<Sum>p'\<in>lgrid b {d} lm. ?S (\<alpha> p') p p') else \<alpha> p)"
    proof (cases "b = base {d} p")
      case True with baseE(2)[OF \<open>p \<in> sparsegrid' dm\<close>] \<open>level p < lm\<close>
      have "p \<in> lgrid b {d} lm" and "p \<in> grid b {d}" by auto
      show ?thesis
        using lgrid_eq[OF \<open>p \<in> grid b {d}\<close>]
        unfolding up' if_P[OF True] if_P[OF \<open>p \<in> lgrid b {d} lm\<close>]
        by (intro sum.mono_neutral_cong_left lgrid_finite) auto
    next
      case False
      moreover have "p \<notin> lgrid b {d} lm"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "base {d} p = b" using b by (auto intro!: baseI)
        thus False using False by auto
      qed
      ultimately show ?thesis unfolding up' by auto
    qed }
  with lift[where F = ?F, OF \<open>d < dm\<close> \<open>p \<in> sparsegrid dm lm\<close>]
  have lift_eq: "lift ?F dm lm d \<alpha> p =
         (\<Sum>p'\<in>lgrid (base {d} p) {d} lm. ?S (\<alpha> p') p p')" by auto
  from lgrid_eq[OF baseE(2)[OF sparsegrid_subset[OF \<open>p \<in> sparsegrid dm lm\<close>]]]
  show ?thesis
    unfolding up_def lift_eq by (intro sum.mono_neutral_cong_right lgrid_finite) auto
qed

end
