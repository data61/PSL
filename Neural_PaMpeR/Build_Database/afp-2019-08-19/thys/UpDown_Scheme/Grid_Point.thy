section \<open> Grid Points \<close>

theory Grid_Point
imports "HOL-Analysis.Analysis"
begin

type_synonym grid_point = "(nat \<times> int) list"

definition lv :: "grid_point \<Rightarrow> nat \<Rightarrow> nat"
  where "lv p d = fst (p ! d)"

definition ix :: "grid_point \<Rightarrow> nat \<Rightarrow> int"
  where "ix p d = snd (p ! d)"

definition level :: "grid_point \<Rightarrow> nat"
  where "level p = (\<Sum> i < length p. lv p i)"

lemma level_all_eq:
  assumes "\<And>d. d < length p \<Longrightarrow> lv p d = lv p' d"
  and "length p = length p'"
  shows "level p' = level p"
  unfolding level_def using assms by auto

datatype dir = left | right

fun sgn :: "dir \<Rightarrow> int"
where
    "sgn left  = -1"
  | "sgn right =  1"

fun inv :: "dir \<Rightarrow> dir"
where
    "inv left = right"
  | "inv right = left"

lemma inv_inv[simp]: "inv (inv dir) = dir"
  by (cases dir) simp_all

lemma sgn_inv[simp]: "sgn (inv dir) = - sgn dir"
  by (cases dir, auto)

definition child :: "grid_point \<Rightarrow> dir \<Rightarrow> nat \<Rightarrow> grid_point"
  where "child p dir d = p[d := (lv p d + 1, 2 * (ix p d) + sgn dir)]"

lemma child_length[simp]: "length (child p dir d) = length p"
  unfolding child_def by simp

lemma child_odd[simp]: "d < length p \<Longrightarrow> odd (ix (child p dir d) d)"
  unfolding child_def ix_def by (cases dir, auto)

lemma child_eq: "p ! d = (l, i) \<Longrightarrow> \<exists> j. child p dir d = p[d := (l + 1, j)]"
  by (auto simp add: child_def ix_def lv_def)

lemma child_other: "d \<noteq> d' \<Longrightarrow> child p dir d ! d' = p ! d'"
  unfolding child_def lv_def ix_def by (cases "d' < length p", auto)

lemma child_invariant: assumes "d' < length p" shows "(child p dir d ! d' = p ! d') = (d \<noteq> d')"
proof -
  obtain l i where "p ! d' = (l, i)" using prod.exhaust .
  with assms show ?thesis
    unfolding child_def ix_def lv_def by auto
qed

lemma child_single_level: "d < length p \<Longrightarrow> lv (child p dir d) d > lv p d"
  unfolding lv_def child_def by simp

lemma child_lv: "d < length p \<Longrightarrow> lv (child p dir d) d = lv p d + 1"
  unfolding child_def lv_def by simp

lemma child_lv_other: assumes "d' \<noteq> d" shows "lv (child p dir d') d = lv p d"
  using child_other[OF assms] unfolding lv_def by simp

lemma child_ix_left: "d < length p \<Longrightarrow> ix (child p left d) d = 2 * ix p d - 1"
  unfolding child_def ix_def by simp

lemma child_ix_right: "d < length p \<Longrightarrow> ix (child p right d) d = 2 * ix p d + 1"
  unfolding child_def ix_def by simp

lemma child_ix: "d < length p \<Longrightarrow> ix (child p dir d) d = 2 * ix p d + sgn dir"
  unfolding child_def ix_def by simp

lemma child_level[simp]: assumes "d < length p"
  shows "level (child p dir d) = level p + 1"
proof -
  have inter: "{0..<length p} \<inter> {d} = {d}" using assms by auto

  have "level (child p dir d) =
    (\<Sum> d' = 0..<length p. if d' \<in> {d} then lv p d + 1 else lv p d')"
    by (auto intro!: sum.cong simp add: child_lv_other child_lv level_def)
  moreover have "level p + 1 =
    (\<Sum> d' = 0..<length p. if d' \<in> {d} then lv p d else lv p d') + 1"
    by (auto intro!: sum.cong simp add: child_lv_other child_lv level_def)
  ultimately show ?thesis
    unfolding sum.If_cases[OF finite_atLeastLessThan] inter
    using assms by auto
qed

lemma child_ex_neighbour: "\<exists> b'. child b dir d = child b' (inv dir) d"
proof
  show "child b dir d = child (b[d := (lv b d, ix b d + sgn dir)]) (inv dir) d"
    unfolding child_def ix_def lv_def by (cases "d < length b", auto simp add: algebra_simps)
qed

lemma child_level_gt[simp]: "level (child p dir d) >= level p"
  by (cases "d < length p", simp, simp add: child_def)

lemma child_estimate_child:
  assumes "d < length p"
    and "l \<le> lv p d"
    and i'_range: "ix p d < (i + 1) * 2^(lv p d - l) \<and>
                   ix p d > (i - 1) * 2^(lv p d - l)"
                  (is "?top p \<and> ?bottom p")
    and is_child: "p' = child p dir d"
  shows "?top p' \<and> ?bottom p'"
proof
  from is_child and \<open>d < length p\<close>
  have "lv p' d = lv p d + 1" by (auto simp add: child_def ix_def lv_def)
  hence "lv p' d - l = lv p d - l + 1" using \<open>lv p d >= l\<close> by auto
  hence pow_l'': "(2^(lv p' d - l) :: int) = 2 * 2^(lv p d - l)" by auto

  show "?top p'"
  proof -
    from is_child and \<open>d < length p\<close>
    have "ix p' d \<le> 2 * (ix p d) + 1"
      by (cases dir, auto simp add: child_def lv_def ix_def)
    also have "\<dots> < (i + 1) * (2 * 2^(lv p d - l))" using i'_range by auto
    finally show ?thesis using pow_l'' by auto
  qed

  show "?bottom p'"
  proof -
    have "(i - 1) * 2^(lv p' d - l) = 2 * ((i - 1) * 2^(lv p d - l))"
      using pow_l'' by simp
    also have "\<dots> < 2 * ix p d - 1" using i'_range by auto
    finally show ?thesis using is_child and \<open>d < length p\<close>
      by (cases dir, auto simp add: child_def lv_def ix_def)
  qed
qed

lemma child_neighbour: assumes "child p (inv dir) d = child ps dir d" (is "?c_p = ?c_ps")
  shows "ps = p[d := (lv p d, ix p d - sgn dir)]" (is "_ = ?ps")
proof (rule nth_equalityI)
  have "length ?c_ps = length ?c_p" using \<open>?c_p = ?c_ps\<close> by simp
  hence len_eq: "length ps = length p" by simp
  thus "length ps = length ?ps" by simp

  show "ps ! i = ?ps ! i" if "i < length ps" for i
  proof -
    have "i < length p"
      using that len_eq by auto

    show "ps ! i = ?ps ! i"
    proof (cases "d = i")
      case [simp]: True

      have "?c_p ! i = ?c_ps ! i" using \<open>?c_p = ?c_ps\<close> by auto
      hence "ix p i = ix ps d + sgn dir" and "lv p i = lv ps i"
        by (auto simp add: child_def
          nth_list_update_eq[OF \<open>i < length p\<close>]
          nth_list_update_eq[OF \<open>i < length ps\<close>])
      thus ?thesis by (simp add: lv_def ix_def \<open>i < length p\<close>)
    next
      assume "d \<noteq> i"
      with child_other[OF this, of ps dir] child_other[OF this, of p "inv dir"]
      show ?thesis using assms by auto
    qed
  qed
qed

definition start :: "nat \<Rightarrow> grid_point"
where
  "start dm = replicate dm (0, 1)"

lemma start_lv[simp]: "d < dm \<Longrightarrow> lv (start dm) d = 0"
  unfolding start_def lv_def by simp

lemma start_ix[simp]: "d < dm \<Longrightarrow> ix (start dm) d = 1"
  unfolding start_def ix_def by simp

lemma start_length[simp]: "length (start dm) = dm"
  unfolding start_def by auto

lemma level_start_0[simp]: "level (start dm) = 0"
  using level_def by auto

end
