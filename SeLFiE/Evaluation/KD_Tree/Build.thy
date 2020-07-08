(*
  File:     Build.thy
  Author:   Martin Rau, TU München
*)

section \<open>Building a balanced \<open>k\<close>-d Tree from a List of Points\<close>

theory Build
imports
  KD_Tree
  Median_Of_Medians_Selection.Median_Of_Medians_Selection
begin

text \<open>
  Build a balanced \<open>k\<close>-d Tree by recursively partition the points into two lists.
  The partitioning criteria will be the median at a particular axis \<open>k\<close>.
  The left list will contain all points \<open>p\<close> with @{term "p$k \<le> median"}.
  The right list will contain all points with median at axis @{term "median < p$k"}.
  The left and right list differ in length by one or none.
  The axis \<open>k\<close> will the widest spread axis.
\<close>

subsection "Auxiliary Lemmas"

lemma length_filter_mset_sorted_nth:
  assumes "distinct xs" "n < length xs" "sorted xs"
  shows "{# x \<in># mset xs. x \<le> xs ! n #} = mset (take (n + 1) xs)"
  using assms
proof (induction xs arbitrary: n rule: list.induct)
  case (Cons x xs)
  thus ?case
  proof (cases n)
    case 0
    thus ?thesis
      using Cons.prems(1,3) filter_mset_is_empty_iff by fastforce
  next
    case (Suc n')
    thus ?thesis
      using Cons by simp
  qed
qed auto

lemma length_filter_sort_nth:
  assumes "distinct xs" "n < length xs"
  shows "length (filter (\<lambda>x. x \<le> sort xs ! n) xs) = n + 1"
proof -
  have "length (filter (\<lambda>x. x \<le> sort xs ! n) xs) = length (filter (\<lambda>x. x \<le> sort xs ! n) (sort xs))"
    by (simp add: filter_sort)
  also have "... = size (mset (filter (\<lambda>x. x \<le> sort xs ! n) (sort xs)))"
    using size_mset by metis
  also have "... = size ({# x \<in># mset (sort xs). x \<le> sort xs ! n #})"
    using mset_filter by simp
  also have "... = size (mset (take (n + 1) (sort xs)))"
    using length_filter_mset_sorted_nth assms sorted_sort distinct_sort length_sort by metis
  finally show ?thesis
    using assms(2) by auto
qed


subsection \<open>Widest Spread Axis\<close>

definition calc_spread :: "('k::finite) \<Rightarrow> 'k point list \<Rightarrow> real" where
  "calc_spread k ps = (case ps of [] \<Rightarrow> 0 | ps \<Rightarrow>
    let ks = map (\<lambda>p. p$k) (tl ps) in
    fold max ks ((hd ps)$k) - fold min ks ((hd ps)$k)
  )"

fun widest_spread :: "('k::finite) list \<Rightarrow> 'k point list \<Rightarrow> 'k \<times> real" where
  "widest_spread [] _ = undefined"
| "widest_spread [k] ps = (k, calc_spread k ps)"
| "widest_spread (k # ks) ps = (
    let (k', s') = widest_spread ks ps in
    let s = calc_spread k ps in
    if s \<le> s' then (k', s') else (k, s)
  )"

lemma calc_spread_spec:
  "calc_spread k ps = spread k (set ps)"
  using Max.set_eq_fold[of "(hd ps)$k"] Min.set_eq_fold[of "(hd ps)$k"]
  by (auto simp: Let_def spread_def calc_spread_def split: list.splits, metis set_map)

lemma widest_spread_calc_spread:
  "ks \<noteq> [] \<Longrightarrow> (k, s) = widest_spread ks ps \<Longrightarrow> s = calc_spread k ps"
  by (induction ks ps rule: widest_spread.induct) (auto simp: Let_def split: prod.splits if_splits)

lemma widest_spread_axis_Un:
  shows "widest_spread_axis k K P \<Longrightarrow> spread k' P \<le> spread k P \<Longrightarrow> widest_spread_axis k (K \<union> { k' }) P"
    and "widest_spread_axis k K P \<Longrightarrow> spread k P \<le> spread k' P \<Longrightarrow> widest_spread_axis k' (K \<union> { k' }) P"
  unfolding widest_spread_axis_def by auto

lemma widest_spread_spec:
  "(k, s) = widest_spread ks ps \<Longrightarrow> widest_spread_axis k (set ks) (set ps)"
proof (induction ks ps arbitrary: k s rule: widest_spread.induct)
  case (3 k\<^sub>0 k\<^sub>1 ks ps)
  obtain K' S' where K'_def: "(K', S') = widest_spread (k\<^sub>1 # ks) ps"
    by (metis surj_pair)
  hence IH: "widest_spread_axis K' (set (k\<^sub>1 # ks)) (set ps)"
    using "3.IH" by blast
  hence 0: "S' = spread K' (set ps)"
    using K'_def widest_spread_calc_spread calc_spread_spec by blast
  define S where "S = calc_spread k\<^sub>0 ps"
  hence 1: "S = spread k\<^sub>0 (set ps)"
    using calc_spread_spec by blast
  show ?case
  proof (cases "S \<le> S'")
    case True
    hence "widest_spread_axis K' (set (k\<^sub>0 # k\<^sub>1 # ks)) (set ps)"
      using 0 1 widest_spread_axis_Un(1)[OF IH, of k\<^sub>0]  by auto
    thus ?thesis
      using True K'_def S_def "3.prems" by (auto split: prod.splits)
  next
    case False
    hence "widest_spread_axis k\<^sub>0 (set (k\<^sub>0 # k\<^sub>1 # ks)) (set ps)"
      using 0 1 widest_spread_axis_Un(2)[OF IH, of k\<^sub>0] "3.prems"(1) by auto
    thus ?thesis
      using False K'_def S_def "3.prems" by (auto split: prod.splits)
  qed
qed (auto simp: widest_spread_axis_def)


subsection \<open>Fast Axis Median\<close>

definition axis_median :: "('k::finite) \<Rightarrow> 'k point list \<Rightarrow> real" where
  "axis_median k ps = (let n = (length ps - 1) div 2 in fast_select n (map (\<lambda>p. p$k) ps))"

lemma length_filter_le_axis_median:
  assumes "0 < length ps" "\<forall>k. distinct (map (\<lambda>p. p$k) ps)"
  shows "length (filter (\<lambda>p. p$k \<le> axis_median k ps) ps) = (length ps - 1) div 2 + 1"
proof -
  let ?n = "(length ps - 1) div 2"
  let ?ps = "map (\<lambda>p. p$k) ps"
  let ?m = "fast_select ?n ?ps"
  have 0: "?n < length ?ps"
    using assms(1) by (auto, linarith)
  have 1: "distinct ?ps"
    using assms(2) by blast
  have "?m = select ?n ?ps"
    using fast_select_correct[OF 0] by blast
  hence "length (filter (\<lambda>p. p$k \<le> axis_median k ps) ps) =
        length (filter (\<lambda>p. p$k \<le> sort ?ps ! ?n) ps)"
    unfolding axis_median_def by (auto simp add: Let_def select_def simp del: fast_select.simps)
  also have "... = length (filter (\<lambda>v. v \<le> sort ?ps ! ?n) ?ps)"
    by (induction ps) (auto, metis comp_apply)
  also have "... = ?n + 1"
    using length_filter_sort_nth[OF 1 0] by blast
  finally show ?thesis .
qed

definition partition_by_median :: "('k::finite) \<Rightarrow> 'k point list \<Rightarrow> 'k point list \<times> real \<times> 'k point list" where
  "partition_by_median k ps = (
     let m = axis_median k ps in
     let (l, r) = partition (\<lambda>p. p$k \<le> m) ps in
     (l, m, r)
  )"

lemma set_partition_by_median:
  "(l, m, r) = partition_by_median k ps \<Longrightarrow> set ps = set l \<union> set r"
  unfolding partition_by_median_def by (auto simp: Let_def)

lemma filter_partition_by_median:
  assumes "(l, m, r) = partition_by_median k ps"
  shows "\<forall>p \<in> set l. p$k \<le> m"
    and "\<forall>p \<in> set r. \<not>p$k \<le> m"
  using assms unfolding partition_by_median_def by (auto simp: Let_def)

lemma sum_length_partition_by_median:
  assumes "(l, m, r) = partition_by_median k ps"
  shows "length ps = length l + length r"
  using assms sum_length_filter_compl[of "(\<lambda>p. p $ k \<le> axis_median k ps)"]
  unfolding partition_by_median_def by (simp add: Let_def o_def)

lemma length_l_partition_by_median:
  assumes "0 < length ps" "\<forall>k. distinct (map (\<lambda>p. p$k) ps)" "(l, m, r) = partition_by_median k ps"
  shows "length l = (length ps - 1) div 2 + 1"
  using assms unfolding partition_by_median_def by (auto simp: Let_def length_filter_le_axis_median)

corollary lengths_partition_by_median_1:
  assumes "0 < length ps"  "\<forall>k. distinct (map (\<lambda>p. p$k) ps)" "(l, m, r) = partition_by_median k ps"
  shows "length l - length r \<le> 1"
    and "length r \<le> length l"
    and "0 < length l"
    and "length r < length ps"
  using length_l_partition_by_median[OF assms] sum_length_partition_by_median[OF assms(3)] by auto

corollary lengths_partition_by_median_2:
  assumes "1 < length ps" "\<forall>k. distinct (map (\<lambda>p. p$k) ps)" "(l, m, r) = partition_by_median k ps"
  shows "0 < length r"
    and "length l < length ps"
proof -
  have *: "0 < length ps"
    using assms(1) by auto
  show "0 < length r" "length l < length ps"
    using length_l_partition_by_median[OF * assms(2,3)] sum_length_partition_by_median[OF assms(3)]
    using assms(1) by linarith+
qed

lemmas length_partition_by_median =
  sum_length_partition_by_median length_l_partition_by_median
  lengths_partition_by_median_1 lengths_partition_by_median_2


subsection \<open>Building the Tree\<close>

function (domintros, sequential) build :: "('k::finite) list \<Rightarrow> 'k point list \<Rightarrow> 'k kdt" where
  "build _ [] = undefined"
| "build _ [p] = Leaf p"
| "build ks ps = (
    let (k, _) = widest_spread ks ps in
    let (l, m, r) = partition_by_median k ps in
    Node k m (build ks l) (build ks r)
  )"
  by pat_completeness auto

lemma build_domintros3:
  assumes "(k, s) = widest_spread ks (x # y # zs)" "(l, m, r) = partition_by_median k (x # y # zs)"
  assumes "build_dom (ks, l)" "build_dom (ks, r)"
  shows "build_dom (ks, x # y # zs)"
proof -
  {
    fix k s l m r
    assume "(k, s) = widest_spread ks (x # y # zs)" "(l, m, r) = partition_by_median k (x # y # zs)"
    hence "build_dom (ks, l)" "build_dom (ks, r)"
      using assms by (metis Pair_inject)+
  }
  thus ?thesis
    by (simp add: build.domintros(3))
qed

lemma build_termination:
  assumes "\<forall>k. distinct (map (\<lambda>p. p$k) ps)"
  shows "build_dom (ks, ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 xs)
  consider (A) "xs = []" | (B) "\<exists>x. xs = [x]" | (C) "\<exists>x y zs. xs = x # y # zs"
    by (induction xs rule: induct_list012) auto
  then show ?case
  proof cases
    case C
    then obtain x y zs where xyzs_def: "xs = x # y # zs"
      by blast
    obtain k s where ks_def: "(k, s) = widest_spread ks xs"
      by (metis surj_pair)
    obtain l m r where lmr_def: "(l, m, r) = partition_by_median k xs"
      by (metis prod_cases3)
    note defs = xyzs_def ks_def lmr_def
    have "\<forall>k. distinct (map (\<lambda>p. p $ k) l)" "\<forall>k. distinct (map (\<lambda>p. p $ k) r)"
      using lmr_def unfolding partition_by_median_def
      by (auto simp: Let_def "1.prems" distinct_map_filter)
    moreover have "length l < length xs" "length r < length xs"
      using length_partition_by_median(8)[OF _ "1.prems"] length_partition_by_median(6)[OF _ "1.prems"]
      using defs by auto
    ultimately have "build_dom (ks, l)" "build_dom (ks, r)"
      using "1.IH" by blast+
    thus ?thesis
      using build_domintros3 defs by blast
  qed (auto intro: build.domintros)
qed

lemma build_psimp_1:
  "ps = [p] \<Longrightarrow> build k ps = Leaf p"
  by (simp add: build.domintros(2) build.psimps(2))

lemma build_psimp_2:
  assumes "(k, s) = widest_spread ks (x # y # zs)" "(l, m, r) = partition_by_median k (x # y # zs)"
  assumes "build_dom (ks, l)" "build_dom (ks, r)"
  shows "build ks (x # y # zs) = Node k m (build ks l) (build ks r)"
proof -
  have 0: "build_dom (ks, x # y # zs)"
    using assms build_domintros3 by blast
  thus ?thesis
    using build.psimps(3)[OF 0] assms(1,2) by (auto split: prod.splits)
qed

lemma length_xs_gt_1:
  "1 < length xs \<Longrightarrow> \<exists>x y ys. xs = x # y # ys"
  by (cases xs, auto simp: neq_Nil_conv)

lemma build_psimp_3:
  assumes "1 < length ps" "(k, s) = widest_spread ks ps" "(l, m, r) = partition_by_median k ps"
  assumes "build_dom (ks, l)" "build_dom (ks, r)"
  shows "build ks ps = Node k m (build ks l) (build ks r)"
  using build_psimp_2 length_xs_gt_1 assms by blast

lemmas build_psimps[simp] = build_psimp_1 build_psimp_3


subsection \<open>Main Theorems\<close>

theorem set_build:
  "0 < length ps \<Longrightarrow> \<forall>k. distinct (map (\<lambda>p. p$k) ps) \<Longrightarrow> set ps = set_kdt (build ks ps)"
proof (induction ps rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "1 < length ps")
    case True
    obtain k s where ks_def: "(k, s) = widest_spread ks ps"
      by (metis surj_pair)
    obtain l m r where lmr_def: "(l, m, r) = partition_by_median k ps"
      by (metis prod_cases3)
    have D: "\<forall>k. distinct (map (\<lambda>p. p$k) l)" "\<forall>k. distinct (map (\<lambda>p. p$k) r)"
      using lmr_def unfolding partition_by_median_def
      by (auto simp: "1.prems"(2) Let_def distinct_map_filter)
    moreover have "length l < length ps" "0 < length l"
                  "length r < length ps" "0 < length r"
      using length_partition_by_median(8)[OF True "1.prems"(2)]
            length_partition_by_median(5)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(6)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(7)[OF True "1.prems"(2)]
            lmr_def by blast+
    ultimately have "set l = set_kdt (build ks l)" "set r = set_kdt (build ks r)"
      using "1.IH" by blast+
    moreover have "set ps = set l \<union> set r"
      using lmr_def unfolding partition_by_median_def by (auto simp: Let_def)
    moreover have "build ks ps = Node k m (build ks l) (build ks r)"
      using build_psimp_3[OF True ks_def lmr_def] build_termination D by blast
    ultimately show ?thesis
      by simp
  next
    case False
    thus ?thesis
      using "1.prems" by (cases ps) auto
  qed
qed

theorem invar_build:
  "0 < length ps \<Longrightarrow> \<forall>k. distinct (map (\<lambda>p. p$k) ps) \<Longrightarrow> set ks = UNIV \<Longrightarrow> invar (build ks ps)"
proof (induction ps rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "1 < length ps")
    case True
    obtain k s where ks_def: "(k, s) = widest_spread ks ps"
      by (metis surj_pair)
    obtain l m r where lmr_def: "(l, m, r) = partition_by_median k ps"
      by (metis prod_cases3)
    have D: "\<forall>k. distinct (map (\<lambda>p. p$k) l)" "\<forall>k. distinct (map (\<lambda>p. p$k) r)"
      using lmr_def unfolding partition_by_median_def
      by (auto simp: "1.prems"(2) Let_def distinct_map_filter)
    moreover have "length l < length ps" "0 < length l"
                  "length r < length ps" "0 < length r"
      using length_partition_by_median(8)[OF True "1.prems"(2)]
            length_partition_by_median(5)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(6)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(7)[OF True "1.prems"(2)]
            lmr_def by blast+
    ultimately have "invar (build ks l)" "invar (build ks r)"
      using "1.IH" "1.prems"(3) by blast+
    moreover have "\<forall>p \<in> set l. p$k \<le> m" "\<forall>p \<in> set r. m < p$k"
      using filter_partition_by_median(1)[OF lmr_def]
            filter_partition_by_median(2)[OF lmr_def] by auto
    moreover have "widest_spread_axis k UNIV (set l \<union> set r)"
      using widest_spread_spec[OF ks_def] "1.prems"(3) set_partition_by_median[OF lmr_def] by simp
    moreover have "build ks ps = Node k m (build ks l) (build ks r)"
      using build_psimp_3[OF True ks_def lmr_def] build_termination D by blast
    ultimately show ?thesis
      using set_build[OF \<open>0 < length l\<close> D(1)] set_build[OF \<open>0 < length r\<close> D(2)] by simp
  next
    case False
    thus ?thesis
      using "1.prems" by (cases ps) auto
  qed
qed

theorem size_build:
  "0 < length ps \<Longrightarrow> \<forall>k. distinct (map (\<lambda>p. p$k) ps) \<Longrightarrow> size_kdt (build ks ps) = length ps"
proof (induction ps rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "1 < length ps")
    case True
    obtain k s where ks_def: "(k, s) = widest_spread ks ps"
      by (metis surj_pair)
    obtain l m r where lmr_def: "(l, m, r) = partition_by_median k ps"
      by (metis prod_cases3)
    have D: "\<forall>k. distinct (map (\<lambda>p. p$k) l)" "\<forall>k. distinct (map (\<lambda>p. p$k) r)"
      using lmr_def unfolding partition_by_median_def
      by (auto simp: "1.prems"(2) Let_def distinct_map_filter)
    moreover have "length l < length ps" "0 < length l"
                  "length r < length ps" "0 < length r"
      using length_partition_by_median(8)[OF True "1.prems"(2)]
            length_partition_by_median(5)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(6)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(7)[OF True "1.prems"(2)]
            lmr_def by blast+
    ultimately have "size_kdt (build ks l) = length l" "size_kdt (build ks r) = length r"
      using "1.IH" by blast+
    moreover have "build ks ps = Node k m (build ks l) (build ks r)"
      using build_psimp_3[OF True ks_def lmr_def] build_termination D by blast
    ultimately show ?thesis
      using length_partition_by_median(1)[OF lmr_def] by simp
  next
    case False
    thus ?thesis
      using "1.prems" by (cases ps) auto
  qed
qed

theorem balanced_build:
  "0 < length ps \<Longrightarrow> \<forall>k. distinct (map (\<lambda>p. p$k) ps) \<Longrightarrow> balanced (build ks ps)"
proof (induction ps rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "1 < length ps")
    case True
    obtain k s where ks_def: "(k, s) = widest_spread ks ps"
      by (metis surj_pair)
    obtain l m r where lmr_def: "(l, m, r) = partition_by_median k ps"
      by (metis prod_cases3)
    have D: "\<forall>k. distinct (map (\<lambda>p. p$k) l)" "\<forall>k. distinct (map (\<lambda>p. p$k) r)"
      using lmr_def unfolding partition_by_median_def
      by (auto simp: "1.prems"(2) Let_def distinct_map_filter)
    moreover have "length l < length ps" "0 < length l"
                  "length r < length ps" "0 < length r"
      using length_partition_by_median(8)[OF True "1.prems"(2)]
            length_partition_by_median(5)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(6)[OF "1.prems"(1) "1.prems"(2)]
            length_partition_by_median(7)[OF True "1.prems"(2)]
            lmr_def by blast+
    ultimately have IH: "balanced (build ks l)" "balanced (build ks r)"
      using "1.IH" by blast+
    have "build ks ps = Node k m (build ks l) (build ks r)"
      using build_psimp_3[OF True ks_def lmr_def] build_termination D by blast
    moreover have "length r + 1 = length l \<or> length r = length l"
      using length_partition_by_median(1)[OF lmr_def]
            length_partition_by_median(3)[OF "1.prems"(1) "1.prems"(2) lmr_def]
            length_partition_by_median(4)[OF "1.prems"(1) "1.prems"(2) lmr_def]
      by linarith
    ultimately show ?thesis
      using balanced_Node_if_wbal1[OF IH] balanced_Node_if_wbal2[OF IH]
            size_build[OF \<open>0 < length l\<close> D(1)] size_build[OF \<open>0 < length r\<close> D(2)]
      by auto
  next
    case False
    thus ?thesis
      using "1.prems" by (cases ps) (auto simp: balanced_def)
  qed
qed

lemma complete_if_balanced_size_2powh:
  assumes "balanced kdt" "size_kdt kdt = 2 ^ h"
  shows "complete kdt"
proof (rule ccontr)
  assume "\<not> complete kdt"
  hence "2 ^ (min_height kdt) < size_kdt kdt" "size_kdt kdt < 2 ^ height kdt"
    by (simp_all add: min_height_size_if_incomplete size_height_if_incomplete)
  hence "height kdt - min_height kdt > 1"
    using assms(2) by simp
  hence "\<not> balanced kdt"
    using balanced_def by force
  thus "False"
    using assms(1) by simp
qed

theorem complete_build:
  "length ps = 2 ^ h \<Longrightarrow> \<forall>k. distinct (map (\<lambda>p. p$k) ps) \<Longrightarrow> complete (build k ps)"
  by (simp add: balanced_build complete_if_balanced_size_2powh size_build)

corollary height_build:
  assumes "length ps = 2 ^ h" "\<forall>k. distinct (map (\<lambda>p. p$k) ps)"
  shows "h = height (build k ps)"
  using complete_build[OF assms] size_build[OF _ assms(2)] by (simp add: assms(1) complete_iff_size)

end
