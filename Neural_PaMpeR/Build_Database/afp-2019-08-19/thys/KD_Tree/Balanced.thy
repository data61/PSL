(*
  File:     Balanced.thy
  Author:   Martin Rau, TU München
*)

section "Building a balanced \<open>k\<close>-d Tree from a List of Points"

theory Balanced
imports
  KDTree
  Median_Of_Medians_Selection.Median_Of_Medians_Selection
begin

text \<open>
  Build a balanced \<open>k\<close>-d Tree by recursively partition the points into two lists.
  The partitioning criteria will be the median at a particular axis \<open>ws\<close>.
  The left list will contain all points \<open>p\<close> with @{term "p!ws \<le> median"}.
  The right list will contain all points with median at axis @{term "ws \<le> p!a"}.
  The left and right list differ in length by one or none.
  The axis \<open>ws\<close> will the widest spread axis. The axis which has the widest spread of point values.
\<close>


subsection "Widest Spread of a List of Points"

definition spread_set :: "axis \<Rightarrow> point set \<Rightarrow> real" where
  "spread_set a ps = (
    let as = (\<lambda>p. p!a) ` ps in
    Max as - Min as
  )"

definition spread :: "axis \<Rightarrow> point list \<Rightarrow> real" where
  "spread a ps = (
    let as = map (\<lambda>p. p!a) (tl ps) in
    fold max as (hd ps !a) - fold min as (hd ps!a)
  )"

definition is_widest_spread :: "axis \<Rightarrow> dimension \<Rightarrow> point set \<Rightarrow> bool" where
  "is_widest_spread a k ps = (\<forall>a' < k. spread_set a' ps \<le> spread_set a ps)"

fun widest_spread_rec :: "axis \<Rightarrow> point list \<Rightarrow> axis * real" where
  "widest_spread_rec 0 ps = (0, spread 0 ps)"
| "widest_spread_rec a ps = (
    let (a', s') = widest_spread_rec (a - 1) ps in
    let s = spread a ps in
    if s \<le> s' then (a', s') else (a, s)
  )"

definition widest_spread :: "point list \<Rightarrow> axis" where
  "widest_spread ps = (
    let (a, _) = widest_spread_rec (dim (hd ps) - 1) ps in
    a
  )"

fun widest_spread_invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "widest_spread_invar _ (Leaf _) \<longleftrightarrow> True"
| "widest_spread_invar k (Node a s l r) \<longleftrightarrow> is_widest_spread a k (set_kdt l \<union> set_kdt r) \<and> widest_spread_invar k l \<and> widest_spread_invar k r"

lemma spread_is_spread_set:
  "ps \<noteq> [] \<Longrightarrow> spread_set a (set ps) = spread a ps"
  using Max.set_eq_fold[of "hd ps !a" _] Min.set_eq_fold[of "hd ps !a"]
  apply (auto simp add: Let_def spread_def spread_set_def)
  by (metis (no_types, lifting) hd_Cons_tl list.simps(15) list.simps(9) set_map)

lemma widest_spread_rec_is_spread:
  "(ws, s) = widest_spread_rec a ps \<Longrightarrow> s = spread ws ps"
  by (induction a) (auto simp add: Let_def split: prod.splits if_splits)

lemma is_widest_spread_k_le_ws:
  "is_widest_spread ws k ps \<Longrightarrow> spread_set k ps \<le> spread_set ws ps \<Longrightarrow> is_widest_spread ws (k+1) ps"
  using is_widest_spread_def less_Suc_eq by auto

lemma is_widest_spread_k_gt_ws:
  "is_widest_spread ws k ps \<Longrightarrow> \<not> (spread_set k ps \<le> spread_set ws ps) \<Longrightarrow> is_widest_spread k (k+1) ps"
  using is_widest_spread_def less_Suc_eq by auto

lemma widest_spread_rec_le_a:
  "ps \<noteq> [] \<Longrightarrow> (ws, s) = widest_spread_rec a ps \<Longrightarrow> ws \<le> a"
  by (induction a arbitrary: ws s) (auto simp add: Let_def le_Suc_eq split: prod.splits if_splits)

lemma widest_spread_rec_is_widest_spread:
  "ps \<noteq> [] \<Longrightarrow> (ws, s) = widest_spread_rec a ps \<Longrightarrow> is_widest_spread ws (a+1) (set ps)"
proof (induction a arbitrary: ws s)
  case 0
  thus ?case
    using is_widest_spread_def by simp
next
  case (Suc a)
  then obtain ws' s' where *: "(ws', s') = widest_spread_rec a ps"
    by (metis surj_pair)
  hence "is_widest_spread ws' (Suc a) (set ps)"
    using Suc.IH Suc.prems(1) by simp
  then show ?case 
    using Suc.prems * spread_is_spread_set widest_spread_rec_is_spread 
    is_widest_spread_k_le_ws[of ws' "Suc a" "set ps"] is_widest_spread_k_gt_ws[of ws' "Suc a" "set ps"]
    by (auto simp add: Let_def split: prod.splits if_splits)
qed

lemma widest_spread_lt_k:
  "\<forall>p \<in> set ps. dim p = k \<Longrightarrow> 0 < k \<Longrightarrow> ps \<noteq> [] \<Longrightarrow> widest_spread ps < k"
  using widest_spread_def widest_spread_rec_le_a
  apply (auto split: prod.splits)
  by (metis Suc_le_lessD Suc_le_mono Suc_pred)

lemma widest_spread_is_widest_spread:
  assumes "ps \<noteq> []" "\<forall>p \<in> set ps. dim p = k"
  shows "is_widest_spread (widest_spread ps) k (set ps)"
proof (cases k)
  case 0
  then show ?thesis
    using is_widest_spread_def by simp
next
  case (Suc n)
  obtain ws s where *: "(ws, s) = widest_spread_rec (dim (hd ps) - 1) ps"
    using prod.collapse by blast
  moreover have "dim (hd ps) = k"
    using assms(1,2) by simp
  ultimately have "is_widest_spread ws (k - 1 + 1) (set ps)"
    using widest_spread_rec_is_widest_spread assms(1) by simp 
  hence "is_widest_spread ws k (set ps)"
    using Suc by simp
  thus ?thesis
    using * widest_spread_def by (auto split: prod.split)
qed


subsection "Partitioning a List of Points by Median"

definition axis_median :: "axis \<Rightarrow> point list \<Rightarrow> real" where
  "axis_median a ps = (
    let n = (length ps - 1) div 2  in
    let ps' = map (\<lambda>p. p!a) ps in
    fast_select n ps'
  )"

lemma size_mset_map_P:
  "size {# y \<in># mset (map f xs). P y #} = size {# x \<in># mset xs. P (f x) #}"
  by (induction xs) auto

lemma size_axis_median_length:
  assumes "0 < length ps"
  shows "size {# p \<in># mset ps. p!a < axis_median a ps #} \<le> (length ps - 1) div 2" (is "?thesis1")
    and "size {# p \<in># mset ps. axis_median a ps < p!a #} \<le> length ps div 2"       (is "?thesis2")
proof -
  let ?n = "(length ps - 1) div 2"
  let ?ps' = "map (\<lambda>p. p!a) ps"
  let ?m = "fast_select ?n ?ps'"

  have "length ps = length ?ps'"
    by simp
  moreover have "?n < length ?ps'"
    using assms calculation by linarith
  ultimately have *: "median ?ps' = ?m"
    using median_def fast_select_correct by metis

  have "size {# a \<in># mset ?ps'. a < ?m #} \<le> (length ps - 1) div 2"
    using * size_less_than_median[of ?ps'] by simp
  hence "size {# p \<in># mset ps. p!a < ?m #} \<le> (length ps - 1) div 2"
    using size_mset_map_P[of "\<lambda>a. a < ?m"] by metis
  thus ?thesis1
    using axis_median_def by metis
  
  have "size {# a \<in># mset ?ps'. ?m < a #} \<le> length ps div 2"
    using * size_greater_than_median[of ?ps'] by simp
  hence "size {# p \<in># mset ps. ?m < p!a #} \<le> length ps div 2"
    using size_mset_map_P[of "\<lambda>a. ?m < a"] by metis
  thus ?thesis2 
    using axis_median_def by metis
qed


subsubsection "Threeway Partitioning a List of Points"

fun partition :: "axis \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point list * point list * point list" where
  "partition _ _ [] = ([], [], [])"
| "partition a m (p # ps) = (
    let (lt, eq, gt) = partition a m ps in
    if p!a < m then 
      (p # lt, eq, gt)
    else if p!a = m then 
      (lt, p # eq, gt)
    else 
      (lt, eq, p # gt)
  )"

lemma partition_set:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "set ps = set lt \<union> set eq \<union> set gt"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_mset:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "mset lt = {# p \<in># mset ps. p!a < m #}"
    and "mset eq = {# p \<in># mset ps. p!a = m #}"
    and "mset gt = {# p \<in># mset ps. m < p!a #}"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_filter:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "\<forall>p \<in> set lt. p!a < m"
    and "\<forall>p \<in> set eq. p!a = m"
    and "\<forall>p \<in> set gt. m < p!a"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_length:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "length ps = length lt + length eq + length gt"
    and "length lt = size {# p \<in># mset ps. p!a < m #}"
    and "length eq = size {# p \<in># mset ps. p!a = m #}"
    and "length gt = size {# p \<in># mset ps. m < p!a #}"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)


subsubsection "Partitioning a List of Points balanced by Median"

definition partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "partition_by_median a ps = (
     let m = axis_median a ps in
     let (lt, eq, gt) = partition a m ps in
     let rem = length ps div 2 - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"

lemma set_take_drop: "set xs = set (take n xs) \<union> set (drop n xs)"
  by (metis append_take_drop_id set_append)

lemma partition_by_median_set:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "set ps = set l \<union> set r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def split: prod.splits)
  using set_take_drop by (metis partition_set inf_sup_aci(6))

lemma partition_by_median_filter:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "\<forall>p \<in> set l. p!a \<le> m"
    and "\<forall>p \<in> set r. m \<le> p!a"
  using assms unfolding partition_by_median_def
  apply (auto simp add: Let_def split: prod.splits)
  by (metis le_less dual_order.refl in_set_takeD in_set_dropD partition_filter)+

lemma partition_by_median_length_1:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "length ps = length l + length r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def min_def split: prod.splits)
  by (metis (no_types, lifting) add.assoc partition_length(1))

lemma partition_by_median_length_2:
  assumes "(l, m, r) = partition_by_median a ps" "0 < length ps"
  shows "length r - length l \<le> 1"
    and "length l \<le> length r"
proof -
  let ?m = "axis_median a ps"
  let ?leg = "partition a ?m ps"
  let ?lt = "fst ?leg"
  let ?eq = "fst (snd ?leg)"
  let ?gt = "snd (snd ?leg)"
  let ?rem = "length ps div 2 - length ?lt"
  let ?l = "?lt @ take ?rem ?eq"
  let ?r = "drop ?rem ?eq @ ?gt"

  have *: "(?lt, ?eq, ?gt) = partition a ?m ps"
    by simp
  have "length ?lt \<le> (length ps - 1) div 2"
    using assms * partition_length(2) size_axis_median_length(1) by presburger
  moreover have "length ?gt \<le> length ps div 2"
    using assms * partition_length(4) size_axis_median_length(2) by presburger
  moreover have "length ps = length ?lt + length ?eq + length ?gt"
    using * partition_length(1) by simp
  ultimately have L: "length ?l = length ps div 2"
    by simp

  have **: "(?l, ?m, ?r) = partition_by_median a ps"
    by (auto simp add: Let_def partition_by_median_def split: prod.splits)
  hence "length ps = length ?l + length ?r"
    using partition_by_median_length_1 by blast
  hence "length ?l \<le> length ?r" "length ?r - length ?l \<le> 1"
    using L by linarith+

  thus "length l \<le> length r" "length r - length l \<le> 1" 
    using ** by (metis Pair_inject assms(1))+
qed

lemma partition_by_median_length_3: 
  assumes "(l, m, r) = partition_by_median a ps" "0 < length ps"
  shows "length l < length ps"
proof (rule ccontr)
  assume *: "\<not> (length l < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length l = length ps" "length r = 0"
    using * by simp_all
  moreover have "length l \<le> length r"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_4: 
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "length r < length ps"
proof (rule ccontr)
  assume *: "\<not> (length r < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length r = length ps" "length l = 0"
    using * by simp_all
  moreover have "length r - length l \<le> 1"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_5:
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "0 < length l"
    and "0 < length r"
  using assms partition_by_median_length_1 partition_by_median_length_4 apply simp
  using assms partition_by_median_length_1 partition_by_median_length_3 by fastforce

lemmas partition_by_median_length = 
  partition_by_median_length_1 partition_by_median_length_2
  partition_by_median_length_3 partition_by_median_length_4
  partition_by_median_length_5


subsection \<open>Building the Tree\<close>

function (sequential) build :: "dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build _ [] = undefined" (* We never hit this case recursively. Only if the original input is really [].*)
| "build k [p] = Leaf p" 
| "build k ps = (
    let a = widest_spread ps in
    let (l, m, r) = partition_by_median a ps in
    Node a m (build k l) (build k r)
  )"
  by pat_completeness auto
termination build
  using partition_by_median_length(4,5)
  apply (relation "measure (\<lambda>( _, ps). length ps)")
  apply (auto)
  apply fastforce+
  done


text \<open>
  Setting up different build simps for length induct.
\<close>

lemma build_simp_1:
  "ps = [p] \<Longrightarrow> build k ps = Leaf p"
  by simp

lemma build_simp_2:
  "ps = p\<^sub>0 # p\<^sub>1 # ps' \<Longrightarrow> a = widest_spread ps \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build k ps = Node a m (build k l) (build k r)"
  using build.simps(3) by (auto simp add: Let_def split: prod.splits)

lemma length_ps_gt_1:
  "1 < length ps \<Longrightarrow> \<exists>p\<^sub>0 p\<^sub>1 ps'. ps = p\<^sub>0 # p\<^sub>1 # ps'"
  by (induction ps) (auto simp add: neq_Nil_conv)

lemma build_simp_3:
  "1 < length ps \<Longrightarrow> a = widest_spread ps \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build k ps = Node a m (build k l) (build k r)"
  using build_simp_2 length_ps_gt_1 by fast

lemmas build_simps[simp] = build_simp_1 build_simp_3

declare build.simps[simp del]


text \<open>
  The main theorems.
\<close>

theorem build_set:
  assumes "0 < length ps"
  shows "set ps = set_kdt (build k ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis
      by simp
  next
    case False

    let ?a = "widest_spread ps"
    let ?lmr = "partition_by_median ?a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have "set ?l = set_kdt (build k ?l)" "set ?r = set_kdt (build k ?r)" 
      using False partition_by_median_length(4,5,6,7)[of ?l ?m ?r ?a ps] "1.IH" by force+
    moreover have "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "build k ps = Node ?a ?m (build k ?l) (build k ?r)"
      using False by simp
    ultimately show ?thesis
      by auto
  qed
qed

theorem build_invar:
  assumes "0 < length ps" "\<forall>p \<in> set ps. dim p = k" "distinct ps" "0 < k"
  shows "invar k (build k ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where P: "ps = [p]"
      using "1.prems"(1) by (cases ps) auto
    hence "dim p = k"
      using "1.prems"(2) by simp
    thus ?thesis
      using P by simp
  next
    case False

    let ?a = "widest_spread ps"
    let ?lmr = "partition_by_median ?a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 1: "length ps = length ?l + length ?r"
      using partition_by_median_length(1) by (metis prod.collapse)+
    hence 2: "length ?l < length ps" "length ?r < length ps"
      using False partition_by_median_length(4,5) not_le_imp_less "1.prems" by (metis prod.collapse)+
    hence 3: "0 < length ?l" "0 < length ?r"
      using 1 False partition_by_median_length(6,7) by simp_all
    moreover have 4: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "distinct ?l" "distinct ?r" and 5: "set ?l \<inter> set ?r = {}"
      using "1.prems"(3) 1 4 by (metis card_distinct distinct_append distinct_card length_append set_append)+
    moreover have "\<forall>p \<in> set ?l .dim p = k" "\<forall>p \<in> set ?r .dim p = k"
      using "1.prems"(2) 4 5 by simp_all
    ultimately have "invar k (build k ?l)" "invar k (build k ?r)"
      using "1.IH" 2 by (simp_all add: "1.prems"(4))
    moreover have "\<forall>p \<in> set ?l. p ! ?a \<le> ?m" "\<forall>p \<in> set ?r. ?m \<le> p ! ?a"
      using partition_by_median_filter by (metis prod.collapse)+
    moreover have "build k ps = Node ?a ?m (build k ?l) (build k ?r)"
      using False by simp
    moreover have "?a < k"
      using "1.prems"(1,2,4) widest_spread_lt_k by auto
    ultimately show ?thesis 
      using 3 5 build_set by auto
  qed
qed

theorem build_widest_spread:
  assumes "0 < length ps" "\<forall>p \<in> set ps. dim p = k"
  shows "widest_spread_invar k (build k ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a = "widest_spread ps"
    let ?lmr = "partition_by_median ?a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 1: "length ps = length ?l + length ?r"
      using partition_by_median_length(1) by (metis prod.collapse)+
    hence 2: "length ?l < length ps" "length ?r < length ps"
      using False partition_by_median_length(4,5) not_le_imp_less "1.prems" by (metis prod.collapse)+
    hence 3: "0 < length ?l" "0 < length ?r"
      using 1 False partition_by_median_length(6,7) by simp_all
    moreover have 4: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "\<forall>p \<in> set ?l .dim p = k" "\<forall>p \<in> set ?r .dim p = k"
      using "1.prems"(2) 4 by simp_all
    ultimately have "widest_spread_invar k (build k ?l)" "widest_spread_invar k (build k ?r)"
      using "1.IH" 2 by simp_all
    moreover have "is_widest_spread ?a k (set_kdt (build k ?l) \<union> set_kdt (build k ?r))"
      using widest_spread_is_widest_spread "1.prems" 3 4 build_set by fastforce
    moreover have "build k ps = Node ?a ?m (build k ?l) (build k ?r)"
      using False by simp
    ultimately show ?thesis
      by auto
  qed
qed

theorem build_size:
  assumes "0 < length ps"
  shows "size_kdt (build k ps) = length ps"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a = "widest_spread ps"
    let ?lmr = "partition_by_median ?a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have "size_kdt (build k ?l) = length ?l" "size_kdt (build k ?r) = length ?r" 
      using False partition_by_median_length(4,5,6,7)[of ?l ?m ?r ?a ps] "1.IH" by force+
    moreover have "build k ps = Node ?a ?m (build k ?l) (build k ?r)"
      using False by simp
    ultimately show ?thesis
      using partition_by_median_length(1) by (metis prod.collapse size_kdt.simps(2))
  qed
qed

theorem build_balanced:
  assumes "0 < length ps"
  shows "balanced (build k ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis 
      unfolding balanced_def by simp
  next
    case False

    let ?a = "widest_spread ps"
    let ?lmr = "partition_by_median ?a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 0: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using partition_by_median_length(1,2,3) "1.prems" by (metis prod.collapse)+
    hence 1: "length ?l + 1 = length ?r \<or> length ?l = length ?r"
      by linarith
    moreover have 2: "length ?l < length ps" "length ?r < length ps"
      using False 0 by auto
    moreover have 3: "0 < length ?l" "0 < length ?r"
      using "1.prems" 0 1 2 by linarith+
    ultimately have 4: "balanced (build k ?l)" "balanced (build k ?r)"
      using "1.IH" by simp_all
    have "build k ps = Node ?a ?m (build k ?l) (build k ?r)"
      using False by simp
    moreover have "size_kdt (build k ?l) + 1 = size_kdt (build k ?r) \<or> size_kdt (build k ?l) = size_kdt (build k ?r)"
      using 1 3 build_size by simp
    ultimately show ?thesis
      using 4 balanced_Node_if_wbal2 by auto
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
    using balanced_def by simp
  thus "False"
    using assms(1) by simp
qed

theorem build_complete:
  assumes "length ps = 2 ^ h"
  shows "complete (build k ps)"
  using assms complete_if_balanced_size_2powh
  by (simp add: build_balanced build_size)

corollary build_height:
  "length ps = 2 ^ h \<Longrightarrow> length ps = 2 ^ (height (build k ps))"
  using build_complete build_size complete_iff_size by auto

end