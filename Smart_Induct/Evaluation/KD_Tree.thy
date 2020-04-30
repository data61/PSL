(*
  File:     KD_Tree.thy
  Author:   Martin Rau, TU München
*)

section "Definition of the \<open>k\<close>-d Tree"

theory KD_Tree
imports
  Complex_Main
  "HOL-Analysis.Finite_Cartesian_Product"
  "HOL-Analysis.Topology_Euclidean_Space"
begin


text \<open>
  A \<open>k\<close>-d tree is a space-partitioning data structure for organizing points in a \<open>k\<close>-dimensional space.
  In principle the \<open>k\<close>-d tree is a binary tree. The leafs hold the \<open>k\<close>-dimensional points and the nodes
  contain left and right subtrees as well as a discriminator \<open>v\<close> at a particular axis \<open>k\<close>.
  Every node divides the space into two parts by splitting along a hyperplane.
  Consider a node \<open>n\<close> with associated discriminator \<open>v\<close> at axis \<open>k\<close>.
  All points in the left subtree must have a value at axis \<open>k\<close> that is less than or
  equal to \<open>v\<close> and all points in the right subtree must have a value at axis \<open>k\<close> that is
  greater than \<open>v\<close>.

  Deviations from the papers:

  The chosen tree representation is taken from @{cite "DBLP:journals/toms/FriedmanBF77"} with one minor
  adjustment. Originally the leafs hold buckets of points of size \<open>b\<close>. This representation fixes the
  bucket size to \<open>b = 1\<close>, a single point per Leaf. This is only a minor adjustment since the paper
  proves that \<open>b = 1\<close> is the optimal bucket size for minimizing the running time of the nearest neighbor
  algorithm @{cite "DBLP:journals/toms/FriedmanBF77"}, only simplifies building the optimized
  \<open>k\<close>-d trees @{cite "DBLP:journals/toms/FriedmanBF77"} and has little influence on the
  search algorithm @{cite "DBLP:journals/cacm/Bentley75"}.
\<close>

type_synonym 'k point = "(real, 'k) vec"

lemma dist_point_def:
  fixes p\<^sub>0 :: "('k::finite) point"
  shows "dist p\<^sub>0 p\<^sub>1 = sqrt (\<Sum>k \<in> UNIV. (p\<^sub>0$k - p\<^sub>1$k)\<^sup>2)"
  unfolding dist_vec_def L2_set_def dist_real_def by simp

datatype 'k kdt =
  Leaf "'k point"
| Node 'k real "'k kdt" "'k kdt"


subsection \<open>Definition of the \<open>k\<close>-d Tree Invariant and Related Functions\<close>

fun set_kdt :: "'k kdt \<Rightarrow> ('k point) set" where
  "set_kdt (Leaf p) = { p }"
| "set_kdt (Node _ _ l r) = set_kdt l \<union> set_kdt r"

definition spread :: "('k::finite) \<Rightarrow> 'k point set \<Rightarrow> real" where
  "spread k P = (if P = {} then 0 else let V = (\<lambda>p. p$k) ` P in Max V - Min V)"

definition widest_spread_axis :: "('k::finite) \<Rightarrow> 'k set \<Rightarrow> 'k point set \<Rightarrow> bool" where
  "widest_spread_axis k K ps \<longleftrightarrow> (\<forall>k' \<in> K. spread k' ps \<le> spread k ps)"

fun invar :: "('k::finite) kdt \<Rightarrow> bool" where
  "invar (Leaf p) \<longleftrightarrow> True"
| "invar (Node k v l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p$k \<le> v) \<and> (\<forall>p \<in> set_kdt r. v < p$k) \<and>
    widest_spread_axis k UNIV (set_kdt l \<union> set_kdt r) \<and> invar l \<and> invar r"

fun size_kdt :: "'k kdt \<Rightarrow> nat" where
  "size_kdt (Leaf _) = 1"
| "size_kdt (Node _ _ l r) = size_kdt l + size_kdt r"

fun height :: "'k kdt \<Rightarrow> nat" where
  "height (Leaf _) = 0"
| "height (Node _ _ l r) = max (height l) (height r) + 1"

fun min_height :: "'k kdt \<Rightarrow> nat" where
  "min_height (Leaf _) = 0"
| "min_height (Node _ _ l r) = min (min_height l) (min_height r) + 1"

definition balanced :: "'k kdt \<Rightarrow> bool" where
  "balanced kdt \<longleftrightarrow> height kdt - min_height kdt \<le> 1"

fun complete :: "'k kdt \<Rightarrow> bool" where
  "complete (Leaf _) = True"
| "complete (Node _ _ l r) \<longleftrightarrow> complete l \<and> complete r \<and> height l = height r"


lemma invar_l:
  "invar (Node k v l r) \<Longrightarrow> invar l"
  by simp

lemma invar_r:
  "invar (Node k v l r) \<Longrightarrow> invar r"
  by simp

lemma invar_l_le_k:
  "invar (Node k v l r) \<Longrightarrow> \<forall>p \<in> set_kdt l. p$k \<le> v"
  by simp

lemma invar_r_ge_k:
  "invar (Node k v l r) \<Longrightarrow> \<forall>p \<in> set_kdt r. v < p$k"
  by simp

lemma invar_set:
  "set_kdt (Node k v l r) = set_kdt l \<union> set_kdt r"
  by simp


subsection \<open>Lemmas adapted from \<open>HOL-Library.Tree\<close> to \<open>k\<close>-d Tree\<close>

lemma size_ge0[simp]:
  "0 < size_kdt kdt"
  by (induction kdt) auto

lemma eq_size_1[simp]:
  "size_kdt kdt = 1 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  apply (induction kdt)
  apply (auto)
  using size_ge0 nat_less_le apply blast+
  done

lemma eq_1_size[simp]:
  "1 = size_kdt kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  using eq_size_1 by metis

lemma neq_Leaf_iff:
  "(\<nexists>p. kdt = Leaf p) = (\<exists>k v l r. kdt = Node k v l r)"
  by (cases kdt) auto

lemma eq_height_0[simp]:
  "height kdt = 0 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_0_height[simp]:
  "0 = height kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_min_height_0[simp]:
  "min_height kdt = 0 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_0_min_height[simp]:
  "0 = min_height kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma size_height:
  "size_kdt kdt \<le> 2 ^ height kdt"
proof(induction kdt)
  case (Node k v l r)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    have "size_kdt (Node k v l r) = size_kdt l + size_kdt r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r" using Node.IH by arith
    also have "\<dots> \<le> 2 ^ height r + 2 ^ height r" using True by simp
    also have "\<dots> = 2 ^ height (Node k v l r)"
      using True by (auto simp: max_def mult_2)
    finally show ?thesis .
  next
    case False
    have "size_kdt (Node k v l r) = size_kdt l + size_kdt r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r" using Node.IH by arith
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height l" using False by simp
    finally show ?thesis using False by (auto simp: max_def mult_2)
  qed
qed simp

lemma min_height_le_height:
  "min_height kdt \<le> height kdt"
  by (induction kdt) auto

lemma min_height_size:
  "2 ^ min_height kdt \<le> size_kdt kdt"
proof(induction kdt)
  case (Node k v l r)
  have "(2::nat) ^ min_height (Node k v l r) \<le> 2 ^ min_height l + 2 ^ min_height r"
    by (simp add: min_def)
  also have "\<dots> \<le> size_kdt (Node k v l r)" using Node.IH by simp
  finally show ?case .
qed simp

lemma complete_iff_height:
  "complete kdt \<longleftrightarrow> (min_height kdt = height kdt)"
  apply (induction kdt)
  apply simp
  apply (simp add: min_def max_def)
  by (metis le_antisym le_trans min_height_le_height)

lemma size_if_complete:
  "complete kdt \<Longrightarrow> size_kdt kdt = 2 ^ height kdt"
  by (induction kdt) auto

lemma complete_if_size_height:
  "size_kdt kdt = 2 ^ height kdt \<Longrightarrow> complete kdt"
proof (induction "height kdt" arbitrary: kdt)
  case 0 thus ?case by auto
next
  case (Suc h)
  hence "\<nexists>p. kdt = Leaf p"
    by auto
  then obtain k v l r where [simp]: "kdt = Node k v l r"
    using neq_Leaf_iff by metis
  have 1: "height l \<le> h" and 2: "height r \<le> h" using Suc(2) by(auto)
  have 3: "\<not> height l < h"
  proof
    assume 0: "height l < h"
    have "size_kdt kdt = size_kdt l + size_kdt r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r"
      using size_height[of l] size_height[of r] by arith
    also have " \<dots> < 2 ^ h + 2 ^ height r" using 0 by (simp)
    also have " \<dots> \<le> 2 ^ h + 2 ^ h" using 2 by (simp)
    also have "\<dots> = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size_kdt kdt" using Suc(2,3) by simp
    finally have "size_kdt kdt < size_kdt kdt" .
    thus False by (simp)
  qed
  have 4: "\<not> height r < h"
  proof
    assume 0: "height r < h"
    have "size_kdt kdt = size_kdt l + size_kdt r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r"
      using size_height[of l] size_height[of r] by arith
    also have " \<dots> < 2 ^ height l + 2 ^ h" using 0 by (simp)
    also have " \<dots> \<le> 2 ^ h + 2 ^ h" using 1 by (simp)
    also have "\<dots> = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size_kdt kdt" using Suc(2,3) by simp
    finally have "size_kdt kdt < size_kdt kdt" .
    thus False by (simp)
  qed
  from 1 2 3 4 have *: "height l = h" "height r = h" by linarith+
  hence "size_kdt l = 2 ^ height l" "size_kdt r = 2 ^ height r"
    using Suc(3) size_height[of l] size_height[of r] by (auto)
  with * Suc(1) show ?case by simp
qed

lemma complete_if_size_min_height:
  "size_kdt kdt = 2 ^ min_height kdt \<Longrightarrow> complete kdt"
proof (induct "min_height kdt" arbitrary: kdt)
  case 0 thus ?case by auto
next
  case (Suc h)
  hence "\<nexists>p. kdt = Leaf p"
    by auto
  then obtain k v l r where [simp]: "kdt = Node k v l r"
    using neq_Leaf_iff by metis
  have 1: "h \<le> min_height l" and 2: "h \<le> min_height r" using Suc(2) by (auto)
  have 3: "\<not> h < min_height l"
  proof
    assume 0: "h < min_height l"
    have "size_kdt kdt = size_kdt l + size_kdt r" by simp
    also note min_height_size[of l]
    also(xtrans) note min_height_size[of r]
    also(xtrans) have "(2::nat) ^ min_height l > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height r \<ge> 2 ^ h" using 2 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size_kdt kdt" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  have 4: "\<not> h < min_height r"
  proof
    assume 0: "h < min_height r"
    have "size_kdt kdt = size_kdt l + size_kdt r" by simp
    also note min_height_size[of l]
    also(xtrans) note min_height_size[of r]
    also(xtrans) have "(2::nat) ^ min_height r > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height l \<ge> 2 ^ h" using 1 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size_kdt kdt" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  from 1 2 3 4 have *: "min_height l = h" "min_height r = h" by linarith+
  hence "size_kdt l = 2 ^ min_height l" "size_kdt r = 2 ^ min_height r"
    using Suc(3) min_height_size[of l] min_height_size[of r] by (auto)
  with * Suc(1) show ?case
    by (simp add: complete_iff_height)
qed

lemma complete_iff_size:
  "complete kdt \<longleftrightarrow> size_kdt kdt = 2 ^ height kdt"
  using complete_if_size_height size_if_complete by blast

lemma size_height_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> size_kdt kdt < 2 ^ height kdt"
  by (meson antisym_conv complete_iff_size not_le size_height)

lemma min_height_size_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> 2 ^ min_height kdt < size_kdt kdt"
  by (metis complete_if_size_min_height le_less min_height_size)

lemma balanced_subtreeL:
  "balanced (Node k v l r) \<Longrightarrow> balanced l"
  by (simp add: balanced_def)

lemma balanced_subtreeR:
  "balanced (Node k v l r) \<Longrightarrow> balanced r"
  by (simp add: balanced_def)

lemma balanced_optimal:
  assumes "balanced kdt" "size_kdt kdt \<le> size_kdt kdt'"
  shows "height kdt \<le> height kdt'"
proof (cases "complete kdt")
  case True
  have "(2::nat) ^ height kdt \<le> 2 ^ height kdt'"
  proof -
    have "2 ^ height kdt = size_kdt kdt"
      using True by (simp add: complete_iff_height size_if_complete)
    also have "\<dots> \<le> size_kdt kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'" by (rule size_height)
    finally show ?thesis .
  qed
  thus ?thesis by (simp)
next
  case False
  have "(2::nat) ^ min_height kdt < 2 ^ height kdt'"
  proof -
    have "(2::nat) ^ min_height kdt < size_kdt kdt"
      by(rule min_height_size_if_incomplete[OF False])
    also have "\<dots> \<le> size_kdt kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'"  by(rule size_height)
    finally have "(2::nat) ^ min_height kdt < (2::nat) ^ height kdt'" .
    thus ?thesis .
  qed
  hence *: "min_height kdt < height kdt'" by simp
  have "min_height kdt + 1 = height kdt"
    using min_height_le_height[of kdt] assms(1) False
    by (simp add: complete_iff_height balanced_def)
  with * show ?thesis by arith
qed


subsection \<open>Lemmas adapted from \<open>HOL-Library.Tree_Real\<close> to \<open>k\<close>-d Tree\<close>

lemma size_height_log:
  "log 2 (size_kdt kdt) \<le> height kdt"
  by (simp add: log2_of_power_le size_height)

lemma min_height_size_log:
  "min_height kdt \<le> log 2 (size_kdt kdt)"
  by (simp add: le_log2_of_power min_height_size)

lemma size_log_if_complete:
  "complete kdt \<Longrightarrow> height kdt = log 2 (size_kdt kdt)"
  using complete_iff_size log2_of_power_eq by blast

lemma min_height_size_log_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> min_height kdt < log 2 (size_kdt kdt)"
  by (simp add: less_log2_of_power min_height_size_if_incomplete)

lemma min_height_balanced:
  assumes "balanced kdt"
  shows "min_height kdt = nat(floor(log 2 (size_kdt kdt)))"
proof cases
  assume *: "complete kdt"
  hence "size_kdt kdt = 2 ^ min_height kdt"
    by (simp add: complete_iff_height size_if_complete)
  from log2_of_power_eq[OF this] show ?thesis by linarith
next
  assume *: "\<not> complete kdt"
  hence "height kdt = min_height kdt + 1"
    using assms min_height_le_height[of kdt]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size_kdt kdt < 2 ^ (min_height kdt + 1)"
    by (metis * size_height_if_incomplete)
  hence "log 2 (size_kdt kdt) < min_height kdt + 1"
    using log2_of_power_less size_ge0 by blast
  thus ?thesis using min_height_size_log[of kdt] by linarith
qed

lemma height_balanced:
  assumes "balanced kdt"
  shows "height kdt = nat(ceiling(log 2 (size_kdt kdt)))"
proof cases
  assume *: "complete kdt"
  hence "size_kdt kdt = 2 ^ height kdt"
    by (simp add: size_if_complete)
  from log2_of_power_eq[OF this] show ?thesis
    by linarith
next
  assume *: "\<not> complete kdt"
  hence **: "height kdt = min_height kdt + 1"
    using assms min_height_le_height[of kdt]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size_kdt kdt \<le> 2 ^ (min_height kdt + 1)" by (metis size_height)
  from  log2_of_power_le[OF this size_ge0] min_height_size_log_if_incomplete[OF *] **
  show ?thesis by linarith
qed

lemma balanced_Node_if_wbal1:
  assumes "balanced l" "balanced r" "size_kdt l = size_kdt r + 1"
  shows "balanced (Node k v l r)"
proof -
  from assms(3) have [simp]: "size_kdt l = size_kdt r + 1" by simp
  have "nat \<lceil>log 2 (1 + size_kdt r)\<rceil> \<ge> nat \<lceil>log 2 (size_kdt r)\<rceil>"
    by(rule nat_mono[OF ceiling_mono]) simp
  hence 1: "height(Node k v l r) = nat \<lceil>log 2 (1 + size_kdt r)\<rceil> + 1"
    using height_balanced[OF assms(1)] height_balanced[OF assms(2)]
    by (simp del: nat_ceiling_le_eq add: max_def)
  have "nat \<lfloor>log 2 (1 + size_kdt r)\<rfloor> \<ge> nat \<lfloor>log 2 (size_kdt r)\<rfloor>"
    by(rule nat_mono[OF floor_mono]) simp
  hence 2: "min_height(Node k v l r) = nat \<lfloor>log 2 (size_kdt r)\<rfloor> + 1"
    using min_height_balanced[OF assms(1)] min_height_balanced[OF assms(2)]
    by (simp)
  have "size_kdt r \<ge> 1" by (simp add: Suc_leI)
  then obtain i where i: "2 ^ i \<le> size_kdt r" "size_kdt r < 2 ^ (i + 1)"
    using ex_power_ivl1[of 2 "size_kdt r"] by auto
  hence i1: "2 ^ i < size_kdt r + 1" "size_kdt r + 1 \<le> 2 ^ (i + 1)" by auto
  from 1 2 floor_log_nat_eq_if[OF i] ceiling_log_nat_eq_if[OF i1]
  show ?thesis by(simp add:balanced_def)
qed

lemma balanced_sym:
  "balanced (Node k v l r) \<Longrightarrow> balanced (Node k' v' r l)"
  by (auto simp: balanced_def)

lemma balanced_Node_if_wbal2:
  assumes "balanced l" "balanced r" "abs(int(size_kdt l) - int(size_kdt r)) \<le> 1"
  shows "balanced (Node k v l r)"
proof -
  have "size_kdt l = size_kdt r \<or> (size_kdt l = size_kdt r + 1 \<or> size_kdt r = size_kdt l + 1)" (is "?A \<or> ?B")
    using assms(3) by linarith
  thus ?thesis
  proof
    assume "?A"
    thus ?thesis using assms(1,2)
      apply(simp add: balanced_def min_def max_def)
      by (metis assms(1,2) balanced_optimal le_antisym le_less)
  next
    assume "?B"
    thus ?thesis
      by (meson assms(1,2) balanced_sym balanced_Node_if_wbal1)
  qed
qed

end
