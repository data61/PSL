(*
  File:     Nearest_Neighbors.thy
  Author:   Martin Rau, TU München
*)

section "Nearest Neighbor Search on the \<open>k\<close>-d Tree"

theory Nearest_Neighbors
imports 
  KDTree
begin

text \<open>
  Verifying nearest neighbor search on the k-d tree.
  Given a \<open>k\<close>-d tree and a point \<open>p\<close>, which might not be in the tree, find the points \<open>ms\<close> which are
  closest to \<open>p\<close> by some metric.
  The chosen metric is the euclidean distance between two points.
  To avoid working with roots I will work with the squared euclidean distance.
\<close>

subsection "Definition of the Squared Euclidean Distance"

definition sqed' :: "real \<Rightarrow> real \<Rightarrow> real" where
  "sqed' x y = (x - y) ^ 2"

fun sqed :: "point \<Rightarrow> point \<Rightarrow> real" where
  "sqed [] [] = 0"
| "sqed (x # xs) (y # ys) = sqed' x y + sqed xs ys"
| "sqed _ _ = undefined"

definition min_by_sqed :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "min_by_sqed p\<^sub>0 p\<^sub>1 q = (
    if sqed p\<^sub>0 q \<le> sqed p\<^sub>1 q then p\<^sub>0 else p\<^sub>1
  )"

lemma sqed'_ge_0:
  "0 \<le> sqed' x y"
  by (simp add: sqed'_def)

lemma sqed'_eq_0[simp]:
  "sqed' x y = 0 \<longleftrightarrow> x = y"
  by (simp add: sqed'_def)

lemma sqed'_com:
  "sqed' x y = sqed' y x"
  by (simp add: sqed'_def power2_commute)

lemma inequality:
  assumes "(x::real) \<le> 0" "y \<le> 0"
  shows "x\<^sup>2 + y\<^sup>2 \<le> (x + y)\<^sup>2"
proof -
  have "x\<^sup>2 + y\<^sup>2 \<le> x\<^sup>2 + 2 * x * y + y\<^sup>2"
    using assms by (simp add: zero_le_mult_iff)
  also have "... = (x + y)\<^sup>2"
    by algebra
  finally show ?thesis .
qed

lemma sqed'_split:
  "x \<le> s \<Longrightarrow> s \<le> y \<Longrightarrow> sqed' x s + sqed' s y \<le> sqed' x y"
  using inequality[of "x - s" "s - y"] sqed'_def by simp

lemma sqed_ge_0:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> 0 \<le> sqed p\<^sub>0 p\<^sub>1"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  "p\<^sub>0 = p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_eq_0_rev:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0 \<Longrightarrow> p\<^sub>0 = p\<^sub>1"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: add_nonneg_eq_0_iff sqed'_ge_0 sqed_ge_0)

lemma sqed_com:
  "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)


subsection "The recursive Nearest Neighbor Algorithm"

fun nearest_nbors :: "nat \<Rightarrow> point list \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "nearest_nbors m ns p (Leaf p') = (
    take m (insort_key (\<lambda>q. sqed q p) p' ns)
  )"
| "nearest_nbors m ns p (Node a s l r) = (
    if p!a \<le> s then
      let candidates = nearest_nbors m ns p l in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        nearest_nbors m candidates p r
    else
      let candidates = nearest_nbors m ns p r in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        nearest_nbors m candidates p l
  )"


text \<open>
  Some intuition about the following auxiliary lemmas.

  Scenario A:

  We are searching for the nearest neighbor of point \<open>p\<close> and have found candidate \<open>c\<close> at axis \<open>a\<close>.
  Since @{term "sqed c p \<le> sqed' s (p!a)"} we do not need to check the right side.

\begin{alltt}
                                s
          c                     |
                                |
               p                |
                                |
                                |  q
                                |
\end{alltt}

  Scenario B:
  We are searching for the nearest neighbor of point \<open>p\<close> and have found candidate \<open>c\<close> at axis \<open>a\<close>.
  Since @{term "sqed' s (p!a) < sqed c p"} we do need to check the right side.

\begin{alltt}
                                s
          c                     |
                                |
                          p     |  q'
                                |
                                |  q
                                |
\end{alltt}

  The minimize sqed lemma moves \<open>q\<close> to \<open>q'\<close> by setting all coordinates of \<open>q'\<close> (except the current axis \<open>a\<close>)
  to the coordinates of \<open>p\<close> and minimizes subsequently the distance between \<open>p\<close> and \<open>q'\<close>.
\<close>

lemma minimize_sqed:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "a < k"
  shows "sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a) \<le> sqed p\<^sub>0 p\<^sub>1"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a k rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (meson dual_order.trans le_add_same_cancel2 sqed'_ge_0)

lemma cutoff_r:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "p!a \<le> s" "sqed p c \<le> sqed' (p!a) s"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  have 0: "s \<le> q!a"
    using * assms(1) invar_r_ge_a by blast
  have 1: "sqed' (p!a) (?q'!a) \<le> sqed p q"
    using * minimize_sqed assms(1,2) invar_axis_lt_d invar_dim invar_r by blast

  have "sqed p c \<le> sqed' (p!a) s"
    using assms(4) by blast
  also have "... \<le> sqed' (p!a) s + sqed' s (q!a)"
    using sqed'_ge_0 by simp
  also have "... \<le> sqed' (p!a) (q!a)"
    using 0 sqed'_split assms(3) by simp
  also have "... \<le> sqed p q"
    using 1 assms(1,2) by simp
  finally show "sqed p c \<le> sqed p q" .
qed

lemma cutoff_l:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "s \<le> p!a" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have 0: "q!a \<le> s"
    using * assms(1) invar_l_le_a by blast
  have 1: "sqed' (p!a) (?q'!a) \<le> sqed p q"
    using * minimize_sqed assms(1,2) invar_axis_lt_d invar_dim invar_l by blast

  have "sqed p c \<le> sqed' s (p!a)"
    using assms(4) by blast
  also have "... \<le> sqed' s (p!a) + sqed' (q!a) s"
    using sqed'_ge_0 by simp
  also have "... \<le> sqed' (p!a) (q!a)"
    using 0 sqed'_split assms(3) by (metis add.commute sqed'_com)
  also have "... \<le> sqed p q"
    using 1 assms(1,2) by simp
  finally show "sqed p c \<le> sqed p q" .
qed


subsection "Auxiliary Lemmas abount \<open>sorted_wrt\<close>"

definition sorted_sqed :: "point \<Rightarrow> point list \<Rightarrow> bool" where
  "sorted_sqed p \<equiv> sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p)"

definition insort_sqed :: "point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point list" where
  "insort_sqed p \<equiv> insort_key (\<lambda>q. sqed q p)"

declare sorted_sqed_def[simp] insort_sqed_def[simp]

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  have "sorted_wrt f (take n xs @ drop n xs)" 
    using assms by simp
  thus "sorted_wrt f (take n xs)" "sorted_wrt f (drop n xs)"
    using sorted_wrt_append by blast+
qed

lemma sorted_insort_sqed:
  "sorted_sqed p ms \<Longrightarrow> sorted_sqed p (insort_sqed p p' ms)"
  apply (induction ms)
  apply (auto)
  by (metis insert_iff le_cases set_insort_key)

lemma sorted_sqed_take_insort:
  assumes "sorted_sqed p ms"
  shows "sorted_sqed p (take m (insort_sqed p p' ms))"
proof -
  have "sorted_sqed p (insort_sqed p p' ms)"
    using assms sorted_insort_sqed by blast
  thus ?thesis 
    using sorted_wrt_take by auto
qed

lemma sorted_sqed_take_drop:
  assumes "sorted_sqed p ps"
  shows "\<forall>p\<^sub>0 \<in> set (take n ps). \<forall>p\<^sub>1 \<in> set (drop n ps). sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p"
  using assms sorted_wrt_append[of _ "take n ps" "drop n ps"] by simp

lemma sorted_sqed_last:
  assumes "sorted_sqed p ps"
  shows "\<forall>n \<in> set ps. sqed n p \<le> sqed (last ps) p"
proof (cases "ps = []")
  case True
  thus ?thesis by simp
next
  case False
  then obtain ps' p' where [simp]:"ps = ps' @ [p']"
    using rev_exhaust by blast
  hence "sorted_sqed p (ps' @ [p'])"
    using assms by blast
  thus ?thesis
    using sorted_wrt_append[of _ ps' "[p']"] by simp
qed

lemma sorted_sqed_take_insort_mono:
  assumes "sorted_sqed p ms"
  shows "\<forall>n \<in> set ms \<union> {p'} - set (take m (insort_sqed p p' ms)). \<forall>n' \<in> set (take m (insort_sqed p p' ms)). sqed n' p \<le> sqed n p"
proof -
  let ?ms' = "insort_sqed p p' ms"
  have "set ms \<union> {p'} = set ?ms'"
    by (simp add: set_insort_key)
  moreover have "set ?ms' = set (take m ?ms') \<union> set (drop m ?ms')"
    using append_take_drop_id set_append by metis
  ultimately have "set ms \<union> {p'} - set (take m ?ms') \<subseteq> set (drop m ?ms')"
    by blast
  moreover have "sorted_sqed p ?ms'"
    using assms sorted_insort_sqed by blast
  ultimately show ?thesis
    using sorted_sqed_take_drop by blast
qed

lemma sorted_sqed_last_take_mono:
  assumes "sorted_sqed p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (take m ms)) p \<le> sqed (last ms) p"
  using assms by (induction ms arbitrary: m) (auto simp add: take_Cons')

lemma sorted_sqed_last_insort_eq:
  assumes "sorted_sqed p ms" "insort_sqed p p' ms \<noteq> ms @ [p']"
  shows "last (insort_sqed p p' ms) = last ms"
  using assms by (induction ms) (auto)

lemma sorted_sqed_last_take_insort_mono:
  assumes "sorted_sqed p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (take m (insort_sqed p p' ms))) p \<le> sqed (last ms) p"
proof -
  let ?ms' = "insort_sqed p p' ms"
  show "sqed (last (take m ?ms')) p \<le> sqed (last ms) p"
  proof (cases "?ms' = ms @ [p']")
    case True
    thus ?thesis
      using assms sorted_sqed_last_take_mono by auto
  next
    case False
    hence EQ: "last ?ms' = last ms"
      using sorted_sqed_last_insort_eq assms by simp
    have "sqed (last (take m ?ms')) p \<le> sqed (last ?ms') p"
      using assms sorted_sqed_last_take_mono sorted_insort_sqed by simp
    thus ?thesis
      using EQ by simp
  qed
qed


subsection "The Main Theorems"

lemma mnn_length:
  "length (nearest_nbors m ms p kdt) = min m (size_kdt kdt + length ms)"
  by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_length_gt_0:
  assumes "0 < m"
  shows "0 < length (nearest_nbors m ms p kdt)"
  using assms by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_length_gt_eq_m:
  assumes "(set_kdt kdt \<union> set ms) - set (nearest_nbors m ms p kdt) \<noteq> {}"
  shows "length (nearest_nbors m ms p kdt) = m"
  using assms mnn_length set_insort_key
  apply (induction kdt arbitrary: ms)
  apply (auto simp add: min_def Let_def)
  by fastforce+

lemma mnn_sorted:
  assumes "sorted_sqed p ms"
  shows "sorted_sqed p (nearest_nbors m ms p kdt)"
  using assms sorted_sqed_take_insort
  by (induction kdt arbitrary: ms) (auto simp add: Let_def)

lemma mnn_set:
  shows "set (nearest_nbors m ms p kdt) \<subseteq> set_kdt kdt \<union> set ms"
  using set_insort_key in_set_takeD
  apply (induction kdt arbitrary: ms)
  apply (auto simp add: Let_def)
  by fastforce

lemma mnn_distinct:
  assumes "invar k kdt" "dim p = k" "distinct ms" "set ms \<inter> set_kdt kdt = {}"
  shows "distinct (nearest_nbors m ms p kdt)"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')
  thus ?case
    by (simp add: distinct_insort)
next
  case (Node a s l r)

  let ?cl = "nearest_nbors m ms p l"
  let ?cr = "nearest_nbors m ms p r"

  have "set ms \<inter> set_kdt l = {} \<and> set ms \<inter> set_kdt r = {}"
    using Node.prems(4) by auto
  hence DCLR: "distinct ?cl \<and> distinct ?cr"
    using Node.IH(1,2) Node.prems(1,2,3) invar_l invar_r by blast

  have "set ?cl \<inter> set_kdt r = {} \<and> set ?cr \<inter> set_kdt l = {}"
    using Node.prems(1,4) mnn_set invar_distinct by fastforce
  hence "distinct (nearest_nbors m ?cl p r) \<and> distinct (nearest_nbors m ?cr p l)"
    using Node.IH(1,2) Node.prems(1,2) DCLR invar_l invar_r by blast

  thus ?case 
    using DCLR by (auto simp add: Let_def)
qed

lemma mnn_le_last_ms:
  assumes "invar k kdt" "dim p = k" "sorted_sqed p ms" "m \<le> length ms" "0 < m"
  shows "sqed (last (nearest_nbors m ms p kdt)) p \<le> sqed (last ms) p"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')

  let ?ms' = "take m (insort_sqed p p' ms)"

  have "sorted_sqed p ?ms'"
    using Leaf.prems(3) sorted_sqed_take_insort by simp
  hence "\<forall>n \<in> set ?ms'. sqed n p \<le> sqed (last ?ms') p"
    using sorted_sqed_last by blast
  hence "\<forall>n \<in> set ?ms'. sqed n p \<le> sqed (last ms) p"
    using Leaf.prems(3,4,5) sorted_sqed_last_take_insort_mono[of p ms m p'] order_trans by blast
  thus ?case
    using Leaf.prems(5) by simp
next
  case (Node a s l r)

  let ?cl = "nearest_nbors m ms p l"
  let ?cr = "nearest_nbors m ms p r"

  have "m \<le> length ?cl"
    using mnn_length Node.prems(4) by auto
  hence "sqed (last (nearest_nbors m ?cl p r)) p \<le> sqed (last ?cl) p"
    using mnn_sorted Node.IH(2) Node.prems(1,2,3,5) invar_r by blast
  hence IHLR: "sqed (last (nearest_nbors m ?cl p r)) p \<le> sqed (last ms) p"
    using Node.IH(1)[of ms] Node.prems invar_l mnn_length_gt_0 by (meson order_trans)

  have "m \<le> length ?cr"
    using mnn_length Node.prems(4) by auto
  hence "sqed (last (nearest_nbors m ?cr p l)) p \<le> sqed (last ?cr) p"
    using mnn_sorted Node.IH(1) Node.prems(1,2,3,5) invar_l by blast
  hence IHRL: "sqed (last (nearest_nbors m ?cr p l)) p \<le> sqed (last ms) p"
    using Node.IH(2)[of ms] Node.prems invar_r mnn_length_gt_0 by (meson order_trans)

  show ?case 
    using Node IHLR IHRL by (auto simp add: Let_def)
qed

theorem mnn_sqed:
  assumes "invar k kdt" "dim p = k"
  assumes "sorted_sqed p ms" "set ms \<inter> set_kdt kdt = {}" "distinct ms" "0 < m"
  shows "\<forall>q \<in> set_kdt kdt \<union> set ms - set (nearest_nbors m ms p kdt). sqed (last (nearest_nbors m ms p kdt)) p \<le> sqed q p"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')
  thus ?case
    using sorted_sqed_take_insort_mono by simp
next
  case (Node a s l r)

  let ?cl = "nearest_nbors m ms p l"
  let ?cr = "nearest_nbors m ms p r"

  have IHL: "\<forall>q \<in> set_kdt l \<union> set ms - set ?cl. sqed (last ?cl) p \<le> sqed q p"
    using Node.IH(1) Node.prems invar_l invar_set by blast
  have IHR: "\<forall>q \<in> set_kdt r \<union> set ms - set ?cr. sqed (last ?cr) p \<le> sqed q p"
    using Node.IH(2) Node.prems invar_r invar_set by blast

  have SORTED_L: "sorted_sqed p ?cl"
    using mnn_sorted Node.prems(3) by blast
  have SORTED_R: "sorted_sqed p ?cr"
    using mnn_sorted Node.prems(3) by blast

  have DISTINCT_L: "distinct ?cl"
    using Node.prems(1,2,4,5) mnn_distinct invar_set invar_l by blast
  have DISTINCT_R: "distinct ?cr"
    using Node.prems(1,2,4,5) mnn_distinct invar_set invar_r by blast

  consider (A) "p!a \<le> s \<and> length ?cl = m \<and> sqed p (last ?cl) \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>(length ?cl = m \<and> sqed p (last ?cl) \<le> sqed' s (p!a))"
         | (C) "s < p!a \<and> length ?cr = m \<and> sqed p (last ?cr) \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>(length ?cr = m \<and> sqed p (last ?cr) \<le> sqed' s (p!a))"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed (last ?cl) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_r by (metis sqed'_com sqed_com)
    thus ?thesis
      using IHL A by auto
  next
    case B

    let ?mnn = "nearest_nbors m ?cl p r"

    have "set ?cl \<subseteq> set_kdt l \<union> set ms \<and> set ms \<inter> set_kdt r = {}"
      using mnn_set Node.prems(1,4) by auto
    hence IHLR: "\<forall>q \<in> set_kdt r \<union> set ?cl - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using SORTED_L DISTINCT_L Node.IH(2) Node.prems(1,2,6) invar_r invar_distinct by blast

    have "\<forall>n \<in> set ms - set ?cl. sqed (last ?mnn) p \<le> sqed n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cl) p"
        using mnn_le_last_ms SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed n p"
        using IHL * by blast
      thus "sqed (last ?mnn) p \<le> sqed n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt r \<union> set ms - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHLR by auto

    have "\<forall>q \<in> set_kdt l - set ?cl. sqed (last ?mnn) p \<le> sqed q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt l - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cl) p"
        using mnn_le_last_ms SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed q p"
        using IHL * by blast
      thus "sqed (last ?mnn) p \<le> sqed q p"
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt l - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHLR by blast

    show ?thesis
      using B R L by auto
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed (last ?cr) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_l[of k a s l r p "last ?cr"] sqed_com by fastforce
    thus ?thesis
      using IHR C by auto
  next
    case D

    let ?mnn = "nearest_nbors m ?cr p l"

    have "set ?cr \<subseteq> set_kdt r \<union> set ms \<and> set ms \<inter> set_kdt l = {}"
      using mnn_set Node.prems(1,4) by auto
    hence IHRL: "\<forall>q \<in> set_kdt l \<union> set ?cr - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using SORTED_R DISTINCT_R Node.IH(1) Node.prems(1,2,6) invar_l invar_distinct by blast

    have "\<forall>n \<in> set ms - set ?cr. sqed (last ?mnn) p \<le> sqed n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cr) p"
        using mnn_le_last_ms SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed n p"
        using IHR * by blast
      thus "sqed (last ?mnn) p \<le> sqed n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt l \<union> set ms - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHRL by auto

    have "\<forall>q \<in> set_kdt r - set ?cr. sqed (last ?mnn) p \<le> sqed q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt r - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "sqed (last ?mnn) p \<le> sqed (last ?cr) p"
        using mnn_le_last_ms SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed q p"
        using IHR * by blast
      thus "sqed (last ?mnn) p \<le> sqed q p" 
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt r - set ?mnn. sqed (last ?mnn) p \<le> sqed q p"
      using IHRL by blast

    show ?thesis 
      using D R L by auto
  qed
qed


subsection "Nearest Neighbors Definition and Theorems"

definition nearest_neighbors :: "nat \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "nearest_neighbors m p kdt = nearest_nbors m [] p kdt"

theorem nearest_neighbors_length:
  "length (nearest_neighbors m p kdt) = min m (size_kdt kdt)"
  using mnn_length nearest_neighbors_def by simp

theorem nearest_neighbors_sorted:
  "sorted_sqed p (nearest_neighbors m p kdt)"
  using mnn_sorted nearest_neighbors_def by simp

theorem nearest_neighbors_set:
  "set (nearest_neighbors m p kdt) \<subseteq> set_kdt kdt"
  using mnn_set nearest_neighbors_def by fastforce

theorem nearest_neighbors_distinct:
  assumes "invar k kdt" "dim p = k"
  shows "distinct (nearest_neighbors m p kdt)"
  using assms mnn_distinct nearest_neighbors_def by simp

theorem nearest_neighbors:
  assumes "invar k kdt" "dim p = k" "nearest_neighbors m p kdt = mns"
  shows "\<forall>q \<in> (set_kdt kdt - set mns). \<forall>n \<in> set mns. sqed n p \<le> sqed q p"
proof (cases "0 < m")
  case True
  hence "\<forall>q \<in> set_kdt kdt - set mns. sqed (last mns) p \<le> sqed q p"
    using assms nearest_neighbors_def mnn_sqed by auto
  hence "\<forall>q \<in> set_kdt kdt - set mns. \<forall>n \<in> set mns. sqed n p \<le> sqed q p"
    using assms(3) nearest_neighbors_sorted[of p m kdt] sorted_sqed_last[of p mns] by force
  thus ?thesis
    using nearest_neighbors_def by blast
next
  case False
  hence "m = 0"
    by simp
  thus ?thesis
    using assms(3) nearest_neighbors_def mnn_length_gt_eq_m by fastforce
qed

end