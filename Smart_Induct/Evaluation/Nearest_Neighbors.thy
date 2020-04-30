(*
  File:     Nearest_Neighbors.thy
  Author:   Martin Rau, TU München
*)

section \<open>Nearest Neighbor Search on the \<open>k\<close>-d Tree\<close>

theory Nearest_Neighbors
imports
  KD_Tree
begin

text \<open>
  Verifying nearest neighbor search on the k-d tree. Given a \<open>k\<close>-d tree and a point \<open>p\<close>,
  which might not be in the tree, find the points \<open>ps\<close> that are closest to \<open>p\<close> using the
  Euclidean metric.
\<close>

subsection \<open>Auxiliary Lemmas about \<open>sorted_wrt\<close>\<close>

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

definition sorted_wrt_dist :: "('k::finite) point \<Rightarrow> 'k point list \<Rightarrow> bool" where
  "sorted_wrt_dist p \<equiv> sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. dist p\<^sub>0 p \<le> dist p\<^sub>1 p)"

lemma sorted_wrt_dist_insort_key:
  "sorted_wrt_dist p ps \<Longrightarrow> sorted_wrt_dist p (insort_key (\<lambda>q. dist q p) q ps)"
  by (induction ps) (auto simp: sorted_wrt_dist_def set_insort_key)

lemma sorted_wrt_dist_take_drop:
  assumes "sorted_wrt_dist p ps"
  shows "\<forall>p\<^sub>0 \<in> set (take n ps). \<forall>p\<^sub>1 \<in> set (drop n ps). dist p\<^sub>0 p \<le> dist p\<^sub>1 p"
  using assms sorted_wrt_append[of _ "take n ps" "drop n ps"] by (simp add: sorted_wrt_dist_def)

lemma sorted_wrt_dist_last_take_mono:
  assumes "sorted_wrt_dist p ps" "n \<le> length ps" "0 < n"
  shows "dist (last (take n ps)) p \<le> dist (last ps) p"
  using assms unfolding sorted_wrt_dist_def by (induction ps arbitrary: n) (auto simp add: take_Cons')

lemma sorted_wrt_dist_last_insort_key_eq:
  assumes "sorted_wrt_dist p ps" "insort_key (\<lambda>q. dist q p) q ps \<noteq> ps @ [q]"
  shows "last (insort_key (\<lambda>q. dist q p) q ps) = last ps"
  using assms unfolding sorted_wrt_dist_def by (induction ps) (auto)

lemma sorted_wrt_dist_last:
  assumes "sorted_wrt_dist p ps"
  shows "\<forall>q \<in> set ps. dist q p \<le> dist (last ps) p"
proof (cases "ps = []")
  case True
  thus ?thesis by simp
next
  case False
  then obtain ps' p' where [simp]:"ps = ps' @ [p']"
    using rev_exhaust by blast
  hence "sorted_wrt_dist p (ps' @ [p'])"
    using assms by blast
  thus ?thesis
    unfolding sorted_wrt_dist_def using sorted_wrt_append[of _ ps' "[p']"] by simp
qed


subsection \<open>Neighbors Sorted wrt. Distance\<close>

definition upd_nbors :: "nat \<Rightarrow> ('k::finite) point \<Rightarrow> 'k point \<Rightarrow> 'k point list \<Rightarrow> 'k point list" where
  "upd_nbors n p q ps = take n (insort_key (\<lambda>q. dist q p) q ps)"

lemma sorted_wrt_dist_nbors:
  assumes "sorted_wrt_dist p ps"
  shows "sorted_wrt_dist p (upd_nbors n p q ps)"
proof -
  have "sorted_wrt_dist p (insort_key (\<lambda>q. dist q p) q ps)"
    using assms sorted_wrt_dist_insort_key by blast
  thus ?thesis
    by (simp add: sorted_wrt_dist_def sorted_wrt_take upd_nbors_def)
qed

lemma sorted_wrt_dist_nbors_diff:
  assumes "sorted_wrt_dist p ps"
  shows "\<forall>r \<in> set ps \<union> {q} - set (upd_nbors n p q ps). \<forall>s \<in> set (upd_nbors n p q ps). dist s p \<le> dist r p"
proof -
  let ?ps' = "insort_key (\<lambda>q. dist q p) q ps"
  have "set ps \<union> { q } = set ?ps'"
    by (simp add: set_insort_key)
  moreover have "set ?ps' = set (take n ?ps') \<union> set (drop n ?ps')"
    using append_take_drop_id set_append by metis
  ultimately have "set ps \<union> { q } - set (take n ?ps') \<subseteq> set (drop n ?ps')"
    by blast
  moreover have "sorted_wrt_dist p ?ps'"
    using assms sorted_wrt_dist_insort_key by blast
  ultimately show ?thesis
    unfolding upd_nbors_def using sorted_wrt_dist_take_drop by blast
qed

lemma sorted_wrt_dist_last_upd_nbors_mono:
  assumes "sorted_wrt_dist p ps" "n \<le> length ps" "0 < n"
  shows "dist (last (upd_nbors n p q ps)) p \<le> dist (last ps) p"
proof (cases "insort_key (\<lambda>q. dist q p) q ps = ps @ [q]")
  case True
  thus ?thesis
    unfolding upd_nbors_def using assms sorted_wrt_dist_last_take_mono by auto
next
  case False
  hence "last (insort_key (\<lambda>q. dist q p) q ps) = last ps"
    using sorted_wrt_dist_last_insort_key_eq assms by blast
  moreover have "dist (last (upd_nbors  n p q ps)) p \<le> dist (last (insort_key (\<lambda>q. dist q p) q ps)) p"
    unfolding upd_nbors_def using assms sorted_wrt_dist_last_take_mono[of p "insort_key (\<lambda>q. dist q p) q ps"]
    by (simp add: sorted_wrt_dist_insort_key)
  ultimately show ?thesis
    by simp
qed


subsection \<open>The Recursive Nearest Neighbor Algorithm\<close>

fun nearest_nbors :: "nat \<Rightarrow> ('k::finite) point list \<Rightarrow> 'k point \<Rightarrow> 'k kdt \<Rightarrow> 'k point list" where
  "nearest_nbors n ps p (Leaf q) = upd_nbors n p q ps"
| "nearest_nbors n ps p (Node k v l r) = (
    if p$k \<le> v then
      let candidates = nearest_nbors n ps p l in
      if length candidates = n \<and> dist p (last candidates) \<le> dist v (p$k) then
        candidates
      else
        nearest_nbors n candidates p r
    else
      let candidates = nearest_nbors n ps p r in
      if length candidates = n \<and> dist p (last candidates) \<le> dist v (p$k) then
        candidates
      else
        nearest_nbors n candidates p l
  )"


subsection \<open>Auxiliary Lemmas\<close>

lemma cutoff_r:
  assumes "invar (Node k v l r)"
  assumes "p$k \<le> v" "dist p c \<le> dist (p$k) v"
  shows "\<forall>q \<in> set_kdt r. dist p c \<le> dist p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt r"
  have "dist p c \<le> dist (p$k) v"
    using assms(3) by blast
  also have "... \<le> dist (p$k) v + dist v (q$k)"
    by simp
  also have "... = dist (p$k) (q$k)"
    using * assms(1,2) dist_real_def by auto
  also have "... \<le> dist p q"
    using dist_vec_nth_le by blast
  finally show "dist p c \<le> dist p q" .
qed

lemma cutoff_l:
  assumes "invar (Node k v l r)"
  assumes "v \<le> p$k" "dist p c \<le> dist v (p$k)"
  shows "\<forall>q \<in> set_kdt l. dist p c \<le> dist p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt l"
  have "dist p c \<le> dist v (p$k)"
    using assms(3) by blast
  also have "... \<le> dist v (p$k) + dist (q$k) v"
    by simp
  also have "... = dist (p$k) (q$k)"
    using * assms(1,2) dist_real_def by auto
  also have "... \<le> dist p q"
    using dist_vec_nth_le by blast
  finally show "dist p c \<le> dist p q" .
qed


subsection \<open>The Main Theorems\<close>

lemma set_nns:
  "set (nearest_nbors n ps p kdt) \<subseteq> set_kdt kdt \<union> set ps"
  apply (induction kdt arbitrary: ps)
  apply (auto simp: Let_def upd_nbors_def set_insort_key)
  using in_set_takeD set_insort_key by fastforce

lemma length_nns:
  "length (nearest_nbors n ps p kdt) = min n (size_kdt kdt + length ps)"
  by (induction kdt arbitrary: ps) (auto simp: Let_def upd_nbors_def)

lemma length_nns_gt_0:
  "0 < n \<Longrightarrow> 0 < length (nearest_nbors n ps p kdt)"
  by (induction kdt arbitrary: ps) (auto simp: Let_def upd_nbors_def)

lemma length_nns_n:
  assumes "(set_kdt kdt \<union> set ps) - set (nearest_nbors n ps p kdt) \<noteq> {}"
  shows "length (nearest_nbors n ps p kdt) = n"
  using assms
proof (induction kdt arbitrary: ps)
  case (Node k v l r)
  let ?nnsl = "nearest_nbors n ps p l"
  let ?nnsr = "nearest_nbors n ps p r"
  consider (A) "p$k \<le> v \<and> length ?nnsl = n \<and> dist p (last ?nnsl) \<le> dist v (p$k)"
         | (B) "p$k \<le> v \<and> \<not>(length ?nnsl = n \<and> dist p (last ?nnsl) \<le> dist v (p$k))"
         | (C) "v < p$k \<and> length ?nnsr = n \<and> dist p (last ?nnsr) \<le> dist v (p$k)"
         | (D) "v < p$k \<and> \<not>(length ?nnsr = n \<and> dist p (last ?nnsr) \<le> dist v (p$k))"
    by argo
  thus ?case
  proof cases
    case B
    let ?nns = "nearest_nbors n ?nnsl p r"
    have "length ?nnsl \<noteq> n \<longrightarrow> (set_kdt l \<union> set ps - set (nearest_nbors n ps p l) = {})"
      using Node.IH(1) by blast
    hence "length ?nnsl \<noteq> n \<longrightarrow> (set_kdt r \<union> set ?nnsl - set ?nns \<noteq> {})"
      using B Node.prems by auto
    moreover have "length ?nnsl = n \<longrightarrow> ?thesis"
      using B by (auto simp: length_nns)
    ultimately show ?thesis
      using B Node.IH(2) by force
  next
    case D
    let ?nns = "nearest_nbors n ?nnsr p l"
    have "length ?nnsr \<noteq> n \<longrightarrow> (set_kdt r \<union> set ps - set (nearest_nbors n ps p r) = {})"
      using Node.IH(2) by blast
    hence "length ?nnsr \<noteq> n \<longrightarrow> (set_kdt l \<union> set ?nnsr - set ?nns \<noteq> {})"
      using D Node.prems by auto
    moreover have "length ?nnsr = n \<longrightarrow> ?thesis"
      using D by (auto simp: length_nns)
    ultimately show ?thesis
      using D Node.IH(1) by force
  qed auto
qed (auto simp: upd_nbors_def min_def set_insort_key)

lemma sorted_nns:
  "sorted_wrt_dist p ps \<Longrightarrow> sorted_wrt_dist p (nearest_nbors n ps p kdt)"
  using sorted_wrt_dist_nbors by (induction kdt arbitrary: ps) (auto simp: Let_def)

lemma distinct_nns:
  assumes "invar kdt" "distinct ps" "set ps \<inter> set_kdt kdt = {}"
  shows "distinct (nearest_nbors n ps p kdt)"
  using assms
proof (induction kdt arbitrary: ps)
  case (Node k v l r)
  let ?nnsl = "nearest_nbors n ps p l"
  let ?nnsr = "nearest_nbors n ps p r"
  have "set ps \<inter> set_kdt l = {}" "set ps \<inter> set_kdt r = {}"
    using Node.prems(3) by auto
  hence DCLR: "distinct ?nnsl" "distinct ?nnsr"
    using Node invar_l invar_r by blast+
  have "set ?nnsl \<inter> set_kdt r = {}" "set ?nnsr \<inter> set_kdt l = {}"
    using Node.prems(1,3) set_nns by fastforce+
  hence "distinct (nearest_nbors n ?nnsl p r)" "distinct (nearest_nbors n ?nnsr p l)"
    using Node.IH(1,2) Node.prems(1,2) DCLR invar_l invar_r by blast+
  thus ?case
    using DCLR by (auto simp add: Let_def)
qed (auto simp: upd_nbors_def distinct_insort)

lemma last_nns_mono:
  assumes "invar kdt" "sorted_wrt_dist p ps" "n \<le> length ps" "0 < n"
  shows "dist (last (nearest_nbors n ps p kdt)) p \<le> dist (last ps) p"
  using assms
proof (induction kdt arbitrary: ps)
  case (Node k v l r)
  let ?nnsl = "nearest_nbors n ps p l"
  let ?nnsr = "nearest_nbors n ps p r"
  have "n \<le> length ?nnsl" "n \<le> length ?nnsr"
    using Node.prems(3) by (simp_all add: length_nns)
  hence "dist (last (nearest_nbors n ?nnsl p r)) p \<le> dist (last ?nnsl) p"
        "dist (last (nearest_nbors n ?nnsr p l)) p \<le> dist (last ?nnsr) p"
    using sorted_nns Node invar_l invar_r by blast+
  hence "dist (last (nearest_nbors n ?nnsl p r)) p \<le> dist (last ps) p"
        "dist (last (nearest_nbors n ?nnsr p l)) p \<le> dist (last ps) p"
    using Node.IH(1)[of ps] Node.IH(2)[of ps] Node.prems invar_l length_nns_gt_0 by auto
  thus ?case
    using Node by (auto simp add: Let_def)
qed (auto simp: sorted_wrt_dist_last_upd_nbors_mono)

theorem dist_nns:
  assumes "invar kdt" "sorted_wrt_dist p ps" "set ps \<inter> set_kdt kdt = {}" "distinct ps" "0 < n"
  shows "\<forall>q \<in> set_kdt kdt \<union> set ps - set (nearest_nbors n ps p kdt). dist (last (nearest_nbors n ps p kdt)) p \<le> dist q p"
  using assms
proof (induction kdt arbitrary: ps)
  case (Node k v l r)

  let ?nnsl = "nearest_nbors n ps p l"
  let ?nnsr = "nearest_nbors n ps p r"

  have IHL: "\<forall>q \<in> set_kdt l \<union> set ps - set ?nnsl. dist (last ?nnsl) p \<le> dist q p"
    using Node.IH(1) Node.prems invar_l invar_set by auto
  have IHR: "\<forall>q \<in> set_kdt r \<union> set ps - set ?nnsr. dist (last ?nnsr) p \<le> dist q p"
    using Node.IH(2) Node.prems invar_r invar_set by auto

  have SORTED_L: "sorted_wrt_dist p ?nnsl"
    using sorted_nns Node.prems(2) by blast
  have SORTED_R: "sorted_wrt_dist p ?nnsr"
    using sorted_nns Node.prems(2) by blast

  have DISTINCT_L: "distinct ?nnsl"
    using Node.prems distinct_nns invar_set invar_l by fastforce
  have DISTINCT_R: "distinct ?nnsr"
    using Node.prems distinct_nns invar_set invar_r
    by (metis inf_bot_right inf_sup_absorb inf_sup_aci(3) sup.commute)

  consider (A) "p$k \<le> v \<and> length ?nnsl = n \<and> dist p (last ?nnsl) \<le> dist v (p$k)"
         | (B) "p$k \<le> v \<and> \<not>(length ?nnsl = n \<and> dist p (last ?nnsl) \<le> dist v (p$k))"
         | (C) "v < p$k \<and> length ?nnsr = n \<and> dist p (last ?nnsr) \<le> dist v (p$k)"
         | (D) "v < p$k \<and> \<not>(length ?nnsr = n \<and> dist p (last ?nnsr) \<le> dist v (p$k))"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. dist (last ?nnsl) p \<le> dist q p"
      using Node.prems(1,2) cutoff_r by (metis dist_commute)
    thus ?thesis
      using IHL A by auto
  next
    case B

    let ?nns = "nearest_nbors n ?nnsl p r"

    have "set ?nnsl \<subseteq> set_kdt l \<union> set ps" "set ps \<inter> set_kdt r = {}"
      using set_nns Node.prems(1,3) by (simp add: set_nns disjoint_iff_not_equal)+
    hence "set ?nnsl \<inter> set_kdt r = {}"
      using Node.prems(1) by fastforce
    hence IHLR: "\<forall>q \<in> set_kdt r \<union> set ?nnsl - set ?nns. dist (last ?nns) p \<le> dist q p"
      using Node.IH(2)[OF _ SORTED_L _ DISTINCT_L Node.prems(5)] Node.prems(1) invar_r by blast

    have "\<forall>q \<in> set ps - set ?nnsl. dist (last ?nns) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set ps - set ?nnsl"

      hence "length ?nnsl = n"
        using length_nns_n by blast
      hence LAST: "dist (last ?nns) p \<le> dist (last ?nnsl) p"
        using last_nns_mono SORTED_L invar_r Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?nnsl) p \<le> dist q p"
        using IHL * by blast
      thus "dist (last ?nns) p \<le> dist q p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt r \<union> set ps - set ?nns. dist (last ?nns) p \<le> dist q p"
      using IHLR by auto

    have "\<forall>q \<in> set_kdt l - set ?nnsl. dist (last ?nns) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt l - set ?nnsl"

      hence "length ?nnsl = n"
        using length_nns_n by blast
      hence LAST: "dist (last ?nns) p \<le> dist (last ?nnsl) p"
        using last_nns_mono SORTED_L invar_r Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?nnsl) p \<le> dist q p"
        using IHL * by blast
      thus "dist (last ?nns) p \<le> dist q p"
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt l - set ?nns. dist (last ?nns) p \<le> dist q p"
      using IHLR by blast

    show ?thesis
      using B R L by auto
  next
    case C
    hence "\<forall>q \<in> set_kdt l. dist (last ?nnsr) p \<le> dist q p"
      using Node.prems(1,2) cutoff_l by (metis dist_commute less_imp_le)
    thus ?thesis
      using IHR C by auto
  next
    case D

    let ?nns = "nearest_nbors n ?nnsr p l"

    have "set ?nnsr \<subseteq> set_kdt r \<union> set ps" "set ps \<inter> set_kdt l = {}"
      using set_nns Node.prems(1,3) by (simp add: set_nns disjoint_iff_not_equal)+
    hence "set ?nnsr \<inter> set_kdt l = {}"
      using Node.prems(1) by fastforce
    hence IHRL: "\<forall>q \<in> set_kdt l \<union> set ?nnsr - set ?nns. dist (last ?nns) p \<le> dist q p"
      using Node.IH(1)[OF _ SORTED_R _ DISTINCT_R Node.prems(5)] Node.prems(1) invar_l by blast

    have "\<forall>q \<in> set ps - set ?nnsr. dist (last ?nns) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set ps - set ?nnsr"

      hence "length ?nnsr = n"
        using length_nns_n by blast
      hence LAST: "dist (last ?nns) p \<le> dist (last ?nnsr) p"
        using last_nns_mono SORTED_R invar_l Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?nnsr) p \<le> dist q p"
        using IHR * by blast
      thus "dist (last ?nns) p \<le> dist q p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt l \<union> set ps - set ?nns. dist (last ?nns) p \<le> dist q p"
      using IHRL by auto

    have "\<forall>q \<in> set_kdt r - set ?nnsr. dist (last ?nns) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt r - set ?nnsr"

      hence "length ?nnsr = n"
        using length_nns_n by blast
      hence LAST: "dist (last ?nns) p \<le> dist (last ?nnsr) p"
        using last_nns_mono SORTED_R invar_l Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?nnsr) p \<le> dist q p"
        using IHR * by blast
      thus "dist (last ?nns) p \<le> dist q p"
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt r - set ?nns. dist (last ?nns) p \<le> dist q p"
      using IHRL by blast

    show ?thesis
      using D R L by auto
  qed
qed (auto simp: sorted_wrt_dist_nbors_diff upd_nbors_def)


subsection \<open>Nearest Neighbors Definition and Theorems\<close>

definition nearest_neighbors :: "nat \<Rightarrow> ('k::finite) point \<Rightarrow> 'k kdt \<Rightarrow> 'k point list" where
  "nearest_neighbors n p kdt = nearest_nbors n [] p kdt"

theorem length_nearest_neighbors:
  "length (nearest_neighbors n p kdt) = min n (size_kdt kdt)"
  by (simp add: length_nns nearest_neighbors_def)

theorem sorted_wrt_dist_nearest_neighbors:
  "sorted_wrt_dist p (nearest_neighbors n p kdt)"
  using sorted_nns unfolding nearest_neighbors_def sorted_wrt_dist_def by force

theorem set_nearest_neighbors:
  "set (nearest_neighbors n p kdt) \<subseteq> set_kdt kdt"
  unfolding nearest_neighbors_def using set_nns by force

theorem distinct_nearest_neighbors:
  assumes "invar kdt"
  shows "distinct (nearest_neighbors n p kdt)"
  using assms by (simp add: distinct_nns nearest_neighbors_def)

theorem dist_nearest_neighbors:
  assumes "invar kdt" "nns = nearest_neighbors n p kdt"
  shows "\<forall>q \<in> (set_kdt kdt - set nns). \<forall>r \<in> set nns. dist r p \<le> dist q p"
proof (cases "0 < n")
  case True
  have "\<forall>q \<in> set_kdt kdt - set nns. dist (last nns) p \<le> dist q p"
    using nearest_neighbors_def dist_nns[OF assms(1), of p "[]", OF _ _ _ True] assms(2)
    by (simp add: nearest_neighbors_def sorted_wrt_dist_def)
  hence "\<forall>q \<in> set_kdt kdt - set nns. \<forall>n \<in> set nns. dist n p \<le> dist q p"
    using assms(2) sorted_wrt_dist_nearest_neighbors[of p n kdt] sorted_wrt_dist_last[of p nns] by force
  thus ?thesis
    using nearest_neighbors_def by blast
next
  case False
  hence "length nns = 0"
    using assms(2) unfolding nearest_neighbors_def by (auto simp: length_nns)
  thus ?thesis
    by simp
qed

end
