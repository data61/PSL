section "Closest Pair Algorithm"

theory Closest_Pair
  imports Common
begin

text\<open>
  Formalization of a slightly optimized divide-and-conquer algorithm solving the Closest Pair Problem
  based on the presentation of Cormen \emph{et al.} \cite{Introduction-to-Algorithms:2009}.
\<close>

subsection "Functional Correctness Proof"

subsubsection "Combine Step"

fun find_closest_tm :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point tm" where
  "find_closest_tm _ _ [] =1 return undefined"
| "find_closest_tm _ _ [p] =1 return p"
| "find_closest_tm p \<delta> (p\<^sub>0 # ps) =1 (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      return p\<^sub>0
    else
      do {
        p\<^sub>1 <- find_closest_tm p (min \<delta> (dist p p\<^sub>0)) ps;
        if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then
          return p\<^sub>0
        else
          return p\<^sub>1
      }
  )"

fun find_closest :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest _ _ [] = undefined"
| "find_closest _ _ [p] = p"
| "find_closest p \<delta> (p\<^sub>0 # ps) = (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      p\<^sub>0
    else
      let p\<^sub>1 = find_closest p (min \<delta> (dist p p\<^sub>0)) ps in
      if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then
        p\<^sub>0
      else
        p\<^sub>1
  )"

lemma find_closest_eq_val_find_closest_tm:
  "val (find_closest_tm p \<delta> ps) = find_closest p \<delta> ps"
  by (induction p \<delta> ps rule: find_closest.induct) (auto simp: Let_def)

lemma find_closest_set:
  "0 < length ps \<Longrightarrow> find_closest p \<delta> ps \<in> set ps"
  by (induction p \<delta> ps rule: find_closest.induct)
     (auto simp: Let_def)

lemma find_closest_dist:
  assumes "sorted_snd (p # ps)" "\<exists>q \<in> set ps. dist p q < \<delta>"
  shows "\<forall>q \<in> set ps. dist p (find_closest p \<delta> ps) \<le> dist p q"
  using assms
proof (induction p \<delta> ps rule: find_closest.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  let ?ps = "p\<^sub>0 # p\<^sub>2 # ps"
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p (min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps)"
  have A: "\<not> \<delta> \<le> snd p\<^sub>0 - snd p"
  proof (rule ccontr)
    assume B: "\<not> \<not> \<delta> \<le> snd p\<^sub>0 - snd p"
    have "\<forall>q \<in> set ?ps. snd p \<le> snd q"
      using sorted_snd_def "3.prems"(1) by simp
    moreover have "\<forall>q \<in> set ?ps. \<delta> \<le> snd q - snd p"
      using sorted_snd_def "3.prems"(1) B by auto
    ultimately have "\<forall>q \<in> set ?ps. \<delta> \<le> dist (snd p) (snd q)"
      using dist_real_def by simp
    hence "\<forall>q \<in> set ?ps. \<delta> \<le> dist p q"
      using dist_snd_le order_trans
      apply (auto split: prod.splits) by fastforce+
    thus False
      using "3.prems"(2) by fastforce
  qed
  show ?case
  proof cases
    assume "\<exists>q \<in> set (p\<^sub>2 # ps). dist p q < min \<delta> (dist p p\<^sub>0)"
    hence "\<forall>q \<in> set (p\<^sub>2 # ps). dist p p\<^sub>1 \<le> dist p q"
      using "3.IH" "3.prems"(1) A p\<^sub>1_def sorted_snd_def by simp
    thus ?thesis
      using p\<^sub>1_def A by (auto split: prod.splits)
  next
    assume B: "\<not> (\<exists>q \<in> set (p\<^sub>2 # ps). dist p q < min \<delta> (dist p p\<^sub>0))"
    hence "dist p p\<^sub>0 < \<delta>"
      using "3.prems"(2) p\<^sub>1_def by auto
    hence C: "\<forall>q \<in> set ?ps. dist p p\<^sub>0 \<le> dist p q"
      using p\<^sub>1_def B by auto
    have "p\<^sub>1 \<in> set (p\<^sub>2 # ps)"
      using p\<^sub>1_def find_closest_set by blast
    hence "dist p p\<^sub>0 \<le> dist p p\<^sub>1"
      using p\<^sub>1_def C by auto
    thus ?thesis
      using p\<^sub>1_def A C by (auto split: prod.splits)
  qed
qed auto

declare find_closest.simps [simp del]

fun find_closest_pair_tm :: "(point * point) \<Rightarrow> point list \<Rightarrow> (point \<times> point) tm" where
  "find_closest_pair_tm (c\<^sub>0, c\<^sub>1) [] =1 return (c\<^sub>0, c\<^sub>1)"
| "find_closest_pair_tm (c\<^sub>0, c\<^sub>1) [_] =1 return (c\<^sub>0, c\<^sub>1)"
| "find_closest_pair_tm (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) =1 (
    do {
      p\<^sub>1 <- find_closest_tm p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps;
      if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
        find_closest_pair_tm (c\<^sub>0, c\<^sub>1) ps
      else
        find_closest_pair_tm (p\<^sub>0, p\<^sub>1) ps
    }
  )"

fun find_closest_pair :: "(point * point) \<Rightarrow> point list \<Rightarrow> (point \<times> point)" where
  "find_closest_pair (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "find_closest_pair (c\<^sub>0, c\<^sub>1) [_] = (c\<^sub>0, c\<^sub>1)"
| "find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      find_closest_pair (c\<^sub>0, c\<^sub>1) ps
    else
      find_closest_pair (p\<^sub>0, p\<^sub>1) ps
  )"

lemma find_closest_pair_eq_val_find_closest_pair_tm:
  "val (find_closest_pair_tm (c\<^sub>0, c\<^sub>1) ps) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"
  by (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: find_closest_pair.induct)
     (auto simp: Let_def find_closest_eq_val_find_closest_tm)

lemma find_closest_pair_set:
  assumes "(C\<^sub>0, C\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"
  shows "(C\<^sub>0 \<in> set ps \<and> C\<^sub>1 \<in> set ps) \<or> (C\<^sub>0 = c\<^sub>0 \<and> C\<^sub>1 = c\<^sub>1)"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 rule: find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) (p\<^sub>2 # ps)"
  hence A: "p\<^sub>1 \<in> set (p\<^sub>2 # ps)"
    using find_closest_set by blast
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "(C\<^sub>0' \<in> set (p\<^sub>2 # ps) \<and> C\<^sub>1' \<in> set (p\<^sub>2 # ps)) \<or> (C\<^sub>0' = c\<^sub>0 \<and> C\<^sub>1' = c\<^sub>1)"
      using "3.hyps"(1) True p\<^sub>1_def by blast
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs True "3.prems" by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      by auto
  next
    case False
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "(C\<^sub>0' \<in> set (p\<^sub>2 # ps) \<and> C\<^sub>1' \<in> set (p\<^sub>2 # ps)) \<or> (C\<^sub>0' = p\<^sub>0 \<and> C\<^sub>1' = p\<^sub>1)"
      using "3.hyps"(2) p\<^sub>1_def False by blast
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs False "3.prems" by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      using A by auto
  qed
qed auto

lemma find_closest_pair_c0_ne_c1:
  "c\<^sub>0 \<noteq> c\<^sub>1 \<Longrightarrow> distinct ps \<Longrightarrow> (C\<^sub>0, C\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps \<Longrightarrow> C\<^sub>0 \<noteq> C\<^sub>1"
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 rule: find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) (p\<^sub>2 # ps)"
  hence A: "p\<^sub>0 \<noteq> p\<^sub>1"
    using "3.prems"(1,2)
    by (metis distinct.simps(2) find_closest_set length_pos_if_in_set list.set_intros(1))
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "C\<^sub>0' \<noteq> C\<^sub>1'"
      using "3.hyps"(1) "3.prems"(1,2) True p\<^sub>1_def by simp
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs True "3.prems"(3) by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "C\<^sub>0' \<noteq> C\<^sub>1'"
      using "3.hyps"(2) "3.prems"(2) A False p\<^sub>1_def by simp
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs False "3.prems"(3) by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      by simp
  qed
qed auto

lemma find_closest_pair_dist_mono:
  assumes "(C\<^sub>0, C\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"
  shows "dist C\<^sub>0 C\<^sub>1 \<le> dist c\<^sub>0 c\<^sub>1"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 rule: find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) (p\<^sub>2 # ps)"
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "dist C\<^sub>0' C\<^sub>1' \<le> dist c\<^sub>0 c\<^sub>1"
      using "3.hyps"(1) True p\<^sub>1_def by simp
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs True "3.prems" by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    note defs = p\<^sub>1_def C'_def
    hence "dist C\<^sub>0' C\<^sub>1' \<le> dist p\<^sub>0 p\<^sub>1"
      using "3.hyps"(2) False p\<^sub>1_def by blast
    moreover have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs False "3.prems"(1) by (auto split: prod.splits, metis Pair_inject)+
    ultimately show ?thesis
      using False by simp
  qed
qed auto

lemma find_closest_pair_dist:
  assumes "sorted_snd ps" "(C\<^sub>0, C\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"
  shows "sparse (dist C\<^sub>0 C\<^sub>1) (set ps)"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 rule: find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) (p\<^sub>2 # ps)"
  show ?case
  proof cases
    assume "\<exists>p \<in> set (p\<^sub>2 # ps). dist p\<^sub>0 p < dist c\<^sub>0 c\<^sub>1"
    hence A: "\<forall>p \<in> set (p\<^sub>2 # ps). dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p" "dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1"
      using p\<^sub>1_def find_closest_dist "3.prems"(1) le_less_trans by blast+
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    hence B: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # p\<^sub>2 # ps)"
      using A(2) p\<^sub>1_def by simp
    have "sparse (dist C\<^sub>0' C\<^sub>1') (set (p\<^sub>2 # ps))"
      using "3.hyps"(2)[of p\<^sub>1 C\<^sub>0' C\<^sub>1'] p\<^sub>1_def C'_def "3.prems"(1) A(2) sorted_snd_def by fastforce
    moreover have "dist C\<^sub>0' C\<^sub>1' \<le> dist p\<^sub>0 p\<^sub>1"
      using C'_def find_closest_pair_dist_mono by blast
    ultimately have "sparse (dist C\<^sub>0' C\<^sub>1') (set (p\<^sub>0 # p\<^sub>2 # ps))"
      using A sparse_identity order_trans by blast
    thus ?thesis
      using B by (metis "3.prems"(2) Pair_inject)
  next
    assume A: "\<not> (\<exists>p \<in> set (p\<^sub>2 # ps). dist p\<^sub>0 p < dist c\<^sub>0 c\<^sub>1)"
    hence B: "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
      using find_closest_set[of "p\<^sub>2 # ps" p\<^sub>0 "dist c\<^sub>0 c\<^sub>1"] p\<^sub>1_def by auto
    obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      using prod.collapse by blast
    hence C: "(C\<^sub>0', C\<^sub>1') = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # p\<^sub>2 # ps)"
      using B p\<^sub>1_def by simp
    have "sparse (dist C\<^sub>0' C\<^sub>1') (set (p\<^sub>2 # ps))"
      using "3.hyps"(1)[of p\<^sub>1 C\<^sub>0' C\<^sub>1'] p\<^sub>1_def C'_def B "3.prems" sorted_snd_def by simp
    moreover have "dist C\<^sub>0' C\<^sub>1' \<le> dist c\<^sub>0 c\<^sub>1"
      using C'_def find_closest_pair_dist_mono by blast
    ultimately have "sparse (dist C\<^sub>0' C\<^sub>1') (set (p\<^sub>0 # p\<^sub>2 # ps))"
      using A sparse_identity[of "dist C\<^sub>0' C\<^sub>1'" "p\<^sub>2 # ps" p\<^sub>0] order_trans by force
    thus ?thesis
      using C by (metis "3.prems"(2) Pair_inject)
  qed
qed (auto simp: sparse_def)

declare find_closest_pair.simps [simp del]

fun combine_tm :: "(point \<times> point) \<Rightarrow> (point \<times> point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (point \<times> point) tm" where
  "combine_tm (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps =1 (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    do {
      ps' <- filter_tm (\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1) ps;
      find_closest_pair_tm (c\<^sub>0, c\<^sub>1) ps'
    }
  )"

fun combine :: "(point \<times> point) \<Rightarrow> (point \<times> point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (point \<times> point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ps' = filter (\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1) ps in
    find_closest_pair (c\<^sub>0, c\<^sub>1) ps'
  )"

lemma combine_eq_val_combine_tm:
  "val (combine_tm (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  by (auto simp: filter_eq_val_filter_tm find_closest_pair_eq_val_find_closest_pair_tm)

lemma combine_set:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "(c\<^sub>0 \<in> set ps \<and> c\<^sub>1 \<in> set ps) \<or> (c\<^sub>0 = p\<^sub>0\<^sub>L \<and> c\<^sub>1 = p\<^sub>1\<^sub>L) \<or> (c\<^sub>0 = p\<^sub>0\<^sub>R \<and> c\<^sub>1 = p\<^sub>1\<^sub>R)"
proof -
  obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    by metis
  define ps' where ps'_def: "ps' = filter (\<lambda>p. dist p (l, snd p) < dist C\<^sub>0' C\<^sub>1') ps"
  obtain C\<^sub>0 C\<^sub>1 where C_def: "(C\<^sub>0, C\<^sub>1) = find_closest_pair (C\<^sub>0', C\<^sub>1') ps'"
    using prod.collapse by blast
  note defs = C'_def ps'_def C_def
  have "(C\<^sub>0 \<in> set ps' \<and> C\<^sub>1 \<in> set ps') \<or> (C\<^sub>0 = C\<^sub>0' \<and> C\<^sub>1 = C\<^sub>1')"
    using C_def find_closest_pair_set by blast+
  hence "(C\<^sub>0 \<in> set ps \<and> C\<^sub>1 \<in> set ps)\<or> (C\<^sub>0 = C\<^sub>0' \<and> C\<^sub>1 = C\<^sub>1')"
    using ps'_def by auto
  moreover have "C\<^sub>0 = c\<^sub>0" "C\<^sub>1 = c\<^sub>1"
    using assms defs apply (auto split: if_splits prod.splits) by (metis Pair_inject)+
  ultimately show ?thesis
    using C'_def by (auto split: if_splits)
qed

lemma combine_c0_ne_c1:
  assumes "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ps"
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
proof -
  obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    by metis
  define ps' where ps'_def: "ps' = filter (\<lambda>p. dist p (l, snd p) < dist C\<^sub>0' C\<^sub>1') ps"
  obtain C\<^sub>0 C\<^sub>1 where C_def: "(C\<^sub>0, C\<^sub>1) = find_closest_pair (C\<^sub>0', C\<^sub>1') ps'"
    using prod.collapse by blast
  note defs = C'_def ps'_def C_def
  have "C\<^sub>0 \<noteq> C\<^sub>1"
    using defs find_closest_pair_c0_ne_c1[of C\<^sub>0' C\<^sub>1' ps'] assms by (auto split: if_splits)
  moreover have "C\<^sub>0 = c\<^sub>0" "C\<^sub>1 = c\<^sub>1"
    using assms(4) defs apply (auto split: if_splits prod.splits) by (metis Pair_inject)+
  ultimately show ?thesis
    by blast
qed

lemma combine_dist:
  assumes "sorted_snd ps" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "sparse (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L" "sparse (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R"
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)"
proof -
  obtain C\<^sub>0' C\<^sub>1' where C'_def: "(C\<^sub>0', C\<^sub>1') = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    by metis
  define ps' where ps'_def: "ps' = filter (\<lambda>p. dist p (l, snd p) < dist C\<^sub>0' C\<^sub>1') ps"
  obtain C\<^sub>0 C\<^sub>1 where C_def: "(C\<^sub>0, C\<^sub>1) = find_closest_pair (C\<^sub>0', C\<^sub>1') ps'"
    using prod.collapse by blast
  note defs = C'_def ps'_def C_def
  have EQ: "C\<^sub>0 = c\<^sub>0" "C\<^sub>1 = c\<^sub>1"
    using defs assms(7) apply (auto split: if_splits prod.splits) by (metis Pair_inject)+
  have ps': "ps' = filter (\<lambda>p. l - dist C\<^sub>0' C\<^sub>1' < fst p \<and> fst p < l + dist C\<^sub>0' C\<^sub>1') ps"
    using ps'_def dist_transform by simp
  have ps\<^sub>L: "sparse (dist C\<^sub>0' C\<^sub>1') ps\<^sub>L"
    using assms(3,5) C'_def sparse_def apply (auto split: if_splits) by force+
  have ps\<^sub>R: "sparse (dist C\<^sub>0' C\<^sub>1') ps\<^sub>R"
    using assms(4,6) C'_def sparse_def apply (auto split: if_splits) by force+
  have "sorted_snd ps'"
    using ps'_def assms(1) sorted_snd_def sorted_wrt_filter by blast
  hence *: "sparse (dist C\<^sub>0 C\<^sub>1) (set ps')"
    using find_closest_pair_dist C_def by simp
  have "\<forall>p\<^sub>0 \<in> set ps. \<forall>p\<^sub>1 \<in> set ps. p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < dist C\<^sub>0' C\<^sub>1' \<longrightarrow> p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
    using set_band_filter ps' ps\<^sub>L ps\<^sub>R assms(2,3,4) by blast
  moreover have "dist C\<^sub>0 C\<^sub>1 \<le> dist C\<^sub>0' C\<^sub>1'"
    using C_def find_closest_pair_dist_mono by blast
  ultimately have "\<forall>p\<^sub>0 \<in> set ps. \<forall>p\<^sub>1 \<in> set ps. p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < dist C\<^sub>0 C\<^sub>1 \<longrightarrow> p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
    by simp
  hence "sparse (dist C\<^sub>0 C\<^sub>1) (set ps)"
    using sparse_def * by (meson not_less)
  thus ?thesis
    using EQ by blast
qed

declare combine.simps [simp del]
declare combine_tm.simps[simp del]

subsubsection "Divide and Conquer Algorithm"

declare split_at_take_drop_conv [simp add]

function closest_pair_rec_tm :: "point list \<Rightarrow> (point list \<times> point \<times> point) tm" where
  "closest_pair_rec_tm xs =1 (
    do {
      n <- length_tm xs;
      if n \<le> 3 then
        do {
          ys <- mergesort_tm snd xs;
          p <- closest_pair_bf_tm xs;
          return (ys, p)
        }
      else
        do {
          (xs\<^sub>L, xs\<^sub>R) <- split_at_tm (n div 2) xs;
          (ys\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) <- closest_pair_rec_tm xs\<^sub>L;
          (ys\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) <- closest_pair_rec_tm xs\<^sub>R;
          ys <- merge_tm snd ys\<^sub>L ys\<^sub>R;
          (p\<^sub>0, p\<^sub>1) <- combine_tm (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys;
          return (ys, p\<^sub>0, p\<^sub>1)
       }
    }
  )"
  by pat_completeness auto
termination closest_pair_rec_tm
  by (relation "Wellfounded.measure (\<lambda>xs. length xs)")
     (auto simp add: length_eq_val_length_tm split_at_eq_val_split_at_tm)

function closest_pair_rec :: "point list \<Rightarrow> (point list * point * point)" where
  "closest_pair_rec xs = (
    let n = length xs in
    if n \<le> 3 then
      (mergesort snd xs, closest_pair_bf xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let (ys\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys)
  )"
  by pat_completeness auto
termination closest_pair_rec
  by (relation "Wellfounded.measure (\<lambda>xs. length xs)")
     (auto simp: Let_def)

declare split_at_take_drop_conv [simp del]

lemma closest_pair_rec_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest_pair_rec xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let (ys\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let ys = merge snd ys\<^sub>L ys\<^sub>R in
    (ys, combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys)
  )"
  using assms by (auto simp: Let_def)

declare closest_pair_rec.simps [simp del]

lemma closest_pair_rec_eq_val_closest_pair_rec_tm:
  "val (closest_pair_rec_tm xs) = closest_pair_rec xs"
proof (induction rule: length_induct)
  case (1 xs)
  define n where "n = length xs"
  obtain xs\<^sub>L xs\<^sub>R where xs_def: "(xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs"
    by (metis surj_pair)
  note defs = n_def xs_def
  show ?case
  proof cases
    assume "n \<le> 3"
    then show ?thesis
      using defs
      by (auto simp: length_eq_val_length_tm mergesort_eq_val_mergesort_tm
                     closest_pair_bf_eq_val_closest_pair_bf_tm closest_pair_rec.simps)
  next
    assume asm: "\<not> n \<le> 3"
    have "length xs\<^sub>L < length xs" "length xs\<^sub>R < length xs"
      using asm defs by (auto simp: split_at_take_drop_conv)
    hence "val (closest_pair_rec_tm xs\<^sub>L) = closest_pair_rec xs\<^sub>L"
          "val (closest_pair_rec_tm xs\<^sub>R) = closest_pair_rec xs\<^sub>R"
      using "1.IH" by blast+
    thus ?thesis
      using asm defs
      apply (subst closest_pair_rec.simps, subst closest_pair_rec_tm.simps)
      by (auto simp del: closest_pair_rec_tm.simps
               simp add: Let_def length_eq_val_length_tm merge_eq_val_merge_tm
                         split_at_eq_val_split_at_tm combine_eq_val_combine_tm
               split: prod.split)
  qed
qed

lemma closest_pair_rec_set_length_sorted_snd:
  assumes "(ys, p) = closest_pair_rec xs"
  shows "set ys = set xs \<and> length ys = length xs \<and> sorted_snd ys"
  using assms
proof (induction xs arbitrary: ys p rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    thus ?thesis using "1.prems" sorted_snd_def
      by (auto simp: mergesort closest_pair_rec.simps)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"
    obtain YS\<^sub>L P\<^sub>L where YSP\<^sub>L_def: "(YS\<^sub>L, P\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by blast
    obtain YS\<^sub>R P\<^sub>R where YSP\<^sub>R_def: "(YS\<^sub>R, P\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by blast
    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define P where "P = combine P\<^sub>L P\<^sub>R L YS"
    note defs = XS\<^sub>L\<^sub>R_def L_def YSP\<^sub>L_def YSP\<^sub>R_def YS_def P_def

    have "length XS\<^sub>L < length xs" "length XS\<^sub>R < length xs"
      using False defs by (auto simp: split_at_take_drop_conv)
    hence IH: "set XS\<^sub>L = set YS\<^sub>L" "set XS\<^sub>R = set YS\<^sub>R"
              "length XS\<^sub>L = length YS\<^sub>L" "length XS\<^sub>R = length YS\<^sub>R"
              "sorted_snd YS\<^sub>L" "sorted_snd YS\<^sub>R"
      using "1.IH" defs by metis+

    have "set xs = set XS\<^sub>L \<union> set XS\<^sub>R"
      using defs by (auto simp: set_take_drop split_at_take_drop_conv)
    hence SET: "set xs = set YS"
      using set_merge IH(1,2) defs by fast

    have "length xs = length XS\<^sub>L + length XS\<^sub>R"
      using defs by (auto simp: split_at_take_drop_conv)
    hence LENGTH: "length xs = length YS"
      using IH(3,4) length_merge defs by metis

    have SORTED: "sorted_snd YS"
      using IH(5,6) by (simp add: defs sorted_snd_def sorted_merge)

    have "(YS, P) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    hence "(ys, p) = (YS, P)"
      using "1.prems" by argo
    thus ?thesis
      using SET LENGTH SORTED by simp
  qed
qed

lemma closest_pair_rec_distinct:
  assumes "distinct xs" "(ys, p) = closest_pair_rec xs"
  shows "distinct ys"
  using assms
proof (induction xs arbitrary: ys p rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    thus ?thesis using "1.prems"
      by (auto simp: mergesort closest_pair_rec.simps)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"
    obtain YS\<^sub>L P\<^sub>L where YSP\<^sub>L_def: "(YS\<^sub>L, P\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by blast
    obtain YS\<^sub>R P\<^sub>R where YSP\<^sub>R_def: "(YS\<^sub>R, P\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by blast
    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define P where "P = combine P\<^sub>L P\<^sub>R L YS"
    note defs = XS\<^sub>L\<^sub>R_def L_def YSP\<^sub>L_def YSP\<^sub>R_def YS_def P_def

    have "length XS\<^sub>L < length xs" "length XS\<^sub>R < length xs"
      using False defs by (auto simp: split_at_take_drop_conv)
    moreover have "distinct XS\<^sub>L" "distinct XS\<^sub>R"
      using "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    ultimately have IH: "distinct YS\<^sub>L" "distinct YS\<^sub>R"
      using "1.IH" defs by blast+

    have "set XS\<^sub>L \<inter> set XS\<^sub>R = {}"
      using "1.prems"(1) defs by (auto simp: split_at_take_drop_conv set_take_disj_set_drop_if_distinct)
    moreover have "set XS\<^sub>L = set YS\<^sub>L" "set XS\<^sub>R = set YS\<^sub>R"
      using closest_pair_rec_set_length_sorted_snd defs by blast+
    ultimately have "set YS\<^sub>L \<inter> set YS\<^sub>R = {}"
      by blast
    hence DISTINCT: "distinct YS"
      using distinct_merge IH defs by blast

    have "(YS, P) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    hence "(ys, p) = (YS, P)"
      using "1.prems" by argo
    thus ?thesis
      using DISTINCT by blast
  qed
qed

lemma closest_pair_rec_c0_c1:
  assumes "1 < length xs" "distinct xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "c\<^sub>0 \<in> set xs \<and> c\<^sub>1 \<in> set xs \<and> c\<^sub>0 \<noteq> c\<^sub>1"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(3) closest_pair_rec.simps by simp
    thus ?thesis
      using "1.prems"(1,2) closest_pair_bf_c0_c1 by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs" "distinct XS\<^sub>L"
      using False "1.prems"(2) defs by (auto simp: split_at_take_drop_conv)
    hence "C\<^sub>0\<^sub>L \<in> set XS\<^sub>L" "C\<^sub>1\<^sub>L \<in> set XS\<^sub>L" and IHL1: "C\<^sub>0\<^sub>L \<noteq> C\<^sub>1\<^sub>L"
      using "1.IH" defs by metis+
    hence IHL2: "C\<^sub>0\<^sub>L \<in> set xs" "C\<^sub>1\<^sub>L \<in> set xs"
      using split_at_take_drop_conv in_set_takeD fst_conv defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs" "distinct XS\<^sub>R"
      using False "1.prems"(2) defs by (auto simp: split_at_take_drop_conv)
    hence "C\<^sub>0\<^sub>R \<in> set XS\<^sub>R" "C\<^sub>1\<^sub>R \<in> set XS\<^sub>R" and IHR1: "C\<^sub>0\<^sub>R \<noteq> C\<^sub>1\<^sub>R"
      using "1.IH" defs by metis+
    hence IHR2: "C\<^sub>0\<^sub>R \<in> set xs" "C\<^sub>1\<^sub>R \<in> set xs"
      using split_at_take_drop_conv in_set_dropD snd_conv defs by metis+

    have *: "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    have YS: "set xs = set YS" "distinct YS"
      using "1.prems"(2) closest_pair_rec_set_length_sorted_snd closest_pair_rec_distinct * by blast+

    have "C\<^sub>0 \<in> set xs" "C\<^sub>1 \<in> set xs"
      using combine_set IHL2 IHR2 YS defs by blast+
    moreover have "C\<^sub>0 \<noteq> C\<^sub>1"
      using combine_c0_ne_c1 IHL1(1) IHR1(1) YS defs by blast
    ultimately show ?thesis
      using "1.prems"(3) * by (metis Pair_inject)
  qed
qed

lemma closest_pair_rec_dist:
  assumes "1 < length xs" "sorted_fst xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set xs)"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(3) closest_pair_rec.simps by simp
    thus ?thesis
      using "1.prems"(1,3) closest_pair_bf_dist by metis
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have XSLR: "XS\<^sub>L = take (?n div 2) xs" "XS\<^sub>R = drop (?n div 2) xs"
      using defs by (auto simp: split_at_take_drop_conv)

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False XSLR by simp_all
    moreover have "sorted_fst XS\<^sub>L"
      using "1.prems"(2) XSLR by (auto simp: sorted_fst_def sorted_wrt_take)
    ultimately have L: "sparse (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set XS\<^sub>L)"
                       "set XS\<^sub>L = set YS\<^sub>L"
      using 1 closest_pair_rec_set_length_sorted_snd closest_pair_rec_c0_c1
              YSC\<^sub>0\<^sub>1\<^sub>L_def by blast+
    hence IHL: "sparse (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set YS\<^sub>L)"
      by argo

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False XSLR by simp_all
    moreover have "sorted_fst XS\<^sub>R"
      using "1.prems"(2) XSLR by (auto simp: sorted_fst_def sorted_wrt_drop)
    ultimately have R: "sparse (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set XS\<^sub>R)"
                       "set XS\<^sub>R = set YS\<^sub>R"
      using 1 closest_pair_rec_set_length_sorted_snd closest_pair_rec_c0_c1
              YSC\<^sub>0\<^sub>1\<^sub>R_def by blast+
    hence IHR: "sparse (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set YS\<^sub>R)"
      by argo

    have *: "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)

    have "set xs = set YS" "sorted_snd YS"
      using "1.prems"(2) closest_pair_rec_set_length_sorted_snd closest_pair_rec_distinct * by blast+
    moreover have "\<forall>p \<in> set YS\<^sub>L. fst p \<le> L"
      using False "1.prems"(2) XSLR L_def L(2) sorted_fst_take_less_hd_drop by simp
    moreover have "\<forall>p \<in> set YS\<^sub>R. L \<le> fst p"
      using False "1.prems"(2) XSLR L_def R(2) sorted_fst_hd_drop_less_drop by simp
    moreover have "set YS = set YS\<^sub>L \<union> set YS\<^sub>R"
      using set_merge defs by fast
    moreover have "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      by (auto simp add: defs)
    ultimately have "sparse (dist C\<^sub>0 C\<^sub>1) (set xs)"
      using combine_dist IHL IHR by auto
    moreover have "(YS, C\<^sub>0, C\<^sub>1) = (ys, c\<^sub>0, c\<^sub>1)"
      using "1.prems"(3) * by simp
    ultimately show ?thesis
      by blast
  qed
qed

fun closest_pair_tm :: "point list \<Rightarrow> (point * point) tm" where
  "closest_pair_tm [] =1 return undefined"
| "closest_pair_tm [_] =1 return undefined"
| "closest_pair_tm ps =1 (
    do {
      xs <- mergesort_tm fst ps;
      (_, p) <- closest_pair_rec_tm xs;
      return p
    }
  )"

fun closest_pair :: "point list \<Rightarrow> (point * point)" where
  "closest_pair [] = undefined"
| "closest_pair [_] = undefined"
| "closest_pair ps = (let (_, p) = closest_pair_rec (mergesort fst ps) in p)"

lemma closest_pair_eq_val_closest_pair_tm:
  "val (closest_pair_tm ps) = closest_pair ps"
  by (induction ps rule: induct_list012)
     (auto simp del: closest_pair_rec_tm.simps mergesort_tm.simps
           simp add: closest_pair_rec_eq_val_closest_pair_rec_tm mergesort_eq_val_mergesort_tm
           split: prod.split)

lemma closest_pair_simps:
  "1 < length ps \<Longrightarrow> closest_pair ps = (let (_, p) = closest_pair_rec (mergesort fst ps) in p)"
  by (induction ps rule: induct_list012) auto

declare closest_pair.simps [simp del]

theorem closest_pair_c0_c1:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "c\<^sub>0 \<in> set ps" "c\<^sub>1 \<in> set ps" "c\<^sub>0 \<noteq> c\<^sub>1"
  using assms closest_pair_rec_c0_c1[of "mergesort fst ps"]
  by (auto simp: closest_pair_simps mergesort split: prod.splits)

theorem closest_pair_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms sorted_fst_def closest_pair_rec_dist[of "mergesort fst ps"] closest_pair_rec_c0_c1[of "mergesort fst ps"]
  by (auto simp: closest_pair_simps mergesort split: prod.splits)


subsection "Time Complexity Proof"

subsubsection "Core Argument"

lemma core_argument:
  fixes \<delta> :: real and p :: point and ps :: "point list"
  assumes "distinct (p # ps)" "sorted_snd (p # ps)" "0 \<le> \<delta>" "set (p # ps) = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>q \<in> set (p # ps). l - \<delta> < fst q \<and> fst q < l + \<delta>"
  assumes "\<forall>q \<in> ps\<^sub>L. fst q \<le> l" "\<forall>q \<in> ps\<^sub>R. l \<le> fst q"
  assumes "sparse \<delta> ps\<^sub>L" "sparse \<delta> ps\<^sub>R"
  shows "length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps) \<le> 7"
proof -
  define PS where "PS = p # ps"
  define R where "R = cbox (l - \<delta>, snd p) (l + \<delta>, snd p + \<delta>)"
  define RPS where "RPS = { p \<in> set PS. p \<in> R }"
  define LSQ where "LSQ = cbox (l - \<delta>, snd p) (l, snd p + \<delta>)"
  define LSQPS where "LSQPS = { p \<in> ps\<^sub>L. p \<in> LSQ }"
  define RSQ where "RSQ = cbox (l, snd p) (l + \<delta>, snd p + \<delta>)"
  define RSQPS where "RSQPS = { p \<in> ps\<^sub>R. p \<in> RSQ }"
  note defs = PS_def R_def RPS_def LSQ_def LSQPS_def RSQ_def RSQPS_def

  have "R = LSQ \<union> RSQ"
    using defs cbox_right_un by auto
  moreover have "\<forall>p \<in> ps\<^sub>L. p \<in> RSQ \<longrightarrow> p \<in> LSQ"
    using RSQ_def LSQ_def assms(6) by auto
  moreover have "\<forall>p \<in> ps\<^sub>R. p \<in> LSQ \<longrightarrow> p \<in> RSQ"
    using RSQ_def LSQ_def assms(7) by auto
  ultimately have "RPS = LSQPS \<union> RSQPS"
    using LSQPS_def RSQPS_def PS_def RPS_def assms(4) by blast

  have "sparse \<delta> LSQPS"
    using assms(8) LSQPS_def sparse_def by simp
  hence CLSQPS: "card LSQPS \<le> 4"
    using max_points_square[of LSQPS "l - \<delta>" "snd p" \<delta>] assms(3) LSQ_def LSQPS_def by auto

  have "sparse \<delta> RSQPS"
    using assms(9) RSQPS_def sparse_def by simp
  hence CRSQPS: "card RSQPS \<le> 4"
    using max_points_square[of RSQPS l "snd p" \<delta>] assms(3) RSQ_def RSQPS_def by auto

  have CRPS: "card RPS \<le> 8"
    using CLSQPS CRSQPS card_Un_le[of LSQPS RSQPS] \<open>RPS = LSQPS \<union> RSQPS\<close> by auto

  have "set (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps) \<subseteq> RPS"
  proof standard
    fix q
    assume *: "q \<in> set (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)"
    hence CPS: "q \<in> set PS"
      using PS_def by auto
    hence "snd p \<le> snd q" "snd q \<le> snd p + \<delta>"
      using assms(2,3) PS_def sorted_snd_def * by (auto split: if_splits)
    moreover have "l - \<delta> < fst q" "fst q < l + \<delta>"
      using CPS assms(5) PS_def by blast+
    ultimately have "q \<in> R"
      using R_def mem_cbox_2D[of "l - \<delta>" "fst q" "l + \<delta>" "snd p" "snd q" "snd p + \<delta>"]
      by (simp add: prod.case_eq_if)
    thus "q \<in> RPS"
      using CPS RPS_def by simp
  qed
  moreover have "finite RPS"
    by (simp add: RPS_def)
  ultimately have "card (set (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)) \<le> 8"
    using CRPS card_mono[of RPS "set (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)"] by simp
  moreover have "distinct (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)"
    using assms(1) by simp
  ultimately have "length (p # filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps) \<le> 8"
    using assms(1) PS_def distinct_card by metis
  thus ?thesis
    by simp
qed

subsubsection "Combine Step"

fun t_find_closest :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest _ _ [] = 1"
| "t_find_closest _ _ [_] = 1"
| "t_find_closest p \<delta> (p\<^sub>0 # ps) = 1 + (
    if \<delta> \<le> snd p\<^sub>0 - snd p then 0
    else t_find_closest p (min \<delta> (dist p p\<^sub>0)) ps
  )"

lemma t_find_closest_eq_time_find_closest_tm:
  "t_find_closest p \<delta> ps = time (find_closest_tm p \<delta> ps)"
  by (induction p \<delta> ps rule: t_find_closest.induct)
     (auto simp: time_simps)

lemma t_find_closest_mono:
  "\<delta>' \<le> \<delta> \<Longrightarrow> t_find_closest p \<delta>' ps \<le> t_find_closest p \<delta> ps"
  by (induction rule: t_find_closest.induct)
     (auto simp: Let_def min_def)

lemma t_find_closest_cnt:
  "t_find_closest p \<delta> ps \<le> 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)"
proof (induction p \<delta> ps rule: t_find_closest.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  show ?case
  proof (cases "\<delta> \<le> snd p\<^sub>0 - snd p")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence *: "snd p\<^sub>0 - snd p \<le> \<delta>"
      by simp
    have "t_find_closest p \<delta> (p\<^sub>0 # p\<^sub>2 # ps) = 1 + t_find_closest p (min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps)"
      using False by simp
    also have "... \<le> 1 + 1 + length (filter (\<lambda>q. snd q - snd p \<le> min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps))"
      using False 3 by simp
    also have "... \<le> 1 + 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) (p\<^sub>2 # ps))"
      using * by (meson add_le_cancel_left length_filter_P_impl_Q min.bounded_iff)
    also have "... \<le> 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) (p\<^sub>0 # p\<^sub>2 # ps))"
      using False by simp
    ultimately show ?thesis
      by simp
  qed
qed auto

corollary t_find_closest_bound:
  fixes \<delta> :: real and p :: point and ps :: "point list" and l :: int
  assumes "distinct (p # ps)" "sorted_snd (p # ps)" "0 \<le> \<delta>" "set (p # ps) = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p' \<in> set (p # ps). l - \<delta> < fst p' \<and> fst p' < l + \<delta>"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "sparse \<delta> ps\<^sub>L" "sparse \<delta> ps\<^sub>R"
  shows "t_find_closest p \<delta> ps \<le> 8"
  using assms core_argument[of p ps \<delta> ps\<^sub>L ps\<^sub>R l] t_find_closest_cnt[of p \<delta> ps] by linarith

fun t_find_closest_pair :: "(point * point) \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest_pair _ [] = 1"
| "t_find_closest_pair _ [_] = 1"
| "t_find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = 1 + (
    let p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps in
    t_find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps + (
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps
    else
      t_find_closest_pair (p\<^sub>0, p\<^sub>1) ps
  ))"

lemma t_find_closest_pair_eq_time_find_closest_pair_tm:
  "t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps = time (find_closest_pair_tm (c\<^sub>0, c\<^sub>1) ps)"
  by (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: t_find_closest_pair.induct)
     (auto simp: time_simps find_closest_eq_val_find_closest_tm t_find_closest_eq_time_find_closest_tm)

lemma t_find_closest_pair_bound:
  assumes "distinct ps" "sorted_snd ps" "\<delta> = dist c\<^sub>0 c\<^sub>1" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> set ps. l - \<Delta> < fst p \<and> fst p < l + \<Delta>"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "sparse \<Delta> ps\<^sub>L" "sparse \<Delta> ps\<^sub>R" "\<delta> \<le> \<Delta>"
  shows "t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps \<le> 9 * length ps + 1"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 ps\<^sub>L ps\<^sub>R rule: t_find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  let ?ps = "p\<^sub>2 # ps"
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps"
  define PS\<^sub>L where PS\<^sub>L_def: "PS\<^sub>L = ps\<^sub>L - { p\<^sub>0 }"
  define PS\<^sub>R where PS\<^sub>R_def: "PS\<^sub>R = ps\<^sub>R - { p\<^sub>0 }"
  note defs = p\<^sub>1_def PS\<^sub>L_def PS\<^sub>R_def
  have *: "0 \<le> \<Delta>"
    using "3.prems"(3,10) zero_le_dist[of c\<^sub>0 c\<^sub>1] by argo
  hence "t_find_closest p\<^sub>0 \<Delta> ?ps \<le> 8"
    using t_find_closest_bound[of p\<^sub>0 ?ps \<Delta> ps\<^sub>L ps\<^sub>R] "3.prems" by blast
  hence A: "t_find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps \<le> 8"
    by (metis "3.prems"(3,10) order_trans t_find_closest_mono)
  have B: "distinct ?ps" "sorted_snd ?ps"
    using "3.prems"(1,2) sorted_snd_def by simp_all
  have C: "set ?ps = PS\<^sub>L \<union> PS\<^sub>R"
    using defs "3.prems"(1,4) by auto
  have D: "\<forall>p \<in> set ?ps. l - \<Delta> < fst p \<and> fst p < l + \<Delta>"
    using "3.prems"(5) by simp
  have E: "\<forall>p \<in> PS\<^sub>L. fst p \<le> l" "\<forall>p \<in> PS\<^sub>R. l \<le> fst p"
    using defs "3.prems"(6,7) by simp_all
  have F: "sparse \<Delta> PS\<^sub>L" "sparse \<Delta> PS\<^sub>R"
    using defs "3.prems"(8,9) sparse_def by simp_all
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence "t_find_closest_pair (c\<^sub>0, c\<^sub>1) ?ps \<le> 9 * length ?ps + 1"
      using "3.hyps"(1) "3.prems"(3,10) defs(1) B C D E F by blast
    moreover have "t_find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ?ps) =
                   1 + t_find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps + t_find_closest_pair (c\<^sub>0, c\<^sub>1) ?ps"
      using defs True by (auto split: prod.splits)
    ultimately show ?thesis
      using A by auto
  next
    case False
    moreover have "0 \<le> dist p\<^sub>0 p\<^sub>1"
      by auto
    ultimately have "t_find_closest_pair (p\<^sub>0, p\<^sub>1) ?ps \<le> 9 * length ?ps + 1"
      using "3.hyps"(2) "3.prems"(3,10) defs(1) B C D E F by auto
    moreover have "t_find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ?ps) =
                   1 + t_find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps + t_find_closest_pair (p\<^sub>0, p\<^sub>1) ?ps"
      using defs False by (auto split: prod.splits)
    ultimately show ?thesis
      using A by simp
  qed
qed auto

fun t_combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> nat" where
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = 1 + (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ps' = filter (\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1) ps in
    time (filter_tm (\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1) ps) + t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps'
  )"

lemma t_combine_eq_time_combine_tm:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = time (combine_tm (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps)"
  by (auto simp: combine_tm.simps time_simps t_find_closest_pair_eq_time_find_closest_pair_tm filter_eq_val_filter_tm)

lemma t_combine_bound:
  fixes ps :: "point list"
  assumes "distinct ps" "sorted_snd ps" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "sparse (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L" "sparse (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R"
  shows "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps \<le> 10 * length ps + 3"
proof -
  obtain c\<^sub>0 c\<^sub>1 where c_def:
    "(c\<^sub>0, c\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))" by metis
  let ?P = "(\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1)"
  define ps' where ps'_def: "ps' = filter ?P ps"
  define ps\<^sub>L' where ps\<^sub>L'_def: "ps\<^sub>L' = { p \<in> ps\<^sub>L. ?P p }"
  define ps\<^sub>R' where ps\<^sub>R'_def: "ps\<^sub>R' = { p \<in> ps\<^sub>R. ?P p }"
  note defs = c_def ps'_def ps\<^sub>L'_def ps\<^sub>R'_def
  have "sparse (dist c\<^sub>0 c\<^sub>1) ps\<^sub>L" "sparse (dist c\<^sub>0 c\<^sub>1) ps\<^sub>R"
    using assms(6,7) sparse_mono c_def by (auto split: if_splits)
  hence "sparse (dist c\<^sub>0 c\<^sub>1) ps\<^sub>L'" "sparse (dist c\<^sub>0 c\<^sub>1) ps\<^sub>R'"
    using ps\<^sub>L'_def ps\<^sub>R'_def sparse_def by auto
  moreover have "distinct ps'"
    using ps'_def assms(1) by simp
  moreover have "sorted_snd ps'"
    using ps'_def assms(2) sorted_snd_def sorted_wrt_filter by blast
  moreover have "0 \<le> dist c\<^sub>0 c\<^sub>1"
    by simp
  moreover have "set ps' = ps\<^sub>L' \<union> ps\<^sub>R'"
    using assms(3) defs(2,3,4) filter_Un by auto
  moreover have "\<forall>p \<in> set ps'. l - dist c\<^sub>0 c\<^sub>1 < fst p \<and> fst p < l + dist c\<^sub>0 c\<^sub>1"
    using ps'_def dist_transform by force
  moreover have "\<forall>p \<in> ps\<^sub>L'. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R'. l \<le> fst p"
    using assms(4,5) ps\<^sub>L'_def ps\<^sub>R'_def by blast+
  ultimately have "t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps' \<le> 9 * length ps' + 1"
    using t_find_closest_pair_bound by blast
  moreover have "length ps' \<le> length ps"
    using ps'_def by simp
  ultimately have *: "t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps' \<le> 9 * length ps + 1"
    by simp
  have "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps =
        1 + time (filter_tm ?P ps) + t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps'"
    using defs by (auto split: prod.splits)
  also have "... = 2 + length ps + t_find_closest_pair (c\<^sub>0, c\<^sub>1) ps'"
    using time_filter_tm by auto
  finally show ?thesis
    using * by simp
qed

declare t_combine.simps [simp del]

subsubsection "Divide and Conquer Algorithm"

lemma time_closest_pair_rec_tm_simps_1:
  assumes "length xs \<le> 3"
  shows "time (closest_pair_rec_tm xs) = 1 + time (length_tm xs) + time (mergesort_tm snd xs) + time (closest_pair_bf_tm xs)"
  using assms by  (auto simp: time_simps length_eq_val_length_tm)

lemma time_closest_pair_rec_tm_simps_2:
  assumes "\<not> (length xs \<le> 3)"
  shows "time (closest_pair_rec_tm xs) = 1 + (
    let (xs\<^sub>L, xs\<^sub>R) = val (split_at_tm (length xs div 2) xs) in
    let (ys\<^sub>L, p\<^sub>L) = val (closest_pair_rec_tm xs\<^sub>L) in
    let (ys\<^sub>R, p\<^sub>R) = val (closest_pair_rec_tm xs\<^sub>R) in
    let ys = val (merge_tm (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R) in
    time (length_tm xs) + time (split_at_tm (length xs div 2) xs) + time (closest_pair_rec_tm xs\<^sub>L) +
    time (closest_pair_rec_tm xs\<^sub>R) + time (merge_tm (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R) + t_combine p\<^sub>L p\<^sub>R (fst (hd xs\<^sub>R)) ys
  )"
  using assms
  apply (subst closest_pair_rec_tm.simps)
  by (auto simp del: closest_pair_rec_tm.simps
           simp add: time_simps length_eq_val_length_tm t_combine_eq_time_combine_tm
              split: prod.split)

function closest_pair_recurrence :: "nat \<Rightarrow> real" where
  "n \<le> 3 \<Longrightarrow> closest_pair_recurrence n = 3 + n + mergesort_recurrence n + n * n"
| "3 < n \<Longrightarrow> closest_pair_recurrence n = 7 + 13 * n +
    closest_pair_recurrence (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_recurrence (nat \<lceil>real n / 2\<rceil>)"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma closest_pair_recurrence_nonneg[simp]:
  "0 \<le> closest_pair_recurrence n"
  by (induction n rule: closest_pair_recurrence.induct) auto

lemma time_closest_pair_rec_conv_closest_pair_recurrence:
  assumes "distinct ps" "sorted_fst ps"
  shows "time (closest_pair_rec_tm ps) \<le> closest_pair_recurrence (length ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  let ?n = "length ps"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "time (closest_pair_rec_tm ps) = 1 + time (length_tm ps) + time (mergesort_tm snd ps) + time (closest_pair_bf_tm ps)"
      using time_closest_pair_rec_tm_simps_1 by simp
    moreover have "closest_pair_recurrence ?n = 3 + ?n + mergesort_recurrence ?n + ?n * ?n"
      using True by simp
    moreover have "time (length_tm ps) \<le> 1 + ?n" "time (mergesort_tm snd ps) \<le> mergesort_recurrence ?n"
                  "time (closest_pair_bf_tm ps) \<le> 1 + ?n * ?n"
      using time_length_tm[of ps] time_mergesort_conv_mergesort_recurrence[of snd ps] time_closest_pair_bf_tm[of ps] by auto
    ultimately show ?thesis
      by linarith
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS_def: "(XS\<^sub>L, XS\<^sub>R) = val (split_at_tm (?n div 2) ps)"
      using prod.collapse by blast
    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where CP\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = val (closest_pair_rec_tm XS\<^sub>L)"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where CP\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = val (closest_pair_rec_tm XS\<^sub>R)"
      using prod.collapse by metis
    define YS where "YS = val (merge_tm (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R)"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = val (combine_tm (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) (fst (hd XS\<^sub>R)) YS)"
      using prod.collapse by metis
    note defs = XS_def CP\<^sub>L_def CP\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have XSLR: "XS\<^sub>L = take (?n div 2) ps" "XS\<^sub>R = drop (?n div 2) ps"
      using defs by (auto simp: split_at_take_drop_conv split_at_eq_val_split_at_tm)
    hence "length XS\<^sub>L = ?n div 2" "length XS\<^sub>R = ?n - ?n div 2"
      by simp_all
    hence *: "(nat \<lfloor>real ?n / 2\<rfloor>) = length XS\<^sub>L" "(nat \<lceil>real ?n / 2\<rceil>) = length XS\<^sub>R"
      by linarith+
    have "length XS\<^sub>L = length YS\<^sub>L" "length XS\<^sub>R = length YS\<^sub>R"
      using defs closest_pair_rec_set_length_sorted_snd closest_pair_rec_eq_val_closest_pair_rec_tm by metis+
    hence L: "?n = length YS\<^sub>L + length YS\<^sub>R"
      using defs XSLR by fastforce

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length ps"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>L" "sorted_fst XS\<^sub>L"
      using XSLR "1.prems"(1,2) sorted_fst_def sorted_wrt_take by simp_all
    ultimately have "time (closest_pair_rec_tm XS\<^sub>L) \<le> closest_pair_recurrence (length XS\<^sub>L)"
      using "1.IH" by simp
    hence IHL: "time (closest_pair_rec_tm XS\<^sub>L) \<le> closest_pair_recurrence (nat \<lfloor>real ?n / 2\<rfloor>)"
      using * by simp

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length ps"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>R" "sorted_fst XS\<^sub>R"
      using XSLR "1.prems"(1,2) sorted_fst_def sorted_wrt_drop by simp_all
    ultimately have "time (closest_pair_rec_tm XS\<^sub>R) \<le> closest_pair_recurrence (length XS\<^sub>R)"
      using "1.IH" by simp
    hence IHR: "time (closest_pair_rec_tm XS\<^sub>R) \<le> closest_pair_recurrence (nat \<lceil>real ?n / 2\<rceil>)"
      using * by simp

    have "(YS, C\<^sub>0, C\<^sub>1) = val (closest_pair_rec_tm ps)"
      using False closest_pair_rec_simps defs by (auto simp: Let_def length_eq_val_length_tm split!: prod.split)
    hence "set ps = set YS" "length ps = length YS" "distinct YS" "sorted_snd YS"
      using "1.prems" closest_pair_rec_set_length_sorted_snd closest_pair_rec_distinct
            closest_pair_rec_eq_val_closest_pair_rec_tm by auto
    moreover have "\<forall>p \<in> set YS\<^sub>L. fst p \<le> fst (hd XS\<^sub>R)"
      using False "1.prems"(2) XSLR \<open>length XS\<^sub>L < length ps\<close> \<open>length XS\<^sub>L = length ps div 2\<close>
            CP\<^sub>L_def sorted_fst_take_less_hd_drop closest_pair_rec_set_length_sorted_snd
            closest_pair_rec_eq_val_closest_pair_rec_tm by metis
    moreover have "\<forall>p \<in> set YS\<^sub>R. fst (hd XS\<^sub>R) \<le> fst p"
      using False "1.prems"(2) XSLR CP\<^sub>R_def sorted_fst_hd_drop_less_drop
            closest_pair_rec_set_length_sorted_snd closest_pair_rec_eq_val_closest_pair_rec_tm by metis
    moreover have "set YS = set YS\<^sub>L \<union> set YS\<^sub>R"
      using set_merge defs by (metis merge_eq_val_merge_tm)
    moreover have "sparse (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set YS\<^sub>L)"
      using CP\<^sub>L_def \<open>1 < length XS\<^sub>L\<close> \<open>distinct XS\<^sub>L\<close> \<open>sorted_fst XS\<^sub>L\<close>
            closest_pair_rec_dist closest_pair_rec_set_length_sorted_snd
            closest_pair_rec_eq_val_closest_pair_rec_tm by auto
    moreover have "sparse (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set YS\<^sub>R)"
      using CP\<^sub>R_def \<open>1 < length XS\<^sub>R\<close> \<open>distinct XS\<^sub>R\<close> \<open>sorted_fst XS\<^sub>R\<close>
            closest_pair_rec_dist closest_pair_rec_set_length_sorted_snd
            closest_pair_rec_eq_val_closest_pair_rec_tm by auto
    ultimately have combine_bound: "t_combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) (fst (hd XS\<^sub>R)) YS \<le> 3 + 10 * ?n"
      using t_combine_bound[of YS "set YS\<^sub>L" "set YS\<^sub>R" "fst (hd XS\<^sub>R)"] by (simp add: add.commute)
    have "time (closest_pair_rec_tm ps) = 1 + time (length_tm ps) + time (split_at_tm (?n div 2) ps) +
              time (closest_pair_rec_tm XS\<^sub>L) + time (closest_pair_rec_tm XS\<^sub>R) + time (merge_tm (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R) +
              t_combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) (fst (hd XS\<^sub>R)) YS"
      using time_closest_pair_rec_tm_simps_2[OF False] defs
      by (auto simp del: closest_pair_rec_tm.simps simp add: Let_def split: prod.split)
    also have "... \<le> 7 + 13 * ?n + time (closest_pair_rec_tm XS\<^sub>L) + time (closest_pair_rec_tm XS\<^sub>R)"
      using time_merge_tm[of "(\<lambda>p. snd p)" YS\<^sub>L YS\<^sub>R] L combine_bound by (simp add: time_length_tm time_split_at_tm)
    also have "... \<le> 7 + 13 * ?n + closest_pair_recurrence (nat \<lfloor>real ?n / 2\<rfloor>) +
              closest_pair_recurrence (nat \<lceil>real ?n / 2\<rceil>)"
      using IHL IHR by simp
    also have "... = closest_pair_recurrence (length ps)"
      using False by simp
    finally show ?thesis
      by simp
  qed
qed

theorem closest_pair_recurrence:
  "closest_pair_recurrence \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem) auto

theorem time_closest_pair_rec_bigo:
  "(\<lambda>xs. time (closest_pair_rec_tm xs)) \<in> O[length going_to at_top within { ps. distinct ps \<and> sorted_fst ps }]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>ps. ps \<in> { ps. distinct ps \<and> sorted_fst ps } \<Longrightarrow>
           time (closest_pair_rec_tm ps) \<le> (closest_pair_recurrence o length) ps"
    unfolding comp_def using time_closest_pair_rec_conv_closest_pair_recurrence by auto
  show ?thesis
    using bigo_measure_trans[OF 0] bigthetaD1[OF closest_pair_recurrence] of_nat_0_le_iff by blast
qed

definition closest_pair_time :: "nat \<Rightarrow> real" where
  "closest_pair_time n = 1 + mergesort_recurrence n + closest_pair_recurrence n"

lemma time_closest_pair_conv_closest_pair_recurrence:
  assumes "distinct ps"
  shows "time (closest_pair_tm ps) \<le> closest_pair_time (length ps)"
  using assms
  unfolding closest_pair_time_def
proof (induction rule: induct_list012)
  case (3 x y zs)
  let ?ps = "x # y # zs"
  define xs where "xs = val (mergesort_tm fst ?ps)"
  have *: "distinct xs" "sorted_fst xs" "length xs = length ?ps"
    using xs_def mergesort(4)[OF "3.prems", of fst] mergesort(1)[of fst ?ps] mergesort(3)[of fst ?ps]
          sorted_fst_def mergesort_eq_val_mergesort_tm by metis+
  have "time (closest_pair_tm ?ps) = 1 + time (mergesort_tm fst ?ps) + time (closest_pair_rec_tm xs)"
    using xs_def by (auto simp del: mergesort_tm.simps closest_pair_rec_tm.simps simp add: time_simps split: prod.split)
  also have "... \<le> 1 + mergesort_recurrence (length ?ps) + time (closest_pair_rec_tm xs)"
    using time_mergesort_conv_mergesort_recurrence[of fst ?ps] by simp
  also have "... \<le> 1 + mergesort_recurrence (length ?ps) + closest_pair_recurrence (length ?ps)"
    using time_closest_pair_rec_conv_closest_pair_recurrence[of xs] * by auto
  finally show ?case
    by blast
qed (auto simp: time_simps)

corollary closest_pair_time:
  "closest_pair_time \<in> O(\<lambda>n. n * ln n)"
  unfolding closest_pair_time_def
  using mergesort_recurrence closest_pair_recurrence sum_in_bigo(1) const_1_bigo_n_ln_n by blast

corollary time_closest_pair_bigo:
  "(\<lambda>ps. time (closest_pair_tm ps)) \<in> O[length going_to at_top within { ps. distinct ps }]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>ps. ps \<in> { ps. distinct ps } \<Longrightarrow>
           time (closest_pair_tm ps) \<le> (closest_pair_time o length) ps"
    unfolding comp_def using time_closest_pair_conv_closest_pair_recurrence by auto
  show ?thesis
    using bigo_measure_trans[OF 0] closest_pair_time by fastforce
qed


subsection "Code Export"

subsubsection "Combine Step"

fun find_closest_code :: "point \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (int * point)" where
  "find_closest_code _ _ [] = undefined"
| "find_closest_code p _ [p\<^sub>0] = (dist_code p p\<^sub>0, p\<^sub>0)"
| "find_closest_code p \<delta> (p\<^sub>0 # ps) = (
    let \<delta>\<^sub>0 = dist_code p p\<^sub>0 in
    if \<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2 then
      (\<delta>\<^sub>0, p\<^sub>0)
    else
      let (\<delta>\<^sub>1, p\<^sub>1) = find_closest_code p (min \<delta> \<delta>\<^sub>0) ps in
      if \<delta>\<^sub>0 \<le> \<delta>\<^sub>1 then
        (\<delta>\<^sub>0, p\<^sub>0)
      else
        (\<delta>\<^sub>1, p\<^sub>1)
  )"

lemma find_closest_code_dist_eq:
  "0 < length ps \<Longrightarrow> (\<delta>\<^sub>c, c) = find_closest_code p \<delta> ps \<Longrightarrow> \<delta>\<^sub>c = dist_code p c"
proof (induction p \<delta> ps arbitrary: \<delta>\<^sub>c c rule: find_closest_code.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  show ?case
  proof cases
    assume "\<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
    thus ?thesis
      using "3.prems"(2) by simp
  next
    assume A: "\<not> \<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
    define \<delta>\<^sub>0 where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist_code p p\<^sub>0"
    obtain \<delta>\<^sub>1 p\<^sub>1 where \<delta>\<^sub>1_def: "(\<delta>\<^sub>1, p\<^sub>1) = find_closest_code p (min \<delta> \<delta>\<^sub>0) (p\<^sub>2 # ps)"
      by (metis surj_pair)
    note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
    have "\<delta>\<^sub>1 = dist_code p p\<^sub>1"
      using "3.IH"[of \<delta>\<^sub>0 \<delta>\<^sub>1 p\<^sub>1] A defs by simp
    thus ?thesis
      using defs "3.prems" by (auto simp: Let_def split: if_splits prod.splits)
  qed
qed simp_all

declare find_closest.simps [simp add]

lemma find_closest_code_eq:
  assumes "0 < length ps" "\<delta> = dist c\<^sub>0 c\<^sub>1" "\<delta>' = dist_code c\<^sub>0 c\<^sub>1" "sorted_snd (p # ps)"
  assumes "c = find_closest p \<delta> ps" "(\<delta>\<^sub>c', c') = find_closest_code p \<delta>' ps"
  shows "c = c'"
  using assms
proof (induction p \<delta> ps arbitrary: \<delta>' c\<^sub>0 c\<^sub>1 c \<delta>\<^sub>c' c' rule: find_closest.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  define \<delta>\<^sub>0 \<delta>\<^sub>0' where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist p p\<^sub>0" "\<delta>\<^sub>0' = dist_code p p\<^sub>0"
  obtain p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1' where \<delta>\<^sub>1_def: "p\<^sub>1 = find_closest p (min \<delta> \<delta>\<^sub>0) (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>1', p\<^sub>1') = find_closest_code p (min \<delta>' \<delta>\<^sub>0') (p\<^sub>2 # ps)"
    by (metis surj_pair)
  note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
  show ?case
  proof cases
    assume *: "\<delta> \<le> snd p\<^sub>0 - snd p"
    hence "\<delta>' \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
      using "3.prems"(2,3) dist_eq_dist_code_abs_le by fastforce
    thus ?thesis
      using * "3.prems"(5,6) by simp
  next
    assume *: "\<not> \<delta> \<le> snd p\<^sub>0 - snd p"
    moreover have "0 \<le> snd p\<^sub>0 - snd p"
      using "3.prems"(4) sorted_snd_def by simp
    ultimately have A: "\<not> \<delta>' \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
      using "3.prems"(2,3) dist_eq_dist_code_abs_le[of c\<^sub>0 c\<^sub>1 "snd p\<^sub>0 - snd p"] by simp
    have "min \<delta> \<delta>\<^sub>0 = \<delta> \<longleftrightarrow> min \<delta>' \<delta>\<^sub>0' = \<delta>'" "min \<delta> \<delta>\<^sub>0 = \<delta>\<^sub>0 \<longleftrightarrow> min \<delta>' \<delta>\<^sub>0' = \<delta>\<^sub>0'"
      by (metis "3.prems"(2,3) defs(1,2) dist_eq_dist_code_le min.commute min_def)+
    moreover have "sorted_snd (p # p\<^sub>2 # ps)"
      using "3.prems"(4) sorted_snd_def by simp
    ultimately have B: "p\<^sub>1 = p\<^sub>1'"
      using "3.IH"[of c\<^sub>0 c\<^sub>1 \<delta>' p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1'] "3.IH"[of p p\<^sub>0 \<delta>\<^sub>0' p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1'] "3.prems"(2,3) defs * by auto
    have "\<delta>\<^sub>1' = dist_code p p\<^sub>1'"
      using find_closest_code_dist_eq defs by blast
    hence "\<delta>\<^sub>0 \<le> dist p p\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>0' \<le> \<delta>\<^sub>1'"
      using defs(1,2) dist_eq_dist_code_le by (simp add: B)
    thus ?thesis
      using "3.prems"(5,6) * A B defs by (auto simp: Let_def split: prod.splits)
  qed
qed auto

fun find_closest_pair_code :: "(int * point * point) \<Rightarrow> point list \<Rightarrow> (int * point * point)" where
  "find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) [] = (\<delta>, c\<^sub>0, c\<^sub>1)"
| "find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) [p] = (\<delta>, c\<^sub>0, c\<^sub>1)"
| "find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let (\<delta>', p\<^sub>1) = find_closest_code p\<^sub>0 \<delta> ps in
    if \<delta> \<le> \<delta>' then
      find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) ps
    else
      find_closest_pair_code (\<delta>', p\<^sub>0, p\<^sub>1) ps
  )"

lemma find_closest_pair_code_dist_eq:
  assumes "\<delta> = dist_code c\<^sub>0 c\<^sub>1" "(\<Delta>, C\<^sub>0, C\<^sub>1) = find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) ps"
  shows "\<Delta> = dist_code C\<^sub>0 C\<^sub>1"
  using assms
proof (induction "(\<delta>, c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 \<Delta> C\<^sub>0 C\<^sub>1 rule: find_closest_pair_code.induct)
  case (3 \<delta> c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  obtain \<delta>' p\<^sub>1 where \<delta>'_def: "(\<delta>', p\<^sub>1) = find_closest_code p\<^sub>0 \<delta> (p\<^sub>2 # ps)"
    by (metis surj_pair)
  hence A: "\<delta>' = dist_code p\<^sub>0 p\<^sub>1"
    using find_closest_code_dist_eq by blast
  show ?case
  proof (cases "\<delta> \<le> \<delta>'")
    case True
    obtain \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>'_def: "(\<Delta>', C\<^sub>0', C\<^sub>1') = find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases4)
    note defs = \<delta>'_def \<Delta>'_def
    hence "\<Delta>' = dist_code C\<^sub>0' C\<^sub>1'"
      using "3.hyps"(1)[of "(\<delta>', p\<^sub>1)" \<delta>' p\<^sub>1] "3.prems"(1) True \<delta>'_def by blast
    moreover have "\<Delta> = \<Delta>'" "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs True "3.prems"(2) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    obtain \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>'_def: "(\<Delta>', C\<^sub>0', C\<^sub>1') = find_closest_pair_code (\<delta>', p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases4)
    note defs = \<delta>'_def \<Delta>'_def
    hence "\<Delta>' = dist_code C\<^sub>0' C\<^sub>1'"
      using "3.hyps"(2)[of "(\<delta>', p\<^sub>1)" \<delta>' p\<^sub>1] A False \<delta>'_def by blast
    moreover have "\<Delta> = \<Delta>'" "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs False "3.prems"(2) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  qed
qed auto

declare find_closest_pair.simps [simp add]

lemma find_closest_pair_code_eq:
  assumes "\<delta> = dist c\<^sub>0 c\<^sub>1" "\<delta>' = dist_code c\<^sub>0 c\<^sub>1" "sorted_snd ps"
  assumes "(C\<^sub>0, C\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"
  assumes "(\<Delta>', C\<^sub>0', C\<^sub>1') = find_closest_pair_code (\<delta>', c\<^sub>0, c\<^sub>1) ps"
  shows "C\<^sub>0 = C\<^sub>0' \<and> C\<^sub>1 = C\<^sub>1'"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> \<delta>' c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' rule: find_closest_pair.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  obtain p\<^sub>1 \<delta>\<^sub>p' p\<^sub>1' where \<delta>\<^sub>p_def: "p\<^sub>1 = find_closest p\<^sub>0 \<delta> (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>p', p\<^sub>1') = find_closest_code p\<^sub>0 \<delta>' (p\<^sub>2 # ps)"
    by (metis surj_pair)
  hence A: "\<delta>\<^sub>p' = dist_code p\<^sub>0 p\<^sub>1'"
    using find_closest_code_dist_eq by blast
  have B: "p\<^sub>1 = p\<^sub>1'"
    using "3.prems"(1,2,3) \<delta>\<^sub>p_def find_closest_code_eq by blast
  show ?case
  proof (cases "\<delta> \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence C: "\<delta>' \<le> \<delta>\<^sub>p'"
      by (simp add: "3.prems"(1,2) A B dist_eq_dist_code_le)
    obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
      "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = find_closest_pair_code (\<delta>', c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases3)
    note defs = \<delta>\<^sub>p_def \<Delta>\<^sub>i_def
    have "sorted_snd (p\<^sub>2 # ps)"
      using "3.prems"(3) sorted_snd_def by simp
    hence "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i' \<and> C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'"
      using "3.hyps"(1) "3.prems"(1,2) True defs by blast
    moreover have "C\<^sub>0 = C\<^sub>0\<^sub>i" "C\<^sub>1 = C\<^sub>1\<^sub>i"
      using defs(1,3) True "3.prems"(1,4) apply (auto split: prod.splits) by (metis Pair_inject)+
    moreover have "\<Delta>' = \<Delta>\<^sub>i'" "C\<^sub>0' = C\<^sub>0\<^sub>i'" "C\<^sub>1' = C\<^sub>1\<^sub>i'"
      using defs(2,4) C "3.prems"(5) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    hence C: "\<not> \<delta>' \<le> \<delta>\<^sub>p'"
      by (simp add: "3.prems"(1,2) A B dist_eq_dist_code_le)
    obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
      "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = find_closest_pair (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = find_closest_pair_code (\<delta>\<^sub>p', p\<^sub>0, p\<^sub>1') (p\<^sub>2 # ps)"
      by (metis prod_cases3)
    note defs = \<delta>\<^sub>p_def \<Delta>\<^sub>i_def
    have "sorted_snd (p\<^sub>2 # ps)"
      using "3.prems"(3) sorted_snd_def by simp
    hence "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i' \<and> C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'"
      using "3.prems"(1) "3.hyps"(2) A B False defs by blast
    moreover have "C\<^sub>0 = C\<^sub>0\<^sub>i" "C\<^sub>1 = C\<^sub>1\<^sub>i"
      using defs(1,3) False "3.prems"(1,4) apply (auto split: prod.splits) by (metis Pair_inject)+
    moreover have "\<Delta>' = \<Delta>\<^sub>i'" "C\<^sub>0' = C\<^sub>0\<^sub>i'" "C\<^sub>1' = C\<^sub>1\<^sub>i'"
      using defs(2,4) C "3.prems"(5) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  qed
qed auto

fun combine_code :: "(int * point * point) \<Rightarrow> (int * point * point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (int * point * point)" where
  "combine_code (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (\<delta>, c\<^sub>0, c\<^sub>1) = if \<delta>\<^sub>L < \<delta>\<^sub>R then (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ps' = filter (\<lambda>p. (fst p - l)\<^sup>2 < \<delta>) ps in
    find_closest_pair_code (\<delta>, c\<^sub>0, c\<^sub>1) ps'
  )"

lemma combine_code_dist_eq:
  assumes "\<delta>\<^sub>L = dist_code p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L" "\<delta>\<^sub>R = dist_code p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R"
  assumes "(\<delta>, c\<^sub>0, c\<^sub>1) = combine_code (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "\<delta> = dist_code c\<^sub>0 c\<^sub>1"
  using assms by (auto simp: find_closest_pair_code_dist_eq split: if_splits)

lemma combine_code_eq:
  assumes "\<delta>\<^sub>L' = dist_code p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L" "\<delta>\<^sub>R' = dist_code p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R" "sorted_snd ps"
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  assumes "(\<delta>', c\<^sub>0', c\<^sub>1') = combine_code (\<delta>\<^sub>L', p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R', p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
proof -
  obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
    "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = (if \<delta>\<^sub>L' < \<delta>\<^sub>R' then (\<delta>\<^sub>L', p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (\<delta>\<^sub>R', p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    by metis
  define ps' ps'' where ps'_def:
    "ps' = filter (\<lambda>p. dist p (l, snd p) < dist C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i) ps"
    "ps'' = filter (\<lambda>p. (fst p - l)\<^sup>2 < \<Delta>\<^sub>i') ps"
  obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>_def:
    "(C\<^sub>0, C\<^sub>1) = find_closest_pair (C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) ps'"
    "(\<Delta>', C\<^sub>0', C\<^sub>1') = find_closest_pair_code (\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') ps''"
    by (metis prod_cases3)
  note defs = \<Delta>\<^sub>i_def ps'_def \<Delta>_def
  have *: "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i'" "C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'" "\<Delta>\<^sub>i' = dist_code C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i'"
    using \<Delta>\<^sub>i_def assms(1,2,3,4) dist_eq_dist_code_lt by (auto split: if_splits)
  hence "\<And>p. \<bar>fst p - l\<bar> < dist C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<longleftrightarrow> (fst p - l)\<^sup>2 < \<Delta>\<^sub>i'"
    using dist_eq_dist_code_abs_lt by (metis (mono_tags) of_int_abs)
  hence "ps' = ps''"
    using ps'_def dist_fst_abs by auto
  moreover have "sorted_snd ps'"
    using assms(3) ps'_def sorted_snd_def sorted_wrt_filter by blast
  ultimately have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
    using * find_closest_pair_code_eq \<Delta>_def by blast+
  moreover have "C\<^sub>0 = c\<^sub>0" "C\<^sub>1 = c\<^sub>1"
    using assms(4) defs(1,3,5) apply (auto simp: combine.simps split: prod.splits) by (metis Pair_inject)+
  moreover have "C\<^sub>0' = c\<^sub>0'" "C\<^sub>1' = c\<^sub>1'"
    using assms(5) defs(2,4,6) apply (auto split: prod.splits) by (metis prod.inject)+
  ultimately show ?thesis
    by blast
qed

subsubsection "Divide and Conquer Algorithm"

function closest_pair_rec_code :: "point list \<Rightarrow> (point list * int * point * point)" where
  "closest_pair_rec_code xs = (
    let n = length xs in
    if n \<le> 3 then
      (mergesort snd xs, closest_pair_bf_code xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec_code xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec_code xs\<^sub>R in

      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine_code p\<^sub>L p\<^sub>R l ys)
  )"
  by pat_completeness auto
termination closest_pair_rec_code
  by (relation "Wellfounded.measure (\<lambda>xs. length xs)")
     (auto simp: split_at_take_drop_conv Let_def)

lemma closest_pair_rec_code_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest_pair_rec_code xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec_code xs\<^sub>L in
    let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec_code xs\<^sub>R in
    let ys = merge snd ys\<^sub>L ys\<^sub>R in
    (ys, combine_code p\<^sub>L p\<^sub>R l ys)
  )"
  using assms by (auto simp: Let_def)

declare combine.simps combine_code.simps closest_pair_rec_code.simps [simp del]

lemma closest_pair_rec_code_dist_eq:
  assumes "1 < length xs" "(ys, \<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_rec_code xs"
  shows "\<delta> = dist_code c\<^sub>0 c\<^sub>1"
  using assms
proof (induction xs arbitrary: ys \<delta> c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(\<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code xs"
      using "1.prems"(2) closest_pair_rec_code.simps by simp
    thus ?thesis
      using "1.prems"(1) closest_pair_bf_code_dist_eq by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L \<Delta>\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, \<Delta>\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R \<Delta>\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, \<Delta>\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain \<Delta> C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(\<Delta>, C\<^sub>0, C\<^sub>1) = combine_code (\<Delta>\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (\<Delta>\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "\<Delta>\<^sub>L = dist_code C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L"
      using "1.IH" defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "\<Delta>\<^sub>R = dist_code C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R"
      using "1.IH" defs by metis+

    have *: "(YS, \<Delta>, C\<^sub>0, C\<^sub>1) = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs by (auto simp: Let_def split: prod.split)
    moreover have "\<Delta> = dist_code C\<^sub>0 C\<^sub>1"
      using combine_code_dist_eq IHL IHR C\<^sub>0\<^sub>1_def by blast
    ultimately show ?thesis
      using "1.prems"(2) * by (metis Pair_inject)
  qed
qed

lemma closest_pair_rec_ys_eq:
  assumes "1 < length xs"
  assumes "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  assumes "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code xs"
  shows "ys = ys'"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "ys = mergesort snd xs"
      using "1.prems"(2) closest_pair_rec.simps by simp
    moreover have "ys' = mergesort snd xs"
      using "1.prems"(3) closest_pair_rec_code.simps by (simp add: True)
    ultimately show ?thesis
      using "1.prems"(1) by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L YS\<^sub>L' \<Delta>\<^sub>L' C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L' where YSC\<^sub>0\<^sub>1\<^sub>L_def:
      "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      "(YS\<^sub>L', \<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R YS\<^sub>R' \<Delta>\<^sub>R' C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R' where YSC\<^sub>0\<^sub>1\<^sub>R_def:
      "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      "(YS\<^sub>R', \<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS YS' where YS_def:
      "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
      "YS' = merge (\<lambda>p. snd p) YS\<^sub>L' YS\<^sub>R'"
    obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where C\<^sub>0\<^sub>1_def:
      "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      "(\<Delta>', C\<^sub>0', C\<^sub>1') = combine_code (\<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') (\<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') L YS'"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "YS\<^sub>L = YS\<^sub>L'"
      using "1.IH" defs by metis

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "YS\<^sub>R = YS\<^sub>R'"
      using "1.IH" defs by metis

    have "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs(1,2,3,5,7,9)
      by (auto simp: Let_def split: prod.split)
    moreover have "(YS', \<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs(1,2,4,6,8,10)
      by (auto simp: Let_def split: prod.split)
    moreover have "YS = YS'"
      using IHL IHR YS_def by simp
    ultimately show ?thesis
      by (metis "1.prems"(2,3) Pair_inject)
  qed
qed

lemma closest_pair_rec_code_eq:
  assumes "1 < length xs"
  assumes "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  assumes "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code xs"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(2) closest_pair_rec.simps by simp
    moreover have "(\<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code xs"
      using "1.prems"(3) closest_pair_rec_code.simps by (simp add: True)
    ultimately show ?thesis
      using "1.prems"(1) closest_pair_bf_code_eq by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L YS\<^sub>L' \<Delta>\<^sub>L' C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L' where YSC\<^sub>0\<^sub>1\<^sub>L_def:
      "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      "(YS\<^sub>L', \<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R YS\<^sub>R' \<Delta>\<^sub>R' C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R' where YSC\<^sub>0\<^sub>1\<^sub>R_def:
      "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      "(YS\<^sub>R', \<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS YS' where YS_def:
      "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
      "YS' = merge (\<lambda>p. snd p) YS\<^sub>L' YS\<^sub>R'"
    obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where C\<^sub>0\<^sub>1_def:
      "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      "(\<Delta>', C\<^sub>0', C\<^sub>1') = combine_code (\<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') (\<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') L YS'"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "C\<^sub>0\<^sub>L = C\<^sub>0\<^sub>L'" "C\<^sub>1\<^sub>L = C\<^sub>1\<^sub>L'"
      using "1.IH" defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "C\<^sub>0\<^sub>R = C\<^sub>0\<^sub>R'" "C\<^sub>1\<^sub>R = C\<^sub>1\<^sub>R'"
      using "1.IH" defs by metis+

    have "sorted_snd YS\<^sub>L" "sorted_snd YS\<^sub>R"
      using closest_pair_rec_set_length_sorted_snd YSC\<^sub>0\<^sub>1\<^sub>L_def(1) YSC\<^sub>0\<^sub>1\<^sub>R_def(1) by blast+
    hence "sorted_snd YS"
      using sorted_merge sorted_snd_def YS_def by blast
    moreover have "YS = YS'"
      using defs \<open>1 < length XS\<^sub>L\<close> \<open>1 < length XS\<^sub>R\<close> closest_pair_rec_ys_eq by blast
    moreover have "\<Delta>\<^sub>L' = dist_code C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L'" "\<Delta>\<^sub>R' = dist_code C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R'"
      using defs \<open>1 < length XS\<^sub>L\<close> \<open>1 < length XS\<^sub>R\<close> closest_pair_rec_code_dist_eq by blast+
    ultimately have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using combine_code_eq IHL IHR C\<^sub>0\<^sub>1_def by blast+
    moreover have "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs(1,2,3,5,7,9)
      by (auto simp: Let_def split: prod.split)
    moreover have "(YS', \<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs(1,2,4,6,8,10)
      by (auto simp: Let_def split: prod.split)
    ultimately show ?thesis
      using "1.prems"(2,3) by (metis Pair_inject)
  qed
qed

declare closest_pair.simps [simp add]

fun closest_pair_code :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_code [] = undefined"
| "closest_pair_code [_] = undefined"
| "closest_pair_code ps = (let (_, _, c\<^sub>0, c\<^sub>1) = closest_pair_rec_code (mergesort fst ps) in (c\<^sub>0, c\<^sub>1))"

lemma closest_pair_code_eq:
  "closest_pair ps = closest_pair_code ps"
proof (induction ps rule: induct_list012)
  case (3 x y zs)
  obtain ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' where *:
    "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec (mergesort fst (x # y # zs))"
    "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code (mergesort fst (x # y # zs))"
    by (metis prod_cases3)
  moreover have "1 < length (mergesort fst (x # y # zs))"
    using length_mergesort[of fst "x # y # zs"] by simp
  ultimately have "c\<^sub>0 = c\<^sub>0'" "c\<^sub>1 = c\<^sub>1'"
    using closest_pair_rec_code_eq by blast+
  thus ?case
    using * by (auto split: prod.splits)
qed auto

export_code closest_pair_code in OCaml
  module_name Verified

end
