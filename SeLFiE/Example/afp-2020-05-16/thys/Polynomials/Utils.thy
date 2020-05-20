(* Author: Alexander Maletzky *)

section \<open>Utilities\<close>

theory Utils
  imports Main Well_Quasi_Orders.Almost_Full_Relations
begin

lemma subset_imageE_inj:
  assumes "B \<subseteq> f ` A"
  obtains C where "C \<subseteq> A" and "B = f ` C" and "inj_on f C"
proof -
  define g where "g = (\<lambda>x. SOME a. a \<in> A \<and> f a = x)"
  have "g b \<in> A \<and> f (g b) = b" if "b \<in> B" for b
  proof -
    from that assms have "b \<in> f ` A" ..
    then obtain a where "a \<in> A" and "b = f a" ..
    hence "a \<in> A \<and> f a = b" by simp
    thus ?thesis unfolding g_def by (rule someI)
  qed
  hence 1: "\<And>b. b \<in> B \<Longrightarrow> g b \<in> A" and 2: "\<And>b. b \<in> B \<Longrightarrow> f (g b) = b" by simp_all
  let ?C = "g ` B"
  show ?thesis
  proof
    show "?C \<subseteq> A" by (auto intro: 1)
  next
    show "B = f ` ?C"
    proof (rule set_eqI)
      fix b
      show "b \<in> B \<longleftrightarrow> b \<in> f ` ?C"
      proof
        assume "b \<in> B"
        moreover from this have "f (g b) = b" by (rule 2)
        ultimately show "b \<in> f ` ?C" by force
      next
        assume "b \<in> f ` ?C"
        then obtain b' where "b' \<in> B" and "b = f (g b')" unfolding image_image ..
        moreover from this(1) have "f (g b') = b'" by (rule 2)
        ultimately show "b \<in> B" by simp
      qed
    qed
  next
    show "inj_on f ?C"
    proof
      fix x y
      assume "x \<in> ?C"
      then obtain bx where "bx \<in> B" and x: "x = g bx" ..
      moreover from this(1) have "f (g bx) = bx" by (rule 2)
      ultimately have *: "f x = bx" by simp
      assume "y \<in> ?C"
      then obtain "by" where "by \<in> B" and y: "y = g by" ..
      moreover from this(1) have "f (g by) = by" by (rule 2)
      ultimately have "f y = by" by simp
      moreover assume "f x = f y"
      ultimately have "bx = by" using * by simp
      thus "x = y" by (simp only: x y)
    qed
  qed
qed

lemma wfP_chain:
  assumes "\<not>(\<exists>f. \<forall>i. r (f (Suc i)) (f i))"
  shows "wfP r"
proof -
  from assms wf_iff_no_infinite_down_chain[of "{(x, y). r x y}"] have "wf {(x, y). r x y}" by auto
  thus "wfP r" unfolding wfP_def .
qed

lemma transp_sequence:
  assumes "transp r" and "\<And>i. r (seq (Suc i)) (seq i)" and "i < j"
  shows "r (seq j) (seq i)"
proof -
  have "\<And>k. r (seq (i + Suc k)) (seq i)"
  proof -
    fix k::nat
    show "r (seq (i + Suc k)) (seq i)"
    proof (induct k)
      case 0
      from assms(2) have "r (seq (Suc i)) (seq i)" .
      thus ?case by simp
    next
      case (Suc k)
      note assms(1)
      moreover from assms(2) have "r (seq (Suc (Suc i + k))) (seq (Suc (i + k)))" by simp
      moreover have "r (seq (Suc (i + k))) (seq i)" using Suc.hyps by simp
      ultimately have "r (seq (Suc (Suc i + k))) (seq i)" by (rule transpD)
      thus ?case by simp
    qed
  qed
  hence "r (seq (i + Suc(j - i - 1))) (seq i)" .
  thus "r (seq j) (seq i)" using \<open>i < j\<close> by simp
qed

lemma almost_full_on_finite_subsetE:
  assumes "reflp P" and "almost_full_on P S"
  obtains T where "finite T" and "T \<subseteq> S" and "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. P t s)"
proof -
  define crit where "crit = (\<lambda>U s. s \<in> S \<and> (\<forall>u\<in>U. \<not> P u s))"
  have critD: "s \<notin> U" if "crit U s" for U s
  proof
    assume "s \<in> U"
    from \<open>crit U s\<close> have "\<forall>u\<in>U. \<not> P u s" unfolding crit_def ..
    from this \<open>s \<in> U\<close> have "\<not> P s s" ..
    moreover from assms(1) have "P s s" by (rule reflpD)
    ultimately show False ..
  qed
  define "fun"
    where "fun = (\<lambda>U. (if (\<exists>s. crit U s) then
                        insert (SOME s. crit U s) U
                      else
                        U
                      ))"
  define seq where "seq = rec_nat {} (\<lambda>_. fun)"
  have seq_Suc: "seq (Suc i) = fun (seq i)" for i by (simp add: seq_def)
  
  have seq_incr_Suc: "seq i \<subseteq> seq (Suc i)" for i by (auto simp add: seq_Suc fun_def)
  have seq_incr: "i \<le> j \<Longrightarrow> seq i \<subseteq> seq j" for i j
  proof -
    assume "i \<le> j"
    hence "i = j \<or> i < j" by auto
    thus "seq i \<subseteq> seq j"
    proof
      assume "i = j"
      thus ?thesis by simp
    next
      assume "i < j"
      with _ seq_incr_Suc show ?thesis by (rule transp_sequence, simp add: transp_def)
    qed
  qed
  have sub: "seq i \<subseteq> S" for i
  proof (induct i, simp add: seq_def, simp add: seq_Suc fun_def, rule)
    fix i
    assume "Ex (crit (seq i))"
    hence "crit (seq i) (Eps (crit (seq i)))" by (rule someI_ex)
    thus "Eps (crit (seq i)) \<in> S" by (simp add: crit_def)
  qed
  have "\<exists>i. seq (Suc i) = seq i"
  proof (rule ccontr, simp)
    assume "\<forall>i. seq (Suc i) \<noteq> seq i"
    with seq_incr_Suc have "seq i \<subset> seq (Suc i)" for i by blast
    define seq1 where "seq1 = (\<lambda>n. (SOME s. s \<in> seq (Suc n) \<and> s \<notin> seq n))"
    have seq1: "seq1 n \<in> seq (Suc n) \<and> seq1 n \<notin> seq n" for n unfolding seq1_def
    proof (rule someI_ex)
      from \<open>seq n \<subset> seq (Suc n)\<close> show "\<exists>x. x \<in> seq (Suc n) \<and> x \<notin> seq n" by blast
    qed
    have "seq1 i \<in> S" for i
    proof
      from seq1[of i] show "seq1 i \<in> seq (Suc i)" ..
    qed (fact sub)
    with assms(2) obtain a b where "a < b" and "P (seq1 a) (seq1 b)" by (rule almost_full_onD)
    from \<open>a < b\<close> have "Suc a \<le> b" by simp
    from seq1 have "seq1 a \<in> seq (Suc a)" ..
    also from \<open>Suc a \<le> b\<close> have "... \<subseteq> seq b" by (rule seq_incr)
    finally have "seq1 a \<in> seq b" .
    from seq1 have "seq1 b \<in> seq (Suc b)" and "seq1 b \<notin> seq b" by blast+
    hence "crit (seq b) (seq1 b)" by (simp add: seq_Suc fun_def someI split: if_splits)
    hence "\<forall>u\<in>seq b. \<not> P u (seq1 b)" by (simp add: crit_def)
    from this \<open>seq1 a \<in> seq b\<close> have "\<not> P (seq1 a) (seq1 b)" ..
    from this \<open>P (seq1 a) (seq1 b)\<close> show False ..
  qed
  then obtain i where "seq (Suc i) = seq i" ..
  show ?thesis
  proof
    show "finite (seq i)" by (induct i, simp_all add: seq_def fun_def)
  next
    fix s
    assume "s \<in> S"
    let ?s = "Eps (crit (seq i))"
    show "\<exists>t\<in>seq i. P t s"
    proof (rule ccontr, simp)
      assume "\<forall>t\<in>seq i. \<not> P t s"
      with \<open>s \<in> S\<close> have "crit (seq i) s" by (simp only: crit_def)
      hence "crit (seq i) ?s" and eq: "seq (Suc i) = insert ?s (seq i)"
        by (auto simp add: seq_Suc fun_def intro: someI)
      from this(1) have "?s \<notin> seq i" by (rule critD)
      hence "seq (Suc i) \<noteq> seq i" unfolding eq by blast
      from this \<open>seq (Suc i) = seq i\<close> show False ..
    qed
  qed (fact sub)
qed

subsection \<open>Lists\<close>

lemma map_upt: "map (\<lambda>i. f (xs ! i)) [0..<length xs] = map f xs"
  by (auto intro: nth_equalityI)

lemma map_upt_zip:
  assumes "length xs = length ys"
  shows "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] = map (\<lambda>(x, y). f x y) (zip xs ys)" (is "?l = ?r")
proof -
  have len_l: "length ?l = length ys" by simp
  from assms have len_r: "length ?r = length ys" by simp
  show ?thesis
  proof (simp only: list_eq_iff_nth_eq len_l len_r, rule, rule, intro allI impI)
    fix i
    assume "i < length ys"
    hence "i < length ?l" and "i < length ?r" by (simp_all only: len_l len_r)
    thus "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] ! i = map (\<lambda>(x, y). f x y) (zip xs ys) ! i"
      by simp
  qed
qed

lemma distinct_sorted_wrt_irrefl:
  assumes "irreflp rel" and "transp rel" and "sorted_wrt rel xs"
  shows "distinct xs"
  using assms(3)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons(2) have "sorted_wrt rel xs" and *: "\<forall>y\<in>set xs. rel x y"
    by (simp_all)
  from this(1) have "distinct xs" by (rule Cons(1))
  show ?case
  proof (simp add: \<open>distinct xs\<close>, rule)
    assume "x \<in> set xs"
    with * have "rel x x" ..
    with assms(1) show False by (simp add: irreflp_def)
  qed
qed

lemma distinct_sorted_wrt_imp_sorted_wrt_strict:
  assumes "distinct xs" and "sorted_wrt rel xs"
  shows "sorted_wrt (\<lambda>x y. rel x y \<and> \<not> x = y) xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case step: (Cons x xs)
  show ?case
  proof (cases "xs")
    case Nil
    thus ?thesis by simp
  next
    case (Cons y zs)
    from step(2) have "x \<noteq> y" and 1: "distinct (y # zs)" by (simp_all add: Cons)
    from step(3) have "rel x y" and 2: "sorted_wrt rel (y # zs)" by (simp_all add: Cons)
    from 1 2 have "sorted_wrt (\<lambda>x y. rel x y \<and> x \<noteq> y) (y # zs)" by (rule step(1)[simplified Cons])
    with \<open>x \<noteq> y\<close> \<open>rel x y\<close> show ?thesis using step.prems by (auto simp: Cons)
  qed
qed

lemma sorted_wrt_distinct_set_unique:
  assumes "antisymp rel"
  assumes "sorted_wrt rel xs" "distinct xs" "sorted_wrt rel ys" "distinct ys" "set xs = set ys"
  shows "xs = ys"
proof -
  from assms have 1: "length xs = length ys" by (auto dest!: distinct_card)
  from assms(2-6) show ?thesis
  proof(induct rule:list_induct2[OF 1])
    case 1
    show ?case by simp
  next
    case (2 x xs y ys)
    from 2(4) have "x \<notin> set xs" and "distinct xs" by simp_all
    from 2(6) have "y \<notin> set ys" and "distinct ys" by simp_all
    have "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      from 2(3) have "\<forall>z\<in>set xs. rel x z" by (simp)
      moreover from \<open>x \<noteq> y\<close> have "y \<in> set xs" using 2(7) by auto
      ultimately have *: "rel x y" ..
      from 2(5) have "\<forall>z\<in>set ys. rel y z" by (simp)
      moreover from \<open>x \<noteq> y\<close> have "x \<in> set ys" using 2(7) by auto
      ultimately have "rel y x" ..
      with assms(1) * have "x = y" by (rule antisympD)
      with \<open>x \<noteq> y\<close> show False ..
    qed
    from 2(3) have "sorted_wrt rel xs" by (simp)
    moreover note \<open>distinct xs\<close>
    moreover from 2(5) have "sorted_wrt rel ys" by (simp)
    moreover note \<open>distinct ys\<close>
    moreover from 2(7) \<open>x \<notin> set xs\<close> \<open>y \<notin> set ys\<close> have "set xs = set ys" by (auto simp add: \<open>x = y\<close>)
    ultimately have "xs = ys" by (rule 2(2))
    with \<open>x = y\<close> show ?case by simp
  qed
qed

lemma sorted_wrt_refl_nth_mono:
  assumes "reflp P" and "sorted_wrt P xs" and "i \<le> j" and "j < length xs"
  shows "P (xs ! i) (xs ! j)"
proof (cases "i < j")
  case True
  from assms(2) this assms(4) show ?thesis by (rule sorted_wrt_nth_less)
next
  case False
  with assms(3) have "i = j" by simp
  from assms(1) show ?thesis unfolding \<open>i = j\<close> by (rule reflpD)
qed

fun merge_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_wrt _ xs [] = xs"|
  "merge_wrt rel [] ys = ys"|
  "merge_wrt rel (x # xs) (y # ys) =
    (if x = y then
      y # (merge_wrt rel xs ys)
    else if rel x y then
      x # (merge_wrt rel xs (y # ys))
    else
      y # (merge_wrt rel (x # xs) ys)
    )"

lemma set_merge_wrt: "set (merge_wrt rel xs ys) = set xs \<union> set ys"
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  show ?case by simp
next
  case (2 rel y ys)
  show ?case by simp
next
  case (3 rel x xs y ys)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis by (simp add: 3(1))
  next
    case False
    show ?thesis
    proof (cases "rel x y")
      case True
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(2) insert_commute)
    next
      case False
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(3))
    qed
  qed
qed

lemma sorted_merge_wrt:
  assumes "transp rel" and "\<And>x y. x \<noteq> y \<Longrightarrow> rel x y \<or> rel y x"
    and "sorted_wrt rel xs" and "sorted_wrt rel ys"
  shows "sorted_wrt rel (merge_wrt rel xs ys)"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  from 1(3) show ?case by simp
next
  case (2 rel y ys)
  from 2(4) show ?case by simp
next
  case (3 rel x xs y ys)
  show ?case
  proof (cases "x = y")
    case True
    show ?thesis
    proof (auto simp add: True)
      fix z
      assume "z \<in> set (merge_wrt rel xs ys)"
      hence "z \<in> set xs \<union> set ys" by (simp only: set_merge_wrt)
      thus "rel y z"
      proof
        assume "z \<in> set xs"
        with 3(6) show ?thesis by (simp add: True)
      next
        assume "z \<in> set ys"
        with 3(7) show ?thesis by (simp)
      qed
    next
      note True 3(4, 5)
      moreover from 3(6) have "sorted_wrt rel xs" by (simp)
      moreover from 3(7) have "sorted_wrt rel ys" by (simp)
      ultimately show "sorted_wrt rel (merge_wrt rel xs ys)" by (rule 3(1))
    qed
  next
    case False
    show ?thesis
    proof (cases "rel x y")
      case True
      show ?thesis
      proof (auto simp add: False True)
        fix z
        assume "z \<in> set (merge_wrt rel xs (y # ys))"
        hence "z \<in> insert y (set xs \<union> set ys)" by (simp add: set_merge_wrt)
        thus "rel x z"
        proof
          assume "z = y"
          with True show ?thesis by simp
        next
          assume "z \<in> set xs \<union> set ys"
          thus ?thesis
          proof
            assume "z \<in> set xs"
            with 3(6) show ?thesis by (simp)
          next
            assume "z \<in> set ys"
            with 3(7) have "rel y z" by (simp)
            with 3(4) True show ?thesis by (rule transpD)
          qed
        qed
      next
        note False True 3(4, 5)
        moreover from 3(6) have "sorted_wrt rel xs" by (simp)
        ultimately show "sorted_wrt rel (merge_wrt rel xs (y # ys))" using 3(7) by (rule 3(2))
      qed
    next
      assume "\<not> rel x y"
      from \<open>x \<noteq> y\<close> have "rel x y \<or> rel y x" by (rule 3(5))
      with \<open>\<not> rel x y\<close> have *: "rel y x" by simp
      show ?thesis
      proof (auto simp add: False \<open>\<not> rel x y\<close>)
        fix z
        assume "z \<in> set (merge_wrt rel (x # xs) ys)"
        hence "z \<in> insert x (set xs \<union> set ys)" by (simp add: set_merge_wrt)
        thus "rel y z"
        proof
          assume "z = x"
          with * show ?thesis by simp
        next
          assume "z \<in> set xs \<union> set ys"
          thus ?thesis
          proof
            assume "z \<in> set xs"
            with 3(6) have "rel x z" by (simp)
            with 3(4) * show ?thesis by (rule transpD)
          next
            assume "z \<in> set ys"
            with 3(7) show ?thesis by (simp)
          qed
        qed
      next
        note False \<open>\<not> rel x y\<close> 3(4, 5, 6)
        moreover from 3(7) have "sorted_wrt rel ys" by (simp)
        ultimately show "sorted_wrt rel (merge_wrt rel (x # xs) ys)" by (rule 3(3))
      qed
    qed
  qed
qed

lemma set_fold:
  assumes "\<And>x ys. set (f (g x) ys) = set (g x) \<union> set ys"
  shows "set (fold (\<lambda>x. f (g x)) xs ys) = (\<Union>x\<in>set xs. set (g x)) \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "set (fold (\<lambda>x. f (g x)) xs (f (g x) ys)) = (\<Union>x\<in>set xs. set (g x)) \<union> set (f (g x) ys)"
    by (rule Cons)
  show ?case by (simp add: o_def assms set_merge_wrt eq ac_simps)
qed

subsection \<open>Sums and Products\<close>

lemma additive_implies_homogenous:
  assumes "\<And>x y. f (x + y) = f x + ((f (y::'a::monoid_add))::'b::cancel_comm_monoid_add)"
  shows "f 0 = 0"
proof -
  have "f (0 + 0) = f 0 + f 0" by (rule assms)
  hence "f 0 = f 0 + f 0" by simp
  thus "f 0 = 0" by simp
qed

lemma fun_sum_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum g A) = (\<Sum>a\<in>A. f (g a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    thus ?case by (simp add: assms(1))
  next
    case step: (insert a A)
    show ?case by (simp add: sum.insert[OF step(1) step(2)] assms(2) step(3))
  qed
next
  case False
  thus ?thesis by (simp add: assms(1))
qed

lemma fun_sum_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum g A) = (\<Sum>a\<in>A. f (g a))"
  by (rule fun_sum_commute, rule additive_implies_homogenous, fact+)

lemma fun_sum_list_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum_list xs) = sum_list (map f xs)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: assms(1))
next
  case (Cons x xs)
  thus ?case by (simp add: assms(2))
qed

lemma fun_sum_list_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum_list xs) = sum_list (map f xs)"
  by (rule fun_sum_list_commute, rule additive_implies_homogenous, fact+)

lemma sum_set_upt_eq_sum_list: "(\<Sum>i = m..<n. f i) = (\<Sum>i\<leftarrow>[m..<n]. f i)"
  using sum_set_upt_conv_sum_list_nat by auto

lemma sum_list_upt: "(\<Sum>i\<leftarrow>[0..<(length xs)]. f (xs ! i)) = (\<Sum>x\<leftarrow>xs. f x)"
  by (simp only: map_upt)

lemma sum_list_upt_zip:
  assumes "length xs = length ys"
  shows "(\<Sum>i\<leftarrow>[0..<(length ys)]. f (xs ! i) (ys ! i)) = (\<Sum>(x, y)\<leftarrow>(zip xs ys). f x y)"
  by (simp only: map_upt_zip[OF assms])

lemma sum_list_zeroI:
  assumes "set xs \<subseteq> {0}"
  shows "sum_list xs = 0"
  using assms by (induct xs, auto)

lemma fun_prod_commute:
  assumes "f 1 = 1" and "\<And>x y. f (x * y) = f x * f y"
  shows "f (prod g A) = (\<Prod>a\<in>A. f (g a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    thus ?case by (simp add: assms(1))
  next
    case step: (insert a A)
    show ?case by (simp add: prod.insert[OF step(1) step(2)] assms(2) step(3))
  qed
next
  case False
  thus ?thesis by (simp add: assms(1))
qed

end (* theory *)
