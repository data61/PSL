section \<open>Lexicographic Extension\<close>

theory Lexicographic_Extension
  imports
    Matrix.Utility
    Order_Pair
begin

text \<open>
  In this theory we define the lexicographic extension of an order pair, so that it generalizes
  the existing notion @{const lex_prod} which is based on a single order only.

  Our main result is that this extension yields again an order pair.
\<close>

fun lex_two :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel" 
  where
    "lex_two s ns s2 = {((a1, b1), (a2, b2)) . (a1, a2) \<in> s \<or> (a1, a2) \<in> ns \<and> (b1, b2) \<in> s2}"

lemma lex_two:
  assumes compat: "ns O s \<subseteq> s"
    and SN_s: "SN s" 
    and SN_s2: "SN s2"
  shows "SN (lex_two s ns s2)" (is "SN ?r")
proof
  fix f
  assume "\<forall> i. (f i, f (Suc i)) \<in> ?r"
  then have steps: "\<And> i. (f i, f (Suc i)) \<in> ?r" ..
  let ?a = "\<lambda> i. fst (f i)"
  let ?b = "\<lambda> i. snd (f i)"
  {
    fix i
    from steps[of i]
    have "(?a i, ?a (Suc i)) \<in> s \<or> (?a i, ?a (Suc i)) \<in> ns \<and> (?b i, ?b (Suc i)) \<in> s2"
      by (cases "f i", cases "f (Suc i)", auto)
  }
  note steps = this
  have "\<exists> j. \<forall> i \<ge> j. (?a i, ?a (Suc i)) \<in> ns - s"
    by (rule non_strict_ending[OF _ compat], insert steps SN_s, unfold SN_on_def, auto)
  with steps obtain j where steps: "\<And> i. i \<ge> j \<Longrightarrow> (?b i, ?b (Suc i)) \<in> s2" by auto
  obtain g where g: "g = (\<lambda> i. ?b (j + i))" by auto
  from steps have "\<And> i. (g i, g (Suc i)) \<in> s2" unfolding g by auto
  with SN_s2 show False unfolding SN_defs by auto
qed

lemma lex_two_compat:
  assumes compat1: "ns1 O s1 \<subseteq> s1"
    and compat1': "s1 O ns1 \<subseteq> s1"
    and trans1: "s1 O s1 \<subseteq> s1"
    and trans1': "ns1 O ns1 \<subseteq> ns1"
    and compat2: "ns2 O s2 \<subseteq> s2"
    and ns: "(ab1, ab2) \<in> lex_two s1 ns1 ns2" 
    and s: "(ab2, ab3) \<in> lex_two s1 ns1 s2"
  shows "(ab1, ab3) \<in> lex_two s1 ns1 s2"
proof -
  obtain a1 b1 where ab1: "ab1 = (a1, b1)" by force
  obtain a2 b2 where ab2: "ab2 = (a2, b2)" by force
  obtain a3 b3 where ab3: "ab3 = (a3, b3)" by force
  note id = ab1 ab2 ab3
  show ?thesis
  proof (cases "(a1, a2) \<in> s1")
    case s1: True
    show ?thesis 
    proof (cases "(a2, a3) \<in> s1")
      case s2: True
      from trans1 s1 s2 show ?thesis unfolding id by auto
    next
      case False with s have "(a2, a3) \<in> ns1" unfolding id by simp
      from compat1' s1 this show ?thesis unfolding id by auto
    qed
  next
    case False 
    with ns have ns: "(a1, a2) \<in> ns1" "(b1, b2) \<in> ns2" unfolding id by auto
    show ?thesis
    proof (cases "(a2, a3) \<in> s1")
      case s2: True
      from compat1 ns(1) s2 show ?thesis unfolding id by auto
    next
      case False
      with s have nss: "(a2, a3) \<in> ns1" "(b2, b3) \<in> s2" unfolding id by auto
      from trans1' ns(1) nss(1) compat2 ns(2) nss(2)
      show ?thesis unfolding id by auto
    qed
  qed
qed

lemma lex_two_compat':
  assumes compat1: "ns1 O s1 \<subseteq> s1"
    and compat1': "s1 O ns1 \<subseteq> s1"
    and trans1: "s1 O s1 \<subseteq> s1"
    and trans1': "ns1 O ns1 \<subseteq> ns1"
    and compat2': "s2 O ns2 \<subseteq> s2"
    and s: "(ab1, ab2) \<in> lex_two s1 ns1 s2" 
    and ns: "(ab2, ab3) \<in> lex_two s1 ns1 ns2"
  shows "(ab1, ab3) \<in> lex_two s1 ns1 s2"
proof -
  obtain a1 b1 where ab1: "ab1 = (a1, b1)" by force
  obtain a2 b2 where ab2: "ab2 = (a2, b2)" by force
  obtain a3 b3 where ab3: "ab3 = (a3, b3)" by force
  note id = ab1 ab2 ab3
  show ?thesis
  proof (cases "(a1, a2) \<in> s1")
    case s1: True
    show ?thesis 
    proof (cases "(a2, a3) \<in> s1")
      case s2: True
      from trans1 s1 s2 show ?thesis unfolding id by auto
    next
      case False with ns have "(a2, a3) \<in> ns1" unfolding id by simp
      from compat1' s1 this show ?thesis unfolding id by auto
    qed
  next
    case False 
    with s have s: "(a1, a2) \<in> ns1" "(b1, b2) \<in> s2" unfolding id by auto
    show ?thesis
    proof (cases "(a2, a3) \<in> s1")
      case s2: True
      from compat1 s(1) s2 show ?thesis unfolding id by auto
    next
      case False
      with ns have nss: "(a2, a3) \<in> ns1" "(b2, b3) \<in> ns2" unfolding id by auto
      from trans1' s(1) nss(1) compat2' s(2) nss(2)
      show ?thesis unfolding id by auto
    qed
  qed
qed

lemma lex_two_compat2:
  assumes "ns1 O s1 \<subseteq> s1" "s1 O ns1 \<subseteq> s1" "s1 O s1 \<subseteq> s1" "ns1 O ns1 \<subseteq> ns1" "ns2 O s2 \<subseteq> s2"
  shows "lex_two s1 ns1 ns2 O lex_two s1 ns1 s2 \<subseteq> lex_two s1 ns1 s2"
  using lex_two_compat[OF assms] by (intro subsetI, elim relcompE, fast)

lemma lex_two_compat'2:
  assumes "ns1 O s1 \<subseteq> s1" "s1 O ns1 \<subseteq> s1" "s1 O s1 \<subseteq> s1" "ns1 O ns1 \<subseteq> ns1" "s2 O ns2 \<subseteq> s2"
  shows "lex_two s1 ns1 s2 O lex_two s1 ns1 ns2 \<subseteq> lex_two s1 ns1 s2"
  using lex_two_compat'[OF assms] by (intro subsetI, elim relcompE, fast)

lemma lex_two_refl:
  assumes r1: "refl ns1" and r2: "refl ns2"
  shows "refl (lex_two s1 ns1 ns2)"
  using refl_onD[OF r1] and refl_onD[OF r2] by (intro refl_onI) auto

lemma lex_two_order_pair:
  assumes o1: "order_pair s1 ns1" and o2: "order_pair s2 ns2"
  shows "order_pair (lex_two s1 ns1 s2) (lex_two s1 ns1 ns2)"
proof -
  interpret o1: order_pair s1 ns1 using o1.
  interpret o2: order_pair s2 ns2 using o2.
  note o1.trans_S o1.trans_NS o2.trans_S o2.trans_NS 
    o1.compat_NS_S o2.compat_NS_S o1.compat_S_NS o2.compat_S_NS
  note this [unfolded trans_O_iff]
  note o1.refl_NS o2.refl_NS
  show ?thesis
    by (unfold_locales, intro lex_two_refl, fact+, unfold trans_O_iff)
      (rule lex_two_compat2 lex_two_compat'2;fact)+
qed

lemma lex_two_SN_order_pair:
  assumes o1: "SN_order_pair s1 ns1" and o2: "SN_order_pair s2 ns2"
  shows "SN_order_pair (lex_two s1 ns1 s2) (lex_two s1 ns1 ns2)"
proof -
  interpret o1: SN_order_pair s1 ns1 using o1.
  interpret o2: SN_order_pair s2 ns2 using o2.
  note o1.trans_S o1.trans_NS o2.trans_S o2.trans_NS o1.SN o2.SN
    o1.compat_NS_S o2.compat_NS_S o1.compat_S_NS o2.compat_S_NS
  note this [unfolded trans_O_iff]
  interpret order_pair "(lex_two s1 ns1 s2)" "(lex_two s1 ns1 ns2)"
    by(rule lex_two_order_pair, standard)
  show ?thesis by(standard, rule lex_two; fact)
qed

text \<open>
  In the unbounded lexicographic extension, there is no restriction on the lengths
  of the lists. Therefore it is possible to compare lists of different lengths.
  This usually results a non-terminating relation, e.g., $[1] > [0, 1] > [0, 0, 1] > \ldots$
\<close>

fun lex_ext_unbounded :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  where "lex_ext_unbounded f [] [] = (False, True)" |
    "lex_ext_unbounded f (_ # _) [] = (True, True)" |
    "lex_ext_unbounded f [] (_ # _) = (False, False)" |
    "lex_ext_unbounded f (a # as) (b # bs) =
      (let (stri, nstri) = f a b in
      if stri then (True, True)
      else if nstri then lex_ext_unbounded f as bs
      else (False, False))"

lemma lex_ext_unbounded_iff: "(lex_ext_unbounded f xs ys) = (
  ((\<exists> i < length xs. i < length ys \<and> (\<forall> j < i. snd (f (xs ! j) (ys ! j))) \<and> fst (f (xs ! i) (ys !i))) \<or> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i))) \<and> length xs > length ys),
  ((\<exists> i < length xs. i < length ys \<and> (\<forall> j < i. snd (f (xs ! j) (ys ! j))) \<and> fst (f (xs ! i) (ys !i))) \<or> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i))) \<and> length xs \<ge> length ys))
  " (is "?lex xs ys = (?stri xs ys, ?nstri xs ys)")
proof (induct xs arbitrary: ys)
  case Nil then show ?case by (cases ys, auto)
next
  case (Cons a as)
  note oCons = this
  from oCons show ?case 
  proof (cases ys, simp)
    case (Cons b bs)
    show ?thesis 
    proof (cases "f a b")
      case (Pair stri nstri)
      show ?thesis
      proof (cases stri)
        case True
        with Pair Cons show ?thesis by auto
      next
        case False        
        show ?thesis 
        proof (cases nstri)
          case False
          with \<open>\<not> stri\<close> Pair Cons show ?thesis by force
        next
          case True
          with False Pair have f: "f a b = (False, True)" by auto
          show ?thesis by (simp add: all_Suc_conv ex_Suc_conv Cons f oCons)
        qed
      qed
    qed
  qed
qed

declare lex_ext_unbounded.simps[simp del]

text \<open>
  The lexicographic extension of an order pair takes a natural number as maximum bound.
  A decrease with lists of unequal lengths will never be successful if the length of the
  second list exceeds this bound. The bound is essential to preserve strong normalization.
\<close>
definition lex_ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  where
    "lex_ext f n ss ts =
      (let lts = length ts in 
      if (length ss = lts \<or> lts \<le> n) then lex_ext_unbounded f ss ts
      else (False, False))"

lemma lex_ext_iff: "(lex_ext f m xs ys) = (
  (length xs = length ys \<or> length ys \<le> m) \<and> ((\<exists> i < length xs. i < length ys \<and> (\<forall> j < i. snd (f (xs ! j) (ys ! j))) \<and> fst (f (xs ! i) (ys !i))) \<or> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i))) \<and> length xs > length ys),
  (length xs = length ys \<or> length ys \<le> m) \<and>
  ((\<exists> i < length xs. i < length ys \<and> (\<forall> j < i. snd (f (xs ! j) (ys ! j))) \<and> fst (f (xs ! i) (ys !i))) \<or> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i))) \<and> length xs \<ge> length ys))
  "
  unfolding lex_ext_def
  by (simp only: lex_ext_unbounded_iff Let_def, auto)

lemma lex_ext_to_lex_ext_unbounded: 
  assumes "length xs \<le> n" and "length ys \<le> n"
  shows "lex_ext f n xs ys = lex_ext_unbounded f xs ys"
  using assms by (simp add: lex_ext_def)


lemma lex_ext_stri_imp_nstri: 
  assumes "fst (lex_ext f m xs ys)" 
  shows "snd (lex_ext f m xs ys)"
  using assms by (auto simp: lex_ext_iff)

lemma lex_ext_unbounded_stri_imp_nstri: 
  assumes "fst (lex_ext_unbounded f xs ys)" 
  shows "snd (lex_ext_unbounded f xs ys)"
  using assms by (auto simp: lex_ext_unbounded_iff)

lemma all_nstri_imp_lex_nstri: assumes "\<forall> i < length ys. snd (f (xs ! i) (ys ! i))" and "length xs \<ge> length ys" and "length xs = length ys \<or> length ys \<le> m"
  shows "snd (lex_ext f m xs ys)"
  using assms by (auto simp: lex_ext_iff)


lemma lex_ext_cong[fundef_cong]: fixes f g m1 m2 xs1 xs2 ys1 ys2
  assumes "length xs1 = length ys1" and "m1 = m2" and "length xs2 = length ys2" and "\<And> i. \<lbrakk>i < length ys1; i < length ys2\<rbrakk> \<Longrightarrow> f (xs1 ! i) (xs2 ! i) = g (ys1 ! i) (ys2 ! i)" 
  shows "lex_ext f m1 xs1 xs2 = lex_ext g m2 ys1 ys2"
  using assms by (auto simp: lex_ext_iff)

lemma lex_ext_unbounded_cong[fundef_cong]: assumes "as = as'" and "bs = bs'"
  and "\<And> i. i < length as' \<Longrightarrow> i < length bs' \<Longrightarrow> f (as' ! i) (bs' ! i) = g (as' ! i) (bs' ! i)" shows "lex_ext_unbounded f as bs = lex_ext_unbounded g as' bs'"
  unfolding assms lex_ext_unbounded_iff using assms(3) by auto

text \<open>Compatibility is the key property to ensure transitivity of the order.\<close>

text \<open>
  We prove compatibility locally, i.e., it only has to hold for elements
  of the argument lists. Locality is essential for being applicable in recursively
  defined term orders such as KBO.
\<close>
lemma lex_ext_compat:
  assumes compat: "\<And> s t u. \<lbrakk>s \<in> set ss; t \<in> set ts; u \<in> set us\<rbrakk> \<Longrightarrow>
    (snd (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u)) \<and> 
    (fst (f s t) \<and> snd (f t u) \<longrightarrow> fst (f s u)) \<and> 
    (snd (f s t) \<and> snd (f t u) \<longrightarrow> snd (f s u)) \<and>
    (fst (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u))"
  shows "
    (snd (lex_ext f n ss ts) \<and> fst (lex_ext f n ts us) \<longrightarrow> fst (lex_ext f n ss us)) \<and> 
    (fst (lex_ext f n ss ts) \<and> snd (lex_ext f n ts us) \<longrightarrow> fst (lex_ext f n ss us)) \<and> 
    (snd (lex_ext f n ss ts) \<and> snd (lex_ext f n ts us) \<longrightarrow> snd (lex_ext f n ss us)) \<and>
    (fst (lex_ext f n ss ts) \<and> fst (lex_ext f n ts us) \<longrightarrow> fst (lex_ext f n ss us))
    "
proof -
  let ?ls = "length ss"
  let ?lt = "length ts"
  let ?lu = "length us"
  let ?st = "lex_ext f n ss ts"
  let ?tu = "lex_ext f n ts us"
  let ?su = "lex_ext f n ss us"
  let ?fst = "\<lambda> ss ts i. fst (f (ss ! i) (ts ! i))"
  let ?snd = "\<lambda> ss ts i. snd (f (ss ! i) (ts ! i))"
  let ?ex = "\<lambda> ss ts. \<exists> i < length ss. i < length ts \<and> (\<forall> j < i. ?snd ss ts j) \<and> ?fst ss ts i"
  let ?all = "\<lambda> ss ts. \<forall> i < length ts. ?snd ss ts i"
  have lengths: "(?ls = ?lt \<or> ?lt \<le> n) \<and> (?lt = ?lu \<or> ?lu \<le> n) \<longrightarrow>
    (?ls = ?lu \<or> ?lu \<le> n)" (is "?lst \<and> ?ltu \<longrightarrow> ?lsu") by arith
  {
    assume st: "snd ?st" and tu: "fst ?tu"
    with lengths have lsu: "?lsu" by (simp add: lex_ext_iff)
    from st have st: "?ex ss ts \<or> ?all ss ts \<and> ?lt \<le> ?ls" by (simp add: lex_ext_iff)
    from tu have tu: "?ex ts us \<or> ?all ts us \<and> ?lu < ?lt" by (simp add: lex_ext_iff)
    from st have "fst ?su"
    proof
      assume st: "?ex ss ts"
      then obtain i1 where i1: "i1 < ?ls \<and> i1 < ?lt" and fst1: "?fst ss ts i1" and snd1: "\<forall> j < i1. ?snd ss ts j" by force
      from tu show ?thesis
      proof
        assume tu: "?ex ts us"
        then obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        let ?i = "min i1 i2"
        from i1 i2 have i: "?i < ?ls \<and> ?i < ?lt \<and> ?i < ?lu" by auto
        then have ssi: "ss ! ?i \<in> set ss" and tsi: "ts ! ?i \<in> set ts" and usi: "us ! ?i \<in> set us" by auto
        have snd: "\<forall> j < ?i. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume j: "j < ?i"
          with snd1 snd2 have snd1: "?snd ss ts j" and snd2: "?snd ts us j" by auto
          from j i have ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        have fst: "?fst ss us ?i" 
        proof (cases "i1 < i2")
          case True
          then have "?i = i1" by simp
          with True fst1 snd2 have "?fst ss ts ?i" and "?snd ts us ?i" by auto
          with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
        next
          case False
          show ?thesis 
          proof (cases "i2 < i1")
            case True
            then have "?i = i2" by simp
            with True snd1 fst2 have "?snd ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          next
            case False
            with \<open>\<not> i1 < i2\<close> have "i1 = i2" by simp
            with fst1 fst2 have "?fst ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          qed
        qed
        show ?thesis by (simp add: lex_ext_iff lsu, rule disjI1, rule exI[of _ ?i], simp add: fst snd i)
      next
        assume tu: "?all ts us \<and> ?lu < ?lt"
        show ?thesis
        proof (cases "i1 < ?lu")
          case True
          then have usi: "us ! i1 \<in> set us" by auto
          from i1 have ssi: "ss ! i1 \<in> set ss" and tsi: "ts ! i1 \<in> set ts" by auto
          from True tu have "?snd ts us i1" by auto
          with fst1 compat[OF ssi tsi usi] have fst: "?fst ss us i1" by auto
          have snd: "\<forall> j < i1. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < i1"
            with i1 True snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with fst lsu True i1 show ?thesis by (auto simp: lex_ext_iff) 
        next
          case False
          with i1 have lus: "?lu < ?ls" by auto
          have snd: "\<forall> j < ?lu. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < ?lu"
            with False i1 snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with lus lsu show ?thesis by (auto simp: lex_ext_iff)
        qed
      qed
    next
      assume st: "?all ss ts \<and> ?lt \<le> ?ls"
      from tu
      show ?thesis
      proof
        assume tu: "?ex ts us"
        with st obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        from st i2 have i2: "i2 < ?ls \<and> i2 < ?lt \<and> i2 < ?lu" by auto
        then have ssi: "ss ! i2 \<in> set ss" and tsi: "ts ! i2 \<in> set ts" and usi: "us ! i2 \<in> set us" by auto
        from i2 st have "?snd ss ts i2" by auto
        with fst2 compat[OF ssi tsi usi] have fst: "?fst ss us i2" by auto
        have snd: "\<forall> j < i2. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < i2"
          with i2 snd2 st have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with fst lsu i2 show ?thesis by (auto simp: lex_ext_iff)
      next
        assume tu: "?all ts us \<and> ?lu < ?lt"
        with st have lus: "?lu < ?ls" by auto
        have snd: "\<forall> j < ?lu. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < ?lu"
          with st tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with lus lsu show ?thesis by (auto simp: lex_ext_iff)
      qed
    qed
  }
  moreover
  {
    assume st: "fst ?st" and tu: "snd ?tu"
    with lengths have lsu: "?lsu" by (simp add: lex_ext_iff)
    from st have st: "?ex ss ts \<or> ?all ss ts \<and> ?lt < ?ls" by (simp add: lex_ext_iff)
    from tu have tu: "?ex ts us \<or> ?all ts us \<and> ?lu \<le> ?lt" by (simp add: lex_ext_iff)
    from st have "fst ?su"
    proof
      assume st: "?ex ss ts"
      then obtain i1 where i1: "i1 < ?ls \<and> i1 < ?lt" and fst1: "?fst ss ts i1" and snd1: "\<forall> j < i1. ?snd ss ts j" by force
      from tu show ?thesis
      proof
        assume tu: "?ex ts us"
        then obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        let ?i = "min i1 i2"
        from i1 i2 have i: "?i < ?ls \<and> ?i < ?lt \<and> ?i < ?lu" by auto
        then have ssi: "ss ! ?i \<in> set ss" and tsi: "ts ! ?i \<in> set ts" and usi: "us ! ?i \<in> set us" by auto
        have snd: "\<forall> j < ?i. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume j: "j < ?i"
          with snd1 snd2 have snd1: "?snd ss ts j" and snd2: "?snd ts us j" by auto
          from j i have ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        have fst: "?fst ss us ?i" 
        proof (cases "i1 < i2")
          case True
          then have "?i = i1" by simp
          with True fst1 snd2 have "?fst ss ts ?i" and "?snd ts us ?i" by auto
          with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
        next
          case False
          show ?thesis 
          proof (cases "i2 < i1")
            case True
            then have "?i = i2" by simp
            with True snd1 fst2 have "?snd ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          next
            case False
            with \<open>\<not> i1 < i2\<close> have "i1 = i2" by simp
            with fst1 fst2 have "?fst ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          qed
        qed
        show ?thesis by (simp add: lex_ext_iff lsu, rule disjI1, rule exI[of _ ?i], simp add: fst snd i)
      next
        assume tu: "?all ts us \<and> ?lu \<le> ?lt"
        show ?thesis
        proof (cases "i1 < ?lu")
          case True
          then have usi: "us ! i1 \<in> set us" by auto
          from i1 have ssi: "ss ! i1 \<in> set ss" and tsi: "ts ! i1 \<in> set ts" by auto
          from True tu have "?snd ts us i1" by auto
          with fst1 compat[OF ssi tsi usi] have fst: "?fst ss us i1" by auto
          have snd: "\<forall> j < i1. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < i1"
            with i1 True snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with fst lsu True i1 show ?thesis by (auto simp: lex_ext_iff) 
        next
          case False
          with i1 have lus: "?lu < ?ls" by auto
          have snd: "\<forall> j < ?lu. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < ?lu"
            with False i1 snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with lus lsu show ?thesis by (auto simp: lex_ext_iff)
        qed
      qed
    next
      assume st: "?all ss ts \<and> ?lt < ?ls"
      from tu
      show ?thesis
      proof
        assume tu: "?ex ts us"
        with st obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        from st i2 have i2: "i2 < ?ls \<and> i2 < ?lt \<and> i2 < ?lu" by auto
        then have ssi: "ss ! i2 \<in> set ss" and tsi: "ts ! i2 \<in> set ts" and usi: "us ! i2 \<in> set us" by auto
        from i2 st have "?snd ss ts i2" by auto
        with fst2 compat[OF ssi tsi usi] have fst: "?fst ss us i2" by auto
        have snd: "\<forall> j < i2. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < i2"
          with i2 snd2 st have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with fst lsu i2 show ?thesis by (auto simp: lex_ext_iff)
      next
        assume tu: "?all ts us \<and> ?lu \<le> ?lt"
        with st have lus: "?lu < ?ls" by auto
        have snd: "\<forall> j < ?lu. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < ?lu"
          with st tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with lus lsu show ?thesis by (auto simp: lex_ext_iff)
      qed
    qed
  }
  moreover
  {
    assume st: "snd ?st" and tu: "snd ?tu"
    with lengths have lsu: "?lsu" by (simp add: lex_ext_iff)
    from st have st: "?ex ss ts \<or> ?all ss ts \<and> ?lt \<le> ?ls" by (simp add: lex_ext_iff)
    from tu have tu: "?ex ts us \<or> ?all ts us \<and> ?lu \<le> ?lt" by (simp add: lex_ext_iff)
    from st have "snd ?su"
    proof
      assume st: "?ex ss ts"
      then obtain i1 where i1: "i1 < ?ls \<and> i1 < ?lt" and fst1: "?fst ss ts i1" and snd1: "\<forall> j < i1. ?snd ss ts j" by force
      from tu show ?thesis
      proof
        assume tu: "?ex ts us"
        then obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        let ?i = "min i1 i2"
        from i1 i2 have i: "?i < ?ls \<and> ?i < ?lt \<and> ?i < ?lu" by auto
        then have ssi: "ss ! ?i \<in> set ss" and tsi: "ts ! ?i \<in> set ts" and usi: "us ! ?i \<in> set us" by auto
        have snd: "\<forall> j < ?i. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume j: "j < ?i"
          with snd1 snd2 have snd1: "?snd ss ts j" and snd2: "?snd ts us j" by auto
          from j i have ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        have fst: "?fst ss us ?i" 
        proof (cases "i1 < i2")
          case True
          then have "?i = i1" by simp
          with True fst1 snd2 have "?fst ss ts ?i" and "?snd ts us ?i" by auto
          with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
        next
          case False
          show ?thesis 
          proof (cases "i2 < i1")
            case True
            then have "?i = i2" by simp
            with True snd1 fst2 have "?snd ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          next
            case False
            with \<open>\<not> i1 < i2\<close> have "i1 = i2" by simp
            with fst1 fst2 have "?fst ss ts ?i" and "?fst ts us ?i" by auto
            with compat[OF ssi tsi usi] show "?fst ss us ?i" by auto
          qed
        qed
        show ?thesis by (simp add: lex_ext_iff lsu, rule disjI1, rule exI[of _ ?i], simp add: fst snd i)
      next
        assume tu: "?all ts us \<and> ?lu \<le> ?lt"
        show ?thesis
        proof (cases "i1 < ?lu")
          case True
          then have usi: "us ! i1 \<in> set us" by auto
          from i1 have ssi: "ss ! i1 \<in> set ss" and tsi: "ts ! i1 \<in> set ts" by auto
          from True tu have "?snd ts us i1" by auto
          with fst1 compat[OF ssi tsi usi] have fst: "?fst ss us i1" by auto
          have snd: "\<forall> j < i1. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < i1"
            with i1 True snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with fst lsu True i1 show ?thesis by (auto simp: lex_ext_iff) 
        next
          case False
          with i1 have lus: "?lu \<le> ?ls" by auto
          have snd: "\<forall> j < ?lu. ?snd ss us j"
          proof (intro allI impI)
            fix j
            assume "j < ?lu"
            with False i1 snd1 tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
              ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
            from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
          qed
          with lus lsu show ?thesis by (auto simp: lex_ext_iff)
        qed
      qed
    next
      assume st: "?all ss ts \<and> ?lt \<le> ?ls"
      from tu
      show ?thesis
      proof
        assume tu: "?ex ts us"
        with st obtain i2 where i2: "i2 < ?lt \<and> i2 < ?lu" and fst2: "?fst ts us i2" and snd2: "\<forall> j < i2. ?snd ts us j" by auto
        from st i2 have i2: "i2 < ?ls \<and> i2 < ?lt \<and> i2 < ?lu" by auto
        then have ssi: "ss ! i2 \<in> set ss" and tsi: "ts ! i2 \<in> set ts" and usi: "us ! i2 \<in> set us" by auto
        from i2 st have "?snd ss ts i2" by auto
        with fst2 compat[OF ssi tsi usi] have fst: "?fst ss us i2" by auto
        have snd: "\<forall> j < i2. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < i2"
          with i2 snd2 st have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with fst lsu i2 show ?thesis by (auto simp: lex_ext_iff)
      next
        assume tu: "?all ts us \<and> ?lu \<le> ?lt"
        with st have lus: "?lu \<le> ?ls" by auto
        have snd: "\<forall> j < ?lu. ?snd ss us j"
        proof (intro allI impI)
          fix j
          assume "j < ?lu"
          with st tu have snd1: "?snd ss ts j" and snd2: "?snd ts us j" and 
            ssj: "ss ! j \<in> set ss" and tsj: "ts ! j \<in> set ts" and usj: "us ! j \<in> set us" by auto
          from compat[OF ssj tsj usj] snd1 snd2 show "?snd ss us j" by auto
        qed
        with lus lsu show ?thesis by (auto simp: lex_ext_iff)
      qed
    qed
  }
  ultimately
  show ?thesis using lex_ext_stri_imp_nstri by blast
qed

lemma lex_ext_unbounded_map:
  assumes S: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> fst (r (ss ! i) (ts ! i)) \<Longrightarrow> fst (r (map f ss ! i) (map f ts ! i))"
    and NS: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> snd (r (ss ! i) (ts ! i)) \<Longrightarrow> snd (r (map f ss ! i) (map f ts ! i))"
  shows "(fst (lex_ext_unbounded r ss ts) \<longrightarrow> fst (lex_ext_unbounded r (map f ss) (map f ts))) \<and>
    (snd (lex_ext_unbounded r ss ts) \<longrightarrow> snd (lex_ext_unbounded r (map f ss) (map f ts)))"
  using S NS unfolding lex_ext_unbounded_iff by auto

lemma lex_ext_unbounded_map_S:
  assumes S: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> fst (r (ss ! i) (ts ! i)) \<Longrightarrow> fst (r (map f ss ! i) (map f ts ! i))"
    and NS: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> snd (r (ss ! i) (ts ! i)) \<Longrightarrow> snd (r (map f ss ! i) (map f ts ! i))"
    and stri: "fst (lex_ext_unbounded r ss ts)"
  shows "fst (lex_ext_unbounded r (map f ss) (map f ts))"
  using lex_ext_unbounded_map[of ss ts r f, OF S NS] stri by blast

lemma lex_ext_unbounded_map_NS:
  assumes S: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> fst (r (ss ! i) (ts ! i)) \<Longrightarrow> fst (r (map f ss ! i) (map f ts ! i))"
    and NS: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> snd (r (ss ! i) (ts ! i)) \<Longrightarrow> snd (r (map f ss ! i) (map f ts ! i))"
    and nstri: "snd (lex_ext_unbounded r ss ts)"
  shows "snd (lex_ext_unbounded r (map f ss) (map f ts))"
  using lex_ext_unbounded_map[of ss ts r f, OF S NS] nstri by blast

text \<open>Strong normalization with local SN assumption\<close>
lemma lex_ext_SN:
  assumes compat: "\<And> x y z. \<lbrakk>snd (g x y); fst (g y z)\<rbrakk> \<Longrightarrow> fst (g x z)"
  shows "SN { (ys, xs). (\<forall> y \<in> set ys. SN_on { (s, t). fst (g s t) } {y}) \<and> fst (lex_ext g m ys xs) }" 
    (is "SN { (ys, xs). ?cond ys xs }")
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this obtain f where f: "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by auto
  have m_imp_m: "\<And> n. length (f n) \<le> m \<Longrightarrow> length (f (Suc n)) \<le> m"
  proof -
    fix n
    assume "length (f n) \<le> m"
    then show "length (f (Suc n)) \<le> m"
      using f[of n] by (auto simp: lex_ext_iff)
  qed
  have lm_imp_m_or_eq: "\<And> n. length (f n) > m \<Longrightarrow> length (f (Suc n)) \<le> m \<or> length (f n) = length (f (Suc n))"
  proof -
    fix n
    assume "length (f n) > m"
    then have "\<not> length (f n) \<le> m" by auto
    then show "length (f (Suc n)) \<le> m \<or> length (f n) = length (f (Suc n))"
      using f[of n] by (simp add: lex_ext_iff, blast)
  qed
  let ?l0 = "max (length (f 0)) m"
  have "\<And> n. length (f n) \<le> ?l0"
  proof -
    fix n
    show "length (f n) \<le> ?l0"
    proof (induct n, simp)
      case (Suc n)
      show ?case
      proof (cases "length (f n) \<le> m")
        case True
        with m_imp_m[of n] show ?thesis by auto
      next
        case False
        then have "length (f n) > m" by auto
        with lm_imp_m_or_eq[of n] 
        have "length (f n) = length (f (Suc n)) \<or> length (f (Suc n)) \<le> m" by auto
        with Suc show ?thesis by auto
      qed
    qed
  qed
  from this obtain m' where len: "\<And> n. length (f n) \<le> m'" by auto
  let ?lexgr = "\<lambda> ys xs. fst (lex_ext g m ys xs)"
  let ?lexge = "\<lambda> ys xs. snd (lex_ext g m ys xs)"
  let ?gr = "\<lambda> t s. fst (g t s)"
  let ?ge = "\<lambda> t s. snd (g t s)"
  let ?S = "{ (y, x). fst (g y x) }"
  let ?NS = "{ (y, x). snd (g y x) }"
  let ?baseSN = "\<lambda> ys. \<forall> y \<in> set ys. SN_on ?S {y}"
  let ?con = "\<lambda> ys xs m'. ?baseSN ys \<and> length ys \<le> m' \<and> ?lexgr ys xs"
  let ?confn = "\<lambda> m' f n . ?con (f n) (f (Suc n)) m'"
  from compat have compat2: "?NS O ?S \<subseteq> ?S" by auto
  from f len have  "\<exists> f. \<forall> n. ?confn m' f n" by auto
  then show False
  proof (induct m')
    case 0
    from this obtain f where "?confn 0 f 0" by auto	
    then have "?lexgr [] (f (Suc 0))" by force
    then show False by (simp add: lex_ext_iff)
  next
    case (Suc m')
    from this obtain f where confn: "\<And> n. ?confn (Suc m') f n" by auto
    have ne: "\<And> n. f n \<noteq> []"
    proof -
      fix n
      show "f n \<noteq> []"
      proof (cases "f n")
        case (Cons a b) then show ?thesis by auto
      next
        case Nil
        with confn[of n] show ?thesis by (simp add: lex_ext_iff)
      qed
    qed
    let ?hf = "\<lambda> n. hd (f n)"
    have ge: "\<And> n. ?ge (?hf n) (?hf (Suc n)) \<or> ?gr (?hf n) (?hf (Suc n))"
    proof -
      fix n
      from ne[of n] obtain a as where n: "f n = a # as" by (cases "f n", auto)
      from ne[of "Suc n"] obtain b bs where sn: "f (Suc n) = b # bs" by (cases "f (Suc n)", auto)
      from n sn have "?ge a b \<or> ?gr a b" 
      proof (cases "?gr a b", simp, cases "?ge a b", simp)
        assume "\<not> ?gr a b" and "\<not> ?ge a b" 
        then have g: "g a b = (False, False)" by (cases "g a b", auto)
        from confn[of n] have "fst (lex_ext g m (f n) (f (Suc n)))" (is ?fst) by simp
        have "?fst = False" by (simp add: n sn lex_ext_def g lex_ext_unbounded.simps)
        with \<open>?fst\<close> show "?ge a b \<or> ?gr a b" by simp
      qed
      with n sn show "?ge (?hf n) (?hf (Suc n)) \<or> ?gr (?hf n) (?hf (Suc n))" by simp
    qed
    from ge have GE: "\<forall> n. (?hf n, ?hf (Suc n)) \<in> ?NS \<union> ?S" by auto
    from confn[of 0] ne[of 0] have SN_0: "SN_on ?S {?hf 0}" by (cases "f 0", auto )
    from non_strict_ending[of ?hf, OF GE compat2 SN_0]
    obtain j where j: "\<forall> i \<ge> j. (?hf i, ?hf (Suc i)) \<in> ?NS - ?S" by auto
    let ?h = "\<lambda> n. tl (f (j + n))"
    obtain h where h: "h = ?h"  by auto
    have "\<And> n. ?confn m' h n" 
    proof -
      fix n
      let ?nj = "j + n"
      from spec[OF j, of ?nj]
      have ge_not_gr: "(?hf ?nj, ?hf (Suc ?nj)) \<in> ?NS - ?S" by simp
      from confn[of ?nj] have old: "?confn (Suc m') f ?nj" by simp
      from ne[of ?nj] obtain a as where n: "f ?nj = a # as" by (cases "f ?nj", auto)
      from ne[of "Suc ?nj"] obtain b bs where sn: "f (Suc ?nj) = b # bs" by (cases "f (Suc ?nj)", auto)
      from old have one: "\<forall> y \<in> set (h n). SN_on ?S {y}" 
        by (simp add: h n)
      from old have two: "length (h n) \<le> m'" by (simp add: j n h)
      from ge_not_gr have ge_not_gr2: "g a b = (False, True)"  by (simp add: n sn, cases "g a b", auto)
      from old have "fst (lex_ext g m (f (j+ n)) (f (Suc (j+n))))" (is ?fst) by simp
      then have "length as = length bs \<or> length bs \<le> m" (is ?len)
        by (simp add: lex_ext_def n sn, cases ?len, auto)
      from \<open>?fst\<close>[simplified n sn] have "fst (lex_ext_unbounded g as bs)" (is ?fst)
        by (simp add: lex_ext_def, cases "length as = length bs \<or> Suc (length bs) \<le> m", simp_all add: ge_not_gr2 lex_ext_unbounded.simps)
      then have "fst (lex_ext_unbounded g as bs)" (is ?fst)
        by (simp add: lex_ext_unbounded_iff)
      have three: "?lexgr (h n) (h (Suc n))"
        by (simp add: lex_ext_def h n sn ge_not_gr2 lex_ext_unbounded.simps, simp only: Let_def, simp add: \<open>?len\<close> \<open>?fst\<close>)
      from one two three show "?confn m' h n" by blast
    qed
    with Suc show ?thesis by blast
  qed
qed

text \<open>Strong normalization with global SN assumption is immediate consequence.\<close>
lemma lex_ext_SN_2:
  assumes compat: "\<And> x y z. \<lbrakk>snd (g x y); fst (g y z)\<rbrakk> \<Longrightarrow> fst (g x z)"
    and SN:  "SN {(s, t). fst (g s t)}"
  shows "SN { (ys, xs). fst (lex_ext g m ys xs) }" 
proof -
  from lex_ext_SN[OF compat] 
  have "SN { (ys, xs). (\<forall> y \<in> set ys. SN_on { (s, t). fst (g s t) } {y}) \<and> fst (lex_ext g m ys xs) }" .
  then show ?thesis using SN unfolding SN_on_def by fastforce
qed

text \<open>The empty list is the least element in the lexicographic extension.\<close>
lemma lex_ext_least_1: "snd (lex_ext f m xs [])"
  by (simp add: lex_ext_iff)

lemma lex_ext_least_2: "\<not> fst (lex_ext f m [] ys)"
  by (simp add: lex_ext_iff)

text \<open>Preservation of totality on lists of same length.\<close>
lemma lex_ext_unbounded_total:
  assumes "\<forall>(s, t)\<in>set (zip ss ts). s = t \<or> fst (f s t) \<or> fst (f t s)" 
    and refl: "\<And> t. snd (f t t)" 
    and "length ss = length ts" 
  shows "ss = ts \<or> fst (lex_ext_unbounded f ss ts) \<or> fst (lex_ext_unbounded f ts ss)" 
  using assms(3, 1)
proof (induct ss ts rule: list_induct2)
  case (Cons s ss t ts)
  from Cons(3) have "s = t \<or> (fst (f s t) \<or> fst (f t s))" by auto
  then show ?case
  proof 
    assume st: "s = t" 
    then show ?thesis using Cons(2-3) refl[of t] by (cases "f t t", auto simp: lex_ext_unbounded.simps)
  qed (auto simp: lex_ext_unbounded.simps split: prod.splits)
qed simp

lemma lex_ext_total:
  assumes "\<forall>(s, t)\<in>set (zip ss ts). s = t \<or> fst (f s t) \<or> fst (f t s)" 
    and "\<And> t. snd (f t t)" 
    and len: "length ss = length ts" 
  shows "ss = ts \<or> fst (lex_ext f n ss ts) \<or> fst (lex_ext f n ts ss)" 
  using lex_ext_unbounded_total[OF assms] unfolding lex_ext_def Let_def len by auto

text \<open>Monotonicity of the lexicographic extension.\<close>
lemma lex_ext_unbounded_mono:
  assumes "\<And>i. \<lbrakk>i < length xs; i < length ys; fst (P (xs ! i) (ys ! i))\<rbrakk> \<Longrightarrow> fst (P' (xs ! i) (ys ! i))"
    and   "\<And>i. \<lbrakk>i < length xs; i < length ys; snd (P (xs ! i) (ys ! i))\<rbrakk> \<Longrightarrow> snd (P' (xs ! i) (ys ! i))"
  shows
    "(fst (lex_ext_unbounded P xs ys) \<longrightarrow> fst (lex_ext_unbounded P' xs ys)) \<and>
     (snd (lex_ext_unbounded P xs ys) \<longrightarrow> snd (lex_ext_unbounded P' xs ys))"
    (is "(?l1 xs ys \<longrightarrow> ?r1 xs ys) \<and> (?l2 xs ys \<longrightarrow> ?r2 xs ys)")
  using assms
proof (induct x\<equiv>P xs ys rule: lex_ext_unbounded.induct)
  note [simp] = lex_ext_unbounded.simps
  case (4 x xs y ys)
  consider (TT) "P x y = (True, True)"
    | (TF) "P x y = (True, False)"
    | (FT) "P x y = (False, True)"
    | (FF) "P x y = (False, False)" by (cases "P x y", auto)
  thus ?case
  proof cases
    case TT
    moreover
    with 4(2) [of 0] and 4(3) [of 0]
    have "P' x y = (True, True)"
      by (auto) (metis (full_types) prod.collapse)
    ultimately
    show ?thesis by simp
  next
    case TF
    show ?thesis
    proof (cases "snd (P' x y)")
      case False
      moreover
      with 4(2) [of 0] and TF
      have "P' x y = (True, False)"
        by (cases "P' x y", auto) 
      ultimately
      show ?thesis by simp
    next
      case True
      with 4(2) [of 0] and TF
      have "P' x y = (True, True)"
        by (auto )(metis (full_types) fst_conv snd_conv surj_pair)
      then show ?thesis by simp
    qed
  next
    case FF then show ?thesis by simp
  next
    case FT
    show ?thesis
    proof (cases "fst (P' x y)")
      case True
      with 4(3) [of 0] and FT
      have *: "P' x y = (True, True)"
        by (auto) (metis (full_types) prod.collapse)
      have "?l1 (x#xs) (y#ys) \<longrightarrow> ?r1 (x#xs) (y#ys)"
        by (simp add: FT *)
      moreover
      have "?l2 (x#xs) (y#ys) \<longrightarrow> ?r2 (x#xs) (y#ys)"
        by (simp add: *)
      ultimately show ?thesis by blast
    next
      case False
      with 4(3) [of 0] and FT
      have *: "P' x y = (False, True)"
        by (cases "P' x y", auto)
      show ?thesis
        using 4(1) [OF refl FT [symmetric]] and 4(2) and 4(3)
        using FT *
        by (auto) (metis Suc_less_eq nth_Cons_Suc)+
    qed
  qed
qed (simp add: lex_ext_unbounded.simps)+

end
