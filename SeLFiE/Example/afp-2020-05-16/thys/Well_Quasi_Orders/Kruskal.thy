(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Kruskal's Tree Theorem\<close>

theory Kruskal
imports Well_Quasi_Orders
begin

locale kruskal_tree =
  fixes F :: "('b \<times> nat) set"
    and mk :: "'b \<Rightarrow> 'a list \<Rightarrow> ('a::size)"
    and root :: "'a \<Rightarrow> 'b \<times> nat"
    and args :: "'a \<Rightarrow> 'a list"
    and trees :: "'a set"
  assumes size_arg: "t \<in> trees \<Longrightarrow> s \<in> set (args t) \<Longrightarrow> size s < size t"
    and root_mk: "(f, length ts) \<in> F \<Longrightarrow> root (mk f ts) = (f, length ts)"
    and args_mk: "(f, length ts) \<in> F \<Longrightarrow> args (mk f ts) = ts"
    and mk_root_args: "t \<in> trees \<Longrightarrow> mk (fst (root t)) (args t) = t"
    and trees_root: "t \<in> trees \<Longrightarrow> root t \<in> F"
    and trees_arity: "t \<in> trees \<Longrightarrow> length (args t) = snd (root t)"
    and trees_args: "\<And>s. t \<in> trees \<Longrightarrow> s \<in> set (args t) \<Longrightarrow> s \<in> trees"
begin

lemma mk_inject [iff]:
  assumes "(f, length ss) \<in> F" and "(g, length ts) \<in> F"
  shows "mk f ss = mk g ts \<longleftrightarrow> f = g \<and> ss = ts"
proof -
  { assume "mk f ss = mk g ts"
    then have "root (mk f ss) = root (mk g ts)"
      and "args (mk f ss) = args (mk g ts)" by auto }
  show ?thesis
    using root_mk [OF assms(1)] and root_mk [OF assms(2)]
      and args_mk [OF assms(1)] and args_mk [OF assms(2)] by auto
qed

inductive emb for P
where
  arg: "\<lbrakk>(f, m) \<in> F; length ts = m; \<forall>t\<in>set ts. t \<in> trees;
    t \<in> set ts; emb P s t\<rbrakk> \<Longrightarrow> emb P s (mk f ts)" |
  list_emb: "\<lbrakk>(f, m) \<in> F; (g, n) \<in> F; length ss = m; length ts = n;
    \<forall>s \<in> set ss. s \<in> trees; \<forall>t \<in> set ts. t \<in> trees;
    P (f, m) (g, n); list_emb (emb P) ss ts\<rbrakk> \<Longrightarrow> emb P (mk f ss) (mk g ts)"
  monos list_emb_mono

lemma almost_full_on_trees:
  assumes "almost_full_on P F"
  shows "almost_full_on (emb P) trees" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret mbs ?A .
  assume "\<not> ?thesis"
  from mbs' [OF this] obtain m
    where bad: "m \<in> BAD ?P"
    and min: "\<forall>g. (m, g) \<in> gseq \<longrightarrow> good ?P g" ..
  then have trees: "\<And>i. m i \<in> trees" by auto

  define r where "r i = root (m i)" for i
  define a where "a i = args (m i)" for i
  define S where "S = \<Union>{set (a i) | i. True}"

  have m: "\<And>i. m i = mk (fst (r i)) (a i)"
   by (simp add: r_def a_def mk_root_args [OF trees])
  have lists: "\<forall>i. a i \<in> lists S" by (auto simp: a_def S_def)
  have arity: "\<And>i. length (a i) = snd (r i)"
    using trees_arity [OF trees] by (auto simp: r_def a_def)
  then have sig: "\<And>i. (fst (r i), length (a i)) \<in> F"
    using trees_root [OF trees] by (auto simp: a_def r_def)
  have a_trees: "\<And>i. \<forall>t \<in> set (a i). t \<in> trees" by (auto simp: a_def trees_args [OF trees])

  have "almost_full_on ?P S"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain s :: "nat \<Rightarrow> 'a"
      where S: "\<And>i. s i \<in> S" and bad_s: "bad ?P s" by (auto simp: almost_full_on_def)

    define n where "n = (LEAST n. \<exists>k. s k \<in> set (a n))"
    have "\<exists>n. \<exists>k. s k \<in> set (a n)" using S by (force simp: S_def)
    from LeastI_ex [OF this] obtain k
      where sk: "s k \<in> set (a n)" by (auto simp: n_def)
    have args: "\<And>k. \<exists>m \<ge> n. s k \<in> set (a m)"
      using S by (auto simp: S_def) (metis Least_le n_def)

    define m' where "m' i = (if i < n then m i else s (k + (i - n)))" for i
    
    have m'_less: "\<And>i. i < n \<Longrightarrow> m' i = m i" by (simp add: m'_def)
    have m'_geq: "\<And>i. i \<ge> n \<Longrightarrow> m' i = s (k + (i - n))" by (simp add: m'_def)

    have "bad ?P m'"
    proof
      assume "good ?P m'"
      then obtain i j where "i < j" and emb: "?P (m' i) (m' j)" by auto
      { assume "j < n"
        with \<open>i < j\<close> and emb have "?P (m i) (m j)" by (auto simp: m'_less)
        with \<open>i < j\<close> and bad have False by blast }
      moreover
      { assume "n \<le> i"
        with \<open>i < j\<close> and emb have "?P (s (k + (i - n))) (s (k + (j - n)))"
          and "k + (i - n) < k + (j - n)" by (auto simp: m'_geq)
        with bad_s have False by auto }
      moreover
      { assume "i < n" and "n \<le> j"
        with \<open>i < j\<close> and emb have *: "?P (m i) (s (k + (j - n)))" by (auto simp: m'_less m'_geq)
        with args obtain l where "l \<ge> n" and **: "s (k + (j - n)) \<in> set (a l)" by blast
        from emb.arg [OF sig [of l] _ a_trees [of l] ** *]
          have "?P (m i) (m l)" by (simp add: m)
        moreover have "i < l" using \<open>i < n\<close> and \<open>n \<le> l\<close> by auto
        ultimately have False using bad by blast }
      ultimately show False using \<open>i < j\<close> by arith
    qed
    moreover have "(m, m') \<in> gseq"
    proof -
      have "m \<in> SEQ ?A" using trees by auto
      moreover have "m' \<in> SEQ ?A"
        using trees and S and trees_args [OF trees] by (auto simp: m'_def a_def S_def)
      moreover have "\<forall>i < n. m i = m' i" by (auto simp: m'_less)
      moreover have "size (m' n) < size (m n)"
        using sk and size_arg [OF trees, unfolded m]
        by (auto simp: m m'_geq root_mk [OF sig] args_mk [OF sig])
      ultimately show ?thesis by (auto simp: gseq_def)
    qed
    ultimately show False using min by blast
  qed
  from almost_full_on_lists [OF this, THEN almost_full_on_imp_homogeneous_subseq, OF lists]
    obtain \<phi> :: "nat \<Rightarrow> nat"
    where less: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
      and lemb: "\<And>i j. i < j \<Longrightarrow> list_emb ?P (a (\<phi> i)) (a (\<phi> j))" by blast
  have roots: "\<And>i. r (\<phi> i) \<in> F" using trees [THEN trees_root] by (auto simp: r_def)
  then have "r \<circ> \<phi> \<in> SEQ F" by auto
  with assms have "good P (r \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j
    where "i < j" and "P (r (\<phi> i)) (r (\<phi> j))" by auto
  with lemb [OF \<open>i < j\<close>] have "?P (m (\<phi> i)) (m (\<phi> j))"
    using sig and arity and a_trees by (auto simp: m intro!: emb.list_emb)
  with less [OF \<open>i < j\<close>] and bad show False by blast
qed

inductive_cases
  emb_mk2 [consumes 1, case_names arg list_emb]: "emb P s (mk g ts)"

inductive_cases
  list_emb_Nil2_cases: "list_emb P xs []" and
  list_emb_Cons_cases: "list_emb P xs (y#ys)"

lemma list_emb_trans_right:
  assumes "list_emb P xs ys" and "list_emb (\<lambda>y z. P y z \<and> (\<forall>x. P x y \<longrightarrow> P x z)) ys zs" 
  shows "list_emb P xs zs"
  using assms(2, 1) by (induct arbitrary: xs) (auto elim!: list_emb_Nil2_cases list_emb_Cons_cases)

lemma emb_trans:
  assumes trans: "\<And>f g h. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> h \<in> F \<Longrightarrow> P f g \<Longrightarrow> P g h \<Longrightarrow> P f h"
  assumes "emb P s t" and "emb P t u"
  shows "emb P s u"
using assms(3, 2)
proof (induct arbitrary: s)
  case (arg f m ts v)
  then show ?case by (auto intro: emb.arg)
next
  case (list_emb f m g n ss ts)
  note IH = this
  from \<open>emb P s (mk f ss)\<close>
    show ?case
  proof (cases rule: emb_mk2)
    case arg
    then show ?thesis using IH by (auto elim!: list_emb_set intro: emb.arg)
  next
    case list_emb
    then show ?thesis using IH by (auto intro: emb.intros dest: trans list_emb_trans_right)
  qed
qed

lemma transp_on_emb:
  assumes "transp_on P F"
  shows "transp_on (emb P) trees"
  using assms and emb_trans [of P] unfolding transp_on_def by blast

lemma kruskal:
  assumes "wqo_on P F"
  shows "wqo_on (emb P) trees"
  using almost_full_on_trees [of P] and assms by (metis transp_on_emb wqo_on_def)

end

end

