subsection "Splay Tree Analysis"

theory Splay_Tree_Analysis
imports
  Splay_Tree_Analysis_Base
  Amortized_Framework
begin

subsubsection "Analysis of splay"

definition a_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"a_splay a t = t_splay a t + \<Phi>(splay a t) - \<Phi> t"

lemma a_splay_simps[simp]: "a_splay a (Node l a r) = 1"
 "a<b \<Longrightarrow> a_splay a (Node (Node ll a lr) b r) = \<phi> (Node lr b r) - \<phi> (Node ll a lr) + 1"
 "b<a \<Longrightarrow> a_splay a (Node l b (Node rl a rr)) = \<phi> (Node rl b l) - \<phi> (Node rl a rr) + 1"
by(auto simp add: a_splay_def algebra_simps)

text\<open>The following lemma is an attempt to prove a generic lemma that covers
both zig-zig cases. However, the lemma is not as nice as one would like.
Hence it is used only once, as a demo. Ideally the lemma would involve
function @{const a_splay}, but that is impossible because this involves @{const splay}
and thus depends on the ordering. We would need a truly symmetric version of @{const splay}
that takes the ordering as an explicit argument. Then we could define
all the symmetric cases by one final equation
@{term"splay2 less t = splay2 (not o less) (mirror t)"}.
This would simplify the code and the proofs.\<close>

lemma zig_zig: fixes lx x rx lb b rb a ra u lb1 lb2
defines [simp]: "X == Node lx (x) rx" defines[simp]: "B == Node lb b rb"
defines [simp]: "t == Node B a ra" defines [simp]: "A' == Node rb a ra"
defines [simp]: "t' == Node lb1 u (Node lb2 b A')"
assumes hyps: "lb \<noteq> \<langle>\<rangle>" and IH: "t_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb \<le> 2 * \<phi> lb - 3 * \<phi> X + 1" and
 prems: "size lb = size lb1 + size lb2 + 1" "X \<in> subtrees lb"
shows "t_splay x lb + \<Phi> t' - \<Phi> t \<le> 3 * (\<phi> t - \<phi> X)"
proof -
  define B' where [simp]: "B' = Node lb2 b A'"
  have "t_splay x lb + \<Phi> t' - \<Phi> t = t_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb + \<phi> B' + \<phi> A' - \<phi> B"
    using prems
    by(auto simp: a_splay_def size_if_splay algebra_simps in_set_tree_if split: tree.split)
  also have "\<dots> \<le> 2 * \<phi> lb + \<phi> B' + \<phi> A' - \<phi> B - 3 * \<phi> X + 1"
    using IH prems(2) by(auto simp: algebra_simps)
  also have "\<dots> \<le> \<phi> lb + \<phi> B' + \<phi> A' - 3 * \<phi> X + 1" by(simp)
  also have "\<dots> \<le> \<phi> B' + 2 * \<phi> t - 3 * \<phi> X "
    using prems ld_ld_1_less[of "size1 lb" "size1 A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> t - 3 * \<phi> X"
    using prems by(simp add: size_if_splay)
  finally show ?thesis by simp
qed

lemma a_splay_ub: "\<lbrakk> bst t; Node lx x rx : subtrees t \<rbrakk>
  \<Longrightarrow> a_splay x t \<le> 3 * (\<phi> t - \<phi>(Node lx x rx)) + 1"
proof(induction x t rule: splay.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by auto
next
  case 4 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 5 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 7 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 10 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 12 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 13 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case (3 b a lb rb ra)
  let ?A = "Node (Node lb b rb) a ra"
  have "b \<notin> set_tree ra" using "3.prems"(1) by auto
  with 3 show ?case using
    log_le_cancel_iff[of 2 "size1(Node rb a ra)" "size1 ?A"]
    log_le_cancel_iff[of 2 "size1(Node lb b rb)" "size1 ?A"]
    by (auto simp: algebra_simps simp del:log_le_cancel_iff)
next
  case (9 a b la lb rb)
  let ?A = "\<langle>la, a, \<langle>lb, b, rb\<rangle>\<rangle>"
  have "b \<notin> set_tree la" using "9.prems"(1) by auto
  with 9 show ?case using
    log_le_cancel_iff[of 2 "size1(Node la a lb)" "size1 ?A"]
    log_le_cancel_iff[of 2 "size1(Node lb b rb)" "size1 ?A"]
    by (auto simp: algebra_simps simp del:log_le_cancel_iff)
next
  case (6 x b a lb rb ra)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree ra" using "6.prems"(1) by auto
  hence 1: "x \<in> set_tree lb" using "6.prems" \<open>x<b\<close> by (auto)
  obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using splay_not_Leaf[OF \<open>lb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node ?B a ra"
  let ?R = lb  let ?R' = "Node lu u ru"
  let ?A' = "Node rb a ra"  let ?B' = "Node ru b ?A'"
  have "a_splay x ?A = a_splay x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "6.prems" 1 sp
    by(auto simp: a_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 6 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?R" "size1 ?A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
next
  case (8 b x a rb lb ra)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree ra"
    using "8.prems"(1) \<open>x < a\<close> by(auto)
  hence 1: "x \<in> set_tree rb" using "8.prems" \<open>b<x\<close> \<open>x<a\<close> by (auto)
  obtain lu u ru where sp: "splay x rb = Node lu u ru"
     using splay_not_Leaf[OF \<open>rb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node ?B a ra"
  let ?R = rb  let ?R' = "Node lu u ru"
  let ?B' = "Node lb b lu"  let ?A' = "Node ru a ra"
  have "a_splay x ?A = a_splay x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "8.prems" 1 sp
    by(auto simp: a_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 8 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> rb + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> rb + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> rb + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?B'" "size1 ?A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (11 a x b lb la rb)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree la"
    using "11.prems"(1) \<open>a<x\<close> by (auto)
  hence 1: "x \<in> set_tree lb" using "11.prems" \<open>a<x\<close> \<open>x<b\<close> by (auto)
  obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using splay_not_Leaf[OF \<open>lb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node la a ?B"
  let ?R = lb  let ?R' = "Node lu u ru"
  let ?B' = "Node ru b rb"  let ?A' = "Node la a lu"
  have "a_splay x ?A = a_splay x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "11.prems" 1 sp
    by(auto simp: a_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 11 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?R + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?B'" "size1 ?A'"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (14 a x b rb la lb)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree la"
    using "14.prems"(1) \<open>b<x\<close> by(auto)
  hence 1: "x \<in> set_tree rb" using "14.prems" \<open>b<x\<close> \<open>a<x\<close> by (auto)
  obtain lu u ru where sp: "splay x rb = Node lu u ru"
    using splay_not_Leaf[OF \<open>rb \<noteq> Leaf\<close>] by blast
  from zig_zig[of rb x ru lu lx rx _ b lb a la] 14 sp 0
  show ?case by(auto simp: a_splay_def size_if_splay algebra_simps)
(* The explicit version:
  have "a_splay x ?A = a_splay x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "14.prems" 1 sp
    by(auto simp: a_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 14 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> rb + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?R" "size1 ?A'"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
*)
qed

lemma a_splay_ub2: assumes "bst t" "a : set_tree t"
shows "a_splay a t \<le> 3 * (\<phi> t - 1) + 1"
proof -
  from assms(2) obtain la ra where N: "Node la a ra : subtrees t"
    by (metis set_treeE)
  have "a_splay a t \<le> 3 * (\<phi> t - \<phi>(Node la a ra)) + 1" by(rule a_splay_ub[OF assms(1) N])
  also have "\<dots> \<le> 3 * (\<phi> t - 1) + 1" by(simp add: field_simps)
  finally show ?thesis .
qed

lemma a_splay_ub3: assumes "bst t" shows "a_splay a t \<le> 3 * \<phi> t + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: a_splay_def)
next
  assume "t \<noteq> Leaf"
  from ex_in_set_tree[OF this assms] obtain a' where
    a': "a' \<in> set_tree t"  "splay a' t = splay a t"  "t_splay a' t = t_splay a t"
    by blast
  have [arith]: "log 2 2 > 0" by simp
  show ?thesis using a_splay_ub2[OF assms a'(1)] by(simp add: a_splay_def a' log_divide)
qed


subsubsection "Analysis of insert"

lemma amor_insert: assumes "bst t"
shows "t_splay a t + \<Phi>(Splay_Tree.insert a t) - \<Phi> t \<le> 4 * log 2 (size1 t) + 2" (is "?l \<le> ?r")
proof cases
  assume "t = Leaf" thus ?thesis by(simp)
next
  assume "t \<noteq> Leaf"
  then obtain l e r where [simp]: "splay a t = Node l e r"
    by (metis tree.exhaust splay_Leaf_iff)
  let ?t = "real(t_splay a t)"
  let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> t"
  let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
  have opt: "?t + \<Phi> (splay a t) - ?Ps  \<le> 3 * log 2 (real (size1 t)) + 1"
    using a_splay_ub3[OF \<open>bst t\<close>, simplified a_splay_def, of a] by (simp)
  from less_linear[of e a]
  show ?thesis
  proof (elim disjE)
    assume "e=a"
    have nneg: "log 2 (1 + real (size t)) \<ge> 0" by simp
    thus ?thesis using \<open>t \<noteq> Leaf\<close> opt \<open>e=a\<close>
      apply(simp add: algebra_simps) using nneg by arith
  next
    let ?L = "log 2 (real(size1 l) + 1)"
    assume "e<a" hence "e \<noteq> a" by simp
    hence "?l = (?t + ?Plr - ?Ps) + ?L + ?LR"
      using  \<open>t \<noteq> Leaf\<close> \<open>e<a\<close> by(simp)
    also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
      using opt size_splay[of a t,symmetric] by(simp)
    also have "?L \<le> log 2 ?slr" by(simp)
    also have "?LR \<le> log 2 ?slr + 1"
    proof -
      have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
      also have "\<dots> \<le> log 2 ?slr + 1"
        by (simp add: log_mult del:distrib_left_numeral)
      finally show ?thesis .
    qed
    finally show ?thesis using size_splay[of a t,symmetric] by (simp)
  next
    let ?R = "log 2 (2 + real(size r))"
    assume "a<e" hence "e \<noteq> a" by simp
    hence "?l = (?t + ?Plr - ?Ps) + ?R + ?LR"
      using \<open>t \<noteq> Leaf\<close> \<open>a<e\<close> by(simp)
    also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
      using opt size_splay[of a t,symmetric] by(simp)
    also have "?R \<le> log 2 ?slr" by(simp)
    also have "?LR \<le> log 2 ?slr + 1"
    proof -
      have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
      also have "\<dots> \<le> log 2 ?slr + 1"
        by (simp add: log_mult del:distrib_left_numeral)
      finally show ?thesis .
    qed
    finally show ?thesis using size_splay[of a t, symmetric] by simp
  qed
qed


subsubsection "Analysis of delete"

definition a_splay_max :: "'a::linorder tree \<Rightarrow> real" where
"a_splay_max t = t_splay_max t + \<Phi>(splay_max t) - \<Phi> t"

lemma a_splay_max_ub: "\<lbrakk> bst t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> a_splay_max t \<le> 3 * (\<phi> t - 1) + 1"
proof(induction t rule: splay_max.induct)
  case 1 thus ?case by (simp)
next
  case (2 l b)
  thus ?case using one_le_log_cancel_iff[of 2 "size1 l + 1"]
    by (simp add: a_splay_max_def del: one_le_log_cancel_iff)
next
  case (3 l b rl c rr)
  show ?case
  proof cases
    assume "rr = Leaf"
    thus ?thesis
      using one_le_log_cancel_iff[of 2 "1 + size1 rl"]
        one_le_log_cancel_iff[of 2 "1 + size1 l + size1 rl"]
        log_le_cancel_iff[of 2 "size1 l + size1 rl" "1 + size1 l + size1 rl"]
     by (auto simp: a_splay_max_def field_simps
           simp del: log_le_cancel_iff one_le_log_cancel_iff)
  next
    assume "rr \<noteq> Leaf"
    then obtain l' u r' where sp: "splay_max rr = Node l' u r'"
      using splay_max_Leaf_iff tree.exhaust by blast
    hence 1: "size rr = size l' + size r' + 1"
      using size_splay_max[of rr,symmetric] by(simp)
    let ?C = "Node rl c rr"  let ?B = "Node l b ?C"
    let ?B' = "Node l b rl"  let ?C' = "Node ?B' c l'"
    have "a_splay_max ?B = a_splay_max rr + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 1" using "3.prems" sp 1
      by(auto simp add: a_splay_max_def)
    also have "\<dots> \<le> 3 * (\<phi> rr - 1) + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 2"
      using 3 \<open>rr \<noteq> Leaf\<close> by auto
    also have "\<dots> = 2 * \<phi> rr + \<phi> ?B' + \<phi> ?C' - \<phi> ?C - 1" by simp
    also have "\<dots> \<le> \<phi> rr + \<phi> ?B' + \<phi> ?C' - 1" by simp
    also have "\<dots> \<le> 2 * \<phi> ?B + \<phi> ?C' - 2"
      using ld_ld_1_less[of "size1 ?B'" "size1 rr"] by(simp add:)
    also have "\<dots> \<le> 3 * \<phi> ?B - 2" using 1 by simp
    finally show ?case by simp
  qed
qed

lemma a_splay_max_ub3: assumes "bst t" shows "a_splay_max t \<le> 3 * \<phi> t + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: a_splay_max_def)
next
  assume "t \<noteq> Leaf"
  have [arith]: "log 2 2 > 0" by simp
  show ?thesis using a_splay_max_ub[OF assms \<open>t \<noteq> Leaf\<close>] by(simp add: a_splay_max_def)
qed

lemma amor_delete: assumes "bst t"
shows "t_delete a t + \<Phi>(Splay_Tree.delete a t) - \<Phi> t \<le> 6 * log 2 (size1 t) + 2"
proof (cases t)
  case Leaf thus ?thesis by(simp add: Splay_Tree.delete_def t_delete_def)
next
  case [simp]: (Node ls x rs)
  then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
    by (metis tree.exhaust splay_Leaf_iff)
  let ?t = "real(t_splay a t)"
  let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> t"
  let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
  let ?lslr = "log 2 (real (size ls) + (real (size rs) + 2))"
  have "?lslr \<ge> 0" by simp
  have opt: "?t + \<Phi> (splay a t) - ?Ps  \<le> 3 * log 2 (real (size1 t)) + 1"
    using a_splay_ub3[OF \<open>bst t\<close>, simplified a_splay_def, of a]
    by (simp add: field_simps)
  show ?thesis
  proof (cases "e=a")
    case False thus ?thesis
      using opt apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
      using \<open>?lslr \<ge> 0\<close> by arith
  next
    case [simp]: True
    show ?thesis
    proof (cases l)
      case Leaf
      have 1: "log 2 (real (size r) + 2) \<ge> 0" by(simp)
      show ?thesis
        using Leaf opt apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
        using 1 \<open>?lslr \<ge> 0\<close> by arith
    next
      case (Node ll y lr)
      then obtain l' y' r' where [simp]: "splay_max (Node ll y lr) = Node l' y' r'"
      using splay_max_Leaf_iff tree.exhaust by blast
      have "bst l" using bst_splay[OF \<open>bst t\<close>, of a] by simp
      have "\<Phi> r' \<ge> 0" apply (induction r') by (auto)
      have optm: "real(t_splay_max l) + \<Phi> (splay_max l) - \<Phi> l  \<le> 3 * \<phi> l + 1"
        using a_splay_max_ub3[OF \<open>bst l\<close>, simplified a_splay_max_def] by (simp add: field_simps Node)
      have 1: "log 2 (2+(real(size l')+real(size r))) \<le> log 2 (2+(real(size l)+real(size r)))"
        using size_splay_max[of l] Node by simp
      have 2: "log 2 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
      have 3: "log 2 (size1 l' + size1 r) \<le> log 2 (size1 l' + size1 r') + log 2 ?slr"
        apply simp using 1 2 by arith
      have 4: "log 2 (real(size ll) + (real(size lr) + 2)) \<le> ?lslr"
        using size_if_splay[OF sp] Node by simp
      show ?thesis using add_mono[OF opt optm] Node 3
        apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
        using 4 \<open>\<Phi> r' \<ge> 0\<close> by arith
    qed
  qed
qed


subsubsection "Overall analysis"

fun U where
"U Empty [] = 1" |
"U (Splay _) [t] = 3 * log 2 (size1 t) + 1" |
"U (Insert _) [t] = 4 * log 2 (size1 t) + 2" |
"U (Delete _) [t] = 6 * log 2 (size1 t) + 2"

interpretation Amortized
where arity = arity and exec = exec and inv = bst
and cost = cost and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 ss f) show ?case
  proof (cases f)
    case Empty thus ?thesis using 1 by auto
  next
    case (Splay a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with Splay bst_splay[OF \<open>bst t\<close>, of a] show ?thesis
      by (auto split: tree.split)
  next
    case (Insert a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with bst_splay[OF \<open>bst t\<close>, of a] Insert show ?thesis
      by (auto simp: splay_bstL[OF \<open>bst t\<close>] splay_bstR[OF \<open>bst t\<close>] split: tree.split)
  next
    case (Delete a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with 1 Delete show ?thesis by(simp add: bst_delete)
  qed
next
  case (2 t) thus ?case by (induction t) auto
next
  case (3 ss f)
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case Empty thus ?thesis using 3(2) by(simp add: a_splay_def)
  next
    case (Splay a)
    then obtain t where "ss = [t]" "bst t" using 3 by auto
    thus ?thesis using Splay a_splay_ub3[OF \<open>bst t\<close>] by(simp add: a_splay_def)
  next
    case [simp]: (Insert a)
    then obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    thus ?thesis using amor_insert[of t a] by auto
  next
    case [simp]: (Delete a)
    then obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    thus ?thesis using amor_delete[of t a] by auto
  qed
qed

end
