(* Author: Tobias Nipkow *)

section "Skew Heap Analysis"

theory Skew_Heap_Analysis
imports
  Complex_Main
  Skew_Heap.Skew_Heap
  Amortized_Framework
  Priority_Queue_ops_merge
begin

text\<open>The following proof is a simplified version of the one by Kaldewaij and
Schoenmakers~\cite{KaldewaijS-IPL91}.\<close>

text \<open>right-heavy:\<close>
definition rh :: "'a tree => 'a tree => nat" where
"rh l r = (if size l < size r then 1 else 0)"

text \<open>Function \<open>\<Gamma>\<close> in \cite{KaldewaijS-IPL91}: number of right-heavy nodes on left spine.\<close>
fun lrh :: "'a tree \<Rightarrow> nat" where
"lrh Leaf = 0" |
"lrh (Node l _ r) = rh l r + lrh l"

text \<open>Function \<open>\<Delta>\<close> in \cite{KaldewaijS-IPL91}: number of not-right-heavy nodes on right spine.\<close>
fun rlh :: "'a tree \<Rightarrow> nat" where
"rlh Leaf = 0" |
"rlh (Node l _ r) = (1 - rh l r) + rlh r"

lemma Gexp: "2 ^ lrh h \<le> size h + 1"
by (induction h) (auto simp: rh_def)

corollary Glog: "lrh h \<le> log 2 (size1 h)"
by (metis Gexp le_log2_of_power size1_size)

lemma Dexp: "2 ^ rlh h \<le> size h + 1"
by (induction h) (auto simp: rh_def)

corollary Dlog: "rlh h \<le> log 2 (size1 h)"
by (metis Dexp le_log2_of_power size1_size)

function t_merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> nat" where
"t_merge Leaf h = 1" |
"t_merge h Leaf = 1" |
"t_merge (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then t_merge (Node l2 a2 r2) r1 else t_merge (Node l1 a1 r1) r2) + 1"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

fun \<Phi> :: "'a heap \<Rightarrow> int" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + rh l r"

lemma \<Phi>_nneg: "\<Phi> t \<ge> 0"
by (induction t) auto

lemma plus_log_le_2log_plus: "\<lbrakk> x > 0; y > 0; b > 1 \<rbrakk>
  \<Longrightarrow> log b x + log b y \<le> 2 * log b (x + y)"
by(subst mult_2; rule add_mono; auto)

lemma rh1: "rh l r \<le> 1"
by(simp add: rh_def)

lemma amor_le_long:
  "t_merge t1 t2 + \<Phi> (merge t1 t2) - \<Phi> t1 - \<Phi> t2 \<le>
   lrh(merge t1 t2) + rlh t1 + rlh t2 + 1"
proof (induction t1 t2 rule: merge.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 l1 a1 r1 l2 a2 r2)
  show ?case
  proof (cases "a1 \<le> a2")
    case True
    let ?t1 = "Node l1 a1 r1" let ?t2 = "Node l2 a2 r2" let ?m = "merge ?t2 r1"
    have "t_merge ?t1 ?t2 + \<Phi> (merge ?t1 ?t2) - \<Phi> ?t1 - \<Phi> ?t2
          = t_merge ?t2 r1 + 1 + \<Phi> ?m + \<Phi> l1 + rh ?m l1 - \<Phi> ?t1 - \<Phi> ?t2"
      using True by (simp)
    also have "\<dots> = t_merge ?t2 r1 + 1 + \<Phi> ?m + rh ?m l1 - \<Phi> r1 - rh l1 r1 - \<Phi> ?t2"
      by simp
    also have "\<dots> \<le> lrh ?m + rlh ?t2 + rlh r1 + rh ?m l1 + 2 - rh l1 r1"
      using "3.IH"(1)[OF True] by linarith
    also have "\<dots> = lrh ?m + rlh ?t2 + rlh r1 + rh ?m l1 + 1 + (1 - rh l1 r1)"
      using rh1[of l1 r1] by (simp)
    also have "\<dots> = lrh ?m + rlh ?t2 + rlh ?t1 + rh ?m l1 + 1"
      by (simp)
    also have "\<dots> = lrh (merge ?t1 ?t2) + rlh ?t1 + rlh ?t2 + 1"
      using True by(simp)
    finally show ?thesis .
  next
    case False with 3 show ?thesis by auto
  qed
qed

lemma amor_le:
  "t_merge t1 t2 + \<Phi> (merge t1 t2) - \<Phi> t1 - \<Phi> t2 \<le>
   lrh(merge t1 t2) + rlh t1 + rlh t2 + 1"
by(induction t1 t2 rule: merge.induct)(auto)

lemma a_merge:
  "t_merge t1 t2 + \<Phi>(merge t1 t2) - \<Phi> t1 - \<Phi> t2 \<le>
   3 * log 2 (size1 t1 + size1 t2) + 1" (is "?l \<le> _")
proof -
  have "?l \<le> lrh(merge t1 t2) + rlh t1 + rlh t2 + 1" using amor_le[of t1 t2] by arith
  also have "\<dots> = real(lrh(merge t1 t2)) + rlh t1 + rlh t2 + 1" by simp
  also have "\<dots> = real(lrh(merge t1 t2)) + (real(rlh t1) + rlh t2) + 1" by simp
  also have "rlh t1 \<le> log 2 (size1 t1)" by(rule Dlog)
  also have "rlh t2 \<le> log 2 (size1 t2)" by(rule Dlog)
  also have "lrh (merge t1 t2) \<le> log 2 (size1(merge t1 t2))" by(rule Glog)
  also have "size1(merge t1 t2) = size1 t1 + size1 t2 - 1" by(simp add: size1_size)
  also have "log 2 (size1 t1 + size1 t2 - 1) \<le> log 2 (size1 t1 + size1 t2)" by(simp add: size1_size)
  also have "log 2 (size1 t1) + log 2 (size1 t2) \<le> 2 * log 2 (real(size1 t1) + (size1 t2))"
    by(rule plus_log_le_2log_plus) (auto simp: size1_size)
  finally show ?thesis by(simp)
qed

definition t_insert :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> int" where
"t_insert a h = t_merge (Node Leaf a Leaf) h + 1"

lemma a_insert: "t_insert a h + \<Phi>(Skew_Heap.insert a h) - \<Phi> h \<le> 3 * log 2 (size1 h + 2) + 2"
using a_merge[of "Node Leaf a Leaf" "h"]
by (simp add: numeral_eq_Suc t_insert_def Skew_Heap.insert_def rh_def)

definition t_del_min :: "('a::linorder) heap \<Rightarrow> int" where
"t_del_min h = (case h of Leaf \<Rightarrow> 1 | Node t1 a t2 \<Rightarrow> t_merge t1 t2 + 1)"

lemma a_del_min: "t_del_min h + \<Phi>(del_min h) - \<Phi> h \<le> 3 * log 2 (size1 h + 2) + 2"
proof (cases h)
  case Leaf thus ?thesis by (simp add: t_del_min_def)
next
  case (Node t1 _ t2)
  have [arith]: "log 2 (2 + (real (size t1) + real (size t2))) \<le>
                log 2 (4 + (real (size t1) + real (size t2)))" by simp
  from Node show ?thesis using a_merge[of t1 t2]
    by (simp add: size1_size t_del_min_def rh_def)
qed


subsubsection "Instantiation of Amortized Framework"

lemma t_merge_nneg: "t_merge h1 h2 \<ge> 0"
by(induction h1 h2 rule: t_merge.induct) auto

fun exec :: "'a::linorder op \<Rightarrow> 'a heap list \<Rightarrow> 'a heap" where
"exec Empty [] = Leaf" |
"exec (Insert a) [h] = Skew_Heap.insert a h" |
"exec Del_min [h] = del_min h" |
"exec Merge [h1,h2] = merge h1 h2"

fun cost :: "'a::linorder op \<Rightarrow> 'a heap list \<Rightarrow> nat" where
"cost Empty [] = 1" |
"cost (Insert a) [h] = t_merge (Node Leaf a Leaf) h" |
"cost Del_min [h] = (case h of Leaf \<Rightarrow> 1 | Node t1 a t2 \<Rightarrow> t_merge t1 t2)" |
"cost Merge [h1,h2] = t_merge h1 h2"

fun U where
"U Empty [] = 1" |
"U (Insert _) [h] = 3 * log 2 (size1 h + 2) + 1" |
"U Del_min [h] = 3 * log 2 (size1 h + 2) + 3" |
"U Merge [h1,h2] = 3 * log 2 (size1 h1 + size1 h2) + 1"

interpretation Amortized
where arity = arity and exec = exec and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 h) show ?case using \<Phi>_nneg[of h] by linarith
next
  case (3 ss f)
  show ?case
  proof (cases f)
    case Empty thus ?thesis using 3(2) by (auto)
  next
    case [simp]: (Insert a)
    obtain h where [simp]: "ss = [h]" using 3(2) by (auto)
    thus ?thesis using a_merge[of "Node Leaf a Leaf" "h"]
      by (simp add: numeral_eq_Suc insert_def rh_def t_merge_nneg)
  next
    case [simp]: Del_min
    obtain h where [simp]: "ss = [h]" using 3(2) by (auto)
    thus ?thesis
    proof (cases h)
      case Leaf with Del_min show ?thesis by simp
    next
      case (Node t1 _ t2)
      have [arith]: "log 2 (2 + (real (size t1) + real (size t2))) \<le>
               log 2 (4 + (real (size t1) + real (size t2)))" by simp
      from Del_min Node show ?thesis using a_merge[of t1 t2]
        by (simp add: size1_size t_merge_nneg)
    qed
  next
    case [simp]: Merge
    obtain h1 h2 where "ss = [h1,h2]" using 3(2) by (auto simp: numeral_eq_Suc)
    thus ?thesis using a_merge[of h1 h2] by (simp add: t_merge_nneg)
  qed
qed

end
