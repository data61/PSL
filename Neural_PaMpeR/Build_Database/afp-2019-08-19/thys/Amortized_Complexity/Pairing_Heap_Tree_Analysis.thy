(* Author: Hauke Brinkop and Tobias Nipkow *)

section \<open>Pairing Heaps\<close>

subsection \<open>Binary Tree Representation\<close>

theory Pairing_Heap_Tree_Analysis
imports  
  Pairing_Heap.Pairing_Heap_Tree
  Amortized_Framework
  Priority_Queue_ops_merge
  Lemmas_log
begin

text
\<open>Verification of logarithmic bounds on the amortized complexity of
pairing heaps \cite{FredmanSST86,Brinkop}.\<close>

fun len :: "'a tree \<Rightarrow> nat" where 
  "len Leaf = 0"
| "len (Node _ _ r) = 1 + len r"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + log 2 (1 + size l + size r)"

lemma link_size[simp]: "size (link h) = size h" 
  by (cases h rule: link.cases) simp_all

lemma size_pass\<^sub>1: "size (pass\<^sub>1 h) = size h" 
  by (induct h rule: pass\<^sub>1.induct) simp_all

lemma size_pass\<^sub>2: "size (pass\<^sub>2 h) = size h" 
  by (induct h rule: pass\<^sub>2.induct) simp_all

lemma size_merge: 
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> size (merge h1 h2) = size h1 + size h2"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_insert: "is_root h \<Longrightarrow> \<Phi> (insert x h) - \<Phi> h \<le> log 2  (size h + 1)"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_merge:
  assumes "h1 = Node lx x Leaf" "h2 = Node ly y Leaf" 
  shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (size h1 + size h2) + 1" 
proof -
  let ?hs = "Node lx x (Node ly y Leaf)"
  have "\<Phi> (merge h1 h2) = \<Phi> (link ?hs)" using assms by simp
  also have "\<dots> = \<Phi> lx + \<Phi> ly + log 2 (size lx + size ly + 1) + log 2 (size lx + size ly + 2)"
    by (simp add: algebra_simps)
  also have "\<dots> = \<Phi> lx + \<Phi> ly + log 2 (size lx + size ly + 1) + log 2 (size h1 + size h2)"
     using assms by simp
  finally have "\<Phi> (merge h1 h2) = \<dots>" .
  have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 =
   log 2 (size lx + size ly + 1) + log 2 (size h1 + size h2)
   - log 2 (size lx + 1) - log 2 (size ly + 1)"
     using assms by (simp add: algebra_simps)
  also have "\<dots> \<le> log 2 (size h1 + size h2) + 1"
    using ld_le_2ld[of "size lx" "size ly"] assms by (simp add: algebra_simps)
  finally show ?thesis .
qed

fun upperbound :: "'a tree \<Rightarrow> real" where
  "upperbound Leaf = 0"
| "upperbound (Node _ _ Leaf) = 0"
| "upperbound (Node lx _ (Node ly _ Leaf)) = 2*log 2 (size lx + size ly + 2)" 
| "upperbound (Node lx _ (Node ly _ ry)) = 2*log 2 (size lx + size ly + size ry + 2) 
    - 2*log 2 (size ry) - 2 + upperbound ry"

lemma \<Delta>\<Phi>_pass1_upperbound: "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs  \<le> upperbound hs"
proof (induction hs rule: upperbound.induct)
  case (3 lx x ly y)
  have "log 2  (size lx + size ly + 1) - log 2  (size ly + 1) 
    \<le> log 2 (size lx + size ly + 1)" by simp
  also have "\<dots> \<le> log 2 (size lx + size ly + 2)" by simp
  also have "\<dots> \<le> 2*\<dots>" by simp
  finally show ?case by (simp add: algebra_simps)
next
  case (4 lx x ly y lz z rz)
  let ?ry = "Node lz z rz"
  let ?rx = "Node ly y ?ry"
  let ?h = "Node lx x ?rx"
  let ?t ="log 2 (size lx + size ly + 1) - log 2 (size ly + size ?ry + 1)"
  have "\<Phi> (pass\<^sub>1 ?h) - \<Phi> ?h \<le> ?t + upperbound ?ry" 
    using "4.IH" by (simp add: size_pass\<^sub>1 algebra_simps)
  moreover have "log 2 (size lx + size ly + 1) + 2 * log 2 (size ?ry) + 2
    \<le> 2 * log 2 (size ?h) + log 2 (size ly + size ?ry + 1)" (is "?l \<le> ?r")
  proof -
    have "?l \<le> 2 * log 2 (size lx + size ly + size ?ry + 1) + log 2 (size ?ry)"
      using ld_sum_inequality [of "size lx + size ly + 1" "size ?ry"] by simp
    also have "\<dots> \<le> 2 * log 2 (size lx + size ly + size ?ry + 2) + log 2 (size ?ry)"
      by simp
    also have "\<dots> \<le> ?r" by simp
    finally show ?thesis .
  qed
  ultimately show ?case by simp
qed simp_all

lemma \<Delta>\<Phi>_pass1: assumes "hs \<noteq> Leaf"
  shows "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs \<le> 2*log 2 (size hs) - len hs + 2"
proof -
  from assms have "upperbound hs \<le> 2*log 2 (size hs) - len hs + 2" 
    by (induct hs rule: upperbound.induct) (simp_all add: algebra_simps)
  thus ?thesis using \<Delta>\<Phi>_pass1_upperbound [of "hs"] order_trans by blast
qed

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (size hs)"
proof (induction hs)
  case (Node lx x rx)
  thus ?case 
  proof (cases rx)
    case 1: (Node ly y ry)
    let ?h = "Node lx x rx"
    obtain la a where 2: "pass\<^sub>2 rx = Node la a Leaf" 
      using pass\<^sub>2_struct 1 by force
    hence 3: "size rx = size \<dots>" using size_pass\<^sub>2 by metis
    have link: "\<Phi>(link(Node lx x (pass\<^sub>2 rx))) - \<Phi> lx - \<Phi> (pass\<^sub>2 rx) =
          log 2 (size lx + size rx + 1) + log 2 (size lx + size rx) - log 2 (size rx)"
      using 2 3 by (simp add: algebra_simps) 
    have "\<Phi> (pass\<^sub>2 ?h) - \<Phi> ?h =
        \<Phi> (link (Node lx x (pass\<^sub>2 rx))) - \<Phi> lx - \<Phi> rx - log 2 (size lx + size rx + 1)"
      by (simp)
    also have "\<dots> = \<Phi> (pass\<^sub>2 rx) - \<Phi> rx + log 2 (size lx + size rx) - log 2 (size rx)"
      using link by linarith
    also have "\<dots> \<le> log 2 (size lx + size rx)"
      using Node.IH 1 by simp
    also have "\<dots> \<le> log 2 (size ?h)" using 1 by simp
    finally show ?thesis .
  qed simp
qed simp

lemma \<Delta>\<Phi>_mergepairs: assumes "hs \<noteq> Leaf"
  shows "\<Phi> (merge_pairs hs) - \<Phi> hs \<le> 3 * log 2 (size hs) - len hs + 2"
proof -
  have "pass\<^sub>1 hs \<noteq> Leaf" by (metis assms eq_size_0 size_pass\<^sub>1)
  with assms \<Delta>\<Phi>_pass1[of hs] \<Delta>\<Phi>_pass2[of "pass\<^sub>1 hs"]
  show ?thesis by (auto simp add: size_pass\<^sub>1 pass12_merge_pairs)
qed

lemma \<Delta>\<Phi>_del_min: assumes "lx \<noteq> Leaf"
shows "\<Phi> (del_min (Node lx x Leaf)) - \<Phi> (Node lx x Leaf) 
  \<le> 3*log 2 (size lx) - len lx + 2"
proof -
  let ?h = "Node lx x Leaf"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> lx - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> lx"
  let ?\<Delta>\<Phi> = "\<Phi> (del_min ?h) - \<Phi> ?h"
  have "lx \<noteq> Leaf \<Longrightarrow> \<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> (pass\<^sub>1 lx) \<le> log 2  (size lx)" 
    using \<Delta>\<Phi>_pass2 [of "pass\<^sub>1 lx"] by(metis eq_size_0 size_pass\<^sub>1)
  moreover have "lx \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>1 lx) - \<Phi> lx \<le>  2*\<dots> - len lx + 2" 
    using \<Delta>\<Phi>_pass1 by metis
  moreover have "?\<Delta>\<Phi> \<le> ?\<Delta>\<Phi>\<^sub>2" by simp
  ultimately show ?thesis using assms by linarith
qed

lemma is_root_merge:
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> is_root (merge h1 h2)"
by (simp split: tree.splits)

lemma is_root_insert: "is_root h \<Longrightarrow> is_root (insert x h)"
by (simp split: tree.splits)

lemma is_root_del_min:
  assumes "is_root h" shows "is_root (del_min h)"
proof (cases h)
  case [simp]: (Node lx x rx)
  have "rx = Leaf" using assms by simp
  thus ?thesis 
  proof (cases lx)
    case (Node ly y ry)
    then obtain la a ra where "pass\<^sub>1 lx = Node a la ra" 
      using pass\<^sub>1_struct by blast
    moreover obtain lb b where "pass\<^sub>2 \<dots> = Node b lb Leaf"
      using pass\<^sub>2_struct by blast
    ultimately show ?thesis using assms by simp
  qed simp
qed simp

lemma pass\<^sub>1_len: "len (pass\<^sub>1 h) \<le> len h"
by (induct h rule: pass\<^sub>1.induct) simp_all

fun exec :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = insert x h" |
"exec Merge [h1,h2] = merge h1 h2"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 :: "'a tree \<Rightarrow> nat" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ Leaf) = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ (Node _ _ ry)) = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 ry + 1"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 :: "'a tree \<Rightarrow> nat" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (Node _ _ rx) = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 rx + 1"

fun cost :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> nat" where
  "cost Empty [] = 1"
| "cost Del_min [Leaf] = 1"
| "cost Del_min [Node lx _  _] = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx"
| "cost (Insert a) _ = 1"
| "cost Merge _ = 1"

fun U :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> real" where
  "U Empty [] = 1"
| "U (Insert a) [h] = log 2 (size h + 1) + 1"
| "U Del_min [h] = 3*log 2 (size h + 1) + 4"
| "U Merge [h1,h2] = log 2 (size h1 + size h2 + 1) + 2"

interpretation Amortized
where arity = arity and exec = exec and cost = cost and inv = is_root 
and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 _ f) thus ?case using is_root_insert is_root_del_min is_root_merge
    by (cases f) (auto simp: numeral_eq_Suc)
next
  case (2 s) show ?case by (induct s) simp_all
next
  case (3 ss f) show ?case 
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case (Insert x)
    then obtain h where "ss = [h]" "is_root h" using 3 by auto
    thus ?thesis using Insert \<Delta>\<Phi>_insert 3 by auto
  next
    case [simp]: (Del_min)
    then obtain h where [simp]: "ss = [h]" using 3 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Node lx x rx)
      have "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx \<le> len lx + 2"
        by (induct lx rule: pass\<^sub>1.induct) simp_all
      hence "cost f ss \<le> \<dots>" by simp 
      moreover have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size h + 1) - len lx + 2"
      proof (cases lx)
        case [simp]: (Node ly y ry) 
        have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size lx) - len lx + 2"
          using  \<Delta>\<Phi>_del_min[of "lx" "x"] 3 by simp
        also have "\<dots> \<le> 3*log 2 (size h + 1) - len lx + 2" by fastforce
        finally show ?thesis by blast
      qed (insert 3, simp)
      ultimately show ?thesis by auto
    qed simp
  next
    case [simp]: Merge
    then obtain h1 h2 where [simp]: "ss = [h1,h2]" and 1: "is_root h1" "is_root h2"
      using 3 by (auto simp: numeral_eq_Suc)
    show ?thesis
    proof (cases h1)
      case Leaf thus ?thesis by (cases h2) auto
    next
      case h1: Node
      show ?thesis
      proof (cases h2)
        case Leaf thus ?thesis using h1 by simp
      next
        case h2: Node
        have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (real (size h1 + size h2)) + 1"
          apply(rule \<Delta>\<Phi>_merge) using h1 h2 1 by auto
        also have "\<dots> \<le> log 2 (size h1 + size h2 + 1) + 1" by (simp add: h1)
        finally show ?thesis by(simp add: algebra_simps)
      qed
    qed
  qed
qed

end
