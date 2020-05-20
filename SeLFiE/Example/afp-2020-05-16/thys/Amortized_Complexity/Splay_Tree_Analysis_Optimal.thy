subsection "Splay Tree Analysis (Optimal)"

theory Splay_Tree_Analysis_Optimal
imports
  Splay_Tree_Analysis_Base
  Amortized_Framework
  "HOL-Library.Sum_of_Squares"
begin

text\<open>This analysis follows Schoenmakers~\cite{Schoenmakers-IPL93}.\<close>

subsubsection "Analysis of splay"

locale Splay_Analysis =
fixes \<alpha> :: real and \<beta> :: real
assumes a1[arith]: "\<alpha> > 1"
assumes A1: "\<lbrakk>1 \<le> x; 1 \<le> y; 1 \<le> z\<rbrakk> \<Longrightarrow>
 (x+y) * (y+z) powr \<beta> \<le> (x+y) powr \<beta> * (x+y+z)"
assumes A2: "\<lbrakk>1 \<le> l'; 1 \<le> r'; 1 \<le> lr; 1 \<le> r\<rbrakk> \<Longrightarrow>
   \<alpha> * (l'+r') * (lr+r) powr \<beta> * (lr+r'+r) powr \<beta>
    \<le> (l'+r') powr \<beta> * (l'+lr+r') powr \<beta> * (l'+lr+r'+r)"
assumes A3: "\<lbrakk>1 \<le> l'; 1 \<le> r'; 1 \<le> ll; 1 \<le> r\<rbrakk> \<Longrightarrow>
  \<alpha> * (l'+r') * (l'+ll) powr \<beta> * (r'+r) powr \<beta>
  \<le> (l'+r') powr \<beta> * (l'+ll+r') powr \<beta> * (l'+ll+r'+r)"
begin

lemma nl2: "\<lbrakk> ll \<ge> 1; lr \<ge> 1; r \<ge> 1 \<rbrakk> \<Longrightarrow>
  log \<alpha> (ll + lr) + \<beta> * log \<alpha> (lr + r)
  \<le> \<beta> * log \<alpha> (ll + lr) + log \<alpha> (ll + lr + r)"
apply(rule powr_le_cancel_iff[THEN iffD1, OF a1])
apply(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric] A1)
done


definition \<phi> :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> real" where
"\<phi> t1 t2 = \<beta> * log \<alpha> (size1 t1 + size1 t2)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + \<phi> l r"

definition A :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"A a t = t_splay a t + \<Phi>(splay a t) - \<Phi> t"

lemma A_simps[simp]: "A a (Node l a r) = 1"
 "a<b \<Longrightarrow> A a (Node (Node ll a lr) b r) = \<phi> lr r - \<phi> lr ll + 1"
 "b<a \<Longrightarrow> A a (Node l b (Node rl a rr)) = \<phi> rl l - \<phi> rr rl + 1"
by(auto simp add: A_def \<phi>_def algebra_simps)


lemma A_ub: "\<lbrakk> bst t; Node la a ra : subtrees t \<rbrakk>
  \<Longrightarrow> A a t \<le> log \<alpha> ((size1 t)/(size1 la + size1 ra)) + 1"
proof(induction a t rule: splay.induct)
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
  have "b \<notin> set_tree ra" using "3.prems"(1) by auto
  thus ?case using "3.prems"(1,2) nl2[of "size1 lb" "size1 rb" "size1 ra"]
    by (auto simp: \<phi>_def log_divide algebra_simps)
next
  case (9 a b la lb rb)
  have "b \<notin> set_tree la" using "9.prems"(1) by auto
  thus ?case using "9.prems"(1,2) nl2[of "size1 rb" "size1 lb" "size1 la"]
    by (auto simp add: \<phi>_def log_divide algebra_simps)
next
  case (6 x b a lb rb ra)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree ra" using "6.prems"(1) by auto
  hence 1: "x \<in> set_tree lb" using "6.prems" \<open>x<b\<close> by (auto)
  then obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using "6.prems"(1,2) by(cases "splay x lb") auto
  have "b < a" using "6.prems"(1,2) by (auto)
  let ?lu = "real (size1 lu)" let ?ru = "real (size1 ru)"
  let ?rb = "real(size1 rb)"  let ?r = "real(size1 ra)"
  have "1 + log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?rb + ?r) + \<beta> * log \<alpha> (?rb + ?ru + ?r) \<le>
        \<beta> * log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?rb + ?ru) + log \<alpha> (?lu + ?rb + ?ru + ?r)" (is "?L\<le>?R")
  proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
    show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?lu ?ru ?rb ?r]
      by(simp add: powr_add add_ac mult.commute[of \<beta>] powr_powr[symmetric])
  qed
  thus ?case using 6 0 1 sp
    by(auto simp: A_def \<phi>_def size_if_splay algebra_simps log_divide)
next
  case (8 b x a rb lb ra)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree ra" using "8.prems"(1) by(auto)
  hence 1: "x \<in> set_tree rb" using "8.prems" \<open>b<x\<close> \<open>x<a\<close> by (auto)
  then obtain lu u ru where sp: "splay x rb = Node lu u ru"
    using "8.prems"(1,2) by(cases "splay x rb") auto
  let ?lu = "real (size1 lu)" let ?ru = "real (size1 ru)"
  let ?lb = "real(size1 lb)" let ?r = "real(size1 ra)"
  have "1 + log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?lb) + \<beta> * log \<alpha> (?ru + ?r) \<le>
        \<beta> * log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?lb + ?ru) + log \<alpha> (?lu + ?lb + ?ru + ?r)" (is "?L\<le>?R")
  proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
     show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A3[of ?lu ?ru ?lb ?r]
       by(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric])
  qed
  thus ?case using 8 0 1 sp
    by(auto simp add: A_def size_if_splay \<phi>_def log_divide algebra_simps)
next
  case (11 a x b lb la rb)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree la" using "11.prems"(1) by (auto)
  hence 1: "x \<in> set_tree lb" using "11.prems" \<open>a<x\<close> \<open>x<b\<close> by (auto)
  then obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using "11.prems"(1,2) by(cases "splay x lb") auto
  let ?lu = "real (size1 lu)" let ?ru = "real (size1 ru)"
  let ?l = "real(size1 la)"  let ?rb = "real(size1 rb)"
  have "1 + log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?l) + \<beta> * log \<alpha> (?ru + ?rb) \<le>
        \<beta> * log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?ru + ?rb) + log \<alpha> (?lu + ?l + ?ru + ?rb)" (is "?L\<le>?R")
  proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
    show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A3[of ?ru ?lu ?rb ?l]
      by(simp add: powr_add mult.commute[of \<beta>] powr_powr[symmetric])
        (simp add: algebra_simps)
  qed
  thus ?case using 11 0 1 sp
    by(auto simp add: A_def size_if_splay \<phi>_def log_divide algebra_simps)
next
  case (14 a x b rb la lb)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree la" using "14.prems"(1) by(auto)
  hence 1: "x \<in> set_tree rb" using "14.prems" \<open>a<x\<close> \<open>b<x\<close> by (auto)
  then obtain lu u ru where sp: "splay x rb = Node lu u ru"
    using "14.prems"(1,2) by(cases "splay x rb") auto
  let ?la = "real(size1 la)"  let ?lb = "real(size1 lb)"
  let ?lu = "real (size1 lu)" let ?ru = "real (size1 ru)"
  have "1 + log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?la + ?lb) + \<beta> * log \<alpha> (?lu + ?la + ?lb) \<le>
        \<beta> * log \<alpha> (?lu + ?ru) + \<beta> * log \<alpha> (?lu + ?lb + ?ru) + log \<alpha> (?lu + ?lb + ?ru + ?la)" (is "?L\<le>?R")
  proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
     show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?ru ?lu ?lb ?la]
       by(simp add: powr_add add_ac mult.commute[of \<beta>] powr_powr[symmetric])
  qed
  thus ?case using 14 0 1 sp
    by(auto simp add: A_def size_if_splay \<phi>_def log_divide algebra_simps)
qed

lemma A_ub2: assumes "bst t" "a : set_tree t"
shows "A a t \<le> log \<alpha> ((size1 t)/2) + 1"
proof -
  from assms(2) obtain la ra where N: "Node la a ra : subtrees t"
    by (metis set_treeE)
  have "A a t \<le> log \<alpha> ((size1 t)/(size1 la + size1 ra)) + 1"
    by(rule A_ub[OF assms(1) N])
  also have "\<dots> \<le> log \<alpha> ((size1 t)/2) + 1" by(simp add: field_simps)
  finally show ?thesis by simp
qed

lemma A_ub3: assumes "bst t" shows "A a t \<le> log \<alpha> (size1 t) + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: A_def)
next
  assume "t \<noteq> Leaf"
  from ex_in_set_tree[OF this assms] obtain a' where
    a': "a' \<in> set_tree t"  "splay a' t = splay a t"  "t_splay a' t = t_splay a t"
    by blast
  have [arith]: "log \<alpha> 2 > 0" by simp
  show ?thesis using A_ub2[OF assms a'(1)] by(simp add: A_def a' log_divide)
qed


definition Am :: "'a::linorder tree \<Rightarrow> real" where
"Am t = t_splay_max t + \<Phi>(splay_max t) - \<Phi> t"

lemma Am_simp3': "\<lbrakk> c<b; bst rr; rr \<noteq> Leaf\<rbrakk> \<Longrightarrow>
  Am (Node l c (Node rl b rr)) =
  (case splay_max rr of Node rrl _ rrr \<Rightarrow>
   Am rr + \<phi> rrl (Node l c rl) + \<phi> l rl - \<phi> rl rr - \<phi> rrl rrr + 1)"
by(auto simp: Am_def \<phi>_def size_if_splay_max algebra_simps neq_Leaf_iff split: tree.split)

lemma Am_ub: "\<lbrakk> bst t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> Am t \<le> log \<alpha> ((size1 t)/2) + 1"
proof(induction t rule: splay_max.induct)
  case 1 thus ?case by (simp)
next
  case 2 thus ?case by (simp add: Am_def)
next
  case (3 l b rl c rr)
  show ?case
  proof cases
    assume "rr = Leaf"
    thus ?thesis
      using nl2[of 1 "size1 rl" "size1 l"] log_le_cancel_iff[of \<alpha> 2 "2 + real(size rl)"]
      by(auto simp: Am_def \<phi>_def log_divide field_simps
           simp del: log_le_cancel_iff)
  next
    assume "rr \<noteq> Leaf"
    then obtain l' u r' where sp: "splay_max rr = Node l' u r'"
      using splay_max_Leaf_iff tree.exhaust by blast
    hence 1: "size rr = size l' + size r' + 1"
      using size_splay_max[of rr] by(simp)
    let ?l = "real (size1 l)" let ?rl = "real (size1 rl)"
    let ?l' = "real (size1 l')" let ?r' = "real (size1 r')"
    have "1 + log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l + ?rl) + \<beta> * log \<alpha> (?l' + ?l + ?rl) \<le>
      \<beta> * log \<alpha> (?l' + ?r') + \<beta> * log \<alpha> (?l' + ?rl + ?r') + log \<alpha> (?l' + ?rl + ?r' + ?l)" (is "?L\<le>?R")
    proof(rule powr_le_cancel_iff[THEN iffD1, OF a1])
      show "\<alpha> powr ?L \<le> \<alpha> powr ?R" using A2[of ?r' ?l' ?rl ?l]
        by(simp add: powr_add add.commute add.left_commute mult.commute[of \<beta>] powr_powr[symmetric])
    qed
    thus ?case using 3 sp 1 \<open>rr \<noteq> Leaf\<close>
      by(auto simp add: Am_simp3' \<phi>_def log_divide algebra_simps)
  qed
qed

lemma Am_ub3: assumes "bst t" shows "Am t \<le> log \<alpha> (size1 t) + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: Am_def)
next
  assume "t \<noteq> Leaf"
  have [arith]: "log \<alpha> 2 > 0" by simp
  show ?thesis using Am_ub[OF assms \<open>t \<noteq> Leaf\<close>] by(simp add: Am_def log_divide)
qed

end


subsubsection "Optimal Interpretation"

lemma mult_root_eq_root:
  "n>0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> root n x * y = root n (x * (y ^ n))"
by(simp add: real_root_mult real_root_pos2)

lemma mult_root_eq_root2:
  "n>0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> y * root n x = root n ((y ^ n) * x)"
by(simp add: real_root_mult real_root_pos2)

lemma powr_inverse_numeral:
  "0 < x \<Longrightarrow> x powr (1 / numeral n) = root (numeral n) x"
by (simp add: root_powr_inverse)

lemmas root_simps = mult_root_eq_root mult_root_eq_root2 powr_inverse_numeral


lemma nl31: "\<lbrakk> (l'::real) \<ge> 1; r' \<ge> 1; lr \<ge> 1; r \<ge> 1 \<rbrakk> \<Longrightarrow>
  4 * (l' + r') * (lr + r) \<le> (l' + lr + r' + r)^2"
by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [r + ~1*l' + lr + ~1*r']^2))))")

lemma nl32: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "lr \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r') * (lr + r) * (lr + r' + r) \<le> (l' + lr + r' + r)^3"
proof -
  have 1: "lr + r' + r \<le> l' + lr + r' + r" using assms by arith
  have 2: "0 \<le> (l' + lr + r' + r)^2" by (rule zero_le_power2)
  have 3: "0 \<le> lr + r' + r" using assms by arith
  from mult_mono[OF nl31[OF assms] 1 2 3] show ?thesis
    by(simp add: ac_simps numeral_eq_Suc)
qed

lemma nl3: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "lr \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r')^2 * (lr + r) * (lr + r' + r)
       \<le> (l' + lr + r') * (l' + lr + r' + r)^3"
proof-
  have 1: "l' + r' \<le> l' + lr + r'" using assms by arith
  have 2: "0 \<le> (l' + lr + r' + r)^3" using assms by simp
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl32[OF assms] 1 2 3] show ?thesis
    unfolding power2_eq_square by (simp only: ac_simps)
qed


lemma nl41: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + ll) * (r' + r) \<le> (l' + ll + r' + r)^2"
using assms by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [r + ~1*l' + ~1*ll + r']^2))))")

lemma nl42: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r') * (l' + ll) * (r' + r) \<le> (l' + ll + r' + r)^3"
proof -
  have 1: "l' + r' \<le> l' + ll + r' + r" using assms by arith
  have 2: "0 \<le> (l' + ll + r' + r)^2" by (rule zero_le_power2)
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl41[OF assms] 1 2 3] show ?thesis
    by(simp add: ac_simps numeral_eq_Suc del: distrib_right_numeral)
qed

lemma nl4: assumes "(l'::real) \<ge> 1" "r' \<ge> 1" "ll \<ge> 1" "r \<ge> 1"
shows "4 * (l' + r')^2 * (l' + ll) * (r' + r)
    \<le> (l' + ll + r') * (l' + ll + r' + r)^3"
proof-
  have 1: "l' + r' \<le> l' + ll + r'" using assms by arith
  have 2: "0 \<le> (l' + ll + r' + r)^3" using assms by simp
  have 3: "0 \<le> l' + r'" using assms by arith
  from mult_mono[OF nl42[OF assms] 1 2 3] show ?thesis
    unfolding power2_eq_square by (simp only: ac_simps)
qed

lemma cancel: "x>(0::real) \<Longrightarrow> c * x ^ 2 * y * z \<le> u * v \<Longrightarrow> c * x ^ 3 * y * z \<le> x * u * v"
by(simp add: power2_eq_square power3_eq_cube)

interpretation S34: Splay_Analysis "root 3 4" "1/3"
proof (standard, goal_cases)
  case 2 thus ?case
    by(simp add: root_simps)
      (auto simp: numeral_eq_Suc split_mult_pos_le intro!: mult_mono)
next
  case 3 thus ?case by(simp add: root_simps cancel nl3)
next
  case 4 thus ?case by(simp add: root_simps cancel nl4)
qed simp


lemma log4_log2: "log 4 x = log 2 x / 2"
proof -
  have "log 4 x = log (2^2) x" by simp
  also have "\<dots> = log 2 x / 2" by(simp only: log_base_pow)
  finally show ?thesis .
qed

declare log_base_root[simp]

lemma A34_ub: assumes "bst t"
shows "S34.A a t \<le> (3/2) * log 2 (size1 t) + 1"
proof -
  have "S34.A a t \<le> log (root 3 4) (size1 t) + 1" by(rule S34.A_ub3[OF assms])
  also have "\<dots> = (3/2) * log 2 (size t + 1) + 1" by(simp add: log4_log2)
  finally show ?thesis by simp
qed

lemma Am34_ub: assumes "bst t"
shows "S34.Am t \<le> (3/2) * log 2 (size1 t) + 1"
proof -
  have "S34.Am t \<le> log (root 3 4) (size1 t) + 1" by(rule S34.Am_ub3[OF assms])
  also have "\<dots> = (3/2) * log 2 (size1 t) + 1" by(simp add: log4_log2)
  finally show ?thesis by simp
qed

subsubsection "Overall analysis"

fun U where
"U Empty [] = 1" |
"U (Splay _) [t] = (3/2) * log 2 (size1 t) + 1" |
"U (Insert _) [t] = 2 * log 2 (size1 t) + 3/2" |
"U (Delete _) [t] = 3 * log 2 (size1 t) + 2"

interpretation Amortized
where arity = arity and exec = exec and inv = bst
and cost = cost and \<Phi> = S34.\<Phi> and U = U
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
  case (2 t) show ?case by(induction t)(simp_all add: S34.\<phi>_def)
next
  case (3 ss f)
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case Empty thus ?thesis using 3(2) by(simp add: S34.A_def)
  next
    case (Splay a)
    then obtain t where "ss = [t]" "bst t" using 3 by auto
    thus ?thesis using S34.A_ub3[OF \<open>bst t\<close>] Splay
      by(simp add: S34.A_def log4_log2)
  next
    case [simp]: (Insert a)
    obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    show ?thesis
    proof cases
      assume "t = Leaf" thus ?thesis by(simp add: S34.\<phi>_def log4_log2)
    next
      assume "t \<noteq> Leaf"
      then obtain l e r where [simp]: "splay a t = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a t)"
      let ?Plr = "S34.\<Phi> l + S34.\<Phi> r"  let ?Ps = "S34.\<Phi> t"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      have opt: "?t + S34.\<Phi> (splay a t) - ?Ps  \<le> 3/2 * log 2 (real (size1 t)) + 1"
        using S34.A_ub3[OF \<open>bst t\<close>, simplified S34.A_def, of a]
        by (simp add: log4_log2)
      from less_linear[of e a]
      show ?thesis
      proof (elim disjE)
        assume "e=a"
        have nneg: "log 2 (1 + real (size t)) \<ge> 0" by simp
        thus ?thesis using \<open>t \<noteq> Leaf\<close> opt \<open>e=a\<close>
          apply(simp add: field_simps) using nneg by arith
      next
        let ?L = "log 2 (real(size1 l) + 1)"
        assume "e<a" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?L / 2 + ?LR / 2"
          using \<open>t \<noteq> Leaf\<close> \<open>e<a\<close> by(simp add: S34.\<phi>_def log4_log2)
        also have "?t + ?Plr - ?Ps \<le> log 2 ?slr + 1"
          using opt size_splay[of a t,symmetric]
          by(simp add: S34.\<phi>_def log4_log2)
        also have "?L/2 \<le> log 2 ?slr / 2" by(simp)
        also have "?LR/2 \<le> log 2 ?slr / 2 + 1/2"
        proof -
          have "?LR/2 \<le> log 2 (2 * ?slr) / 2" by simp
          also have "\<dots> \<le> log 2 ?slr / 2 + 1/2"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a t,symmetric] by simp
      next
        let ?R = "log 2 (2 + real(size r))"
        assume "a<e" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?R / 2 + ?LR / 2"
          using  \<open>t \<noteq> Leaf\<close> \<open>a<e\<close> by(simp add: S34.\<phi>_def log4_log2)
        also have "?t + ?Plr - ?Ps \<le> log 2 ?slr + 1"
          using opt size_splay[of a t,symmetric]
          by(simp add: S34.\<phi>_def log4_log2)
        also have "?R/2 \<le> log 2 ?slr / 2" by(simp)
        also have "?LR/2 \<le> log 2 ?slr / 2 + 1/2"
        proof -
          have "?LR/2 \<le> log 2 (2 * ?slr) / 2" by simp
          also have "\<dots> \<le> log 2 ?slr / 2 + 1/2"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a t,symmetric] by simp
      qed
    qed
  next
    case [simp]: (Delete a)
    obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    show ?thesis
    proof (cases t)
      case Leaf thus ?thesis
        by(simp add: Splay_Tree.delete_def t_delete_def S34.\<phi>_def log4_log2)
    next
      case [simp]: (Node ls x rs)
      then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a t)"
      let ?Plr = "S34.\<Phi> l + S34.\<Phi> r"  let ?Ps = "S34.\<Phi> t"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      let ?lslr = "log 2 (real (size ls) + (real (size rs) + 2))"
      have "?lslr \<ge> 0" by simp
      have opt: "?t + S34.\<Phi> (splay a t) - ?Ps  \<le> 3/2 * log 2 (real (size1 t)) + 1"
        using S34.A_ub3[OF \<open>bst t\<close>, simplified S34.A_def, of a]
        by (simp add: log4_log2 field_simps)
      show ?thesis
      proof (cases "e=a")
        case False thus ?thesis using opt
          apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
          using \<open>?lslr \<ge> 0\<close> by arith
      next
        case [simp]: True
        show ?thesis
        proof (cases l)
          case Leaf
          have "S34.\<phi> Leaf r \<ge> 0" by(simp add: S34.\<phi>_def)
          thus ?thesis using Leaf opt
            apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
            using \<open>?lslr \<ge> 0\<close> by arith
        next
          case (Node ll y lr)
          then obtain l' y' r' where [simp]:
            "splay_max (Node ll y lr) = Node l' y' r'"
            using splay_max_Leaf_iff tree.exhaust by blast
          have "bst l" using bst_splay[OF \<open>bst t\<close>, of a] by simp
          have "S34.\<Phi> r' \<ge> 0" apply (induction r') by (auto simp add: S34.\<phi>_def)
          have optm: "real(t_splay_max l) + S34.\<Phi> (splay_max l) - S34.\<Phi> l
            \<le> 3/2 * log 2 (real (size1 l)) + 1"
            using S34.Am_ub3[OF \<open>bst l\<close>, simplified S34.Am_def]
            by (simp add: log4_log2 field_simps Node)
          have 1: "log 4 (2+(real(size l')+real(size r))) \<le>
            log 4 (2+(real(size l)+real(size r)))"
            using size_splay_max[of l] Node by simp
          have 2: "log 4 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
          have 3: "S34.\<phi> l' r \<le> S34.\<phi> l' r' + S34.\<phi> l r"
            apply(simp add: S34.\<phi>_def) using 1 2 by arith
          have 4: "log 2 (real(size ll) + (real(size lr) + 2)) \<le> ?lslr"
            using size_if_splay[OF sp] Node by simp
          show ?thesis using add_mono[OF opt optm] Node 3
            apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
            using 4 \<open>S34.\<Phi> r' \<ge> 0\<close> by arith
        qed
      qed
    qed
  qed
qed

end
