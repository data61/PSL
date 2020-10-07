section "Root Balanced Tree"

theory Root_Balanced_Tree
imports
  Amortized_Complexity.Amortized_Framework0
  "HOL-Library.Tree_Multiset"
  "HOL-Data_Structures.Tree_Set"
  "HOL-Data_Structures.Balance"
  Time_Monad
begin

declare Let_def[simp]

subsection \<open>Time Prelude\<close>

text\<open>Redefinition of some auxiliary functions, but now with \<open>tm\<close> monad:\<close>

subsubsection \<open>@{const size_tree}\<close>

fun size_tree_tm :: "'a tree \<Rightarrow> nat tm" where
"size_tree_tm \<langle>\<rangle> =1 return 0" |
"size_tree_tm \<langle>l, x, r\<rangle> =1
  do { m \<leftarrow> size_tree_tm l;
       n \<leftarrow> size_tree_tm r;
       return (m+n+1)}"

definition size_tree :: "'a tree \<Rightarrow> nat" where
"size_tree t = val(size_tree_tm t)"

lemma size_tree_Leaf[simp,code]: "size_tree \<langle>\<rangle> = 0"
using val_cong[OF size_tree_tm.simps(1)]
by(simp only: size_tree_def val_simps)

lemma size_tree_Node[simp,code]:
  "size_tree \<langle>l, x, r\<rangle> =
  (let m = size_tree l;
       n = size_tree r
   in m+n+1)"
using val_cong[OF size_tree_tm.simps(2)]
by(simp only: size_tree_def val_simps)

lemma size_tree: "size_tree t = size t"
by(induction t rule: size_tree_tm.induct)(auto)

definition t_size_tree :: "'a tree \<Rightarrow> nat" where
"t_size_tree t = time(size_tree_tm t)"

lemma t_size_tree_Leaf: "t_size_tree \<langle>\<rangle> = 1"
by(simp add: t_size_tree_def tm_simps)

lemma t_size_tree_Node:
  "t_size_tree \<langle>l, x, r\<rangle> = t_size_tree l + t_size_tree r + 1"
by(simp add: t_size_tree_def size_tree_def tm_simps split: tm.split)

lemma t_size_tree: "t_size_tree t = 2 * size t + 1"
by(induction t)(auto simp: t_size_tree_Leaf t_size_tree_Node)

subsubsection \<open>@{const inorder}\<close>

fun inorder2_tm :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list tm" where
"inorder2_tm \<langle>\<rangle> xs =1 return xs" |
"inorder2_tm \<langle>l, x, r\<rangle> xs =1
  do { rs \<leftarrow> inorder2_tm r xs; inorder2_tm l (x#rs) }"

definition inorder2 :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"inorder2 t xs = val(inorder2_tm t xs)"

lemma inorder2_Leaf[simp,code]: "inorder2 \<langle>\<rangle> xs = xs"
using val_cong[OF inorder2_tm.simps(1)]
by(simp only: inorder2_def val_simps)

lemma inorder2_Node[simp,code]:
  "inorder2 \<langle>l, x, r\<rangle> xs = (let rs = inorder2 r xs in inorder2 l (x # rs))"
using val_cong[OF inorder2_tm.simps(2), of l]
by(simp only: inorder2_def val_simps)

lemma inorder2: "inorder2 t xs = Tree.inorder2 t xs"
by(induction t xs rule: inorder2_tm.induct)(auto)

definition t_inorder2 :: "'a tree \<Rightarrow> 'a list \<Rightarrow> nat" where
"t_inorder2 t xs = time(inorder2_tm t xs)"

lemma t_inorder2_Leaf: "t_inorder2 \<langle>\<rangle> xs = 1"
by(simp add: t_inorder2_def tm_simps)

lemma t_inorder2_Node:
  "t_inorder2 \<langle>l, x, r\<rangle> xs = t_inorder2 r xs + t_inorder2 l (x # inorder2 r xs) + 1"
by(simp add: t_inorder2_def inorder2_def tm_simps split: tm.split)

lemma t_inorder2: "t_inorder2 t xs = 2*size t + 1"
by(induction t arbitrary: xs)(auto simp: t_inorder2_Leaf t_inorder2_Node)


subsubsection \<open>@{const split_min}\<close>

fun split_min_tm :: "'a tree \<Rightarrow> ('a * 'a tree) tm" where
"split_min_tm Leaf =1 return undefined" |
"split_min_tm (Node l x r) =1
  (if l = Leaf then return (x,r)
   else do { (y,l') \<leftarrow> split_min_tm l; return (y, Node l' x r)})"

definition split_min :: "'a tree \<Rightarrow> ('a * 'a tree)" where
"split_min t = val (split_min_tm t)"

lemma split_min_Node[simp,code]:
  "split_min (Node l x r) =
  (if l = Leaf then (x,r)
   else let (y,l') = split_min l in (y, Node l' x r))"
using val_cong[OF split_min_tm.simps(2)]
by(simp only: split_min_def val_simps)

definition t_split_min :: "'a tree \<Rightarrow> nat" where
"t_split_min t = time (split_min_tm t)"

lemma t_split_min_Node[simp]:
  "t_split_min (Node l x r) = (if l = Leaf then 1 else t_split_min l + 1)"
using val_cong[OF split_min_tm.simps(2)]
by(simp add: t_split_min_def tm_simps split: tm.split)

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: sorted_lems split: prod.splits if_splits)


subsubsection \<open>Balancing\<close>

fun bal_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a tree * 'a list) tm" where
"bal_tm n xs =1
  (if n=0 then return (Leaf,xs) else
  (let m = n div 2
   in do { (l, ys) \<leftarrow> bal_tm m xs;
           (r, zs) \<leftarrow> bal_tm (n-1-m) (tl ys);
           return (Node l (hd ys) r, zs)}))"

declare bal_tm.simps[simp del]

lemma bal_tm_simps:
  "bal_tm 0 xs =1 return(Leaf, xs)"
  "n > 0 \<Longrightarrow>
   bal_tm n xs =1
  (let m = n div 2
   in do { (l, ys) \<leftarrow> bal_tm m xs;
           (r, zs) \<leftarrow> bal_tm (n-1-m) (tl ys);
           return (Node l (hd ys) r, zs)})"
by(simp_all add: bal_tm.simps)

definition bal :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a tree * 'a list)" where
"bal n xs = val (bal_tm n xs)"

lemma bal_def2[code]:
"bal n xs =
  (if n=0 then (Leaf,xs) else
  (let m = n div 2;
       (l, ys) = bal m xs;
       (r, zs) = bal (n-1-m) (tl ys)
   in (Node l (hd ys) r, zs)))"
using val_cong[OF bal_tm.simps(1)]
by(simp only: bal_def val_simps)

lemma bal_simps:
  "bal 0 xs = (Leaf, xs)"
  "n > 0 \<Longrightarrow>
   bal n xs =
  (let m = n div 2;
      (l, ys) = bal m xs;
      (r, zs) = bal (n-1-m) (tl ys)
  in (Node l (hd ys) r, zs))"
by(simp_all add: bal_def2)

lemma bal_eq: "bal n xs = Balance.bal n xs"
apply(induction n xs rule: bal.induct)
apply(case_tac "n=0")
 apply(simp add: bal_simps Balance.bal_simps)
apply(simp add: bal_simps Balance.bal_simps split: prod.split)
done


definition t_bal :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
"t_bal n xs = time (bal_tm n xs)"

lemma t_bal: "t_bal n xs = 2*n+1"
unfolding t_bal_def
apply(induction n xs rule: bal_tm.induct)
apply(case_tac "n=0")
apply(simp add: bal_tm_simps)
apply(auto simp add: bal_tm_simps tm_simps split: tm.split)
subgoal premises p for n xs t1 xs1
  using p(2)[OF refl,of xs1] p(3-) by(simp)
done

definition bal_list_tm :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a tree tm" where
"bal_list_tm n xs = do { (t,_) \<leftarrow> bal_tm n xs; return t }"

definition bal_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a tree" where
"bal_list n xs = val (bal_list_tm n xs)"

lemma bal_list_def2[code]: "bal_list n xs = (let (t,ys) = bal n xs in t)"
using val_cong[OF bal_list_tm_def]
by(simp only: bal_list_def bal_def val_simps)

lemma bal_list: "bal_list n xs = Balance.bal_list n xs"
by(auto simp add: bal_list_def2 Balance.bal_list_def bal_eq split: prod.split)

definition bal_tree_tm :: "nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree tm" where
"bal_tree_tm n t =1 do { xs \<leftarrow> inorder2_tm t []; bal_list_tm n xs }"

definition bal_tree :: "nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"bal_tree n t = val (bal_tree_tm n t)"

lemma bal_tree_def2[code]:
  "bal_tree n t = (let xs = inorder2 t [] in bal_list n xs)"
using val_cong[OF bal_tree_tm_def, of n t]
by(simp only: bal_tree_def bal_list_def inorder2_def val_simps)

lemma bal_tree: "bal_tree n t = Balance.bal_tree n t"
by(simp add: bal_tree_def2 Balance.bal_tree_def bal_list inorder2 inorder2_inorder)

definition t_bal_tree :: "nat \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_bal_tree n xs = time (bal_tree_tm n xs)"

lemma t_bal_tree: "n = size xs \<Longrightarrow> t_bal_tree n xs = 4*n+3"
by(simp add: t_bal_tree_def bal_tree_tm_def tm_simps bal_list_tm_def
    surj_TM[OF inorder2_def t_inorder2_def] t_inorder2
    surj_TM[OF bal_def t_bal_def] t_bal size1_size
    split: tm.split prod.split)


subsection "Naive implementation (insert only)"

fun node :: "bool \<Rightarrow> 'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"node twist s x t = (if twist then Node t x s else Node s x t)"

datatype 'a up = Same | Bal "'a tree" | Unbal "'a tree"

locale RBTi1 =
fixes bal_i :: "nat \<Rightarrow> nat \<Rightarrow> bool"
assumes bal_i_balance:
  "bal_i (size t) (height (balance_tree (t::'a::linorder tree)))"
assumes mono_bal_i: "\<lbrakk> bal_i n h; n \<le> n'; h' \<le> h \<rbrakk> \<Longrightarrow> bal_i n' h'"
begin

subsubsection \<open>Functions\<close>

definition up :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a up \<Rightarrow> 'a up" where
"up x sib twist u = (case u of Same \<Rightarrow> Same |
   Bal t \<Rightarrow> Bal(node twist t x sib) |
   Unbal t \<Rightarrow> let t' = node twist t x sib; h' = height t'; n' = size t'
              in if bal_i n' h' then Unbal t'
                 else Bal(balance_tree t'))"

declare up_def[simp]

fun ins :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a up" where
"ins n d x Leaf =
  (if bal_i (n+1) (d+1) then Bal (Node Leaf x Leaf) else Unbal (Node Leaf x Leaf))" |
"ins n d x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> up y r False (ins n (d+1) x l) |
     EQ \<Rightarrow> Same |
     GT \<Rightarrow> up  y l True (ins n (d+1) x r))"

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x t =
  (case ins (size t) 0 x t of
    Same \<Rightarrow> t |
    Bal t' \<Rightarrow> t')"
    (* Unbal unreachable *)


subsubsection \<open>Functional Correctness and Invariants\<close>

lemma height_balance: "\<lbrakk> \<not> bal_i (size t) h \<rbrakk>
  \<Longrightarrow> height (balance_tree (t::'a::linorder tree)) < h"
by (meson bal_i_balance leI le_refl mono_bal_i)

lemma mono_bal_i':
  "\<lbrakk> ASSUMPTION(bal_i n h); n \<le> n'; h' \<le> h \<rbrakk> \<Longrightarrow> bal_i n' h'"
unfolding ASSUMPTION_def by(rule mono_bal_i)

lemma inorder_ins: "sorted(inorder t) \<Longrightarrow>
  (ins n d x t = Same \<longrightarrow> ins_list x (inorder t) = inorder t) \<and>
  (ins n d x t = Bal t' \<longrightarrow> ins_list x (inorder t) = inorder t') \<and>
  (ins n d x t = Unbal t' \<longrightarrow> ins_list x (inorder t) = inorder t')"
by(induction t arbitrary: d t')
  (auto simp: ins_list_simps bal.simps[of "Suc 0"] bal.simps[of 0]
        split!: if_splits prod.splits up.splits)

lemma ins_size:
shows "ins n d x t = Bal t' \<Longrightarrow> size t' = size t + 1"
and "ins n d x t = Unbal t' \<Longrightarrow> size t' = size t + 1"
by(induction t arbitrary: d t')
  (auto split: if_splits up.splits)

lemma ins_height:
shows "ins n d x t = Bal t' \<Longrightarrow> height t' \<le> height t + 1"
and "ins n d x t = Unbal t' \<Longrightarrow> height t \<le> height t' \<and> height t' \<le> height t + 1"
proof(induction t arbitrary: d t')
  case Leaf
  { case 1 thus ?case by (auto split: if_splits)
  next
    case 2 thus ?case by (auto split: if_splits)
  }
next
  case (Node l y r)
  { case 1
    consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y" by(metis less_linear)
    thus ?case
    proof cases
      case ls
      show ?thesis
      proof (cases "ins n (d+1) x l")
        case Same thus ?thesis using 1 ls by (simp)
      next
        case Bal
        thus ?thesis
          using 1 ls by (auto simp: max_def dest: Node)
      next
        case (Unbal l')
        let ?t = "Node l' y r" let ?h = "height ?t" let ?n = "size ?t"
        have "\<not> bal_i ?n ?h" using 1 ls Unbal by (auto)
        thus ?thesis
          using 1 ls Unbal Node.IH(2)[OF Unbal]
            height_balance[of ?t "height ?t"]
          by(auto)
      qed
    next
      case eq
      thus ?thesis using 1 by(simp)
    next
      case gr
      show ?thesis
      proof (cases "ins n (d+1) x r")
        case Same
        thus ?thesis using 1 gr by (simp)
      next
        case Bal
        thus ?thesis
          using 1 gr by (auto simp: max_def dest: Node)
      next
        case (Unbal r')
        let ?t = "Node l y r'" let ?h = "height ?t" let ?n = "size ?t"
        have "\<not> bal_i ?n ?h" using 1 gr Unbal by (auto)
        thus ?thesis
          using 1 gr Unbal Node.IH(4)[OF Unbal]
            height_balance[of ?t "height ?t"]
          by(auto)
      qed
    qed
  next
    case 2
    thus ?case
      by(auto simp: max_def dest: Node split: if_splits up.splits)
  }
qed

lemma bal_i0: "bal_i 0 0"
using bal_i_balance[of Leaf]
by(auto simp add: Balance.bal_tree_def balance_tree_def Balance.bal_list_def Balance.bal_simps)

lemma bal_i1: "bal_i 1 1"
using bal_i_balance[of "Node Leaf undefined Leaf"]
by(auto simp add: balance_tree_def Balance.bal_tree_def Balance.bal_list_def Balance.bal_simps)

lemma bal_i_ins_Unbal:
  assumes "ins n d x t = Unbal t'" shows "bal_i (size t') (height t')"
proof(cases t)
  case Leaf thus ?thesis
    using assms bal_i1 by(auto split: if_splits)
next
  case Node thus ?thesis
    using assms by(auto split: if_splits up.splits)
qed

lemma unbal_ins_Unbal:
  "ins n d x t = Unbal t' \<Longrightarrow> \<not> bal_i (n+1) (height t' + d)"
proof(induction t arbitrary: d t')
  case Leaf thus ?case
    by (auto split: if_splits)
next
  case Node thus ?case
    by(fastforce simp: mono_bal_i' split: if_splits up.splits)
qed

lemma height_Unbal_l: assumes "ins n (d+1) x l = Unbal l'"
  "bal_i n (height \<langle>l, y, r\<rangle> + d)"
shows "height r < height l'" (is ?P)
proof(rule ccontr)
  assume "\<not> ?P"
  thus False
    using assms(2) unbal_ins_Unbal[OF assms(1)]
    by (auto simp: mono_bal_i')
qed
lemma height_Unbal_r: assumes "ins n (d+1) x r = Unbal r'"
  "bal_i n (height \<langle>l, y, r\<rangle> + d)"
shows "height l < height r'" (is ?P)
proof(rule ccontr)
  assume "\<not> ?P"
  thus False
    using assms(2) unbal_ins_Unbal[OF assms(1)]
    by (auto simp: mono_bal_i' split: if_splits)
qed
  
lemma ins_bal_i_Bal:
  "\<lbrakk> ins n d x t = Bal t'; bal_i n (height t + d) \<rbrakk>
  \<Longrightarrow> bal_i (n+1) (height t' + d)"
proof(induction t arbitrary: d t')
  case Leaf
  thus ?case
    by (auto split: if_splits)
next
  case (Node l y r)
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    have 2: "bal_i n (height l + (d + 1))"
      using Node.prems(2) by (simp add: mono_bal_i')
    show ?thesis
    proof (cases "ins n (d+1) x l")
      case Same
      thus ?thesis
        using Node.prems ls by (simp)
    next
      case Bal
      thus ?thesis
        using Node.prems ls ins_height(1)[OF Bal] Node.IH(1)[OF Bal 2]
        by (auto simp: max_def mono_bal_i')
    next
      case (Unbal l')
      let ?t = "Node l' y r" let ?h = "height ?t" let ?n = "size ?t"
      have "\<not> bal_i ?n ?h" using Node.prems ls Unbal by (auto)
      thus ?thesis
        using Node.prems ls Unbal height_balance[of ?t "height ?t"]
          ins_height(2)[OF Unbal]
        by (auto simp: mono_bal_i')
    qed
  next
    case eq
    thus ?thesis
      using Node.prems by(simp)
  next
    case gr
    have 2: "bal_i n (height r + (d + 1))"
      using Node.prems(2) by(simp add: mono_bal_i')
    show ?thesis
    proof (cases "ins n (d+1) x r")
      case Same
      thus ?thesis
        using Node.prems gr by (simp)
    next
      case Bal
      thus ?thesis
        using Node.prems gr ins_height(1)[OF Bal] Node.IH(2)[OF Bal 2]
        by (auto simp: max_def mono_bal_i')
    next
      case (Unbal r')
      let ?t = "Node l y r'" let ?h = "height ?t" let ?n = "size ?t"
      have "\<not> bal_i ?n ?h" using Node.prems gr Unbal by (auto)
      thus ?thesis
        using Node.prems gr Unbal
          height_balance[of ?t "height ?t"] ins_height(2)[OF Unbal]
        by (auto simp: mono_bal_i')
    qed
  qed
qed

lemma ins0_neq_Unbal: assumes "n \<ge> size t" shows "ins n 0 a t \<noteq> Unbal t'"
proof(cases t)
  case Leaf thus ?thesis using bal_i1 by(simp add: numeral_eq_Suc mono_bal_i')
next
  case Node
  thus ?thesis
    using unbal_ins_Unbal[of "n" 0 a t t'] assms
    by(auto simp: ins_size mono_bal_i' split: up.splits)
qed

lemma inorder_insert: "sorted(inorder t)
  \<Longrightarrow> inorder (insert x t) = ins_list x (inorder t)"
using ins0_neq_Unbal
by(auto simp add: insert_def inorder_ins split: prod.split up.split)

lemma bal_i_insert: assumes "bal_i (size t) (height t)"
shows "bal_i (size(insert x t)) (height(insert x t))"
proof (cases "ins (size t) 0 x t")
  case Same
  with assms show ?thesis by simp
next
  case Bal
  thus ?thesis
    using ins_bal_i_Bal[OF Bal] assms ins_size by(simp add: size1_size)
next
  case (Unbal t')
  hence False using ins0_neq_Unbal by blast
  thus ?thesis ..
qed

end (* RBTi1 *)

text \<open>This is just a test that (a simplified version of) the intended
interpretation works (so far):\<close>

interpretation Test: RBTi1 "\<lambda>n h. h \<le> log 2 (real(n + 1)) + 1"
proof (standard, goal_cases)
  case (1 t)
  have *: "log 2 (1 + real(size t)) \<ge> 0" by (simp)
  show ?case apply(simp add: height_balance_tree) using * by linarith
next
  case (2 n h n' h')
  have "real h' \<le> real h" by(simp add: 2)
  also have "\<dots> \<le> log 2 (n+1) + 1" by(rule 2)
  also have "\<dots> \<le> log 2 (n'+1) + 1" using "2"(2,3) by(simp)
  finally show ?case .
qed


subsection "Efficient Implementation (insert only)"

fun imbal :: "'a tree \<Rightarrow> nat" where
"imbal Leaf = 0" |
"imbal (Node l _ r) = nat(abs(int(size l) - int(size r))) - 1"

declare imbal.simps [simp del]

lemma imbal0_if_wbalanced: "wbalanced t \<Longrightarrow> imbal t = 0"
by (cases t) (auto simp add: imbal.simps)

text \<open>The degree of imbalance allowed:
how far from the perfect balance may the tree degenerate.\<close>

axiomatization c :: real where
c1: "c > 1"

definition bal_log :: "'a tree \<Rightarrow> bool" where
"bal_log t = (height t \<le> ceiling(c * log 2 (size1 t)))"

fun hchild :: "'a tree \<Rightarrow> 'a tree" where
"hchild (Node l _ r) = (if height l \<le> height r then r else l)"

lemma size1_imbal:
  assumes "\<not> bal_log t" and "bal_log (hchild t)" and "t \<noteq> Leaf"
  shows "imbal t > (2 powr (1 - 1/c) - 1) * size1 (t) - 1"
proof -
  obtain l x r where t: "t = Node l x r"
    using \<open>t \<noteq> Leaf\<close> by(auto simp: neq_Leaf_iff)
  let ?sh = "hchild t"
  have *: "c * log 2 (size1 ?sh) \<ge> 0"
    using c1 apply(simp add: zero_le_mult_iff)
    using size1_ge0[of ?sh] by linarith
  have "(2 powr (1 - 1/c) - 1) * size1 t - 1
    = 2 powr (1 - 1/c) * size1 t - size1 t - 1"
    by (simp add: ring_distribs)
  also have "\<dots> = 2 * (2 powr (- 1/c) * size1 t) - size1 t - 1"
    using c1 by(simp add: powr_minus powr_add[symmetric] field_simps)
  also have "2 powr (- 1/c) * size1 t < size1 ?sh"
  proof -
    have "ceiling(c * log 2 (size1 t)) < ceiling (c * log 2 (size1 ?sh)) + 1"
    proof -
      have "ceiling(c * log 2 (size1 t)) < height t"
        using assms(1) by (simp add: bal_log_def)
      also have "\<dots> = height(?sh) + 1" by(simp add: t max_def)
      finally show ?thesis
        using assms(2) unfolding bal_log_def by linarith
    qed
    hence "c * log 2 (size1 t) < c * log 2 (size1 ?sh) + 1"
      using * by linarith
    hence "log 2 (size1 t) - 1/c < log 2 (size1 ?sh)"
      using c1 by(simp add: field_simps)
    from powr_less_mono[OF this, of 2] show ?thesis
      by (simp add: powr_diff powr_minus field_simps)
  qed
  also have "2 * real(size1 ?sh) - size1 t - 1
           = real(size1 ?sh) - (real(size1 t) - size1 ?sh) - 1"
    by (simp add: assms(1))
  also have "\<dots> \<le> imbal t"
    by (auto simp add: t assms(1) imbal.simps size1_size)
  finally show ?thesis by simp
qed

text\<open>The following key lemma shows that \<open>imbal\<close> is a suitable potential because
it can pay for the linear-time cost of restructuring a tree
that is not balanced but whose higher son is.\<close>

lemma size1_imbal2:
  assumes "\<not> bal_log t" and "bal_log (hchild t)" and "t \<noteq> Leaf"
  shows "size1 (t) < (2 powr (1/c) / (2 - 2 powr (1/c))) * (imbal t + 1)"
proof -
  have *: "2 powr (1 - 1 / c) - 1 > 0"
    using c1 by(simp add: field_simps log_less_iff[symmetric])
  have "(2 powr (1 - 1 / c) - 1) * size1 t < imbal t + 1"
    using size1_imbal[OF assms] by linarith
  hence "size1 t < 1 / (2 powr (1 - 1 / c) - 1) * (imbal t + 1)"
    using * by(simp add: field_simps)
  also have "1 / (2 powr (1 - 1 / c) - 1) = 2 powr (1/c) / (2 - 2 powr (1/c))"
  proof -
    have "1 / (2 powr (1 - 1 / c) - 1) = 1 / (2 / 2 powr (1/c) - 1)"
      by(simp add: powr_diff)
    also have "\<dots> = 2 powr (1/c) / (2 - 2 powr (1/c))"
      by(simp add: field_simps)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

datatype 'a up2 = Same2 | Bal2 "'a tree" | Unbal2 "'a tree" nat nat

type_synonym 'a rbt1 = "'a tree * nat"

text \<open>An implementation where size and height are computed incrementally:\<close>

locale RBTi2 = RBTi1 +
fixes e :: real
assumes e0: "e > 0"
assumes imbal_size:
  "\<lbrakk> \<not> bal_i (size t) (height t);
     bal_i (size(hchild t)) (height(hchild t));
     t \<noteq> Leaf \<rbrakk>
    \<Longrightarrow> e * (imbal t + 1) \<ge> size1 (t::'a::linorder tree)"
begin

subsubsection \<open>Functions\<close>

definition up2 :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a up2 \<Rightarrow> 'a up2" where
"up2 x sib twist u = (case u of Same2 \<Rightarrow> Same2 |
   Bal2 t \<Rightarrow> Bal2(node twist t x sib) |
   Unbal2 t n1 h1 \<Rightarrow>
     let n2 = size sib; h2 = height sib;
         t' = node twist t x sib;
         n' = n1+n2+1; h' = max h1 h2 + 1
     in if bal_i n' h' then Unbal2 t' n' h'
        else Bal2(bal_tree n' t'))"

declare up2_def[simp]

text\<open>@{const up2} traverses \<open>sib\<close> twice; unnecessarily, as it turns out: \<close>

definition up3_tm :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a up2 \<Rightarrow> 'a up2 tm" where
"up3_tm x sib twist u =1 (case u of
   Same2 \<Rightarrow> return Same2 |
   Bal2 t \<Rightarrow> return (Bal2(node twist t x sib)) |
   Unbal2 t n1 h1 \<Rightarrow>
     do { n2 \<leftarrow> size_tree_tm sib;
          let t' = node twist t x sib;
              n' = n1+n2+1;
              h' = h1 + 1
          in if bal_i n' h' then return (Unbal2 t' n' h')
             else do { t'' \<leftarrow> bal_tree_tm n' t';
                       return (Bal2 t'')}})"

definition up3 :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a up2 \<Rightarrow> 'a up2" where
"up3 a sib twist u = val (up3_tm a sib twist u)"

lemma up3_def2[simp,code]:
  "up3 x sib twist u = (case u of
  Same2 \<Rightarrow> Same2 |
  Bal2 t \<Rightarrow> Bal2 (node twist t x sib) |
  Unbal2 t n1 h1 \<Rightarrow>
     let n2 = size_tree sib; t' = node twist t x sib; n' = n1 + n2 + 1; h' = h1 + 1
     in if bal_i n' h' then Unbal2 t' n' h'
        else let t'' = bal_tree n' t' in Bal2 t'')"
using val_cong[OF up3_tm_def]
by(simp only: up3_def size_tree_def bal_tree_def val_simps up2.case_distrib[of val])

definition t_up3 :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a up2 \<Rightarrow> nat" where
"t_up3 x sib twist u = time (up3_tm x sib twist u)"

lemma t_up3_def2[simp]: "t_up3 x sib twist u =
 (case u of Same2 \<Rightarrow> 1 |
   Bal2 t \<Rightarrow> 1 |
   Unbal2 t n1 h1 \<Rightarrow>
     let n2 = size sib; t' = node twist t x sib; h' = h1 + 1; n' = n1+n2+1
     in 2 * size sib + 1 + (if bal_i n' h' then 1 else t_bal_tree n' t' + 1))"
by(simp add: t_up3_def up3_tm_def surj_TM[OF size_tree_def t_size_tree_def]
    size_tree t_size_tree t_bal_tree_def tm_simps split: tm.split up2.split)

fun ins2 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a up2" where
"ins2 n d x Leaf =
  (if bal_i (n+1) (d+1) then Bal2 (Node Leaf x Leaf) else Unbal2 (Node Leaf x Leaf) 1 1)" |
"ins2 n d x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> up2 y r False (ins2 n (d+1) x l) |
     EQ \<Rightarrow> Same2 |
     GT \<Rightarrow> up2 y l True (ins2 n (d+1) x r))"


text\<open>Definition of timed final insertion function:\<close>

fun ins3_tm :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a up2 tm" where
"ins3_tm n d x Leaf =1
   (if bal_i (n+1) (d+1) then return(Bal2 (Node Leaf x Leaf))
   else return(Unbal2 (Node Leaf x Leaf) 1 1))" |
"ins3_tm n d x (Node l y r) =1
  (case cmp x y of
     LT \<Rightarrow> do {l' \<leftarrow> ins3_tm n (d+1) x l; up3_tm y r False l'} |
     EQ \<Rightarrow> return Same2 |
     GT \<Rightarrow> do {r' \<leftarrow> ins3_tm n (d+1) x r; up3_tm y l True r'})"

definition ins3 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a up2" where
"ins3 n d x t = val(ins3_tm n d x t)"

lemma ins3_Leaf[simp,code]:
  "ins3 n d x Leaf =
  (if bal_i (n+1) (d+1) then Bal2 (Node Leaf x Leaf) else Unbal2 (Node Leaf x Leaf) 1 1)"
using val_cong[OF ins3_tm.simps(1)]
by(simp only: ins3_def val_simps cmp_val.case_distrib[of val])

lemma ins3_Node[simp,code]:
  "ins3 n d x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> let l' = ins3 n (d+1) x l in up3 y r False l' |
     EQ \<Rightarrow> Same2 |
     GT \<Rightarrow> let r' = ins3 n (d+1) x r in up3 y l True r')"
using val_cong[OF ins3_tm.simps(2)]
by(simp only: ins3_def up3_def val_simps cmp_val.case_distrib[of val])

definition t_ins3 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_ins3 n d x t = time(ins3_tm n d x t)"

lemma t_ins3_Leaf[simp]: "t_ins3 n d x Leaf = 1"
by(simp add: tm_simps t_ins3_def)

lemma t_ins3_Node[simp]: "t_ins3 n d x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> t_ins3 n (d+1) x l + t_up3 y r False (ins3 n (d+1) x l) |
     EQ \<Rightarrow> 0 |
     GT \<Rightarrow> t_ins3 n (d+1) x r + t_up3 y l True (ins3 n (d+1) x r)) + 1"
apply(subst t_ins3_def)
apply(subst ins3_tm.simps)
apply(auto simp add: tm_simps surj_TM[OF ins3_def t_ins3_def] surj_TM[OF up3_def t_up3_def]
           simp del: t_up3_def2 split: tm.splits up2.split)
done
(*FIXME simp del: t_up3_def2 t_ins3_Node[simp] *)

fun insert2 :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1" where
"insert2 x (t,n) =
  (case ins2 n 0 x t of
     Same2 \<Rightarrow> (t,n) |
     Bal2 t' \<Rightarrow> (t',n+1))"
  (* Unbal unreachable *)

fun insert3_tm :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1 tm" where
"insert3_tm x (t,n) =1
  (do { u \<leftarrow> ins3_tm n 0 x t;
        case u of
          Same2 \<Rightarrow> return (t,n) |
          Bal2 t' \<Rightarrow> return (t',n+1) |
          Unbal2 _ _ _ \<Rightarrow> return undefined })"
  (* Unbal unreachable *)

definition insert3 :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1" where
"insert3 a t = val (insert3_tm a t)"

lemma insert3_def2[simp]: "insert3 x (t,n) =
  (let t' = ins3 n 0 x t in
   case t' of
     Same2 \<Rightarrow> (t,n) |
     Bal2 t' \<Rightarrow> (t',n+1))"
using val_cong[OF insert3_tm.simps(1)]
by(simp only: insert3_def ins3_def val_simps up2.case_distrib[of val])

definition t_insert3 :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> nat" where
"t_insert3 a t = time (insert3_tm a t)"

lemma t_insert3_def2: "t_insert3 x (t,n) = t_ins3 n 0 x t + 1"
by(simp add: t_insert3_def ins3_def t_ins3_def tm_simps split: tm.split up2.split)


subsubsection "Equivalence Proofs"

lemma ins_ins2:
shows "ins2 n d x t = Same2 \<Longrightarrow> ins n d x t = Same"
and "ins2 n d x t = Bal2 t' \<Longrightarrow> ins n d x t = Bal t'"
and "ins2 n d x t = Unbal2 t' n' h'
  \<Longrightarrow> ins n d x t = Unbal t' \<and> n' = size t' \<and> h' = height t'"
by(induction t arbitrary: d t' n' h')
  (auto simp: size_height add.commute max.commute balance_tree_def bal_tree
    split: if_splits up2.splits prod.splits)

lemma ins2_ins:
shows "ins n d x t = Same \<Longrightarrow> ins2 n d x t = Same2"
and "ins n d x t = Bal t' \<Longrightarrow> ins2 n d x t = Bal2 t'"
and "ins n d x t = Unbal t'
  \<Longrightarrow> ins2 n d x t = Unbal2 t' (size t') (height t')"
by(induction t arbitrary: d t')
  (auto simp: size_height add.commute max.commute balance_tree_def bal_tree
    split: if_splits up.splits prod.splits)

corollary ins2_iff_ins:
shows "ins2 n d x t = Same2 \<longleftrightarrow> ins n d x t = Same"
and "ins2 n d x t = Bal2 t' \<longleftrightarrow> ins n d x t = Bal t'"
and "ins2 n d x t = Unbal2 t' n' h' \<longleftrightarrow>
  ins n d x t = Unbal t' \<and> n' = size t' \<and> h' = height t'"
  using ins2_ins(1) ins_ins2(1) apply blast
 using ins2_ins(2) ins_ins2(2) apply blast
using ins2_ins(3) ins_ins2(3) by blast

lemma ins3_ins2:
  "bal_i n (height t + d) \<Longrightarrow> ins3 n d x t = ins2 n d x t"
proof(induction t arbitrary: d)
  case Leaf
  thus ?case by (auto)
next
  case (Node l y r)
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    have *: "bal_i n (height l + (d + 1))"
      using Node.prems by (simp add: mono_bal_i')
    note IH = Node.IH(1)[OF *]
    show ?thesis
    proof (cases "ins2 n (d+1) x l")
      case Same2
      thus ?thesis
        using IH ls by (simp)
    next
      case Bal2
      thus ?thesis
        using IH ls by (simp)
    next
      case (Unbal2 l' nl' hl')
      let ?t' = "Node l' y r" let ?h' = "height ?t'" let ?n' = "size ?t'"
      have ins: "ins n (d+1) x l = Unbal l'"
        and "nl' = size l' \<and> hl' = height l'"
        using ins2_iff_ins(3)[THEN iffD1, OF Unbal2] by auto
      thus ?thesis
        using ls IH Unbal2 height_Unbal_l[OF ins Node.prems(1)]
        by(auto simp add: size_height mono_bal_i size_tree)
    qed
  next
    case eq
    thus ?thesis
      using Node.prems by(simp)
  next
    case gr
    have *: "bal_i n (height r + (d + 1))"
      using Node.prems by (simp add: mono_bal_i')
    note IH = Node.IH(2)[OF *]
    show ?thesis
    proof (cases "ins2 n (d+1) x r")
      case Same2
      thus ?thesis
        using IH gr by (simp)
    next
      case Bal2
      thus ?thesis
        using IH gr by (simp)
    next
      case (Unbal2 r' nr' hr')
      let ?t' = "Node r' y r" let ?h' = "height ?t'" let ?n' = "size ?t'"
      have ins: "ins n (d+1) x r = Unbal r'"
        and "nr' = size r' \<and> hr' = height r'"
        using ins2_iff_ins(3)[THEN iffD1, OF Unbal2] by auto
      thus ?thesis
        using gr IH Unbal2 height_Unbal_r[OF ins Node.prems]
        by(auto simp add: size_height mono_bal_i size_tree)
    qed
  qed
qed

lemma insert2_insert:
  "insert2 x (t,size t) = (t',n') \<longleftrightarrow> t' = insert x t \<and> n' = size t'"
using ins0_neq_Unbal
by(auto simp: ins2_iff_ins ins_size split: up2.split up.split)

lemma insert3_insert2:
  "bal_i n (height t) \<Longrightarrow> insert3 x (t,n) = insert2 x (t,n)"
by(simp add: ins3_ins2 split: up2.split)

subsubsection \<open>Amortized Complexity\<close>

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l x r) = 6 * e * imbal (Node l x r) + \<Phi> l + \<Phi> r"

lemma \<Phi>_nn: "\<Phi> t \<ge> 0"
by(induction t) (use e0 in auto)

lemma \<Phi>_sum_mset: "\<Phi> t = (\<Sum>s \<in># subtrees_mset t. 6*e*imbal s)"
proof(induction t)
  case Leaf show ?case by(simp add: imbal.simps)
next
  case Node thus ?case by(auto)
qed

lemma \<Phi>_wbalanced: assumes "wbalanced t" shows "\<Phi> t = 0"
proof -
  have "\<Phi> t = 6*e * (\<Sum>s\<in>#subtrees_mset t. real (imbal s))"
    by(simp add: \<Phi>_sum_mset sum_mset_distrib_left)
  also have "\<dots> = (6*e) * real(\<Sum>s\<in>#subtrees_mset t. imbal s)"
    using e0 by (simp add: multiset.map_comp o_def)
  also have "\<dots> = 0" using e0 assms
    by(simp add: imbal0_if_wbalanced wbalanced_subtrees del: of_nat_sum_mset)
  finally show ?thesis .
qed

lemma imbal_ins_Bal: "ins n d x t = Bal t' \<Longrightarrow>
 real(imbal (node tw t' y s)) - imbal (node tw t y s) \<le> 1"
apply(drule ins_size)
apply(auto simp add: size1_size imbal.simps)
done

lemma imbal_ins_Unbal: "ins n d x t = Unbal t' \<Longrightarrow>
 real(imbal (node tw t' y s)) - imbal (node tw t y s) \<le> 1"
apply(drule ins_size)
apply(auto simp add: size1_size imbal.simps)
done

lemma t_ins3_Same:
  "ins3 n d x t = Same2 \<Longrightarrow> t_ins3 n d x t \<le> 2 * height t + 1"
apply(induction t arbitrary: d)
 apply simp
apply (force simp: max_def split!: up2.splits if_splits)
done

lemma t_ins3_Unbal:
  "\<lbrakk> ins3 n d x t = Unbal2 t' n' h';  bal_i n (height t + d) \<rbrakk> \<Longrightarrow>
  t_ins3 n d x t \<le> 2 * size t + 1 + height t"
apply(induction t arbitrary: d t' n' h')
 apply simp
apply (auto simp: ins3_ins2 ins2_iff_ins ins_height size_tree size1_size max_def mono_bal_i'
         dest: unbal_ins_Unbal split!: up2.splits if_splits)
   apply (fastforce simp: mono_bal_i')+
done

lemma Phi_diff_Unbal:
  "\<lbrakk> ins3 n d x t = Unbal2 t' n' h';  bal_i n (height t + d) \<rbrakk> \<Longrightarrow>
  \<Phi> t' - \<Phi> t \<le> 6*e * height t"
proof(induction t arbitrary: d t' n' h')
  case Leaf thus ?case
    by (auto simp: imbal.simps split: if_splits)
next
  case (Node l y r)
  have ins: "ins n d x \<langle>l, y, r\<rangle> = Unbal t'"
    using Node.prems(1)
    by (simp only: ins2_iff_ins(3) ins3_ins2[OF Node.prems(2)])
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    with Node.prems obtain l' nl' nh' where rec: "ins3 n (d+1) x l = Unbal2 l' nl' nh'"
      and t': "t' = Node l' y r"
      by (auto split: up2.splits if_splits)
    have bal: "bal_i n (height l + (d+1))"
      using Node.prems(2) by (simp add: mono_bal_i' split: if_splits)
    have rec': "ins n (d+1) x l = Unbal l'"
      using rec ins_ins2(3) ins3_ins2[OF bal] by simp
    have "\<Phi> t' - \<Phi> \<langle>l,y,r\<rangle> = 6*e*imbal\<langle>l',y,r\<rangle> - 6*e*imbal\<langle>l,y,r\<rangle> + \<Phi> l' - \<Phi> l"
      using t' by simp
    also have "\<dots> = 6*e * (real(imbal\<langle>l',y,r\<rangle>) - imbal\<langle>l,y,r\<rangle>) + \<Phi> l' - \<Phi> l"
      by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e + \<Phi> l' - \<Phi> l"
      using imbal_ins_Unbal[OF rec', of False y r] e0 t' by (simp)
    also have "\<dots> \<le> 6*e * (height l + 1)"
      using Node.IH(1)[OF rec bal] by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e * height \<langle>l, y, r\<rangle>"
      using e0 by(simp del: times_divide_eq_left)
    finally show ?thesis .
  next
    case eq
    thus ?thesis using Node.prems by(simp)
  next
    case gr
    with Node.prems obtain r' rn' rh' where rec: "ins3 n (d+1) x r = Unbal2 r' rn' rh'"
      and t': "t' = Node l y r'"
      by (auto split: up2.splits if_splits)
    have bal: "bal_i n (height r + (d+1))"
      using Node.prems(2) by (simp add: mono_bal_i' split: if_splits)
    have rec': "ins n (d+1) x r = Unbal r'"
      using rec ins_ins2(3) ins3_ins2[OF bal] by simp
    have "\<Phi> t' - \<Phi> \<langle>l,y,r\<rangle> = 6*e*imbal\<langle>l,y,r'\<rangle> - 6*e*imbal\<langle>l,y,r\<rangle> + \<Phi> r' - \<Phi> r"
      using t' by simp
    also have "\<dots> = 6*e * (real(imbal\<langle>l,y,r'\<rangle>) - imbal\<langle>l,y,r\<rangle>) + \<Phi> r' - \<Phi> r"
      by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e + \<Phi> r' - \<Phi> r"
      using imbal_ins_Unbal[OF rec', of True y l] e0 t'
      by (simp)
    also have "\<dots> \<le> 6*e * (height r + 1)"
      using Node.IH(2)[OF rec bal] by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e * height \<langle>l, y, r\<rangle>"
      using e0 by(simp del: times_divide_eq_left)
    finally show ?thesis .
  qed
qed

lemma amor_Unbal:
  "\<lbrakk> ins3 n d x t = Unbal2 t' n' h';  bal_i n (height t + d) \<rbrakk> \<Longrightarrow> 
  t_ins3 n d x t + \<Phi> t' - \<Phi> t \<le> 2*size1 t + (6*e + 1) * height t"
apply(frule (1) t_ins3_Unbal)
apply(drule (1) Phi_diff_Unbal)
by(simp add: ring_distribs size1_size)

lemma t_ins3_Bal:
  "\<lbrakk> ins3 n d x t = Bal2 t'; bal_i n (height t + d) \<rbrakk>
  \<Longrightarrow> t_ins3 n d x t + \<Phi> t' - \<Phi> t \<le> (6*e+2) * (height t + 1)"
proof(induction t arbitrary: d t')
  case Leaf
  thus ?case
    using e0 by (auto simp: imbal.simps split: if_splits)
next
  case (Node l y r)
  have Bal: "ins n d x \<langle>l, y, r\<rangle> = Bal t'"
    by (metis Node.prems ins3_ins2 ins_ins2(2))
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y" by(metis less_linear)
  thus ?case
  proof cases
    case ls
    have *: "bal_i n (height l + (d+1))"
      using Node.prems(2) by (simp add: mono_bal_i')
    show ?thesis
    proof (cases "ins3 n (d+1) x l")
      case Same2
      thus ?thesis using Node ls by (simp)
    next
      case (Bal2 l')
      have Bal: "ins n (d + 1) x l = Bal l'"
        using "*" Bal2 by (auto simp: ins3_ins2 ins2_iff_ins(2))
      let ?t = "Node l y r"
      let ?t' = "Node l' y r"
      from Bal2 have t': "t' = ?t'" using Node.prems ls by (simp)
      have "t_ins3 n d x ?t + \<Phi> t' - \<Phi> ?t = t_ins3 n (d+1) x l + 2 + \<Phi> t' - \<Phi> ?t"
         using ls Bal2 by simp
      also have "\<dots>
        = t_ins3 n (d+1) x l + 6*e*imbal ?t' + \<Phi> l' - 6*e*imbal ?t - \<Phi> l + 2"
        using t' by simp
      also have "\<dots>
        \<le> t_ins3 n (d+1) x l + \<Phi> l' - \<Phi> l + 6*e*imbal ?t' - 6*e*imbal ?t + 2"
        by linarith
      also have "\<dots> \<le> (6*e+2) * height l + 6*e*imbal ?t' - 6*e*imbal ?t + 6*e + 4"
        using Node.IH(1)[OF Bal2 *] by(simp add: ring_distribs)
      also have "\<dots> = (6*e+2) * height l + 6*e*(real(imbal ?t') - imbal ?t) + 6*e + 4"
        by(simp add: algebra_simps)
      also have "\<dots> \<le> (6*e+2) * height l + 6*e + 6*e + 4"
        using imbal_ins_Bal[OF Bal, of False y r] e0
        by (simp del: times_divide_eq_left)
      also have "\<dots> = (6*e+2) * (height l + 1) + 6*e + 2"
        by (simp add: ring_distribs)
      also have "\<dots> \<le> (6*e+2) * (max (height l) (height r) + 1) + 6*e + 2"
        using e0 by (simp add: mult_left_mono)
      also have "\<dots> \<le> (6*e+2) * (height ?t + 1)"
        using e0 by(simp add: field_simps)
      finally show ?thesis .
    next
      case (Unbal2 l' nl' hl')
      have Unbal: "ins n (d + 1) x l = Unbal l'"
        and inv: "nl' = size l'" "hl' = height l'"
        using  Unbal2 ins3_ins2[OF *] by(auto simp add: ins2_iff_ins(3))
      have bal_l': "bal_i (size l') (height l')"
        by(fact bal_i_ins_Unbal[OF Unbal])
      let ?t = "Node l y r" let ?h = "height ?t" let ?n = "size ?t"
      let ?t' = "Node l' y r" let ?h' = "height ?t'" let ?n' = "size ?t'"
      have bal_t': "\<not> bal_i ?n' ?h'" using ls Unbal Bal by (auto)
      hence t': "t' = balance_tree ?t'" using ls Unbal Bal by (auto)
      have hl': "height r < height l'"
        by(fact height_Unbal_l[OF Unbal Node.prems(2)])
      have "t_ins3 n d x ?t + \<Phi> t' - \<Phi> ?t = t_ins3 n d x ?t - \<Phi> ?t"
        by(simp add: t' \<Phi>_wbalanced wbalanced_balance_tree)
      also have "\<dots> =  t_ins3 n d x ?t - 6*e * imbal ?t - \<Phi> l - \<Phi> r" by simp
      also have "\<dots> \<le> t_ins3 n d x ?t - 6*e * imbal ?t - \<Phi> l"
        using \<Phi>_nn[of r] by linarith
      also have "\<dots> \<le> t_ins3 n d x ?t - 6*e * imbal ?t' - \<Phi> l + 6*e"
        using mult_left_mono[OF imbal_ins_Unbal[OF Unbal, of False y r], of "4*e"] e0
        apply (simp only: node.simps if_False ring_distribs)
        by (simp)
      also have "\<dots> \<le> real(t_ins3 n d x ?t) - 6*(size1 ?t' - e) - \<Phi> l + 6*e + 1"
        using imbal_size[OF bal_t'] hl' bal_l' by(simp add: ring_distribs)
      also have "\<dots> = real(t_ins3 n (d+1) x l) + 2*size1 l' + 4*size1 r - 4*size1 ?t' - \<Phi> l + 6*e + 6*e + 1"
        using ls Unbal2 inv bal_t' hl' by (simp add: t_bal_tree max_def size1_size)
      also have "\<dots> = real(t_ins3 n (d+1) x l) - 2*size1 l' - \<Phi> l + 6*e + 6*e + 1"
        by simp
      also have "\<dots> \<le> (6*e + 2) * height l + 6*e + 6*e"
        using amor_Unbal[OF Unbal2 *] ins_size(2)[OF Unbal] \<Phi>_nn[of l']
        by(simp add: ring_distribs size1_size)
      also have "\<dots> \<le> (6*e + 2) * (height l + 2)"
        by (simp add: ring_distribs)
      also have "\<dots> \<le> (6*e+2) * (height \<langle>l, y, r\<rangle> + 1)"
        using e0 by (simp add: mult_mono del: times_divide_eq_left)
      finally show ?thesis by linarith
    qed
  next
    case eq thus ?thesis using Node.prems by(simp)
  next
    case gr
    have *: "bal_i n (height r + (d+1))"
      using Node.prems(2) by (simp add: mono_bal_i')
    show ?thesis
    proof (cases "ins3 n (d+1) x r")
      case Same2
      thus ?thesis using Node gr by (simp)
    next
      case (Bal2 r')
      have Bal: "ins n (d + 1) x r = Bal r'"
        using "*" Bal2 by (auto simp: ins3_ins2 ins2_iff_ins(2))
      let ?t = "Node l y r"
      let ?t' = "Node l y r'"
      from Bal2 have t': "t' = ?t'" using Node.prems gr by (simp)
      have "t_ins3 n d x ?t + \<Phi> t' - \<Phi> ?t = t_ins3 n (d+1) x r + 2 + \<Phi> t' - \<Phi> ?t"
         using gr Bal2 by simp
      also have "\<dots>
        = t_ins3 n (d+1) x r + 6*e*imbal ?t' + \<Phi> r' - 6*e*imbal ?t - \<Phi> r + 2"
        using t' by simp
      also have "\<dots>
        \<le> t_ins3 n (d+1) x r + \<Phi> r' - \<Phi> r + 6*e*imbal ?t' - 6*e*imbal ?t + 2"
        by linarith
      also have "\<dots> \<le> (6*e+2) * height r + 6*e*imbal ?t' - 6*e*imbal ?t + 6*e + 4"
        using Node.IH(2)[OF Bal2 *] by(simp add: ring_distribs)
      also have "\<dots> = (6*e+2) * height r + 6*e*(real(imbal ?t') - imbal ?t) + 6*e + 4"
        by(simp add: algebra_simps)
      also have "\<dots> \<le> (6*e+2) * height r + 6*e + 6*e + 4"
        using imbal_ins_Bal[OF Bal, of True y l] e0
        by (simp del: times_divide_eq_left)
      also have "\<dots> = (6*e+2) * (height r + 1) + 6*e + 2"
        by (simp add: ring_distribs)
      also have "\<dots> \<le> (6*e+2) * (max (height l) (height r) + 1) + 6*e + 2"
        using e0 by (simp add: mult_left_mono)
      also have "\<dots> = (6*e+2) * (height ?t + 1)"
        using e0 by(simp add: field_simps)
      finally show ?thesis .
    next
      case (Unbal2 r' nr' hr')
      have Unbal: "ins n (d + 1) x r = Unbal r'"
        and inv: "nr' = size r'" "hr' = height r'"
        using  Unbal2 ins3_ins2[OF *] by(auto simp add: ins2_iff_ins(3))
      have bal_r': "bal_i (size r') (height r')"
        by(fact bal_i_ins_Unbal[OF Unbal])
      let ?t = "Node l y r" let ?h = "height ?t" let ?n = "size ?t"
      let ?t' = "Node l y r'" let ?h' = "height ?t'" let ?n' = "size ?t'"
      have bal_t': "\<not> bal_i ?n' ?h'" using gr Unbal Bal by (auto)
      hence t': "t' = balance_tree ?t'" using gr Unbal Bal by (auto)
      have hr': "height l < height r'"
        by(fact height_Unbal_r[OF Unbal Node.prems(2)])
      have "t_ins3 n d x ?t + \<Phi> t' - \<Phi> ?t = t_ins3 n d x ?t - \<Phi> ?t"
        by(simp add: t' \<Phi>_wbalanced wbalanced_balance_tree)
      also have "\<dots> =  t_ins3 n d x ?t - 6*e * imbal ?t - \<Phi> r - \<Phi> l" by simp
      also have "\<dots> \<le> t_ins3 n d x ?t - 6*e * imbal ?t - \<Phi> r"
        using \<Phi>_nn[of l] by linarith
      also have "\<dots> \<le> t_ins3 n d x ?t - 6*e * imbal ?t' - \<Phi> r + 6*e"
        using mult_left_mono[OF imbal_ins_Unbal[OF Unbal, of True y l], of "4*e"] e0
        apply (simp only: node.simps if_True ring_distribs)
        by (simp)
      also have "\<dots> \<le> real(t_ins3 n d x ?t) - 6*(size1 ?t' - e) - \<Phi> r + 6*e + 1"
        using imbal_size[OF bal_t'] hr' bal_r' by (simp add: ring_distribs)
      also have "\<dots> = real(t_ins3 n (d+1) x r) + 2*size1 r' + 4*size1 l - 4*size1 ?t' - \<Phi> r + 6*e + 6*e + 1"
        using gr Unbal2 inv bal_t' hr' by (simp add: t_bal_tree max_def size1_size add_ac)
      also have "\<dots> = real(t_ins3 n (d+1) x r) - 2*size1 r' - \<Phi> r + 6*e + 6*e + 1"
        by simp
      also have "\<dots> \<le> (6*e + 2) * height r + 6*e + 6*e"
        using amor_Unbal[OF Unbal2 *] ins_size(2)[OF Unbal] \<Phi>_nn[of r']
        by(simp add: ring_distribs size1_size)
      also have "\<dots> \<le> (6*e + 2) * (height r + 2)"
        by (simp add: ring_distribs)
      also have "\<dots> \<le> (6*e+2) * (height \<langle>l, y, r\<rangle> + 1)"
        using e0 by (simp add: mult_mono del: times_divide_eq_left)
      finally show ?thesis by linarith
    qed
  qed
qed

lemma t_insert3_amor: assumes "n = size t" "bal_i (size t) (height t)"
  "insert3 a (t,n) = (t',n')"
shows "t_insert3 a (t,n) + \<Phi> t' - \<Phi> t \<le> (6*e+2) * (height t + 1) + 1"
proof (cases "ins3 (size t) 0 a t")
  case Same2
  have *: "5*e * real (height t') \<ge> 0" using e0 by simp
  show ?thesis using Same2 assms(1,3) e0 t_ins3_Same[OF Same2]
    apply (simp add: ring_distribs t_insert3_def2) using * by linarith
next
  case (Bal2 t')
  thus ?thesis
    using t_ins3_Bal[OF Bal2] assms by(simp add: ins_size t_insert3_def2)
next
  case Unbal2
  hence False using ins0_neq_Unbal
    using assms(1,2) ins3_ins2[of n t 0] by (fastforce simp: ins2_iff_ins(3))
  thus ?thesis ..
qed

end (* RBTi2 *)

text \<open>The insert-only version is shown to have the desired logarithmic
amortized complexity. First it is shown to be linear in the height of the tree.\<close>

locale RBTi2_Amor = RBTi2
begin

fun nxt :: "'a \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1" where
"nxt x tn = insert3 x tn"

fun t\<^sub>s :: "'a \<Rightarrow> 'a rbt1 \<Rightarrow> real" where
"t\<^sub>s x tn = t_insert3 x tn"

interpretation I_RBTi2_Amor: Amortized
where init = "(Leaf,0)"
and nxt = nxt
and inv = "\<lambda>(t,n). n = size t \<and> bal_i (size t) (height t)"
and t = t\<^sub>s and \<Phi> = "\<lambda>(t,n). \<Phi> t"
and U = "\<lambda>x (t,_). (6*e+2) * (height t + 1) + 1"
proof (standard, goal_cases)
  case 1
  show ?case using bal_i0 by (simp split: prod.split)
next
  case (2 s x)
  thus ?case using insert2_insert[of x "fst s"] bal_i_insert[of "fst s"]
    by (simp del: insert2.simps insert3_def2 insert.simps
             add: insert3_insert2 split: prod.splits)
next
  case (3 s)
  thus ?case
    using \<Phi>_nn[of "fst s" ] by (auto split: prod.splits)
next
  case 4
  show ?case by(simp)
next
  case (5 s x)
  thus ?case using t_insert3_amor[of "snd s" "fst s" x]
    by (auto simp del: insert3_def2 split: prod.splits)
qed

end

text\<open>Now it is shown that a certain instantiation of \<open>bal_i\<close> that guarantees
logarithmic height satisfies the assumptions of locale @{locale RBTi2}.\<close>

interpretation I_RBTi2: RBTi2
where bal_i = "\<lambda>n h. h \<le> ceiling(c * log 2 (n+1))"
and e = "2 powr (1/c) / (2 - 2 powr (1/c))"
proof (standard, goal_cases)
  case (1 t)
  have 0: "log 2 (1 + real (size t)) \<ge> 0" by simp
  have 1: "log 2 (1 + real (size t)) \<le> c * log 2 (1 + real (size t))"
    using c1 "0" less_eq_real_def by auto
  thus ?case
    apply(simp add: height_balance_tree add_ac ceiling_mono)
    using 0 by linarith
next
  case (2 n h n' h')
  have "int h' \<le> int h" by(simp add: 2)
  also have "\<dots> \<le> ceiling(c * log 2 (real n + 1))" by(rule 2)
  also have "\<dots> \<le> ceiling(c * log 2 (real n' + 1))"
    using c1 "2"(2,3) by (simp add: ceiling_mono)
  finally show ?case .
next
  case 3
  have "2 powr (1/c) < 2 powr 1"
      using c1 by (simp only: powr_less_cancel_iff) simp
  hence "2 - 2 powr (1 / c) > 0" by simp
  thus ?case by(simp)
next
  case (4 t) thus ?case
    using size1_imbal2[of t]
    by(simp add: bal_log_def size1_size add_ac ring_distribs)
qed


subsection "Naive implementation (with delete)"

axiomatization cd :: real where
cd0: "cd > 0"

definition bal_d :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"bal_d n dl = (dl < cd*(n+1))"

lemma bal_d0: "bal_d n 0"
using cd0 by(simp add: bal_d_def)

lemma mono_bal_d: "\<lbrakk> bal_d n dl; n \<le> n' \<rbrakk> \<Longrightarrow> bal_d n' dl"
unfolding  bal_d_def
using cd0 mult_left_mono[of "real n + 1" "real n' + 1" cd]
  by linarith

locale RBTid1 = RBTi1
begin

subsubsection \<open>Functions\<close>

fun insert_d :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1" where
"insert_d x (t,dl) =
  (case ins (size t + dl) 0 x t of
    Same \<Rightarrow> t |
    Bal t' \<Rightarrow> t', dl)"
    (* Unbal unreachable *)

definition up_d :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool \<Rightarrow> 'a tree option \<Rightarrow> 'a tree option" where
"up_d x sib twist u =
  (case u of
     None \<Rightarrow> None |
     Some t \<Rightarrow> Some(node twist t x sib))"

declare up_d_def[simp]
(* FIXME tdel \<le> height
fun t_split_min :: "'a tree \<Rightarrow> nat" where
"t_split_min t = height t"
*)
fun del_tm :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree option tm" where
"del_tm x Leaf =1 return None" |
"del_tm x (Node l y r) =1
  (case cmp x y of
     LT \<Rightarrow> do { l' \<leftarrow> del_tm x l; return (up_d y r False l')} |
     EQ \<Rightarrow> if r = Leaf then return (Some l)
           else do { (a',r') \<leftarrow> split_min_tm r;
                     return (Some(Node l a' r'))} |
     GT \<Rightarrow> do { r' \<leftarrow> del_tm x r; return (up_d y l True r')})"

definition del :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree option" where
"del x t = val(del_tm x t)"

lemma del_Leaf[simp]: "del x Leaf = None"
using val_cong[OF del_tm.simps(1)]
by(simp only: del_def val_simps)

lemma del_Node[simp]: "del x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> let l' = del x l in up_d y r False l' |
     EQ \<Rightarrow> if r = Leaf then Some l
           else let (a',r') = split_min r in Some(Node l a' r') |
     GT \<Rightarrow> let r' = del x r in up_d y l True r')"
using val_cong[OF del_tm.simps(2)]
by(simp only: del_def split_min_def val_simps cmp_val.case_distrib[of val])

definition t_del :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_del x t = time(del_tm x t)"

lemma t_del_Leaf[simp]: "t_del x Leaf = 1"
by(simp add: t_del_def tm_simps)

lemma t_del_Node[simp]: "t_del x (Node l y r) =
  (case cmp x y of
     LT \<Rightarrow> t_del x l + 1 |
     EQ \<Rightarrow> if r = Leaf then 1 else t_split_min r + 1 |
     GT \<Rightarrow> t_del x r + 1)"
by(simp add: t_del_def t_split_min_def tm_simps split: tm.split prod.split)

fun delete :: "'a::linorder \<Rightarrow> 'a rbt1 \<Rightarrow> 'a rbt1" where
"delete x (t,dl) =
  (case del x t of
    None \<Rightarrow> (t,dl) |
    Some t' \<Rightarrow>
      if bal_d (size t') (dl+1) then (t',dl+1) else (balance_tree t', 0))"

declare delete.simps [simp del]

subsubsection \<open>Functional Correctness\<close>

lemma size_insert_d: "insert_d x (t,dl) = (t',dl') \<Longrightarrow> size t \<le> size t'"
by(auto simp: ins_size ins0_neq_Unbal split: if_splits up.splits)

lemma inorder_insert_d: "insert_d x (t,dl) = (t',dl') \<Longrightarrow> sorted(inorder t)
  \<Longrightarrow> inorder t' = ins_list x (inorder t)"
by(auto simp add: ins0_neq_Unbal insert_def inorder_ins split: prod.split up.split)

lemma bal_i_insert_d: assumes "insert_d x (t,dl) = (t',dl')" "bal_i (size t + dl) (height t)"
shows "bal_i (size t' + dl) (height t')"
proof (cases "ins (size t + dl) 0 x t")
  case Same
  with assms show ?thesis by (simp)
next
  case Bal
  thus ?thesis
    using ins_bal_i_Bal[OF Bal] assms ins_size by(simp add: size1_size)
next
  case (Unbal t')
  hence False by(simp add: ins0_neq_Unbal)
  thus ?thesis ..
qed

lemma inorder_del:
  "sorted(inorder t) \<Longrightarrow>
  inorder(case del x t of None \<Rightarrow> t | Some t' \<Rightarrow> t') = del_list x (inorder t)"
by(induction t)
  (auto simp add: del_list_simps split_minD split: option.splits prod.splits)

lemma inorder_delete:
  "\<lbrakk> delete x (t,dl) = (t',dl'); sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder t' = del_list x (inorder t)"
using inorder_del[of t x]
by(auto simp add: delete.simps split: option.splits if_splits)

lemma size_split_min:
  "\<lbrakk> split_min t = (a,t'); t \<noteq> Leaf \<rbrakk> \<Longrightarrow> size t' = size t - 1"
by(induction t arbitrary: t')
  (auto simp add: zero_less_iff_neq_zero split: if_splits prod.splits)

lemma height_split_min:
  "\<lbrakk> split_min t = (a,t'); t \<noteq> Leaf \<rbrakk> \<Longrightarrow> height t' \<le> height t"
apply(induction t arbitrary: t')
 apply simp
by(fastforce split: if_splits prod.splits)

lemma size_del: "del x t = Some t' \<Longrightarrow> size t' = size t - 1"
proof(induction x t arbitrary: t' rule: del_tm.induct)
  case 1 thus ?case by simp
next
  case (2 x l y r)
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    with "2.prems" obtain l' where l': "del x l = Some l'"
      by(auto split: option.splits)
    hence [arith]: "size l \<noteq> 0" by(cases l) auto
    show ?thesis using ls 2 l' by(auto)
  next
    case eq
    show ?thesis
    proof (cases "r = Leaf")
      case True thus ?thesis using eq "2.prems" by(simp)
    next
      case False
      thus ?thesis
        using eq "2.prems" eq_size_0[of r]
        by (auto simp add: size_split_min simp del: eq_size_0 split: prod.splits)
    qed
  next
    case gr
    with "2.prems" obtain r' where r': "del x r = Some r'"
      by(auto split: option.splits)
    hence [arith]: "size r \<noteq> 0" by(cases r) auto
    show ?thesis using gr 2 r' by(auto)
  qed
qed

lemma height_del: "del x t = Some t' \<Longrightarrow> height t' \<le> height t"
proof(induction x t arbitrary: t' rule: del_tm.induct)
  case 1 thus ?case by simp
next
  case (2 x l y r)
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    thus ?thesis
      using 2 by(fastforce split: option.splits)
  next
    case eq
    thus ?thesis
      using "2.prems"
      by (auto dest: height_split_min split: if_splits prod.splits)
  next
    case gr
    thus ?thesis
      using 2 by(fastforce split: option.splits)
  qed
qed

lemma bal_i_delete:
assumes "bal_i (size t + dl) (height t)" "delete x (t,dl) = (t',dl')"
shows "bal_i (size t' + dl') (height t')"
proof (cases "del x t")
  case None
  with assms show ?thesis by (simp add: delete.simps)
next
  case Some
  hence "size t \<noteq> 0" by(cases t) auto
  thus ?thesis
    using Some assms size_del height_del[OF Some]
    by(force simp add: delete.simps bal_i_balance mono_bal_i' split: if_splits)
qed

lemma bal_d_delete:
  "\<lbrakk> bal_d (size t) dl; delete x (t,dl) = (t',dl') \<rbrakk>
   \<Longrightarrow> bal_d (size t') dl'"
by (auto simp add: delete.simps bal_d0 size_del split: option.splits if_splits)

text \<open>Full functional correctness of the naive implementation:\<close>

interpretation Set_by_Ordered
where empty = "(Leaf,0)" and isin = "\<lambda>(t,n). isin t"
and insert = insert_d and delete = delete
and inorder = "\<lambda>(t,n). inorder t" and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set split: prod.splits)
next
  case (3 t) thus ?case
    by(auto simp del: insert_d.simps simp add: inorder_insert_d split: prod.splits)
next
  case (4 tn x)
  obtain t n where "tn = (t,n)" by fastforce
  thus ?case
    using 4 by(auto simp: inorder_delete split: prod.splits)
qed (rule TrueI)+

end (* RBTid1 *)

interpretation I_RBTid1: RBTid1
where bal_i = "\<lambda>n h. h \<le> log 2 (real(n + 1)) + 1" ..

subsection "Efficient Implementation (with delete)"

type_synonym 'a rbt2 = "'a tree * nat * nat"

locale RBTid2 = RBTi2 + RBTid1
begin

subsubsection \<open>Functions\<close>

fun insert2_d :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2" where
"insert2_d x (t,n,dl) =
  (case ins2 (n+dl) 0 x t of
     Same2 \<Rightarrow> (t,n,dl) |
     Bal2 t' \<Rightarrow> (t',n+1,dl))"
  (* Unbal unreachable *)

fun insert3_d_tm :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2 tm" where
"insert3_d_tm x (t,n,dl) =1
  do { t' \<leftarrow> ins3_tm (n+dl) 0 x t;
       case t' of
         Same2 \<Rightarrow> return (t,n,dl) |
         Bal2 t' \<Rightarrow> return (t',n+1,dl) |
         Unbal2 _ _ _ \<Rightarrow> return undefined}"
  (* Unbal unreachable *)

definition insert3_d :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2" where
"insert3_d a t = val (insert3_d_tm a t)"

lemma insert3_d_def2[simp,code]: "insert3_d x (t,n,dl) =
  (let t' = ins3 (n+dl) 0 x t in
   case t' of
     Same2 \<Rightarrow> (t,n,dl) |
     Bal2 t' \<Rightarrow> (t',n+1,dl) |
     Unbal2 _ _ _ \<Rightarrow> undefined)"
using val_cong[OF insert3_d_tm.simps(1)]
by(simp only: insert3_d_def ins3_def val_simps up2.case_distrib[of val])

definition t_insert3_d :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> nat" where
"t_insert3_d x t = time(insert3_d_tm x t)"

lemma t_insert3_d_def2[simp]:
  "t_insert3_d x (t,n,dl) = (t_ins3 (n+dl) 0 x t + 1)"
by(simp add: t_insert3_d_def t_ins3_def tm_simps split: tm.split up2.split)

fun delete2_tm :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2 tm" where
"delete2_tm x (t,n,dl) =1
  do { t' \<leftarrow> del_tm x t;
       case t' of
         None \<Rightarrow> return (t,n,dl) |
         Some t' \<Rightarrow>
           (let n' = n-1; dl' = dl + 1
            in if bal_d n' dl' then return (t',n',dl')
               else do { t'' \<leftarrow> bal_tree_tm n' t';
                         return (t'', n', 0)})}"

definition delete2 :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2" where
"delete2 x t = val(delete2_tm x t)"

lemma delete2_def2:
  "delete2 x (t,n,dl) =
  (let t' = del x t in
   case t' of
    None \<Rightarrow> (t,n,dl) |
    Some t' \<Rightarrow> (let n' = n-1; dl' = dl + 1
      in if bal_d n' dl' then (t',n',dl')
         else let t'' = bal_tree n' t' in (t'', n', 0)))"
using val_cong[OF delete2_tm.simps(1)]
by(simp only: delete2_def ins3_def del_def bal_tree_def val_simps option.case_distrib[of val])

definition t_delete2 :: "'a::linorder \<Rightarrow> 'a rbt2 \<Rightarrow> nat" where
"t_delete2 x t = time(delete2_tm x t)"

lemma t_delete2_def2:
  "t_delete2 x (t,n,dl) = (t_del x t +
  (case del x t of
     None \<Rightarrow> 1 |
     Some t' \<Rightarrow> (let n' = n-1; dl' = dl + 1
       in if bal_d n' dl' then 1 else t_bal_tree n' t' + 1)))"
by(auto simp add: t_delete2_def tm_simps t_del_def del_def t_bal_tree_def split: tm.split option.split)

subsubsection \<open>Equivalence proofs\<close>

lemma insert2_insert_d:
  "insert2_d x (t,size t,dl) = (t',n',dl') \<longleftrightarrow>
   (t',dl') = insert_d x (t,dl) \<and> n' = size t'"
by(auto simp: ins2_iff_ins ins_size ins0_neq_Unbal split: up2.split up.split)

lemma insert3_insert2_d:
  "bal_i (n+dl) (height t) \<Longrightarrow> insert3_d x (t,n,dl) = insert2_d x (t,n,dl)"
by(simp add: ins3_ins2 split: up2.split)

lemma delete2_delete:
  "delete2 x (t,size t,dl) = (t',n',dl') \<longleftrightarrow>
  (t',dl') = delete x (t,dl) \<and> n' = size t'"
by(auto simp: delete2_def2 delete.simps size_del balance_tree_def bal_tree
    split: option.splits)

subsubsection \<open>Amortized complexity\<close>

fun \<Phi>\<^sub>d :: "'a rbt2 \<Rightarrow> real" where
"\<Phi>\<^sub>d (t,n,dl) = \<Phi> t + 4*dl/cd"

lemma \<Phi>\<^sub>d_case: "\<Phi>\<^sub>d tndl = (case tndl of (t,n,dl) \<Rightarrow> \<Phi> t + 4*dl/cd)"
by(simp split: prod.split)

lemma imbal_diff_decr:
  "size r' = size r - 1 \<Longrightarrow>
   real(imbal (Node l x' r')) - imbal (Node l x r) \<le> 1"
by(simp add: imbal.simps)

lemma tinsert_d_amor:
assumes "n = size t" "insert_d a (t,dl) = (t',dl')" "bal_i (size t + dl) (height t)"
shows "t_insert3_d a (t,n,dl) + \<Phi> t' - \<Phi> t \<le> (6*e+2) * (height t + 1) + 1"
proof (cases "ins (size t + dl) 0 a t")
  case Same
  have *: "5*e * real (height t) \<ge> 0" using e0 by simp
  show ?thesis using t_ins3_Same[of "size t + dl" 0 a t] Same assms
    apply (auto simp add: ring_distribs ins3_ins2 ins2_ins)
    using * e0
    apply safe
    by linarith
next
  case (Bal t')
  thus ?thesis
    using t_ins3_Bal[of "size t + dl" 0 a t t'] Bal assms
    by(simp add: ins_size ins3_ins2 ins2_ins)
next
  case Unbal
  hence False by(simp add: ins0_neq_Unbal)
  thus ?thesis ..
qed


lemma t_split_min_ub:
  "t \<noteq> Leaf \<Longrightarrow> t_split_min t \<le> height t + 1"
by(induction t) auto

lemma t_del_ub:
  "t_del x t \<le> height t + 1"
by(induction t) (auto dest: t_split_min_ub)

lemma imbal_split_min:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> real(imbal t') - imbal t \<le> 1"
proof(induction t arbitrary: t')
  case Leaf thus ?case
    by simp
next
  case (Node l y r)
  thus ?case using size_split_min[OF Node.prems]
    apply(auto split: if_splits option.splits prod.splits)
    apply(auto simp: imbal.simps)
    apply(cases t')
    apply (simp add: imbal.simps)
    apply (simp add: imbal.simps)
    done
qed

lemma imbal_del_Some:
  "del x t = Some t' \<Longrightarrow> real(imbal t') - imbal t \<le> 1"
proof(induction t arbitrary: t')
  case Leaf
  thus ?case
    by (auto simp add: imbal.simps split!: if_splits)
next
  case (Node t1 x2 t2)
  thus ?case using size_del[OF Node.prems]
    apply(auto split: if_splits option.splits prod.splits)
    apply(auto simp: imbal.simps)
    apply(cases t')
    apply (simp add: imbal.simps)
    apply (simp add: imbal.simps)
    done
qed

lemma Phi_diff_split_min:
  "split_min t = (x, t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> \<Phi> t' - \<Phi> t \<le> 6*e*height t"
proof(induction t arbitrary: t')
  case Leaf thus ?case
    by simp
next
  case (Node l y r)
  note [arith] = e0
  thus ?case
  proof (cases "l = Leaf")
    have *: "- a \<le> b \<longleftrightarrow> 0 \<le> a+b" for a b :: real by linarith
    case True
    thus ?thesis using Node.prems
        by(cases r)(auto simp: imbal.simps *)
  next
    case False
    with Node.prems obtain l' where rec: "split_min l = (x,l')"
      and t': "t' = Node l' y r"
      by (auto split: prod.splits)
    hence "\<Phi> t' - \<Phi> \<langle>l,y,r\<rangle> = 6*e*imbal\<langle>l',y,r\<rangle> - 6*e*imbal\<langle>l,y,r\<rangle> + \<Phi> l' - \<Phi> l"
      by simp
    also have "\<dots> = 6*e * (real(imbal\<langle>l',y,r\<rangle>) - imbal\<langle>l,y,r\<rangle>) + \<Phi> l' - \<Phi> l"
      by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e + \<Phi> l' - \<Phi> l"
      using imbal_split_min[OF Node.prems(1)] t'
      by (simp)
    also have "\<dots> \<le> 6*e * (height l + 1)"
      using Node.IH(1)[OF rec False] by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e * height \<langle>l, y, r\<rangle>"
      by(simp del: times_divide_eq_left)
    finally show ?thesis .
  qed
qed

lemma Phi_diff_del_Some:
  "del x t = Some t' \<Longrightarrow> \<Phi> t' - \<Phi> t \<le> 6*e * height t"
proof(induction t arbitrary: t')
  case Leaf thus ?case
    by (auto simp: imbal.simps)
next
  case (Node l y r)
  note [arith] = e0
  consider (ls) "x < y" | (eq) "x = y" | (gr) "x > y"
    by(metis less_linear)
  thus ?case
  proof cases
    case ls
    with Node.prems obtain l' where rec: "del x l = Some l'"
      and t': "t' = Node l' y r"
      by (auto split: option.splits)
    hence "\<Phi> t' - \<Phi> \<langle>l,y,r\<rangle> = 6*e*imbal\<langle>l',y,r\<rangle> - 6*e*imbal\<langle>l,y,r\<rangle> + \<Phi> l' - \<Phi> l"
      by simp
    also have "\<dots> = 6*e * (real(imbal\<langle>l',y,r\<rangle>) - imbal\<langle>l,y,r\<rangle>) + \<Phi> l' - \<Phi> l"
      by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e + \<Phi> l' - \<Phi> l"
      using imbal_del_Some[OF Node.prems] t'
      by (simp)
    also have "\<dots> \<le> 6*e * (height l + 1)"
      using Node.IH(1)[OF rec] by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e * height \<langle>l, y, r\<rangle>"
      by(simp del: times_divide_eq_left)
    finally show ?thesis .
  next
    case [simp]: eq
    show ?thesis
    proof (cases "r = Leaf")
      case [simp]: True
      show ?thesis
      proof (cases "size t' = 0")
        case True
        thus ?thesis
          using Node.prems by(auto simp: imbal.simps of_nat_diff)
      next
        case [arith]: False
        show ?thesis using Node.prems by(simp add: imbal.simps of_nat_diff algebra_simps)
      qed
    next
      case False
      then obtain a r' where *: "split_min r = (a,r')" using Node.prems
        by(auto split: prod.splits)
      from  mult_left_mono[OF imbal_diff_decr[OF size_split_min[OF this False], of l a y], of "5*e"]
      have "6*e*real (imbal \<langle>l, a, r'\<rangle>) - 6*e*real (imbal \<langle>l, y, r\<rangle>) \<le> 6*e"
        by(simp add: ring_distribs)
      thus ?thesis using Node.prems * False Phi_diff_split_min[OF *]
        apply(auto simp add: max_def ring_distribs)
        using mult_less_cancel_left_pos[of "6*e" "height r" "height l"] by linarith
    qed
  next
    case gr
    with Node.prems obtain r' where rec: "del x r = Some r'"
      and t': "t' = Node l y r'"
      by (auto split: option.splits)
    hence "\<Phi> t' - \<Phi> \<langle>l,y,r\<rangle> = 6*e*imbal\<langle>l,y,r'\<rangle> - 6*e*imbal\<langle>l,y,r\<rangle> + \<Phi> r' - \<Phi> r"
      by simp
    also have "\<dots> = 6*e * (real(imbal\<langle>l,y,r'\<rangle>) - imbal\<langle>l,y,r\<rangle>) + \<Phi> r' - \<Phi> r"
      by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e + \<Phi> r' - \<Phi> r"
      using imbal_del_Some[OF Node.prems] t'
      by (simp)
    also have "\<dots> \<le> 6*e * (height r + 1)"
      using Node.IH(2)[OF rec] by (simp add: ring_distribs)
    also have "\<dots> \<le> 6*e * height \<langle>l, y, r\<rangle>"
      by(simp del: times_divide_eq_left)
    finally show ?thesis .
  qed
qed


lemma amor_del_Some:
  "del x t = Some t' \<Longrightarrow>
  t_del x t + \<Phi> t' - \<Phi> t \<le> (6*e + 1) * height t + 1"
apply(drule Phi_diff_del_Some)
using t_del_ub[of x t]
by (simp add: ring_distribs)

lemma cd1: "1/cd > 0"
by(simp add: cd0)

lemma t_delete_amor: assumes "n = size t"
shows "t_delete2 x (t,n,dl) + \<Phi>\<^sub>d (delete2 x (t,n,dl)) - \<Phi>\<^sub>d (t,n,dl)
       \<le> (6*e+1) * height t + 4/cd + 4"
proof (cases "del x t")
  case None
  have *: "6*e * real (height t) \<ge> 0" using e0 by simp
  show ?thesis using None
    apply (simp add: delete2_def2 t_delete2_def2 ring_distribs)
    using * t_del_ub[of x t] cd1 by linarith
next
  case (Some t')
  show ?thesis
  proof (cases "bal_d (n-1) (dl+1)")
    case True
    thus ?thesis
      using assms Some amor_del_Some[OF Some] 
      by(simp add: size_del delete2_def2 t_delete2_def2 algebra_simps add_divide_distrib)
  next
    case False
    from Some have [arith]: "size t \<noteq> 0" by(cases t) (auto)
    have "t_delete2 x (t, n, dl) + \<Phi>\<^sub>d (delete2 x (t,n,dl)) - \<Phi>\<^sub>d (t,n,dl) =
      t_delete2 x (t, n, dl) - \<Phi> t - 4*dl/cd"
      using False Some
      by(simp add: delete2_def2 t_delete2_def2 \<Phi>_wbalanced bal_tree)
    also have "\<dots> = t_del x t + 4 * size t - \<Phi> t - 4*dl/cd"
      using False assms Some by(simp add: t_delete2_def2 t_bal_tree size_del size1_size)
    also have "\<dots> \<le> (6*e+1)*height t + 4*(size t - dl/cd + 1)"
      using amor_del_Some[OF Some] \<Phi>_nn[of t] \<Phi>_nn[of t']
      by(simp add: ring_distribs)
    also have "size t - dl/cd + 1 \<le> 1/cd + 1"
      using assms False cd0 unfolding bal_d_def
      by(simp add: algebra_simps of_nat_diff)(simp add: field_simps)
    finally show ?thesis
      by(simp add: ring_distribs)
  qed
qed

datatype (plugins del: lifting) 'b ops = Insert 'b | Delete 'b

fun nxt :: "'a ops \<Rightarrow> 'a rbt2 \<Rightarrow> 'a rbt2" where
"nxt (Insert x) t = insert3_d x t" |
"nxt (Delete x) t = delete2 x t"

fun t\<^sub>s :: "'a ops \<Rightarrow> 'a rbt2 \<Rightarrow> real" where
"t\<^sub>s (Insert x) t = t_insert3_d x t" |
"t\<^sub>s (Delete x) t = t_delete2 x t"

interpretation RBTid2_Amor: Amortized
where init = "(Leaf,0,0)"
and nxt = nxt
and inv = "\<lambda>(t,n,dl). n = size t \<and>
  bal_i (size t+dl) (height t) \<and> bal_d (size t) dl"
and t = t\<^sub>s and \<Phi> = \<Phi>\<^sub>d
and U = "\<lambda>f (t,_). case f of
  Insert _ \<Rightarrow> (6*e+2) * (height t + 1) + 1 |
  Delete _ \<Rightarrow> (6*e+1) * height t + 4/cd + 4"
proof (standard, goal_cases)
  case 1
  show ?case using bal_i0 bal_d0 by (simp split: prod.split)
next
  case (2 s f)
  obtain t n dl where [simp]: "s = (t,n,dl)"
    using prod_cases3 by blast 
  show ?case
  proof (cases f)
    case (Insert x)
    thus ?thesis
      using 2 insert2_insert_d[of x t dl] bal_i_insert_d[of x t dl]
        mono_bal_d[OF _ size_insert_d]
      by (simp del: insert2_d.simps insert3_d_def2 insert_d.simps
               add: insert3_insert2_d split: prod.splits)
         fastforce
  next
    case (Delete x)
    thus ?thesis
      using 2 bal_i_delete[of t dl x] bal_d_delete[of t dl x]
      by (auto simp: delete2_delete)
  qed
next
  case (3 s)
  thus ?case
    using \<Phi>_nn[of "fst s" ] cd0 by (auto split: prod.splits)
next
  case 4
  show ?case by(simp)
next
  case (5 s f)
  obtain t n dl where [simp]: "s = (t,n,dl)"
    using prod_cases3 by blast 
  show ?case
  proof (cases f)
    case (Insert x)
    thus ?thesis
      using 5 insert2_insert_d[of x t dl] tinsert_d_amor[of n t x dl]
      by (fastforce simp del: insert2_d.simps insert3_d_def2 insert.simps
               simp add: insert3_insert2_d \<Phi>\<^sub>d_case split: prod.split)
  next
    case (Delete x)
    then show ?thesis
      using 5 delete2_delete[of x t dl] t_delete_amor[of n t x dl]
      by (simp)
  qed
qed

end (* RBTid2 *)

axiomatization b :: real where
b0: "b > 0"

axiomatization where
cd_le_log: "cd \<le> 2 powr (b/c) - 1"
text\<open>This axiom is only used to prove that the height remains logarithmic
in the size.\<close>

interpretation I_RBTid2: RBTid2
where bal_i = "\<lambda>n h. h \<le> ceiling(c * log 2 (n+1))"
and e = "2 powr (1/c) / (2 - 2 powr (1/c))"
..
(* For code generation:
defines insert_id2 = I_RBTid2.insert3_d
and ins3_id2 = I_RBTid2.ins3
and up3_id2 = I_RBTid2.up3
*)

(* Code Generation *)
(*
(* FIXME why not done in Code_Float? *)
lemmas [code del] = real_less_code real_less_eq_code real_floor_code

lemma [code]: "bal_i n h = (h \<le> ceiling(c * log (real_of_integer 2) (n+1)))"
  by (simp add: bal_i_def real_of_integer_def)

lemma myc[code_unfold]: "c = real_of_integer 3 / real_of_integer 2"
sorry

definition "floor_integer (x::real) = integer_of_int (floor x)"

code_printing
  constant "floor_integer :: real \<Rightarrow> integer" \<rightharpoonup>
    (SML) "Real.floor"

lemma [code]: "(floor::real \<Rightarrow> int) = (\<lambda>x. int_of_integer (floor_integer x))"
  by (auto simp: floor_integer_def)

definition "ceiling_integer (x::real) = integer_of_int (ceiling x)"

code_printing
  constant "ceiling_integer :: real \<Rightarrow> integer" \<rightharpoonup>
    (SML) "Real.ceil"

code_printing
  constant "0 :: real" \<rightharpoonup> (SML) "0.0"
code_printing
  constant "1 :: real" \<rightharpoonup> (SML) "1.0"

lemma [code_unfold del]: "0 \<equiv> real_of_rat 0"
  by simp
lemma [code_unfold del]: "1 \<equiv> real_of_rat 1"
  by simp

lemma [code_abbrev]: "real_of_integer (integer_of_nat x) = real x"
  sorry

lemma [code_abbrev]: "(\<lambda>x. int_of_integer (ceiling_integer x)) = (ceiling::real \<Rightarrow> int)"
  by (auto simp: ceiling_integer_def)

print_codeproc

export_code insert_id2 in SML
module_name Root_Balanced
*)

text\<open>Finally we show that under the above interpretation of \<open>bal_i\<close>
the height is logarithmic:\<close>

definition bal_i :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"bal_i n h = (h \<le> ceiling(c * log 2 (n+1)))"

lemma assumes "bal_i (size t + dl) (height t)" "bal_d (size t) dl"
shows "height t \<le> ceiling(c * log 2 (size1 t) + b)"
proof -
  have *: "0 < real (size t + 1) + cd * real (size t + 1)"
    using cd0 by (simp add: add_pos_pos)
  have "0 < 2 powr (b / c) - 1"
    using b0 c1 by(auto simp: less_powr_iff)
  hence **: "0 < real (size t + 1) + (2 powr (b / c) - 1) * real (size t + 1)"
    by (simp add: add_pos_pos)
  have "height t \<le> ceiling(c * log 2 (size t + 1 + dl))"
    using assms(1) by(simp add: bal_i_def add_ac)
  also have "\<dots> \<le> ceiling(c * log 2 (size t + 1 + cd * (size t + 1)))"
    using c1 cd0 assms(2)
    by(simp add: ceiling_mono add_pos_nonneg bal_d_def add_ac)
  also have "\<dots> \<le> ceiling(c * log 2 (size t + 1 + (2 powr (b/c) - 1) * (size t + 1)))"
    using * ** cd_le_log c1 by(simp add: ceiling_mono mult_left_mono)
  also have "\<dots> = ceiling(c * log 2 (2 powr (b/c) * (size1 t)))"
    by(simp add:algebra_simps size1_size)
  also have "\<dots> = ceiling(c * (b/c + log 2 (size1 t)))"
    by(simp add: log_mult)
  also have "\<dots> = ceiling(c * log 2 (size1 t) + b)"
    using c1 by(simp add: algebra_simps)
  finally show ?thesis .
qed


end
