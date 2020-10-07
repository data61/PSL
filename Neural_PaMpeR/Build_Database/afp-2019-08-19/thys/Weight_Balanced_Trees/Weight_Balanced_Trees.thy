(* Author: Tobias Nipkow & Stefan Dirix *)

section \<open>Weight Balanced Tree Implementation of Sets\<close>

text \<open>This theory follows Hirai and Yamamoto but we do not prove their general
theorem. Instead we provide a short parameterized theory that, when
interpreted with valid parameters, will prove perservation of the invariant
for these parameters.\<close>

theory Weight_Balanced_Trees
imports
  "HOL-Data_Structures.Isin2"
begin

lemma neq_Leaf2_iff: "t \<noteq> Leaf \<longleftrightarrow> (\<exists>n l a r. t = Node n l a r)"
by(cases t) auto

type_synonym 'a wbt = "('a,nat) tree"

fun size_wbt :: "'a wbt \<Rightarrow> nat" where
"size_wbt Leaf = 0" |
"size_wbt (Node _ _ n _) = n"

text \<open>Smart constructor:\<close>

fun N :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"N l a r = Node l a (size_wbt l + size_wbt r + 1) r"

text "Basic Rotations:"

fun rot1L :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"rot1L A a B b C = N (N A a B) b C"

fun rot1R :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"rot1R A a B b C = N A a (N B b C)"

fun rot2 :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"rot2 A a (Node B1 b _ B2) c C = N (N A a B1) b (N B2 c C)"


subsection "WB trees"

text \<open>
Parameters:
  \<^descr> \<open>\<Delta>\<close> determines when a tree needs to be rebalanced
  \<^descr> \<open>\<Gamma>\<close> determines whether it needs to be single or double rotation.

\noindent We represent rational numbers as pairs: \<open>\<Delta> = \<Delta>1/\<Delta>2\<close> and \<open>\<Gamma> = \<Gamma>1/\<Gamma>2\<close>.
\bigskip

Hirai and Yamamoto \cite{HiraiY11} proved that under the following constraints
insertion and deletion preserve the WB invariant, i.e.\
\<open>\<Delta>\<close> and \<open>\<Gamma>\<close> are \emph{valid}:\<close>

definition valid_params :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"valid_params \<Delta>1 \<Delta>2 \<Gamma>1 \<Gamma>2 = (
  \<Delta>1 * 2 < \<Delta>2 * 9  \<comment> \<open>right: \<open>\<Delta> < 4.5\<close>\<close> \<and>
  \<Gamma>1 * \<Delta>2 + \<Gamma>2 * \<Delta>2 \<le> \<Gamma>2 * \<Delta>1 \<comment> \<open>left: \<open>\<Gamma> + 1 \<le> \<Delta>\<close>\<close> \<and>
  \<Gamma>1 * \<Delta>1 \<ge> \<Gamma>2 * (\<Delta>1 + \<Delta>2)  \<comment> \<open>lower: \<open>\<Gamma> \<ge> (\<Delta> + 1) / \<Delta>\<close>\<close> \<and>
  \<comment> \<open>upper:\<close>
  (5*\<Delta>2 \<le> 2*\<Delta>1 \<and> 1*\<Delta>1 < 3*\<Delta>2 \<longrightarrow> \<Gamma>1*2 \<le> \<Gamma>2*3)
     \<comment> \<open>\<open>\<Gamma> \<le> 3/2\<close> if \<open>2.5 \<le> \<Delta> < 3\<close>\<close> \<and>
  (3*\<Delta>2 \<le> 1*\<Delta>1 \<and> 2*\<Delta>1 < 7*\<Delta>2 \<longrightarrow> \<Gamma>1*2 \<le> \<Gamma>2*4)
     \<comment> \<open>\<open>\<Gamma> \<le> 4/2\<close> if \<open>3 \<le> \<Delta> < 3.5\<close>\<close> \<and>
  (7*\<Delta>2 \<le> 2*\<Delta>1 \<and> 1*\<Delta>1 < 4*\<Delta>2 \<longrightarrow> \<Gamma>1*3 \<le> \<Gamma>2*4)
     \<comment> \<open>\<open>\<Gamma> \<le> 4/3\<close> when \<open>3.5 \<le> \<Delta> < 4\<close>\<close> \<and>
  (4*\<Delta>2 \<le> 1*\<Delta>1 \<and> 2*\<Delta>1 < 9*\<Delta>2 \<longrightarrow> \<Gamma>1*3 \<le> \<Gamma>2*5)
     \<comment> \<open>\<open>\<Gamma> \<le> 5/3\<close> when \<open>4 \<le> \<Delta> < 4.5\<close>\<close>
  )"

text \<open>We do not make use of these constraints and do not prove that they guarantee
preservation of the invariant. Instead, we provide generic proofs of invariant preservation
that work for many (all?) interpretations of locale \<open>WBT\<close> (below) with valid parameters.
Further down we demonstrate this by interpreting \<open>WBT\<close> with a selection of valid parameters.
[For some parameters, some \<open>smt\<close> proofs fail because \<open>smt\<close> on \<open>nat\<close>s fails although
on non-negative \<open>int\<close>s it succeeds, i.e.\ the goal should be provable.
This is a shortcoming of \<open>smt\<close> that is under investigation.]

Locale \<open>WBT\<close> comes with some minimal assumptions (\<open>\<Gamma>1 > \<Gamma>2\<close> and \<open>\<Delta>1 > \<Delta>2\<close>) which follow
from @{const valid_params} and from which we conclude some simple lemmas.
\<close>

locale WBT =
fixes \<Delta>1 \<Delta>2 :: nat and \<Gamma>1 \<Gamma>2 :: nat
assumes Delta_gr1: "\<Delta>1 > \<Delta>2" and Gamma_gr1: "\<Gamma>1 > \<Gamma>2"
begin

(* How to prove the assumptions from valid_params:
lemma Gamma_gr1: "\<Gamma>1 > \<Gamma>2"
proof -
  have "\<not> (\<Delta>1 + \<Delta>2) * \<Gamma>2 \<le> \<Delta>1 * \<Gamma>2" by (simp add: not0)
  thus ?thesis by (metis order.trans lower mult.commute mult_le_cancel2 not_le)
qed

lemma Delta_gr2: "\<Delta>1 > 2 * \<Delta>2"
proof -
  from Gamma_gr1 have "\<Gamma>2 * \<Delta>2 < \<Gamma>1 * \<Delta>2" by (simp add: not0)
  with left have "2 * \<Gamma>2 * \<Delta>2 < \<Gamma>2 * \<Delta>1" by linarith
  thus ?thesis by(simp)
qed
*)

subsubsection "Balance Indicators"

fun balanced1 :: "'a wbt \<Rightarrow> 'a wbt \<Rightarrow> bool" where
"balanced1 t1 t2 = (\<Delta>1 * (size_wbt t1 + 1) \<ge> \<Delta>2 * (size_wbt t2 + 1))"

text \<open>The global weight-balanced tree invariant:\<close>

fun wbt :: "'a wbt \<Rightarrow> bool" where
"wbt Leaf = True"|
"wbt (Node l _ n r) =
  (n = size l + size r + 1 \<and> balanced1 l r \<and> balanced1 r l \<and> wbt l \<and> wbt r)"

lemma size_wbt_eq_size[simp]: "wbt t \<Longrightarrow> size_wbt t = size t"
by(induction t) auto

fun single :: "'a wbt \<Rightarrow> 'a wbt \<Rightarrow> bool" where
"single t1 t2 = (\<Gamma>1 * (size_wbt t2 + 1) > \<Gamma>2 * (size_wbt t1 + 1))"

subsubsection "Code"

fun rotateL :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"rotateL A a (Node B b _ C) =
   (if single B C then rot1L A a B b C else rot2 A a B b C)"

fun balanceL :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"balanceL l a r = (if balanced1 l r then N l a r else rotateL l a r)"

fun rotateR :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"rotateR (Node A a _ B) b C =
  (if single B A then rot1R A a B b C else rot2 A a B b C)"

fun balanceR :: "'a wbt \<Rightarrow> 'a \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"balanceR l a r = (if balanced1 r l then N l a r else rotateR l a r)"

fun insert :: "'a::linorder \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"insert x Leaf = Node Leaf x 1 Leaf" |
"insert x (Node l a n r) =
   (case cmp x a of
      LT \<Rightarrow> balanceR (insert x l) a r |
      GT \<Rightarrow> balanceL l a (insert x r) |
      EQ \<Rightarrow> Node l a n r )"

fun split_min :: "'a wbt \<Rightarrow> 'a * 'a wbt" where
"split_min (Node l a _ r) =
   (if l = Leaf then (a,r) else let (x,l') = split_min l in (x, balanceL l' a r))"

fun del_max :: "'a wbt \<Rightarrow> 'a * 'a wbt" where
"del_max (Node l a _ r) =
   (if r = Leaf then (a,l) else let (x,r') = del_max r in (x, balanceR l a r'))"

fun combine :: "'a wbt \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt"  where
"combine Leaf Leaf = Leaf"|
"combine Leaf r = r"|
"combine l Leaf = l"|
"combine l r =
   (if size l > size r then
      let (lMax, l') = del_max l in balanceL l' lMax r
    else
      let (rMin, r') = split_min r in balanceR l rMin r')"

fun delete :: "'a::linorder \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
"delete _ Leaf = Leaf" |
"delete x (Node l a _ r) =
  (case cmp x a of
     LT \<Rightarrow> balanceL (delete x l) a r |
     GT \<Rightarrow> balanceR l a (delete x r) |
     EQ \<Rightarrow> combine l r)"


subsection "Functional Correctness Proofs"

text \<open>A WB tree must be of a certain structure if balanced1 and single are False.\<close>

lemma not_Leaf_if_not_balanced1:
  assumes "\<not> balanced1 l r"
  shows "r \<noteq> Leaf"
proof
  assume "r = Leaf" with assms Delta_gr1 show False by simp
qed

lemma not_Leaf_if_not_single:
  assumes "\<not> single l r"
  shows "l \<noteq> Leaf"
proof
  assume "l = Leaf" with assms Gamma_gr1 show False by simp
qed

subsubsection "Inorder Properties"

lemma inorder_rot2:
  "B \<noteq> Leaf \<Longrightarrow> inorder(rot2 A a B b C) = inorder A @ a # inorder B @ b # inorder C"
by (cases "(A,a,B,b,C)" rule: rot2.cases) (auto)

lemma inorder_rotateL:
  "r \<noteq> Leaf \<Longrightarrow> inorder(rotateL l a r) = inorder l @ a # inorder r"
by (induction l a r rule: rotateL.induct) (auto simp add: inorder_rot2 not_Leaf_if_not_single)

lemma inorder_rotateR:
  "l \<noteq> Leaf \<Longrightarrow> inorder(rotateR l a r) = inorder l @ a # inorder r"
by (induction l a r rule: rotateR.induct) (auto simp add: inorder_rot2 not_Leaf_if_not_single)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (induction t)
   (auto simp: ins_list_simps inorder_rotateL inorder_rotateR not_Leaf_if_not_balanced1)

lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by (induction t arbitrary: t' rule: split_min.induct)
   (auto simp: sorted_lems inorder_rotateL not_Leaf_if_not_balanced1
     split: prod.splits if_splits)

lemma del_maxD:
  "del_max t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> inorder t' @ [x] = inorder t"
by (induction t arbitrary: t' rule: del_max.induct)
   (auto simp: sorted_lems inorder_rotateR not_Leaf_if_not_balanced1
     split: prod.splits if_splits)

lemma inorder_combine:
  "inorder(combine l r) = inorder l @ inorder r"
by(induction l r rule: combine.induct)
  (auto simp: del_maxD split_minD inorder_rotateL inorder_rotateR not_Leaf_if_not_balanced1
    simp del: rotateL.simps rotateR.simps split: prod.splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_combine inorder_rotateL inorder_rotateR
     not_Leaf_if_not_balanced1 simp del: rotateL.simps rotateR.simps)


subsection "Size Lemmas"

subsubsection "Insertion"

lemma size_rot2L[simp]:
  "B \<noteq> Leaf \<Longrightarrow> size(rot2 A a B b C) = size A + size B + size C + 2"
by(induction A a B b C rule: rot2.induct) auto

lemma size_rotateR[simp]:
  "l \<noteq> Leaf \<Longrightarrow> size(rotateR l a r) = size l + size r + 1"
by(induction l a r rule: rotateR.induct)
  (auto simp: not_Leaf_if_not_single simp del: rot2.simps)

lemma size_rotateL[simp]:
  "r \<noteq> Leaf \<Longrightarrow> size(rotateL l a r) = size l + size r + 1"
by(induction l a r rule: rotateL.induct)
  (auto simp: not_Leaf_if_not_single simp del: rot2.simps)

lemma size_length: "size t = length (inorder t)"
by (induction t rule: inorder.induct) auto

lemma size_insert: "size (insert x t) = (if isin t x then size t else Suc (size t))"
by (induction t) (auto simp: not_Leaf_if_not_balanced1)

subsubsection "Deletion"

lemma size_delete_if_isin: "isin t x \<Longrightarrow> size t = Suc (size(delete x t))"
proof (induction t)
  case (Node _ a _ _)
  thus ?case
  proof (cases "cmp x a")
    case LT thus ?thesis using Node.prems by (simp add: Node.IH(1) not_Leaf_if_not_balanced1)
  next
    case EQ thus ?thesis by simp (metis size_length inorder_combine length_append)
  next
    case GT thus ?thesis using Node.prems by (simp add: Node.IH(2) not_Leaf_if_not_balanced1)
  qed
qed (auto)

lemma delete_id_if_wbt_notin: "wbt t \<Longrightarrow> \<not> isin t x \<Longrightarrow> delete x t = t"
by (induction t) auto

lemma size_split_min: "t \<noteq> Leaf \<Longrightarrow> size t = Suc (size (snd (split_min t)))"
by(induction t) (auto simp: not_Leaf_if_not_balanced1 split: if_splits prod.splits)

lemma size_del_max: "t \<noteq> Leaf \<Longrightarrow> size t = Suc(size(snd(del_max t)))"
by(induction t) (auto simp: not_Leaf_if_not_balanced1 split: if_splits prod.splits)


subsection "Auxiliary Definitions"

fun balanced1_arith :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"balanced1_arith a b = (\<Delta>1 * (a + 1) \<ge> \<Delta>2 * (b + 1))"

fun balanced2_arith :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"balanced2_arith a b = (balanced1_arith a b \<and> balanced1_arith b a)"

fun singly_balanced_arith :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"singly_balanced_arith x y w = (balanced2_arith x y \<and> balanced2_arith (x+y+1) w)"

fun doubly_balanced_arith :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"doubly_balanced_arith x y z w =
  (balanced2_arith x y \<and> balanced2_arith z w \<and> balanced2_arith (x+y+1) (z+w+1))"

end


subsection "Preservation of WB tree Invariant for Concrete Parameters"

text \<open>A number of sample interpretations with valid parameters:\<close>

interpretation WBT where
  \<Delta>1 = 25 and \<Delta>2 = 10 and \<Gamma>1 = 14 and \<Gamma>2 = 10
(* \<Delta>1 = 25 and \<Delta>2 = 10 and \<Gamma>1 = 15 and \<Gamma>2 = 10*)
(* \<Delta>1 = 28 and \<Delta>2 = 10 and \<Gamma>1 = 10 and \<Gamma>2 = 7*)

(* \<Delta>1 = 3 and \<Delta>2 = "Suc 0" and \<Gamma>1 = 4 and \<Gamma>2 = 3*)
  (* The only integer solution: *)
(* \<Delta>1 = 3 and \<Delta>2 = "Suc 0" and \<Gamma>1 = 2 and \<Gamma>2 = "Suc 0"*)
(* \<Delta>1 = 31 and \<Delta>2 = 10 and \<Gamma>1 = 18 and \<Gamma>2 = 10*)

(* \<Delta>1 = 35 and \<Delta>2 = 10 and \<Gamma>1 = 45 and \<Gamma>2 = 35*)
(* \<Delta>1 = 35 and \<Delta>2 = 10 and \<Gamma>1 = 4 and \<Gamma>2 = 3*)
(* \<Delta>1 = 37 and \<Delta>2 = 10 and \<Gamma>1 = 13 and \<Gamma>2 = 10*)

(* \<Delta>1 = 4 and \<Delta>2 = "Suc 0" and \<Gamma>1 = 5 and \<Gamma>2 = 4*)
(* \<Delta>1 = 4 and \<Delta>2 = "Suc 0" and \<Gamma>1 = 5 and \<Gamma>2 = 3*)
(* \<Delta>1 = 17 and \<Delta>2 = 4 and \<Gamma>1 = 5 and \<Gamma>2 = 3 *)
by (auto simp add: WBT_def)

lemma wbt_insert:
  "wbt t \<Longrightarrow> wbt (insert x t)"
proof (induction t)
  case Leaf show ?case by simp
next
  case (Node l a _ r)
  show ?case
  proof (cases "cmp x a")
    case EQ thus ?thesis using Node.prems by auto
  next
    case [simp]: LT
    let ?l' = "insert x l"
    show ?thesis
    proof (cases "balanced1 r ?l'")
      case True thus ?thesis using Node size_insert[of x l] by auto
    next
      case [simp]: False
      hence "?l' \<noteq> Leaf" using not_Leaf_if_not_balanced1 by auto
      then obtain k ll' al' rl' where [simp]: "?l' = (Node ll' al' k rl')"
        by(meson neq_Leaf2_iff)
      show ?thesis
      proof (cases "single rl' ll'")
        case True thus ?thesis using Node size_insert[of x l]
          by (auto split: if_splits)
      next
        case isDouble: False
        then obtain k llr' alr' rlr' where [simp]: "rl' = (Node llr' alr' k rlr')"
          using not_Leaf_if_not_single tree.exhaust by blast
        show ?thesis using isDouble Node size_insert[of x l]
          by (auto split: if_splits)
      qed
    qed
  next
    case [simp]: GT
    let ?r' = "insert x r"
    show ?thesis
    proof (cases "balanced1 l ?r'")
      case True thus ?thesis using Node size_insert[of x r] by auto
    next
      case [simp]: False
      hence "?r' \<noteq> Leaf" using not_Leaf_if_not_balanced1 by auto
      then obtain k lr' ar' rr' where [simp]: "?r' = (Node lr' ar' k rr')"
        by(meson neq_Leaf2_iff)
      show ?thesis
      proof (cases "single lr' rr'")
        case True thus ?thesis using Node size_insert[of x r]
          by (auto split: if_splits)
      next
        case isDouble: False
        hence "lr' \<noteq> Leaf" using not_Leaf_if_not_single by auto
        thus ?thesis
          using Node isDouble size_insert[of x r]
          by (auto simp: neq_Leaf2_iff split: if_splits)
      qed
    qed
  qed
qed

declare [[smt_nat_as_int]]

text \<open>
  Show that invariant is preserved by deletion in the left/right subtree:
\<close>

lemma wbt_balanceL:
  assumes "wbt (Node l a n r)" "wbt l'" "size l = size l' + 1"
  shows "wbt (balanceL l' a' r)"
proof -
  have rl'Balanced: "balanced1 r l'" using assms by auto
  have rBalanced: "wbt r" using assms(1) by simp
  show ?thesis
  proof (cases "balanced1 l' r")
    case True thus ?thesis using assms(2) rBalanced rl'Balanced by auto
  next
    case notBalanced: False
    hence "r \<noteq> Leaf" using not_Leaf_if_not_balanced1 by auto
    then obtain k lr ar rr where [simp]: "r = Node lr ar k rr" by(meson neq_Leaf2_iff)
    show ?thesis
    proof (cases "single lr rr")
      case single: True
      have "singly_balanced_arith (size l') (size lr) (size rr)"
        using assms(1) notBalanced rl'Balanced rBalanced single assms
        by (simp) (smt?)
      thus ?thesis using notBalanced single assms(2) rBalanced by simp
    next
      case isDouble: False
      hence "lr \<noteq> Leaf" using not_Leaf_if_not_single by auto
      then obtain k2 llr alr rlr where [simp]: "lr = (Node llr alr k2 rlr)"
        by(meson neq_Leaf2_iff)
      have "doubly_balanced_arith (size l') (size llr) (size rlr) (size rr)"
        using assms(1) notBalanced rl'Balanced rBalanced isDouble assms(2,3)
        apply (auto) apply((thin_tac "_ = _")+, smt)? done
      thus ?thesis using notBalanced isDouble assms(2) rBalanced by simp
    qed
  qed
qed

lemma wbt_balanceR:
  assumes "wbt (Node l a n r)" "wbt r'" "size r = size r' + 1"
  shows "wbt (balanceR l a' r')"
proof -
  have lr'Balanced: "balanced1 l r'" using assms by auto
  have lBalanced: "wbt l" using assms(1) by simp
  show ?thesis
  proof (cases "balanced1 r' l")
    case True thus ?thesis using assms(2) lBalanced lr'Balanced by simp
  next
    case notBalanced: False
    hence "l \<noteq> Leaf" using not_Leaf_if_not_balanced1 by auto
    then obtain k ll al rl where [simp]: "l = (Node ll al k rl)" by(meson neq_Leaf2_iff)
    show ?thesis
    proof (cases "single rl ll")
      case single: True
      have "singly_balanced_arith (size rl) (size r') (size ll)"
        using assms(1) notBalanced lr'Balanced lBalanced single assms(2,3)
        apply (auto) apply((thin_tac "_ = _")+, smt)? done
      thus ?thesis using assms(2) lBalanced notBalanced single by simp
    next
      case isDouble: False
      hence "rl \<noteq> Leaf" using not_Leaf_if_not_single by auto
      then obtain k lrl arl rrl where [simp]: "rl = (Node lrl arl k rrl)"
        by(meson neq_Leaf2_iff)
      have "doubly_balanced_arith (size ll) (size lrl) (size rrl) (size r')"
        using assms(1) notBalanced lr'Balanced lBalanced isDouble assms(2,3)
        apply (auto) apply((thin_tac "_ = _")+, smt)? done
      thus ?thesis using assms(2) lBalanced notBalanced isDouble by simp
    qed
  qed
qed

lemma wbt_split_min: "t \<noteq> Leaf \<Longrightarrow> wbt t \<Longrightarrow> wbt (snd (split_min t))"
proof (induction t rule: split_min.induct)
  case (1 l a m r)
  show ?case
  proof (cases l)
    case Leaf thus ?thesis using "1.prems"(2) by simp
  next
    case (Node ll al n rl)
    let ?l' = "snd (split_min (Node ll al n rl))"
    have delBalanceL: "snd (split_min (Node l a m r)) = balanceL ?l' a r"
      using Node by(auto split: prod.splits)
    have "wbt ?l'" using "1"(1) "1.prems"(2) Node by auto
    moreover have "size l = size ?l' + 1"
      using Node size_split_min by fastforce
    ultimately have "wbt (balanceL ?l' a r)"
      by (meson "1.prems"(2) wbt_balanceL)
    thus ?thesis using delBalanceL by auto
  qed
qed (blast)

lemma wbt_del_max: "t \<noteq> Leaf \<Longrightarrow> wbt t \<Longrightarrow> wbt (snd (del_max t))"
proof (induction t rule: del_max.induct)
  case (1 l a m r)
  show ?case
  proof (cases r)
    case Leaf thus ?thesis using "1.prems"(2) by simp
  next
    case (Node lr ar n rr)
    then obtain r' where delMaxR: "r' = snd (del_max (Node lr ar n rr))"
      by simp
    hence delBalanceR: "snd (del_max (Node l a m r)) = balanceR l a r'"
      using Node by(auto split: prod.splits)
    have "wbt r'" using "1"(1) "1.prems"(2) Node delMaxR by auto
    moreover have "size r = size r' + 1" using size_del_max Node delMaxR
      by (metis Suc_eq_plus1 tree.simps(3))
    ultimately have "wbt (balanceR l a r')"
      using wbt_balanceR by (metis "1.prems"(2))
    thus ?thesis using delBalanceR by auto
  qed
qed (blast)

lemma wbt_delete: "wbt t \<Longrightarrow> wbt (delete x t)"
proof (induction t)
  case Leaf thus ?case by simp
next
  case (Node l a n r)
  show ?case
  proof (cases "isin (Node l a n r) x")
    case False thus ?thesis using Node.prems delete_id_if_wbt_notin by metis
  next
    case isin: True
    thus ?thesis
    proof (cases "cmp x a")
      case LT
      let ?l' = "delete x l"
      have "size l = size ?l' + 1"
        using LT isin by (auto simp: size_delete_if_isin)
      hence "wbt (balanceL ?l' a r)"
        using Node.IH(1) Node.prems by (fastforce intro: wbt_balanceL)
      thus ?thesis by (simp add: LT)
    next
      case GT
      let ?r' = "delete x r"
      have "wbt ?r'" using Node.IH(2) Node.prems by simp
      moreover have "size r = size ?r' + 1"
        using GT Node.prems isin size_delete_if_isin by auto
      ultimately have "wbt (balanceR l a ?r')"
        by (meson Node.prems wbt_balanceR)
      thus ?thesis by (simp add: GT)
    next
      case [simp]: EQ
      hence xCombine: "delete x (Node l a n r) = combine l r" by simp
      {
        assume "l = Leaf" "r = Leaf" hence ?thesis by simp
      }
      moreover
      {
        assume "l = Leaf" "r \<noteq> Leaf"
        hence ?thesis using Node.prems by (auto simp: neq_Leaf2_iff)
      }
      moreover
      {
        assume "l \<noteq> Leaf" "r = Leaf"
        hence ?thesis using Node.prems by (auto simp: neq_Leaf2_iff)
      }
      moreover
      {
        assume lrNotLeaf: "l \<noteq> Leaf" "r \<noteq> Leaf"
        then obtain kl kr ll al rl lr ar rr
          where [simp]: "l = (Node ll al kl rl)" "r = (Node lr ar kr rr)"
          by (meson neq_Leaf2_iff)
        have ?thesis
        proof (cases "size l > size r")
          case True
          obtain lMax l' where letMax: "del_max l = (lMax, l')"
            by (metis prod.exhaust)
          hence balanceLeft: "combine l r = balanceL l' lMax r"
            using \<open>size l > size r\<close> by (simp)
          have "wbt l'"
            using Node.prems wbt_del_max[OF lrNotLeaf(1)] letMax
            by (metis wbt.simps(2) snd_conv)
          moreover have "size l = size l' + 1"
            using size_del_max[OF lrNotLeaf(1)] letMax by (simp)
          ultimately have "wbt(balanceL l' lMax r)"
            using wbt_balanceL by (metis Node.prems)
          thus ?thesis using balanceLeft by simp
        next
          case False
          obtain rMin r' where letMin: "split_min r = (rMin, r')"
            by (metis prod.exhaust)
          hence balanceRight: "combine l r = balanceR l rMin r'"
            using \<open>\<not> size l > size r\<close> by (simp)
          have "wbt r'"
            using Node.prems wbt_split_min[OF lrNotLeaf(2)] letMin
            by (metis wbt.simps(2) snd_conv)
          moreover have "size r = size r' + 1"
            using size_split_min[OF lrNotLeaf(2)] letMin by simp
          ultimately have "wbt(balanceR l rMin r')"
            using wbt_balanceR by (metis Node.prems)
          thus ?thesis using balanceRight by simp
        qed
      }
      ultimately show ?thesis by blast
    qed
  qed
qed

subsection \<open>The final correctness proof\<close>

interpretation S: Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = wbt
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 show ?case by simp
next
  case 6 thus ?case using wbt_insert by blast
next
  case 7 thus ?case using wbt_delete by blast
qed

end
