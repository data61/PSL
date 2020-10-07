(* Author: Wimmer *)
theory Floyd_Warshall
  imports Main
begin

chapter \<open>Floyd-Warshall Algorithm for the All-Pairs Shortest Paths Problem\<close>

section \<open>Introduction\<close>
text \<open>
  The \fw @{cite floyd and roy and warshall} is a classic dynamic programming algorithm to compute
  the length of all shortest paths between any two vertices in a graph
  (i.e. to solve the all-pairs shortest path problem, or \<open>APSP\<close> for short).
  Given a representation of the graph as a matrix of weights \<open>M\<close>, it computes another matrix \<open>M'\<close>
  which represents a graph with the same path lengths and contains the length of the shortest path
  between any two vertices \<open>i\<close> and \<open>j\<close>.
  This is only possible if the graph does not contain any negative cycles (then the length
  of the shortest path is \<open>-\<infinity>\<close>). However, in this case the \fw will detect the situation by
  calculating a negative diagonal entry corresponding to the negative cycle.
  In the following, we present a formalization of the algorithm and of the aforementioned
  key properties.

  Abstractly, the algorithm corresponds to the following imperative pseudo-code:
  \<^verbatim>\<open>
  for k = 1 .. n do
    for i = 1 .. n do
      for j = 1 .. n do
        m[i, j] := min(m[i, j], m[i, k] + m[k, j])
  \<close>

  However, we will carry out the whole formalization on a recursive version of the algorithm, and
  refine it to an efficient imperative version corresponding to the above pseudo-code in the end.
  The main observation underlying the algorithm is that the shortest path from \<open>i\<close> to \<open>j\<close> which only
  uses intermediate vertices from the set \<open>{0\<dots>k+1}\<close>, is: either the shortest path from \<open>i\<close> to \<open>j\<close>
  using intermediate vertices from the set \<open>{0\<dots>k}\<close>;
  or a combination of the shortest path from \<open>i\<close> to \<open>k\<close> and the shortest path from \<open>k\<close> to \<open>j\<close>,
  each of them only using intermediate vertices from \<open>{0\<dots>k}\<close>.
  Our presentation we be slightly more general than the typical textbook version, in that we will
  factor our the inner two loops as a separate algorithm and show that it has similar properties
  as the full algorithm for a single intermediate vertex \<open>k\<close>.
\<close>


section \<open>Preliminaries\<close>

subsection \<open>Cycles in Lists\<close>

abbreviation "cnt x xs \<equiv> length (filter (\<lambda>y. x = y) xs)"

fun remove_cycles :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove_cycles [] _ acc = rev acc" |
  "remove_cycles (x#xs) y acc =
    (if x = y then remove_cycles xs y [x] else remove_cycles xs y (x#acc))"

lemma cnt_rev: "cnt x (rev xs) = cnt x xs" by (metis length_rev rev_filter)

value "as @ [x] @ bs @ [x] @ cs @ [x] @ ds"

lemma remove_cycles_removes: "cnt x (remove_cycles xs x ys) \<le> max 1 (cnt x ys)"
proof (induction xs arbitrary: ys)
  case Nil thus ?case
  by (simp, cases "x \<in> set ys", (auto simp: cnt_rev[of x ys]))
next
  case (Cons y xs)
  thus ?case
  proof (cases "x = y")
    case True
    thus ?thesis using Cons[of "[y]"] True by auto
  next
    case False
    thus ?thesis using Cons[of "y # ys"] by auto
  qed
qed

lemma remove_cycles_id: "x \<notin> set xs \<Longrightarrow> remove_cycles xs x ys = rev ys @ xs"
by (induction xs arbitrary: ys) auto

lemma remove_cycles_cnt_id:
  "x \<noteq> y \<Longrightarrow> cnt y (remove_cycles xs x ys) \<le> cnt y ys + cnt y xs"
proof (induction xs arbitrary: ys x)
  case Nil thus ?case by (simp add: cnt_rev)
next
  case (Cons z xs)
  thus ?case
  proof (cases "x = z")
    case True thus ?thesis using Cons.IH[of z "[z]"] Cons.prems by auto
  next
    case False
    thus ?thesis using Cons.IH[of x "z # ys"] Cons.prems False by auto
  qed
qed

lemma remove_cycles_ends_cycle: "remove_cycles xs x ys \<noteq> rev ys @ xs \<Longrightarrow> x \<in> set xs"
using remove_cycles_id by fastforce

lemma remove_cycles_begins_with: "x \<in> set xs \<Longrightarrow> \<exists> zs. remove_cycles xs x ys = x # zs \<and> x \<notin> set zs"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  thus ?case
  proof (cases "x = y")
    case True thus ?thesis
    proof (cases "x \<in> set xs", goal_cases)
      case 1 with Cons show ?case by auto
    next
      case 2 with remove_cycles_id[of x xs "[y]"] show ?case by auto
    qed
  next
    case False
    with Cons show ?thesis by auto
  qed
qed

lemma remove_cycles_self:
  "x \<in> set xs \<Longrightarrow> remove_cycles (remove_cycles xs x ys) x zs = remove_cycles xs x ys"
proof -
  assume x:"x \<in> set xs"
  then obtain ws where ws: "remove_cycles xs x ys = x # ws" "x \<notin> set ws"
  using remove_cycles_begins_with[OF x, of ys] by blast
  from remove_cycles_id[OF this(2)] have "remove_cycles ws x [x] = x # ws" by auto
  with ws(1) show "remove_cycles (remove_cycles xs x ys) x zs = remove_cycles xs x ys" by simp
qed

lemma remove_cycles_one: "remove_cycles (as @ x # xs) x ys = remove_cycles (x#xs) x ys"
by (induction as arbitrary: ys) auto

lemma remove_cycles_cycles:
  "\<exists> xxs as. as @ concat (map (\<lambda> xs. x # xs) xxs) @ remove_cycles xs x ys = xs \<and> x \<notin> set as"
  if "x \<in> set xs"
using that proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  thus ?case
  proof (cases "x = y")
    case True thus ?thesis
    proof (cases "x \<in> set xs", goal_cases)
      case 1
      then obtain as xxs where "as @ concat (map (\<lambda>xs. y#xs) xxs) @ remove_cycles xs y [y] = xs"
      using Cons.IH[of "[y]"] by auto
      hence "[] @ concat (map (\<lambda>xs. x#xs) (as#xxs)) @ remove_cycles (y#xs) x ys = y # xs"
      by (simp add: \<open>x = y\<close>)
      thus ?thesis by fastforce
    next
      case 2
      hence "remove_cycles (y # xs) x ys = y # xs" using remove_cycles_id[of x xs "[y]"] by auto
      hence "[] @ concat (map (\<lambda>xs. x # xs) []) @ remove_cycles (y#xs) x ys = y # xs" by auto
      thus ?thesis by fastforce
    qed
  next
    case False
    then obtain as xxs where as:
      "as @ concat (map (\<lambda>xs. x # xs) xxs) @ remove_cycles xs x (y#ys) = xs" "x \<notin> set as"
    using Cons.IH[of "y # ys"] Cons.prems by auto
    hence "(y # as) @ concat (map (\<lambda>xs. x # xs) xxs) @ remove_cycles (y#xs) x ys = y # xs"
    using \<open>x \<noteq> y\<close> by auto
    thus ?thesis using as(2) \<open>x \<noteq> y\<close> by fastforce
  qed
qed

fun start_remove :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "start_remove [] _ acc = rev acc" |
  "start_remove (x#xs) y acc =
    (if x = y then rev acc @ remove_cycles xs y [y] else start_remove xs y (x # acc))"

lemma start_remove_decomp:
  "x \<in> set xs \<Longrightarrow> \<exists> as bs. xs = as @ x # bs \<and> start_remove xs x ys = rev ys @ as @ remove_cycles bs x [x]"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  thus ?case
  proof (auto, goal_cases)
    case 1
    from 1(1)[of "y # ys"]
    obtain as bs where
      "xs = as @ x # bs" "start_remove xs x (y # ys) = rev (y # ys) @ as @ remove_cycles bs x [x]"
    by blast
    hence "y # xs = (y # as) @ x # bs"
          "start_remove xs x (y # ys) = rev ys @ (y # as) @ remove_cycles bs x [x]" by simp+
    thus ?case by blast
  qed
qed

lemma start_remove_removes: "cnt x (start_remove xs x ys) \<le> Suc (cnt x ys)"
proof (induction xs arbitrary: ys)
  case Nil thus ?case using cnt_rev[of x ys] by auto
next
  case (Cons y xs)
  thus ?case
  proof (cases "x = y")
    case True
    thus ?thesis using remove_cycles_removes[of y xs "[y]"] cnt_rev[of y ys] by auto
  next
    case False
    thus ?thesis using Cons[of "y # ys"] by auto
  qed
qed

lemma start_remove_id[simp]: "x \<notin> set xs \<Longrightarrow> start_remove xs x ys = rev ys @ xs"
by (induction xs arbitrary: ys) auto

lemma start_remove_cnt_id:
  "x \<noteq> y \<Longrightarrow> cnt y (start_remove xs x ys) \<le> cnt y ys + cnt y xs"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by (simp add: cnt_rev)
next
  case (Cons z xs)
  thus ?case
  proof (cases "x = z", goal_cases)
    case 1 thus ?case using remove_cycles_cnt_id[of x y xs "[x]"] by (simp add: cnt_rev)
  next
    case 2 from this(1)[of "(z # ys)"] this(2,3) show ?case by auto
  qed
qed

fun remove_all_cycles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove_all_cycles [] xs = xs" |
  "remove_all_cycles (x # xs) ys = remove_all_cycles xs (start_remove ys x [])"

lemma cnt_remove_all_mono:"cnt y (remove_all_cycles xs ys) \<le> max 1 (cnt y ys)"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  thus ?case
  proof (cases "x = y")
    case True thus ?thesis using start_remove_removes[of y ys "[]"] Cons[of "start_remove ys y []"]
    by auto
  next
    case False
    hence "cnt y (start_remove ys x []) \<le> cnt y ys"
    using start_remove_cnt_id[of x y ys "[]"] by auto
    thus ?thesis using Cons[of "start_remove ys x []"] by auto
  qed
qed


lemma cnt_remove_all_cycles: "x \<in> set xs \<Longrightarrow> cnt x (remove_all_cycles xs ys) \<le> 1"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  thus ?case
  using start_remove_removes[of x ys "[]"] cnt_remove_all_mono[of y xs "start_remove ys y []"]
  by auto
qed

lemma cnt_mono:
  "cnt a (b # xs) \<le> cnt a (b # c # xs)"
by (induction xs) auto

lemma cnt_distinct_intro: "\<forall> x \<in> set xs. cnt x xs \<le> 1 \<Longrightarrow> distinct xs"
proof (induction xs)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  from this(2) have "\<forall> x \<in> set xs. cnt x xs \<le> 1"
  by (metis filter.simps(2) impossible_Cons linorder_class.linear list.set_intros(2)
      preorder_class.order_trans)
  with Cons.IH have "distinct xs" by auto
  moreover have "x \<notin> set xs" using Cons.prems
  proof (induction xs)
    case Nil then show ?case by auto
  next
    case (Cons a xs)
    from this(2) have "\<forall>xa\<in>set (x # xs). cnt xa (x # a # xs) \<le> 1"
    by auto
    then have *: "\<forall>xa\<in>set (x # xs). cnt xa (x # xs) \<le> 1"
    proof (safe, goal_cases)
      case (1 b)
      then have "cnt b (x # a # xs) \<le> 1" by auto
      with cnt_mono[of b x xs a] show ?case by fastforce
    qed
    with Cons(1) have "x \<notin> set xs" by auto
    moreover have "x \<noteq> a"
    by (metis (full_types) Cons.prems One_nat_def * empty_iff filter.simps(2) impossible_Cons
                           le_0_eq le_Suc_eq length_0_conv list.set(1) list.set_intros(1))
    ultimately show ?case by auto
  qed
  ultimately show ?case by auto
qed

lemma remove_cycles_subs:
  "set (remove_cycles xs x ys) \<subseteq> set xs \<union> set ys"
by (induction xs arbitrary: ys; auto; fastforce)

lemma start_remove_subs:
  "set (start_remove xs x ys) \<subseteq> set xs \<union> set ys"
using remove_cycles_subs by (induction xs arbitrary: ys; auto; fastforce)

lemma remove_all_cycles_subs:
  "set (remove_all_cycles xs ys) \<subseteq> set ys"
using start_remove_subs by (induction xs arbitrary: ys, auto) (fastforce+)

lemma remove_all_cycles_distinct: "set ys \<subseteq> set xs \<Longrightarrow> distinct (remove_all_cycles xs ys)"
proof -
  assume "set ys \<subseteq> set xs"
  hence "\<forall> x \<in> set ys. cnt x (remove_all_cycles xs ys) \<le> 1" using cnt_remove_all_cycles
    by fastforce
  hence "\<forall> x \<in> set (remove_all_cycles xs ys). cnt x (remove_all_cycles xs ys) \<le> 1"
  using remove_all_cycles_subs by fastforce
  thus "distinct (remove_all_cycles xs ys)" using cnt_distinct_intro by auto
qed

lemma distinct_remove_cycles_inv: "distinct (xs @ ys) \<Longrightarrow> distinct (remove_cycles xs x ys)"
proof (induction xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  thus ?case by auto
qed

definition
  "remove_all x xs = (if x \<in> set xs then tl (remove_cycles xs x []) else xs)"

definition
  "remove_all_rev x xs = (if x \<in> set xs then rev (tl (remove_cycles (rev xs) x [])) else xs)"

lemma remove_all_distinct:
  "distinct xs \<Longrightarrow> distinct (x # remove_all x xs)"
proof (cases "x \<in> set xs", goal_cases)
  case 1
  from remove_cycles_begins_with[OF 1(2), of "[]"] obtain zs
  where "remove_cycles xs x [] = x # zs" "x \<notin> set zs" by auto
  thus ?thesis using 1(1) distinct_remove_cycles_inv[of "xs" "[]" x] by (simp add: remove_all_def)
next
  case 2 thus ?thesis by (simp add: remove_all_def)
qed

lemma remove_all_removes:
  "x \<notin> set (remove_all x xs)"
by (metis list.sel(3) remove_all_def remove_cycles_begins_with)

lemma remove_all_subs:
  "set (remove_all x xs) \<subseteq> set xs"
using remove_cycles_subs remove_all_def
by (metis (no_types, lifting) append_Nil2 list.sel(2) list.set_sel(2) set_append subsetCE subsetI)

lemma remove_all_rev_distinct: "distinct xs \<Longrightarrow> distinct (x # remove_all_rev x xs)"
proof (cases "x \<in> set xs", goal_cases)
  case 1
  then have "x \<in> set (rev xs)" by auto
  from remove_cycles_begins_with[OF this, of "[]"] obtain zs
  where "remove_cycles (rev xs) x [] = x # zs" "x \<notin> set zs" by auto
  thus ?thesis using 1(1) distinct_remove_cycles_inv[of "rev xs" "[]" x]
    by (simp add: remove_all_rev_def)
next
  case 2 thus ?thesis by (simp add: remove_all_rev_def)
qed

lemma remove_all_rev_removes: "x \<notin> set (remove_all_rev x xs)"
by (metis remove_all_def remove_all_removes remove_all_rev_def set_rev)

lemma remove_all_rev_subs: "set (remove_all_rev x xs) \<subseteq> set xs"
by (metis remove_all_def remove_all_subs set_rev remove_all_rev_def)

abbreviation "rem_cycles i j xs \<equiv> remove_all i (remove_all_rev j (remove_all_cycles xs xs))"

lemma rem_cycles_distinct': "i \<noteq> j \<Longrightarrow> distinct (i # j # rem_cycles i j xs)"
proof -
  assume "i \<noteq> j"
  have "distinct (remove_all_cycles xs xs)" by (simp add: remove_all_cycles_distinct)
  from remove_all_rev_distinct[OF this] have
    "distinct (remove_all_rev j (remove_all_cycles xs xs))"
  by simp
  from remove_all_distinct[OF this] have "distinct (i # rem_cycles i j xs)" by simp
  moreover have
    "j \<notin> set (rem_cycles i j xs)"
  using remove_all_subs remove_all_rev_removes remove_all_removes by fastforce
  ultimately show ?thesis by (simp add: \<open>i \<noteq> j\<close>)
qed

lemma rem_cycles_removes_last: "j \<notin> set (rem_cycles i j xs)"
by (meson remove_all_rev_removes remove_all_subs rev_subsetD)

lemma rem_cycles_distinct: "distinct (rem_cycles i j xs)"
by (meson distinct.simps(2) order_refl remove_all_cycles_distinct
          remove_all_distinct remove_all_rev_distinct)

lemma rem_cycles_subs: "set (rem_cycles i j xs) \<subseteq> set xs"
by (meson order_trans remove_all_cycles_subs remove_all_subs remove_all_rev_subs)


section \<open>Definition of the Algorithm\<close>

subsection \<open>Definitions\<close>

text \<open>
  In our formalization of the \fw, edge weights are from a linearly ordered abelian monoid.
\<close>

class linordered_ab_monoid_add = linorder + ordered_comm_monoid_add
begin

subclass linordered_ab_semigroup_add ..

end

subclass (in linordered_ab_group_add) linordered_ab_monoid_add ..


context linordered_ab_monoid_add
begin

type_synonym 'c mat = "nat \<Rightarrow> nat \<Rightarrow> 'c"

definition upd :: "'c mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'c mat"
where
  "upd m x y v = m (x := (m x) (y := v))"

definition fw_upd :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw_upd m k i j \<equiv> upd m i j (min (m i j) (m i k + m k j))"

text \<open>Recursive version of the two inner loops.\<close>
fun fwi :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fwi m n k 0       0        = fw_upd m k 0 0" |
  "fwi m n k (Suc i) 0        = fw_upd (fwi m n k i n) k (Suc i) 0" |
  "fwi m n k i       (Suc j)  = fw_upd (fwi m n k i j) k i (Suc j)"

text \<open>Recursive version of the full algorithm.\<close>
fun fw :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw m n 0       = fwi m n 0 n n" |
  "fw m n (Suc k) = fwi (fw m n k) n (Suc k) n n"


subsection \<open>Elementary Properties\<close>

lemma fw_upd_mono:
  "fw_upd m k i j i' j' \<le> m i' j'"
by (cases "i = i'", cases "j = j'") (auto simp: fw_upd_def upd_def)

lemma fw_upd_out_of_bounds1:
  assumes "i' > i"
  shows "(fw_upd M k i j) i' j' = M i' j'"
using assms unfolding fw_upd_def upd_def by (auto split: split_min)

lemma fw_upd_out_of_bounds2:
  assumes "j' > j"
  shows "(fw_upd M k i j) i' j' = M i' j'"
using assms unfolding fw_upd_def upd_def by (auto split: split_min)

lemma fwi_out_of_bounds1:
  assumes "i' > n" "i \<le> n"
  shows "(fwi M n k i j) i' j' = M i' j'"
  using assms
  apply (induction _ "(i, j)" arbitrary: i j rule: wf_induct[of "less_than <*lex*> less_than"])
   apply (auto; fail)
  subgoal for i j
    by (cases i; cases j; auto simp add: fw_upd_out_of_bounds1)
  done

lemma fw_out_of_bounds1:
  assumes "i' > n"
  shows "(fw M n k) i' j' = M i' j'"
  using assms by (induction k; simp add: fwi_out_of_bounds1)

lemma fwi_out_of_bounds2:
  assumes "j' > n" "j \<le> n"
  shows "(fwi M n k i j) i' j' = M i' j'"
using assms
 apply (induction _ "(i, j)" arbitrary: i j rule: wf_induct[of "less_than <*lex*> less_than"])
 apply (auto; fail)
 subgoal for i j
 by (cases i; cases j; auto simp add: fw_upd_out_of_bounds2)
  done

lemma fw_out_of_bounds2:
  assumes "j' > n"
  shows "(fw M n k) i' j' = M i' j'"
  using assms by (induction k; simp add: fwi_out_of_bounds2)

lemma fwi_invariant_aux_1:
  "j'' \<le> j \<Longrightarrow> fwi m n k i j i' j' \<le> fwi m n k i j'' i' j'"
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j) thus ?case
  proof (cases "j'' = Suc j")
    case True thus ?thesis by simp
  next
    case False
    have "fw_upd (fwi m n k i j) k i (Suc j) i' j' \<le> fwi m n k i j i' j'"
      by (simp add: fw_upd_mono)
    thus ?thesis using Suc False by simp
  qed
qed

lemma fwi_invariant:
  "j \<le> n \<Longrightarrow> i'' \<le> i \<Longrightarrow> j'' \<le> j
   \<Longrightarrow> fwi m n k i j i' j' \<le> fwi m n k i'' j'' i' j'"
proof (induction i)
  case 0 thus ?case using fwi_invariant_aux_1 by auto
next
  case (Suc i) thus ?case
  proof (cases "i'' = Suc i")
    case True thus ?thesis using Suc fwi_invariant_aux_1 by simp
  next
    case False
    have "fwi m n k (Suc i) j i' j' \<le> fwi m n k (Suc i) 0 i' j'"
      by (rule fwi_invariant_aux_1[of 0]; simp)
    also have "\<dots> \<le> fwi m n k i n i' j'" by (simp add: fw_upd_mono)
    also have "\<dots> \<le> fwi m n k i j i' j'" using fwi_invariant_aux_1 False Suc by simp
    also have "\<dots> \<le> fwi m n k i'' j'' i' j'" using Suc False by simp
    finally show ?thesis by simp
  qed
qed

lemma single_row_inv:
  "j' < j \<Longrightarrow> fwi m n k i' j i' j' = fwi m n k i' j' i' j'"
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j) thus ?case by (cases "j' = j") (simp add: fw_upd_def upd_def)+
qed

lemma single_iteration_inv':
  "i' < i \<Longrightarrow> j' \<le> n \<Longrightarrow> fwi m n k i j i' j' = fwi m n k i' j' i' j'"
proof (induction i arbitrary: j)
  case 0 thus ?case by simp
next
  case (Suc i) thus ?case
  proof (induction j)
    case 0 thus ?case
    proof (cases "i = i'", goal_cases)
      case 2 thus ?case by (simp add: fw_upd_def upd_def)
    next
      case 1 thus ?case using single_row_inv[of j' n]
      by (cases "j' = n") (fastforce simp add: fw_upd_def upd_def)+
    qed
  next
    case (Suc j) thus ?case by (simp add: fw_upd_def upd_def)
  qed
qed

lemma single_iteration_inv:
  "i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> j \<le> n \<Longrightarrow> fwi m n k i j i' j' = fwi m n k i' j' i' j'"
proof (induction i arbitrary: j)
  case 0 thus ?case
  proof (induction j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using 0 by (cases "j' = Suc j") (simp add: fw_upd_def upd_def)+
  qed
next
  case (Suc i) thus ?case
  proof (induction j)
    case 0 thus ?case by (cases "i' = Suc i") (simp add: fw_upd_def upd_def)+
  next
    case (Suc j) thus ?case
    proof (cases "i' = Suc i", goal_cases)
      case 1 thus ?case
      proof (cases "j' = Suc j", goal_cases)
        case 1 thus ?case by simp
      next
        case 2 thus ?case by (simp add: fw_upd_def upd_def)
      qed
    next
      case 2 thus ?case
      proof (cases "j' = Suc j", goal_cases)
        case 1 thus ?case by - (rule single_iteration_inv'; simp)
      next
        case 2 thus ?case by (simp add: fw_upd_def upd_def)
      qed
    qed
  qed
qed

lemma fwi_innermost_id:
  "i' < i \<Longrightarrow> fwi m n k i' j' i j = m i j"
proof (induction i' arbitrary: j')
  case 0 thus ?case
  proof (induction j')
    case 0 thus ?case by (simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp: fw_upd_def upd_def)
  qed
next
  case (Suc i') thus ?case
  proof (induction j')
    case 0 thus ?case by (auto simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp add: fw_upd_def upd_def)
  qed
qed

lemma fwi_middle_id:
  "j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> fwi m n k i' j' i j = m i j"
proof (induction i' arbitrary: j')
  case 0 thus ?case
  proof (induction j')
    case 0 thus ?case by (simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp: fw_upd_def upd_def)
  qed
next
  case (Suc i') thus ?case
  proof (induction j')
    case 0 thus ?case using fwi_innermost_id by (auto simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp add: fw_upd_def upd_def)
  qed
qed

lemma fwi_outermost_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fwi m n k i j i j \<le> m i j"
proof (cases j)
  case 0
  assume "i \<le> n"
  thus ?thesis
  proof (cases i)
    case 0 thus ?thesis using \<open>j = 0\<close> by (simp add: fw_upd_def upd_def)
  next
    case (Suc i')
    hence "fwi m n k i' n (Suc i') 0 = m (Suc i') 0" using fwi_innermost_id \<open>i \<le> n\<close> by simp
    thus ?thesis using \<open>j = 0\<close> Suc by (simp add: fw_upd_def upd_def)
  qed
next
  case (Suc j')
  assume "i \<le> n" "j \<le> n"
  hence "fwi m n k i j' i (Suc j') = m i (Suc j')"
  using fwi_middle_id Suc by simp
  thus ?thesis using Suc by (simp add: fw_upd_def upd_def)
qed

lemma fwi_mono:
  "fwi m n k i' j' i j \<le> m i j" if "i \<le> n" "j \<le> n"
proof (cases "i' < i")
  case True
  then have "fwi m n k i' j' i j = m i j"
    by (simp add: fwi_innermost_id)
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "i' > i")
    case True
    then have "fwi m n k i' j' i j = fwi m n k i j i j"
      by (simp add: single_iteration_inv' that(2))
    with fwi_outermost_mono[OF that] show ?thesis by simp
  next
    case False
    with \<open>\<not> i' < i\<close> have [simp]: "i' = i" by simp
    show ?thesis
    proof (cases "j' < j")
      case True
      then have "fwi m n k i' j' i j = m i j"
        by (simp add: fwi_middle_id)
      then show ?thesis by simp
    next
      case False
      then have "fwi m n k i' j' i j = fwi m n k i j i j"
        by (cases "j' = j"; simp add: single_row_inv)
      with fwi_outermost_mono[OF that] show ?thesis by simp
    qed
  qed
qed

lemma Suc_innermost_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n (Suc k) i j \<le> fw m n k i j"
  by (simp add: fwi_mono)

lemma fw_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n k i j \<le> m i j"
proof (induction k)
  case 0 thus ?case using fwi_mono by simp
next
  case (Suc k) thus ?case using Suc_innermost_mono[OF Suc.prems, of m k] by simp
qed

text \<open>
  Justifies the use of destructive updates in the case that there is no negative cycle for \<open>k\<close>.
\<close>
lemma fwi_step:
  "m k k \<ge> 0 \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fwi m n k i j i j = min (m i j) (m i k + m k j)"
proof (induction _ "(i, j)" arbitrary: i j rule: wf_induct[of "less_than <*lex*> less_than"],
      (auto; fail), goal_cases)
  case (1 i' j')
  note assms = 1(2-)
  note IH = 1(1)
  note [simp] = fwi_innermost_id fwi_middle_id
  note simps = add_increasing add_increasing2 ord.min_def fw_upd_def upd_def
  show ?case
  proof (cases i')
    case [simp]: 0 thus ?thesis
    proof (cases j')
      case 0 thus ?thesis by (simp add: fw_upd_def upd_def)
    next
      case (Suc j)
      hence "fwi m n k 0 j 0 (Suc j) = m 0 (Suc j)" by simp
      moreover have "fwi m n k 0 j k (Suc j) = m k (Suc j)" by simp
      moreover have "fwi m n k 0 j 0 k = m 0 k"
      proof (cases "j < k")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
          apply (subst single_iteration_inv; simp)
          subgoal
            using assms Suc by auto
          using assms by (cases k; simp add: simps)
      qed
      ultimately show ?thesis using Suc assms by (simp add: fw_upd_def upd_def)
    qed
  next
    case [simp]: (Suc i)
    show ?thesis
    proof (cases j')
      case 0
      have "fwi m n k i n (Suc i) 0 = m (Suc i) 0" by simp
      moreover have "fwi m n k i n (Suc i) k = m (Suc i) k" by simp
      moreover have "fwi m n k i n k 0 = m k 0"
      proof (cases "i < k")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
          apply (subst single_iteration_inv; simp)
          using 0 \<open>m k k \<ge> _\<close> by (cases k; simp add: simps)
      qed
      ultimately show ?thesis using 0 by (simp add: fw_upd_def upd_def)
    next
      case Suc_j: (Suc j)
      from \<open>j' \<le> n\<close> \<open>j' = _\<close> have [simp]: "j \<le> n" "Suc j \<le> n" by simp+
      have diag: "fwi m n k k k k k = m k k" if "k \<le> i"
      proof -
        from that IH assms have "fwi m n k k k k k = min (m k k) (m k k + m k k)" by auto
        with \<open>m k k \<ge> 0\<close> \<open>k \<le> n\<close> show ?thesis by (simp add: simps)
      qed
      have **: "fwi m n k i n k k = m k k"
      proof (cases "i < k")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
          by (subst single_iteration_inv; simp add: diag \<open>k \<le> n\<close>)
      qed
      have diag2: "fwi m n k k j k k = m k k" if "k \<le> i"
      proof (cases "j < k")
        case True
        then show ?thesis by simp
      next
        case False
        with \<open>k \<le> i\<close> show ?thesis
          by (subst single_iteration_inv; simp add: diag)
      qed
      have ***: "fwi m n k (Suc i) j k (Suc j) = m k (Suc j)"
      proof (cases "Suc i \<le> k")
        case True
        then show ?thesis by simp
      next
        case False
        then have "fwi m n k k j k (Suc j) = m k (Suc j)"
          by simp
        with False \<open>m k k \<ge> 0\<close> show ?thesis
          by (subst single_iteration_inv'; simp add: simps diag2)
      qed
      have "fwi m n k (Suc i) j (Suc i) k = m (Suc i) k"
      proof (cases "j < k")
        case True thus ?thesis by simp
      next
        case False
        then show ?thesis
          apply (subst single_iteration_inv; simp)
          apply (cases k)
          subgoal premises prems
          proof -
            have "fwi m n 0 i n 0 0 \<ge> 0"
              using ** assms(1) prems(2) by force
            moreover have "fwi m n 0 i n (Suc i) 0 = m (Suc i) 0"
              by simp
            ultimately show ?thesis
              using prems by (simp add: simps)
          qed
          subgoal premises prems for k'
          proof -
            have "fwi m n (Suc k') (Suc i) k' (Suc k') (Suc k') \<ge> 0"
              by (metis ** assms(1,4) fwi_innermost_id fwi_middle_id le_SucE lessI
                    linorder_class.not_le_imp_less prems(2) preorder_class.order_refl
                    single_iteration_inv single_iteration_inv'
                 )
            with prems show ?thesis
              by (simp add: simps)
          qed
          done
      qed
      moreover have "fwi m n k (Suc i) j (Suc i) (Suc j) = m (Suc i) (Suc j)" by simp
      ultimately show ?thesis using \<open>j' = _\<close> by (simp add: simps ***)
    qed
  qed
qed


section \<open>Result Under The Absence of Negative Cycles\<close>

text \<open>
  If the given input graph does not contain any negative cycles, the \fw computes the
  \<^bold>\<open>unique\<close> shortest paths matrix corresponding to the graph. It contains the shortest path
  between any two nodes \<open>i, j \<le> n\<close>.
\<close>


subsection \<open>Length of Paths\<close>

fun len :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a" where
  "len m u v [] = m u v" |
  "len m u v (w#ws) = m u w + len m w v ws"

lemma len_decomp: "xs = ys @ y # zs \<Longrightarrow> len m x z xs = len m x y ys + len m y z zs"
by (induction ys arbitrary: x xs) (simp add: add.assoc)+

lemma len_comp: "len m a c (xs @ b # ys) = len m a b xs + len m b c ys"
by (induction xs arbitrary: a) (auto simp: add.assoc)


subsection \<open>Canonicality\<close>

text \<open>
  The unique shortest path matrices are in a so-called \<open>canonical form\<close>.
  We will say that a matrix \<open>m\<close> is in canonical form for a set of indices \<open>I\<close>
  if the following holds:
\<close>

definition canonical_subs :: "nat \<Rightarrow> nat set \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "canonical_subs n I m = (\<forall> i j k. i \<le> n \<and> k \<le> n \<and> j \<in> I \<longrightarrow> m i k \<le> m i j + m j k)"

text \<open>
  Similarly we express that \<open>m\<close> does not contain a negative cycle which only uses intermediate
  vertices from the set \<open>I\<close> as follows:
\<close>
abbreviation cyc_free_subs :: "nat \<Rightarrow> nat set \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "cyc_free_subs n I m \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> I \<longrightarrow> len m i i xs \<ge> 0"

text \<open>
  To prove the main result under \<open>the absence of negative cycles\<close>, we will proceed as follows:
  \<^item> we show that an invocation of \<open>fwi m n k n n\<close> extends canonicality to index \<open>k\<close>,
  \<^item> we show that an invocation of \<open>fw m n n\<close> computes a matrix in canonical form,
  \<^item> and finally we show that canonical forms specify the lengths of \<open>shortest paths\<close>,
    provided that there are no negative cycles.
\<close>

text \<open>Canonical forms specify lower bounds for the length of any path.\<close>
lemma canonical_subs_len:
  "M i j \<le> len M i j xs" if "canonical_subs n I M" "i \<le> n" "j \<le> n" "set xs \<subseteq> I" "I \<subseteq> {0..n}"
using that
proof (induction xs arbitrary: i)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then have "M x j \<le> len M x j xs" by auto
  from Cons.prems \<open>canonical_subs n I M\<close> have "M i j \<le> M i x + M x j"
    unfolding canonical_subs_def by auto
  also with Cons have "\<dots> \<le> M i x + len M x j xs" by (auto simp add: add_mono)
  finally show ?case by simp
qed

text \<open>
  This lemma justifies the use of destructive updates under the absence of negative cycles.
\<close>
lemma fwi_step':
  "fwi m n k i' j' i j = min (m i j) (m i k + m k j)" if
  "m k k \<ge> 0" "i' \<le> n" "j' \<le> n" "k \<le> n" "i \<le> i'" "j \<le> j'"
  using that by (subst single_iteration_inv; auto simp: fwi_step)

text \<open>An invocation of \<open>fwi\<close> extends canonical forms.\<close>
lemma fwi_canonical_extend:
  "canonical_subs n (I \<union> {k}) (fwi m n k n n)" if
  "canonical_subs n I m" "I \<subseteq> {0..n}" "0 \<le> m k k" "k \<le> n"
  using that
  unfolding canonical_subs_def
  apply safe
  subgoal for i j k'
    apply (subst fwi_step', (auto; fail)+)+
    unfolding min_def
  proof (clarsimp, safe, goal_cases)
    case 1
    then show ?case by force
  next
    case prems: 2
    from prems have "m i k \<le> m i j + m j k"
      by auto
    with prems(10) show ?case
      by (auto simp: add.assoc[symmetric] add_mono intro: order.trans)
  next
    case prems: 3
    from prems have "m i k \<le> m i j + m j k"
      by auto
    with prems(10) show ?case
      by (auto simp: add.assoc[symmetric] add_mono intro: order.trans)
  next
    case prems: 4
    from prems have "m k k' \<le> m k j + m j k'"
      by auto
    with prems(10) show ?case
      by (auto simp: add_mono add.assoc intro: order.trans)
  next
    case prems: 5
    from prems have "m k k' \<le> m k j + m j k'"
      by auto
    with prems(10) show ?case
      by (auto simp: add_mono add.assoc intro: order.trans)
  next
    case prems: 6
    from prems have "0 \<le> m k j + m j k"
      by (auto intro: order.trans)
    with prems(10) show ?case
      apply -
      apply (rule order.trans, assumption)
      apply (simp add: add.assoc[symmetric])
      by (rule add_mono, auto simp: add_increasing2 add.assoc intro: order.trans)
  next
    case prems: 7
    from prems have "0 \<le> m k j + m j k"
      by (auto intro: order.trans)
    with prems(10) show ?case
      by (simp add: add.assoc[symmetric])
        (rule add_mono, auto simp: add_increasing2 add.assoc intro: order.trans)
  qed
  subgoal for i j k'
    apply (subst fwi_step', (auto; fail)+)+
    unfolding min_def by (auto intro: add_increasing add_increasing2)
  done

text \<open>
  An invocation of \<open>fwi\<close> will not produce a negative diagonal entry if there is no negative cycle.
\<close>
lemma fwi_cyc_free_diag:
  "fwi m n k n n i i \<ge> 0" if
  "cyc_free_subs n I m" "0 \<le> m k k" "k \<le> n" "k \<in> I" "i \<le> n"
  using that
  apply (subst fwi_step', (auto; fail)+)+
  unfolding min_def
  proof (clarsimp; safe, goal_cases)
    case 1
    have "set [] \<subseteq> I"
      by simp
    with 1(1) \<open>i \<le> n\<close> show ?case
      by fastforce
  next
    case 2
    then have "set [k] \<subseteq> I"
      by simp
    with 2(1) \<open>i \<le> n\<close> show ?case by fastforce
  qed

lemma cyc_free_subs_diag:
  "m i i \<ge> 0" if "cyc_free_subs n I m" "i \<le> n"
proof -
  have "set [] \<subseteq> I" by auto
  with that show ?thesis by fastforce
qed

lemma fwi_cyc_free_subs':
  "cyc_free_subs n (I \<union> {k}) (fwi m n k n n)" if
  "cyc_free_subs n I m" "canonical_subs n I m" "I \<subseteq> {0..n}" "k \<le> n"
  "\<forall> i \<le> n. fwi m n k n n i i \<ge> 0"
proof (safe, goal_cases)
  case prems: (1 i xs)
  from that(1) \<open>k \<le> n\<close> have "0 \<le> m k k" by (rule cyc_free_subs_diag)
  from that \<open>0 \<le> m k k\<close> have *: "canonical_subs n (I \<union> {k}) (fwi m n k n n)"
    by - (rule fwi_canonical_extend; auto)
  from prems that have "0 \<le> fwi m n k n n i i" by blast
  also from * prems that have "fwi m n k n n i i \<le> len (fwi m n k n n) i i xs"
    by (auto intro: canonical_subs_len)
  finally show ?case .
qed

lemma fwi_cyc_free_subs:
  "cyc_free_subs n (I \<union> {k}) (fwi m n k n n)" if
  "cyc_free_subs n (I \<union> {k}) m" "canonical_subs n I m" "I \<subseteq> {0..n}" "k \<le> n"
proof (safe, goal_cases)
  case prems: (1 i xs)
  from that(1) \<open>k \<le> n\<close> have "0 \<le> m k k" by (rule cyc_free_subs_diag)
  from that \<open>0 \<le> m k k\<close> have *: "canonical_subs n (I \<union> {k}) (fwi m n k n n)"
    by - (rule fwi_canonical_extend; auto)
  from prems that \<open>0 \<le> m k k\<close> have "0 \<le> fwi m n k n n i i" by (auto intro!: fwi_cyc_free_diag)
  also from * prems that have "fwi m n k n n i i \<le> len (fwi m n k n n) i i xs"
    by (auto intro: canonical_subs_len)
  finally show ?case .
qed

lemma canonical_subs_empty [simp]:
  "canonical_subs n {} m"
  unfolding canonical_subs_def by simp

lemma fwi_neg_diag_neg_cycle:
  "\<exists> i \<le> n. \<exists> xs. set xs \<subseteq> {0..k} \<and> len m i i xs < 0" if "fwi m n k n n i i < 0" "i \<le> n" "k \<le> n"
proof (cases "m k k \<ge> 0")
  case True
  from fwi_step'[of m, OF True] that have "min (m i i) (m i k + m k i) < 0"
    by auto
  then show ?thesis
    unfolding min_def
  proof (clarsimp split: if_split_asm, goal_cases)
    case 1
    then have "len m i i [] < 0" "set [] \<subseteq> {}" by auto
    with \<open>i \<le> n\<close> show ?case by fastforce
  next
    case 2
    then have "len m i i [k] < 0" "set [k] \<subseteq> {0..k}" by auto
    with \<open>i \<le> n\<close> show ?case by fastforce
  qed
next
  case False
  with \<open>k \<le> n\<close> have "len m k k [] < 0" "set [] \<subseteq> {}" by auto
  with \<open>k \<le> n\<close> show ?thesis by fastforce
qed

text \<open>\<open>fwi\<close> preserves the length of paths.\<close>
lemma fwi_len:
  "\<exists> ys. set ys \<subseteq> set xs \<union> {k} \<and> len (fwi m n k n n) i j xs = len m i j ys"
  if "i \<le> n" "j \<le> n" "k \<le> n" "m k k \<ge> 0" "set xs \<subseteq> {0..n}"
  using that
proof (induction xs arbitrary: i)
  case Nil
  then show ?case
    apply (simp add: fwi_step')
    unfolding min_def
    apply (clarsimp; safe)
     apply (rule exI[where x = "[]"]; simp)
    by (rule exI[where x = "[k]"]; simp)
next
  case (Cons x xs)
  then obtain ys where "set ys \<subseteq> set xs \<union> {k}" "len (fwi m n k n n) x j xs = len m x j ys"
    by force
  with Cons.prems show ?case
    apply (simp add: fwi_step')
    unfolding min_def
    apply (clarsimp; safe)
     apply (rule exI[where x = "x # ys"]; auto; fail)
    by (rule exI[where x = "k # x # ys"]; auto simp: add.assoc)
qed

lemma fwi_neg_cycle_neg_cycle:
  "\<exists> i \<le> n. \<exists> ys. set ys \<subseteq> set xs \<union> {k} \<and> len m i i ys < 0" if
  "len (fwi m n k n n) i i xs < 0" "i \<le> n" "k \<le> n" "set xs \<subseteq> {0..n}"
proof (cases "m k k \<ge> 0")
  case True
  from fwi_len[OF that(2,2,3), of m, OF True that(4)] that(1,2) show ?thesis
    by safe (rule exI conjI | simp)+
next
  case False
  then have "len m k k [] < 0" "set [] \<subseteq> set xs \<union> {k}"
    by auto
  with \<open>k \<le> n\<close> show ?thesis by (intro exI conjI)
qed

text \<open>
  If the \fw produces a negative diagonal entry, then there is a negative cycle.
\<close>
lemma fw_neg_diag_neg_cycle:
  "\<exists> i \<le> n. \<exists> ys. set ys \<subseteq> set xs \<union> {0..k} \<and> len m i i ys < 0" if
  "len (fw m n k) i i xs < 0" "i \<le> n" "k \<le> n" "set xs \<subseteq> {0..n}"
  using that
  proof (induction k arbitrary: i xs)
    case 0
    then show ?case by simp (drule fwi_neg_cycle_neg_cycle; auto)
  next
    case (Suc k)
    from fwi_neg_cycle_neg_cycle[OF Suc.prems(1)[simplified]] Suc.prems obtain i' ys where
      "i' \<le> n"  "set ys \<subseteq> set xs \<union> {Suc k}" "len (fw m n k) i' i' ys < 0"
      by auto
    with Suc.prems obtain i'' zs where
      "i'' \<le> n" "set zs \<subseteq> set ys \<union> {0..k}" "len m i'' i'' zs < 0"
      by atomize_elim (auto intro!: Suc.IH)
    with \<open>set ys \<subseteq> _\<close> have "set zs \<subseteq> set xs \<union> {0..Suc k} \<and> len m i'' i'' zs < 0"
      by force
    with \<open>i'' \<le> n\<close> show ?case by blast
  qed

text \<open>Main theorem under the absence of negative cycles.\<close>
theorem fw_correct:
  "canonical_subs n {0..k} (fw m n k) \<and> cyc_free_subs n {0..k} (fw m n k)"
  if "cyc_free_subs n {0..k} m" "k \<le> n"
  using that
proof (induction k)
  case 0
  then show ?case
    using fwi_cyc_free_subs[of n "{}" 0 m] fwi_canonical_extend[of n "{}"]
    by (auto simp: cyc_free_subs_diag)
next
  case (Suc k)
  then have IH:
    "canonical_subs n {0..k} (fw m n k) \<and> cyc_free_subs n {0..k} (fw m n k)"
    by fastforce
  have *: "{0..Suc k} = {0..k} \<union> {Suc k}" by auto
  then have **: "canonical_subs n {0..Suc k} (fw m n (Suc k))"
    apply simp
    apply (rule fwi_canonical_extend[of n "{0..k}" _ "Suc k", simplified])
    subgoal
      using IH ..
    subgoal
      using IH Suc.prems by (auto intro: cyc_free_subs_diag[of n "{0..k}" "fw m n k"])
    by (rule Suc)
  show ?case
  proof (cases "\<exists>i\<le>n. fw m n (Suc k) i i < 0")
    case True
    then obtain i where "i \<le> n" "len (fw m n (Suc k)) i i [] < 0"
      by auto
    from fw_neg_diag_neg_cycle[OF this(2,1) \<open>Suc k \<le> n\<close>] Suc.prems show ?thesis by fastforce
  next
    case False
    have "cyc_free_subs n {0..Suc k} (fw m n (Suc k))"
      apply (simp add: *)
      apply (rule fwi_cyc_free_subs'[of n "{0..k}", simplified])
      using Suc IH False by force+
    with ** show ?thesis by blast
  qed
qed

lemmas fw_canonical_subs = fw_correct[THEN conjunct1]
lemmas fw_cyc_free_subs = fw_correct[THEN conjunct2]
lemmas cyc_free_diag = cyc_free_subs_diag


section \<open>Definition of Shortest Paths\<close>

text \<open>
  We define the notion of the length of the shortest \<open>simple\<close> path between two vertices,
  using only intermediate vertices from the set \<open>{0\<dots>k}\<close>.
\<close>
definition D :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "D m i j k \<equiv> Min {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"

lemma distinct_length_le:"finite s \<Longrightarrow> set xs \<subseteq> s \<Longrightarrow> distinct xs \<Longrightarrow> length xs \<le> card s"
by (metis card_mono distinct_card)

lemma finite_distinct: "finite s \<Longrightarrow> finite {xs . set xs \<subseteq> s \<and> distinct xs}"
proof -
  assume "finite s"
  hence "{xs . set xs \<subseteq> s \<and> distinct xs} \<subseteq> {xs. set xs \<subseteq> s \<and> length xs \<le> card s}"
  using distinct_length_le by auto
  moreover have "finite {xs. set xs \<subseteq> s \<and> length xs \<le> card s}"
  using finite_lists_length_le[OF \<open>finite s\<close>] by auto
  ultimately show ?thesis by (rule finite_subset)
qed

lemma D_base_finite:
  "finite {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct xs}"
using finite_distinct finite_image_set by blast

lemma D_base_finite':
  "finite {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct (i # j # xs)}"
proof -
  have "{len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct (i # j # xs)}
        \<subseteq> {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct xs}" by auto
  with D_base_finite[of m i j k] show ?thesis by (rule rev_finite_subset)
qed

lemma D_base_finite'':
  "finite {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
using D_base_finite[of m i j k] by - (rule finite_subset, auto)

definition cycle_free :: "'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "cycle_free m n \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<longrightarrow>
  (\<forall> j. j \<le> n \<longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs) \<and> len m i i xs \<ge> 0"

lemma D_eqI:
  fixes m n i j k
  defines "A \<equiv> {len m i j xs | xs. set xs \<subseteq> {0..k}}"
  defines "A_distinct \<equiv> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  assumes "cycle_free m n" "i \<le> n" "j \<le> n" "k \<le> n" "(\<And>y. y \<in> A_distinct \<Longrightarrow> x \<le> y)" "x \<in> A"
  shows "D m i j k = x" using assms
proof -
  let ?S = "{len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  show ?thesis unfolding D_def
  proof (rule Min_eqI)
    have "?S \<subseteq> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> distinct xs}" by auto
    thus "finite {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
    using D_base_finite[of m i j k] by (rule finite_subset)
  next
    fix y assume "y \<in> ?S"
    hence "y \<in> A_distinct" using assms(2,7) by fastforce
    thus "x \<le> y" using assms by meson
  next
    from assms obtain xs where xs: "x = len m i j xs" "set xs \<subseteq> {0..k}" by auto
    let ?ys = "rem_cycles i j xs"
    let ?y = "len m i j ?ys"
    from assms(3-6) xs have *:"?y \<le> x" by (fastforce simp add: cycle_free_def)
    have distinct: "i \<notin> set ?ys" "j \<notin> set ?ys" "distinct ?ys"
    using rem_cycles_distinct remove_all_removes rem_cycles_removes_last by fast+
    with xs(2) have "?y \<in> A_distinct" unfolding A_distinct_def using rem_cycles_subs by fastforce
    hence "x \<le> ?y" using assms by meson
    moreover have "?y \<le> x" using assms(3-6) xs by (fastforce simp add: cycle_free_def)
    ultimately have "x = ?y" by simp
    thus "x \<in> ?S" using distinct xs(2) rem_cycles_subs[of i j xs] by fastforce
  qed
qed

lemma D_base_not_empty:
   "{len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs} \<noteq> {}"
proof -
  have "len m i j [] \<in> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  by fastforce
  thus ?thesis by auto
qed

lemma Min_elem_dest: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x = Min A \<Longrightarrow> x \<in> A" by simp

lemma D_dest: "x = D m i j k \<Longrightarrow>
  x \<in> {len m i j xs |xs. set xs \<subseteq> {0..Suc k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
using Min_elem_dest[OF D_base_finite'' D_base_not_empty] by (fastforce simp add: D_def)

lemma D_dest': "x = D m i j k \<Longrightarrow> x \<in> {len m i j xs |xs. set xs \<subseteq> {0..Suc k}}"
using Min_elem_dest[OF D_base_finite'' D_base_not_empty] by (fastforce simp add: D_def)

lemma D_dest'': "x = D m i j k \<Longrightarrow> x \<in> {len m i j xs |xs. set xs \<subseteq> {0..k}}"
using Min_elem_dest[OF D_base_finite'' D_base_not_empty] by (fastforce simp add: D_def)

lemma cycle_free_loop_dest: "i \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> cycle_free m n \<Longrightarrow> len m i i xs \<ge> 0"
unfolding cycle_free_def by auto

lemma cycle_free_dest:
  "cycle_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n}
    \<Longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs"
by (auto simp add: cycle_free_def)

definition cycle_free_up_to :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cycle_free_up_to m k n \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> {0..k} \<longrightarrow>
  (\<forall> j. j \<le> n \<longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs) \<and> len m i i xs \<ge> 0"

lemma cycle_free_up_to_loop_dest:
  "i \<le> n \<Longrightarrow> set xs \<subseteq> {0..k} \<Longrightarrow> cycle_free_up_to m k n \<Longrightarrow> len m i i xs \<ge> 0"
unfolding cycle_free_up_to_def by auto

lemma cycle_free_up_to_diag:
  assumes "cycle_free_up_to m k n" "i \<le> n"
  shows "m i i \<ge> 0"
using cycle_free_up_to_loop_dest[OF assms(2) _ assms(1), of "[]"] by auto

lemma D_eqI2:
  fixes m n i j k
  defines "A \<equiv> {len m i j xs | xs. set xs \<subseteq> {0..k}}"
  defines "A_distinct \<equiv> {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  assumes "cycle_free_up_to m k n" "i \<le> n" "j \<le> n" "k \<le> n"
          "(\<And>y. y \<in> A_distinct \<Longrightarrow> x \<le> y)" "x \<in> A"
  shows "D m i j k = x" using assms
proof -
  show ?thesis
  proof (simp add: D_def A_distinct_def[symmetric], rule Min_eqI)
    show "finite A_distinct" using D_base_finite''[of m i j k] unfolding A_distinct_def by auto
  next
    fix y assume "y \<in> A_distinct"
    thus "x \<le> y" using assms by meson
  next
    from assms obtain xs where xs: "x = len m i j xs" "set xs \<subseteq> {0..k}" by auto
    let ?ys = "rem_cycles i j xs"
    let ?y = "len m i j ?ys"
    from assms(3-6) xs have *:"?y \<le> x" by (fastforce simp add: cycle_free_up_to_def)
    have distinct: "i \<notin> set ?ys" "j \<notin> set ?ys" "distinct ?ys"
    using rem_cycles_distinct remove_all_removes rem_cycles_removes_last by fast+
    with xs(2) have "?y \<in> A_distinct" unfolding A_distinct_def using rem_cycles_subs by fastforce
    hence "x \<le> ?y" using assms by meson
    moreover have "?y \<le> x" using assms(3-6) xs by (fastforce simp add: cycle_free_up_to_def)
    ultimately have "x = ?y" by simp
    then show "x \<in> A_distinct" using distinct xs(2) rem_cycles_subs[of i j xs]
    unfolding A_distinct_def by fastforce
  qed
qed

subsection \<open>Connecting the Algorithm to the Notion of Shortest Paths\<close>

text \<open>
  Under the absence of negative cycles, the \fw correctly computes the length of the shortest path
  between any pair of vertices \<open>i, j\<close>.
\<close>
lemma canonical_D:
  assumes
    "cycle_free_up_to m k n" "canonical_subs n {0..k} m" "i \<le> n" "j \<le> n" "k \<le> n"
  shows "D m i j k = m i j"
  using assms
  apply -
  apply (rule D_eqI2)
       apply (assumption | simp; fail)+
  subgoal
    by (auto intro: canonical_subs_len)
  apply clarsimp
  by (rule exI[where x = "[]"]) auto


theorem fw_subs_len:
  "(fw m n k) i j \<le> len m i j xs" if
  "cyc_free_subs n {0..k} m" "k \<le> n" "i \<le> n" "j \<le> n" "set xs \<subseteq> I" "I \<subseteq> {0..k}"
proof -
  from fw_correct[OF that(1,2)] have "canonical_subs n {0..k} (fw m n k)" ..
  from canonical_subs_len[OF this, of i j xs] that have "fw m n k i j \<le> len (fw m n k) i j xs"
    by auto
  also from that(2-) have "\<dots> \<le> len m i j xs"
  proof (induction xs arbitrary: i)
    case Nil
    then show ?case by (auto intro: fw_mono)
  next
    case (Cons x xs)
    then have "len (fw m n k) x j xs \<le> len m x j xs"
      by auto
    moreover from Cons.prems have "fw m n k i x \<le> m i x" by - (rule fw_mono; auto)
    ultimately show ?case by (auto simp: add_mono)
  qed
  finally show ?thesis by auto
qed

text \<open>
  This shows that the value calculated by \<open>fwi\<close> for a pair \<open>i, j\<close> always corresponds to the length
  of an actual path between \<open>i\<close> and \<open>j\<close>.
\<close>
lemma fwi_len':
  "\<exists> xs. set xs \<subseteq> {k} \<and> fwi m n k i' j' i j = len m i j xs" if
  "m k k \<ge> 0" "i' \<le> n" "j' \<le> n" "k \<le> n" "i \<le> i'" "j \<le> j'"
  using that apply (subst fwi_step'; auto)
  unfolding min_def
  apply (clarsimp; safe)
   apply (rule exI[where x = "[]"]; auto; fail)
  by (rule exI[where x = "[k]"]; auto; fail)

text \<open>
  The same result for \<open>fw\<close>.
\<close>
lemma fw_len:
  "\<exists> xs. set xs \<subseteq> {0..k} \<and> fw m n k i j = len m i j xs" if
  "cyc_free_subs n {0..k} m" "i \<le> n" "j \<le> n" "k \<le> n"
  using that
proof (induction k arbitrary: i j)
  case 0
  from cyc_free_subs_diag[OF this(1)] have "m 0 0 \<ge> 0" by blast
  with 0 show ?case by (auto intro: fwi_len')
next
  case (Suc k)
  have IH: "\<exists> xs. set xs \<subseteq> {0..k} \<and> fw m n k i j = len m i j xs" if "i \<le> n" "j \<le> n" for i j
    apply (rule Suc.IH)
    using Suc.prems that by force+
  from fw_cyc_free_subs[OF Suc.prems(1,4)] have "cyc_free_subs n {0..Suc k} (fw m n (Suc k))" .
  then have "0 \<le> fw m n k (Suc k) (Suc k)" using IH Suc.prems(1, 4) by fastforce
  with Suc.prems fwi_len'[of "fw m n k" "Suc k" n n n i j] obtain xs where
    "set xs \<subseteq> {Suc k}" "fwi (fw m n k) n (Suc k) n n i j = len (fw m n k) i j xs"
    by auto
  moreover from Suc.prems(2-) this(1) have
    "\<exists> ys. set ys \<subseteq> {0..Suc k} \<and> len (fw m n k) i j xs = len m i j ys"
  proof (induction xs arbitrary: i)
    case Nil
    then show ?case by (force dest: IH)
  next
    case (Cons x xs)
    then obtain ys where ys:
      "set ys \<subseteq> {0..Suc k}" "len (fw m n k) x j xs = len m x j ys"
      by force
    moreover from IH[of i x] Cons.prems obtain zs where
      "set zs \<subseteq> {0..k}" "fw m n k i x = len m i x zs"
      by auto
    ultimately have
      "set (zs @ x # ys) \<subseteq> {0..Suc k}" "len (fw m n k) i j (x # xs) = len m i j (zs @ x # ys)"
      using \<open>Suc k \<le> n\<close> \<open>set (x # xs) \<subseteq> _\<close> by (auto simp: len_comp)
    then show ?case by (intro exI conjI)
  qed
  ultimately show ?case by auto
qed


section \<open>Intermezzo: Equivalent Characterizations of Cycle-Freeness\<close>

subsection \<open>Shortening Negative Cycles\<close>

lemma remove_cycles_neg_cycles_aux:
  fixes i xs ys
  defines "xs' \<equiv> i # ys"
  assumes "i \<notin> set ys"
  assumes "i \<in> set xs"
  assumes "xs = as @ concat (map ((#) i) xss) @ xs'"
  assumes "len m i j ys > len m i j xs"
  shows "\<exists> ys. set ys \<subseteq> set xs \<and> len m i i ys < 0" using assms
proof (induction xss arbitrary: xs as)
  case Nil
  with Nil show ?case
  proof (cases "len m i i as \<ge> 0", goal_cases)
    case 1
    from this(4,6) len_decomp[of xs as i ys m i j]
    have "len m i j xs = len m i i as + len m i j ys" by simp
    with 1(11)
    have "len m i j ys \<le> len m i j xs" using add_mono by fastforce
    thus ?thesis using Nil(5) by auto
  next
    case 2 thus ?case by auto
  qed
next
  case (Cons zs xss)
  let ?xs = "zs @ concat (map ((#) i) xss) @ xs'"
  from Cons show ?case
  proof (cases "len m i i as \<ge> 0", goal_cases)
    case 1
    from this(5,7) len_decomp add_mono
    have "len m i j ?xs \<le> len m i j xs" by fastforce
    hence 4:"len m i j ?xs < len m i j ys" using 1(6) by simp
    have 2:"i \<in> set ?xs" using Cons(2) by auto
    have "set ?xs \<subseteq> set xs" using Cons(5) by auto
    moreover from Cons(1)[OF 1(2,3) 2 _ 4] have "\<exists>ys. set ys \<subseteq> set ?xs \<and> len m i i ys < 0" by auto
    ultimately show ?case by blast
  next
    case 2
    from this(5,7) show ?case by auto
  qed
qed

lemma add_lt_neutral: "a + b < b \<Longrightarrow> a < 0"
proof (rule ccontr)
  assume "a + b < b" "\<not> a < 0"
  hence "a \<ge> 0" by auto
  from add_mono[OF this, of b b] \<open>a + b < b\<close> show False by auto
qed

lemma remove_cycles_neg_cycles_aux':
  fixes j xs ys
  assumes "j \<notin> set ys"
  assumes "j \<in> set xs"
  assumes "xs = ys @ j # concat (map (\<lambda> xs. xs @ [j]) xss) @ as"
  assumes "len m i j ys > len m i j xs"
  shows "\<exists> ys. set ys \<subseteq> set xs \<and> len m j j ys < 0" using assms
proof (induction xss arbitrary: xs as)
  case Nil
  show ?case
  proof (cases "len m j j as \<ge> 0")
    case True
    from Nil(3) len_decomp[of xs ys j as m i j]
    have "len m i j xs = len m i j ys + len m j j as" by simp
    with True
    have "len m i j ys \<le> len m i j xs" using add_mono by fastforce
    with Nil show ?thesis by auto
  next
    case False with Nil show ?thesis by auto
  qed
next
  case (Cons zs xss)
  let ?xs = "ys @ j # concat (map (\<lambda>xs. xs @ [j]) xss) @ as"
  let ?t = "concat (map (\<lambda>xs. xs @ [j]) xss) @ as"
  show ?case
  proof (cases "len m i j ?xs \<le> len m i j xs")
    case True
    hence 4:"len m i j ?xs < len m i j ys" using Cons(5) by simp
    have 2:"j \<in> set ?xs" using Cons(2) by auto
    have "set ?xs \<subseteq> set xs" using Cons(4) by auto
    moreover from Cons(1)[OF Cons(2) 2 _ 4] have "\<exists>ys. set ys \<subseteq> set ?xs \<and> len m j j ys < 0" by blast
    ultimately show ?thesis by blast
  next
    case False
    hence "len m i j xs < len m i j ?xs" by auto
    from this len_decomp Cons(4) add_mono
    have "len m j j (concat (map (\<lambda>xs. xs @ [j]) (zs # xss)) @ as) < len m j j ?t"
    using False local.leI by fastforce
    hence "len m j j (zs @ j # ?t) < len m j j ?t" by simp
    with len_decomp[of "zs @ j # ?t" zs j ?t m j j]
    have "len m j j zs + len m j j ?t < len m j j ?t" by auto
    hence "len m j j zs < 0" using add_lt_neutral by auto
    thus ?thesis using Cons.prems(3) by auto
  qed
qed

lemma add_le_impl: "a + b < a + c \<Longrightarrow> b < c"
proof (rule ccontr)
  assume "a + b < a + c" "\<not> b < c"
  hence "b \<ge> c" by auto
  from add_mono[OF _ this, of a a] \<open>a + b < a + c\<close> show False by auto
qed

lemma start_remove_neg_cycles:
  "len m i j (start_remove xs k []) > len m i j xs \<Longrightarrow> \<exists> ys. set ys \<subseteq> set xs \<and> len m k k ys < 0"
proof-
  let ?xs = "start_remove xs k []"
  assume len_lt:"len m i j ?xs > len m i j xs"
  hence "k \<in> set xs" using start_remove_id by fastforce
  from start_remove_decomp[OF this, of "[]"] obtain as bs where as_bs:
    "xs = as @ k # bs" "?xs = as @ remove_cycles bs k [k]"
  by fastforce
  let ?xs' = "remove_cycles bs k [k]"
  have "k \<in> set bs" using as_bs len_lt remove_cycles_id by fastforce
  then obtain ys where ys: "?xs = as @ k # ys" "?xs' = k # ys" "k \<notin> set ys"
  using as_bs(2) remove_cycles_begins_with[OF \<open>k \<in> set bs\<close>] by auto
  have len_lt': "len m k j bs < len m k j ys"
  using len_decomp[OF as_bs(1), of m i j] len_decomp[OF ys(1), of m i j] len_lt add_le_impl by metis
  from remove_cycles_cycles[OF \<open>k \<in> set bs\<close>] obtain xss as'
  where "as' @ concat (map ((#) k) xss) @ ?xs' = bs" by fastforce
  hence "as' @ concat (map ((#) k) xss) @ k # ys = bs" using ys(2) by simp
  from remove_cycles_neg_cycles_aux[OF \<open>k \<notin> set ys\<close> \<open>k \<in> set bs\<close> this[symmetric] len_lt']
  show ?thesis using as_bs(1) by auto
qed

lemma remove_all_cycles_neg_cycles:
  "len m i j (remove_all_cycles ys xs) > len m i j xs
  \<Longrightarrow> \<exists> ys k. set ys \<subseteq> set xs \<and> k \<in> set xs \<and> len m k k ys < 0"
proof (induction ys arbitrary: xs)
  case Nil thus ?case by auto
next
  case (Cons y ys)
  let ?xs = "start_remove xs y []"
  show ?case
  proof (cases "len m i j xs < len m i j ?xs")
    case True
    with start_remove_id have "y \<in> set xs" by fastforce
    with start_remove_neg_cycles[OF True] show ?thesis by blast
  next
    case False
    with Cons(2) have "len m i j ?xs < len m i j (remove_all_cycles (y # ys) xs)" by auto
    hence "len m i j ?xs < len m i j (remove_all_cycles ys ?xs)" by auto
    from Cons(1)[OF this] show ?thesis using start_remove_subs[of xs y "[]"] by auto
  qed
qed

lemma concat_map_cons_rev:
  "rev (concat (map ((#) j) xss)) = concat (map (\<lambda> xs. xs @ [j]) (rev (map rev xss)))"
by (induction xss) auto

lemma negative_cycle_dest: "len m i j (rem_cycles i j xs) > len m i j xs
       \<Longrightarrow> \<exists> i' ys. len m i' i' ys < 0 \<and> set ys \<subseteq> set xs \<and> i' \<in> set (i # j # xs)"
proof -
  let ?xsij = "rem_cycles i j xs"
  let ?xsj  = "remove_all_rev j (remove_all_cycles xs xs)"
  let ?xs   = "remove_all_cycles xs xs"
  assume len_lt: "len m i j ?xsij > len m i j xs"
  show ?thesis
  proof (cases "len m i j ?xsij \<le> len m i j ?xsj")
    case True
    hence len_lt: "len m i j ?xsj > len m i j xs" using len_lt by simp
    show ?thesis
    proof (cases "len m i j ?xsj \<le> len m i j ?xs")
      case True
      hence "len m i j ?xs > len m i j xs" using len_lt by simp
      with remove_all_cycles_neg_cycles[OF this] show ?thesis by auto
    next
      case False
      then have len_lt': "len m i j ?xsj > len m i j ?xs" by simp
      show ?thesis
      proof (cases "j \<in> set ?xs")
        case False
        thus ?thesis using len_lt' by (simp add: remove_all_rev_def)
      next
        case True
          from remove_all_rev_removes[of j] have 1: "j \<notin> set ?xsj" by simp
          from True have "j \<in> set (rev ?xs)" by auto
          from remove_cycles_cycles[OF this] obtain xss as where as:
          "as @ concat (map ((#) j) xss) @ remove_cycles (rev ?xs) j [] = rev ?xs" "j \<notin> set as"
          by blast
          from True have "?xsj = rev (tl (remove_cycles (rev ?xs) j []))" by (simp add: remove_all_rev_def)
          with remove_cycles_begins_with[OF \<open>j \<in> set (rev ?xs)\<close>, of "[]"]
          have "remove_cycles (rev ?xs) j [] = j # rev ?xsj" "j \<notin> set ?xsj"
          by auto
          with as(1) have xss: "as @ concat (map ((#) j) xss) @ j # rev ?xsj = rev ?xs" by simp
          hence "rev (as @ concat (map ((#) j) xss) @ j # rev ?xsj) = ?xs" by simp
          hence "?xsj @ j # rev (concat (map ((#) j) xss)) @ rev as = ?xs" by simp
          hence "?xsj @ j # concat (map (\<lambda> xs. xs @ [j]) (rev (map rev xss))) @ rev as = ?xs"
          by (simp add: concat_map_cons_rev)
          from remove_cycles_neg_cycles_aux'[OF 1 True this[symmetric] len_lt']
          show ?thesis using remove_all_cycles_subs by fastforce
      qed
    qed
  next
    case False
    hence len_lt': "len m i j ?xsij > len m i j ?xsj" by simp
    show ?thesis
    proof (cases "i \<in> set ?xsj")
      case False
      thus ?thesis using len_lt' by (simp add: remove_all_def)
    next
      case True
      from remove_all_removes[of i] have 1: "i \<notin> set ?xsij" by (simp add: remove_all_def)
      from remove_cycles_cycles[OF True] obtain xss as where as:
      "as @ concat (map ((#) i) xss) @ remove_cycles ?xsj i [] = ?xsj" "i \<notin> set as" by blast
      from True have "?xsij = tl (remove_cycles ?xsj i [])" by (simp add: remove_all_def)
      with remove_cycles_begins_with[OF True, of "[]"]
      have "remove_cycles ?xsj i [] = i # ?xsij" "i \<notin> set ?xsij"
      by auto
      with as(1) have xss: "as @ concat (map ((#) i) xss) @ i # ?xsij = ?xsj" by simp
      from remove_cycles_neg_cycles_aux[OF 1 True this[symmetric] len_lt']
      show ?thesis using remove_all_rev_subs remove_all_cycles_subs by fastforce
    qed
  qed
qed


subsection \<open>Cycle-Freeness\<close>

lemma cycle_free_alt_def:
  "cycle_free M n \<longleftrightarrow> cycle_free_up_to M n n"
  unfolding cycle_free_def cycle_free_up_to_def ..

lemma negative_cycle_dest_diag:
  "\<not> cycle_free_up_to m k n \<Longrightarrow> k \<le> n \<Longrightarrow> \<exists> i xs. i \<le> n \<and> set xs \<subseteq> {0..k} \<and> len m i i xs < 0"
proof (auto simp: cycle_free_up_to_def, goal_cases)
  case (1 i xs j)
  from this(5) have "len m i j xs < len m i j (rem_cycles i j xs)" by auto
  from negative_cycle_dest[OF this] obtain i' ys
  where *:"len m i' i' ys < 0" "set ys \<subseteq> set xs" "i' \<in> set (i # j # xs)" by auto
  from this(2,3) 1(1-4) have "set ys \<subseteq> {0..k}" "i' \<le> n" by auto
  with * show ?case by auto
next
  case 2 then show ?case by fastforce
qed

lemma negative_cycle_dest_diag':
  "\<not> cycle_free m n \<Longrightarrow> \<exists> i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<and> len m i i xs < 0"
  by (rule negative_cycle_dest_diag) (auto simp: cycle_free_alt_def)

abbreviation cyc_free :: "'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "cyc_free m n \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<longrightarrow> len m i i xs \<ge> 0"

lemma cycle_free_diag_intro:
  "cyc_free m n \<Longrightarrow> cycle_free m n"
  using negative_cycle_dest_diag' by force

lemma cycle_free_diag_equiv:
  "cyc_free m n \<longleftrightarrow> cycle_free m n" using negative_cycle_dest_diag'
  by (force simp: cycle_free_def)

lemma cycle_free_diag_dest:
  "cycle_free m n \<Longrightarrow> cyc_free m n"
  using cycle_free_diag_equiv by blast

lemma cycle_free_upto_diag_equiv:
  "cycle_free_up_to m k n \<longleftrightarrow> cyc_free_subs n {0..k} m" if "k \<le> n"
  using negative_cycle_dest_diag[of m k n] that by (force simp: cycle_free_up_to_def)

theorem fw_shortest_path_up_to:
  "D m i j k = fw m n k i j" if "cyc_free_subs n {0..k} m" "i \<le> n" "j \<le> n" "k \<le> n"
proof -
  from that(1,4) have cycle_free: "cycle_free_up_to m k n" by (subst cycle_free_upto_diag_equiv)
  from that have "canonical_subs n {0..k} (fw m n k)" "cyc_free_subs n {0..k} (fw m n k)"
    by (auto dest: fw_correct)
  show ?thesis
  proof (rule D_eqI2[where n = n], safe, goal_cases)
      case (5 y xs)
    with that(1) that show ?case by (auto intro: fw_subs_len)
  next
    case 6
    from fw_len[OF that(1) that(2-)] show ?case by blast
  qed (rule that cycle_free)+
qed

text \<open>We do not need to prove this because the definitions match.\<close>
lemma
  "cyc_free m n \<longleftrightarrow> cyc_free_subs n {0..n} m" ..

lemma cycle_free_cycle_free_up_to:
  "cycle_free m n \<Longrightarrow> k \<le> n \<Longrightarrow> cycle_free_up_to m k n"
unfolding cycle_free_def cycle_free_up_to_def by force

lemma cycle_free_diag:
  "cycle_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> 0 \<le> m i i"
using cycle_free_up_to_diag[OF cycle_free_cycle_free_up_to] by blast

corollary fw_shortest_path:
  "cyc_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> D m i j k = fw m n k i j"
by (rule fw_shortest_path_up_to; force)

corollary fw_shortest:
  assumes "cyc_free m n" "i \<le> n" "j \<le> n" "k \<le> n"
  shows "fw m n n i j \<le> fw m n n i k + fw m n n k j"
  using fw_canonical_subs[OF assms(1)] assms(2-) unfolding canonical_subs_def by auto


section \<open>Result Under the Presence of Negative Cycles\<close>

text \<open>
  Under the presence of negative cycles, the \fw will detect the situation by computing a negative
  diagonal entry.
\<close>

lemma not_cylce_free_dest: "\<not> cycle_free m n \<Longrightarrow> \<exists> k \<le> n. \<not> cycle_free_up_to m k n"
by (auto simp add: cycle_free_def cycle_free_up_to_def)

lemma D_not_diag_le:
  "(x :: 'a) \<in> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}
  \<Longrightarrow> D m i j k \<le> x" using Min_le[OF D_base_finite''] by (auto simp add: D_def)

lemma D_not_diag_le': "set xs \<subseteq> {0..k} \<Longrightarrow> i \<notin> set xs \<Longrightarrow> j \<notin> set xs \<Longrightarrow> distinct xs
  \<Longrightarrow> D m i j k \<le> len m i j xs" using Min_le[OF D_base_finite''] by (fastforce simp add: D_def)

lemma nat_upto_subs_top_removal':
  "S \<subseteq> {0..Suc n} \<Longrightarrow> Suc n \<notin> S \<Longrightarrow> S \<subseteq> {0..n}"
apply (induction n)
 apply safe
 apply (rename_tac x)
 apply (case_tac "x = Suc 0"; fastforce)
apply (rename_tac n x)
apply (case_tac "x = Suc (Suc n)"; fastforce)
done

lemma nat_upto_subs_top_removal:
  "S \<subseteq> {0..n::nat} \<Longrightarrow> n \<notin> S \<Longrightarrow> S \<subseteq> {0..n - 1}"
using nat_upto_subs_top_removal' by (cases n; simp)

text \<open>Monotonicity with respect to \<open>k\<close>.\<close>
lemma fw_invariant:
  "k' \<le> k \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw m n k i j \<le> fw m n k' i j"
proof (induction k)
  case 0
  then show ?case by (auto intro: fwi_invariant)
next
  case (Suc k)
  show ?case
  proof (cases "k' = Suc k")
    case True
    then show ?thesis by simp
  next
    case False
    with Suc have "fw m n k i j \<le> fw m n k' i j"
      by auto
    moreover from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have "fw m n (Suc k) i j \<le> fw m n k i j"
      by (auto intro: fwi_mono)
    ultimately show ?thesis by auto
  qed
qed

lemma negative_len_shortest:
  "length xs = n \<Longrightarrow> len m i i xs < 0
    \<Longrightarrow> \<exists> j ys. distinct (j # ys) \<and> len m j j ys < 0 \<and> j \<in> set (i # xs) \<and> set ys \<subseteq> set xs"
proof (induction n arbitrary: xs i rule: less_induct)
  case (less n)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis using less.prems by auto
  next
    case (Cons y ys)
    then have "length xs \<ge> 1" by auto
    show ?thesis
    proof (cases "i \<in> set xs")
      assume i: "i \<in> set xs"
      then obtain as bs where xs: "xs = as @ i # bs" by (meson split_list)
      show ?thesis
      proof (cases "len m i i as < 0")
        case True
        from xs less.prems have "length as < n" by auto
        from less.IH[OF this _ True] xs show ?thesis by auto
      next
        case False
        from len_decomp[OF xs] have "len m i i xs = len m i i as + len m i i bs" by auto
        with False less.prems have *: "len m i i bs < 0"
        by (metis add_lt_neutral local.dual_order.strict_trans local.neqE)
        from xs less.prems have "length bs < n" by auto
        from less.IH[OF this _ *] xs show ?thesis by auto
      qed
    next
      assume i: "i \<notin> set xs"
      show ?thesis
      proof (cases "distinct xs")
        case True
        with i less.prems show ?thesis by auto
      next
        case False
        from not_distinct_decomp[OF this] obtain a as bs cs where xs:
          "xs = as @ a # bs @ a # cs"
        by auto
        show ?thesis
        proof (cases "len m a a bs < 0")
          case True
          from xs less.prems have "length bs < n" by auto
          from less.IH[OF this _ True] xs show ?thesis by auto
        next
          case False
          from len_decomp[OF xs, of m  i i] len_decomp[of "bs @ a # cs" bs a cs m a i]
          have *:"len m i i xs = len m i a as + (len m a a bs + len m a i cs)" by auto
          from False have "len m a a bs \<ge> 0" by auto
          with add_mono have "len m a a bs + len m a i cs \<ge> len m a i cs" by fastforce
          with * have "len m i i xs \<ge> len m i a as + len m a i cs" by (simp add: add_mono)
          with less.prems(2) have "len m i a as + len m a i cs < 0" by auto
          with len_comp have "len m i i (as @ a # cs) < 0" by auto
          from less.IH[OF _ _ this, of "length (as @ a # cs)"] xs less.prems
          show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma fw_upd_leI:
  "fw_upd m' k i j i j \<le> fw_upd m k i j i j" if
  "m' i k \<le> m i k" "m' k j \<le> m k j" "m' i j \<le> m i j"
  using that unfolding fw_upd_def upd_def min_def using add_mono by fastforce

lemma fwi_fw_upd_mono:
  "fwi m n k i j i j \<le> fw_upd m k i j i j" if "k \<le> n" "i \<le> n" "j \<le> n"
  using that by (cases i; cases j) (auto intro: fw_upd_leI fwi_mono)

text \<open>
  The \fw will always detect negative cycles. The argument goes as follows:
  In case there is a negative cycle, then we know that there is some smallest \<open>k\<close> for which
  there is a negative cycle containing only intermediate vertices from the set \<open>{0\<dots>k}\<close>.
  We will show that then \<open>fwi m n k\<close> computes a negative entry on the diagonal, and thus,
  by monotonicity, \<open>fw m n n\<close> will compute a negative entry on the diagonal.
\<close>
theorem FW_neg_cycle_detect:
  "\<not> cyc_free m n \<Longrightarrow> \<exists> i \<le> n. fw m n n i i < 0"
proof -
  assume A: "\<not> cyc_free m n"
  let ?K = "{k. k \<le> n \<and> \<not> cyc_free_subs n {0..k} m}"
  define k where "k = Min ?K"
  have not_empty_K: "?K \<noteq> {}" using A by auto
  have "finite ?K" by auto
  with not_empty_K have *:
    "\<forall> k' < k. cyc_free_subs n {0..k'} m"
    unfolding k_def
    by simp (meson order_class.dual_order.trans preorder_class.less_le_not_le)
  from linorder_class.Min_in[OF \<open>finite ?K\<close> \<open>?K \<noteq> {}\<close>] have
    "\<not> cyc_free_subs n {0..k} m" "k \<le> n"
    unfolding k_def by auto
  then have "\<exists> xs j. j \<le> n \<and> len m j j xs < 0 \<and> set xs \<subseteq> {0..k}"
    by force
  then obtain a as where a_as: "a \<le> n \<and> len m a a as < 0 \<and> set as \<subseteq> {0..k}" by auto
  with negative_len_shortest[of as "length as" m a] obtain j xs where j_xs:
  "distinct (j # xs) \<and> len m j j xs < 0 \<and> j \<in> set (a # as) \<and> set xs \<subseteq> set as" by auto
  with a_as \<open>k \<le> n\<close> have cyc: "j \<le> n" "set xs \<subseteq> {0..k}" "len m j j xs < 0" "distinct (j # xs)"
    by auto
  { assume "k > 0"
    then have "k - 1 < k" by simp
    with * have **:"cyc_free_subs n {0..k - 1} m" by blast
    have "k \<in> set xs"
    proof (rule ccontr, goal_cases)
      case 1
      with \<open>set xs \<subseteq> {0..k}\<close> nat_upto_subs_top_removal have "set xs \<subseteq> {0..k-1}" by auto
      with \<open>cyc_free_subs n {0..k - 1} m\<close> \<open>j \<le> n\<close> have "0 \<le> len m j j xs" by blast
      with cyc(3) show ?case by simp
    qed
    with cyc(4) have "j \<noteq> k" by auto
    from \<open>k \<in> set xs\<close> obtain ys zs where "xs = ys @ k # zs" by (meson split_list)
    with \<open>distinct (j # xs)\<close>
    have xs: "xs = ys @ k # zs" "distinct ys" "distinct zs" "k \<notin> set ys" "k \<notin> set zs"
             "j \<notin> set ys" "j \<notin> set zs" by auto
    from xs(1,4) \<open>set xs \<subseteq> {0..k}\<close> nat_upto_subs_top_removal have ys: "set ys \<subseteq> {0..k-1}" by auto
    from xs(1,5) \<open>set xs \<subseteq> {0..k}\<close> nat_upto_subs_top_removal have zs: "set zs \<subseteq> {0..k-1}" by auto
    have "D m j k (k - 1) = fw m n (k - 1) j k"
      using \<open>k \<le> n\<close> \<open>j \<le> n\<close> fw_shortest_path_up_to[OF **] by auto
    moreover have "D m k j (k - 1) = fw m n (k - 1) k j"
      using \<open>k \<le> n\<close> \<open>j \<le> n\<close> fw_shortest_path_up_to[OF **] by auto
    ultimately have "fw m n (k - 1) j k + fw m n (k - 1) k j \<le> len m j k ys + len m k j zs"
      using D_not_diag_le'[OF zs(1) xs(5,7,3), of m] D_not_diag_le'[OF ys(1) xs(6,4,2), of m]
      by (auto simp: add_mono)
    then have neg: "fw m n (k - 1) j k + fw m n (k - 1) k j < 0"
      using xs(1) \<open>len m j j xs < 0\<close> len_comp by auto
    have "fw m n k j j \<le> fw m n (k - 1) j k + fw m n (k - 1) k j"
    proof -
      from \<open>k > 0\<close> have *: "fw m n k = fwi (fw m n (k - 1)) n k n n"
        by (cases k) auto
      from fw_cyc_free_subs[OF **, THEN cyc_free_subs_diag] \<open>k \<le> n\<close> have
        "fw m n (k - 1) k k \<ge> 0"
        by auto
      from fwi_step'[of "fw m n (k - 1)", OF this] \<open>k \<le> n\<close> \<open>j \<le> n\<close> show ?thesis
        by (auto intro: min.cobounded2 simp: *)
    qed
    with neg have "fw m n k j j < 0" by auto
    moreover from fw_invariant \<open>j \<le> n\<close> \<open>k \<le> n\<close> have "fw m n n j j \<le> fw m n k j j"
      by blast
    ultimately have ?thesis using \<open>j \<le> n\<close> by auto
  }
  moreover
  { assume "k = 0"
    with cyc(2,4) have "xs = [] \<or> xs = [0]"
      apply safe
      apply (case_tac xs)
       apply fastforce
      apply (rename_tac ys)
      apply (case_tac ys)
       apply auto
    done
    then have ?thesis
    proof
      assume "xs = []"
      with cyc have "m j j < 0" by auto
      with fw_mono[of j n j m n] \<open>j \<le> n\<close> have "fw m n n j j < 0" by auto
      with \<open>j \<le> n\<close> show ?thesis by auto
    next
      assume xs: "xs = [0]"
      with cyc have "m j 0 + m 0 j < 0" by auto
      moreover from \<open>j \<le> n\<close> have "fw m n 0 j j \<le> fw_upd m 0 j j j j"
        by (auto intro: order.trans[OF fwi_invariant fwi_fw_upd_mono])
      ultimately have "fw m n 0 j j < 0"
        unfolding fw_upd_def upd_def by auto
      then have "fw m n 0 j j < 0" by (metis cyc(1) less_or_eq_imp_le single_iteration_inv)
      with \<open>j \<le> n\<close> have "fw m n n j j < 0" using fw_invariant[of 0 n j n j m] by auto
      with \<open>j \<le> n\<close> show ?thesis by blast
    qed
  }
  ultimately show ?thesis by auto
qed

end (* End of local class context *)

section \<open>More on Canonical Matrices\<close>

abbreviation
  "canonical M n \<equiv> \<forall> i j k. i \<le> n \<and> j \<le> n \<and> k \<le> n \<longrightarrow> M i k \<le> M i j + M j k"

lemma canonical_alt_def:
  "canonical M n \<longleftrightarrow> canonical_subs n {0..n} M"
  unfolding canonical_subs_def by auto

lemma fw_canonical:
 "canonical (fw m n n) n" if "cyc_free m n"
 using fw_canonical_subs[OF \<open>cyc_free m n\<close>] unfolding canonical_alt_def by auto

lemma canonical_len:
  "canonical M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> M i j \<le> len M i j xs"
proof (induction xs arbitrary: i)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then have "M x j \<le> len M x j xs" by auto
  from Cons.prems \<open>canonical M n\<close> have "M i j \<le> M i x + M x j" by simp
  also with Cons have "\<dots> \<le> M i x + len M x j xs" by (simp add: add_mono)
  finally show ?case by simp
qed


section \<open>Additional Theorems\<close>

lemma D_cycle_free_len_dest:
  "cycle_free m n
    \<Longrightarrow> \<forall> i \<le> n. \<forall> j \<le> n. D m i j n = m' i j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n}
    \<Longrightarrow> \<exists> ys. set ys \<subseteq> {0..n} \<and> len m' i j xs = len m i j ys"
proof (induction xs arbitrary: i)
  case Nil
  with Nil have "m' i j = D m i j n" by simp
  from D_dest''[OF this]
  obtain ys where "set ys \<subseteq> {0..n}" "len m' i j [] = len m i j ys"
  by auto
  then show ?case by auto
next
  case (Cons y ys)
  from Cons.IH[OF Cons.prems(1,2) _ \<open>j \<le> n\<close>, of y] Cons.prems(5)
  obtain zs where zs:"set zs \<subseteq> {0..n}" "len m' y j ys = len m y j zs" by auto
  with Cons have "m' i y = D m i y n" by simp
  from D_dest''[OF this] obtain ws where ws:"set ws \<subseteq> {0..n}" "m' i y = len m i y ws" by auto
  with len_comp[of m i j ws y zs] zs Cons.prems(5)
  have "len m' i j (y # ys) = len m i j (ws @ y # zs)" "set (ws @ y # zs) \<subseteq> {0..n}" by auto
  then show ?case by blast
qed

lemma D_cyc_free_preservation:
  "cyc_free m n \<Longrightarrow> \<forall> i \<le> n. \<forall> j \<le> n. D m i j n = m' i j \<Longrightarrow> cyc_free m' n"
proof (auto, goal_cases)
  case (1 i xs)
  from D_cycle_free_len_dest[OF _ 1(2,3,3,4)] 1(1) cycle_free_diag_equiv
  obtain ys where "set ys \<subseteq> {0..n} \<and> len m' i i xs = len m i i ys" by fast
  with 1(1,3) show ?case by auto
qed

abbreviation "FW m n \<equiv> fw m n n"

lemma FW_out_of_bounds1:
  assumes "i > n"
  shows "(FW M n) i j = M i j"
  using assms by (rule fw_out_of_bounds1)

lemma FW_out_of_bounds2:
  assumes "j > n"
  shows "(FW M n) i j = M i j"
  using assms by (rule fw_out_of_bounds2)

lemma FW_cyc_free_preservation:
  "cyc_free m n \<Longrightarrow> cyc_free (FW m n) n"
  apply (rule D_cyc_free_preservation)
   apply assumption
  apply safe
  apply (rule fw_shortest_path)
  using cycle_free_diag_equiv by auto

lemma cyc_free_diag_dest':
  "cyc_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> m i i \<ge> 0"
  by (rule cyc_free_subs_diag)

lemma FW_diag_neutral_preservation:
  "\<forall> i \<le> n. M i i = 0 \<Longrightarrow> cyc_free M n \<Longrightarrow> \<forall> i\<le>n. (FW M n) i i = 0"
proof (auto, goal_cases)
  case (1 i)
  from this(3) have "(FW M n) i i \<le> M i i" by (auto intro: fw_mono)
  with 1 have "(FW M n) i i \<le> 0" by auto
  with cyc_free_diag_dest'[OF FW_cyc_free_preservation[OF 1(2)] \<open>i \<le> n\<close>] show "FW M n i i = 0"
    by auto
qed

lemma FW_fixed_preservation:
  fixes M :: "('a::linordered_ab_monoid_add) mat"
  assumes A: "i \<le> n" "M 0 i + M i 0 = 0" "canonical (FW M n) n" "cyc_free (FW M n) n"
  shows "FW M n 0 i + FW M n i 0 = 0" using assms
proof -
  let ?M' = "FW M n"
  assume A: "i \<le> n" "M 0 i + M i 0 = 0" "canonical ?M' n" "cyc_free ?M' n"
  from \<open>i \<le> n\<close> have "?M' 0 i + ?M' i 0 \<le> M 0 i + M i 0" by (auto intro: fw_mono add_mono)
  with A(2) have "?M' 0 i + ?M' i 0 \<le> 0" by auto
  moreover from \<open>canonical ?M' n\<close> \<open>i \<le> n\<close>
  have "?M' 0 0 \<le> ?M' 0 i + ?M' i 0" by auto
  moreover from cyc_free_diag_dest'[OF  \<open>cyc_free ?M' n\<close>] have "0 \<le> ?M' 0 0" by simp
  ultimately show "?M' 0 i + ?M' i 0 = 0" by (auto simp: add_mono)
qed

lemma diag_cyc_free_neutral:
  "cyc_free M n \<Longrightarrow> \<forall>k\<le>n. M k k \<le> 0 \<Longrightarrow> \<forall>i\<le>n. M i i = 0"
proof (clarify, goal_cases)
  case (1 i)
  note A = this
  then have "i \<le> n \<and> set [] \<subseteq> {0..n}" by auto
  with A(1) have "0 \<le> M i i" by fastforce
  with A(2) \<open>i \<le> n\<close> show "M i i = 0" by auto
qed

lemma fw_upd_canonical_subs_id:
  "canonical_subs n {k} M \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw_upd M k i j = M"
proof (auto simp: fw_upd_def upd_def less_eq[symmetric] min.coboundedI2, goal_cases)
  case 1
  then have "M i j \<le> M i k + M k j" unfolding canonical_subs_def by auto
  then have "min (M i j) (M i k + M k j) = M i j" by (simp split: split_min)
  thus ?case by force
qed

lemma fw_upd_canonical_id:
  "canonical M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw_upd M k i j = M"
  using fw_upd_canonical_subs_id[of n k M i j] unfolding canonical_subs_def by auto

lemma fwi_canonical_id:
  "fwi M n k i j = M" if "canonical_subs n {k} M" "i \<le> n" "j \<le> n" "k \<le> n"
  using that
proof (induction i arbitrary: j)
  case 0
  then show ?case by (induction j) (auto intro: fw_upd_canonical_subs_id)
next
  case Suc
  then show ?case by (induction j) (auto intro: fw_upd_canonical_subs_id)
qed

lemma fw_canonical_id:
  "fw M n k = M" if "canonical_subs n {0..k} M" "k \<le> n"
  using that by (induction k) (auto simp: canonical_subs_def fwi_canonical_id)

lemmas FW_canonical_id = fw_canonical_id[OF _ order.refl, unfolded canonical_alt_def[symmetric]]

definition "FWI M n k \<equiv> fwi M n k n n"

text \<open>The characteristic property of \<open>fwi\<close>.\<close>
theorem fwi_characteristic:
  "canonical_subs n (I \<union> {k::nat}) (FWI M n k) \<or> (\<exists> i \<le> n. FWI M n k i i < 0)" if
  "canonical_subs n I M" "I \<subseteq> {0..n}" "k \<le> n"
proof (cases "0 \<le> M k k")
  case True
  from fwi_canonical_extend[OF that(1,2) this \<open>k \<le> n\<close>] show ?thesis unfolding FWI_def ..
next
  case False
  with \<open>k \<le> n\<close> fwi_mono[OF \<open>k \<le> n\<close> \<open>k \<le> n\<close>, of M k n n] show ?thesis
    unfolding FWI_def by fastforce
qed

end (* End of theory *)
