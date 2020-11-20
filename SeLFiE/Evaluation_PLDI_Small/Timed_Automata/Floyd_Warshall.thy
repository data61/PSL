theory Floyd_Warshall
  imports Main
begin

chapter \<open>Floyd-Warshall Algorithm for the All-Pairs Shortest Paths Problem\<close>

subsubsection \<open>Auxiliary\<close>

lemma distinct_list_single_elem_decomp: "{xs. set xs \<subseteq> {0} \<and> distinct xs} = {[], [0]}"
proof (standard, goal_cases)
  case 1
  { fix xs :: "'a list" assume xs: "xs \<in> {xs. set xs \<subseteq> {0} \<and> distinct xs}"
    have "xs \<in> {[], [0]}"
    proof (cases xs)
      case (Cons y ys)
      hence y: "y = 0" using xs by auto
      with Cons xs have "ys = []" by (cases ys, auto)
      thus ?thesis using y Cons by simp
    qed simp
  }
  thus ?case by blast
qed simp


section \<open>Cycles in Lists\<close>

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
  "x \<in> set xs \<Longrightarrow> \<exists> xxs as. as @ concat (map (\<lambda> xs. x # xs) xxs) @ remove_cycles xs x ys = xs \<and> x \<notin> set as"
proof (induction xs arbitrary: ys)
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
  hence "\<forall> x \<in> set ys. cnt x (remove_all_cycles xs ys) \<le> 1" using cnt_remove_all_cycles by fastforce
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

definition "remove_all x xs = (if x \<in> set xs then tl (remove_cycles xs x []) else xs)"

definition "remove_all_rev x xs = (if x \<in> set xs then rev (tl (remove_cycles (rev xs) x [])) else xs)"

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
  thus ?thesis using 1(1) distinct_remove_cycles_inv[of "rev xs" "[]" x] by (simp add: remove_all_rev_def)
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

text \<open>
  We formalize the Floyd-Warshall algorithm on a linearly ordered abelian semigroup.
  However, we would not need an \<open>abelian\<close> monoid if we had the right type class.
\<close>

class linordered_ab_monoid_add = linordered_ab_semigroup_add +
  fixes neutral :: 'a ("\<one>")
    assumes neutl[simp]: "\<one> + x = x"
    assumes neutr[simp]: "x + \<one> = x"
begin

lemmas assoc = add.assoc

type_synonym 'c mat = "nat \<Rightarrow> nat \<Rightarrow> 'c"

definition (in -) upd :: "'c mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'c mat"
where
  "upd m x y v = m (x := (m x) (y := v))"

definition fw_upd :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw_upd m k i j \<equiv> upd m i j (min (m i j) (m i k + m k j))"

lemma fw_upd_mono:
  "fw_upd m k i j i' j' \<le> m i' j'" 
by (cases "i = i'", cases "j = j'") (auto simp: fw_upd_def upd_def)

fun fw :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw m n 0       0       0        = fw_upd m 0 0 0" |
  "fw m n (Suc k) 0       0        = fw_upd (fw m n k n n) (Suc k) 0 0" |
  "fw m n k       (Suc i) 0        = fw_upd (fw m n k i n) k (Suc i) 0" |
  "fw m n k       i       (Suc j)  = fw_upd (fw m n k i j) k i (Suc j)"

lemma fw_invariant_aux_1:
  "j'' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw m n k i j i' j' \<le> fw m n k i j'' i' j'"
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j) thus ?case
  proof (cases "j'' = Suc j")
    case True thus ?thesis by simp
  next
    case False
    have "fw_upd (fw m n k i j) k i (Suc j) i' j' \<le> fw m n k i j i' j'" by (simp add: fw_upd_mono)
    thus ?thesis using Suc False by simp
  qed
qed

lemma fw_invariant_aux_2:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> i'' \<le> i \<Longrightarrow> j'' \<le> j
   \<Longrightarrow> fw m n k i j i' j' \<le> fw m n k i'' j'' i' j'"
proof (induction i)
  case 0 thus ?case using fw_invariant_aux_1 by auto
next
  case (Suc i) thus ?case
  proof (cases "i'' = Suc i")
    case True thus ?thesis using Suc fw_invariant_aux_1 by simp
  next
    case False
    have "fw m n k (Suc i) j i' j' \<le> fw m n k (Suc i) 0 i' j'"
    using fw_invariant_aux_1[of 0 j "Suc i" n k] Suc(2-) by simp
    also have "\<dots> \<le> fw m n k i n i' j'" by (simp add: fw_upd_mono)
    also have "\<dots> \<le> fw m n k i j i' j'" using fw_invariant_aux_1[of j n i n k] False Suc by simp
    also have "\<dots> \<le> fw m n k i'' j'' i' j'" using Suc False by simp
    finally show ?thesis by simp
  qed
qed

lemma fw_invariant:
  "k' \<le> k \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> j'' \<le> j \<Longrightarrow> i'' \<le> i
   \<Longrightarrow> fw m n k i j i' j' \<le> fw m n k' i'' j'' i' j'"
proof (induction k)
  case 0 thus ?case using fw_invariant_aux_2 by auto
next
  case (Suc k) thus ?case
  proof (cases "k' = Suc k")
    case True thus ?thesis using Suc fw_invariant_aux_2 by simp
  next
    case False
    have "fw m n (Suc k) i j i' j' \<le> fw m n (Suc k) 0 0 i' j'"
    using fw_invariant_aux_2[of i n j "Suc k" 0 0] Suc(2-) by simp
    also have "\<dots> \<le> fw m n k n n i' j'" by (simp add: fw_upd_mono)
    also have "\<dots> \<le> fw m n k i j i' j'" using fw_invariant_aux_2[of n n n k] False Suc by simp
    also have "\<dots> \<le> fw m n k' i'' j'' i' j'" using Suc False by simp
    finally show ?thesis by simp
  qed
qed

lemma single_row_inv:
  "j' < j \<Longrightarrow> j \<le> n \<Longrightarrow> i' \<le> n \<Longrightarrow> fw m n k i' j i' j' = fw m n k i' j' i' j'"
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j) thus ?case by (cases "j' = j") (simp add: fw_upd_def upd_def)+
qed

lemma single_iteration_inv':
  "i' < i \<Longrightarrow> j' \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i \<le> n \<Longrightarrow> fw m n k i j i' j' = fw m n k i' j' i' j'"
proof (induction i arbitrary: j)
  case 0 thus ?case by simp
next
  case (Suc i) thus ?case
  proof (induction j)
    case 0 thus ?case
    proof (cases "i = i'", goal_cases)
      case 2 thus ?case by (simp add: fw_upd_def upd_def)
    next
      case 1 thus ?case using single_row_inv[of j' n n i' m k] 
      by (cases "j' = n") (fastforce simp add: fw_upd_def upd_def)+
    qed
  next
    case (Suc j) thus ?case by (simp add: fw_upd_def upd_def)
  qed
qed

lemma single_iteration_inv:
  "i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n\<Longrightarrow> fw m n k i j i' j' = fw m n k i' j' i' j'"
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
        case 1 thus ?case using single_iteration_inv'[of i' "Suc i" j' n "Suc j" m k] by simp
      next
        case 2 thus ?case by (simp add: fw_upd_def upd_def)
      qed
    qed
  qed
qed

lemma fw_innermost_id:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> i' < i \<Longrightarrow> fw m n 0 i' j' i j = m i j"
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

lemma fw_middle_id:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> fw m n 0 i' j' i j = m i j"
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
    case 0 thus ?case using fw_innermost_id by (auto simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp add: fw_upd_def upd_def)
  qed
qed

lemma fw_outermost_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n 0 i j i j \<le> m i j"
proof (cases j)
  case 0
  assume "i \<le> n"
  thus ?thesis
  proof (cases i)
    case 0 thus ?thesis using \<open>j = 0\<close> by (simp add: fw_upd_def upd_def)
  next
    case (Suc i')
    hence "fw m n 0 i' n (Suc i') 0 = m (Suc i') 0" using fw_innermost_id[of "Suc i'" n 0 n i' m]
    using \<open>i \<le> n\<close> by simp
    thus ?thesis using \<open>j = 0\<close> Suc by (simp add: fw_upd_def upd_def)
  qed
next
  case (Suc j')
  assume "i \<le> n" "j \<le> n"
  hence "fw m n 0 i j' i (Suc j') = m i (Suc j')"
  using fw_middle_id[of i n "Suc j'" j' i m] Suc by simp
  thus ?thesis using Suc by (simp add: fw_upd_def upd_def)
qed

lemma Suc_innermost_id1:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> i' < i \<Longrightarrow> fw m n (Suc k) i' j' i j = fw m n k i j i j"
proof (induction i' arbitrary: j')
  case 0 thus ?case
  proof (induction j')
    case 0
    hence "fw m n k n n i j = fw m n k i j i j" using single_iteration_inv[of i n j n n m k] by simp
    thus ?case using 0 by (simp add: fw_upd_def upd_def)
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

lemma Suc_innermost_id2:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> fw m n (Suc k) i' j' i j = fw m n k i j i j"
proof (induction i' arbitrary: j')
  case 0
  hence "fw m n k n n i j = fw m n k i j i j" using single_iteration_inv[of i n j n n m k] by simp
  with 0 show ?case
  proof (induction j')
    case 0
    thus ?case by (auto simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp: fw_upd_def upd_def)
  qed
next
  case (Suc i') thus ?case
  proof (induction j')
    case 0 thus ?case using Suc_innermost_id1 by (auto simp add: fw_upd_def upd_def)
  next
    case (Suc j') thus ?case by (auto simp add: fw_upd_def upd_def)
  qed
qed

lemma Suc_innermost_id1':
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> i' < i \<Longrightarrow> fw m n (Suc k) i' j' i j = fw m n k n n i j"
proof goal_cases
  case 1
  hence "fw m n (Suc k) i' j' i j = fw m n k i j i j" using Suc_innermost_id1 by simp
  thus ?thesis using 1 single_iteration_inv[of i n] by simp
qed

lemma Suc_innermost_id2':
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> fw m n (Suc k) i' j' i j = fw m n k n n i j"
proof goal_cases
  case 1
  hence "fw m n (Suc k) i' j' i j = fw m n k i j i j" using Suc_innermost_id2 by simp
  thus ?thesis using 1 single_iteration_inv[of i n] by simp
qed

lemma Suc_innermost_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n (Suc k) i j i j \<le> fw m n k i j i j"
proof (cases j)
  case 0
  assume "i \<le> n"
  thus ?thesis
  proof (cases i)
    case 0 thus ?thesis using \<open>j = 0\<close> single_iteration_inv[of 0 n 0 n n m k]
    by (simp add: fw_upd_def upd_def)
  next
    case (Suc i')
    thus ?thesis using Suc_innermost_id1 \<open>i \<le> n\<close> \<open>j = 0\<close>
    by (auto simp: fw_upd_def upd_def local.min.coboundedI1)
  qed
next
  case (Suc j')
  assume "i \<le> n" "j \<le> n"
  thus ?thesis using Suc Suc_innermost_id2 by (auto simp: fw_upd_def upd_def local.min.coboundedI1)
qed

lemma fw_mono':
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n k i j i j \<le> m i j"
proof (induction k)
  case 0 thus ?case using fw_outermost_mono by simp
next
  case (Suc k) thus ?case using Suc_innermost_mono[OF Suc.prems, of m k] by simp
qed

lemma fw_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> fw m n k i j i' j' \<le> m i' j'"
proof (cases k)
  case 0
  assume 0: "i \<le> n" "j \<le> n" "i' \<le> n" "j' \<le> n" "k = 0"
  thus ?thesis
  proof (cases "i' \<le> i")
    case False thus ?thesis using 0 fw_innermost_id by simp
  next
    case True thus ?thesis
    proof (cases "j' \<le> j")
      case True
      have "fw m n 0 i j i' j' \<le> fw m n 0 i' j' i' j'" using fw_invariant True \<open>i' \<le> i\<close> 0 by simp
      also have "fw m n 0 i' j' i' j' \<le> m i' j'" using 0 fw_outermost_mono by blast
      finally show ?thesis by (simp add: \<open>k = 0\<close>)
    next
      case False thus ?thesis
      proof (cases "i = i'", goal_cases)
        case 1 then show ?thesis using fw_middle_id[of i' n j' j i' m] 0 by simp
      next
        case 2
        then show ?case
        using single_iteration_inv'[of i' i j' n j m 0] \<open>i' \<le> i\<close> fw_middle_id[of i' n j' j i' m]
              fw_outermost_mono[of i' n j' m] 0
        by simp
      qed
    qed
  qed
next
  case (Suc k)
  assume prems: "i \<le> n" "j \<le> n" "i' \<le> n" "j' \<le> n"
  thus ?thesis
  proof (cases "i' \<le> i \<and> j' \<le> j")
    case True
    hence "fw m n (Suc k) i j i' j' = fw m n (Suc k) i' j' i' j'"
    using prems single_iteration_inv by blast
    thus ?thesis using Suc prems fw_mono' by auto
  next
    case False thus ?thesis
    proof auto
      assume "\<not> i' \<le> i"
      thus ?thesis using Suc prems fw_mono' Suc_innermost_id1 by auto
    next
      assume "\<not> j' \<le> j"
      hence "j < j'" by simp
      show ?thesis
      proof (cases "i \<le> i'")
        case True
        thus ?thesis using Suc prems Suc_innermost_id2 \<open>j < j'\<close> fw_mono' by auto
      next
        case False
        thus ?thesis using single_iteration_inv' Suc prems fw_mono' by auto
      qed
    qed
  qed
qed

lemma add_mono_neutr:
  assumes "\<one> \<le> b"
  shows "a \<le> a + b"
using neutr add_mono assms by force

lemma add_mono_neutl:
  assumes "\<one> \<le> b"
  shows "a \<le> b + a"
using neutr add_mono assms by force

lemma fw_step_0:
  "m 0 0 \<ge> \<one> \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> fw m n 0 i j i j = min (m i j) (m i 0 + m 0 j)"
proof (induction i)
  case 0 thus ?case
  proof (cases j)
    case 0 thus ?thesis by (simp add: fw_upd_def upd_def)
  next
    case (Suc j)
    hence "fw m n 0 0 j 0 (Suc j) = m 0 (Suc j)" using 0 fw_middle_id[of 0 n "Suc j" j 0 m] by fast
    moreover have "fw m n 0 0 j 0 0 = m 0 0" using single_iteration_inv[of 0 0 0 j n m 0] Suc 0
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutl)
    ultimately show ?thesis using Suc by (simp add: fw_upd_def upd_def)
  qed
next
  case (Suc i)
  note A = this
  show ?case
  proof (cases j)
    case 0
    have "fw m n 0 i n (Suc i) 0 = m (Suc i) 0" using fw_innermost_id[of "Suc i" n 0 n i m] Suc by simp
    moreover have "fw m n 0 i n 0 0 = m 0 0" using Suc single_iteration_inv[of 0 i 0 n n m 0]
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutl)
    ultimately show ?thesis using 0 by (simp add: fw_upd_def upd_def)
  next
    case (Suc j)
    have *: "fw m n 0 0 j 0 0 = m 0 0" using single_iteration_inv[ of 0 0 0 j n m 0] A Suc
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutl)
    have **: "fw m n 0 i n 0 0 = m 0 0" using single_iteration_inv[of 0 i 0 n n m 0] A
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutl)
    have "m 0 (Suc j) = fw_upd m 0 0 (Suc j) 0 (Suc j)" using \<open>m 0 0 >= \<one>\<close>
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutl)
    also have "\<dots> = fw m n 0 0 (Suc j) 0 (Suc j)" using fw_middle_id[of 0 n "Suc j" j 0 m] Suc A(4)
    by (simp add: fw_upd_def upd_def *)
    finally have ***: "fw m n 0 (Suc i) j 0 (Suc j) = m 0 (Suc j)"
    using single_iteration_inv'[of 0 "Suc i" "Suc j" n j m 0] A Suc by simp
    have "m (Suc i) 0 = fw_upd m 0 (Suc i) 0 (Suc i) 0" using \<open>m 0 0 >= \<one>\<close>
    by (auto simp add: fw_upd_def upd_def min_def intro: add_mono_neutr)
    also have "\<dots> = fw m n 0 (Suc i) 0 (Suc i) 0"
    using fw_innermost_id[of "Suc i" n 0 n i m] \<open>Suc i \<le> n\<close> ** by (simp add: fw_upd_def upd_def)
    finally have "fw m n 0 (Suc i) j (Suc i) 0 = m (Suc i) 0"
    using single_iteration_inv A Suc by auto
    moreover have "fw m n 0 (Suc i) j (Suc i) (Suc j) = m (Suc i) (Suc j)"
    using fw_middle_id A Suc by simp
    ultimately show ?thesis using Suc *** by (simp add: fw_upd_def upd_def)
  qed
qed

lemma fw_step_Suc:
  "\<forall> k'\<le>n. fw m n k n n k' k' \<ge> \<one> \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> Suc k \<le> n
    \<Longrightarrow> fw m n (Suc k) i j i j = min (fw m n k n n i j) (fw m n k n n i (Suc k) + fw m n k n n (Suc k) j)"
proof (induction i)
  case 0 thus ?case
  proof (cases j)
    case 0 thus ?thesis by (simp add: fw_upd_def upd_def)
  next
    case (Suc j)
    then have
      "fw m n k n n 0 (Suc j) = fw m n (Suc k) 0 j 0 (Suc j)"
    using 0(2-) Suc_innermost_id2' by simp
    moreover have "fw m n (Suc k) 0 j 0 (Suc k) = fw m n k n n 0 (Suc k)"
    proof (cases "j < Suc k")
      case True thus ?thesis using 0 Suc_innermost_id2' by simp
    next
      case False
      hence
        "fw m n (Suc k) 0 k 0 (Suc k) = fw m n k n n 0 (Suc k)"
      using 0(2-) Suc Suc_innermost_id2' by simp
      moreover have "fw m n (Suc k) 0 k (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
      using 0(2-) Suc Suc_innermost_id2' by simp
      moreover have "fw m n (Suc k) 0 j 0 (Suc k) = fw m n (Suc k) 0 (Suc k) 0 (Suc k)"
      using False single_iteration_inv 0(2-) Suc by force
      ultimately show ?thesis using 0(1)
      by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutr)
    qed
    moreover have "fw m n k n n (Suc k) (Suc j) = fw m n (Suc k) 0 j (Suc k) (Suc j)"
    using 0(2-) Suc Suc_innermost_id2' by simp
    ultimately show ?thesis using Suc by (simp add: fw_upd_def upd_def)
  qed
next
  case (Suc i)
  note A = this
  show ?case
  proof (cases j)
    case 0
    hence
      "fw m n (Suc k) i n (Suc i) 0 = fw m n k n n (Suc i) 0"
    using Suc_innermost_id1' \<open>Suc i \<le> n\<close> by simp
    moreover have "fw m n (Suc k) i n (Suc i) (Suc k) = fw m n k n n (Suc i) (Suc k)"
    using Suc_innermost_id1' A(3,5) by simp
    moreover have "fw m n (Suc k) i n (Suc k) 0 = fw m n k n n (Suc k) 0"
    proof (cases "i < Suc k")
      case True thus ?thesis using Suc_innermost_id1' A(3,5) by simp
    next
      case False
      have "fw m n (Suc k) k n (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
      using Suc_innermost_id1' \<open>Suc i \<le> n\<close> False by simp
      moreover have "fw m n (Suc k) k n (Suc k) 0 = fw m n k n n (Suc k) 0"
      using Suc_innermost_id1' \<open>Suc i \<le> n\<close> False by simp
      moreover have "fw m n (Suc k) i n (Suc k) 0 = fw m n (Suc k) (Suc k) 0 (Suc k) 0"
      using single_iteration_inv \<open>Suc i \<le> n\<close> False by simp
      ultimately show ?thesis using Suc(2)
      by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutl)
    qed
    ultimately show ?thesis using 0 by (simp add: fw_upd_def upd_def)
  next
    case (Suc j)
    hence "fw m n (Suc k) (Suc i) j (Suc i) (Suc j) = fw m n k n n (Suc i) (Suc j)"
    using Suc_innermost_id2' A(3,4) by simp
    moreover have "fw m n (Suc k) (Suc i) j (Suc i) (Suc k) = fw m n k n n (Suc i) (Suc k)"
    proof (cases "j < Suc k")
      case True thus ?thesis using Suc A(3-) Suc_innermost_id2' by simp
    next
      case False
      have *:"fw m n (Suc k) (Suc i) k (Suc i) (Suc k) = fw m n k n n (Suc i) (Suc k)"
      using Suc_innermost_id2' A(3,5) by simp
      have **:"fw m n (Suc k) (Suc i) k (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
      proof (cases "Suc i \<le> Suc k")
        case True thus ?thesis using Suc_innermost_id2' A(5) by simp
      next
        case False
        hence "fw m n (Suc k) (Suc i) k (Suc k) (Suc k) = fw m n (Suc k) (Suc k) (Suc k) (Suc k) (Suc k)"
        using single_iteration_inv'[of "Suc k" "Suc i" "Suc k" n k m "Suc k"] A(3) by simp
        moreover have "fw m n (Suc k) (Suc k) k (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
        using Suc_innermost_id2' A(5) by simp
        ultimately show ?thesis using A(2)
        by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutl)
      qed
      have "fw m n (Suc k) (Suc i) j (Suc i) (Suc k) = fw m n (Suc k) (Suc i) (Suc k) (Suc i) (Suc k)"
      using False single_iteration_inv[of "Suc i" "Suc i" "Suc k" j n m "Suc k"] A(3-) Suc by simp
      also have "\<dots> = fw m n k n n (Suc i) (Suc k)" using * ** A(2)
      by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutr)
      finally show ?thesis by simp
    qed
    moreover have "fw m n (Suc k) (Suc i) j (Suc k) (Suc j) = fw m n k n n (Suc k) (Suc j)"
    proof (cases "Suc i \<le> Suc k")
      case True thus ?thesis using Suc_innermost_id2' Suc A(3-5) by simp
    next
      case False
      have "fw m n (Suc k) (Suc k) j (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
      proof (cases "j < Suc k")
        case True thus ?thesis using Suc_innermost_id2' A(5) by simp
      next
        case False
        hence "fw m n (Suc k) (Suc k) j (Suc k) (Suc k) = fw m n (Suc k) (Suc k) (Suc k) (Suc k) (Suc k)"
        using single_iteration_inv A(3,4) Suc by simp
        moreover have "fw m n (Suc k) (Suc k) k (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
        using Suc_innermost_id2' A(5) by simp
        ultimately show ?thesis using A(2)
        by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutl)
      qed
      moreover have "fw m n (Suc k) (Suc k) j (Suc k) (Suc j) = fw m n k n n (Suc k) (Suc j)"
      using Suc_innermost_id2' Suc A(3-5) by simp
      ultimately have "fw m n (Suc k) (Suc k) (Suc j) (Suc k) (Suc j) = fw m n k n n (Suc k) (Suc j)"
      using A(2) by (auto simp add: fw_upd_def upd_def \<open>Suc k \<le> n\<close> min_def intro: add_mono_neutl)
      moreover have "fw m n (Suc k) (Suc i) j (Suc k) (Suc j) = fw m n (Suc k) (Suc k) (Suc j) (Suc k) (Suc j)"
      using single_iteration_inv'[of "Suc k" "Suc i" "Suc j" n j m "Suc k"] Suc A(3-) False  by simp
      moreover have "fw m n (Suc k) (Suc k) k (Suc k) (Suc k) = fw m n k n n (Suc k) (Suc k)"
      using Suc_innermost_id2' A(5) by simp
      ultimately show ?thesis using A(2) by (simp add: fw_upd_def upd_def)
    qed
    ultimately show ?thesis using Suc by (simp add: fw_upd_def upd_def)
  qed
qed


subsection \<open>Length of Paths\<close>

fun len :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a" where
  "len m u v [] = m u v" |
  "len m u v (w#ws) = m u w + len m w v ws"

lemma len_decomp: "xs = ys @ y # zs \<Longrightarrow> len m x z xs = len m x y ys + len m y z zs"
by (induction ys arbitrary: x xs) (simp add: assoc)+

lemma len_comp: "len m a c (xs @ b # ys) = len m a b xs + len m b c ys"
by (induction xs arbitrary: a) (auto simp: assoc)


subsection \<open>Shortening Negative Cycles\<close>

lemma remove_cycles_neg_cycles_aux:
  fixes i xs ys
  defines "xs' \<equiv> i # ys"
  assumes "i \<notin> set ys"
  assumes "i \<in> set xs"
  assumes "xs = as @ concat (map ((#) i) xss) @ xs'"
  assumes "len m i j ys > len m i j xs"
  shows "\<exists> ys. set ys \<subseteq> set xs \<and> len m i i ys < \<one>" using assms
proof (induction xss arbitrary: xs as)
  case Nil
  with Nil show ?case
  proof (cases "len m i i as \<ge> \<one>", goal_cases)
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
  proof (cases "len m i i as \<ge> \<one>", goal_cases)
    case 1
    from this(5,7) len_decomp add_mono
    have "len m i j ?xs \<le> len m i j xs" by fastforce
    hence 4:"len m i j ?xs < len m i j ys" using 1(6) by simp
    have 2:"i \<in> set ?xs" using Cons(2) by auto
    have "set ?xs \<subseteq> set xs" using Cons(5) by auto
    moreover from Cons(1)[OF 1(2,3) 2 _ 4] have "\<exists>ys. set ys \<subseteq> set ?xs \<and> len m i i ys < \<one>" by auto
    ultimately show ?case by blast
  next
    case 2
    from this(5,7) show ?case by auto
  qed
qed

lemma add_lt_neutral: "a + b < b \<Longrightarrow> a < \<one>"
proof (rule ccontr)
  assume "a + b < b" "\<not> a < \<one>"
  hence "a \<ge> \<one>" by auto
  from add_mono[OF this, of b b] \<open>a + b < b\<close> show False by auto
qed

lemma remove_cycles_neg_cycles_aux':
  fixes j xs ys
  assumes "j \<notin> set ys"
  assumes "j \<in> set xs"
  assumes "xs = ys @ j # concat (map (\<lambda> xs. xs @ [j]) xss) @ as"
  assumes "len m i j ys > len m i j xs"
  shows "\<exists> ys. set ys \<subseteq> set xs \<and> len m j j ys < \<one>" using assms
proof (induction xss arbitrary: xs as)
  case Nil
  show ?case
  proof (cases "len m j j as \<ge> \<one>")
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
    moreover from Cons(1)[OF Cons(2) 2 _ 4] have "\<exists>ys. set ys \<subseteq> set ?xs \<and> len m j j ys < \<one>" by blast
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
    hence "len m j j zs < \<one>" using add_lt_neutral by auto
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
  "len m i j (start_remove xs k []) > len m i j xs \<Longrightarrow> \<exists> ys. set ys \<subseteq> set xs \<and> len m k k ys < \<one>"
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
  \<Longrightarrow> \<exists> ys k. set ys \<subseteq> set xs \<and> k \<in> set xs \<and> len m k k ys < \<one>"
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

lemma (in -) concat_map_cons_rev:
  "rev (concat (map ((#) j) xss)) = concat (map (\<lambda> xs. xs @ [j]) (rev (map rev xss)))"
by (induction xss) auto

lemma negative_cycle_dest: "len m i j (rem_cycles i j xs) > len m i j xs
       \<Longrightarrow> \<exists> i' ys. len m i' i' ys < \<one> \<and> set ys \<subseteq> set xs \<and> i' \<in> set (i # j # xs)"
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

section \<open>Definition of Shortest Paths\<close>

definition D :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "D m i j k \<equiv> Min {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"

lemma (in -) distinct_length_le:"finite s \<Longrightarrow> set xs \<subseteq> s \<Longrightarrow> distinct xs \<Longrightarrow> length xs \<le> card s"
by (metis card_mono distinct_card) 

lemma (in -) finite_distinct: "finite s \<Longrightarrow> finite {xs . set xs \<subseteq> s \<and> distinct xs}"
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
  (\<forall> j. j \<le> n \<longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs) \<and> len m i i xs \<ge> \<one>"

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

lemma cycle_free_loop_dest: "i \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> cycle_free m n \<Longrightarrow> len m i i xs \<ge> \<one>"
unfolding cycle_free_def by auto

lemma cycle_free_dest:
  "cycle_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n}
    \<Longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs"
by (auto simp add: cycle_free_def)

definition cycle_free_up_to :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cycle_free_up_to m k n \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> {0..k} \<longrightarrow>
  (\<forall> j. j \<le> n \<longrightarrow> len m i j (rem_cycles i j xs) \<le> len m i j xs) \<and> len m i i xs \<ge> \<one>"

lemma cycle_free_up_to_loop_dest:
  "i \<le> n \<Longrightarrow> set xs \<subseteq> {0..k} \<Longrightarrow> cycle_free_up_to m k n \<Longrightarrow> len m i i xs \<ge> \<one>"
unfolding cycle_free_up_to_def by auto

lemma cycle_free_up_to_diag:
  assumes "cycle_free_up_to m k n" "i \<le> n"
  shows "m i i \<ge> \<one>"
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


section \<open>Result Under The Absence of Negative Cycles\<close>

text \<open>
  This proves that the algorithm correctly computes shortest paths under the absence of negative
  cycles by a standard argument.
\<close>

theorem fw_shortest_path_up_to:
  "cycle_free_up_to m k n \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n
        \<Longrightarrow> D m i' j' k = fw m n k i j i' j'"
proof (induction k arbitrary: i j i' j')
  case 0
  from cycle_free_up_to_diag[OF 0(1)] have diag: "\<forall> k \<le> n. m k k \<ge> \<one>" by auto
  then have m_diag: "m 0 0 \<ge> \<one>" by simp
  let ?S = "{len m i' j' xs |xs. set xs \<subseteq> {0} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
  show ?case unfolding D_def
  proof (simp, rule Min_eqI)
    have "?S \<subseteq> {len m i' j' xs |xs. set xs \<subseteq> {0..0} \<and> distinct xs}" by auto
    thus "finite ?S" using D_base_finite[of m i' j' 0] by (rule finite_subset)
  next
    fix l assume "l \<in> ?S"
    then obtain xs where l: "l = len m i' j' xs" and xs: "xs = [] \<or> xs = [0]"
    using distinct_list_single_elem_decomp by auto
    { assume "xs = []"
      have "fw m n 0 i j i' j' \<le> fw m n 0 0 0 i' j'" using fw_invariant 0 by blast
      also have "\<dots> \<le> m i' j'" by (cases "i' = 0 \<and> j' = 0") (simp add: fw_upd_def upd_def)+
      finally have "fw m n 0 i j i' j' \<le> l" using \<open>xs = []\<close> l by simp
    }
    moreover
    { assume "xs = [0]"
      have "fw m n 0 i j i' j' \<le> fw m n 0 i' j' i' j'" using fw_invariant 0 by blast
      also have "\<dots> \<le> m i' 0 + m 0 j'"
      proof (cases j')
        assume "j' = 0"
        show ?thesis
        proof (cases i')
          assume "i' = 0"
          thus ?thesis using \<open>j' = 0\<close> by (simp add: fw_upd_def upd_def)
        next
          fix i'' assume i'': "i' = Suc i''"
          have "fw_upd (fw m n 0 i'' n) 0 (Suc i'') 0 (Suc i'') 0 \<le> fw m n 0 i'' n (Suc i'') 0"
          by (simp add: fw_upd_mono)
          also have "\<dots> \<le> m (Suc i'') 0" using fw_mono 0 i'' by simp
          finally show ?thesis using \<open>j' = 0\<close> m_diag i'' neutr add_mono by fastforce
        qed
      next
        fix j'' assume j'': "j' = Suc j''"
        have "fw_upd (fw m n 0 i' j'') 0 i' (Suc j'') i' (Suc j'')
              \<le> fw m n 0 i' j'' i' 0 + fw m n 0 i' j'' 0 (Suc j'') "
        by (simp add: fw_upd_def upd_def)
        also have "\<dots> \<le> m i' 0 + m 0 (Suc j'')"
        using fw_mono[of i' n j'' i' 0 m 0] fw_mono[of i' n j'' 0 "Suc j''" m 0 ] j'' 0
        by (simp add: add_mono)
        finally show ?thesis using j'' by simp
      qed
      finally have "fw m n 0 i j i' j' \<le> l" using \<open>xs = [0]\<close> l by simp
    }
    ultimately show "fw m n 0 i j i' j' \<le> l" using xs by auto
  next
    have A: "fw m n 0 i j i' j' = fw m n 0 i' j' i' j'" using single_iteration_inv 0 by blast
    have "fw m n 0 i' j' i' j' = min (m i' j') (m i' 0 + m 0 j')"
    using 0 by (simp add: fw_step_0[of m, OF m_diag])
    hence
      "fw m n 0 i' j' i' j' = m i' j'
      \<or> (fw m n 0 i' j' i' j' = m i' 0 + m 0 j'\<and> m i' 0 + m 0 j' \<le> m i' j')"
    by (auto simp add: ord.min_def) 
    thus "fw m n 0 i j i' j' \<in> ?S"
    proof (standard, goal_cases)
      case 1
      hence "fw m n 0 i j i' j' = len m i' j' []" using A by auto
      thus ?case by fastforce
    next
      case 2
      hence *:"fw m n 0 i j i' j' = len m i' j' [0]" using A by auto
      thus ?case
      proof (cases "i' = 0 \<or> j' = 0")
        case False thus ?thesis using * by fastforce
      next
        case True
        { assume "i' = 0"
          from diag have "m 0 0 + m 0 j' \<ge> m 0 j'" by (auto intro: add_mono_neutl)
          with \<open>i' = 0\<close> have "fw m n 0 i j i' j' = len m 0 j' []" using 0 A 2 by auto
        } moreover
        { assume "j' = 0"
          from diag have "m i' 0 + m 0 0 \<ge> m i' 0" by (auto intro: add_mono_neutr)
          with \<open>j' = 0\<close> have "fw m n 0 i j i' j' = len m i' 0 []" using 0 A 2 by auto
        }
        ultimately have "fw m n 0 i j i' j' = len m i' j' []" using True by auto
        then show ?thesis by fastforce
      qed
    qed
  qed
next
  case (Suc k)
  from cycle_free_up_to_diag[OF Suc.prems(1)] have diag: "\<forall> k \<le> n. m k k \<ge> \<one>" by auto
  from Suc.prems have cycle_free_to_k:
    "cycle_free_up_to m k n" by (fastforce simp add: cycle_free_up_to_def)
  { fix k' assume "k' \<le> n"
    with Suc cycle_free_to_k have "D m k' k' k = fw m n k n n k' k'" by auto
    from D_dest''[OF this[symmetric]] obtain xs where
      "set xs \<subseteq> {0..k}" "fw m n k n n k' k'= len m k' k' xs"
    by auto
    with Suc(2) \<open>Suc k \<le> n\<close> \<open>k' \<le> n\<close> have "fw m n k n n k' k' \<ge> \<one>"
    unfolding cycle_free_up_to_def by force
  }
  hence K: "\<forall>k'\<le>n. fw m n k n n k' k' \<ge> \<one>" by simp
  let ?S = "\<lambda> k i j. {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  show ?case
  proof (rule D_eqI2)
    show "cycle_free_up_to m (Suc k) n" using Suc.prems(1) .
  next
    show "i' \<le> n" using Suc.prems by simp
  next
    show "j' \<le> n" using Suc.prems by simp
  next
    show "Suc k \<le> n" using Suc.prems by simp
  next
    fix l assume "l \<in> {len m i' j' xs | xs. set xs \<subseteq> {0..Suc k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
    then obtain xs where xs:
      "l = len m i' j' xs" "set xs \<subseteq> {0..Suc k}" "i' \<notin> set xs" "j' \<notin> set xs" "distinct xs"
    by auto
    have IH: "D m i' j' k = fw m n k i j i' j'" using cycle_free_to_k Suc by auto
    have fin:
      "finite {len m i' j' xs |xs. set xs \<subseteq> {0..k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
    using D_base_finite'' by simp
    show "fw m n (Suc k) i j i' j' \<le> l"
    proof (cases "Suc k \<in> set xs")
      case False
      hence "set xs \<subseteq> {0..k}" using xs(2) using atLeastAtMostSuc_conv by auto
      hence
        "l \<in> {len m i' j' xs | xs. set xs \<subseteq> {0..k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
      using xs by auto
      with Min_le[OF fin this] have "fw m n k i j i' j' \<le> l" using IH by (simp add: D_def)
      thus ?thesis using fw_invariant[of k "Suc k" i n j j i m i' j'] Suc.prems by simp
    next
      case True
      then obtain ys zs where ys_zs_id: "xs = ys @ Suc k # zs" by (meson split_list)
      with xs(5) have ys_zs: "distinct ys" "distinct zs" "Suc k \<notin> set ys" "Suc k \<notin> set zs"
      "set ys \<inter> set zs = {}" by auto
      have "i' \<noteq> Suc k" "j' \<noteq> Suc k" using xs(3,4) True by auto

      have "set ys \<subseteq> {0..k}" using ys_zs(3) xs(2) ys_zs_id using atLeastAtMostSuc_conv by auto
      hence "len m i' (Suc k) ys \<in> ?S k i' (Suc k)" using ys_zs_id ys_zs xs(3) by fastforce
      with Min_le[OF _ this] have "Min (?S k i' (Suc k)) \<le> len m i' (Suc k) ys"
      using D_base_finite'[of m i' "Suc k" k] \<open>i' \<noteq> Suc k\<close> by fastforce
      moreover have "fw m n k n n i' (Suc k)  =  D m i' (Suc k) k"
      using Suc.IH[OF cycle_free_to_k, of i' n] Suc.prems by auto
      ultimately have *:"fw m n k n n i' (Suc k) \<le> len m i' (Suc k) ys" using \<open>i' \<noteq> Suc k\<close>
      by (auto simp: D_def)

      have "set zs \<subseteq> {0..k}" using ys_zs(4) xs(2) ys_zs_id using atLeastAtMostSuc_conv by auto
      hence "len m (Suc k) j' zs \<in> ?S k (Suc k) j'" using ys_zs_id ys_zs xs(3,4,5) by fastforce
      with Min_le[OF _ this] have "Min (?S k (Suc k) j') \<le> len m (Suc k) j' zs"
      using D_base_finite'[of m "Suc k" j' k] \<open>j' \<noteq> Suc k\<close> by fastforce
      moreover have "fw m n k n n (Suc k) j'  =  D m (Suc k) j' k"
      using Suc.IH[OF cycle_free_to_k, of "Suc k" n j' n] Suc.prems by auto
      ultimately have **:"fw m n k n n (Suc k) j' \<le> len m (Suc k) j' zs" using \<open>j' \<noteq> Suc k\<close>
      by (auto simp: D_def)

      have len_eq: "l = len m i' (Suc k) ys + len m (Suc k) j' zs"
      by (simp add: xs(1) len_decomp[OF ys_zs_id, symmetric] ys_zs_id)
      have "fw m n (Suc k) i' j' i' j' \<le> fw m n k n n i' (Suc k) + fw m n k n n (Suc k) j'"
      using fw_step_Suc[of n m k i' j', OF K] Suc.prems(2-) by simp
      hence "fw m n (Suc k) i' j' i' j' \<le> l"
      using fw_step_Suc[of n m k i j] Suc.prems(3-) * ** len_eq add_mono by fastforce
      thus ?thesis using fw_invariant[of "Suc k" "Suc k" i n j j' i' m i' j'] Suc.prems(2-) by simp
    qed
  next
    have "fw m n (Suc k) i j i' j' = fw m n (Suc k) i' j' i' j'"
    using single_iteration_inv[OF Suc.prems(2-5)] .
    also have "\<dots> = min (fw m n k n n i' j') (fw m n k n n i' (Suc k) + fw m n k n n (Suc k) j')"
    using fw_step_Suc[OF K] Suc.prems(2-) by simp
    finally show "fw m n (Suc k) i j i' j' \<in> {len m i' j' xs | xs. set xs \<subseteq> {0..Suc k}}"
    proof (cases "fw m n (Suc k) i j i' j' = fw m n k n n i' j'", goal_cases)
      case True
      have "fw m n (Suc k) i j i' j' = D m i' j' k"
      using Suc.IH[OF cycle_free_to_k, of i' n j' n] Suc.prems(2-) True by simp
      from D_dest'[OF this] show ?thesis by blast
    next
      case 2
      hence A:"fw m n (Suc k) i j i' j' = fw m n k n n i' (Suc k) + fw m n k n n (Suc k) j'"
      by (metis ord.min_def)
      have "fw m n k n n i' j' = D m i' j' k"
      using Suc.IH[OF cycle_free_to_k, of i' n j' n] Suc.prems by simp
      from D_dest[OF this] have B:"fw m n k n n i' j' \<in> ?S (Suc k) i' j'"
      by blast
      have "fw m n k n n i' (Suc k) = D m i' (Suc k) k"
      using Suc.IH[OF cycle_free_to_k, of i' n "Suc k" n] Suc.prems by simp
      from D_dest'[OF this] obtain xs where xs:
        "fw m n k n n i' (Suc k) = len m i' (Suc k) xs" "set xs \<subseteq> {0..Suc k}" by blast
      have "fw m n k n n (Suc k) j' = D m (Suc k) j' k"
      using Suc.IH[OF cycle_free_to_k, of "Suc k" n j' n] Suc.prems by simp
      from D_dest'[OF this] obtain ys where ys:
        "fw m n k n n (Suc k) j' = len m (Suc k) j' ys" "set ys \<subseteq> {0..Suc k}" by blast
      from A xs(1) ys(1) len_comp
      have "fw m n (Suc k) i j i' j' = len m i' j' (xs @ Suc k # ys)" by simp
      moreover have "set (xs @ Suc k # ys) \<subseteq> {0..Suc k}" using xs(2) ys(2) by auto
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma cycle_free_cycle_free_up_to:
  "cycle_free m n \<Longrightarrow> k \<le> n \<Longrightarrow> cycle_free_up_to m k n"
unfolding cycle_free_def cycle_free_up_to_def by force

lemma cycle_free_diag:
  "cycle_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> \<one> \<le> m i i"
using cycle_free_up_to_diag[OF cycle_free_cycle_free_up_to] by blast

corollary fw_shortest_path:
  "cycle_free m n \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n
        \<Longrightarrow> D m i' j' k = fw m n k i j i' j'"
using fw_shortest_path_up_to[OF cycle_free_cycle_free_up_to] by auto

corollary fw_shortest:
  assumes "cycle_free m n" "i \<le> n" "j \<le> n" "k \<le> n"
  shows "fw m n n n n i j \<le> fw m n n n n i k + fw m n n n n k j"
proof (rule ccontr, goal_cases)
  case 1
  let ?S = "\<lambda> i j. {len m i j xs |xs. set xs \<subseteq> {0..n}}"
  let ?FW = "fw m n n n n"
  from assms fw_shortest_path
  have FW: "?FW i j = D m i j n" "?FW i k = D m i k n" "?FW k j = D m k j n" by auto
  with D_dest'' FW have "?FW i k \<in> ?S i k" "?FW k j \<in> ?S k j" by auto
  then obtain xs ys where xs_ys:
    "?FW i k = len m i k xs" "set xs \<subseteq> {0..n}" "?FW k j = len m k j ys" "set ys \<subseteq> {0..n}" by auto
  let ?zs = "rem_cycles i j (xs @ k # ys)"
  have *:"?FW i j = Min {len m i j xs |xs. set xs \<subseteq> {0..n} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  using FW(1) unfolding D_def .
  have "set (xs @ k # ys) \<subseteq> {0..n}" using assms xs_ys by fastforce
  from cycle_free_dest [OF \<open>cycle_free m n\<close> \<open>i \<le> n\<close> \<open>j \<le> n\<close> this]
  have **:"len m i j ?zs \<le> len m i j (xs @ k # ys)" by auto
  moreover have "i \<notin> set ?zs" "j \<notin> set ?zs" "distinct ?zs"
  using rem_cycles_distinct remove_all_removes rem_cycles_removes_last by fast+
  moreover have "set ?zs \<subseteq> {0..n}" using rem_cycles_subs[of i j"xs @ k # ys"] xs_ys assms by fastforce
  ultimately have
    "len m i j ?zs \<in> {len m i j xs |xs. set xs \<subseteq> {0..n} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  by blast
  with * have "?FW i j \<le> len m i j ?zs" using D_base_finite'' by auto
  with ** xs_ys len_comp 1 show ?case by auto
qed


section \<open>Result Under the Presence of Negative Cycles\<close>

lemma not_cylce_free_dest: "\<not> cycle_free m n \<Longrightarrow> \<exists> k \<le> n. \<not> cycle_free_up_to m k n"
by (auto simp add: cycle_free_def cycle_free_up_to_def)

lemma D_not_diag_le:
  "(x :: 'a) \<in> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}
  \<Longrightarrow> D m i j k \<le> x" using Min_le[OF D_base_finite''] by (auto simp add: D_def)

lemma D_not_diag_le': "set xs \<subseteq> {0..k} \<Longrightarrow> i \<notin> set xs \<Longrightarrow> j \<notin> set xs \<Longrightarrow> distinct xs
  \<Longrightarrow> D m i j k \<le> len m i j xs" using Min_le[OF D_base_finite''] by (fastforce simp add: D_def)

lemma (in -) nat_upto_subs_top_removal':
  "S \<subseteq> {0..Suc n} \<Longrightarrow> Suc n \<notin> S \<Longrightarrow> S \<subseteq> {0..n}"
apply (induction n)
 apply safe
 apply (rename_tac x)
 apply (case_tac "x = Suc 0"; fastforce)
apply (rename_tac n x)
apply (case_tac "x = Suc (Suc n)"; fastforce)
done

lemma (in -) nat_upto_subs_top_removal:
  "S \<subseteq> {0..n::nat} \<Longrightarrow> n \<notin> S \<Longrightarrow> S \<subseteq> {0..n - 1}"
using nat_upto_subs_top_removal' by (cases n; simp)

lemma fw_Suc:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> fw m n (Suc k) i' j' i j \<le> fw m n k n n i j"
by (metis Suc_innermost_id1' Suc_innermost_id2 Suc_innermost_mono linorder_class.not_le local.eq_iff
          preorder_class.order_refl single_iteration_inv single_iteration_inv')

lemma negative_len_shortest:
  "length xs = n \<Longrightarrow> len m i i xs < \<one>
    \<Longrightarrow> \<exists> j ys. distinct (j # ys) \<and> len m j j ys < \<one> \<and> j \<in> set (i # xs) \<and> set ys \<subseteq> set xs"
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
      proof (cases "len m i i as < \<one>")
        case True
        from xs less.prems have "length as < n" by auto
        from less.IH[OF this _ True] xs show ?thesis by auto
      next
        case False
        from len_decomp[OF xs] have "len m i i xs = len m i i as + len m i i bs" by auto
        with False less.prems have *: "len m i i bs < \<one>"
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
        proof (cases "len m a a bs < \<one>")
          case True
          from xs less.prems have "length bs < n" by auto
          from less.IH[OF this _ True] xs show ?thesis by auto
        next
          case False
          from len_decomp[OF xs, of m  i i] len_decomp[of "bs @ a # cs" bs a cs m a i]
          have *:"len m i i xs = len m i a as + (len m a a bs + len m a i cs)" by auto
          from False have "len m a a bs \<ge> \<one>" by auto
          with add_mono have "len m a a bs + len m a i cs \<ge> len m a i cs" by fastforce
          with * have "len m i i xs \<ge> len m i a as + len m a i cs" by (simp add: add_mono)
          with less.prems(2) have "len m i a as + len m a i cs < \<one>" by auto
          with len_comp have "len m i i (as @ a # cs) < \<one>" by auto
          from less.IH[OF _ _ this, of "length (as @ a # cs)"] xs less.prems
          show ?thesis by auto
        qed
      qed
    qed
  qed
qed

theorem FW_neg_cycle_detect:
  "\<not> cycle_free m n \<Longrightarrow> \<exists> i \<le> n. fw m n n n n i i < \<one>"
proof -
  assume A: "\<not> cycle_free m n"
  let ?K = "{k. k \<le> n \<and> \<not> cycle_free_up_to m k n}"
  let ?k = "Min ?K"
  have not_empty_K: "?K \<noteq> {}" using not_cylce_free_dest[OF A(1)] by auto
  have "finite ?K" by auto
  with not_empty_K have *:
    "\<forall> k' < ?k. cycle_free_up_to m k' n"
  by (auto, metis le_trans less_or_eq_imp_le preorder_class.less_irrefl)
  from linorder_class.Min_in[OF \<open>finite ?K\<close> \<open>?K \<noteq> {}\<close>] have
    "\<not> cycle_free_up_to m ?k n" "?k \<le> n"
  by auto
  then have "\<exists> xs j. j \<le> n \<and> len m j j xs < \<one> \<and> set xs \<subseteq> {0..?k}" unfolding cycle_free_up_to_def
  proof (auto, goal_cases)
    case (2 i xs) then have "len m i i xs < \<one>" by auto
    with 2 show ?case by auto
  next
    case (1 i xs j)
    then have "len m i j (rem_cycles i j xs) > len m i j xs" by auto
    from negative_cycle_dest[OF this]
    obtain i' ys where ys: "i' \<in> set (i # j # xs)" "len m i' i' ys < \<one>" "set ys \<subseteq> set xs" by blast
    from ys(1) 1(2-4) show ?case
    proof (auto, goal_cases)
      case 1
      with ys(2,3) show ?case by auto
    next
      case 2
      with ys(2,3) show ?case by auto
    next
      case 3
      with \<open>?k \<le> n\<close> have "i' \<le> n" unfolding cycle_free_up_to_def by auto
      with 3 ys(2,3) show ?case by auto
    qed
  qed
  then obtain a as where a_as: "a \<le> n \<and> len m a a as < \<one> \<and> set as \<subseteq> {0..?k}" by auto
  with negative_len_shortest[of as "length as" m a] obtain j xs where j_xs:
  "distinct (j # xs) \<and> len m j j xs < \<one> \<and> j \<in> set (a # as) \<and> set xs \<subseteq> set as" by auto
  with a_as \<open>?k \<le> n\<close> have cyc: "j \<le> n" "set xs \<subseteq> {0..?k}" "len m j j xs < \<one>" "distinct (j # xs)"
  by auto
  { assume "?k > 0"
    then have "?k - 1 < ?k" by simp
    with * have **:"cycle_free_up_to m (?k - 1) n" by blast
    have "?k \<in> set xs"
    proof (rule ccontr, goal_cases)
      case 1
      with \<open>set xs \<subseteq> {0..?k}\<close> nat_upto_subs_top_removal have "set xs \<subseteq> {0..?k-1}" by auto
      from cycle_free_up_to_loop_dest[OF \<open>j \<le> n\<close> this \<open>cycle_free_up_to m (?k - 1) n\<close>] cyc(3)
      show ?case by auto
    qed
    with cyc(4) have "j \<noteq> ?k" by auto
    from \<open>?k \<in> set xs\<close> obtain ys zs where "xs = ys @ ?k # zs" by (meson split_list)
    with \<open>distinct (j # xs)\<close>
    have xs: "xs = ys @ ?k # zs" "distinct ys" "distinct zs" "?k \<notin> set ys" "?k \<notin> set zs"
             "j \<notin> set ys" "j \<notin> set zs" by auto
    from xs(1,4) \<open>set xs \<subseteq> {0..?k}\<close> nat_upto_subs_top_removal have ys: "set ys \<subseteq> {0..?k-1}" by auto
    from xs(1,5) \<open>set xs \<subseteq> {0..?k}\<close> nat_upto_subs_top_removal have zs: "set zs \<subseteq> {0..?k-1}" by auto
    have "D m j ?k (?k - 1) = fw m n (?k - 1) n n j ?k"
    using \<open>?k \<le> n\<close> \<open>j \<le> n\<close> fw_shortest_path_up_to[OF **, of j n ?k n] by auto
    moreover have "D m ?k j (?k - 1) = fw m n (?k - 1) n n ?k j"
    using \<open>?k \<le> n\<close> \<open>j \<le> n\<close> fw_shortest_path_up_to[OF **, of ?k n j n] by auto
    ultimately have "fw m n (?k - 1) n n j ?k + fw m n (?k - 1) n n ?k j \<le> len m j ?k ys + len m ?k j zs"
    using D_not_diag_le'[OF zs(1) xs(5,7,3), of m]
          D_not_diag_le'[OF ys(1) xs(6,4,2), of m] by (auto simp: add_mono)
    then have neg: "fw m n (?k - 1) n n j ?k + fw m n (?k - 1) n n ?k j < \<one>"
    using xs(1) \<open>len m j j xs < \<one>\<close> len_comp by auto
    have "fw m n ?k j j j j \<le> fw m n (?k - 1) n n j ?k + fw m n (?k - 1) n n ?k j"
    proof (cases "j = 0")
      case True
      with\<open>?k > 0\<close> fw.simps(2)[of m n "?k - 1"]
      have "fw m n ?k j j = fw_upd (fw m n (?k - 1) n n) ?k j j" by auto
      then have "fw m n ?k j j j j \<le> fw m n (?k - 1) n n j ?k + fw m n (?k - 1) n n ?k j"
      by (simp add: fw_upd_def upd_def)
      then show ?thesis by auto
    next
      case False
      with fw.simps(4)[of m n ?k j "j - 1"]
      have "fw m n ?k j j = fw_upd (fw m n ?k j (j -1)) ?k j j" by simp
      then have *: "fw m n ?k j j j j \<le> fw m n ?k j (j -1) j ?k + fw m n ?k j (j -1) ?k j"
      by (simp add: fw_upd_def upd_def)
      have "j - 1 < n" using \<open>j \<le> n\<close> False by auto
      then have "fw m n ?k j (j -1) j ?k \<le> fw m n (?k - 1) n n j ?k"
      using fw_Suc[of j n ?k j "j - 1" m "?k - 1"] \<open>j \<le> n\<close> \<open>?k \<le> n\<close> \<open>?k > 0\<close> by auto
      moreover have "fw m n ?k j (j -1) ?k j \<le> fw m n (?k - 1) n n ?k j"
      using fw_Suc[of ?k n j j "j - 1" m "?k - 1"] \<open>j \<le> n\<close> \<open>?k \<le> n\<close> \<open>?k > 0\<close> by auto
      ultimately have "fw m n ?k j j j j \<le> fw m n (?k - 1) n n j ?k + fw m n (?k - 1) n n ?k j"
      using * add_mono by fastforce
      then show ?thesis by auto
    qed
    with neg have "fw m n ?k j j j j < \<one>" by auto
    moreover have "fw m n n n n j j \<le> fw m n ?k j j j j" using fw_invariant \<open>j\<le>n\<close> \<open>?k \<le> n\<close> by auto
    ultimately have "fw m n n n n j j < \<one>" using neg by auto
    with \<open>j\<le>n\<close> have ?thesis by auto
  }
  moreover
  { assume "?k = 0"
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
      with cyc have "m j j < \<one>" by auto
      with fw_mono[of n n n j j m n] \<open>j \<le> n\<close> have "fw m n n n n j j < \<one>" by auto
      with \<open>j \<le> n\<close> show ?thesis by auto
    next
      assume xs: "xs = [0]"
      with cyc have "m j 0 + m 0 j < \<one>" by auto
      then have "fw m n 0 j j j j < \<one>"
      proof (cases "j = 0", goal_cases)
        case 1
        have "m j j < \<one>"
        proof (rule ccontr)
          assume "\<not> m j j < \<one>"
          with 1 have "m 0 0 \<ge> \<one>" by simp
          with add_mono have "m 0 0 + m 0 0 \<ge> \<one>" by fastforce
          with 1 show False by simp
        qed
        with fw_mono[of j n j j j m 0] \<open>j \<le> n\<close> show ?thesis by auto
      next
        case 2
        with fw.simps(4)[of m n 0 j "j - 1"]
        have "fw m n 0 j j = fw_upd (fw m n 0 j (j - 1)) 0 j j" by simp
        then have "fw m n 0 j j j j \<le> fw m n 0 j (j - 1) j 0 + fw m n 0 j (j - 1) 0 j"
        by (simp add: fw_upd_def upd_def)
        also have "\<dots> \<le> m j 0 + m 0 j" using \<open>j \<le> n\<close> add_mono fw_mono by auto
        finally show ?thesis using 2 by auto
      qed
      then have "fw m n 0 n n j j < \<one>" by (metis cyc(1) less_or_eq_imp_le single_iteration_inv) 
      with fw_invariant[of 0 n n n n n n m j j] \<open>j \<le> n\<close> have "fw m n n n n j j < \<one>" by auto
      with \<open>j \<le> n\<close> show ?thesis by blast
    qed
  }
  ultimately show ?thesis by auto
qed

end (* End of local class context *)
end (* End of theory *)
