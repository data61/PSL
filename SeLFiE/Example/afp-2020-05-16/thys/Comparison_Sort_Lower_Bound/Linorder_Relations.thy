(*
   File:    Linorder_Relations.thy
   Author:  Manuel Eberl

   Linear orderings represented as relations (i.e. set of pairs). Also contains 
   material connecting such orderings to lists, and insertion sort w.r.t. a 
   given ordering relation.
*)
section \<open>Linear orderings as relations\<close>
theory Linorder_Relations
  imports 
    Complex_Main 
    "HOL-Library.Multiset_Permutations"
    "List-Index.List_Index"
begin

subsection \<open>Auxiliary facts\<close>

(* TODO: Move *)
lemma distinct_count_atmost_1':
  "distinct xs = (\<forall>a. count (mset xs) a \<le> 1)"
proof -
  {
    fix x have "count (mset xs) x = (if x \<in> set xs then 1 else 0) \<longleftrightarrow> count (mset xs) x \<le> 1"
      using count_eq_zero_iff[of "mset xs" x]
      by (cases "count (mset xs) x") (auto simp del: count_mset_0_iff) 
  }
  thus ?thesis unfolding distinct_count_atmost_1 by blast
qed
        
lemma distinct_mset_mono: 
  assumes "distinct ys" "mset xs \<subseteq># mset ys"
  shows   "distinct xs" 
  unfolding distinct_count_atmost_1'
proof
  fix x
  from assms(2) have "count (mset xs) x \<le> count (mset ys) x"
    by (rule mset_subset_eq_count)
  also from assms(1) have "\<dots> \<le> 1" unfolding distinct_count_atmost_1' ..
  finally show "count (mset xs) x \<le> 1" .
qed

lemma mset_eq_imp_distinct_iff:
  assumes "mset xs = mset ys"
  shows   "distinct xs \<longleftrightarrow> distinct ys"
  using assms by (simp add: distinct_count_atmost_1')

lemma total_on_subset: "total_on B R \<Longrightarrow> A \<subseteq> B \<Longrightarrow> total_on A R"
  by (auto simp: total_on_def)
 

subsection \<open>Sortedness w.r.t. a relation\<close>

inductive sorted_wrt :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> bool" for R where
  "sorted_wrt R []"
| "sorted_wrt R xs \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> (x,y) \<in> R) \<Longrightarrow> sorted_wrt R (x # xs)"

lemma sorted_wrt_Nil [simp]: "sorted_wrt R []"
  by (rule sorted_wrt.intros)

lemma sorted_wrt_Cons: "sorted_wrt R (x # xs) \<longleftrightarrow> (\<forall>y\<in>set xs. (x,y) \<in> R) \<and> sorted_wrt R xs"
  by (auto intro: sorted_wrt.intros elim: sorted_wrt.cases)

lemma sorted_wrt_singleton [simp]: "sorted_wrt R [x]"
  by (intro sorted_wrt.intros) simp_all

lemma sorted_wrt_many:
  assumes "trans R"
  shows   "sorted_wrt R (x # y # xs) \<longleftrightarrow> (x,y) \<in> R \<and> sorted_wrt R (y # xs)"
  by (force intro: sorted_wrt.intros transD[OF assms] elim: sorted_wrt.cases)

lemma sorted_wrt_imp_le_last:
  assumes "sorted_wrt R xs" "xs \<noteq> []" "x \<in> set xs" "x \<noteq> last xs"
  shows   "(x, last xs) \<in> R"
  using assms by induction auto
    
lemma sorted_wrt_append:
  assumes "sorted_wrt R xs" "sorted_wrt R ys" 
          "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> (x,y) \<in> R" "trans R"
  shows   "sorted_wrt R (xs @ ys)"
  using assms by (induction xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_snoc:
  assumes "sorted_wrt R xs" "(last xs, y) \<in> R" "trans R"
  shows   "sorted_wrt R (xs @ [y])"
  using assms(1,2)
proof induction
  case (2 xs x)
  show ?case
  proof (cases "xs = []")
    case False
    with 2 have "(z,y) \<in> R" if "z \<in> set xs" for z
      using that by (cases "z = last xs")
                    (auto intro: assms transD[OF assms(3), OF sorted_wrt_imp_le_last[OF 2(1)]])
    from False have *: "last xs \<in> set xs" by simp
    moreover from 2 False have "(x,y) \<in> R" by (intro transD[OF assms(3) 2(2)[OF *]]) simp
    ultimately show ?thesis using 2 False
      by (auto intro!: sorted_wrt.intros)
  qed (insert 2, auto intro: sorted_wrt.intros)
qed simp_all
  
lemma sorted_wrt_conv_nth:
  "sorted_wrt R xs \<longleftrightarrow> (\<forall>i j. i < j \<and> j < length xs \<longrightarrow> (xs!i, xs!j) \<in> R)"
  by (induction xs) (auto simp: sorted_wrt_Cons nth_Cons set_conv_nth split: nat.splits)


subsection \<open>Linear orderings\<close>

definition linorder_on :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"  where
  "linorder_on A R \<longleftrightarrow> refl_on A R \<and> antisym R \<and> trans R \<and> total_on A R"
 
lemma linorder_on_cases:
  assumes "linorder_on A R" "x \<in> A" "y \<in> A"
  shows   "x = y \<or> ((x, y) \<in> R \<and> (y, x) \<notin> R) \<or> ((y, x) \<in> R \<and> (x, y) \<notin> R)"
  using assms by (auto simp: linorder_on_def refl_on_def total_on_def antisym_def)

lemma sorted_wrt_linorder_imp_index_le:
  assumes "linorder_on A R" "set xs \<subseteq> A" "sorted_wrt R xs" 
          "x \<in> set xs" "y \<in> set xs" "(x,y) \<in> R"
  shows   "index xs x \<le> index xs y"
proof -
  define i j where "i = index xs x" and "j = index xs y"
  {
    assume "j < i"
    moreover from assms have "i < length xs" by (simp add: i_def)
    ultimately have "(xs!j,xs!i) \<in> R" using assms by (auto simp: sorted_wrt_conv_nth)
    with assms have "x = y" by (auto simp: linorder_on_def antisym_def i_def j_def)
  }
  hence "i \<le> j \<or> x = y" by linarith
  thus ?thesis by (auto simp: i_def j_def)
qed

lemma sorted_wrt_linorder_index_le_imp:
  assumes "linorder_on A R" "set xs \<subseteq> A" "sorted_wrt R xs" 
          "x \<in> set xs" "y \<in> set xs" "index xs x \<le> index xs y"
  shows   "(x,y) \<in> R"
proof (cases "x = y")
  case False
  define i j where "i = index xs x" and "j = index xs y"
  from False and assms have "i \<noteq> j" by (simp add: i_def j_def)
  with \<open>index xs x \<le> index xs y\<close> have "i < j" by (simp add: i_def j_def)
  moreover from assms have "j < length xs" by (simp add: j_def)
  ultimately have "(xs ! i, xs ! j) \<in> R" using assms(3)
    by (auto simp: sorted_wrt_conv_nth)
  with assms show ?thesis by (simp_all add: i_def j_def)
qed (insert assms, auto simp: linorder_on_def refl_on_def)

lemma sorted_wrt_linorder_index_le_iff:
  assumes "linorder_on A R" "set xs \<subseteq> A" "sorted_wrt R xs" 
          "x \<in> set xs" "y \<in> set xs"
  shows   "index xs x \<le> index xs y \<longleftrightarrow> (x,y) \<in> R"
  using sorted_wrt_linorder_index_le_imp[OF assms] sorted_wrt_linorder_imp_index_le[OF assms] 
  by blast
    
lemma sorted_wrt_linorder_index_less_iff:
  assumes "linorder_on A R" "set xs \<subseteq> A" "sorted_wrt R xs" 
          "x \<in> set xs" "y \<in> set xs"
  shows   "index xs x < index xs y \<longleftrightarrow> (y,x) \<notin> R"
  by (subst sorted_wrt_linorder_index_le_iff[OF assms(1-3) assms(5,4), symmetric]) auto

lemma sorted_wrt_distinct_linorder_nth:
  assumes "linorder_on A R" "set xs \<subseteq> A" "sorted_wrt R xs" "distinct xs" 
          "i < length xs" "j < length xs"
  shows   "(xs!i, xs!j) \<in> R \<longleftrightarrow> i \<le> j"
proof (cases i j rule: linorder_cases)
  case less
  with assms show ?thesis by (simp add: sorted_wrt_conv_nth)
next
  case equal
  from assms have "xs ! i \<in> set xs" "xs ! j \<in> set xs" by (auto simp: set_conv_nth)
  with assms(2) have "xs ! i \<in> A" "xs ! j \<in> A" by blast+
  with \<open>linorder_on A R\<close> and equal show ?thesis by (simp add: linorder_on_def refl_on_def)
next
  case greater
  with assms have "(xs!j, xs!i) \<in> R" by (auto simp add: sorted_wrt_conv_nth)
  moreover from assms and greater have "xs ! i \<noteq> xs ! j" by (simp add: nth_eq_iff_index_eq)
  ultimately show ?thesis using \<open>linorder_on A R\<close> greater
    by (auto simp: linorder_on_def antisym_def)
qed
  

subsection \<open>Converting a list into a linear ordering\<close>

definition linorder_of_list :: "'a list \<Rightarrow> ('a \<times> 'a) set" where
  "linorder_of_list xs = {(a,b). a \<in> set xs \<and> b \<in> set xs \<and> index xs a \<le> index xs b}"

lemma linorder_linorder_of_list [intro, simp]:
  assumes "distinct xs"
  shows   "linorder_on (set xs) (linorder_of_list xs)"
  unfolding linorder_on_def using assms
  by (auto simp: refl_on_def antisym_def trans_def total_on_def linorder_of_list_def)

lemma sorted_wrt_linorder_of_list [intro, simp]: 
  "distinct xs \<Longrightarrow> sorted_wrt (linorder_of_list xs) xs"
  by (auto simp: sorted_wrt_conv_nth linorder_of_list_def index_nth_id)


subsection \<open>Insertion sort\<close>

primrec insert_wrt :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_wrt R x [] = [x]"
| "insert_wrt R x (y # ys) = (if (x, y) \<in> R then x # y # ys else y # insert_wrt R x ys)"

lemma set_insert_wrt [simp]: "set (insert_wrt R x xs) = insert x (set xs)"
  by (induction xs) auto

lemma mset_insert_wrt [simp]: "mset (insert_wrt R x xs) = add_mset x (mset xs)"
  by (induction xs) auto

lemma length_insert_wrt [simp]: "length (insert_wrt R x xs) = Suc (length xs)"
  by (induction xs) simp_all

definition insort_wrt :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort_wrt R xs = foldr (insert_wrt R) xs []"

lemma set_insort_wrt [simp]: "set (insort_wrt R xs) = set xs"
  by (induction xs) (simp_all add: insort_wrt_def)

lemma mset_insort_wrt [simp]: "mset (insort_wrt R xs) = mset xs"
  by (induction xs) (simp_all add: insort_wrt_def)
    
lemma length_insort_wrt [simp]: "length (insort_wrt R xs) = length xs"
  by (induction xs) (simp_all add: insort_wrt_def)

lemma sorted_wrt_insert_wrt [intro]: 
  "linorder_on A R \<Longrightarrow> set (x # xs) \<subseteq> A \<Longrightarrow> 
     sorted_wrt R xs \<Longrightarrow> sorted_wrt R (insert_wrt R x xs)"
proof (induction xs)
  case (Cons y ys)
  from Cons.prems have "(x,y) \<in> R \<or> (y,x) \<in> R" 
    by (cases "x = y") (auto simp: linorder_on_def refl_on_def total_on_def)
  with Cons show ?case
    by (auto simp: sorted_wrt_Cons intro: transD simp: linorder_on_def)
qed auto

lemma sorted_wrt_insort [intro]:
  assumes "linorder_on A R" "set xs \<subseteq> A"
  shows   "sorted_wrt R (insort_wrt R xs)"
proof -
  from assms have "set (insort_wrt R xs) = set xs \<and> sorted_wrt R (insort_wrt R xs)"
    by (induction xs) (auto simp: insort_wrt_def intro!: sorted_wrt_insert_wrt)
  thus ?thesis ..
qed

lemma distinct_insort_wrt [simp]: "distinct (insort_wrt R xs) \<longleftrightarrow> distinct xs"
  by (simp add: distinct_count_atmost_1)

lemma sorted_wrt_linorder_unique:
  assumes "linorder_on A R" "mset xs = mset ys" "sorted_wrt R xs" "sorted_wrt R ys"
  shows   "xs = ys"
proof -
  from \<open>mset xs = mset ys\<close> have "length xs = length ys" by (rule mset_eq_length)
  from this and assms(2-) show ?thesis
  proof (induction xs ys rule: list_induct2)
    case (Cons x xs y ys)
    have "set (x # xs) = set_mset (mset (x # xs))" by simp
    also have "mset (x # xs) = mset (y # ys)" by fact
    also have "set_mset \<dots> = set (y # ys)" by simp
    finally have eq: "set (x # xs) = set (y # ys)" .
    
    have "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      with eq have "x \<in> set ys" "y \<in> set xs" by auto
      with Cons.prems and assms(1) and eq have "(x, y) \<in> R" "(y, x) \<in> R"
        by (auto simp: sorted_wrt_Cons)
      with assms(1) have "x = y" by (auto simp: linorder_on_def antisym_def)
      with \<open>x \<noteq> y\<close> show False by contradiction
    qed
    with Cons show ?case by (auto simp: sorted_wrt_Cons)
  qed auto
qed


subsection \<open>Obtaining a sorted list of a given set\<close>

definition sorted_wrt_list_of_set where
  "sorted_wrt_list_of_set R A = 
     (if finite A then (THE xs. set xs = A \<and> distinct xs \<and> sorted_wrt R xs) else [])"
  
lemma mset_remdups: "mset (remdups xs) = mset_set (set xs)"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (cases "x \<in> set xs") (auto simp: insert_absorb)
qed auto
  
lemma sorted_wrt_list_set:
  assumes "linorder_on A R" "set xs \<subseteq> A"
  shows   "sorted_wrt_list_of_set R (set xs) = insort_wrt R (remdups xs)"
proof -
  have "sorted_wrt_list_of_set R (set xs) = 
          (THE xsa. set xsa = set xs \<and> distinct xsa \<and> sorted_wrt R xsa)"
    by (simp add: sorted_wrt_list_of_set_def)
  also have "\<dots> = insort_wrt R (remdups xs)"
  proof (rule the_equality)
    fix xsa assume xsa: "set xsa = set xs \<and> distinct xsa \<and> sorted_wrt R xsa"
    from xsa have "mset xsa = mset_set (set xsa)" by (subst mset_set_set) simp_all
    also from xsa have "set xsa = set xs" by simp
    also have "mset_set \<dots> = mset (remdups xs)" by (simp add: mset_remdups)
    finally show "xsa = insort_wrt R (remdups xs)" using xsa assms
      by (intro sorted_wrt_linorder_unique[OF assms(1)])
         (auto intro!: sorted_wrt_insort)
  qed (insert assms, auto intro!: sorted_wrt_insort)
  finally show ?thesis .
qed

lemma linorder_sorted_wrt_exists:
  assumes "linorder_on A R" "finite B" "B \<subseteq> A"
  shows   "\<exists>xs. set xs = B \<and> distinct xs \<and> sorted_wrt R xs"
proof -
  from \<open>finite B\<close> obtain xs where "set xs = B" "distinct xs"
    using finite_distinct_list by blast
  hence "set (insort_wrt R xs) = B" "distinct (insort_wrt R xs)" by simp_all
  moreover have "sorted_wrt R (insort_wrt R xs)"
    using assms \<open>set xs = B\<close> by (intro sorted_wrt_insort[OF assms(1)]) auto
  ultimately show ?thesis by blast
qed

lemma linorder_sorted_wrt_list_of_set:
  assumes "linorder_on A R" "finite B" "B \<subseteq> A"
  shows   "set (sorted_wrt_list_of_set R B) = B" "distinct (sorted_wrt_list_of_set R B)"
          "sorted_wrt R (sorted_wrt_list_of_set R B)"
proof -
  have "\<exists>!xs. set xs = B \<and> distinct xs \<and> sorted_wrt R xs"
  proof (rule ex_ex1I)
    show "\<exists>xs. set xs = B \<and> distinct xs \<and> sorted_wrt R xs"
      by (rule linorder_sorted_wrt_exists assms)+
  next
    fix xs ys assume "set xs = B \<and> distinct xs \<and> sorted_wrt R xs" 
                     "set ys = B \<and> distinct ys \<and> sorted_wrt R ys"
    thus "xs = ys" 
      by (intro sorted_wrt_linorder_unique[OF assms(1)]) (auto simp: set_eq_iff_mset_eq_distinct)
  qed
  from theI'[OF this] show  "set (sorted_wrt_list_of_set R B) = B" 
    "distinct (sorted_wrt_list_of_set R B)" "sorted_wrt R (sorted_wrt_list_of_set R B)" 
    by (simp_all add: sorted_wrt_list_of_set_def \<open>finite B\<close>)
qed

lemma sorted_wrt_list_of_set_eqI:
  assumes "linorder_on B R" "A \<subseteq> B" "set xs = A" "distinct xs" "sorted_wrt R xs"
  shows   "sorted_wrt_list_of_set R A = xs"
proof (rule sorted_wrt_linorder_unique)
  show "linorder_on B R" by fact
  let ?ys = "sorted_wrt_list_of_set R A"
  have fin [simp]: "finite A" by (simp_all add: assms(3) [symmetric])
  have *: "distinct ?ys" "set ?ys = A" "sorted_wrt R ?ys"
    by (rule linorder_sorted_wrt_list_of_set[OF assms(1)] fin assms)+
  from assms * show "mset ?ys = mset xs"
    by (subst set_eq_iff_mset_eq_distinct [symmetric]) simp_all
  show "sorted_wrt R ?ys" by fact
qed fact+



subsection \<open>Rank of an element in an ordering\<close>
  
text \<open>
  The `rank' of an element in a set w.r.t. an ordering is how many smaller elements exist.
  This is particularly useful in linear orders, where there exists a unique $n$-th element 
  for every $n$.
\<close>
definition linorder_rank where
  "linorder_rank R A x = card {y\<in>A-{x}. (y,x) \<in> R}"
  
lemma linorder_rank_le: 
  assumes "finite A"
  shows   "linorder_rank R A x \<le> card A"
  unfolding linorder_rank_def using assms
  by (rule card_mono) auto
    
lemma linorder_rank_less:
  assumes "finite A" "x \<in> A"
  shows   "linorder_rank R A x < card A"
proof -
  have "linorder_rank R A x \<le> card (A - {x})"
    unfolding linorder_rank_def using assms by (intro card_mono) auto
  also from assms have "\<dots> < card A" by (intro psubset_card_mono) auto
  finally show ?thesis .
qed

lemma linorder_rank_union:
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows   "linorder_rank R (A \<union> B) x = linorder_rank R A x + linorder_rank R B x"
proof -
  have "linorder_rank R (A \<union> B) x = card {y\<in>(A\<union>B)-{x}. (y,x) \<in> R}"
    by (simp add: linorder_rank_def)
  also have "{y\<in>(A\<union>B)-{x}. (y,x) \<in> R} = {y\<in>A-{x}. (y,x) \<in> R} \<union> {y\<in>B-{x}. (y,x) \<in> R}" by blast
  also have "card \<dots> = linorder_rank R A x + linorder_rank R B x" unfolding linorder_rank_def
    using assms by (intro card_Un_disjoint) auto
  finally show ?thesis .
qed

lemma linorder_rank_empty [simp]: "linorder_rank R {} x = 0"
  by (simp add: linorder_rank_def)

lemma linorder_rank_singleton: 
  "linorder_rank R {y} x = (if x \<noteq> y \<and> (y,x) \<in> R then 1 else 0)"
proof -
  have "linorder_rank R {y} x = card {z\<in>{y}-{x}. (z,x) \<in> R}" by (simp add: linorder_rank_def)
  also have "{z\<in>{y}-{x}. (z,x) \<in> R} = (if x \<noteq> y \<and> (y,x) \<in> R then {y} else {})" by auto
  also have "card \<dots> = (if x \<noteq> y \<and> (y,x) \<in> R then 1 else 0)" by simp
  finally show ?thesis .
qed

lemma linorder_rank_insert:
  assumes "finite A" "y \<notin> A"
  shows   "linorder_rank R (insert y A) x = 
             (if x \<noteq> y \<and> (y,x) \<in> R then 1 else 0) + linorder_rank R A x"
  using linorder_rank_union[of "{y}" A R x] assms by (auto simp: linorder_rank_singleton)
   
lemma linorder_rank_mono:
  assumes "linorder_on B R" "finite A" "A \<subseteq> B" "(x, y) \<in> R"
  shows   "linorder_rank R A x \<le> linorder_rank R A y"
  unfolding linorder_rank_def
proof (rule card_mono)
  from assms have trans: "trans R" and antisym: "antisym R" by (simp_all add: linorder_on_def)
  from assms antisym show "{y \<in> A - {x}. (y, x) \<in> R} \<subseteq> {ya \<in> A - {y}. (ya, y) \<in> R}"
    by (auto intro: transD[OF trans] simp: antisym_def)
qed (insert assms, simp_all)

lemma linorder_rank_strict_mono:
  assumes "linorder_on B R" "finite A" "A \<subseteq> B" "y \<in> A" "(y, x) \<in> R" "x \<noteq> y"
  shows   "linorder_rank R A y < linorder_rank R A x"
proof -
  from assms(1) have trans: "trans R" by (simp add: linorder_on_def)
  from assms have *: "(x, y) \<notin> R" by (auto simp: linorder_on_def antisym_def)
  from this and \<open>(y,x) \<in> R\<close> have "{z\<in>A-{y}. (z, y) \<in> R} \<subseteq> {z\<in>A-{x}. (z,x) \<in> R}"
    by (auto intro: transD[OF trans])
  moreover from * and assms have "y \<notin> {z\<in>A-{y}. (z, y) \<in> R}" "y \<in> {z\<in>A-{x}. (z, x) \<in> R}"
    by auto
  ultimately have "{z\<in>A-{y}. (z, y) \<in> R} \<subset> {z\<in>A-{x}. (z,x) \<in> R}" by blast
  thus ?thesis using assms unfolding linorder_rank_def by (intro psubset_card_mono) auto
qed      

lemma linorder_rank_le_iff:
  assumes "linorder_on B R" "finite A" "A \<subseteq> B" "x \<in> A" "y \<in> A"
  shows   "linorder_rank R A x \<le> linorder_rank R A y \<longleftrightarrow> (x, y) \<in> R"
proof (cases "x = y")
  case True
  with assms show ?thesis by (auto simp: linorder_on_def refl_on_def)
next
  case False
  from assms(1) have trans: "trans R" by (simp_all add: linorder_on_def)
  from assms have "x \<in> B" "y \<in> B" by auto
  with \<open>linorder_on B R\<close> and False have "((x,y) \<in> R \<and> (y,x) \<notin> R) \<or> ((y,x) \<in> R \<and> (x,y) \<notin> R)"
    by (fastforce simp: linorder_on_def antisym_def total_on_def)
  thus ?thesis
  proof
    assume "(x,y) \<in> R \<and> (y,x) \<notin> R"
    with assms show ?thesis by (auto intro!: linorder_rank_mono)
  next
    assume *: "(y,x) \<in> R \<and> (x,y) \<notin> R"
    with linorder_rank_strict_mono[OF assms(1-3), of y x] assms False 
      show ?thesis by auto
  qed
qed

lemma linorder_rank_eq_iff:
  assumes "linorder_on B R" "finite A" "A \<subseteq> B" "x \<in> A" "y \<in> A"
  shows   "linorder_rank R A x = linorder_rank R A y \<longleftrightarrow> x = y"
proof
  assume "linorder_rank R A x = linorder_rank R A y"
  with linorder_rank_le_iff[OF assms(1-5)] linorder_rank_le_iff[OF assms(1-3) assms(5,4)]
    have "(x, y) \<in> R" "(y, x) \<in> R" by simp_all
  with assms show "x = y" by (auto simp: linorder_on_def antisym_def)
qed simp_all
  
lemma linorder_rank_set_sorted_wrt:
  assumes "linorder_on B R" "set xs \<subseteq> B" "sorted_wrt R xs" "x \<in> set xs" "distinct xs"
  shows   "linorder_rank R (set xs) x = index xs x"
proof -
  define j where "j = index xs x"
  from assms have j: "j < length xs" by (simp add: j_def)
  have *: "x = y \<or> ((x, y) \<in> R \<and> (y, x) \<notin> R) \<or> ((y, x) \<in> R \<and> (x, y) \<notin> R)" if "y \<in> set xs" for y
    using linorder_on_cases[OF assms(1), of x y] assms that by auto
  from assms have "{y\<in>set xs-{x}. (y, x) \<in> R} = {y\<in>set xs-{x}. index xs y < index xs x}"
    by (auto simp: sorted_wrt_linorder_index_less_iff[OF assms(1-3)] dest: *)
  also have "\<dots> = {y\<in>set xs. index xs y < j}" by (auto simp: j_def)
  also have "\<dots> = (\<lambda>i. xs ! i) ` {i. i < j}"
  proof safe
    fix y assume "y \<in> set xs" "index xs y < j"
    moreover from this and j have "y = xs ! index xs y" by simp
    ultimately show "y \<in> (!) xs ` {i. i < j}" by blast
  qed (insert assms j, auto simp: index_nth_id)
  also from assms and j have "card \<dots> = card {i. i < j}" 
    by (intro card_image) (auto simp: inj_on_def nth_eq_iff_index_eq)
  also have "\<dots> = j" by simp
  finally show ?thesis by (simp only: j_def linorder_rank_def)
qed

lemma bij_betw_linorder_rank:
  assumes "linorder_on B R" "finite A" "A \<subseteq> B"
  shows   "bij_betw (linorder_rank R A) A {..<card A}"
proof -
  define xs where "xs = sorted_wrt_list_of_set R A"
  note xs = linorder_sorted_wrt_list_of_set[OF assms, folded xs_def]
  from \<open>distinct xs\<close> have len_xs: "length xs = card A"
    by (subst \<open>set xs = A\<close> [symmetric]) (auto simp: distinct_card)
  have rank: "linorder_rank R (set xs) x = index xs x" if "x \<in> A" for x
    using linorder_rank_set_sorted_wrt[OF assms(1), of xs x] assms that xs by simp_all
  from xs len_xs show ?thesis
    by (intro bij_betw_byWitness[where f' = "\<lambda>i. xs ! i"])
       (auto simp: rank index_nth_id intro!: nth_mem)
qed


subsection \<open>The bijection between linear orderings and lists\<close>

theorem bij_betw_linorder_of_list:
  assumes "finite A"
  shows   "bij_betw linorder_of_list (permutations_of_set A) {R. linorder_on A R}"
proof (intro bij_betw_byWitness[where f' = "\<lambda>R. sorted_wrt_list_of_set R A"] ballI subsetI,
       goal_cases)
  case (1 xs)
  thus ?case by (intro sorted_wrt_list_of_set_eqI) (auto simp: permutations_of_set_def)
next
  case (2 R)
  hence R: "linorder_on A R" by simp
  from R have in_R: "x \<in> A" "y \<in> A" if "(x,y) \<in> R" for x y using that 
    by (auto simp: linorder_on_def refl_on_def)
  let ?xs = "sorted_wrt_list_of_set R A"
  have xs: "distinct ?xs" "set ?xs = A" "sorted_wrt R ?xs"
    by (rule linorder_sorted_wrt_list_of_set[OF R] assms order.refl)+
  thus ?case using sorted_wrt_linorder_index_le_iff[OF R, of ?xs]
    by (auto simp: linorder_of_list_def dest: in_R)
next
  case (4 xs)
  then obtain R where R: "linorder_on A R" and xs [simp]: "xs = sorted_wrt_list_of_set R A" by auto
  let ?xs = "sorted_wrt_list_of_set R A"
  have xs: "distinct ?xs" "set ?xs = A" "sorted_wrt R ?xs"
    by (rule linorder_sorted_wrt_list_of_set[OF R] assms order.refl)+
  thus ?case by auto
qed (auto simp: permutations_of_set_def)

corollary card_finite_linorders:
  assumes "finite A"
  shows   "card {R. linorder_on A R} = fact (card A)"
proof -
  have "card {R. linorder_on A R} = card (permutations_of_set A)"
    by (rule sym, rule bij_betw_same_card [OF bij_betw_linorder_of_list[OF assms]])
  also from assms have "\<dots> = fact (card A)" by (rule card_permutations_of_set)
  finally show ?thesis .
qed

end
