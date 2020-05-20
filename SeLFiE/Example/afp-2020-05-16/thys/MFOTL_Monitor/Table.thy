(*<*)
theory Table
  imports Main
begin
(*>*)

section \<open>Finite Tables\<close>

primrec tabulate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "tabulate f x 0 = []"
| "tabulate f x (Suc n) = f x # tabulate f (Suc x) n"

lemma tabulate_alt: "tabulate f x n = map f [x ..< x + n]"
  by (induct n arbitrary: x) (auto simp: not_le Suc_le_eq upt_rec)

lemma length_tabulate[simp]: "length (tabulate f x n) = n"
  by (induction n arbitrary: x) simp_all

lemma map_tabulate[simp]: "map f (tabulate g x n) = tabulate (\<lambda>x. f (g x)) x n"
  by (induction n arbitrary: x) simp_all

lemma nth_tabulate[simp]: "k < n \<Longrightarrow> tabulate f x n ! k = f (x + k)"
proof (induction n arbitrary: x k)
  case (Suc n)
  then show ?case by (cases k) simp_all
qed simp

type_synonym 'a tuple = "'a option list"
type_synonym 'a table = "'a tuple set"

definition wf_tuple :: "nat \<Rightarrow> nat set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "wf_tuple n V x \<longleftrightarrow> length x = n \<and> (\<forall>i<n. x!i = None \<longleftrightarrow> i \<notin> V)"

definition table :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> bool" where
  "table n V X \<longleftrightarrow> (\<forall>x\<in>X. wf_tuple n V x)"

definition "empty_table = {}"

definition "unit_table n = {replicate n None}"

definition "singleton_table n i x = {tabulate (\<lambda>j. if i = j then Some x else None) 0 n}"

lemma in_empty_table[simp]: "\<not> x \<in> empty_table"
  unfolding empty_table_def by simp

lemma empty_table[simp]: "table n V empty_table"
  unfolding table_def empty_table_def by simp

lemma unit_table_wf_tuple[simp]: "V = {} \<Longrightarrow> x \<in> unit_table n \<Longrightarrow> wf_tuple n V x"
  unfolding unit_table_def wf_tuple_def by simp

lemma unit_table[simp]: "V = {} \<Longrightarrow> table n V (unit_table n)"
  unfolding table_def by simp

lemma in_unit_table: "v \<in> unit_table n \<longleftrightarrow> wf_tuple n {} v"
  unfolding unit_table_def wf_tuple_def by (auto intro!: nth_equalityI)

lemma singleton_table_wf_tuple[simp]: "V = {i} \<Longrightarrow> x \<in> singleton_table n i z \<Longrightarrow> wf_tuple n V x"
  unfolding singleton_table_def wf_tuple_def by simp

lemma singleton_table[simp]: "V = {i} \<Longrightarrow> table n V (singleton_table n i z)"
  unfolding table_def by simp

lemma table_Un[simp]: "table n V X \<Longrightarrow> table n V Y \<Longrightarrow> table n V (X \<union> Y)"
  unfolding table_def by auto

lemma wf_tuple_length: "wf_tuple n V x \<Longrightarrow> length x = n"
  unfolding wf_tuple_def by simp


fun join1 :: "'a tuple \<times> 'a tuple \<Rightarrow> 'a tuple option" where
  "join1 ([], []) = Some []"
| "join1 (None # xs, None # ys) = map_option (Cons None) (join1 (xs, ys))"
| "join1 (Some x # xs, None # ys) = map_option (Cons (Some x)) (join1 (xs, ys))"
| "join1 (None # xs, Some y # ys) = map_option (Cons (Some y)) (join1 (xs, ys))"
| "join1 (Some x # xs, Some y # ys) = (if x = y
    then map_option (Cons (Some x)) (join1 (xs, ys))
    else None)"
| "join1 _ = None"

definition join :: "'a table \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join A pos B = (if pos then Option.these (join1 ` (A \<times> B))
    else A - Option.these (join1 ` (A \<times> B)))"

lemma join_True_code[code]: "join A True B = (\<Union>a \<in> A. \<Union>b \<in> B. set_option (join1 (a, b)))"
  unfolding join_def by (force simp: Option.these_def image_iff)

lemma join_False_alt: "join X False Y = X - join X True Y"
  unfolding join_def by auto

lemma self_join1: "join1 (xs, ys) \<noteq> Some xs \<Longrightarrow> join1 (zs, ys) \<noteq> Some xs"
  by (induct "(zs, ys)" arbitrary: zs ys xs rule: join1.induct; auto; auto)

lemma join_False_code[code]: "join A False B = {a \<in> A. \<forall>b \<in> B. join1 (a, b) \<noteq> Some a}"
  unfolding join_False_alt join_True_code
  by (auto simp: Option.these_def image_iff dest: self_join1)

lemma wf_tuple_Nil[simp]: "wf_tuple n A [] = (n = 0)"
  unfolding wf_tuple_def by auto

lemma Suc_pred': "Suc (x - Suc 0) = (case x of 0 \<Rightarrow> Suc 0 | _ \<Rightarrow> x)"
  by (auto split: nat.splits)

lemma wf_tuple_Cons[simp]:
  "wf_tuple n A (x # xs) \<longleftrightarrow> ((if x = None then 0 \<notin> A else 0 \<in> A) \<and>
   (\<exists>m. n = Suc m \<and> wf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) xs))"
  unfolding wf_tuple_def
  by (auto 0 3 simp: nth_Cons image_iff Ball_def gr0_conv_Suc Suc_pred' split: nat.splits)

lemma join1_wf_tuple:
  "join1 (v1, v2) = Some v \<Longrightarrow> wf_tuple n A v1 \<Longrightarrow> wf_tuple n B v2 \<Longrightarrow> wf_tuple n (A \<union> B) v"
  by (induct "(v1, v2)" arbitrary: n v v1 v2 A B rule: join1.induct)
    (auto simp: image_Un Un_Diff split: if_splits)

lemma join_wf_tuple: "x \<in> join X b Y \<Longrightarrow>
  \<forall>v \<in> X. wf_tuple n A v \<Longrightarrow> \<forall>v \<in> Y. wf_tuple n B v \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> A \<union> B = C \<Longrightarrow> wf_tuple n C x"
  unfolding join_def
  by (fastforce simp: Option.these_def image_iff sup_absorb1 dest: join1_wf_tuple split: if_splits)

lemma join_table: "table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> A \<union> B = C \<Longrightarrow>
  table n C (join X b Y)"
  unfolding table_def by (auto elim!: join_wf_tuple)

lemma wf_tuple_Suc: "wf_tuple (Suc m) A a \<longleftrightarrow> a \<noteq> [] \<and>
   wf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) (tl a) \<and> (0 \<in> A \<longleftrightarrow> hd a \<noteq> None)"
  by (cases a) (auto simp: nth_Cons image_iff split: nat.splits)

lemma table_project: "table (Suc n) A X \<Longrightarrow> table n ((\<lambda>x. x - Suc 0) ` (A - {0})) (tl ` X)"
  unfolding table_def
  by (auto simp: wf_tuple_Suc)

definition restrict where
  "restrict A v = map (\<lambda>i. if i \<in> A then v ! i else None) [0 ..< length v]"

lemma restrict_Nil[simp]: "restrict A [] = []"
  unfolding restrict_def by auto

lemma restrict_Cons[simp]: "restrict A (x # xs) =
  (if 0 \<in> A then x # restrict ((\<lambda>x. x - 1) ` (A - {0})) xs else None # restrict ((\<lambda>x. x - 1) ` A) xs)"
  unfolding restrict_def
  by (auto simp: map_upt_Suc image_iff Suc_pred' Ball_def simp del: upt_Suc split: nat.splits)

lemma wf_tuple_restrict: "wf_tuple n B v \<Longrightarrow> A \<inter> B = C \<Longrightarrow> wf_tuple n C (restrict A v)"
  unfolding restrict_def wf_tuple_def by auto

lemma wf_tuple_restrict_simple: "wf_tuple n B v \<Longrightarrow> A \<subseteq> B \<Longrightarrow> wf_tuple n A (restrict A v)"
  unfolding restrict_def wf_tuple_def by auto

lemma nth_restrict: "i \<in> A \<Longrightarrow> i < length v \<Longrightarrow> restrict A v ! i = v ! i"
  unfolding restrict_def by auto

lemma restrict_eq_Nil[simp]: "restrict A v = [] \<longleftrightarrow> v = []"
  unfolding restrict_def by auto

lemma length_restrict[simp]: "length (restrict A v) = length v"
  unfolding restrict_def by auto

lemma join1_Some_restrict:
  fixes x y :: "'a tuple"
  assumes "wf_tuple n A x" "wf_tuple n B y"
  shows "join1 (x, y) = Some z \<longleftrightarrow> wf_tuple n (A \<union> B) z \<and> restrict A z = x \<and> restrict B z = y"
  using assms
proof (induct "(x, y)" arbitrary: n x y z A B rule: join1.induct)
  case (2 xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (3 x xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (4 xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (5 x xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
qed auto

lemma restrict_idle: "wf_tuple n A v \<Longrightarrow> restrict A v = v"
  by (induct v arbitrary: n A) (auto split: if_splits)

lemma map_the_restrict:
  "i \<in> A \<Longrightarrow> map the (restrict A v) ! i = map the v ! i"
  by (induct v arbitrary: A i) (auto simp: nth_Cons' gr0_conv_Suc split: option.splits)

lemma join_restrict:
  fixes X Y :: "'a tuple set"
  assumes "\<And>v. v \<in> X \<Longrightarrow> wf_tuple n A v" "\<And>v. v \<in> Y \<Longrightarrow> wf_tuple n B v" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> join X b Y \<longleftrightarrow>
    wf_tuple n (A \<union> B) v \<and> restrict A v \<in> X \<and> (if b then restrict B v \<in> Y else restrict B v \<notin> Y)"
  by (auto 4 4 simp: join_def Option.these_def image_iff assms wf_tuple_restrict sup_absorb1 restrict_idle
    restrict_idle[OF assms(1)] elim: assms
    dest: join1_Some_restrict[OF assms(1,2), THEN iffD1, rotated -1]
    dest!: spec[of _ "Some v"]
    intro!: exI[of _ "Some v"] join1_Some_restrict[THEN iffD2, symmetric] bexI[rotated])

lemma join_restrict_table:
  assumes "table n A X" "table n B Y" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> join X b Y \<longleftrightarrow>
    wf_tuple n (A \<union> B) v \<and> restrict A v \<in> X \<and> (if b then restrict B v \<in> Y else restrict B v \<notin> Y)"
  using assms unfolding table_def
  by (simp add: join_restrict)

lemma join_restrict_annotated:
  fixes X Y :: "'a tuple set"
  assumes "\<not> b =simp=> B \<subseteq> A"
  shows "join {v. wf_tuple n A v \<and> P v} b {v. wf_tuple n B v \<and> Q v} =
    {v. wf_tuple n (A \<union> B) v \<and> P (restrict A v) \<and> (if b then Q (restrict B v) else \<not> Q (restrict B v))}"
  using assms
  by (intro set_eqI, subst join_restrict) (auto simp: wf_tuple_restrict_simple simp_implies_def)

lemma in_joinI: "table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not>b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> wf_tuple n (A \<union> B) v \<Longrightarrow>
  restrict A v \<in> X \<Longrightarrow> (b \<Longrightarrow> restrict B v \<in> Y) \<Longrightarrow> (\<not>b \<Longrightarrow> restrict B v \<notin> Y) \<Longrightarrow> v \<in> join X b Y"
  unfolding table_def
  by (subst join_restrict) (auto)

lemma in_joinE: "v \<in> join X b Y \<Longrightarrow> table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow>
  (wf_tuple n (A \<union> B) v \<Longrightarrow> restrict A v \<in> X \<Longrightarrow> if b then restrict B v \<in> Y else restrict B v \<notin> Y \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding table_def
  by (subst (asm) join_restrict) (auto)

definition qtable :: "nat \<Rightarrow> nat set \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow>
  'a table \<Rightarrow> bool" where
  "qtable n A P Q X \<longleftrightarrow> table n A X \<and> (\<forall>x. (x \<in> X \<and> P x \<longrightarrow> Q x) \<and> (wf_tuple n A x \<and> P x \<and> Q x \<longrightarrow> x \<in> X))"

abbreviation wf_table where
  "wf_table n A Q X \<equiv> qtable n A (\<lambda>_. True) Q X"

lemma wf_table_iff: "wf_table n A Q X \<longleftrightarrow> (\<forall>x. x \<in> X \<longleftrightarrow> (Q x \<and> wf_tuple n A x))"
  unfolding qtable_def table_def by auto

lemma table_wf_table: "table n A X = wf_table n A (\<lambda>v. v \<in> X) X"
  unfolding table_def wf_table_iff by auto

lemma qtableI: "table n A X \<Longrightarrow>
  (\<And>x. x \<in> X \<Longrightarrow> wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X) \<Longrightarrow>
  qtable n A P Q X"
  unfolding qtable_def table_def by auto

lemma in_qtableI: "qtable n A P Q X \<Longrightarrow> wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X"
  unfolding qtable_def by blast

lemma in_qtableE: "qtable n A P Q X \<Longrightarrow> x \<in> X \<Longrightarrow> P x \<Longrightarrow> (wf_tuple n A x \<Longrightarrow> Q x \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding qtable_def table_def by blast

lemma qtable_empty: "(\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> False) \<Longrightarrow> qtable n A P Q empty_table"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_empty_iff: "qtable n A P Q empty_table = (\<forall>x. wf_tuple n A x \<longrightarrow> P x \<longrightarrow> Q x \<longrightarrow> False)"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_unit_table: "(\<And>x. wf_tuple n {} x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> qtable n {} P Q (unit_table n)"
  unfolding qtable_def table_def in_unit_table by auto

lemma qtable_union: "qtable n A P Q1 X \<Longrightarrow> qtable n A P Q2 Y \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 x \<or> Q2 x) \<Longrightarrow> qtable n A P Q (X \<union> Y)"
  unfolding qtable_def table_def by blast

lemma qtable_Union: "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> qtable n A P (Qi i) (Xi i)) \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<exists>i \<in> I. Qi i x)) \<Longrightarrow> qtable n A P Q (\<Union>i \<in> I. Xi i)"
proof (induct I arbitrary: Q rule: finite_induct)
  case (insert i F)
  then show ?case
    by (auto intro!: qtable_union[where ?Q1.0 = "Qi i" and ?Q2.0 = "\<lambda>x. \<exists>i\<in>F. Qi i x"])
qed (auto intro!: qtable_empty[unfolded empty_table_def])

lemma qtable_join: 
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
  "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
  "\<And>x. b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> Q2 (restrict B x)"
  "\<And>x. \<not> b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> \<not> Q2 (restrict B x)"
  shows "qtable n C P Q (join X b Y)"
proof (rule qtableI)
  from assms(1-4) show "table n C (join X b Y)" 
    unfolding qtable_def by (auto simp: join_table)
next
  fix x assume "x \<in> join X b Y" "wf_tuple n C x" "P x"
  with assms(1-3) assms(5-7)[of x] show "Q x" unfolding qtable_def
    by (auto 0 2 simp: wf_tuple_restrict_simple elim!: in_joinE split: if_splits)
next
  fix x assume "wf_tuple n C x" "P x" "Q x"
  with assms(1-4) assms(5-7)[of x] show "x \<in> join X b Y" unfolding qtable_def
    by (auto dest: wf_tuple_restrict_simple intro!: in_joinI[of n A X B Y])
qed

lemma qtable_join_fixed: 
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
  "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
  shows "qtable n C P (\<lambda>x. Q1 (restrict A x) \<and> (if b then Q2 (restrict B x) else \<not> Q2 (restrict B x))) (join X b Y)"
  by (rule qtable_join[OF assms]) auto

lemma wf_tuple_cong:
  assumes "wf_tuple n A v" "wf_tuple n A w" "\<forall>x \<in> A. map the v ! x = map the w ! x"
  shows "v = w"
proof -
  from assms(1,2) have "length v = length w" unfolding wf_tuple_def by simp
  from this assms show "v = w"
  proof (induct v w arbitrary: n A rule: list_induct2)
    case (Cons x xs y ys)
    let ?n = "n - 1" and ?A = "(\<lambda>x. x - 1) ` (A - {0})"
    have *: "map the xs ! z = map the ys ! z" if "z \<in> ?A" for z
      using that Cons(5)[THEN bspec, of "Suc z"]
      by (cases z) (auto simp: le_Suc_eq split: if_splits)
    from Cons(1,3-5) show ?case
      by (auto intro!: Cons(2)[of ?n ?A] * split: if_splits)
  qed simp
qed

definition mem_restr :: "'a list set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "mem_restr A x \<longleftrightarrow> (\<exists>y\<in>A. list_all2 (\<lambda>a b. a \<noteq> None \<longrightarrow> a = Some b) x y)"

lemma mem_restrI: "y \<in> A \<Longrightarrow> length y = n \<Longrightarrow> wf_tuple n V x \<Longrightarrow> \<forall>i\<in>V. x ! i = Some (y ! i) \<Longrightarrow> mem_restr A x"
  unfolding mem_restr_def wf_tuple_def by (force simp add: list_all2_conv_all_nth)

lemma mem_restrE: "mem_restr A x \<Longrightarrow> wf_tuple n V x \<Longrightarrow> \<forall>i\<in>V. i < n \<Longrightarrow>
  (\<And>y. y \<in> A \<Longrightarrow> \<forall>i\<in>V. x ! i = Some (y ! i) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding mem_restr_def wf_tuple_def by (fastforce simp add: list_all2_conv_all_nth)

lemma mem_restr_IntD: "mem_restr (A \<inter> B) v \<Longrightarrow> mem_restr A v \<and> mem_restr B v"
  unfolding mem_restr_def by auto

lemma mem_restr_Un_iff: "mem_restr (A \<union> B) x \<longleftrightarrow> mem_restr A x \<or> mem_restr B x"
  unfolding mem_restr_def by blast

lemma mem_restr_UNIV [simp]: "mem_restr UNIV x"
  unfolding mem_restr_def
  by (auto simp add: list.rel_map intro!: exI[of _ "map the x"] list.rel_refl)

lemma restrict_mem_restr[simp]: "mem_restr A x \<Longrightarrow> mem_restr A (restrict V x)"
  unfolding mem_restr_def restrict_def
  by (auto simp: list_all2_conv_all_nth elim!: bexI[rotated])

definition lift_envs :: "'a list set \<Rightarrow> 'a list set" where
  "lift_envs R = (\<lambda>(a,b). a # b) ` (UNIV \<times> R)"

lemma lift_envs_mem_restr[simp]: "mem_restr A x \<Longrightarrow> mem_restr (lift_envs A) (a # x)"
  by (auto simp: mem_restr_def lift_envs_def)

lemma qtable_project:
  assumes "qtable (Suc n) A (mem_restr (lift_envs R)) P X"
  shows "qtable n ((\<lambda>x. x - Suc 0) ` (A - {0})) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> A then Some x else None) # v)) (tl ` X)"
      (is "qtable n ?A (mem_restr R) ?P ?X")
proof ((rule qtableI; (elim exE)?), goal_cases table left right)
  case table
  with assms show ?case
    unfolding qtable_def by (simp add: table_project) 
next
  case (left v)
  from assms have "[] \<notin> X"
    unfolding qtable_def table_def by fastforce
  with left(1) obtain x where "x # v \<in> X"
    by (metis (no_types, hide_lams) image_iff hd_Cons_tl)    
  with assms show ?case
    by (rule in_qtableE) (auto simp: left(3) split: if_splits)
next
  case (right v x)
  with assms have "(if 0 \<in> A then Some x else None) # v \<in> X"
    by (elim in_qtableI) auto
  then show ?case
    by (auto simp: image_iff elim: bexI[rotated])
qed

lemma qtable_cong: "qtable n A P Q X \<Longrightarrow> A = B \<Longrightarrow> (\<And>v. P v \<Longrightarrow> Q v \<longleftrightarrow> Q' v) \<Longrightarrow> qtable n B P Q' X"
  by (auto simp: qtable_def)

(*<*)
end
(*>*)
