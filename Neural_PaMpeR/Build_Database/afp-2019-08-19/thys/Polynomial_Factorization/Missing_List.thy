(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Missing List\<close>

text \<open>The provides some standard algorithms and lemmas on lists.\<close>
theory Missing_List
imports 
  Matrix.Utility
  "HOL-Library.Monad_Syntax"
begin

fun concat_lists :: "'a list list \<Rightarrow> 'a list list" where
  "concat_lists [] = [[]]"
| "concat_lists (as # xs) = concat (map (\<lambda>vec. map (\<lambda>a. a # vec) as) (concat_lists xs))"

lemma concat_lists_listset: "set (concat_lists xs) = listset (map set xs)" 
  by (induct xs, auto simp: set_Cons_def)

lemma sum_list_concat: "sum_list (concat ls) = sum_list (map sum_list ls)"
  by (induct ls, auto)


(* TODO: move to src/HOL/List *)
lemma listset: "listset xs = { ys. length ys = length xs \<and> (\<forall> i < length xs. ys ! i \<in> xs ! i)}"
proof (induct xs)
  case (Cons x xs)
  let ?n = "length xs" 
  from Cons 
  have "?case = (set_Cons x {ys. length ys = ?n \<and> (\<forall>i < ?n. ys ! i \<in> xs ! i)} =
    {ys. length ys = Suc ?n \<and> ys ! 0 \<in> x \<and> (\<forall>i < ?n. ys ! Suc i \<in> xs ! i)})" 
    (is "_ = (?L = ?R)")
    by (auto simp: all_Suc_conv)
  also have "?L = ?R"
    by (auto simp: set_Cons_def, case_tac xa, auto)
  finally show ?case by simp
qed auto

lemma set_concat_lists[simp]: "set (concat_lists xs) = {as. length as = length xs \<and> (\<forall>i<length xs. as ! i \<in> set (xs ! i))}"
  unfolding concat_lists_listset listset by simp

declare concat_lists.simps[simp del]

fun find_map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
  "find_map_filter f p [] = None"
| "find_map_filter f p (a # as) = (let b = f a in if p b then Some b else find_map_filter f p as)"

lemma find_map_filter_Some: "find_map_filter f p as = Some b \<Longrightarrow> p b \<and> b \<in> f ` set as"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma find_map_filter_None: "find_map_filter f p as = None \<Longrightarrow> \<forall> b \<in> f ` set as. \<not> p b"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma remdups_adj_sorted_distinct[simp]: "sorted xs \<Longrightarrow> distinct (remdups_adj xs)"
by (induct xs rule: remdups_adj.induct) (auto)

lemma subseqs_length_simple:
  assumes "b \<in> set (subseqs xs)" shows "length b \<le> length xs"
  using assms by(induct xs arbitrary:b;auto simp:Let_def Suc_leD)

lemma subseqs_length_simple_False:
  assumes "b \<in> set (subseqs xs)" " length xs < length b" shows False
  using assms subseqs_length_simple by fastforce

lemma empty_subseqs[simp]: "[] \<in> set (subseqs xs)" by (induct xs, auto simp: Let_def)

lemma full_list_subseqs: "{ys. ys \<in> set (subseqs xs) \<and> length ys = length xs} = {xs}" 
proof (induct xs)
  case (Cons x xs)
  have "?case = ({ys \<in> (#) x ` set (subseqs xs) \<union> set (subseqs xs). 
    length ys = Suc (length xs)} = (#) x ` {xs})" (is "_ = (?l = ?r)")
    by (auto simp: Let_def)
  also have "?l = {ys \<in> (#) x ` set (subseqs xs). length ys = Suc (length xs)}" 
    using length_subseqs[of xs]
    using subseqs_length_simple_False by force
  also have "\<dots> = (#) x ` {ys \<in> set (subseqs xs). length ys = length xs}"
    by auto
  also have "\<dots> = (#) x ` {xs}" unfolding Cons by auto
  finally show ?case by simp
qed simp

lemma nth_concat_split: assumes "i < length (concat xs)" 
  shows "\<exists> j k. j < length xs \<and> k < length (xs ! j) \<and> concat xs ! i = xs ! j ! k"
  using assms
proof (induct xs arbitrary: i)
  case (Cons x xs i)
  define I where "I = i - length x" 
  show ?case 
  proof (cases "i < length x")
    case True note l = this
    hence i: "concat (Cons x xs) ! i = x ! i" by (auto simp: nth_append)
    show ?thesis unfolding i
      by (rule exI[of _ 0], rule exI[of _ i], insert Cons l, auto)
  next
    case False note l = this
    from l Cons(2) have i: "i = length x + I" "I < length (concat xs)" unfolding I_def by auto
    hence iI: "concat (Cons x xs) ! i = concat xs ! I" by (auto simp: nth_append)
    from Cons(1)[OF i(2)] obtain j k where
      IH: "j < length xs \<and> k < length (xs ! j) \<and> concat xs ! I = xs ! j ! k" by auto
    show ?thesis unfolding iI
      by (rule exI[of _ "Suc j"], rule exI[of _ k], insert IH, auto)
  qed
qed simp

lemma nth_concat_diff: assumes "i1 < length (concat xs)" "i2 < length (concat xs)" "i1 \<noteq> i2"
  shows "\<exists> j1 k1 j2 k2. (j1,k1) \<noteq> (j2,k2) \<and> j1 < length xs \<and> j2 < length xs
    \<and> k1 < length (xs ! j1) \<and> k2 < length (xs ! j2) 
    \<and> concat xs ! i1 = xs ! j1 ! k1 \<and> concat xs ! i2 = xs ! j2 ! k2"
  using assms
proof (induct xs arbitrary: i1 i2)
  case (Cons x xs)
  define I1 where "I1 = i1 - length x" 
  define I2 where "I2 = i2 - length x" 
  show ?case 
  proof (cases "i1 < length x")
    case True note l1 = this
    hence i1: "concat (Cons x xs) ! i1 = x ! i1" by (auto simp: nth_append)
    show ?thesis
    proof (cases "i2 < length x")
      case True note l2 = this
      hence i2: "concat (Cons x xs) ! i2 = x ! i2" by (auto simp: nth_append)
      show ?thesis unfolding i1 i2 
        by (rule exI[of _ 0], rule exI[of _ i1], rule exI[of _ 0], rule exI[of _ i2], 
         insert Cons(4) l1 l2, auto)
    next
      case False note l2 = this
      from l2 Cons(3) have i22: "i2 = length x + I2" "I2 < length (concat xs)" unfolding I2_def by auto
      hence i2: "concat (Cons x xs) ! i2 = concat xs ! I2" by (auto simp: nth_append)
      from nth_concat_split[OF i22(2)] obtain j2 k2 where
        *: "j2 < length xs \<and> k2 < length (xs ! j2) \<and> concat xs ! I2 = xs ! j2 ! k2" by auto
      show ?thesis unfolding i1 i2
        by (rule exI[of _ 0], rule exI[of _ i1], rule exI[of _ "Suc j2"], rule exI[of _ k2],
         insert * l1, auto)
    qed
  next
    case False note l1 = this
    from l1 Cons(2) have i11: "i1 = length x + I1" "I1 < length (concat xs)" unfolding I1_def by auto
    hence i1: "concat (Cons x xs) ! i1 = concat xs ! I1" by (auto simp: nth_append)
    show ?thesis
    proof (cases "i2 < length x")
      case False note l2 = this
      from l2 Cons(3) have i22: "i2 = length x + I2" "I2 < length (concat xs)" unfolding I2_def by auto
      hence i2: "concat (Cons x xs) ! i2 = concat xs ! I2" by (auto simp: nth_append)
      from Cons(4) i11 i22 have diff: "I1 \<noteq> I2" by auto
      from Cons(1)[OF i11(2) i22(2) diff] obtain j1 k1 j2 k2
        where IH: "(j1,k1) \<noteq> (j2,k2) \<and> j1 < length xs \<and> j2 < length xs
        \<and> k1 < length (xs ! j1) \<and> k2 < length (xs ! j2) 
        \<and> concat xs ! I1 = xs ! j1 ! k1 \<and> concat xs ! I2 = xs ! j2 ! k2" by auto
      show ?thesis unfolding i1 i2 
        by (rule exI[of _ "Suc j1"], rule exI[of _ k1], rule exI[of _ "Suc j2"], rule exI[of _ k2],
        insert IH, auto)
    next
      case True note l2 = this
      hence i2: "concat (Cons x xs) ! i2 = x ! i2" by (auto simp: nth_append)
      from nth_concat_split[OF i11(2)] obtain j1 k1 where
        *: "j1 < length xs \<and> k1 < length (xs ! j1) \<and> concat xs ! I1 = xs ! j1 ! k1" by auto
      show ?thesis unfolding i1 i2
        by (rule exI[of _ "Suc j1"], rule exI[of _ k1], rule exI[of _ 0], rule exI[of _ i2],
         insert * l2, auto)
    qed
  qed      
qed auto

lemma list_all2_map_map: "(\<And> x. x \<in> set xs \<Longrightarrow> R (f x) (g x)) \<Longrightarrow> list_all2 R (map f xs) (map g xs)"
  by (induct xs, auto)

subsection \<open>Partitions\<close>
text \<open>Check whether a list of sets forms a partition, i.e.,
whether the sets are pairwise disjoint.\<close>
definition is_partition :: "('a set) list \<Rightarrow> bool" where
  "is_partition cs \<longleftrightarrow> (\<forall>j<length cs. \<forall>i<j. cs ! i \<inter> cs ! j = {})"

(* and an equivalent but more symmetric version *)
definition is_partition_alt :: "('a set) list \<Rightarrow> bool" where
  "is_partition_alt cs \<longleftrightarrow> (\<forall> i j. i < length cs \<and> j < length cs \<and> i \<noteq> j \<longrightarrow> cs!i \<inter> cs!j = {})"

lemma is_partition_alt: "is_partition = is_partition_alt"
proof (intro ext)
  fix cs :: "'a set list"
  {
    assume "is_partition_alt cs"
    hence "is_partition cs" unfolding is_partition_def is_partition_alt_def by auto
  }
  moreover
  {
    assume part: "is_partition cs"
    have "is_partition_alt cs" unfolding is_partition_alt_def
    proof (intro allI impI)
      fix i j
      assume "i < length cs \<and> j < length cs \<and> i \<noteq> j"
      with part show "cs ! i \<inter> cs ! j = {}"
        unfolding is_partition_def
        by (cases "i < j", simp, cases "j < i", force, simp)
    qed
  }
  ultimately
  show "is_partition cs = is_partition_alt cs" by auto
qed
      
lemma is_partition_Nil:
  "is_partition [] = True" unfolding is_partition_def by auto

lemma is_partition_Cons:
  "is_partition (x#xs) \<longleftrightarrow> is_partition xs \<and> x \<inter> \<Union>(set xs) = {}" (is "?l = ?r")
proof
  assume ?l
  have one: "is_partition xs"
  proof (unfold is_partition_def, intro allI impI)
    fix j i assume "j < length xs" and "i < j"
    hence "Suc j < length(x#xs)" and "Suc i < Suc j" by auto
    from \<open>?l\<close>[unfolded is_partition_def,THEN spec,THEN mp,THEN spec,THEN mp,OF this]
    have "(x#xs)!(Suc i) \<inter> (x#xs)!(Suc j) = {}" .
    thus "xs!i \<inter> xs!j = {}" by simp
  qed
  have two: "x \<inter> \<Union>(set xs) = {}"
  proof (rule ccontr)
    assume "x \<inter> \<Union>(set xs) \<noteq> {}"
    then obtain y where "y \<in> x" and "y \<in> \<Union>(set xs)" by auto
    then obtain z where "z \<in> set xs" and "y \<in> z" by auto
    then obtain i where "i < length xs" and "xs!i = z" using in_set_conv_nth[of z xs] by auto
    with \<open>y \<in> z\<close> have "y \<in> (x#xs)!Suc i" by auto
    moreover with \<open>y \<in> x\<close> have "y \<in> (x#xs)!0" by simp
    ultimately have "(x#xs)!0 \<inter> (x#xs)!Suc i \<noteq> {}" by auto
    moreover from \<open>i < length xs\<close> have "Suc i < length(x#xs)" by simp
    ultimately show False using \<open>?l\<close>[unfolded is_partition_def] by best
  qed
  from one two show ?r ..
next
  assume ?r
  show ?l
  proof (unfold is_partition_def, intro allI impI)
    fix j i
    assume j: "j < length (x # xs)"
    assume i: "i < j"
    from i obtain j' where j': "j = Suc j'" by (cases j, auto)
    with j have j'len: "j' < length xs" and j'elem: "(x # xs) ! j = xs ! j'" by auto
    show "(x # xs) ! i \<inter> (x # xs) ! j = {}"
    proof (cases i)
      case 0
      with j'elem have "(x # xs) ! i \<inter> (x # xs) ! j = x \<inter> xs ! j'" by auto
      also have "\<dots> \<subseteq> x \<inter> \<Union>(set xs)" using j'len by force
      finally show ?thesis using \<open>?r\<close> by auto
    next
      case (Suc i')
      with i j' have i'j': "i' < j'" by auto
      from Suc j' have "(x # xs) ! i \<inter> (x # xs) ! j = xs ! i' \<inter> xs ! j'" by auto
      with \<open>?r\<close> i'j' j'len show ?thesis unfolding is_partition_def by auto
    qed
  qed
qed

lemma is_partition_sublist:
  assumes "is_partition (us @ xs @ ys @ zs @ vs)" 
  shows "is_partition (xs @ zs)"
proof (rule ccontr)
  assume "\<not> is_partition (xs @ zs)"
  then obtain i j where j:"j < length (xs @ zs)" and i:"i < j" and *:"(xs @ zs) ! i \<inter> (xs @ zs) ! j \<noteq> {}" 
    unfolding is_partition_def by blast
  then show False
  proof (cases "j < length xs")
    case True
    let ?m = "j + length us"
    let ?n = "i + length us" 
    from True have "?m < length (us @ xs @ ys @ zs @ vs)" by auto
    moreover from i have "?n < ?m" by auto
    moreover have "(us @ xs @ ys @ zs @ vs) ! ?n \<inter> (us @ xs @ ys @ zs @ vs) ! ?m \<noteq> {}" 
      using i True * nth_append 
      by (metis (no_types, lifting) add_diff_cancel_right' not_add_less2 order.strict_trans)
    ultimately show False using assms unfolding is_partition_def by auto
  next
    case False
    let ?m = "j + length us + length ys"
    from j have m:"?m < length (us @ xs @ ys @ zs @ vs)" by auto
    have mj:"(us @ (xs @ ys @ zs @ vs)) ! ?m = (xs @ zs) ! j" unfolding nth_append using False j by auto
    show False
    proof (cases "i < length xs")
      case True
      let ?n = "i + length us"
      from i have "?n < ?m" by auto
      moreover have "(us @ xs @ ys @ zs @ vs) ! ?n = (xs @ zs) ! i" by (simp add: True nth_append) 
      ultimately show False using * m assms mj unfolding is_partition_def by blast
    next
      case False
      let ?n = "i + length us + length ys"
      from i have i:"?n < ?m" by auto
      moreover have "(us @ xs @ ys @ zs @ vs) ! ?n = (xs @ zs) ! i"
        unfolding nth_append using False i j less_diff_conv2 by auto
      ultimately show False using * m assms mj unfolding is_partition_def by blast
    qed
  qed
qed

lemma is_partition_inj_map:
  assumes "is_partition xs"
  and "inj_on f (\<Union>x \<in> set xs. x)"
  shows "is_partition (map ((`) f) xs)"
proof (rule ccontr)
  assume "\<not> is_partition (map ((`) f) xs)"
  then obtain i j where neq:"i \<noteq> j" 
    and i:"i < length (map ((`) f) xs)" and j:"j < length (map ((`) f) xs)"
    and "map ((`) f) xs ! i \<inter> map ((`) f) xs ! j \<noteq> {}" 
    unfolding is_partition_alt is_partition_alt_def by auto
  then obtain x where "x \<in> map ((`) f) xs ! i" and "x \<in> map ((`) f) xs ! j" by auto
  then obtain y z where yi:"y \<in> xs ! i" and yx:"f y = x" and zj:"z \<in> xs ! j" and zx:"f z = x" 
    using i j by auto
  show False
  proof (cases "y = z")
    case True
    with zj yi neq assms(1) i j show ?thesis by (auto simp: is_partition_alt is_partition_alt_def)
  next
    case False
    have "y \<in> (\<Union>x \<in> set xs. x)" using yi i by force
    moreover have "z \<in> (\<Union>x \<in> set xs. x)" using zj j by force
    ultimately show ?thesis using assms(2) inj_on_def[of f "(\<Union>x\<in>set xs. x)"] False zx yx by blast
  qed
qed

context
begin
private fun is_partition_impl :: "'a set list \<Rightarrow> 'a set option" where
  "is_partition_impl [] = Some {}"
| "is_partition_impl (as # rest) = do {
      all \<leftarrow> is_partition_impl rest;
      if as \<inter> all = {} then Some (all \<union> as) else None
    }" 

lemma is_partition_code[code]: "is_partition as = (is_partition_impl as \<noteq> None)" 
proof -
  note [simp] = is_partition_Cons is_partition_Nil
  have "\<And> bs. (is_partition as = (is_partition_impl as \<noteq> None)) \<and>
    (is_partition_impl as = Some bs \<longrightarrow> bs = \<Union> (set as))"
  proof (induct as)
    case (Cons as rest bs)
    show ?case
    proof (cases "is_partition rest")
      case False
      thus ?thesis using Cons by auto
    next
      case True
      with Cons obtain c where rest: "is_partition_impl rest = Some c" 
        by (cases "is_partition_impl rest", auto)
      with Cons True show ?thesis by auto
    qed
  qed auto
  thus ?thesis by blast
qed
end

lemma case_prod_partition:
  "case_prod f (partition p xs) = f (filter p xs) (filter (Not \<circ> p) xs)"
  by simp

lemmas map_id[simp] = list.map_id


subsection \<open>merging functions\<close>

definition fun_merge :: "('a \<Rightarrow> 'b)list \<Rightarrow> 'a set list \<Rightarrow> 'a \<Rightarrow> 'b"
  where "fun_merge fs as a \<equiv> (fs ! (LEAST i. i < length as \<and> a \<in> as ! i)) a"

lemma fun_merge: assumes 
      i: "i < length as"
  and a: "a \<in> as ! i"
  and ident: "\<And> i j a. i < length as \<Longrightarrow> j < length as \<Longrightarrow> a \<in> as ! i \<Longrightarrow> a \<in> as ! j \<Longrightarrow> (fs ! i) a = (fs ! j) a"
  shows "fun_merge fs as a = (fs ! i) a"
proof -
  let ?p = "\<lambda> i. i < length as \<and> a \<in> as ! i"
  let ?l = "LEAST i. ?p i"
  have p: "?p ?l"
    by (rule LeastI, insert i a, auto)
  show ?thesis unfolding fun_merge_def
    by (rule ident[OF _ i _ a], insert p, auto)
qed

lemma fun_merge_part: assumes 
      part: "is_partition as"
  and i: "i < length as"
  and a: "a \<in> as ! i"
  shows "fun_merge fs as a = (fs ! i) a"
proof(rule fun_merge[OF i a])
  fix i j a
  assume "i < length as" and "j < length as" and "a \<in> as ! i" and "a \<in> as ! j"
  hence "i = j" using part[unfolded is_partition_alt is_partition_alt_def] by (cases "i = j", auto)
  thus "(fs ! i) a = (fs ! j) a" by simp
qed


lemma map_nth_conv: "map f ss = map g ts \<Longrightarrow> \<forall>i < length ss. f(ss!i) = g(ts!i)"
proof (intro allI impI)
  fix i show "map f ss = map g ts \<Longrightarrow> i < length ss \<Longrightarrow> f(ss!i) = g(ts!i)"
  proof (induct ss arbitrary: i ts)
    case Nil thus ?case by (induct ts) auto
  next
    case (Cons s ss) thus ?case
      by (induct ts, simp, (cases i, auto))
  qed
qed

lemma distinct_take_drop:
  assumes dist: "distinct vs" and len: "i < length vs" shows "distinct(take i vs @ drop (Suc i) vs)" (is "distinct(?xs@?ys)")
proof -
  from id_take_nth_drop[OF len] have vs[symmetric]: "vs = ?xs @ vs!i # ?ys" .
  with dist have "distinct ?xs" and "distinct(vs!i#?ys)" and "set ?xs \<inter> set(vs!i#?ys) = {}" using distinct_append[of ?xs "vs!i#?ys"] by auto
  hence "distinct ?ys" and "set ?xs \<inter> set ?ys = {}" by auto
  with \<open>distinct ?xs\<close> show ?thesis using distinct_append[of ?xs ?ys] vs by simp
qed

lemma map_nth_eq_conv:
  assumes len: "length xs = length ys"
  shows "(map f xs = ys) = (\<forall>i<length ys. f (xs ! i) = ys ! i)" (is "?l = ?r")
proof -
  have "(map f xs = ys) = (map f xs = map id ys)" by auto
  also have "... = (\<forall> i < length ys. f (xs ! i) = id (ys ! i))" 
    using map_nth_conv[of f xs id ys] nth_map_conv[OF len, of f id] unfolding len
    by blast
  finally  show ?thesis by auto
qed

lemma map_upt_len_conv: 
  "map (\<lambda> i . f (xs!i)) [0..<length xs] = map f xs"
  by (rule nth_equalityI, auto)

lemma map_upt_add':
  "map f [a..<a+b] = map (\<lambda> i. f (a + i)) [0..<b]"
  by (induct b, auto)


definition generate_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where "generate_lists n xs \<equiv> concat_lists (map (\<lambda> _. xs) [0 ..< n])"

lemma set_generate_lists[simp]: "set (generate_lists n xs) = {as. length as = n \<and> set as \<subseteq> set xs}"
proof -
  {
    fix as
    have "(length as = n \<and> (\<forall>i<n. as ! i \<in> set xs)) = (length as = n \<and> set as \<subseteq> set xs)"
    proof -
      {
        assume "length as = n"
        hence n: "n = length as" by auto
        have "(\<forall>i<n. as ! i \<in> set xs) = (set as \<subseteq> set xs)" unfolding n
          unfolding all_set_conv_all_nth[of as "\<lambda> x. x \<in> set xs", symmetric] by auto
      }
      thus ?thesis by auto
    qed
  }
  thus ?thesis unfolding generate_lists_def unfolding set_concat_lists by auto
qed

lemma nth_append_take:
  assumes "i \<le> length xs" shows "(take i xs @ y#ys)!i = y"
proof -
  from assms have a: "length(take i xs) = i" by simp
  have "(take i xs @ y#ys)!(length(take i xs)) = y" by (rule nth_append_length)
  thus ?thesis unfolding a .
qed

lemma nth_append_take_is_nth_conv:
  assumes "i < j" and "j \<le> length xs" shows "(take j xs @ ys)!i = xs!i"
proof -
  from assms have "i < length(take j xs)" by simp
  hence "(take j xs @ ys)!i = take j xs ! i" unfolding nth_append by simp
  thus ?thesis unfolding nth_take[OF assms(1)] .
qed

lemma nth_append_drop_is_nth_conv:
  assumes "j < i" and "j \<le> length xs" and "i \<le> length xs"
  shows "(take j xs @ y # drop (Suc j) xs)!i = xs!i"
proof -
  from \<open>j < i\<close> obtain n where ij: "Suc(j + n) = i" using less_imp_Suc_add by auto
  with assms have i: "i = length(take j xs) + Suc n" by auto
  have len: "Suc j + n \<le> length xs" using assms i by auto
  have "(take j xs @ y # drop (Suc j) xs)!i =
    (y # drop (Suc j) xs)!(i - length(take j xs))" unfolding nth_append i by auto
  also have "\<dots> = (y # drop (Suc j) xs)!(Suc n)" unfolding i by simp
  also have "\<dots> = (drop (Suc j) xs)!n" by simp
  finally show ?thesis using ij len by simp
qed

lemma nth_append_take_drop_is_nth_conv: 
 assumes "i \<le> length xs" and "j \<le> length xs" and "i \<noteq> j" 
 shows "(take j xs @ y # drop (Suc j) xs)!i = xs!i"
proof -
 from assms have "i < j \<or> i > j" by auto
 thus ?thesis using assms 
   by (auto simp: nth_append_take_is_nth_conv nth_append_drop_is_nth_conv)
qed
  
lemma take_drop_imp_nth: "\<lbrakk>take i ss @ x # drop (Suc i) ss = ss\<rbrakk> \<Longrightarrow> x = ss!i"
proof (induct ss arbitrary: i)
 case (Cons s ss)
 from \<open>take i (s#ss) @ x # drop (Suc i) (s#ss) = (s#ss)\<close> show ?case
 proof (induct i)
  case (Suc i)
  from Cons have IH: "take i ss @ x # drop (Suc i) ss = ss \<Longrightarrow> x = ss!i" by auto
  from Suc have "take i ss @ x # drop (Suc i) ss = ss" by auto
  with IH show ?case by auto
 qed auto
qed auto

lemma take_drop_update_first: assumes "j < length ds" and "length cs = length ds"
  shows "(take j ds @ drop j cs)[j := ds ! j] = take (Suc j) ds @ drop (Suc j) cs" 
using assms
proof (induct j arbitrary: ds cs)
  case 0
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  show ?case unfolding ds cs by auto
next
  case (Suc j)
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  from Suc(1)[of dds ccs] Suc(2) Suc(3) show ?case unfolding ds cs by auto
qed

lemma take_drop_update_second: assumes "j < length ds" and "length cs = length ds"
  shows "(take j ds @ drop j cs)[j := cs ! j] = take j ds @ drop j cs"
using assms
proof (induct j arbitrary: ds cs)
  case 0
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  show ?case unfolding ds cs by auto
next
  case (Suc j)
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  from Suc(1)[of dds ccs] Suc(2) Suc(3) show ?case unfolding ds cs by auto
qed


lemma nth_take_prefix:
 "length ys \<le> length xs \<Longrightarrow> \<forall>i < length ys. xs!i = ys!i \<Longrightarrow> take (length ys) xs = ys"
proof (induct xs ys rule: list_induct2')
  case (4 x xs y ys)
  have "take (length ys) xs = ys"
    by (rule 4(1), insert 4(2-3), auto)
  moreover from 4(3) have "x = y" by auto
  ultimately show ?case by auto
qed auto


lemma take_upt_idx:
  assumes i: "i < length ls"
  shows "take i ls = [ ls ! j . j \<leftarrow> [0..<i]]" 
proof -
  have e: "0 + i \<le> i" by auto
  show ?thesis 
    using take_upt[OF e] take_map map_nth
    by (metis (hide_lams, no_types) add.left_neutral i nat_less_le take_upt)
qed


fun distinct_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "distinct_eq _ [] = True"
| "distinct_eq eq (x # xs) = ((\<forall> y \<in> set xs. \<not> (eq y x)) \<and> distinct_eq eq xs)"

lemma distinct_eq_append: "distinct_eq eq (xs @ ys) = (distinct_eq eq xs \<and> distinct_eq eq ys \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set ys. \<not> (eq y x)))"
  by (induct xs, auto)

lemma append_Cons_nth_left:
  assumes "i < length xs"
  shows "(xs @ u # ys) ! i = xs ! i"
  using assms nth_append[of xs _ i] by simp

lemma append_Cons_nth_middle:
  assumes "i = length xs"
  shows "(xs @ y # zs) ! i = y"
using assms by auto

lemma append_Cons_nth_right:
  assumes "i > length xs"
  shows "(xs @ u # ys) ! i = (xs @ z # ys) ! i"
proof -
  from assms have "i - length xs > 0" by auto
  then obtain j where j: "i - length xs = Suc j" by (cases "i - length xs", auto)
  thus ?thesis by (simp add: nth_append)
qed

lemma append_Cons_nth_not_middle:
  assumes "i \<noteq> length xs"
  shows "(xs @ u # ys) ! i = (xs @ z # ys) ! i"
proof (cases "i < length xs")
  case True
  thus ?thesis by (simp add: append_Cons_nth_left)
next
  case False 
  with assms have "i > length xs" by arith
  thus ?thesis by (rule append_Cons_nth_right)
qed

lemmas append_Cons_nth = append_Cons_nth_middle append_Cons_nth_not_middle

lemma concat_all_nth:
  assumes "length xs = length ys"
    and "\<And>i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)"
    and "\<And>i j. i < length xs \<Longrightarrow> j < length (xs ! i) \<Longrightarrow> P (xs ! i ! j) (ys ! i ! j)"
  shows "\<forall>k<length (concat xs). P (concat xs ! k) (concat ys ! k)" 
  using assms
proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)
  from Cons(3)[of 0] have xy: "length x = length y" by simp
  from Cons(4)[of 0] xy have pxy: "\<And> j. j < length x \<Longrightarrow> P (x ! j) (y ! j)" by auto
  {
    fix i
    assume i: "i < length xs"
    with Cons(3)[of "Suc i"] 
    have len: "length (xs ! i) = length (ys ! i)" by simp
    from Cons(4)[of "Suc i"] i have "\<And> j. j < length (xs ! i) \<Longrightarrow> P (xs ! i ! j) (ys ! i ! j)"
      by auto
    note len and this
  } 
  from Cons(2)[OF this] have ind: "\<And> k. k < length (concat xs) \<Longrightarrow> P (concat xs ! k) (concat ys ! k)" 
    by auto
  show ?case unfolding concat.simps
  proof (intro allI impI) 
    fix k
    assume k: "k < length (x @ concat xs)"
    show "P ((x @ concat xs) ! k) ((y @ concat ys) ! k)"
    proof (cases "k < length x")
      case True
      show ?thesis unfolding nth_append using True xy pxy[OF True]
        by simp
    next
      case False
      with k have "k - (length x) < length (concat xs)" by auto
      then obtain n where n: "k - length x = n" and nxs: "n < length (concat xs)" by auto
      show ?thesis unfolding nth_append n n[unfolded xy] using False xy ind[OF nxs]
        by auto
    qed
  qed
qed auto

lemma eq_length_concat_nth:
  assumes "length xs = length ys"
    and "\<And>i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)"
  shows "length (concat xs) = length (concat ys)"
using assms
proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)
  from Cons(3)[of 0] have xy: "length x = length y" by simp
  {
    fix i
    assume "i < length xs"
    with Cons(3)[of "Suc i"] 
    have "length (xs ! i) = length (ys ! i)" by simp
  } 
  from Cons(2)[OF this] have ind: "length (concat xs) = length (concat ys)" by simp
  show ?case using xy ind by auto
qed auto

primrec
  list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_union [] ys = ys"
| "list_union (x # xs) ys = (let zs = list_union xs ys in if x \<in> set zs then zs else x # zs)"

lemma set_list_union[simp]: "set (list_union xs ys) = set xs \<union> set ys"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases "x \<in> set (list_union xs ys)") (auto)
qed simp

declare list_union.simps[simp del]

(*Why was list_inter thrown out of List.thy?*)
fun list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_inter [] bs = []"
| "list_inter (a#as) bs =
    (if a \<in> set bs then a # list_inter as bs else list_inter as bs)"

lemma set_list_inter[simp]:
  "set (list_inter xs ys) = set xs \<inter> set ys"
  by (induct rule: list_inter.induct) simp_all

declare list_inter.simps[simp del]

primrec list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_diff [] ys = []"
| "list_diff (x # xs) ys = (let zs = list_diff xs ys in if x \<in> set ys then zs else x # zs)"

lemma set_list_diff[simp]:
  "set (list_diff xs ys) = set xs - set ys"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases "x \<in> set ys") (auto)
qed simp

declare list_diff.simps[simp del]

lemma nth_drop_0: "0 < length ss \<Longrightarrow> (ss!0)#drop (Suc 0) ss = ss" by (induct ss) auto


lemma set_foldr_remdups_set_map_conv[simp]:
  "set (foldr (\<lambda>x xs. remdups (f x @ xs)) xs []) = \<Union>(set (map (set \<circ> f) xs))"
  by (induct xs) auto


lemma subset_set_code[code_unfold]: "set xs \<subseteq> set ys \<longleftrightarrow> list_all (\<lambda>x. x \<in> set ys) xs"
  unfolding list_all_iff by auto

fun union_list_sorted where
  "union_list_sorted (x # xs) (y # ys) = 
   (if x = y then x # union_list_sorted xs ys 
    else if x < y then x # union_list_sorted xs (y # ys)
    else y # union_list_sorted (x # xs) ys)"
| "union_list_sorted [] ys = ys"
| "union_list_sorted xs [] = xs"

lemma [simp]: "set (union_list_sorted xs ys) = set xs \<union> set ys"
  by (induct xs ys rule: union_list_sorted.induct, auto)

fun subtract_list_sorted :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "subtract_list_sorted (x # xs) (y # ys) = 
   (if x = y then subtract_list_sorted xs (y # ys) 
    else if x < y then x # subtract_list_sorted xs (y # ys)
    else subtract_list_sorted (x # xs) ys)"
| "subtract_list_sorted [] ys = []"
| "subtract_list_sorted xs [] = xs"

lemma set_subtract_list_sorted[simp]: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow>
  set (subtract_list_sorted xs ys) = set xs - set ys"
proof (induct xs ys rule: subtract_list_sorted.induct)
  case (1 x xs y ys)
  have xxs: "sorted (x # xs)" by fact 
  have yys: "sorted (y # ys)" by fact
  have xs: "sorted xs" using xxs by (simp)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis using 1(1)[OF True xs yys] by auto
  next 
    case False note neq = this
    note IH = 1(2-3)[OF this]
    show ?thesis 
      by (cases "x < y", insert IH xxs yys False, auto)
  qed
qed auto  

lemma subset_subtract_listed_sorted: "set (subtract_list_sorted xs ys) \<subseteq> set xs"
  by (induct xs ys rule: subtract_list_sorted.induct, auto)

lemma set_subtract_list_distinct[simp]: "distinct xs \<Longrightarrow> distinct (subtract_list_sorted xs ys)"
  by (induct xs ys rule: subtract_list_sorted.induct, insert subset_subtract_listed_sorted, auto)

definition "remdups_sort xs = remdups_adj (sort xs)"

lemma remdups_sort[simp]: "sorted (remdups_sort xs)" "set (remdups_sort xs) = set xs"
  "distinct (remdups_sort xs)"
  by (simp_all add: remdups_sort_def)

text \<open>maximum and minimum\<close>
lemma max_list_mono: assumes "\<And> x. x \<in> set xs - set ys \<Longrightarrow> \<exists> y. y \<in> set ys \<and> x \<le> y"
  shows "max_list xs \<le> max_list ys"
  using assms
proof (induct xs)
  case (Cons x xs)
  have "x \<le> max_list ys"
  proof (cases "x \<in> set ys")
    case True
    from max_list[OF this] show ?thesis .
  next
    case False
    with Cons(2)[of x] obtain y where y: "y \<in> set ys"
      and xy: "x \<le> y" by auto
    from xy max_list[OF y] show ?thesis by arith
  qed
  moreover have "max_list xs \<le> max_list ys"
    by (rule Cons(1)[OF Cons(2)], auto)
  ultimately show ?case by auto
qed auto

fun min_list :: "('a :: linorder) list \<Rightarrow> 'a" where
  "min_list [x] = x"
| "min_list (x # xs) = min x (min_list xs)"

lemma min_list: "(x :: 'a :: linorder) \<in> set xs \<Longrightarrow> min_list xs \<le> x"
proof (induct xs)
  case oCons : (Cons y ys) 
  show ?case
  proof (cases ys)
    case Nil
    thus ?thesis using oCons by auto
  next
    case (Cons z zs)
    hence id: "min_list (y # ys) = min y (min_list ys)" 
      by auto
    show ?thesis 
    proof (cases "x = y")
      case True
      show ?thesis unfolding id True by auto
    next
      case False
      have "min y (min_list ys) \<le> min_list ys" by auto
      also have "... \<le> x" using oCons False by auto
      finally show ?thesis unfolding id .
    qed
  qed
qed simp

lemma min_list_Cons:
  assumes xy: "x \<le> y"
    and len: "length xs = length ys"
    and xsys: "min_list xs \<le> min_list ys"
  shows "min_list (x # xs) \<le> min_list (y # ys)"
proof (cases xs)
  case Nil
  with len have ys: "ys = []" by simp
  with xy Nil show ?thesis by simp
next
  case (Cons x' xs')
  with len obtain y' ys' where ys: "ys = y' # ys'" by (cases ys, auto)
  from Cons have one: "min_list (x # xs) = min x (min_list xs)" by auto
  from ys have two: "min_list (y # ys) = min y (min_list ys)" by auto
  show ?thesis unfolding one two using xy xsys 
    unfolding  min_def by auto
qed

lemma min_list_nth:
  assumes "length xs = length ys"
    and "\<And>i. i < length ys \<Longrightarrow> xs ! i \<le> ys ! i"
  shows "min_list xs \<le> min_list ys"
using assms
proof (induct xs arbitrary: ys)
  case (Cons x xs zs)
  from Cons(2) obtain y ys where zs: "zs = y # ys" by (cases zs, auto)
  note Cons = Cons[unfolded zs]
  from Cons(2) have len: "length xs = length ys" by simp
  from Cons(3)[of 0] have xy: "x \<le> y" by simp
  {
    fix i
    assume "i < length xs"
    with Cons(3)[of "Suc i"] Cons(2)
    have "xs ! i \<le> ys ! i" by simp
  } 
  from Cons(1)[OF len this] Cons(2) have ind: "min_list xs \<le> min_list ys" by simp
  show ?case unfolding zs
    by (rule min_list_Cons[OF xy len ind])
qed auto

lemma min_list_ex:
  assumes "xs \<noteq> []" shows "\<exists>x\<in>set xs. min_list xs = x"
  using assms
proof (induct xs)
  case oCons : (Cons x xs) 
  show ?case
  proof (cases xs)
    case (Cons y ys)
    hence id: "min_list (x # xs) = min x (min_list xs)" and nNil: "xs \<noteq> []" by auto
    show ?thesis
    proof (cases "x \<le> min_list xs")
      case True
      show ?thesis unfolding id 
        by (rule bexI[of _ x], insert True, auto simp: min_def)
    next
      case False
      show ?thesis unfolding id min_def
        using oCons(1)[OF nNil] False by auto
    qed
  qed auto
qed auto

lemma min_list_subset:
  assumes subset: "set ys \<subseteq> set xs" and mem: "min_list xs \<in> set ys"
  shows "min_list xs = min_list ys"
proof -
  from subset mem have "xs \<noteq> []" by auto
  from min_list_ex[OF this] obtain x where x: "x \<in> set xs" and mx: "min_list xs = x" by auto
  from min_list[OF mem] have two: "min_list ys \<le> min_list xs" by auto
  from mem have "ys \<noteq> []" by auto
  from min_list_ex[OF this] obtain y where y: "y \<in> set ys" and my: "min_list ys = y" by auto
  from y subset have "y \<in> set xs" by auto
  from min_list[OF this] have one: "min_list xs \<le> y" by auto
  from one two 
  show ?thesis unfolding mx my by auto
qed

text\<open>Apply a permutation to a list.\<close>

primrec permut_aux :: "'a list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "permut_aux [] _ _ = []" |
  "permut_aux (a # as) f bs = (bs ! f 0) # (permut_aux as (\<lambda>n. f (Suc n)) bs)"

definition permut :: "'a list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a list" where
  "permut as f = permut_aux as f as"
declare permut_def[simp]

lemma permut_aux_sound:
  assumes "i < length as"
  shows "permut_aux as f bs ! i = bs ! (f i)"
using assms proof (induct as arbitrary: i f bs)
  case (Cons x xs)
  show ?case 
  proof (cases i)
    case (Suc j)
    with Cons(2) have "j < length xs" by simp
    from Cons(1)[OF this] and Suc show ?thesis by simp
  qed simp
qed simp

lemma permut_sound:
  assumes "i < length as"
  shows "permut as f ! i = as ! (f i)"
using assms and permut_aux_sound by simp

lemma permut_aux_length:
  assumes "bij_betw f {..<length as} {..<length bs}"
  shows "length (permut_aux as f bs) = length as"
by (induct as arbitrary: f bs, simp_all)

lemma permut_length:
  assumes "bij_betw f {..< length as} {..< length as}"
  shows "length (permut as f) = length as"
  using permut_aux_length[OF assms] by simp
 
declare permut_def[simp del]

lemma foldl_assoc:
  fixes b :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 55)
  assumes "\<And>f g h. f \<cdot> (g \<cdot> h) = f \<cdot> g \<cdot> h"
  shows "foldl (\<cdot>) (x \<cdot> y) zs = x \<cdot> foldl (\<cdot>) y zs"
  using assms[symmetric] by (induct zs arbitrary: y) simp_all

lemma foldr_assoc:
  assumes "\<And>f g h. b (b f g) h = b f (b g h)"
  shows "foldr b xs (b y z) = b (foldr b xs y) z"
  using assms by (induct xs) simp_all

lemma foldl_foldr_o_id:
  "foldl (\<circ>) id fs = foldr (\<circ>) fs id"
proof (induct fs)
  case (Cons f fs)
  have "id \<circ> f = f \<circ> id" by simp
  with Cons [symmetric] show ?case
    by (simp only: foldl_Cons foldr_Cons o_apply [of _ _ id] foldl_assoc o_assoc)
qed simp

lemma foldr_o_o_id[simp]:
  "foldr ((\<circ>) \<circ> f) xs id a = foldr f xs a"
  by (induct xs) simp_all

lemma Ex_list_of_length_P:
  assumes "\<forall>i<n. \<exists>x. P x i"
  shows "\<exists>xs. length xs = n \<and> (\<forall>i<n. P (xs ! i) i)"
proof -
  from assms have "\<forall> i. \<exists> x. i < n \<longrightarrow> P x i" by simp
  from choice[OF this] obtain xs where xs: "\<And> i. i < n \<Longrightarrow> P (xs i) i" by auto
  show ?thesis
    by (rule exI[of _ "map xs [0 ..< n]"], insert xs, auto)
qed

lemma ex_set_conv_ex_nth: "(\<exists>x\<in>set xs. P x) = (\<exists>i<length xs. P (xs ! i))"
  using in_set_conv_nth[of _ xs] by force

lemma map_eq_set_zipD [dest]:
  assumes "map f xs = map f ys"
    and "(x, y) \<in> set (zip xs ys)"
  shows "f x = f y"
using assms
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  then show ?case by (cases ys) auto
qed simp

fun span :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "span P (x # xs) =
    (if P x then let (ys, zs) = span P xs in (x # ys, zs)
    else ([], x # xs))" |
  "span _ [] = ([], [])"

lemma span[simp]: "span P xs = (takeWhile P xs, dropWhile P xs)"
  by (induct xs, auto)

declare span.simps[simp del]

lemma parallel_list_update: assumes 
  one_update: "\<And> xs i y. length xs = n \<Longrightarrow> i < n \<Longrightarrow> r (xs ! i) y \<Longrightarrow> p xs \<Longrightarrow> p (xs[i := y])"
  and init: "length xs = n" "p xs"
  and rel: "length ys = n" "\<And> i. i < n \<Longrightarrow> r (xs ! i) (ys ! i)"
  shows "p ys"
proof -
  note len = rel(1) init(1)
  {
    fix i
    assume "i \<le> n"
    hence "p (take i ys @ drop i xs)"
    proof (induct i)
      case 0 with init show ?case by simp
    next
      case (Suc i)
      hence IH: "p (take i ys @ drop i xs)" by simp
      from Suc have i: "i < n" by simp
      let ?xs = "(take i ys @ drop i xs)"
      have "length ?xs = n" using i len by simp
      from one_update[OF this i _ IH, of "ys ! i"] rel(2)[OF i] i len
      show ?case by (simp add: nth_append take_drop_update_first)
    qed
  }
  from this[of n] show ?thesis using len by auto
qed

lemma nth_concat_two_lists: 
  "i < length (concat (xs :: 'a list list)) \<Longrightarrow> length (ys :: 'b list list) = length xs 
  \<Longrightarrow> (\<And> i. i < length xs \<Longrightarrow> length (ys ! i) = length (xs ! i))
  \<Longrightarrow> \<exists> j k. j < length xs \<and> k < length (xs ! j) \<and> (concat xs) ! i = xs ! j ! k \<and>
     (concat ys) ! i = ys ! j ! k"
proof (induct xs arbitrary: i ys)
  case (Cons x xs i yys)
  then obtain y ys where yys: "yys = y # ys" by (cases yys, auto)
  note Cons = Cons[unfolded yys]
  from Cons(4)[of 0] have [simp]: "length y = length x" by simp
  show ?case
  proof (cases "i < length x")
    case True
    show ?thesis unfolding yys
      by (rule exI[of _ 0], rule exI[of _ i], insert True Cons(2-4), auto simp: nth_append)
  next
    case False
    let ?i = "i - length x"
    from False Cons(2-3) have "?i < length (concat xs)" "length ys = length xs" by auto
    note IH = Cons(1)[OF this]
    {
      fix i
      assume "i < length xs"
      with Cons(4)[of "Suc i"] have "length (ys ! i) = length (xs ! i)" by simp
    }
    from IH[OF this]
    obtain j k where IH1: "j < length xs" "k < length (xs ! j)" 
      "concat xs ! ?i = xs ! j ! k"
      "concat ys ! ?i = ys ! j ! k" by auto
    show ?thesis unfolding yys
      by (rule exI[of _ "Suc j"], rule exI[of _ k], insert IH1 False, auto simp: nth_append)
  qed
qed simp

text \<open>Removing duplicates w.r.t. some function.\<close>
fun remdups_gen :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_gen f [] = []"
| "remdups_gen f (x # xs) = x # remdups_gen f [y <- xs. \<not> f x = f y]"

lemma remdups_gen_subset: "set (remdups_gen f xs) \<subseteq> set xs"
  by (induct f xs rule: remdups_gen.induct, auto)

lemma remdups_gen_elem_imp_elem: "x \<in> set (remdups_gen f xs) \<Longrightarrow> x \<in> set xs"
  using remdups_gen_subset[of f xs] by blast

lemma elem_imp_remdups_gen_elem: "x \<in> set xs \<Longrightarrow> \<exists> y \<in> set (remdups_gen f xs). f x = f y"
proof (induct f xs rule: remdups_gen.induct)
  case (2 f z zs)
  show ?case
  proof (cases "f x = f z")
    case False
    with 2(2) have "x \<in> set [y\<leftarrow>zs . f z \<noteq> f y]" by auto
    from 2(1)[OF this] show ?thesis by auto
  qed auto
qed auto


lemma take_nth_drop_concat:
  assumes "i < length xss" and "xss ! i = ys"
    and "j < length ys" and "ys ! j = z"
  shows "\<exists>k < length (concat xss).
    take k (concat xss) = concat (take i xss) @ take j ys \<and>
    concat xss ! k = xss ! i ! j \<and>
    drop (Suc k) (concat xss) = drop (Suc j) ys @ concat (drop (Suc i) xss)"
using assms(1, 2)
proof (induct xss arbitrary: i rule: List.rev_induct)
  case (snoc xs xss)
  then show ?case using assms by (cases "i < length xss") (auto simp: nth_append)
qed simp

lemma concat_map_empty [simp]:
  "concat (map (\<lambda>_. []) xs) = []"
  by simp

lemma map_upt_len_same_len_conv:
  assumes "length xs = length ys"
  shows "map (\<lambda>i. f (xs ! i)) [0 ..< length ys] = map f xs"
  unfolding assms [symmetric] by (rule map_upt_len_conv)

lemma concat_map_concat [simp]:
  "concat (map concat xs) = concat (concat xs)"
  by (induct xs) simp_all

lemma concat_concat_map:
  "concat (concat (map f xs)) = concat (map (concat \<circ> f) xs)"
  by (induct xs) simp_all

lemma UN_upt_len_conv [simp]:
  "length xs = n \<Longrightarrow> (\<Union>i \<in> {0 ..< n}. f (xs ! i)) = \<Union>(set (map f xs))"
  by (force simp: in_set_conv_nth)

lemma Ball_at_Least0LessThan_conv [simp]:
  "length xs = n \<Longrightarrow>
    (\<forall>i \<in> {0 ..< n}. P (xs ! i)) \<longleftrightarrow> (\<forall>x \<in> set xs. P x)"
  by (metis atLeast0LessThan in_set_conv_nth lessThan_iff)

lemma sum_list_replicate_length [simp]:
  "sum_list (replicate (length xs) (Suc 0)) = length xs"
  by (induct xs) simp_all

lemma list_all2_in_set2:
  assumes "list_all2 P xs ys" and "y \<in> set ys"
  obtains x where "x \<in> set xs" and "P x y"
  using assms by (induct) auto

lemma map_eq_conv':
  "map f xs = map g ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i < length xs. f (xs ! i) = g (ys ! i))"
by (auto dest: map_eq_imp_length_eq map_nth_conv simp: nth_map_conv)


lemma list_3_cases[case_names Nil 1 2]:
  assumes "xs = [] \<Longrightarrow> P"
      and "\<And>x. xs = [x] \<Longrightarrow> P"
      and "\<And>x y ys. xs = x#y#ys \<Longrightarrow> P"
  shows P
  using assms by (cases xs; cases "tl xs", auto)

lemma list_4_cases[case_names Nil 1 2 3]:
  assumes "xs = [] \<Longrightarrow> P"
      and "\<And>x. xs = [x] \<Longrightarrow> P"
      and "\<And>x y. xs = [x,y] \<Longrightarrow> P"
      and "\<And>x y z zs. xs = x # y # z # zs \<Longrightarrow> P"
  shows P
  using assms by (cases xs; cases "tl xs"; cases "tl (tl xs)", auto)

lemma foldr_append2 [simp]:
  "foldr ((@) \<circ> f) xs (ys @ zs) = foldr ((@) \<circ> f) xs ys @ zs"
  by (induct xs) simp_all

lemma foldr_append2_Nil [simp]:
  "foldr ((@) \<circ> f) xs [] @ zs = foldr ((@) \<circ> f) xs zs"
  unfolding foldr_append2 [symmetric] by simp

lemma UNION_set_zip:
  "(\<Union>x \<in> set (zip [0..<length xs] (map f xs)). g x) = (\<Union>i < length xs. g (i, f (xs ! i)))"
by (auto simp: set_conv_nth)

lemma zip_fst: "p \<in> set (zip as bs) \<Longrightarrow> fst p \<in> set as"
  by (cases p, rule set_zip_leftD, simp)

lemma zip_snd: "p \<in> set (zip as bs) \<Longrightarrow> snd p \<in> set bs"
  by (cases p, rule set_zip_rightD, simp)

lemma zip_size_aux: "size_list (size o snd) (zip ts ls) \<le> (size_list size ls)"
proof (induct ls arbitrary: ts)
  case (Cons l ls ts)
  thus ?case by (cases ts, auto)
qed auto

text\<open>We definie the function that remove the nth element of
a list. It uses take and drop and the soundness is therefore not
too hard to prove thanks to the already existing lemmas.\<close>

definition remove_nth :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_nth n xs \<equiv> (take n xs) @ (drop (Suc n) xs)"

declare remove_nth_def[simp]

lemma remove_nth_len:
  assumes i: "i < length xs"
  shows "length xs = Suc (length (remove_nth i xs))"
proof -
  show ?thesis unfolding arg_cong[where f = "length", OF id_take_nth_drop[OF i]]
    unfolding remove_nth_def by simp
qed

lemma remove_nth_length :
  assumes n_bd: "n < length xs"
  shows "length (remove_nth n xs) = length xs - 1"
proof-
 from length_take have ll:"n < length xs \<longrightarrow> length (take n xs) = n" by auto
 from length_drop have lr: "length (drop (Suc n) xs) = length xs - (Suc n)" by simp
 from ll and lr and length_append and n_bd show ?thesis by auto
qed

lemma remove_nth_id : "length xs \<le> n \<Longrightarrow> remove_nth n xs = xs"
using take_all drop_all append_Nil2 by simp

lemma remove_nth_sound_l :
  assumes p_ub: "p < n"
  shows "(remove_nth n xs) ! p = xs ! p"
proof (cases "n < length xs")
 case True  
  from length_take and True have ltk: "length (take n xs) = n" by simp
   {
     assume pltn: "p < n"
     from this and ltk have plttk: "p < length (take n xs)" by simp
     with nth_append[of "take n xs" _ p]
     have "((take n xs) @ (drop (Suc n) xs)) ! p = take n xs ! p" by auto
     with pltn and nth_take have "((take n xs) @ (drop (Suc n) xs)) ! p =  xs ! p" by simp
   }
  from this and ltk and p_ub show ?thesis by simp
 next
 case False
  hence "length xs \<le> n" by arith
  with remove_nth_id show ?thesis by force
qed

lemma remove_nth_sound_r :
  assumes "n \<le> p" and "p < length xs"
  shows "(remove_nth n xs) ! p = xs ! (Suc p)"
proof-
 from \<open>n \<le> p\<close> and \<open>p < length xs\<close> have n_ub: "n < length xs" by arith
 from length_take and n_ub have ltk: "length (take n xs) = n" by simp
 from \<open>n \<le> p\<close> and ltk and nth_append[of "take n xs" _ p]
 have Hrew: "((take n xs) @ (drop (Suc n) xs)) ! p = drop (Suc n) xs ! (p - n)" by auto
 from \<open>n \<le> p\<close> have idx: "Suc n + (p - n) = Suc p" by arith
 from \<open>p < length xs\<close> have Sp_ub: "Suc p \<le> length xs" by arith
 from idx and Sp_ub and nth_drop have Hrew': "drop (Suc n) xs ! (p - n) = xs ! (Suc p)" by simp
 from Hrew and Hrew' show ?thesis by simp
qed

lemma nth_remove_nth_conv:
  assumes "i < length (remove_nth n xs)"
  shows "remove_nth n xs ! i = xs ! (if i < n then i else Suc i)"
using assms remove_nth_sound_l remove_nth_sound_r[of n i xs] by auto

lemma remove_nth_P_compat :
  assumes aslbs: "length as = length bs"
  and Pab: "\<forall>i. i < length as \<longrightarrow> P (as ! i) (bs ! i)"
  shows "\<forall>i. i < length (remove_nth p as) \<longrightarrow> P (remove_nth p as ! i) (remove_nth p bs ! i)"
proof (cases "p < length as")
 case True
  hence p_ub: "p < length as" by assumption
  with remove_nth_length have lr_ub: "length (remove_nth p as) = length as - 1" by auto
  {
    fix i assume i_ub: "i < length (remove_nth p as)"
    have "P (remove_nth p as ! i) (remove_nth p bs ! i)"
     proof (cases "i < p")
     case True
      from i_ub and lr_ub have i_ub2: "i < length as" by arith
      from i_ub2 and Pab have P: "P (as ! i) (bs ! i)" by blast
      from P and remove_nth_sound_l[OF True, of as] and remove_nth_sound_l[OF True, of bs]
      show ?thesis by simp
     next
     case False
      hence p_ub2: "p \<le> i" by arith
      from i_ub and lr_ub have Si_ub: "Suc i < length as" by arith
      with Pab have P: "P (as ! Suc i) (bs ! Suc i)" by blast
      from i_ub and lr_ub have i_uba: "i < length as" by arith
      from i_uba and aslbs have i_ubb: "i < length bs" by simp      
      from P and p_ub and aslbs and remove_nth_sound_r[OF p_ub2 i_uba]
       and remove_nth_sound_r[OF p_ub2 i_ubb]
       show ?thesis by auto
     qed
  }
  thus ?thesis by simp
 next    
 case False
  hence p_lba: "length as \<le> p" by arith
  with aslbs have p_lbb: "length bs \<le> p" by simp
  from remove_nth_id[OF p_lba] and remove_nth_id[OF p_lbb] and Pab
  show ?thesis by simp
qed

declare remove_nth_def[simp del]

definition adjust_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "adjust_idx i j \<equiv> (if j < i then j else (Suc j))"

definition adjust_idx_rev :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "adjust_idx_rev i j \<equiv> (if j < i then j else j - Suc 0)"

lemma adjust_idx_rev1: "adjust_idx_rev i (adjust_idx i j) = j"
  unfolding adjust_idx_def adjust_idx_rev_def by (cases "i < j", auto)

lemma adjust_idx_rev2:
  assumes "j \<noteq> i" shows "adjust_idx i (adjust_idx_rev i j) = j"
  unfolding adjust_idx_def adjust_idx_rev_def using assms by (cases "i < j", auto)

lemma adjust_idx_i:
  "adjust_idx i j \<noteq> i"
  unfolding adjust_idx_def by (cases "j < i", auto)

lemma adjust_idx_nth:
  assumes i: "i < length xs"
  shows "remove_nth i xs ! j = xs ! adjust_idx i j" (is "?l = ?r")
proof -
  let ?j = "adjust_idx i j"
  from i have ltake: "length (take i xs) = i" by simp
  note nth_xs = arg_cong[where f = "\<lambda> xs. xs ! ?j", OF id_take_nth_drop[OF i], unfolded nth_append ltake]
  show ?thesis
  proof (cases "j < i")
    case True
    hence j: "?j = j" unfolding adjust_idx_def by simp
    show ?thesis unfolding nth_xs unfolding j remove_nth_def nth_append ltake
      using True by simp
  next
    case False
    hence j: "?j = Suc j" unfolding adjust_idx_def by simp
    from i have lxs: "min (length xs) i = i" by simp
    show ?thesis unfolding nth_xs unfolding j remove_nth_def nth_append
      using False by (simp add: lxs)
  qed
qed

lemma adjust_idx_rev_nth:
  assumes i: "i < length xs"
    and ji: "j \<noteq> i"
  shows "remove_nth i xs ! adjust_idx_rev i j = xs ! j" (is "?l = ?r")
proof -
  let ?j = "adjust_idx_rev i j"
  from i have ltake: "length (take i xs) = i" by simp
  note nth_xs = arg_cong[where f = "\<lambda> xs. xs ! j", OF id_take_nth_drop[OF i], unfolded nth_append ltake]
  show ?thesis
  proof (cases "j < i")
    case True
    hence j: "?j = j" unfolding adjust_idx_rev_def by simp
    show ?thesis unfolding nth_xs unfolding j remove_nth_def nth_append ltake
      using True by simp
  next
    case False
    with ji have ji: "j > i" by auto
    hence j: "?j = j - Suc 0" unfolding adjust_idx_rev_def by simp
    show ?thesis unfolding nth_xs unfolding j remove_nth_def nth_append ltake
      using ji by auto
  qed
qed

lemma adjust_idx_length:
  assumes i: "i < length xs"
    and j: "j < length (remove_nth i xs)"
  shows "adjust_idx i j < length xs"
  using j unfolding remove_nth_len[OF i] adjust_idx_def by (cases "j < i", auto)

lemma adjust_idx_rev_length:
  assumes "i < length xs"
    and "j < length xs"
    and "j \<noteq> i"
  shows "adjust_idx_rev i j < length (remove_nth i xs)"
  using assms by (cases "j < i") (simp_all add: adjust_idx_rev_def remove_nth_len[OF assms(1)])


text\<open>If a binary relation holds on two couples of lists, then it holds on
the concatenation of the two couples.\<close>

lemma P_as_bs_extend:
  assumes lab: "length as = length bs"
  and lcd: "length cs = length ds"
  and nsab: "\<forall>i. i < length bs \<longrightarrow> P (as ! i) (bs ! i)"
  and nscd: "\<forall>i. i < length ds \<longrightarrow> P (cs ! i) (ds ! i)"
  shows "\<forall>i. i < length (bs @ ds) \<longrightarrow> P ((as @ cs) ! i) ((bs @ ds) ! i)"
proof-
 {
   fix i
   assume i_bd: "i < length (bs @ ds)"
   have "P ((as @ cs) ! i) ((bs @ ds) ! i)"
   proof (cases "i < length as")
    case True
     with nth_append and nsab and lab
      show ?thesis by metis
    next
     case False
      with lab and lcd and i_bd and length_append[of bs ds]
       have "(i - length as) < length cs" by arith
      with False and nth_append[of _ _ i] and lab and lcd
       and nscd[rule_format] show ?thesis by metis
   qed
 }
 thus ?thesis by clarify
qed

text\<open>Extension of filter and partition to binary relations.\<close>

fun filter2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a list \<times> 'b list)" where
  "filter2 P [] _ = ([], [])" |
  "filter2 P _ [] = ([], [])" |
  "filter2 P (a # as) (b # bs) = (if P a b
        then (a # fst (filter2 P as bs), b # snd (filter2 P as bs))
        else filter2 P as bs)"

lemma filter2_length:
  "length (fst (filter2 P as bs)) \<equiv> length (snd (filter2 P as bs))"
proof (induct as arbitrary: bs)
 case Nil
  show ?case by simp
 next
 case (Cons a as) note IH = this
  thus ?case proof (cases bs)
    case Nil
     thus ?thesis by simp
    next
    case (Cons b bs)
     thus ?thesis proof (cases "P a b")
       case True
        with Cons and IH show ?thesis by simp
       next
       case False
        with Cons and IH show ?thesis by simp
     qed
  qed
qed

lemma filter2_sound: "\<forall>i. i < length (fst (filter2 P as bs)) \<longrightarrow> P (fst (filter2 P as bs) ! i) (snd (filter2 P as bs) ! i)"
proof (induct as arbitrary: bs)
 case Nil
  thus ?case by simp
 next
 case (Cons a as) note IH = this
  thus ?case proof (cases bs)
    case Nil
     thus ?thesis by simp
    next
    case (Cons b bs)
     thus ?thesis proof (cases "P a b")
      case False
       with Cons and IH show ?thesis by simp
      next
      case True
       {
         fix i
         assume i_bd: "i < length (fst (filter2 P (a # as) (b # bs)))"
         have "P (fst (filter2 P (a # as) (b # bs)) ! i) (snd (filter2 P (a # as) (b # bs)) ! i)"         proof (cases i)
          case 0
           with True show ?thesis by simp
          next
          case (Suc j)
           with i_bd and True have "j < length (fst (filter2 P as bs))" by auto
           with Suc and IH and True show ?thesis by simp
         qed
       }
       with Cons show ?thesis by simp
     qed
 qed
qed

definition partition2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a list \<times> 'b list) \<times> ('a list \<times> 'b list)" where
  "partition2 P as bs \<equiv> ((filter2 P as bs) , (filter2 (\<lambda>a b. \<not> (P a b)) as bs))"

lemma partition2_sound_P: "\<forall>i. i < length (fst (fst (partition2 P as bs))) \<longrightarrow>
  P (fst (fst (partition2 P as bs)) ! i) (snd (fst (partition2 P as bs)) ! i)"
proof-
 from filter2_sound show ?thesis unfolding partition2_def by simp
qed

lemma partition2_sound_nP: "\<forall>i. i < length (fst (snd (partition2 P as bs))) \<longrightarrow>
  \<not> P (fst (snd (partition2 P as bs)) ! i) (snd (snd (partition2 P as bs)) ! i)" 
proof-
 from filter2_sound show ?thesis unfolding partition2_def by simp
qed


text\<open>Membership decision function that actually returns the
value of the index where the value can be found.\<close>

fun mem_idx :: "'a \<Rightarrow> 'a list \<Rightarrow> nat Option.option" where
  "mem_idx _ []       = None" |
  "mem_idx x (a # as) = (if x = a then Some 0 else map_option Suc (mem_idx x as))"

lemma mem_idx_sound_output:
  assumes "mem_idx x as = Some i"
  shows "i < length as \<and> as ! i = x"
using assms proof (induct as arbitrary: i)
  case Nil thus ?case by simp
  next
  case (Cons a as) note IH = this
   thus ?case proof (cases "x = a")
     case True with IH(2) show ?thesis by simp
     next
     case False note neq_x_a = this
      show ?thesis proof (cases "mem_idx x as")
       case None with IH(2) and neq_x_a show ?thesis by simp
       next
       case (Some j)
        with IH(2) and neq_x_a have "i = Suc j" by simp
        with IH(1) and Some show ?thesis by simp
      qed
   qed
qed

lemma mem_idx_sound_output2:
  assumes "mem_idx x as = Some i"
  shows "\<forall>j. j < i \<longrightarrow> as ! j \<noteq> x"
using assms proof (induct as arbitrary: i)
  case Nil thus ?case by simp
  next
  case (Cons a as) note IH = this
   thus ?case proof (cases "x = a")
     case True with IH show ?thesis by simp
     next
     case False note neq_x_a = this
      show ?thesis proof (cases "mem_idx x as")
       case None with IH(2) and neq_x_a show ?thesis by simp
       next
       case (Some j)
        with IH(2) and neq_x_a have eq_i_Sj: "i = Suc j" by simp
        {
          fix k assume k_bd: "k < i"
          have "(a # as) ! k \<noteq> x"
          proof (cases k)
          case 0 with neq_x_a show ?thesis by simp
          next
          case (Suc l)
            with k_bd and eq_i_Sj have l_bd: "l < j" by arith
            with IH(1) and Some have "as ! l \<noteq> x" by simp
            with Suc show ?thesis by simp
          qed
        }
        thus ?thesis by simp
      qed
   qed
qed

lemma mem_idx_sound:
 "(x \<in> set as) = (\<exists>i. mem_idx x as = Some i)"
proof (induct as)
 case Nil thus ?case by simp
 next
 case (Cons a as) note IH = this
  show ?case proof (cases "x = a")
   case True thus ?thesis by simp
   next
   case False
    {
      assume "x \<in> set (a # as)"
       with False have "x \<in> set as" by simp
       with IH obtain i where Some_i: "mem_idx x as = Some i" by auto
       with False have "mem_idx x (a # as) = Some (Suc i)" by simp
      hence "\<exists>i. mem_idx x (a # as) = Some i" by simp
    }
    moreover
    {
      assume "\<exists>i. mem_idx x (a # as) = Some i"
       then obtain i where Some_i: "mem_idx x (a # as) = Some i" by fast
       have "x \<in> set as" proof (cases i)
         case 0 with mem_idx_sound_output[OF Some_i] and False show ?thesis by simp
         next
         case (Suc j)
          with Some_i and False have "mem_idx x as = Some j" by simp
          hence "\<exists>i. mem_idx x as = Some i" by simp
          with IH show ?thesis by simp
       qed
       hence "x \<in> set (a # as)" by simp
    }
    ultimately show ?thesis by fast
  qed
qed

lemma mem_idx_sound2:
  "(x \<notin> set as) = (mem_idx x as = None)"
  unfolding mem_idx_sound by auto

lemma sum_list_replicate_mono: assumes "w1 \<le> (w2 :: nat)"
  shows "sum_list (replicate n w1) \<le> sum_list (replicate n w2)"
proof (induct n)
  case (Suc n)
  thus ?case using \<open>w1 \<le> w2\<close> by auto
qed simp

lemma all_gt_0_sum_list_map:
  assumes *: "\<And>x. f x > (0::nat)"
    and x: "x \<in> set xs" and len: "1 < length xs"
  shows "f x < (\<Sum>x\<leftarrow>xs. f x)"
  using x len
proof (induct xs)
  case (Cons y xs)
  show ?case
  proof (cases "y = x")
    case True
    with *[of "hd xs"] Cons(3) show ?thesis by (cases xs, auto)
  next
    case False
    with Cons(2) have x: "x \<in> set xs" by auto
    then obtain z zs where xs: "xs = z # zs" by (cases xs, auto)
    show ?thesis
    proof (cases "length zs")
      case 0
      with x xs *[of y] show ?thesis by auto
    next
      case (Suc n)
      with xs have "1 < length xs" by auto
      from Cons(1)[OF x this] show ?thesis by simp
    qed
  qed
qed simp

lemma finite_distinct: "finite { xs . distinct xs \<and> set xs = X}" (is "finite (?S X)")
proof (cases "finite X")
  case False
  with finite_set have id: "?S X = {}" by auto
  show ?thesis unfolding id by auto
next
  case True
  show ?thesis
  proof (induct rule: finite_induct[OF True])
    case (2 x X)
    let ?L = "{0..< card (insert x X)} \<times> ?S X"
    from 2(3)
    have fin: "finite ?L" by auto
    let ?f = "\<lambda> (i,xs). take i xs @ x # drop i xs"
    show ?case
    proof (rule finite_surj[OF fin, of _ ?f], rule)
      fix xs
      assume "xs \<in> ?S (insert x X)"
      hence dis: "distinct xs" and set: "set xs = insert x X" by auto
      from distinct_card[OF dis] have len: "length xs = card (set xs)" by auto
      from set[unfolded set_conv_nth] obtain i where x: "x = xs ! i" and i: "i < length xs" by auto
      from i have min: "min (length xs) i = i" by simp
      let ?ys = "take i xs @ drop (Suc i) xs"
      from id_take_nth_drop[OF i] have xsi: "xs = take i xs @ xs ! i # drop (Suc i) xs" .
      also have "... = ?f (i,?ys)" unfolding split
        by (simp add: min x)
      finally have xs: "xs = ?f (i,?ys)" .
      show "xs \<in> ?f ` ?L"
      proof (rule image_eqI, rule xs, rule SigmaI)
        show "i \<in> {0..<card (insert x X)}" using i[unfolded len] set[symmetric] by simp
      next
        from dis xsi have disxsi: "distinct (take i xs @ xs ! i # drop (Suc i) xs)" by simp
        note disxsi = disxsi[unfolded distinct_append x[symmetric]]
        have xys: "x \<notin> set ?ys" using disxsi by auto
        from distinct_take_drop[OF dis i]
        have disys: "distinct ?ys" .
        have "insert x (set ?ys) = set xs" unfolding arg_cong[OF xsi, of set] x by simp
        hence "insert x (set ?ys) = insert x X" unfolding set by simp
        from this[unfolded insert_eq_iff[OF xys 2(2)]]
        show "?ys \<in> ?S X" using disys by auto
      qed
    qed
  qed simp
qed

lemma finite_distinct_subset:
  assumes "finite X"
  shows "finite { xs . distinct xs \<and> set xs \<subseteq> X}" (is "finite (?S X)")
proof -
  let ?X = "{ { xs. distinct xs \<and> set xs = Y} | Y. Y \<subseteq> X}"
  have id: "?S X = \<Union> ?X" by blast
  show ?thesis unfolding id
  proof (rule finite_Union)
    show "finite ?X" using assms  by auto
  next
    fix M
    assume "M \<in> ?X"
    with finite_distinct show "finite M" by auto
  qed
qed

lemma map_of_filter:
  assumes "P x"
  shows "map_of [(x',y) \<leftarrow> ys. P x'] x = map_of ys x"
proof (induct ys)
  case (Cons xy ys)
  obtain x' y where xy: "xy = (x',y)" by force
  show ?case
    by (cases "x' = x", insert assms xy Cons, auto)
qed simp

lemma set_subset_insertI: "set xs \<subseteq> set (List.insert x xs)" by auto
lemma set_removeAll_subset: "set (removeAll x xs) \<subseteq> set xs" by auto

lemma map_of_append_Some:
  "map_of xs y = Some z \<Longrightarrow> map_of (xs @ ys) y = Some z"
  by (induction xs) auto

lemma map_of_append_None:
  "map_of xs y = None \<Longrightarrow> map_of (xs @ ys) y = map_of ys y"
  by (induction xs) auto


end
