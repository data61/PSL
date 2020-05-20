section \<open>General Utilities\<close>

theory General
  imports Polynomials.Utils
begin

text \<open>A couple of general-purpose functions and lemmas, mainly related to lists.\<close>

subsection \<open>Lists\<close>

lemma distinct_reorder: "distinct (xs @ (y # ys)) = distinct (y # (xs @ ys))" by auto
    
lemma set_reorder: "set (xs @ (y # ys)) = set (y # (xs @ ys))" by simp

lemma distinctI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp, intro conjI, rule)
    assume "x \<in> set xs"
    then obtain j where "j < length xs" and "x = xs ! j" by (metis in_set_conv_nth)
    hence "Suc j < length (x # xs)" by simp
    have "(x # xs) ! 0 \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2), simp, simp, fact)
    thus False by (simp add: \<open>x = xs ! j\<close>)
  next
    show "distinct xs"
    proof (rule Cons(1))
      fix i j
      assume "i < j" and "i < length xs" and "j < length xs"
      hence "Suc i < Suc j" and "Suc i < length (x # xs)" and "Suc j < length (x # xs)" by simp_all
      hence "(x # xs) ! (Suc i) \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2))
      thus "xs ! i \<noteq> xs ! j" by simp
    qed
  qed
qed

lemma filter_nth_pairE:
  assumes "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  obtains i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and "(filter P xs) ! i = xs ! i'" and "(filter P xs) ! j = xs ! j'"
  using assms
proof (induct xs arbitrary: i j thesis)
  case Nil
  from Nil(3) show ?case by simp
next
  case (Cons x xs)
  let ?ys = "filter P (x # xs)"
  show ?case
  proof (cases "P x")
    case True
    hence *: "?ys = x # (filter P xs)" by simp
    from \<open>i < j\<close> obtain j0 where j: "j = Suc j0" using lessE by blast
    have len_ys: "length ?ys = Suc (length (filter P xs))" and ys_j: "?ys ! j = (filter P xs) ! j0"
      by (simp only: * length_Cons, simp only: j * nth_Cons_Suc)
    from Cons(5) have "j0 < length (filter P xs)" unfolding len_ys j by auto
    show ?thesis
    proof (cases "i = 0")
      case True
      from \<open>j0 < length (filter P xs)\<close> obtain j' where "j' < length xs" and **: "(filter P xs) ! j0 = xs ! j'"
        by (metis (no_types, lifting) in_set_conv_nth mem_Collect_eq nth_mem set_filter)
      have "0 < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp, simp add: \<open>j' < length xs\<close>, simp only: True * nth_Cons_0,
            simp only: ys_j nth_Cons_Suc **)
    next
      case False
      then obtain i0 where i: "i = Suc i0" using lessE by blast
      have ys_i: "?ys ! i = (filter P xs) ! i0" by (simp only: i * nth_Cons_Suc)
      from Cons(3) have "i0 < j0" by (simp add: i j)
      from Cons(4) have "i0 < length (filter P xs)" unfolding len_ys i by auto
      from _ \<open>i0 < j0\<close> this \<open>j0 < length (filter P xs)\<close> obtain i' j'
        where "i' < j'" and "i' < length xs" and "j' < length xs"
          and i': "filter P xs ! i0 = xs ! i'" and j': "filter P xs ! j0 = xs ! j'"
        by (rule Cons(1))
      from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
            simp only: ys_i nth_Cons_Suc i', simp only: ys_j nth_Cons_Suc j')
    qed
  next
    case False
    hence *: "?ys = filter P xs" by simp
    with Cons(4) Cons(5) have "i < length (filter P xs)" and "j < length (filter P xs)" by simp_all
    with _ \<open>i < j\<close> obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
      and i': "filter P xs ! i = xs ! i'" and j': "filter P xs ! j = xs ! j'"
      by (rule Cons(1))
    from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
    thus ?thesis
      by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
          simp only: * nth_Cons_Suc i', simp only: * nth_Cons_Suc j')
  qed
qed

lemma distinct_filterI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow> P (xs ! j) \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct (filter P xs)"
proof (rule distinctI)
  fix i j::nat
  assume "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  then obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and i: "(filter P xs) ! i = xs ! i'" and j: "(filter P xs) ! j = xs ! j'" by (rule filter_nth_pairE)
  from \<open>i' < j'\<close> \<open>i' < length xs\<close> \<open>j' < length xs\<close> show "(filter P xs) ! i \<noteq> (filter P xs) ! j" unfolding i j
  proof (rule assms)
    from \<open>i < length (filter P xs)\<close> show "P (xs ! i')" unfolding i[symmetric] using nth_mem by force
  next
    from \<open>j < length (filter P xs)\<close> show "P (xs ! j')" unfolding j[symmetric] using nth_mem by force
  qed
qed

lemma set_zip_map: "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
proof -
  have "{(map f xs ! i, map g xs ! i) |i. i < length xs} = {(f (xs ! i), g (xs ! i)) |i. i < length xs}"
  proof (rule Collect_eqI, rule, elim exE conjE, intro exI conjI, simp add: map_nth, assumption,
      elim exE conjE, intro exI)
    fix x i
    assume "x = (f (xs ! i), g (xs ! i))" and "i < length xs"
    thus "x = (map f xs ! i, map g xs ! i) \<and> i < length xs" by (simp add: map_nth)
  qed
  also have "... = (\<lambda>x. (f x, g x)) ` {xs ! i | i. i < length xs}" by blast
  finally show "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
    by (simp add: set_zip set_conv_nth[symmetric])
qed

lemma set_zip_map1: "set (zip (map f xs) xs) = (\<lambda>x. (f x, x)) ` (set xs)"
proof -
  have "set (zip (map f xs) (map id xs)) = (\<lambda>x. (f x, id x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

lemma set_zip_map2: "set (zip xs (map f xs)) = (\<lambda>x. (x, f x)) ` (set xs)"
proof -
  have "set (zip (map id xs) (map f xs)) = (\<lambda>x. (id x, f x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

lemma UN_upt: "(\<Union>i\<in>{0..<length xs}. f (xs ! i)) = (\<Union>x\<in>set xs. f x)"
  by (metis image_image map_nth set_map set_upt)

lemma sum_list_zeroI':
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i = 0"
  shows "sum_list xs = 0"
proof (rule sum_list_zeroI, rule, simp)
  fix x
  assume "x \<in> set xs"
  then obtain i where "i < length xs" and "x = xs ! i" by (metis in_set_conv_nth)
  from this(1) show "x = 0" unfolding \<open>x = xs ! i\<close> by (rule assms)
qed

lemma sum_list_map2_plus:
  assumes "length xs = length ys"
  shows "sum_list (map2 (+) xs ys) = sum_list xs + sum_list (ys::'a::comm_monoid_add list)"
  using assms
proof (induct rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  show ?case by (simp add: Cons(2) ac_simps)
qed

lemma sum_list_eq_nthI:
  assumes "i < length xs" and "\<And>j. j < length xs \<Longrightarrow> j \<noteq> i \<Longrightarrow> xs ! j = 0"
  shows "sum_list xs = xs ! i"
  using assms
proof (induct xs arbitrary: i)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  have *: "xs ! j = 0" if "j < length xs" and "Suc j \<noteq> i" for j
  proof -
    have "xs ! j = (x # xs) ! (Suc j)" by simp
    also have "... = 0" by (rule Cons(3), simp add: \<open>j < length xs\<close>, fact)
    finally show ?thesis .
  qed
  show ?case
  proof (cases i)
    case 0
    have "sum_list xs = 0" by (rule sum_list_zeroI', erule *, simp add: 0)
    with 0 show ?thesis by simp
  next
    case (Suc k)
    with Cons(2) have "k < length xs" by simp
    hence "sum_list xs = xs ! k"
    proof (rule Cons(1))
      fix j
      assume "j < length xs"
      assume "j \<noteq> k"
      hence "Suc j \<noteq> i" by (simp add: Suc)
      with \<open>j < length xs\<close> show "xs ! j = 0" by (rule *)
    qed
    moreover have "x = 0"
    proof -
      have "x = (x # xs) ! 0" by simp
      also have "... = 0" by (rule Cons(3), simp_all add: Suc)
      finally show ?thesis .
    qed
    ultimately show ?thesis by (simp add: Suc)
  qed
qed

subsubsection \<open>\<open>max_list\<close>\<close>

fun (in ord) max_list :: "'a list \<Rightarrow> 'a" where
  "max_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> max x (max_list xs))"

context linorder
begin

lemma max_list_Max: "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
  by (induct xs rule: induct_list012, auto)

lemma max_list_ge:
  assumes "x \<in> set xs"
  shows "x \<le> max_list xs"
proof -
  from assms have "xs \<noteq> []" by auto
  from finite_set assms have "x \<le> Max (set xs)" by (rule Max_ge)
  also from \<open>xs \<noteq> []\<close> have "Max (set xs) = max_list xs" by (rule max_list_Max[symmetric])
  finally show ?thesis .
qed

lemma max_list_boundedI:
  assumes "xs \<noteq> []" and "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> a"
  shows "max_list xs \<le> a"
proof -
  from assms(1) have "set xs \<noteq> {}" by simp
  from assms(1) have "max_list xs = Max (set xs)" by (rule max_list_Max)
  also from finite_set \<open>set xs \<noteq> {}\<close> assms(2) have "\<dots> \<le> a" by (rule Max.boundedI)
  finally show ?thesis .
qed

end

subsubsection \<open>\<open>insort_wrt\<close>\<close>

primrec insort_wrt :: "('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'c list \<Rightarrow> 'c list" where
  "insort_wrt _ x [] = [x]" |
  "insort_wrt r x (y # ys) =
    (if r x y then (x # y # ys) else y # (insort_wrt r x ys))"

lemma insort_wrt_not_Nil [simp]: "insort_wrt r x xs \<noteq> []"
  by (induct xs, simp_all)

lemma length_insort_wrt [simp]: "length (insort_wrt r x xs) = Suc (length xs)"
  by (induct xs, simp_all)

lemma set_insort_wrt [simp]: "set (insort_wrt r x xs) = insert x (set xs)"
  by (induct xs, auto)

lemma sorted_wrt_insort_wrt_imp_sorted_wrt:
  assumes "sorted_wrt r (insort_wrt s x xs)"
  shows "sorted_wrt r xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "s x a")
    case True
    with Cons.prems have "sorted_wrt r (x # a # xs)" by simp
    thus ?thesis by simp
  next
    case False
    with Cons(2) have "sorted_wrt r (a # (insort_wrt s x xs))" by simp
    hence *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r (insort_wrt s x xs)"
      by (simp_all)
    from this(2) have "sorted_wrt r xs" by (rule Cons(1))
    with * show ?thesis by (simp)
  qed
qed

lemma sorted_wrt_imp_sorted_wrt_insort_wrt:
  assumes "transp r" and "\<And>a. r a x \<or> r x a" and "sorted_wrt r xs"
  shows "sorted_wrt r (insort_wrt r x xs)"
  using assms(3)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "r x a")
    case True
    with Cons(2) assms(1) show ?thesis by (auto dest: transpD)
  next
    case False
    with assms(2) have "r a x" by blast
    from Cons(2) have *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r xs"
      by (simp_all)
    from this(2) have "sorted_wrt r (insort_wrt r x xs)" by (rule Cons(1))
    with \<open>r a x\<close> * show ?thesis by (simp add: False)
  qed
qed

corollary sorted_wrt_insort_wrt:
  assumes "transp r" and "\<And>a. r a x \<or> r x a"
  shows "sorted_wrt r (insort_wrt r x xs) \<longleftrightarrow> sorted_wrt r xs" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then show ?r by (rule sorted_wrt_insort_wrt_imp_sorted_wrt)
next
  assume ?r
  with assms show ?l by (rule sorted_wrt_imp_sorted_wrt_insort_wrt)
qed

subsubsection \<open>\<open>diff_list\<close> and \<open>insert_list\<close>\<close>

definition diff_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "--" 65)
  where "diff_list xs ys = fold removeAll ys xs"

lemma set_diff_list: "set (xs -- ys) = set xs - set ys"
  by (simp only: diff_list_def, induct ys arbitrary: xs, auto)

lemma diff_list_disjoint: "set ys \<inter> set (xs -- ys) = {}"
  unfolding set_diff_list by (rule Diff_disjoint)

lemma subset_append_diff_cancel:
  assumes "set ys \<subseteq> set xs"
  shows "set (ys @ (xs -- ys)) = set xs"
  by (simp only: set_append set_diff_list Un_Diff_cancel, rule Un_absorb1, fact)

definition insert_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "insert_list x xs = (if x \<in> set xs then xs else x # xs)"

lemma set_insert_list: "set (insert_list x xs) = insert x (set xs)"
  by (auto simp add: insert_list_def)

subsubsection \<open>\<open>remdups_wrt\<close>\<close>

primrec remdups_wrt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  remdups_wrt_base: "remdups_wrt _ [] = []" |
  remdups_wrt_rec: "remdups_wrt f (x # xs) = (if f x \<in> f ` set xs then remdups_wrt f xs else x # remdups_wrt f xs)"
    
lemma set_remdups_wrt: "f ` set (remdups_wrt f xs) = f ` set xs"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base ..
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits, intro conjI, intro impI)
    assume "f a \<in> f ` set xs"
      have "f ` set (a # xs) = insert (f a) (f ` set xs)" by simp
    have "f ` set (remdups_wrt f xs) = f ` set xs" by fact
    also from \<open>f a \<in> f ` set xs\<close> have "... = insert (f a) (f ` set xs)" by (simp add: insert_absorb)
    also have "... = f ` set (a # xs)" by simp
    finally show "f ` set (remdups_wrt f xs) = f ` set (a # xs)" .
  qed (simp add: Cons.hyps)
qed

lemma subset_remdups_wrt: "set (remdups_wrt f xs) \<subseteq> set xs"
  by (induct xs, auto)

lemma remdups_wrt_distinct_wrt:
  assumes "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)" and "x \<noteq> y"
  shows "f x \<noteq> f y"
  using assms(1) assms(2)
proof (induct xs)
  case Nil
  thus ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  from Cons(2) Cons(3) show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits)
    assume "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)"
    thus "f x \<noteq> f y" by (rule Cons.hyps)
  next
    assume "\<not> True"
    thus "f x \<noteq> f y" by simp
  next
    assume "f a \<notin> f ` set xs" and xin: "x \<in> set (a # remdups_wrt f xs)" and yin: "y \<in> set (a # remdups_wrt f xs)"
    from yin have y: "y = a \<or> y \<in> set (remdups_wrt f xs)" by simp
    from xin have "x = a \<or> x \<in> set (remdups_wrt f xs)" by simp
    thus "f x \<noteq> f y"
    proof
      assume "x = a"
      from y show ?thesis
      proof
        assume "y = a"
        with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>x = a\<close> by simp
      next
        assume "y \<in> set (remdups_wrt f xs)"
        have "y \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f y \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>x = a\<close> by auto
      qed
    next
      assume "x \<in> set (remdups_wrt f xs)"
      from y show ?thesis
      proof
        assume "y = a"
        have "x \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f x \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>y = a\<close> by auto
      next
        assume "y \<in> set (remdups_wrt f xs)"
        with \<open>x \<in> set (remdups_wrt f xs)\<close> show ?thesis by (rule Cons.hyps)
      qed
    qed
  qed
qed
  
lemma distinct_remdups_wrt: "distinct (remdups_wrt f xs)"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps)
    assume "f a \<notin> f ` set xs"
    hence "a \<notin> set xs" by auto
    hence "a \<notin> set (remdups_wrt f xs)" using subset_remdups_wrt[of f xs] by auto
    with Cons.hyps show "distinct (a # remdups_wrt f xs)" by simp
  qed
qed

lemma map_remdups_wrt: "map f (remdups_wrt f xs) = remdups (map f xs)"
  by (induct xs, auto)

lemma remdups_wrt_append:
  "remdups_wrt f (xs @ ys) = (filter (\<lambda>a. f a \<notin> f ` set ys) (remdups_wrt f xs)) @ (remdups_wrt f ys)"
  by (induct xs, auto)

subsubsection \<open>\<open>map_idx\<close>\<close>

primrec map_idx :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'b list" where
  "map_idx f [] n = []"|
  "map_idx f (x # xs) n = (f x n) # (map_idx f xs (Suc n))"

lemma map_idx_eq_map2: "map_idx f xs n = map2 f xs [n..<n + length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[n..<n + length (x # xs)] = n # [Suc n..<Suc (n + length xs)]"
    by (metis add_Suc_right length_Cons less_add_Suc1 upt_conv_Cons)
  show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma length_map_idx [simp]: "length (map_idx f xs n) = length xs"
  by (simp add: map_idx_eq_map2)

lemma map_idx_append: "map_idx f (xs @ ys) n = (map_idx f xs n) @ (map_idx f ys (n + length xs))"
  by (simp add: map_idx_eq_map2 ab_semigroup_add_class.add_ac(1) zip_append1)

lemma map_idx_nth:
  assumes "i < length xs"
  shows "(map_idx f xs n) ! i = f (xs ! i) (n + i)"
  using assms by (simp add: map_idx_eq_map2)

lemma map_map_idx: "map f (map_idx g xs n) = map_idx (\<lambda>x i. f (g x i)) xs n"
  by (auto simp add: map_idx_eq_map2)

lemma map_idx_map: "map_idx f (map g xs) n = map_idx (f \<circ> g) xs n"
  by (simp add: map_idx_eq_map2 map_zip_map)

lemma map_idx_no_idx: "map_idx (\<lambda>x _. f x) xs n = map f xs"
  by (induct xs arbitrary: n, simp_all)

lemma map_idx_no_elem: "map_idx (\<lambda>_. f) xs n = map f [n..<n + length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[n..<n + length (x # xs)] = n # [Suc n..<Suc (n + length xs)]"
    by (metis add_Suc_right length_Cons less_add_Suc1 upt_conv_Cons)
  show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma map_idx_eq_map: "map_idx f xs n = map (\<lambda>i. f (xs ! i) (i + n)) [0..<length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[0..<length (x # xs)] = 0 # [Suc 0..<Suc (length xs)]"
    by (metis length_Cons upt_conv_Cons zero_less_Suc)
  have "map (\<lambda>i. f ((x # xs) ! i) (i + n)) [Suc 0..<Suc (length xs)] =
        map ((\<lambda>i. f ((x # xs) ! i) (i + n)) \<circ> Suc) [0..<length xs]"
    by (metis map_Suc_upt map_map)
  also have "... = map (\<lambda>i. f (xs ! i) (Suc (i + n))) [0..<length xs]"
    by (rule map_cong, fact refl, simp)
  finally show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma set_map_idx: "set (map_idx f xs n) = (\<lambda>i. f (xs ! i) (i + n)) ` {0..<length xs}"
  by (simp add: map_idx_eq_map)

subsubsection \<open>\<open>map_dup\<close>\<close>

primrec map_dup :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_dup _ _ [] = []"|
  "map_dup f g (x # xs) = (if x \<in> set xs then g x else f x) # (map_dup f g xs)"

lemma length_map_dup[simp]: "length (map_dup f g xs) = length xs"
  by (induct xs, simp_all)

lemma map_dup_distinct:
  assumes "distinct xs"
  shows "map_dup f g xs = map f xs"
  using assms by (induct xs, simp_all)

lemma filter_map_dup_const:
  "filter (\<lambda>x. x \<noteq> c) (map_dup f (\<lambda>_. c) xs) = filter (\<lambda>x. x \<noteq> c) (map f (remdups xs))"
  by (induct xs, simp_all)

lemma filter_zip_map_dup_const:
  "filter (\<lambda>(a, b). a \<noteq> c) (zip (map_dup f (\<lambda>_. c) xs) xs) =
    filter (\<lambda>(a, b). a \<noteq> c) (zip (map f (remdups xs)) (remdups xs))"
  by (induct xs, simp_all)

subsubsection \<open>Filtering Minimal Elements\<close>

context
  fixes rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

primrec filter_min_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_min_aux [] ys = ys"|
  "filter_min_aux (x # xs) ys =
    (if (\<exists>y\<in>(set xs \<union> set ys). rel y x) then (filter_min_aux xs ys)
    else (filter_min_aux xs (x # ys)))"

definition filter_min :: "'a list \<Rightarrow> 'a list"
  where "filter_min xs = filter_min_aux xs []"

definition filter_min_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "filter_min_append xs ys =
                  (let P = (\<lambda>zs. \<lambda>x. \<not> (\<exists>z\<in>set zs. rel z x)); ys1 = filter (P xs) ys in
                    (filter (P ys1) xs) @ ys1)"
  
lemma filter_min_aux_supset: "set ys \<subseteq> set (filter_min_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "set ys \<subseteq> set (x # ys)" by auto
  also have "set (x # ys) \<subseteq> set (filter_min_aux xs (x # ys))" by (rule Cons.hyps)
  finally have "set ys \<subseteq> set (filter_min_aux xs (x # ys))" .
  moreover have "set ys \<subseteq> set (filter_min_aux xs ys)" by (rule Cons.hyps)
  ultimately show ?case by simp
qed
    
lemma filter_min_aux_subset: "set (filter_min_aux xs ys) \<subseteq> set xs \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  note Cons.hyps
  also have "set xs \<union> set ys \<subseteq> set (x # xs) \<union> set ys" by fastforce
  finally have c1: "set (filter_min_aux xs ys) \<subseteq> set (x # xs) \<union> set ys" .
  
  note Cons.hyps
  also have "set xs \<union> set (x # ys) = set (x # xs) \<union> set ys" by simp
  finally have "set (filter_min_aux xs (x # ys)) \<subseteq> set (x # xs) \<union> set ys" .
  with c1 show ?case by simp
qed

lemma filter_min_aux_relE:
  assumes "transp rel" and "x \<in> set xs" and "x \<notin> set (filter_min_aux xs ys)"
  obtains y where "y \<in> set (filter_min_aux xs ys)" and "rel y x"
  using assms(2, 3)
proof (induct xs arbitrary: x ys thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons x0 xs)
  from Cons(3) have "x = x0 \<or> x \<in> set xs" by simp
  thus ?case
  proof
    assume "x = x0"
    from Cons(4) have *: "\<exists>y\<in>set xs \<union> set ys. rel y x0"
    proof (simp add: \<open>x = x0\<close> split: if_splits)
      assume "x0 \<notin> set (filter_min_aux xs (x0 # ys))"
      moreover from filter_min_aux_supset have "x0 \<in> set (filter_min_aux xs (x0 # ys))"
        by (rule subsetD) simp
      ultimately show False ..
    qed
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
    from * obtain x1 where "x1 \<in> set xs \<union> set ys" and "rel x1 x" unfolding \<open>x = x0\<close> ..
    from this(1) show ?thesis
    proof
      assume "x1 \<in> set xs"
      show ?thesis
      proof (cases "x1 \<in> set (filter_min_aux xs ys)")
        case True
        hence "x1 \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
        thus ?thesis using \<open>rel x1 x\<close> by (rule Cons(2))
      next
        case False
        with \<open>x1 \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs ys)" and "rel y x1"
          using Cons.hyps by blast
        from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
        moreover from assms(1) \<open>rel y x1\<close> \<open>rel x1 x\<close> have "rel y x" by (rule transpD)
        ultimately show ?thesis by (rule Cons(2))
      qed
    next
      assume "x1 \<in> set ys"
      hence "x1 \<in> set (filter_min_aux (x0 # xs) ys)" using filter_min_aux_supset ..
      thus ?thesis using \<open>rel x1 x\<close> by (rule Cons(2))
    qed
  next
    assume "x \<in> set xs"
    show ?thesis
    proof (cases "\<exists>y\<in>set xs \<union> set ys. rel y x0")
      case True
      hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
      with Cons(4) have "x \<notin> set (filter_min_aux xs ys)" by simp
      with \<open>x \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs ys)" and "rel y x"
        using Cons.hyps by blast
      from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
      thus ?thesis using \<open>rel y x\<close> by (rule Cons(2))
    next
      case False
      hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs (x0 # ys)" by simp
      with Cons(4) have "x \<notin> set (filter_min_aux xs (x0 # ys))" by simp
      with \<open>x \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs (x0 # ys))" and "rel y x"
        using Cons.hyps by blast
      from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
      thus ?thesis using \<open>rel y x\<close> by (rule Cons(2))
    qed
  qed
qed

lemma filter_min_aux_minimal:
  assumes "transp rel" and "x \<in> set (filter_min_aux xs ys)" and "y \<in> set (filter_min_aux xs ys)"
    and "rel x y"
  assumes "\<And>a b. a \<in> set xs \<union> set ys \<Longrightarrow> b \<in> set ys \<Longrightarrow> rel a b \<Longrightarrow> a = b"
  shows "x = y"
  using assms(2-5)
proof (induct xs arbitrary: x y ys)
  case Nil
  from Nil(1) have "x \<in> set [] \<union> set ys" by simp
  moreover from Nil(2) have "y \<in> set ys" by simp
  ultimately show ?case using Nil(3) by (rule Nil(4))
next
  case (Cons x0 xs)
  show ?case
  proof (cases "\<exists>y\<in>set xs \<union> set ys. rel y x0")
    case True
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
    with Cons(2, 3) have "x \<in> set (filter_min_aux xs ys)" and "y \<in> set (filter_min_aux xs ys)"
      by simp_all
    thus ?thesis using Cons(4)
    proof (rule Cons.hyps)
      fix a b
      assume "a \<in> set xs \<union> set ys"
      hence "a \<in> set (x0 # xs) \<union> set ys" by simp
      moreover assume "b \<in> set ys" and "rel a b"
      ultimately show "a = b" by (rule Cons(5))
    qed
  next
    case False
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs (x0 # ys)" by simp
    with Cons(2, 3) have "x \<in> set (filter_min_aux xs (x0 # ys))" and "y \<in> set (filter_min_aux xs (x0 # ys))"
      by simp_all
    thus ?thesis using Cons(4)
    proof (rule Cons.hyps)
      fix a b
      assume a: "a \<in> set xs \<union> set (x0 # ys)" and "b \<in> set (x0 # ys)" and "rel a b"
      from this(2) have "b = x0 \<or> b \<in> set ys" by simp
      thus "a = b"
      proof
        assume "b = x0"
        from a have "a = x0 \<or> a \<in> set xs \<union> set ys" by simp
        thus ?thesis
        proof
          assume "a = x0"
          with \<open>b = x0\<close> show ?thesis by simp
        next
          assume "a \<in> set xs \<union> set ys"
          hence "\<exists>y\<in>set xs \<union> set ys. rel y x0" using \<open>rel a b\<close> unfolding \<open>b = x0\<close> ..
          with False show ?thesis ..
        qed
      next
        from a have "a \<in> set (x0 # xs) \<union> set ys" by simp
        moreover assume "b \<in> set ys"
        ultimately show ?thesis using \<open>rel a b\<close> by (rule Cons(5))
      qed
    qed
  qed
qed
  
lemma filter_min_aux_distinct:
  assumes "reflp rel" and "distinct ys"
  shows "distinct (filter_min_aux xs ys)"
  using assms(2)
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp split: if_split, intro conjI impI)
    from Cons(2) show "distinct (filter_min_aux xs ys)" by (rule Cons.hyps)
  next
    assume a: "\<forall>y\<in>set xs \<union> set ys. \<not> rel y x"
    show "distinct (filter_min_aux xs (x # ys))"
    proof (rule Cons.hyps)
      have "x \<notin> set ys"
      proof
        assume "x \<in> set ys"
        hence "x \<in> set xs \<union> set ys" by simp
        with a have "\<not> rel x x" ..
        moreover from assms(1) have "rel x x" by (rule reflpD)
        ultimately show False ..
      qed
      with Cons(2) show "distinct (x # ys)" by simp
    qed
  qed
qed

lemma filter_min_subset: "set (filter_min xs) \<subseteq> set xs"
  using filter_min_aux_subset[of xs "[]"] by (simp add: filter_min_def)

lemma filter_min_cases:
  assumes "transp rel" and "x \<in> set xs"
  assumes "x \<in> set (filter_min xs) \<Longrightarrow> thesis"
  assumes "\<And>y. y \<in> set (filter_min xs) \<Longrightarrow> x \<notin> set (filter_min xs) \<Longrightarrow> rel y x \<Longrightarrow> thesis"
  shows thesis
proof (cases "x \<in> set (filter_min xs)")
  case True
  thus ?thesis by (rule assms(3))
next
  case False
  with assms(1, 2) obtain y where "y \<in> set (filter_min xs)" and "rel y x"
    unfolding filter_min_def by (rule filter_min_aux_relE)
  from this(1) False this(2) show ?thesis by (rule assms(4))
qed

corollary filter_min_relE:
  assumes "transp rel" and "reflp rel" and "x \<in> set xs"
  obtains y where "y \<in> set (filter_min xs)" and "rel y x"
  using assms(1, 3)
proof (rule filter_min_cases)
  assume "x \<in> set (filter_min xs)"
  moreover from assms(2) have "rel x x" by (rule reflpD)
  ultimately show ?thesis ..
qed

lemma filter_min_minimal:
  assumes "transp rel" and "x \<in> set (filter_min xs)" and "y \<in> set (filter_min xs)" and "rel x y"
  shows "x = y"
  using assms unfolding filter_min_def by (rule filter_min_aux_minimal) simp

lemma filter_min_distinct:
  assumes "reflp rel"
  shows "distinct (filter_min xs)"
  unfolding filter_min_def by (rule filter_min_aux_distinct, fact, simp)

lemma filter_min_append_subset: "set (filter_min_append xs ys) \<subseteq> set xs \<union> set ys"
  by (auto simp: filter_min_append_def)

lemma filter_min_append_cases:
  assumes "transp rel" and "x \<in> set xs \<union> set ys"
  assumes "x \<in> set (filter_min_append xs ys) \<Longrightarrow> thesis"
  assumes "\<And>y. y \<in> set (filter_min_append xs ys) \<Longrightarrow> x \<notin> set (filter_min_append xs ys) \<Longrightarrow> rel y x \<Longrightarrow> thesis"
  shows thesis
proof (cases "x \<in> set (filter_min_append xs ys)")
  case True
  thus ?thesis by (rule assms(3))
next
  case False
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  from assms(2) obtain y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
  proof
    assume "x \<in> set xs"
    with False obtain y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
      by (auto simp: filter_min_append_def P_def)
    thus ?thesis ..
  next
    assume "x \<in> set ys"
    with False obtain y where "y \<in> set xs" and "rel y x"
      by (auto simp: filter_min_append_def P_def)
    show ?thesis
    proof (cases "y \<in> set (filter_min_append xs ys)")
      case True
      thus ?thesis using \<open>rel y x\<close> ..
    next
      case False
      with \<open>y \<in> set xs\<close> obtain y' where y': "y' \<in> set (filter_min_append xs ys)" and "rel y' y"
        by (auto simp: filter_min_append_def P_def)
      from assms(1) this(2) \<open>rel y x\<close> have "rel y' x" by (rule transpD)
      with y' show ?thesis ..
    qed
  qed
  from this(1) False this(2) show ?thesis by (rule assms(4))
qed

corollary filter_min_append_relE:
  assumes "transp rel" and "reflp rel" and "x \<in> set xs \<union> set ys"
  obtains y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
  using assms(1, 3)
proof (rule filter_min_append_cases)
  assume "x \<in> set (filter_min_append xs ys)"
  moreover from assms(2) have "rel x x" by (rule reflpD)
  ultimately show ?thesis ..
qed

lemma filter_min_append_minimal:
  assumes "\<And>x' y'. x' \<in> set xs \<Longrightarrow> y' \<in> set xs \<Longrightarrow> rel x' y' \<Longrightarrow> x' = y'"
    and "\<And>x' y'. x' \<in> set ys \<Longrightarrow> y' \<in> set ys \<Longrightarrow> rel x' y' \<Longrightarrow> x' = y'"
    and "x \<in> set (filter_min_append xs ys)" and "y \<in> set (filter_min_append xs ys)" and "rel x y"
  shows "x = y"
proof -
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  define ys1 where "ys1 = filter (P xs) ys"
  from assms(3) have "x \<in> set xs \<union> set ys1"
    by (auto simp: filter_min_append_def P_def ys1_def)
  moreover from assms(4) have "y \<in> set (filter (P ys1) xs) \<union> set ys1"
    by (simp add: filter_min_append_def P_def ys1_def)
  ultimately show ?thesis
  proof (elim UnE)
    assume "x \<in> set xs"
    assume "y \<in> set (filter (P ys1) xs)"
    hence "y \<in> set xs" by simp
    with \<open>x \<in> set xs\<close> show ?thesis using assms(5) by (rule assms(1))
  next
    assume "y \<in> set ys1"
    hence "\<And>z. z \<in> set xs \<Longrightarrow> \<not> rel z y" by (simp add: ys1_def P_def)
    moreover assume "x \<in> set xs"
    ultimately have "\<not> rel x y" by blast
    thus ?thesis using \<open>rel x y\<close> ..
  next
    assume "y \<in> set (filter (P ys1) xs)"
    hence "\<And>z. z \<in> set ys1 \<Longrightarrow> \<not> rel z y" by (simp add: P_def)
    moreover assume "x \<in> set ys1"
    ultimately have "\<not> rel x y" by blast
    thus ?thesis using \<open>rel x y\<close> ..
  next
    assume "x \<in> set ys1" and "y \<in> set ys1"
    hence "x \<in> set ys" and "y \<in> set ys" by (simp_all add: ys1_def)
    thus ?thesis using assms(5) by (rule assms(2))
  qed
qed

lemma filter_min_append_distinct:
  assumes "reflp rel" and "distinct xs" and "distinct ys"
  shows "distinct (filter_min_append xs ys)"
proof -
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  define ys1 where "ys1 = filter (P xs) ys"
  from assms(2) have "distinct (filter (P ys1) xs)" by simp
  moreover from assms(3) have "distinct ys1" by (simp add: ys1_def)
  moreover have "set (filter (P ys1) xs) \<inter> set ys1 = {}"
  proof (simp add: set_eq_iff, intro allI impI notI)
    fix x
    assume "P ys1 x"
    hence "\<And>z. z \<in> set ys1 \<Longrightarrow> \<not> rel z x" by (simp add: P_def)
    moreover assume "x \<in> set ys1"
    ultimately have "\<not> rel x x" by blast
    moreover from assms(1) have "rel x x" by (rule reflpD)
    ultimately show False ..
  qed
  ultimately show ?thesis by (simp add: filter_min_append_def ys1_def P_def)
qed

end

end (* theory *)
