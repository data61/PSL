section \<open>Implementation\<close>
theory Affine_Code
  imports
    Affine_Approximation
    Intersection
begin

text \<open>Implementing partial deviations as sorted lists of coefficients.\<close>

subsection \<open>Reverse Sorted, Distinct Association Lists\<close>

typedef (overloaded) ('a, 'b) slist =
  "{xs::('a::linorder \<times> 'b) list. distinct (map fst xs) \<and> sorted (rev (map fst xs))}"
  by (auto intro!: exI[where x="[]"])

setup_lifting type_definition_slist

lift_definition map_of_slist::"(nat, 'a::zero) slist \<Rightarrow> nat \<Rightarrow> 'a option" is map_of .

lemma finite_dom_map_of_slist[intro, simp]: "finite (dom (map_of_slist xs))"
  by transfer (auto simp: finite_dom_map_of)

abbreviation "the_default a x \<equiv> (case x of None \<Rightarrow> a | Some b \<Rightarrow> b)"

definition "Pdevs_raw xs i = the_default 0 (map_of xs i)"

lemma nonzeros_Pdevs_raw_subset: "{i. Pdevs_raw xs i \<noteq> 0} \<subseteq> dom (map_of xs)"
  unfolding Pdevs_raw_def[abs_def]
  by transfer (auto simp: Pdevs_raw_def split: option.split_asm)

lift_definition Pdevs::"(nat, 'a::zero) slist \<Rightarrow> 'a pdevs"
  is Pdevs_raw
  by (rule finite_subset[OF nonzeros_Pdevs_raw_subset]) (simp add: finite_dom_map_of)

code_datatype Pdevs

subsection \<open>Degree\<close>

primrec degree_list::"(nat \<times> 'a::zero) list \<Rightarrow> nat" where
  "degree_list [] = 0"
| "degree_list (x#xs) = (if snd x = 0 then degree_list xs else Suc (fst x))"

lift_definition degree_slist::"(nat, 'a::zero) slist \<Rightarrow> nat" is degree_list .

lemma degree_list_eq_zeroD:
  assumes "degree_list xs = 0"
  shows "the_default 0 (map_of xs i) = 0"
  using assms
  by (induct xs) (auto simp: Pdevs_raw_def sorted_append split: if_split_asm)

lemma degree_slist_eq_zeroD: "degree_slist xs = 0 \<Longrightarrow> degree (Pdevs xs) = 0"
  unfolding degree_eq_Suc_max
  by transfer (auto dest: degree_list_eq_zeroD simp: Pdevs_raw_def)

lemma degree_slist_eq_SucD: "degree_slist xs = Suc n \<Longrightarrow> pdevs_apply (Pdevs xs) n \<noteq> 0"
proof (transfer, goal_cases)
  case (1 xs n)
  thus ?case
    by (induct xs)
      (auto simp: Pdevs_raw_def sorted_append map_of_eq_None_iff[symmetric]
        split: if_split_asm option.split_asm)
qed

lemma degree_slist_zero:
  "degree_slist xs = n \<Longrightarrow> n \<le> j \<Longrightarrow> pdevs_apply (Pdevs xs) j = 0"
proof (transfer, goal_cases)
  case (1 xs n j)
  thus ?case
    by (induct xs)
      (auto simp: Pdevs_raw_def sorted_append split: if_split_asm option.split)
qed

lemma compute_degree[code]: "degree (Pdevs xs) = degree_slist xs"
  by (cases "degree_slist xs")
    (auto dest: degree_slist_eq_zeroD degree_slist_eq_SucD intro!: degree_eqI degree_slist_zero)


subsection \<open>Auxiliary Definitions\<close>

fun binop where
  "binop f z1 z2 [] [] = []"
| "binop f z1 z2 ((i, x)#xs) [] = (i, f x z2) # binop f z1 z2 xs []"
| "binop f z1 z2 [] ((i, y)#ys) = (i, f z1 y) # binop f z1 z2 [] ys"
| "binop f z1 z2 ((i, x)#xs) ((j, y)#ys) =
    (if (i = j)     then (i, f x y) # binop f z1 z2 xs ys
    else if (i > j) then (i, f x z2) # binop f z1 z2 xs ((j, y)#ys)
    else                 (j, f z1 y) # binop f z1 z2 ((i, x)#xs) ys)"

lemma set_binop_elemD1:
  "(a, b) \<in> set (binop f z1 z2 xs ys) \<Longrightarrow> (a \<in> set (map fst xs) \<or> a \<in> set (map fst ys))"
  by (induct f z1 z2 xs ys rule: binop.induct) (auto split: if_split_asm)

lemma set_binop_elemD2:
  "(a, b) \<in> set (binop f z1 z2 xs ys) \<Longrightarrow>
    (\<exists>x\<in>set (map snd xs). b = f x z2) \<or>
    (\<exists>y\<in>set (map snd ys). b = f z1 y) \<or>
    (\<exists>x\<in>set (map snd xs). \<exists>y\<in>set (map snd ys). b = f x y)"
  by (induct f z1 z2 xs ys rule: binop.induct) (auto split: if_split_asm)

abbreviation "rsorted\<equiv>\<lambda>x. sorted (rev x)"

lemma rsorted_binop:
  fixes xs::"('a::linorder * 'b) list" and ys::"('a::linorder * 'c) list"
  assumes "rsorted ((map fst xs))"
  assumes "rsorted ((map fst ys))"
  shows "rsorted ((map fst (binop f z1 z2 xs ys)))"
  using assms
  by (induct f z1 z2 xs ys rule: binop.induct) (force simp: sorted_append dest!: set_binop_elemD1)+

lemma distinct_binop:
  fixes xs::"('a::linorder * 'b) list" and ys::"('a::linorder * 'c) list"
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst ys)"
  assumes "rsorted ((map fst xs))"
  assumes "rsorted ((map fst ys))"
  shows "distinct (map fst (binop f z1 z2 xs ys))"
  using assms
  by (induct f z1 z2 xs ys rule: binop.induct)
    (force dest!: set_binop_elemD1 simp: sorted_append)+

lemma binop_plus:
  fixes b::"(nat * 'a::euclidean_space) list"
  shows
    "(\<Sum>(i, y)\<leftarrow>binop (+) 0 0 b ba. e i *\<^sub>R y) = (\<Sum>(i, y)\<leftarrow>b. e i *\<^sub>R y) + (\<Sum>(i, y)\<leftarrow>ba. e i *\<^sub>R y)"
  by (induct "(+) ::'a\<Rightarrow>_" "0::'a" "0::'a" b ba rule: binop.induct)
    (auto simp: algebra_simps)

lemma binop_compose:
  "binop (\<lambda>x y. f (g x y)) z1 z2 xs ys = map (apsnd f) (binop g z1 z2 xs ys)"
  by (induct "\<lambda>x y. f (g x y)" z1 z2 xs ys rule: binop.induct) auto

lemma linear_cmul_left[intro, simp]: "linear ((*) x::real \<Rightarrow> _)"
  by (auto intro!: linearI simp: algebra_simps)

lemma length_merge_sorted_eq:
  "length (binop f z1 z2 xs ys) = length (binop g y1 y2 xs ys)"
  by (induction f z1 z2 xs ys rule: binop.induct) auto


subsection \<open>Pointswise Addition\<close>

lift_definition add_slist::"(nat, 'a::{plus, zero}) slist \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'a) slist" is
  "\<lambda>xs ys. binop (+) 0 0 xs ys"
  by (auto simp: intro!: distinct_binop rsorted_binop)

lemma map_of_binop[simp]: "rsorted (map fst xs) \<Longrightarrow> rsorted (map fst ys) \<Longrightarrow>
  distinct (map fst xs) \<Longrightarrow> distinct (map fst ys) \<Longrightarrow>
  map_of (binop f z1 z2 xs ys) i =
  (case map_of xs i of
    Some x \<Rightarrow> Some (f x (case map_of ys i of Some x \<Rightarrow> x | None \<Rightarrow> z2))
  | None \<Rightarrow> (case map_of ys i of Some y \<Rightarrow> Some (f z1 y) | None \<Rightarrow> None))"
  by (induct f z1 z2 xs ys rule: binop.induct)
    (auto split: option.split option.split_asm simp: sorted_append)

lemma pdevs_apply_Pdevs_add_slist[simp]:
  fixes xs ys::"(nat, 'a::monoid_add) slist"
  shows "pdevs_apply (Pdevs (add_slist xs ys)) i =
    pdevs_apply (Pdevs xs) i + pdevs_apply (Pdevs ys) i"
  by (transfer) (auto simp: Pdevs_raw_def split: option.split)

lemma compute_add_pdevs[code]: "add_pdevs (Pdevs xs) (Pdevs ys) = Pdevs (add_slist xs ys)"
  by (rule pdevs_eqI) simp

subsection \<open>prod of pdevs\<close>

lift_definition prod_slist::"(nat, 'a::zero) slist \<Rightarrow> (nat, 'b::zero) slist \<Rightarrow> (nat, ('a \<times> 'b)) slist" is
  "\<lambda>xs ys. binop Pair 0 0 xs ys"
  by (auto simp: intro!: distinct_binop rsorted_binop)

lemma pdevs_apply_Pdevs_prod_slist[simp]:
  "pdevs_apply (Pdevs (prod_slist xs ys)) i = (pdevs_apply (Pdevs xs) i, pdevs_apply (Pdevs ys) i)"
  by transfer (auto simp: Pdevs_raw_def zero_prod_def split: option.splits)

lemma compute_prod_of_pdevs[code]: "prod_of_pdevs (Pdevs xs) (Pdevs ys) = Pdevs (prod_slist xs ys)"
  by (rule pdevs_eqI) simp


subsection \<open>Set of Coefficients\<close>

lift_definition set_slist::"(nat, 'a::real_vector) slist \<Rightarrow> (nat * 'a) set" is set .

lemma finite_set_slist[intro, simp]: "finite (set_slist xs)"
  by transfer simp

subsection \<open>Domain\<close>

lift_definition list_of_slist::"('a::linorder, 'b::zero) slist \<Rightarrow> ('a * 'b) list"
  is "\<lambda>xs. filter (\<lambda>x. snd x \<noteq> 0) xs" .

lemma compute_pdevs_domain[code]: "pdevs_domain (Pdevs xs) = set (map fst (list_of_slist xs))"
  unfolding pdevs_domain_def
  by transfer (force simp: Pdevs_raw_def split: option.split_asm)

lemma sort_rev_eq_sort: "distinct xs \<Longrightarrow> sort (rev xs) = sort xs"
  by (rule sorted_distinct_set_unique) auto

lemma compute_list_of_pdevs[code]: "list_of_pdevs (Pdevs xs) = list_of_slist xs"
proof -
  have "list_of_pdevs (Pdevs xs) =
    map (\<lambda>i. (i, pdevs_apply (Pdevs xs) i)) (rev (sorted_list_of_set (pdevs_domain (Pdevs xs))))"
    by (simp add: list_of_pdevs_def)
  also have "(sorted_list_of_set (pdevs_domain (Pdevs xs))) = rev (map fst (list_of_slist xs))"
    unfolding compute_pdevs_domain sorted_list_of_set_sort_remdups
  proof (transfer, goal_cases)
    case prems: (1 xs)
    hence distinct: "distinct (map fst [x\<leftarrow>xs . snd x \<noteq> 0])"
      by (auto simp: filter_map distinct_map intro: subset_inj_on)
    with prems show ?case
      using sort_rev_eq_sort[symmetric, OF distinct]
      by (auto simp: rev_map rev_filter distinct_map distinct_remdups_id
        intro!: sorted_sort_id sorted_filter)
  qed
  also
  have "map (\<lambda>i. (i, pdevs_apply (Pdevs xs) i)) (rev \<dots>) = list_of_slist xs"
  proof (transfer, goal_cases)
    case (1 xs)
    thus ?case
      unfolding Pdevs_raw_def o_def rev_rev_ident map_map
      by (subst map_cong[where g="\<lambda>x. x"]) (auto simp: map_filter_map_filter)
  qed
  finally show ?thesis .
qed

lift_definition slist_of_pdevs::"'a pdevs \<Rightarrow> (nat, 'a::real_vector) slist" is list_of_pdevs
  by (auto simp: list_of_pdevs_def rev_map rev_filter
    filter_map o_def distinct_map image_def
    intro!: distinct_filter sorted_filter[of "\<lambda>x. x", simplified])

subsection \<open>Application\<close>

lift_definition slist_apply::"('a::linorder, 'b::zero) slist \<Rightarrow> 'a \<Rightarrow> 'b" is
  "\<lambda>xs i. the_default 0 (map_of xs i)" .

lemma compute_pdevs_apply[code]: "pdevs_apply (Pdevs x) i = slist_apply x i"
  by transfer (auto simp: Pdevs_raw_def)


subsection \<open>Total Deviation\<close>

lift_definition tdev_slist::"(nat, 'a::ordered_euclidean_space) slist \<Rightarrow> 'a" is
  "sum_list o map (abs o snd)" .

lemma tdev_slist_sum: "tdev_slist xs = sum (abs \<circ> snd) (set_slist xs)"
  by transfer (auto simp: distinct_map sum_list_distinct_conv_sum_set[symmetric] o_def)

lemma pdevs_apply_set_slist: "x \<in> set_slist xs \<Longrightarrow> snd x = pdevs_apply (Pdevs xs) (fst x)"
  by transfer (auto simp: Pdevs_raw_def)

lemma
  tdev_list_eq_zeroI:
  shows "(\<And>i. pdevs_apply (Pdevs xs) i = 0) \<Longrightarrow> tdev_slist xs = 0"
  unfolding tdev_slist_sum
  by (auto simp: pdevs_apply_set_slist)

lemma inj_on_fst_set_slist: "inj_on fst (set_slist xs)"
  by transfer (simp add: distinct_map)

lemma pdevs_apply_Pdevs_eq_0:
  "pdevs_apply (Pdevs xs) i = 0 \<longleftrightarrow> ((\<forall>x. (i, x) \<in> set_slist xs \<longrightarrow> x = 0))"
  by transfer (safe, auto simp: Pdevs_raw_def split: option.split)

lemma compute_tdev[code]: "tdev (Pdevs xs) = tdev_slist xs"
proof -
  have "tdev (Pdevs xs) = (\<Sum>i<degree (Pdevs xs). \<bar>pdevs_apply (Pdevs xs) i\<bar>)"
    by (simp add: tdev_def)
  also have "\<dots> =
    (\<Sum>i <degree (Pdevs xs).
      if pdevs_apply (Pdevs xs) i = 0 then 0 else \<bar>pdevs_apply (Pdevs xs) i\<bar>)"
    by (auto intro!: sum.cong)
  also have "\<dots> =
    (\<Sum>i\<in>{0..<degree (Pdevs xs)} \<inter> {x. pdevs_apply (Pdevs xs) x \<noteq> 0}.
      \<bar>pdevs_apply (Pdevs xs) i\<bar>)"
    by (auto simp: sum.If_cases Collect_neg_eq atLeast0LessThan)
  also have "\<dots> = (\<Sum>x\<in>fst ` set_slist xs. \<bar>pdevs_apply (Pdevs xs) x\<bar>)"
    by (rule sum.mono_neutral_cong_left)
      (force simp: pdevs_apply_Pdevs_eq_0 intro!: imageI degree_gt)+
  also have "\<dots> = (\<Sum>x\<in>set_slist xs. \<bar>pdevs_apply (Pdevs xs) (fst x)\<bar>)"
    by (rule sum.reindex_cong[of fst]) (auto simp: inj_on_fst_set_slist)
  also have "\<dots> = tdev_slist xs"
    by (simp add: tdev_slist_sum pdevs_apply_set_slist)
  finally show ?thesis .
qed


subsection \<open>Minkowski Sum\<close>

lemma dropWhile_rsorted_eq_filter:
  "rsorted (map fst xs) \<Longrightarrow> dropWhile (\<lambda>(i, x). i \<ge> (m::nat)) xs = filter (\<lambda>(i, x). i < m) xs"
  (is "_ \<Longrightarrow> ?lhs xs = ?rhs xs")
proof (induct xs)
  case (Cons x xs)
  hence "?rhs (x#xs) = ?lhs (x#xs)"
    by (auto simp: sorted_append filter_id_conv intro: sym)
  thus ?case ..
qed simp

lift_definition msum_slist::"nat \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'a) slist"
  is "\<lambda>m xs ys. map (apfst (\<lambda>n. n + m)) ys @ dropWhile (\<lambda>(i, x). i \<ge> m) xs"
proof (safe, goal_cases)
  case (1 n l1 l2)
  then have "set (dropWhile (\<lambda>(i, x). n \<le> i) l1) \<subseteq> set l1"
    by (simp add: set_dropWhileD subrelI)
  with 1 show ?case
    by (auto simp add: distinct_map add.commute [of _ n] intro!: comp_inj_on intro: subset_inj_on)
      (simp add: dropWhile_rsorted_eq_filter)
next
  case prems: (2 n l1 l2)
  hence "sorted (map ((\<lambda>na. na + n) \<circ> fst) (rev l2))"
    by(simp add: sorted_iff_nth_mono rev_map)
  with prems show ?case
    by (auto simp: sorted_append dropWhile_rsorted_eq_filter rev_map rev_filter sorted_filter)
qed

lemma slist_apply_msum_slist:
  "slist_apply (msum_slist m xs ys) i =
    (if i < m then slist_apply xs i else slist_apply ys (i - m))"
proof (transfer, goal_cases)
  case prems: (1 m xs ys i)
  thus ?case
  proof (cases "i \<in> dom (map_of (map (\<lambda>(x, y). (x + m, y)) ys))")
    case False
    have "\<And>a. i < m \<Longrightarrow> i \<notin> fst ` {x \<in> set xs. case x of (i, x) \<Rightarrow> i < m} \<Longrightarrow> (i, a) \<notin> set xs"
      "\<And>a. i \<notin> fst ` set xs \<Longrightarrow> (i, a) \<notin> set xs"
      "\<And>a. m \<le> i \<Longrightarrow> i \<notin> fst ` (\<lambda>(x, y). (x + m, y)) ` set ys \<Longrightarrow> (i - m, a) \<notin> set ys"
       by force+
    thus ?thesis
      using prems False
      by (auto simp add: dropWhile_rsorted_eq_filter map_of_eq_None_iff distinct_map_fst_snd_eqD
        split: option.split dest!: map_of_SomeD)
  qed (force simp: map_of_eq_None_iff distinct_map_fst_snd_eqD
    split: option.split
    dest!: map_of_SomeD)
qed

lemma pdevs_apply_msum_slist:
  "pdevs_apply (Pdevs (msum_slist m xs ys)) i =
    (if i < m then pdevs_apply (Pdevs xs) i else pdevs_apply (Pdevs ys) (i - m))"
  by (auto simp: compute_pdevs_apply slist_apply_msum_slist)

lemma compute_msum_pdevs[code]: "msum_pdevs m (Pdevs xs) (Pdevs ys) = Pdevs (msum_slist m xs ys)"
  by (rule pdevs_eqI) (auto simp: pdevs_apply_msum_slist pdevs_apply_msum_pdevs)


subsection \<open>Unary Operations\<close>

lift_definition map_slist::"('a \<Rightarrow> 'b) \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'b) slist" is "\<lambda>f. map (apsnd f)"
  by simp

lemma pdevs_apply_map_slist:
  "f 0 = 0 \<Longrightarrow> pdevs_apply (Pdevs (map_slist f xs)) i = f (pdevs_apply (Pdevs xs) i)"
  by transfer
    (force simp: Pdevs_raw_def map_of_eq_None_iff distinct_map_fst_snd_eqD image_def
      split: option.split dest: distinct_map_fst_snd_eqD)

lemma compute_scaleR_pdves[code]: "scaleR_pdevs r (Pdevs xs) = Pdevs (map_slist (\<lambda>x. r *\<^sub>R x) xs)"
  and compute_pdevs_scaleR[code]: "pdevs_scaleR (Pdevs rs) x = Pdevs (map_slist (\<lambda>r. r *\<^sub>R x) rs)"
  and compute_uminus_pdevs[code]: "uminus_pdevs (Pdevs xs) = Pdevs (map_slist (\<lambda>x. - x) xs)"
  and compute_abs_pdevs[code]: "abs_pdevs (Pdevs xs) = Pdevs (map_slist abs xs)"
  and compute_pdevs_inner[code]: "pdevs_inner (Pdevs xs) b = Pdevs (map_slist (\<lambda>x. x \<bullet> b) xs)"
  and compute_pdevs_inner2[code]:
    "pdevs_inner2 (Pdevs xs) b c = Pdevs (map_slist (\<lambda>x. (x \<bullet> b, x \<bullet> c)) xs)"
  and compute_inner_scaleR_pdevs[code]:
    "inner_scaleR_pdevs x (Pdevs ys) = Pdevs (map_slist (\<lambda>y. (x \<bullet> y) *\<^sub>R y) ys)"
  and compute_trunc_pdevs[code]:
    "trunc_pdevs p (Pdevs xs) = Pdevs (map_slist (\<lambda>x. eucl_truncate_down p x) xs)"
  and compute_trunc_err_pdevs[code]:
    "trunc_err_pdevs p (Pdevs xs) = Pdevs (map_slist (\<lambda>x. eucl_truncate_down p x - x) xs)"
  by (auto intro!: pdevs_eqI simp: pdevs_apply_map_slist zero_prod_def abs_pdevs_def)

  
subsection \<open>Filter\<close>

lift_definition filter_slist::"(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'a) slist"
  is "\<lambda>P xs. filter (\<lambda>(i, x). (P i x)) xs"
  by (auto simp: o_def filter_map distinct_map rev_map rev_filter sorted_filter
    intro: subset_inj_on)

lemma slist_apply_filter_slist: "slist_apply (filter_slist P xs) i =
  (if P i (slist_apply xs i) then slist_apply xs i else 0)"
  by transfer (force simp: Pdevs_raw_def o_def map_of_eq_None_iff distinct_map_fst_snd_eqD
    dest: map_of_SomeD distinct_map_fst_snd_eqD split: option.split)

lemma pdevs_apply_filter_slist: "pdevs_apply (Pdevs (filter_slist P xs)) i =
  (if P i (pdevs_apply (Pdevs xs) i) then pdevs_apply (Pdevs xs) i else 0)"
  by (simp add: compute_pdevs_apply slist_apply_filter_slist)

lemma compute_filter_pdevs[code]: "filter_pdevs P (Pdevs xs) = Pdevs (filter_slist P xs)"
  by (auto simp: pdevs_apply_filter_slist intro!: pdevs_eqI)


subsection \<open>Constant\<close>

lift_definition zero_slist::"(nat, 'a) slist" is "[]" by simp

lemma compute_zero_pdevs[code]: "zero_pdevs = Pdevs (zero_slist)"
  by transfer (auto simp: Pdevs_raw_def)

lift_definition One_slist::"(nat, 'a::executable_euclidean_space) slist"
  is "rev (zip [0..<length (Basis_list::'a list)] (Basis_list::'a list))"
  by (simp add: zip_rev[symmetric])

lemma
  map_of_rev_zip_upto_length_eq_nth:
  assumes "i < length B" "d = length B"
  shows "(map_of (rev (zip [0..<d] B)) i) = Some (B ! i)"
proof -
  have "length (rev [0..<length B]) = length (rev B)"
    by simp
  from map_of_zip_is_Some[OF this, of i] assms
  obtain y where y: "map_of (zip (rev [0..<length B]) (rev B)) i = Some y"
    by (auto simp: zip_rev)
  hence "y = B ! i"
    by (auto simp: in_set_zip rev_nth)
  with y show ?thesis
    by (simp add: zip_rev assms)
qed

lemma
  map_of_rev_zip_upto_length_eq_None:
  assumes "\<not>i < length B"
  assumes "d = length B"
  shows "(map_of (rev (zip [0..<d] B)) i) = None"
  using assms
  by (auto simp: map_of_eq_None_iff in_set_zip)

lemma pdevs_apply_One_slist:
  "pdevs_apply (Pdevs One_slist) i =
    (if i < length (Basis_list::'a::executable_euclidean_space list)
    then (Basis_list::'a list) ! i
    else 0)"
  by transfer (auto simp: Pdevs_raw_def map_of_rev_zip_upto_length_eq_nth map_of_rev_zip_upto_length_eq_None
      in_set_zip split: option.split)
  
lemma compute_One_pdevs[code]: "One_pdevs = Pdevs One_slist"
  by (rule pdevs_eqI) (simp add: pdevs_apply_One_slist)

lift_definition coord_slist::"nat \<Rightarrow> (nat, real) slist" is "\<lambda>i. [(i, 1)]" by simp

lemma compute_coord_pdevs[code]: "coord_pdevs i = Pdevs (coord_slist i)"
  by transfer (auto simp: Pdevs_raw_def)


subsection \<open>Update\<close>

primrec update_list::"nat \<Rightarrow> 'a \<Rightarrow> (nat * 'a) list \<Rightarrow> (nat * 'a) list"
  where
  "update_list n x [] = [(n, x)]"
| "update_list n x (y#ys) =
    (if n > fst y then (n, x)#y#ys
    else if n = fst y then (n, x)#ys
    else y#(update_list n x ys))"

lemma map_of_update_list[simp]: "map_of (update_list n x ys) = (map_of ys)(n:=Some x)"
  by (induct ys) auto

lemma in_set_update_listD:
  assumes "y \<in> set (update_list n x ys)"
  shows "y = (n, x) \<or> (y \<in> set ys)"
  using assms
  by (induct ys) (auto split: if_split_asm)

lemma in_set_update_listI:
  "y = (n, x) \<or> (fst y \<noteq> n \<and> y \<in> set ys) \<Longrightarrow> y \<in> set (update_list n x ys)"
  by (induct ys) (auto split: if_split_asm)

lemma in_set_update_list: "(n, x) \<in> set (update_list n x xs)"
  by (induct xs) simp_all

lemma overwrite_update_list: "(a, b) \<in> set xs \<Longrightarrow> (a, b) \<notin> set (update_list n x xs) \<Longrightarrow> a = n"
  by (induct xs) (auto split: if_split_asm)

lemma insert_update_list:
  "distinct (map fst xs) \<Longrightarrow> rsorted (map fst xs) \<Longrightarrow> (a, b) \<in> set (update_list a x xs) \<Longrightarrow> b = x"
  by (induct xs) (force split: if_split_asm simp: sorted_append)+

lemma set_update_list_eq: "distinct (map fst xs) \<Longrightarrow> rsorted (map fst xs) \<Longrightarrow>
    set (update_list n x xs) = insert (n, x) (set xs - {x. fst x = n})"
  by (auto intro!: in_set_update_listI dest: in_set_update_listD simp: insert_update_list)

lift_definition update_slist::"nat \<Rightarrow> 'a \<Rightarrow> (nat, 'a) slist \<Rightarrow> (nat, 'a) slist" is update_list
proof goal_cases
  case (1 n a l)
  thus ?case
    by (induct l) (force simp: sorted_append distinct_map not_less dest!: in_set_update_listD)+
qed

lemma pdevs_apply_update_slist: "pdevs_apply (Pdevs (update_slist n x xs)) i =
  (if i = n then x else pdevs_apply (Pdevs xs) i)"
  by transfer (auto simp: Pdevs_raw_def)

lemma compute_pdev_upd[code]: "pdev_upd (Pdevs xs) n x = Pdevs (update_slist n x xs)"
  by (rule pdevs_eqI) (auto simp: pdevs_apply_update_slist)


subsection \<open>Approximate Total Deviation\<close>

lift_definition fold_slist::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (nat, 'a::zero) slist \<Rightarrow> 'b \<Rightarrow> 'b"
  is "\<lambda>f xs z. fold (f o snd) (filter (\<lambda>x. snd x \<noteq> 0) xs) z" .

lemma Pdevs_raw_Cons:
  "Pdevs_raw ((a, b) # xs) = (\<lambda>i. if i = a then b else Pdevs_raw xs i)"
  by (auto simp: Pdevs_raw_def map_of_eq_None_iff
    dest!: map_of_SomeD
    split: option.split)

lemma zeros_aux: "- (\<lambda>i. if i = a then b else Pdevs_raw xs i) -` {0} \<subseteq>
  - Pdevs_raw xs -` {0} \<union> {a}"
  by auto

lemma compute_tdev'[code]:
  "tdev' p (Pdevs xs) = fold_slist (\<lambda>a b. eucl_truncate_up p (\<bar>a\<bar> + b)) xs 0"
  unfolding tdev'_def sum_list'_def compute_list_of_pdevs
  by transfer (auto simp: o_def fold_map)

subsection \<open>Equality\<close>

lemma slist_apply_list_of_slist_eq: "slist_apply a i = the_default 0 (map_of (list_of_slist a) i)"
  by (transfer)
    (force split: option.split simp: map_of_eq_None_iff distinct_map_fst_snd_eqD
      dest!: map_of_SomeD)

lemma compute_equal_pdevs[code]:
  "equal_class.equal (Pdevs a) (Pdevs b) \<longleftrightarrow> (list_of_slist a) = (list_of_slist b)"
  by (auto intro!: pdevs_eqI simp: equal_pdevs_def compute_pdevs_apply slist_apply_list_of_slist_eq
    compute_list_of_pdevs[symmetric])


subsection \<open>From List of Generators\<close>

lift_definition slist_of_list::"'a::zero list \<Rightarrow> (nat, 'a) slist"
  is "\<lambda>xs. rev (zip [0..<length xs] xs)"
  by (auto simp: rev_map[symmetric] )

lemma slist_apply_slist_of_list:
  "slist_apply (slist_of_list xs) i = (if i < length xs then xs ! i else 0)"
  by transfer (auto simp: in_set_zip map_of_rev_zip_upto_length_eq_nth map_of_rev_zip_upto_length_eq_None)

lemma compute_pdevs_of_list[code]: "pdevs_of_list xs = Pdevs (slist_of_list xs)"
  by (rule pdevs_eqI)
    (auto simp: compute_pdevs_apply slist_apply_slist_of_list pdevs_apply_pdevs_of_list)

text \<open>abstraction function which can be used in code equations\<close>

lift_definition abs_slist_if::"('a::linorder\<times>'b) list \<Rightarrow> ('a, 'b) slist"
  is "\<lambda>list. if distinct (map fst list) \<and> rsorted (map fst list) then list else []"
  by auto

definition "slist = Abs_slist"

lemma [code_post]: "Abs_slist = slist"
  by (simp add: slist_def)

lemma [code]: "slist = (\<lambda>xs.
  (if distinct (map fst xs) \<and> rsorted (map fst xs) then abs_slist_if xs else Code.abort (STR '''') (\<lambda>_. slist xs)))"
  by (auto simp add: slist_def abs_slist_if.abs_eq)

abbreviation "pdevs \<equiv> (\<lambda>x. Pdevs (slist x))"

lift_definition nlex_slist::"(nat, point) slist \<Rightarrow> (nat, point) slist" is
  "map (\<lambda>(i, x). (i, if lex 0 x then - x else x))"
  by (auto simp: o_def split_beta')

lemma Pdevs_raw_map: "f 0 = 0 \<Longrightarrow> Pdevs_raw (map (\<lambda>(i, x). (i, f x)) xs) i = f (Pdevs_raw xs i)"
  by (auto simp: Pdevs_raw_def map_of_map split: option.split)

lemma compute_nlex_pdevs[code]: "nlex_pdevs (Pdevs x) = Pdevs (nlex_slist x)"
  by transfer (auto simp: Pdevs_raw_map)

end
