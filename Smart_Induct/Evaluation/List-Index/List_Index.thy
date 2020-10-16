(* Author: Tobias Nipkow, with contributions from Dmitriy Traytel, Lukas Bulwahn, and Peter Lammich *)

section \<open>Index-based manipulation of lists\<close>

theory List_Index imports Main begin

text \<open>\noindent
This theory collects functions for index-based manipulation of lists.
\<close>

subsection \<open>Finding an index\<close>

text \<open>
This subsection defines three functions for finding the index of items in a list:
\begin{description}
\item[\<open>find_index P xs\<close>] finds the index of the first element in
 \<open>xs\<close> that satisfies \<open>P\<close>.
\item[\<open>index xs x\<close>] finds the index of the first occurrence of
 \<open>x\<close> in \<open>xs\<close>.
\item[\<open>last_index xs x\<close>] finds the index of the last occurrence of
 \<open>x\<close> in \<open>xs\<close>.
\end{description}
All functions return @{term "length xs"} if \<open>xs\<close> does not contain a
suitable element.

The argument order of \<open>find_index\<close> follows the function of the same
name in the Haskell standard library. For \<open>index\<close> (and \<open>last_index\<close>) the order is intentionally reversed: \<open>index\<close> maps
lists to a mapping from elements to their indices, almost the inverse of
function \<open>nth\<close>.\<close>

primrec find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"find_index _ [] = 0" |
"find_index P (x#xs) = (if P x then 0 else find_index P xs + 1)"

definition index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index xs = (\<lambda>a. find_index (\<lambda>x. x=a) xs)"

definition last_index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"last_index xs x =
 (let i = index (rev xs) x; n = size xs
  in if i = n then i else n - (i+1))"

lemma find_index_append: "find_index P (xs @ ys) =
  (if \<exists>x\<in>set xs. P x then find_index P xs else size xs + find_index P ys)"
  by (induct xs) simp_all
  
lemma find_index_le_size: "find_index P xs <= size xs"
by(induct xs) simp_all

lemma index_le_size: "index xs x <= size xs"
by(simp add: index_def find_index_le_size)

lemma last_index_le_size: "last_index xs x <= size xs"
by(simp add: last_index_def Let_def index_le_size)

lemma index_Nil[simp]: "index [] a = 0"
by(simp add: index_def)

lemma index_Cons[simp]: "index (x#xs) a = (if x=a then 0 else index xs a + 1)"
by(simp add: index_def)

lemma index_append: "index (xs @ ys) x =
  (if x : set xs then index xs x else size xs + index ys x)"
by (induct xs) simp_all

lemma index_conv_size_if_notin[simp]: "x \<notin> set xs \<Longrightarrow> index xs x = size xs"
by (induct xs) auto

lemma find_index_eq_size_conv:
  "size xs = n \<Longrightarrow> (find_index P xs = n) = (\<forall>x \<in> set xs. ~ P x)"
by(induct xs arbitrary: n) auto

lemma size_eq_find_index_conv:
  "size xs = n \<Longrightarrow> (n = find_index P xs) = (\<forall>x \<in> set xs. ~ P x)"
by(metis find_index_eq_size_conv)

lemma index_size_conv: "size xs = n \<Longrightarrow> (index xs x = n) = (x \<notin> set xs)"
by(auto simp: index_def find_index_eq_size_conv)

lemma size_index_conv: "size xs = n \<Longrightarrow> (n = index xs x) = (x \<notin> set xs)"
by (metis index_size_conv)

lemma last_index_size_conv:
  "size xs = n \<Longrightarrow> (last_index xs x = n) = (x \<notin> set xs)"
apply(auto simp: last_index_def index_size_conv)
apply(drule length_pos_if_in_set)
apply arith
done

lemma size_last_index_conv:
  "size xs = n \<Longrightarrow> (n = last_index xs x) = (x \<notin> set xs)"
by (metis last_index_size_conv)

lemma find_index_less_size_conv:
  "(find_index P xs < size xs) = (\<exists>x \<in> set xs. P x)"
by (induct xs) auto

lemma index_less_size_conv:
  "(index xs x < size xs) = (x \<in> set xs)"
by(auto simp: index_def find_index_less_size_conv)

lemma last_index_less_size_conv:
  "(last_index xs x < size xs) = (x : set xs)"
by(simp add: last_index_def Let_def index_size_conv length_pos_if_in_set
        del:length_greater_0_conv)

lemma index_less[simp]:
  "x : set xs \<Longrightarrow> size xs <= n \<Longrightarrow> index xs x < n"
apply(induct xs) apply auto
apply (metis index_less_size_conv less_eq_Suc_le less_trans_Suc)
done

lemma last_index_less[simp]:
  "x : set xs \<Longrightarrow> size xs <= n \<Longrightarrow> last_index xs x < n"
by(simp add: last_index_less_size_conv[symmetric])

lemma last_index_Cons: "last_index (x#xs) y =
  (if x=y then
      if x \<in> set xs then last_index xs y + 1 else 0
   else last_index xs y + 1)"
using index_le_size[of "rev xs" y]
apply(auto simp add: last_index_def index_append Let_def)
apply(simp add: index_size_conv)
done

lemma last_index_append: "last_index (xs @ ys) x =
  (if x : set ys then size xs + last_index ys x
   else if x : set xs then last_index xs x else size xs + size ys)"
by (induct xs) (simp_all add: last_index_Cons last_index_size_conv)

lemma last_index_Snoc[simp]:
  "last_index (xs @ [x]) y =
  (if x=y then size xs
   else if y : set xs then last_index xs y else size xs + 1)"
by(simp add: last_index_append last_index_Cons)

lemma nth_find_index: "find_index P xs < size xs \<Longrightarrow> P(xs ! find_index P xs)"
by (induct xs) auto

lemma nth_index[simp]: "x \<in> set xs \<Longrightarrow> xs ! index xs x = x"
by (induct xs) auto

lemma nth_last_index[simp]: "x \<in> set xs \<Longrightarrow> xs ! last_index xs x = x"
by(simp add:last_index_def index_size_conv Let_def rev_nth[symmetric])

lemma index_rev: "\<lbrakk> distinct xs; x \<in> set xs \<rbrakk> \<Longrightarrow>
  index (rev xs) x = length xs - index xs x - 1"
by (induct xs) (auto simp: index_append)

lemma index_nth_id:
  "\<lbrakk> distinct xs;  n < length xs \<rbrakk> \<Longrightarrow> index xs (xs ! n) = n"
by (metis in_set_conv_nth index_less_size_conv nth_eq_iff_index_eq nth_index)

lemma index_upt[simp]: "m \<le> i \<Longrightarrow> i < n \<Longrightarrow> index [m..<n] i = i-m"
by (induction n) (auto simp add: index_append)

lemma index_eq_index_conv[simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow>
  (index xs x = index xs y) = (x = y)"
by (induct xs) auto

lemma last_index_eq_index_conv[simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow>
  (last_index xs x = last_index xs y) = (x = y)"
by (induct xs) (auto simp:last_index_Cons)

lemma inj_on_index: "inj_on (index xs) (set xs)"
by (simp add:inj_on_def)

lemma inj_on_index2: "I \<subseteq> set xs \<Longrightarrow> inj_on (index xs) I"
by (rule inj_onI) auto

lemma inj_on_last_index: "inj_on (last_index xs) (set xs)"
by (simp add:inj_on_def)

lemma find_index_conv_takeWhile: 
  "find_index P xs = size(takeWhile (Not o P) xs)"
by(induct xs) auto

lemma index_conv_takeWhile: "index xs x = size(takeWhile (\<lambda>y. x\<noteq>y) xs)"
by(induct xs) auto

lemma find_index_first: "i < find_index P xs \<Longrightarrow> \<not>P (xs!i)"
unfolding find_index_conv_takeWhile
by (metis comp_apply nth_mem set_takeWhileD takeWhile_nth)

lemma index_first: "i<index xs x \<Longrightarrow> x\<noteq>xs!i"
using find_index_first unfolding index_def by blast

lemma find_index_eqI:
  assumes "i\<le>length xs"  
  assumes "\<forall>j<i. \<not>P (xs!j)"
  assumes "i<length xs \<Longrightarrow> P (xs!i)"
  shows "find_index P xs = i"
by (metis (mono_tags, lifting) antisym_conv2 assms find_index_eq_size_conv 
  find_index_first find_index_less_size_conv linorder_neqE_nat nth_find_index)
  
lemma find_index_eq_iff:
  "find_index P xs = i 
  \<longleftrightarrow> (i\<le>length xs \<and> (\<forall>j<i. \<not>P (xs!j)) \<and> (i<length xs \<longrightarrow> P (xs!i)))"  
by (auto intro: find_index_eqI 
         simp: nth_find_index find_index_le_size find_index_first)
  
lemma index_eqI:
  assumes "i\<le>length xs"  
  assumes "\<forall>j<i. xs!j \<noteq> x"
  assumes "i<length xs \<Longrightarrow> xs!i = x"
  shows "index xs x = i"
unfolding index_def by (simp add: find_index_eqI assms)
  
lemma index_eq_iff:
  "index xs x = i 
  \<longleftrightarrow> (i\<le>length xs \<and> (\<forall>j<i. xs!j \<noteq> x) \<and> (i<length xs \<longrightarrow> xs!i = x))"  
by (auto intro: index_eqI 
         simp: index_le_size index_less_size_conv 
         dest: index_first)

lemma index_take: "index xs x >= i \<Longrightarrow> x \<notin> set(take i xs)"
apply(subst (asm) index_conv_takeWhile)
apply(subgoal_tac "set(take i xs) <= set(takeWhile ((\<noteq>) x) xs)")
 apply(blast dest: set_takeWhileD)
apply(metis set_take_subset_set_take takeWhile_eq_take)
done

lemma last_index_drop:
  "last_index xs x < i \<Longrightarrow> x \<notin> set(drop i xs)"
apply(subgoal_tac "set(drop i xs) = set(take (size xs - i) (rev xs))")
 apply(simp add: last_index_def index_take Let_def split:if_split_asm)
apply (metis rev_drop set_rev)
done

lemma set_take_if_index: assumes "index xs x < i" and "i \<le> length xs"
shows "x \<in> set (take i xs)"
proof -
  have "index (take i xs @ drop i xs) x < i"
    using append_take_drop_id[of i xs] assms(1) by simp
  thus ?thesis using assms(2)
    by(simp add:index_append del:append_take_drop_id split: if_splits)
qed

lemma index_take_if_index:
assumes "index xs x \<le> n" shows "index (take n xs) x = index xs x"
proof cases
  assume "x : set(take n xs)" with assms show ?thesis
    by (metis append_take_drop_id index_append)
next
  assume "x \<notin> set(take n xs)" with assms show ?thesis
   by (metis order_le_less set_take_if_index le_cases length_take min_def size_index_conv take_all)
qed

lemma index_take_if_set:
  "x : set(take n xs) \<Longrightarrow> index (take n xs) x = index xs x"
by (metis index_take index_take_if_index linear)

lemma index_last[simp]:
  "xs \<noteq> [] \<Longrightarrow> distinct xs \<Longrightarrow> index xs (last xs) = length xs - 1"
by (induction xs) auto

lemma index_update_if_diff2:
  "n < length xs \<Longrightarrow> x \<noteq> xs!n \<Longrightarrow> x \<noteq> y \<Longrightarrow> index (xs[n := y]) x = index xs x"
by(subst (2) id_take_nth_drop[of n xs])
  (auto simp: upd_conv_take_nth_drop index_append min_def)

lemma set_drop_if_index: "distinct xs \<Longrightarrow> index xs x < i \<Longrightarrow> x \<notin> set(drop i xs)"
by (metis in_set_dropD index_nth_id last_index_drop last_index_less_size_conv nth_last_index)

lemma index_swap_if_distinct: assumes "distinct xs" "i < size xs" "j < size xs"
shows "index (xs[i := xs!j, j := xs!i]) x =
  (if x = xs!i then j else if x = xs!j then i else index xs x)"
proof-
  have "distinct(xs[i := xs!j, j := xs!i])" using assms by simp
  with assms show ?thesis
    apply (auto simp: swap_def simp del: distinct_swap)
    apply (metis index_nth_id list_update_same_conv)
    apply (metis (erased, hide_lams) index_nth_id length_list_update list_update_swap nth_list_update_eq)
    apply (metis index_nth_id length_list_update nth_list_update_eq)
    by (metis index_update_if_diff2 length_list_update nth_list_update)
qed

lemma bij_betw_index:
  "distinct xs \<Longrightarrow> X = set xs \<Longrightarrow> l = size xs \<Longrightarrow> bij_betw (index xs) X {0..<l}"
apply simp
apply(rule bij_betw_imageI[OF inj_on_index])
by (auto simp: image_def) (metis index_nth_id nth_mem)

lemma index_image: "distinct xs \<Longrightarrow> set xs = X \<Longrightarrow> index xs ` X = {0..<size xs}"
by (simp add: bij_betw_imp_surj_on bij_betw_index)

lemma index_map_inj_on:
  "\<lbrakk> inj_on f S; y \<in> S; set xs \<subseteq> S \<rbrakk> \<Longrightarrow> index (map f xs) (f y) = index xs y"
by (induct xs) (auto simp: inj_on_eq_iff)

lemma index_map_inj: "inj f \<Longrightarrow> index (map f xs) (f y) = index xs y"
by (simp add: index_map_inj_on[where S=UNIV])

subsection \<open>Map with index\<close>

primrec map_index' :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_index' n f [] = []"
| "map_index' n f (x#xs) = f n x # map_index' (Suc n) f xs"

lemma length_map_index'[simp]: "length (map_index' n f xs) = length xs"
  by (induct xs arbitrary: n) auto

lemma map_index'_map_zip: "map_index' n f xs = map (case_prod f) (zip [n ..< n + length xs] xs)"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  hence "map_index' n f (x#xs) = f n x # map (case_prod f) (zip [Suc n ..< n + length (x # xs)] xs)" by simp
  also have "\<dots> =  map (case_prod f) (zip (n # [Suc n ..< n + length (x # xs)]) (x # xs))" by simp
  also have "(n # [Suc n ..< n + length (x # xs)]) = [n ..< n + length (x # xs)]" by (induct xs) auto
  finally show ?case by simp
qed simp

abbreviation "map_index \<equiv> map_index' 0"

lemmas map_index = map_index'_map_zip[of 0, simplified]

lemma take_map_index: "take p (map_index f xs) = map_index f (take p xs)"
  unfolding map_index by (auto simp: min_def take_map take_zip)

lemma drop_map_index: "drop p (map_index f xs) = map_index' p f (drop p xs)"
  unfolding map_index'_map_zip by (cases "p < length xs") (auto simp: drop_map drop_zip)

lemma map_map_index[simp]: "map g (map_index f xs) = map_index (\<lambda>n x. g (f n x)) xs"
  unfolding map_index by auto

lemma map_index_map[simp]: "map_index f (map g xs) = map_index (\<lambda>n x. f n (g x)) xs"
  unfolding map_index by (auto simp: map_zip_map2)

lemma set_map_index[simp]: "x \<in> set (map_index f xs) = (\<exists>i < length xs. f i (xs ! i) = x)"
  unfolding map_index by (auto simp: set_zip intro!: image_eqI[of _ "case_prod f"])

lemma set_map_index'[simp]: "x\<in>set (map_index' n f xs)
  \<longleftrightarrow> (\<exists>i<length xs. f (n+i) (xs!i) = x) "
  unfolding map_index'_map_zip
  by (auto simp: set_zip intro!: image_eqI[of _ "case_prod f"])

lemma nth_map_index[simp]: "p < length xs \<Longrightarrow> map_index f xs ! p = f p (xs ! p)"
  unfolding map_index by auto

lemma map_index_cong:
  "\<forall>p < length xs. f p (xs ! p) = g p (xs ! p) \<Longrightarrow> map_index f xs = map_index g xs"
  unfolding map_index by (auto simp: set_zip)

lemma map_index_id: "map_index (curry snd) xs = xs"
  unfolding map_index by auto

lemma map_index_no_index[simp]: "map_index (\<lambda>n x. f x) xs = map f xs"
  unfolding map_index by (induct xs rule: rev_induct) auto

lemma map_index_congL:
  "\<forall>p < length xs. f p (xs ! p) = xs ! p \<Longrightarrow> map_index f xs = xs"
  by (rule trans[OF map_index_cong map_index_id]) auto

lemma map_index'_is_NilD: "map_index' n f xs = [] \<Longrightarrow> xs = []"
  by (induct xs) auto

declare map_index'_is_NilD[of 0, dest!]

lemma map_index'_is_ConsD:
  "map_index' n f xs = y # ys \<Longrightarrow> \<exists>z zs. xs = z # zs \<and> f n z = y \<and> map_index' (n + 1) f zs = ys"
  by (induct xs arbitrary: n) auto

lemma map_index'_eq_imp_length_eq: "map_index' n f xs = map_index' n g ys \<Longrightarrow> length xs = length ys"
proof (induct ys arbitrary: xs n)
  case (Cons y ys) thus ?case by (cases xs) auto
qed (auto dest!: map_index'_is_NilD)

lemmas map_index_eq_imp_length_eq = map_index'_eq_imp_length_eq[of 0]

lemma map_index'_comp[simp]: "map_index' n f (map_index' n g xs) = map_index' n (\<lambda>n. f n o g n) xs"
  by (induct xs arbitrary: n) auto

lemma map_index'_append[simp]: "map_index' n f (a @ b)
  = map_index' n f a @ map_index' (n + length a) f b"
  by (induct a arbitrary: n) auto

lemma map_index_append[simp]: "map_index f (a @ b)
  = map_index f a @ map_index' (length a) f b"
  using map_index'_append[where n=0]
  by (simp del: map_index'_append)


subsection \<open>Insert at position\<close>

primrec insert_nth :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_nth 0 x xs = x # xs"
| "insert_nth (Suc n) x xs = (case xs of [] \<Rightarrow> [x] | y # ys \<Rightarrow> y # insert_nth n x ys)"

lemma insert_nth_take_drop[simp]: "insert_nth n x xs = take n xs @ [x] @ drop n xs"
proof (induct n arbitrary: xs)
  case Suc thus ?case by (cases xs) auto
qed simp

lemma length_insert_nth: "length (insert_nth n x xs) = Suc (length xs)"
  by (induct xs) auto

lemma set_insert_nth:
  "set (insert_nth i x xs) = insert x (set xs)"
by (simp add: set_append[symmetric])

lemma distinct_insert_nth:
  assumes "distinct xs"
  assumes "x \<notin> set xs"
  shows "distinct (insert_nth i x xs)"
using assms proof (induct xs arbitrary: i)
  case Nil
  then show ?case by (cases i) auto
next
  case (Cons a xs)
  then show ?case
    by (cases i) (auto simp add: set_insert_nth simp del: insert_nth_take_drop)
qed

lemma nth_insert_nth_front:
  assumes "i < j" "j \<le> length xs"
  shows "insert_nth j x xs ! i = xs ! i"
using assms by (simp add: nth_append)

lemma nth_insert_nth_index_eq:
  assumes "i \<le> length xs"
  shows "insert_nth i x xs ! i = x"
using assms by (simp add: nth_append)

lemma nth_insert_nth_back:
  assumes "j < i" "i \<le> length xs"
  shows "insert_nth j x xs ! i = xs ! (i - 1)"
using assms by (cases i) (auto simp add: nth_append min_def)

lemma nth_insert_nth:
  assumes "i \<le> length xs" "j \<le> length xs"
  shows "insert_nth j x xs ! i = (if i = j then x else if i < j then xs ! i else xs ! (i - 1))"
using assms by (simp add: nth_insert_nth_front nth_insert_nth_index_eq nth_insert_nth_back del: insert_nth_take_drop)

lemma insert_nth_inverse:
  assumes "j \<le> length xs" "j' \<le> length xs'"
  assumes "x \<notin> set xs" "x \<notin> set xs'"
  assumes "insert_nth j x xs = insert_nth j' x xs'"
  shows "j = j'"
proof -
  from assms(1,3) have "\<forall>i\<le>length xs. insert_nth j x xs ! i = x \<longleftrightarrow> i = j"
    by (auto simp add: nth_insert_nth simp del: insert_nth_take_drop)
  moreover from assms(2,4) have "\<forall>i\<le>length xs'. insert_nth j' x xs' ! i = x \<longleftrightarrow> i = j'"
    by (auto simp add: nth_insert_nth simp del: insert_nth_take_drop)
  ultimately show "j = j'"
    using assms(1,2,5) by (metis dual_order.trans nat_le_linear)
qed

text \<open>Insert several elements at given (ascending) positions\<close>

lemma length_fold_insert_nth:
  "length (fold (\<lambda>(p, b). insert_nth p b) pxs xs) = length xs + length pxs"
  by (induct pxs arbitrary: xs) auto

lemma invar_fold_insert_nth:
  "\<lbrakk>\<forall>x\<in>set pxs. p < fst x; p < length xs; xs ! p = b\<rbrakk> \<Longrightarrow>
    fold (\<lambda>(x, y). insert_nth x y) pxs xs ! p = b"
  by (induct pxs arbitrary: xs) (auto simp: nth_append)

lemma nth_fold_insert_nth:
  "\<lbrakk>sorted (map fst pxs); distinct (map fst pxs); \<forall>(p, b) \<in> set pxs. p < length xs + length pxs;
    i < length pxs; pxs ! i = (p, b)\<rbrakk> \<Longrightarrow>
  fold (\<lambda>(p, b). insert_nth p b) pxs xs ! p = b"
proof (induct pxs arbitrary: xs i p b)
  case (Cons pb pxs)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems have "p < Suc (length xs)"
    proof (induct pxs rule: rev_induct)
      case (snoc pb' pxs)
      then obtain p' b' where "pb' = (p', b')" by auto
      with snoc.prems have "\<forall>p \<in> fst ` set pxs. p < p'" "p' \<le> Suc (length xs + length pxs)"
        by (auto simp: image_iff sorted_append le_eq_less_or_eq)
      with snoc.prems show ?case by (intro snoc(1)) (auto simp: sorted_append)
    qed auto
    with 0 Cons.prems show ?thesis unfolding fold.simps o_apply
    by (intro invar_fold_insert_nth) (auto simp: image_iff le_eq_less_or_eq nth_append)
  next
    case (Suc n) with Cons.prems show ?thesis unfolding fold.simps
      by (auto intro!: Cons(1))
  qed
qed simp

subsection \<open>Remove at position\<close>

fun remove_nth :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove_nth i [] = []"
| "remove_nth 0 (x # xs) = xs"
| "remove_nth (Suc i) (x # xs) = x # remove_nth i xs"

lemma remove_nth_take_drop:
  "remove_nth i xs = take i xs @ drop (Suc i) xs"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma remove_nth_insert_nth:
  assumes "i \<le> length xs"
  shows "remove_nth i (insert_nth i x xs) = xs"
using assms proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma insert_nth_remove_nth:
  assumes "i < length xs"
  shows "insert_nth i (xs ! i) (remove_nth i xs) = xs"
using assms proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma length_remove_nth:
  assumes "i < length xs"
  shows "length (remove_nth i xs) = length xs - 1"
using assms unfolding remove_nth_take_drop by simp

lemma set_remove_nth_subset:
  "set (remove_nth j xs) \<subseteq> set xs"
proof (induct xs arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases j) auto
qed

lemma set_remove_nth:
  assumes "distinct xs" "j < length xs"
  shows "set (remove_nth j xs) = set xs - {xs ! j}"
using assms proof (induct xs arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases j) auto
qed

lemma distinct_remove_nth:
  assumes "distinct xs"
  shows "distinct (remove_nth i xs)"
using assms proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases i) (auto simp add: set_remove_nth_subset rev_subsetD)
qed

end
