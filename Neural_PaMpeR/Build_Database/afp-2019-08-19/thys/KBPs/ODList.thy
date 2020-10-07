(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *
 * Based on Florian Haftmann's DList.thy and Tobias Nipkow's msort proofs.
 *)

theory ODList
imports
  "HOL-Library.Multiset"
  List_local
begin
(*>*)

text\<open>

Define a type of ordered distinct lists, intended to represent sets.

The advantage of this representation is that it is isomorphic to the
set of finite sets. Conversely it requires the carrier type to be a
linear order.  Note that this representation does not arise from a
quotient on lists: all the unsorted lists are junk.

\<close>

context linorder
begin

text\<open>

"Absorbing" msort, a variant of Tobias Nipkow's proofs from 1992.

\<close>

fun
  merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x#xs) (y#ys) =
    (if x = y then merge xs (y#ys)
             else if x < y then x # merge xs (y#ys)
                           else y # merge (x#xs) ys)"

(*<*)
lemma set_merge[simp]:
  "set (merge xs ys) = set (xs @ ys)"
  by (induct xs ys rule: merge.induct) auto

lemma distinct_sorted_merge[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> distinct (merge xs ys) \<and> sorted (merge xs ys)"
  by (induct xs ys rule: merge.induct) (auto)

lemma mset_merge [simp]:
  "\<lbrakk> distinct (xs @ ys) \<rbrakk> \<Longrightarrow> mset (merge xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)
(*>*)

text\<open>The "absorbing" sort itself.\<close>

fun msort :: "'a list \<Rightarrow> 'a list"
where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (size xs div 2) xs))
                    (msort (drop (size xs div 2) xs))"

(*<*)
lemma msort_distinct_sorted[simp]:
  "distinct (msort xs) \<and> sorted (msort xs)"
  by (induct xs rule: msort.induct) simp_all

lemma msort_set[simp]:
  "set (msort xs) = set xs"
  by (induct xs rule: msort.induct)
     (simp_all, metis List.set_simps(2) append_take_drop_id set_append) (* thankyou sledgehammer! *)

lemma msort_remdups[simp]:
  "remdups (msort xs) = msort xs"
  by simp

lemma msort_idle[simp]:
  "\<lbrakk> distinct xs; sorted xs \<rbrakk> \<Longrightarrow> msort xs = xs"
  by (rule map_sorted_distinct_set_unique[where f=id]) (auto simp: map.id)

lemma mset_msort[simp]:
  "distinct xs \<Longrightarrow> mset (msort xs) = mset xs"
  by (rule iffD1[OF set_eq_iff_mset_eq_distinct]) simp_all

lemma msort_sort[simp]:
  "distinct xs \<Longrightarrow> sort xs = msort xs"
  by (simp add: properties_for_sort)
(*>*)

end (* context linorder *)


section \<open>The @{term "odlist"} type\<close>

typedef (overloaded) ('a :: linorder) odlist = "{ x::'a list . sorted x \<and> distinct x }"
  morphisms toList odlist_Abs by (auto iff: sorted.simps(1))

lemma distinct_toList[simp]: "distinct (toList xs)"
  using toList by auto

lemma sorted_toList[simp]: "sorted (toList xs)"
  using toList by auto

text\<open>

Code generator voodoo: this is the constructor for the abstract type.

\<close>

definition
  ODList :: "('a :: linorder) list \<Rightarrow> 'a odlist"
where
  "ODList \<equiv> odlist_Abs \<circ> msort"

lemma toList_ODList:
  "toList (ODList xs) = msort xs"
  unfolding ODList_def
  by (simp add: odlist_Abs_inverse)

lemma ODList_toList[simp, code abstype]:
  "ODList (toList xs) = xs"
  unfolding ODList_def
  by (cases xs) (simp add: odlist_Abs_inverse)

text\<open>

Runtime cast from @{typ "'a list"} into @{typ "'a odlist"}. This is
just a renaming of @{term "ODList"} -- names are significant to the
code generator's abstract type machinery.

\<close>

definition
  fromList :: "('a :: linorder) list \<Rightarrow> 'a odlist"
where
  "fromList \<equiv> ODList"

lemma toList_fromList[code abstract]:
  "toList (fromList xs) = msort xs"
  unfolding fromList_def
  by (simp add: toList_ODList)

subsection\<open>Basic properties: equality, finiteness\<close>

(*<*)
declare toList_inject[iff]
(*>*)

instantiation odlist :: (linorder) equal
(*<*)
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> odlist_equal (toList A) (toList B)"

instance
  by standard (simp add: equal_odlist_def)

end
(*>*)

instance odlist :: ("{finite, linorder}") finite
(*<*)
proof
  let ?ol = "UNIV :: 'a odlist set"
  let ?s = "UNIV :: 'a set set"
  have "finite ?s" by simp
  moreover
  have "?ol \<subseteq> range (odlist_Abs \<circ> sorted_list_of_set)"
  proof
    fix x show "x \<in> range (odlist_Abs \<circ> sorted_list_of_set)"
      apply (cases x)
      apply (rule range_eqI[where x="set (toList x)"])
      apply (clarsimp simp: odlist_Abs_inject sorted_list_of_set_sort_remdups odlist_Abs_inverse distinct_remdups_id)
      done
  qed
  ultimately show "finite ?ol" by (blast intro: finite_surj)
qed
(*>*)

subsection\<open>Constants\<close>

definition
  empty :: "('a :: linorder) odlist"
where
  "empty \<equiv> ODList []"

lemma toList_empty[simp, code abstract]:
  "toList empty = []"
  unfolding empty_def by (simp add: toList_ODList)

subsection\<open>Operations\<close>

subsubsection\<open>toSet\<close>

definition
  toSet :: "('a :: linorder) odlist \<Rightarrow> 'a set"
where
  "toSet X = set (toList X)"

lemma toSet_empty[simp]:
  "toSet empty = {}"
  unfolding toSet_def empty_def by (simp add: toList_ODList)

lemma toSet_ODList[simp]:
  "\<lbrakk> distinct xs; sorted xs \<rbrakk> \<Longrightarrow> toSet (ODList xs) = set xs"
  unfolding toSet_def by (simp add: toList_ODList)

lemma toSet_fromList_set[simp]:
  "toSet (fromList xs) = set xs"
  unfolding toSet_def fromList_def
  by (simp add: toList_ODList)

lemma toSet_inj[intro, simp]: "inj toSet"
  apply (rule injI)
  unfolding toSet_def
  apply (case_tac x)
  apply (case_tac y)
  apply (auto iff: odlist_Abs_inject odlist_Abs_inverse sorted_distinct_set_unique)
  done

lemma toSet_eq_iff:
  "X = Y \<longleftrightarrow> toSet X = toSet Y"
  by (blast dest: injD[OF toSet_inj])

subsubsection\<open>head\<close>

definition
  hd :: "('a :: linorder) odlist \<Rightarrow> 'a"
where
  [code]: "hd \<equiv> List.hd \<circ> toList"

lemma hd_toList: "toList xs = y # ys \<Longrightarrow> ODList.hd xs = y"
  unfolding hd_def by simp

subsubsection\<open>member\<close>

definition
  member :: "('a :: linorder) odlist \<Rightarrow> 'a \<Rightarrow> bool"
where
  [code]: "member xs x \<equiv> List.member (toList xs) x"

lemma member_toSet[iff]:
  "member xs x \<longleftrightarrow>x \<in> toSet xs"
  unfolding member_def toSet_def by (simp add: in_set_member)

subsubsection\<open>Filter\<close>

definition
  filter :: "(('a :: linorder) \<Rightarrow> bool) \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "filter P xs \<equiv> ODList (List.filter P (toList xs))"

lemma toList_filter[simp, code abstract]:
  "toList (filter P xs) = List.filter P (toList xs)"
  unfolding filter_def by (simp add: toList_ODList)

lemma toSet_filter[simp]:
  "toSet (filter P xs) = { x \<in> toSet xs . P x }"
  unfolding filter_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection\<open>All\<close>

definition
  odlist_all :: "('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  [code]: "odlist_all P xs \<equiv> list_all P (toList xs)"

lemma odlist_all_iff:
  "odlist_all P xs \<longleftrightarrow> (\<forall>x \<in> toSet xs. P x)"
  unfolding odlist_all_def toSet_def by (simp only: list_all_iff)

lemma odlist_all_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> toSet ys \<Longrightarrow> f x = g x) \<Longrightarrow> odlist_all f xs = odlist_all g ys"
  by (simp add: odlist_all_iff)

subsubsection\<open>Difference\<close>

definition
  difference :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "difference xs ys = ODList (List_local.difference (toList xs) (toList ys))"

lemma toList_difference[simp, code abstract]:
  "toList (difference xs ys) = List_local.difference (toList xs) (toList ys)"
  unfolding difference_def by (simp add: toList_ODList)

lemma toSet_difference[simp]:
  "toSet (difference xs ys) = toSet xs - toSet ys"
  unfolding difference_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection\<open>Intersection\<close>

definition
  intersect :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "intersect xs ys = ODList (List_local.intersection (toList xs) (toList ys))"

lemma toList_intersect[simp, code abstract]:
  "toList (intersect xs ys) = List_local.intersection (toList xs) (toList ys)"
  unfolding intersect_def by (simp add: toList_ODList)

lemma toSet_intersect[simp]:
  "toSet (intersect xs ys) = toSet xs \<inter> toSet ys"
  unfolding intersect_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection\<open>Union\<close>

definition
  union :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "union xs ys = ODList (merge (toList xs) (toList ys))"

lemma toList_union[simp, code abstract]:
  "toList (union xs ys) = merge (toList xs) (toList ys)"
  unfolding union_def by (simp add: toList_ODList)

lemma toSet_union[simp]:
  "toSet (union xs ys) = toSet xs \<union> toSet ys"
  unfolding union_def
  apply simp
  apply (simp add: toSet_def)
  done

definition
  big_union :: "('b \<Rightarrow> ('a :: linorder) odlist) \<Rightarrow> 'b list \<Rightarrow> 'a odlist"
where
  [code]: "big_union f X \<equiv> foldr (\<lambda>a A. ODList.union (f a) A) X ODList.empty"

lemma toSet_big_union[simp]:
  "toSet (big_union f X) = (\<Union>x \<in> set X. toSet (f x))"
proof -
  { fix X Y
    have "toSet (foldr (\<lambda>x A. ODList.union (f x) A) X Y) = toSet Y \<union> (\<Union>x \<in> set X. toSet (f x))"
      by (induct X arbitrary: Y) auto }
   thus ?thesis
     unfolding big_union_def by simp
qed

subsubsection\<open>Case distinctions\<close>

text\<open>

We construct ODLists out of lists, so talk in terms of those, not a
one-step constructor we don't use.

\<close>

lemma distinct_sorted_induct [consumes 2, case_names Nil insert]:
  assumes "distinct xs"
  assumes "sorted xs"
  assumes base: "P []"
  assumes step: "\<And>x xs. \<lbrakk> distinct (x # xs); sorted (x # xs); P xs \<rbrakk> \<Longrightarrow> P (x # xs)"
  shows "P xs"
using \<open>distinct xs\<close> \<open>sorted xs\<close> proof (induct xs)
  case Nil from \<open>P []\<close> show ?case .
next
  case (Cons x xs)
  then have "distinct (x # xs)" and "sorted (x # xs)" and "P xs" by (simp_all)
  with step show "P (x # xs)" .
qed

lemma odlist_induct [case_names empty insert, cases type: odlist]:
  assumes empty: "\<And>dxs. dxs = empty \<Longrightarrow> P dxs"
  assumes insrt: "\<And>dxs x xs. \<lbrakk> dxs = fromList (x # xs); distinct (x # xs); sorted (x # xs); P (fromList xs) \<rbrakk>
                            \<Longrightarrow> P dxs"
  shows "P dxs"
proof (cases dxs)
  case (odlist_Abs xs)
  then have dxs: "dxs = ODList xs" and distinct: "distinct xs" and sorted: "sorted xs"
    by (simp_all add: ODList_def)
  from \<open>distinct xs\<close> and \<open>sorted xs\<close> have "P (ODList xs)"
  proof (induct xs rule: distinct_sorted_induct)
    case Nil from empty show ?case by (simp add: empty_def)
  next
    case (insert x xs) thus ?case
      apply -
      apply (rule insrt)
      apply (auto simp: fromList_def)
      done
  qed
  with dxs show "P dxs" by simp
qed

lemma odlist_cases [case_names empty insert, cases type: odlist]:
  assumes empty: "dxs = empty \<Longrightarrow> P"
  assumes insert: "\<And>x xs. \<lbrakk> dxs = fromList (x # xs); distinct (x # xs); sorted (x # xs) \<rbrakk>
                            \<Longrightarrow> P"
  shows P
proof (cases dxs)
  case (odlist_Abs xs)
  then have dxs: "dxs = ODList xs" and distinct: "distinct xs" and sorted: "sorted xs"
    by (simp_all add: ODList_def)
  show P proof (cases xs)
    case Nil with dxs have "dxs = empty" by (simp add: empty_def)
    with empty show P .
  next
    case (Cons y ys)
    with dxs distinct sorted insert
    show P by (simp add: fromList_def)
  qed
qed

subsubsection\<open>Relations\<close>

text\<open>

Relations, represented as a list of pairs.

\<close>

type_synonym 'a odrelation = "('a \<times> 'a) odlist"

subsubsection\<open>Image\<close>

text\<open>

The output of @{term "List_local.image"} is not guaranteed to be
ordered or distinct. Also the relation need not be monomorphic.

\<close>

definition
  image :: "('a :: linorder \<times> 'b :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'b odlist"
where
  "image R xs = ODList (List_local.image (toList R) (toList xs))"

lemma toList_image[simp, code abstract]:
  "toList (image R xs) = msort (List_local.image (toList R) (toList xs))"
  unfolding image_def by (simp add: toList_ODList)

lemma toSet_image[simp]:
  "toSet (image R xs) = toSet R `` toSet xs"
  unfolding image_def by (simp add: toSet_def toList_ODList)

subsubsection\<open>Linear order\<close>

text\<open>

Lexicographic ordering on lists. Executable, unlike in List.thy.

\<close>

instantiation odlist :: (linorder) linorder
begin
print_context
fun
  less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "less_eq_list [] ys = True"
| "less_eq_list xs [] = False"
| "less_eq_list (x # xs) (y # ys) = (x < y \<or> (x = y \<and> less_eq_list xs ys))"

lemma less_eq_list_nil_inv:
  fixes xs :: "'a list"
  shows "less_eq_list xs [] \<Longrightarrow> xs = []"
  by (cases xs) simp_all

lemma less_eq_list_cons_inv:
  fixes x :: 'a
  shows "less_eq_list (x # xs) yys \<Longrightarrow> \<exists>y ys. yys = y # ys \<and> (x < y \<or> (x = y \<and> less_eq_list xs ys))"
  by (cases yys) auto

lemma less_eq_list_refl:
  fixes xs :: "'a list"
  shows "less_eq_list xs xs"
  by (induct xs) simp_all

lemma less_eq_list_trans:
  fixes xs ys zs :: "'a list"
  shows "\<lbrakk> less_eq_list xs ys; less_eq_list ys zs \<rbrakk> \<Longrightarrow> less_eq_list xs zs"
  apply (induct xs ys arbitrary: zs rule: less_eq_list.induct)
    apply simp
   apply simp
  apply clarsimp
  apply (erule disjE)
   apply (drule less_eq_list_cons_inv)
   apply clarsimp
   apply (erule disjE)
    apply auto[1]
   apply auto[1]
  apply (auto dest: less_eq_list_cons_inv)
  done

lemma less_eq_list_antisym:
  fixes xs ys :: "'a list"
  shows "\<lbrakk> less_eq_list xs ys; less_eq_list ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  by (induct xs ys rule: less_eq_list.induct) (auto dest: less_eq_list_nil_inv)

lemma less_eq_list_linear:
  fixes xs ys :: "'a list"
  shows "less_eq_list xs ys \<or> less_eq_list ys xs"
  by (induct xs ys rule: less_eq_list.induct) auto

definition
  less_eq_odlist :: "'a odlist \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  "xs \<le> ys \<equiv> less_eq_list (toList xs) (toList ys)"

fun
  less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "less_list [] [] = False"
| "less_list [] ys = True"
| "less_list xs [] = False"
| "less_list (x # xs) (y # ys) = (x < y \<or> (x = y \<and> less_list xs ys))"

definition
  less_odlist :: "'a odlist \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  "xs < ys \<equiv> less_list (toList xs) (toList ys)"

lemma less_eq_list_not_le:
  fixes xs ys :: "'a list"
  shows "(less_list xs ys) = (less_eq_list xs ys \<and> \<not> less_eq_list ys xs)"
  by (induct xs ys rule: less_list.induct) auto

instance
  apply intro_classes
  unfolding less_eq_odlist_def less_odlist_def
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  apply (rule less_eq_list_linear)
  done

end

subsubsection\<open>Finite maps\<close>

text\<open>

A few operations on finite maps.

Unlike the AssocList theory, ODLists give us canonical
representations, so we can order them. Our tabulate has the wrong type
(we want to take an odlist, not a list) so we can't use that
part of the framework.

\<close>

definition
  lookup :: "('a :: linorder \<times> 'b :: linorder) odlist \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  [code]: "lookup = map_of \<circ> toList"

text\<open>Specific to ODLists.\<close>

definition
  tabulate :: "('a :: linorder) odlist \<Rightarrow> ('a \<Rightarrow> 'b :: linorder) \<Rightarrow> ('a \<times> 'b) odlist"
where
  "tabulate ks f = ODList (List.map (\<lambda>k. (k, f k)) (toList ks))"

definition (in order) mono_on :: "('a \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_on f X \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma (in order) mono_onI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b::order"
  shows "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> mono_on f X"
  unfolding mono_on_def by simp

lemma (in order) mono_onD [dest?]:
  fixes f :: "'a \<Rightarrow> 'b::order"
  shows "mono_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  unfolding mono_on_def by simp

lemma (in order) mono_on_subset:
  fixes f :: "'a \<Rightarrow> 'b::order"
  shows "mono_on f X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> mono_on f Y"
  unfolding mono_on_def by auto

lemma sorted_mono_map:
  "\<lbrakk> sorted xs; mono_on f (set xs) \<rbrakk> \<Longrightarrow> sorted (List.map f xs)"
  apply (induct xs)
   apply simp
  apply (simp)
  apply (cut_tac X="insert a (set xs)" and Y="set xs" in mono_on_subset)
  apply (auto dest: mono_onD)
  done

lemma msort_map:
  "\<lbrakk> distinct xs; sorted xs; inj_on f (set xs); mono_on f (set xs) \<rbrakk> \<Longrightarrow> msort (List.map f xs) = List.map f xs"
  apply (rule msort_idle)
   apply (simp add: distinct_map)
  apply (simp add: sorted_mono_map)
  done

lemma tabulate_toList[simp, code abstract]:
  "toList (tabulate ks f) = List.map (\<lambda>k. (k, f k)) (toList ks)"
  unfolding tabulate_def
  apply (simp add: toList_ODList)
  apply (subst msort_map)
  apply simp_all
   apply (rule inj_onI)
   apply simp
  apply (rule mono_onI)
  apply (simp add: less_eq_prod_def less_le)
  done

lemma lookup_tabulate[simp]:
  "lookup (tabulate ks f) = (Some o f) |` toSet ks"
proof(induct ks rule: odlist_induct)
  case (empty dxs) thus ?case unfolding tabulate_def lookup_def by (simp add: toList_ODList)
next
  case (insert dxs x xs)
  from insert have "map_of (List.map (\<lambda>k. (k, f k)) xs) = map_of (msort (List.map (\<lambda>k. (k, f k)) xs))"
    apply (subst msort_map)
    apply (auto intro: inj_onI)
    apply (rule mono_onI)
    apply (simp add: less_eq_prod_def less_le)
    done
  also from insert have "... = lookup (tabulate (fromList xs) f)"
    unfolding tabulate_def lookup_def
    by (simp add: toList_ODList toList_fromList)
  also from insert have "... = (Some \<circ> f) |` toSet (fromList xs)"
    by (simp only: toSet_fromList_set)
  finally have IH: "map_of (List.map (\<lambda>k. (k, f k)) xs) = (Some \<circ> f) |` toSet (fromList xs)" .
  from insert have "lookup (tabulate dxs f) = map_of (toList (ODList (List.map (\<lambda>k. (k, f k)) (x # xs))))"
    unfolding tabulate_def lookup_def by (simp add: toList_fromList)
  also have "... = map_of (msort (List.map (\<lambda>k. (k, f k)) (x # xs)))"
    by (simp only: toList_ODList)
  also from insert have "... = map_of (List.map (\<lambda>k. (k, f k)) (x # xs))"
    apply (subst msort_map)
    apply (auto intro: inj_onI)
    apply (rule mono_onI)
    apply (simp add: less_eq_prod_def less_le)
    done
  also with insert IH have "... = (Some \<circ> f) |` toSet dxs"
    by (auto simp add: restrict_map_def fun_eq_iff)
  finally show ?case .
qed

(*<*)
end
(*>*)
