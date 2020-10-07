(*
    Author:     René Thiemann
    License:    BSD
*)
section \<open>Calculating All Possible Sums of Sub-Multisets\<close>
theory Sub_Sums
  imports 
    Main 
    "HOL-Library.Multiset"
begin

fun sub_mset_sums :: "'a :: comm_monoid_add list \<Rightarrow> 'a set" where
  "sub_mset_sums [] = {0}"
| "sub_mset_sums (x # xs) = (let S = sub_mset_sums xs in S \<union> ( (+) x) ` S)" 

lemma subset_add_mset: "ys \<subseteq># add_mset x zs \<longleftrightarrow> (ys \<subseteq># zs \<or> (\<exists> xs. xs \<subseteq># zs \<and> ys = add_mset x xs))" 
  (is "?l = ?r")
proof 
  have sub: "ys \<subseteq># zs \<Longrightarrow> ys \<subseteq># add_mset x zs"
    by (metis add_mset_remove_trivial diff_subset_eq_self subset_mset.dual_order.trans)
  assume ?r
  thus ?l using sub by auto
next
  assume l: ?l
  show ?r
  proof (cases "x \<in># ys")
    case True
    define xs where "xs = (ys - {# x #})" 
    from True have ys: "ys = add_mset x xs" unfolding xs_def by auto 
    from l[unfolded ys] have "xs \<subseteq># zs" by auto
    thus ?r unfolding ys by auto
  next
    case False
    with l have "ys \<subseteq># zs" by (simp add: subset_mset.le_iff_sup)
    thus ?thesis by auto
  qed
qed

lemma sub_mset_sums[simp]: "sub_mset_sums xs = sum_mset ` { ys. ys \<subseteq># mset xs }" 
proof (induct xs)
  case (Cons x xs)
  have id: "{ys. ys \<subseteq># mset (x # xs)} = {ys. ys \<subseteq># mset xs} \<union> {add_mset x ys | ys. ys \<subseteq># mset xs}" 
    unfolding mset.simps subset_add_mset by auto
  show ?case unfolding sub_mset_sums.simps Let_def Cons id image_Un 
    by force
qed auto

end