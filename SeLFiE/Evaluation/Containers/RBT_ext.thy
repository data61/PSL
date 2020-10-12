(*  Title:      Containers/RBT_ext.thy
    Author:     Andreas Lochbihler, KIT *)

theory RBT_ext
imports
  "HOL-Library.RBT_Impl"
  Containers_Auxiliary
  List_Fusion
begin

section \<open>More on red-black trees\<close>

subsection \<open>More lemmas\<close>

context linorder begin

lemma is_rbt_fold_rbt_insert_impl:
  "is_rbt t \<Longrightarrow> is_rbt (RBT_Impl.fold rbt_insert t' t)"
by(simp add: rbt_insert_def is_rbt_fold_rbt_insertwk)

lemma rbt_sorted_fold_insert: "rbt_sorted t \<Longrightarrow> rbt_sorted (RBT_Impl.fold rbt_insert t' t)"
by(induct t' arbitrary: t)(simp_all add: rbt_insert_rbt_sorted)

lemma rbt_lookup_rbt_insert': "rbt_sorted t \<Longrightarrow> rbt_lookup (rbt_insert k v t) = rbt_lookup t(k \<mapsto> v)"
by(simp add: rbt_insert_def rbt_lookup_rbt_insertwk fun_eq_iff split: option.split)

lemma rbt_lookup_fold_rbt_insert_impl:
  "rbt_sorted t2 \<Longrightarrow> 
  rbt_lookup (RBT_Impl.fold rbt_insert t1 t2) = rbt_lookup t2 ++ map_of (rev (RBT_Impl.entries t1))"
proof(induction t1 arbitrary: t2)
  case Empty thus ?case by simp
next
  case (Branch c l x k r)
  show ?case using Branch.prems
    by(simp add: map_add_def Branch.IH rbt_insert_rbt_sorted rbt_sorted_fold_insert rbt_lookup_rbt_insert' fun_eq_iff split: option.split)
qed

end

subsection \<open>Build the cross product of two RBTs\<close>

context fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e" begin

definition alist_product :: "('a \<times> 'b) list \<Rightarrow> ('c \<times> 'd) list \<Rightarrow> (('a \<times> 'c) \<times> 'e) list"
where "alist_product xs ys = concat (map (\<lambda>(a, b). map (\<lambda>(c, d). ((a, c), f a b c d)) ys) xs)"

lemma alist_product_simps [simp]:
  "alist_product [] ys = []"
  "alist_product xs [] = []"
  "alist_product ((a, b) # xs) ys = map (\<lambda>(c, d). ((a, c), f a b c d)) ys @ alist_product xs ys"
by(simp_all add: alist_product_def)

lemma append_alist_product_conv_fold:
  "zs @ alist_product xs ys = rev (fold (\<lambda>(a, b). fold (\<lambda>(c, d) rest. ((a, c), f a b c d) # rest) ys) xs (rev zs))"
proof(induction xs arbitrary: zs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  obtain a b where x: "x = (a, b)" by(cases x)
  have "\<And>zs. fold (\<lambda>(c, d). (#) ((a, c), f a b c d)) ys zs =
    rev (map (\<lambda>(c, d). ((a, c), f a b c d)) ys) @ zs"
    by(induct ys) auto
  with Cons.IH[of "zs @ map (\<lambda>(c, d). ((a, c), f a b c d)) ys"] x
  show ?case by simp
qed

lemma alist_product_code [code]:
  "alist_product xs ys =
  rev (fold (\<lambda>(a, b). fold (\<lambda>(c, d) rest. ((a, c), f a b c d) # rest) ys) xs [])"
using append_alist_product_conv_fold[of "[]" xs ys]
by simp

lemma set_alist_product:
  "set (alist_product xs ys) =
  (\<lambda>((a, b), (c, d)). ((a, c), f a b c d)) ` (set xs \<times> set ys)"
by(auto 4 3 simp add: alist_product_def intro: rev_image_eqI rev_bexI)

lemma distinct_alist_product:
  "\<lbrakk> distinct (map fst xs); distinct (map fst ys) \<rbrakk>
  \<Longrightarrow> distinct (map fst (alist_product xs ys))"
proof(induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  obtain a b where x: "x = (a, b)" by(cases x)
  have "distinct (map (fst \<circ> (\<lambda>(c, d). ((a, c), f a b c d))) ys)"
    using \<open>distinct (map fst ys)\<close> by(induct ys)(auto intro: rev_image_eqI)
  thus ?case using Cons x by(auto simp add: set_alist_product intro: rev_image_eqI)
qed

lemma map_of_alist_product:
  "map_of (alist_product xs ys) (a, c) = 
  (case map_of xs a of None \<Rightarrow> None
   | Some b \<Rightarrow> map_option (f a b c) (map_of ys c))"
proof(induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  obtain a b where x: "x = (a, b)" by (cases x)
  let ?map = "map (\<lambda>(c, d). ((a, c), f a b c d)) ys"
  have "map_of ?map (a, c) = map_option (f a b c) (map_of ys c)"
    by(induct ys) auto
  moreover {
    fix a' assume "a' \<noteq> a"
    hence "map_of ?map (a', c) = None"
      by(induct ys) auto }
  ultimately show ?case using x Cons.IH
    by(auto simp add: map_add_def split: option.split)
qed

definition rbt_product :: "('a, 'b) rbt \<Rightarrow> ('c, 'd) rbt \<Rightarrow> ('a \<times> 'c, 'e) rbt"
where
  "rbt_product rbt1 rbt2 = rbtreeify (alist_product (RBT_Impl.entries rbt1) (RBT_Impl.entries rbt2))"

lemma rbt_product_code [code]:
  "rbt_product rbt1 rbt2 =
   rbtreeify (rev (RBT_Impl.fold (\<lambda>a b. RBT_Impl.fold (\<lambda>c d rest. ((a, c), f a b c d) # rest) rbt2) rbt1 []))"
unfolding rbt_product_def alist_product_code RBT_Impl.fold_def ..

end

context
  fixes leq_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>a" 50) 
  and less_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>a" 50) 
  and leq_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>b" 50) 
  and less_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>b" 50) 
  assumes lin_a: "class.linorder leq_a less_a" 
  and lin_b: "class.linorder leq_b less_b"
begin

abbreviation (input) less_eq_prod' :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where "less_eq_prod' \<equiv> less_eq_prod leq_a less_a leq_b"

abbreviation (input) less_prod' :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where "less_prod' \<equiv> less_prod leq_a less_a less_b"

lemmas linorder_prod = linorder_prod[OF lin_a lin_b]

lemma sorted_alist_product: 
  assumes xs: "linorder.sorted leq_a (map fst xs)" "distinct (map fst xs)"
  and ys: "linorder.sorted (\<sqsubseteq>\<^sub>b) (map fst ys)"
  shows "linorder.sorted (\<sqsubseteq>) (map fst (alist_product f xs ys))"
proof -
  interpret a: linorder "(\<sqsubseteq>\<^sub>a)" "(\<sqsubset>\<^sub>a)" by(fact lin_a)

  note [simp] = 
    linorder.sorted.simps(1)[OF linorder_prod] linorder.sorted.simps(2)[OF linorder_prod]
    linorder.sorted_append[OF linorder_prod]
    linorder.sorted.simps(2)[OF lin_b]

  show ?thesis using xs
  proof(induction xs)
    case Nil show ?case by simp
  next
    case (Cons x xs)
    obtain a b where x: "x = (a, b)" by(cases x)
    have "linorder.sorted (\<sqsubseteq>) (map fst (map (\<lambda>(c, d). ((a, c), f a b c d)) ys))"
      using ys by(induct ys) auto
    thus ?case using x Cons
      by(fastforce simp add: set_alist_product a.not_less dest: bspec a.antisym intro: rev_image_eqI)
  qed
qed

lemma is_rbt_rbt_product:
  "\<lbrakk> ord.is_rbt (\<sqsubset>\<^sub>a) rbt1; ord.is_rbt (\<sqsubset>\<^sub>b) rbt2 \<rbrakk>
  \<Longrightarrow> ord.is_rbt (\<sqsubset>) (rbt_product f rbt1 rbt2)"
unfolding rbt_product_def
by(blast intro: linorder.is_rbt_rbtreeify[OF linorder_prod] sorted_alist_product linorder.rbt_sorted_entries[OF lin_a] ord.is_rbt_rbt_sorted linorder.distinct_entries[OF lin_a] linorder.rbt_sorted_entries[OF lin_b] distinct_alist_product linorder.distinct_entries[OF lin_b])

lemma rbt_lookup_rbt_product:
  "\<lbrakk> ord.is_rbt (\<sqsubset>\<^sub>a) rbt1; ord.is_rbt (\<sqsubset>\<^sub>b) rbt2 \<rbrakk>
  \<Longrightarrow> ord.rbt_lookup (\<sqsubset>) (rbt_product f rbt1 rbt2) (a, c) =
     (case ord.rbt_lookup (\<sqsubset>\<^sub>a) rbt1 a of None \<Rightarrow> None
      | Some b \<Rightarrow> map_option (f a b c) (ord.rbt_lookup (\<sqsubset>\<^sub>b) rbt2 c))"
by(simp add: rbt_product_def linorder.rbt_lookup_rbtreeify[OF linorder_prod] linorder.is_rbt_rbtreeify[OF linorder_prod] sorted_alist_product linorder.rbt_sorted_entries[OF lin_a] ord.is_rbt_rbt_sorted linorder.distinct_entries[OF lin_a] linorder.rbt_sorted_entries[OF lin_b] distinct_alist_product linorder.distinct_entries[OF lin_b] map_of_alist_product linorder.map_of_entries[OF lin_a] linorder.map_of_entries[OF lin_b] cong: option.case_cong)

end

hide_const less_eq_prod' less_prod'

subsection \<open>Build an RBT where keys are paired with themselves\<close>

primrec RBT_Impl_diag :: "('a, 'b) rbt \<Rightarrow> ('a \<times> 'a, 'b) rbt"
where
  "RBT_Impl_diag rbt.Empty = rbt.Empty"
| "RBT_Impl_diag (rbt.Branch c l k v r) = rbt.Branch c (RBT_Impl_diag l) (k, k) v (RBT_Impl_diag r)"

lemma entries_RBT_Impl_diag:
  "RBT_Impl.entries (RBT_Impl_diag t) = map (\<lambda>(k, v). ((k, k), v)) (RBT_Impl.entries t)"
by(induct t) simp_all

lemma keys_RBT_Impl_diag:
  "RBT_Impl.keys (RBT_Impl_diag t) = map (\<lambda>k. (k, k)) (RBT_Impl.keys t)"
by(simp add: RBT_Impl.keys_def entries_RBT_Impl_diag split_beta)

lemma rbt_sorted_RBT_Impl_diag:
  "ord.rbt_sorted lt t \<Longrightarrow> ord.rbt_sorted (less_prod leq lt lt) (RBT_Impl_diag t)"
by(induct t)(auto simp add: ord.rbt_sorted.simps ord.rbt_less_prop ord.rbt_greater_prop keys_RBT_Impl_diag)

lemma bheight_RBT_Impl_diag:
  "bheight (RBT_Impl_diag t) = bheight t"
by(induct t) simp_all

lemma inv_RBT_Impl_diag:
  assumes "inv1 t" "inv2 t"
  shows "inv1 (RBT_Impl_diag t)" "inv2 (RBT_Impl_diag t)"
  and "color_of t = color.B \<Longrightarrow> color_of (RBT_Impl_diag t) = color.B"
using assms by(induct t)(auto simp add: bheight_RBT_Impl_diag)

lemma is_rbt_RBT_Impl_diag:
  "ord.is_rbt lt t \<Longrightarrow> ord.is_rbt (less_prod leq lt lt) (RBT_Impl_diag t)"
by(simp add: ord.is_rbt_def rbt_sorted_RBT_Impl_diag inv_RBT_Impl_diag)

lemma (in linorder) rbt_lookup_RBT_Impl_diag:
  "ord.rbt_lookup (less_prod (\<le>) (<) (<)) (RBT_Impl_diag t) =
  (\<lambda>(k, k'). if k = k' then ord.rbt_lookup (<) t k else None)"
by(induct t)(auto simp add: ord.rbt_lookup.simps fun_eq_iff)

subsection \<open>Folding and quantifiers over RBTs\<close>

definition RBT_Impl_fold1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a, unit) RBT_Impl.rbt \<Rightarrow> 'a"
where "RBT_Impl_fold1 f rbt = fold f (tl (RBT_Impl.keys rbt)) (hd (RBT_Impl.keys rbt))"

lemma RBT_Impl_fold1_simps [simp, code]:
  "RBT_Impl_fold1 f rbt.Empty = undefined"
  "RBT_Impl_fold1 f (Branch c rbt.Empty k v r) = RBT_Impl.fold (\<lambda>k v. f k) r k"
  "RBT_Impl_fold1 f (Branch c (Branch c' l' k' v' r') k v r) = 
   RBT_Impl.fold (\<lambda>k v. f k) r (f k (RBT_Impl_fold1 f (Branch c' l' k' v' r')))"
by(simp_all add: RBT_Impl_fold1_def RBT_Impl.keys_def fold_map RBT_Impl.fold_def split_def o_def tl_append hd_def split: list.split)

definition RBT_Impl_rbt_all :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"
where [code del]: "RBT_Impl_rbt_all P rbt = (\<forall>(k, v) \<in> set (RBT_Impl.entries rbt). P k v)"

lemma RBT_Impl_rbt_all_simps [simp, code]:
  "RBT_Impl_rbt_all P rbt.Empty \<longleftrightarrow> True"
  "RBT_Impl_rbt_all P (Branch c l k v r) \<longleftrightarrow> P k v \<and> RBT_Impl_rbt_all P l \<and> RBT_Impl_rbt_all P r"
by(auto simp add: RBT_Impl_rbt_all_def)

definition RBT_Impl_rbt_ex :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> bool"
where [code del]: "RBT_Impl_rbt_ex P rbt = (\<exists>(k, v) \<in> set (RBT_Impl.entries rbt). P k v)"

lemma RBT_Impl_rbt_ex_simps [simp, code]:
  "RBT_Impl_rbt_ex P rbt.Empty \<longleftrightarrow> False"
  "RBT_Impl_rbt_ex P (Branch c l k v r) \<longleftrightarrow> P k v \<or> RBT_Impl_rbt_ex P l \<or> RBT_Impl_rbt_ex P r"
by(auto simp add: RBT_Impl_rbt_ex_def)

subsection \<open>List fusion for RBTs\<close>

type_synonym ('a, 'b, 'c) rbt_generator_state = "('c \<times> ('a, 'b) RBT_Impl.rbt) list \<times> ('a, 'b) RBT_Impl.rbt"

fun rbt_has_next :: "('a, 'b, 'c) rbt_generator_state \<Rightarrow> bool"
where
  "rbt_has_next ([], rbt.Empty) = False"
| "rbt_has_next _ = True"

fun rbt_keys_next :: "('a, 'b, 'a) rbt_generator_state \<Rightarrow> 'a \<times> ('a, 'b, 'a) rbt_generator_state"
where
  "rbt_keys_next ((k, t) # kts, rbt.Empty) = (k, kts, t)"
| "rbt_keys_next (kts, rbt.Branch c l k v r) = rbt_keys_next ((k, r) # kts, l)"

lemma rbt_generator_induct [case_names empty split shuffle]:
  assumes "P ([], rbt.Empty)"
  and "\<And>k t kts. P (kts, t) \<Longrightarrow> P ((k, t) # kts, rbt.Empty)"
  and "\<And>kts c l k v r. P ((f k v, r) # kts, l) \<Longrightarrow> P (kts, Branch c l k v r)"
  shows "P ktst"
using assms
apply(induction_schema)
apply pat_completeness
apply(relation "measure (\<lambda>(kts, t). size_list (\<lambda>(k, t). size_rbt (\<lambda>_. 1) (\<lambda>_. 1) t) kts + size_rbt (\<lambda>_. 1) (\<lambda>_. 1) t)")
apply simp_all
done

lemma terminates_rbt_keys_generator:
  "terminates (rbt_has_next, rbt_keys_next)"
proof
  fix ktst :: "('a \<times> ('a, 'b) rbt) list \<times> ('a, 'b) rbt"
  show "ktst \<in> terminates_on (rbt_has_next, rbt_keys_next)"
    by(induct ktst taking: "\<lambda>k _. k" rule: rbt_generator_induct)(auto 4 3 intro: terminates_on.intros elim: terminates_on.cases)
qed

lift_definition rbt_keys_generator :: "('a, ('a, 'b, 'a) rbt_generator_state) generator"
  is "(rbt_has_next, rbt_keys_next)"
by(rule terminates_rbt_keys_generator)

definition rbt_init :: "('a, 'b) rbt \<Rightarrow> ('a, 'b, 'c) rbt_generator_state"
where "rbt_init = Pair []"

lemma has_next_rbt_keys_generator [simp]:
  "list.has_next rbt_keys_generator = rbt_has_next"
by transfer simp

lemma next_rbt_keys_generator [simp]:
  "list.next rbt_keys_generator = rbt_keys_next"
by transfer simp

lemma unfoldr_rbt_keys_generator_aux:
  "list.unfoldr rbt_keys_generator (kts, t) = 
  RBT_Impl.keys t @ concat (map (\<lambda>(k, t). k # RBT_Impl.keys t) kts)"
proof(induct "(kts, t)" arbitrary: kts t taking: "\<lambda>k _. k" rule: rbt_generator_induct)
  case empty thus ?case
    by(simp add: list.unfoldr.simps)
next
  case split thus ?case
    by(subst list.unfoldr.simps) simp
next
  case shuffle thus ?case
    by(subst list.unfoldr.simps)(subst (asm) list.unfoldr.simps, simp)
qed

corollary unfoldr_rbt_keys_generator:
  "list.unfoldr rbt_keys_generator (rbt_init t) = RBT_Impl.keys t"
by(simp add: unfoldr_rbt_keys_generator_aux rbt_init_def)

fun rbt_entries_next :: 
  "('a, 'b, 'a \<times> 'b) rbt_generator_state \<Rightarrow> ('a \<times> 'b) \<times> ('a, 'b, 'a \<times> 'b) rbt_generator_state"
where
  "rbt_entries_next ((kv, t) # kts, rbt.Empty) = (kv, kts, t)"
| "rbt_entries_next (kts, rbt.Branch c l k v r) = rbt_entries_next (((k, v), r) # kts, l)"

lemma terminates_rbt_entries_generator:
  "terminates (rbt_has_next, rbt_entries_next)"
proof(rule terminatesI)
  fix ktst :: "('a, 'b, 'a \<times> 'b) rbt_generator_state"
  show "ktst \<in> terminates_on (rbt_has_next, rbt_entries_next)"
    by(induct ktst taking: Pair rule: rbt_generator_induct)(auto 4 3 intro: terminates_on.intros elim: terminates_on.cases)
qed

lift_definition rbt_entries_generator :: "('a \<times> 'b, ('a, 'b, 'a \<times> 'b) rbt_generator_state) generator"
  is "(rbt_has_next, rbt_entries_next)"
by(rule terminates_rbt_entries_generator)

lemma has_next_rbt_entries_generator [simp]:
  "list.has_next rbt_entries_generator = rbt_has_next"
by transfer simp

lemma next_rbt_entries_generator [simp]:
  "list.next rbt_entries_generator = rbt_entries_next"
by transfer simp

lemma unfoldr_rbt_entries_generator_aux:
  "list.unfoldr rbt_entries_generator (kts, t) = 
  RBT_Impl.entries t @ concat (map (\<lambda>(k, t). k # RBT_Impl.entries t) kts)"
proof(induct "(kts, t)" arbitrary: kts t taking: Pair rule: rbt_generator_induct)
  case empty thus ?case
    by(simp add: list.unfoldr.simps)
next
  case split thus ?case
    by(subst list.unfoldr.simps) simp
next
  case shuffle thus ?case
    by(subst list.unfoldr.simps)(subst (asm) list.unfoldr.simps, simp)
qed

corollary unfoldr_rbt_entries_generator:
  "list.unfoldr rbt_entries_generator (rbt_init t) = RBT_Impl.entries t"
by(simp add: unfoldr_rbt_entries_generator_aux rbt_init_def)

end
