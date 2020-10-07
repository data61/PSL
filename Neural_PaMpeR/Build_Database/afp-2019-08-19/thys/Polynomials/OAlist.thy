(* Author: Florian Haftmann, TU Muenchen *)
(* Author: Andreas Lochbihler, ETH Zurich *)
(* Author: Alexander Maletzky, RISC Linz *)

section \<open>Associative Lists with Sorted Keys\<close>

theory OAlist
  imports Deriving.Comparator
begin

text \<open>We define the type of @{emph \<open>ordered associative lists\<close>} (oalist). An oalist is an associative
  list (i.\,e. a list of pairs) such that the keys are distinct and sorted wrt. some linear
  order relation, and no key is mapped to @{term 0}. The latter invariant allows to implement various
  functions operating on oalists more efficiently.

  The ordering of the keys in an oalist \<open>xs\<close> is encoded as an additional parameter of \<open>xs\<close>.
  This means that oalists may be ordered wrt. different orderings, even if they are of the same type.
  Operations operating on more than one oalists, like \<open>map2_val\<close>, typically ensure that the orderings
  of their arguments are identical by re-ordering one argument wrt. the order relation of the other.
  This, however, implies that equality of order relations must be effectively decidable if executable
  code is to be generated.\<close>

subsection \<open>Preliminaries\<close>

fun min_list_param :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "min_list_param rel (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> (let m = min_list_param rel xs in if rel x m then x else m))"

lemma min_list_param_in:
  assumes "xs \<noteq> []"
  shows "min_list_param rel xs \<in> set xs"
  using assms
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp add: min_list_param.simps[of rel x xs] Let_def del: min_list_param.simps set_simps(2) split: list.split,
        intro conjI impI allI, simp, simp)
    fix y ys
    assume xs: "xs = y # ys"
    have "min_list_param rel (y # ys) = min_list_param rel xs" by (simp only: xs)
    also have "... \<in> set xs" by (rule Cons(1), simp add: xs)
    also have "... \<subseteq> set (x # y # ys)" by (auto simp: xs)
    finally show "min_list_param rel (y # ys) \<in> set (x # y # ys)" .
  qed
qed

lemma min_list_param_minimal:
  assumes "transp rel" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> rel x y \<or> rel y x"
    and "z \<in> set xs"
  shows "rel (min_list_param rel xs) z"
  using assms(2, 3)
proof (induct xs)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons x xs)
  from Cons(3) have disj1: "z = x \<or> z \<in> set xs" by simp
  have "x \<in> set (x # xs)" by simp
  hence disj2: "rel x z \<or> rel z x" using Cons(3) by (rule Cons(2))
  have *: "rel (min_list_param rel xs) z" if "z \<in> set xs" using _ that
  proof (rule Cons(1))
    fix a b
    assume "a \<in> set xs" and "b \<in> set xs"
    hence "a \<in> set (x # xs)" and "b \<in> set (x # xs)" by simp_all
    thus "rel a b \<or> rel b a" by (rule Cons(2))
  qed
  show ?case
  proof (simp add: min_list_param.simps[of rel x xs] Let_def del: min_list_param.simps set_simps(2) split: list.split,
        intro conjI impI allI)
    assume "xs = []"
    with disj1 disj2 show "rel x z" by simp
  next
    fix y ys
    assume "xs = y # ys" and "rel x (min_list_param rel (y # ys))"
    hence "rel x (min_list_param rel xs)" by simp
    from disj1 show "rel x z"
    proof
      assume "z = x"
      thus ?thesis using disj2 by simp
    next
      assume "z \<in> set xs"
      hence "rel (min_list_param rel xs) z" by (rule *)
      with assms(1) \<open>rel x (min_list_param rel xs)\<close> show ?thesis by (rule transpD)
    qed
  next
    fix y ys
    assume xs: "xs = y # ys" and "\<not> rel x (min_list_param rel (y # ys))"
    from disj1 show "rel (min_list_param rel (y # ys)) z"
    proof
      assume "z = x"
      have "min_list_param rel (y # ys) \<in> set (y # ys)" by (rule min_list_param_in, simp)
      hence "min_list_param rel (y # ys) \<in> set (x # xs)" by (simp add: xs)
      with \<open>x \<in> set (x # xs)\<close> have "rel x (min_list_param rel (y # ys)) \<or> rel (min_list_param rel (y # ys)) x"
        by (rule Cons(2))
      with \<open>\<not> rel x (min_list_param rel (y # ys))\<close> have "rel (min_list_param rel (y # ys)) x" by simp
      thus ?thesis by (simp only: \<open>z = x\<close>)
    next
      assume "z \<in> set xs"
      hence "rel (min_list_param rel xs) z" by (rule *)
      thus ?thesis by (simp only: xs)
    qed
  qed
qed

definition comp_of_ord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a comparator" where
  "comp_of_ord le x y = (if le x y then if x = y then Eq else Lt else Gt)"

lemma comp_of_ord_eq_comp_of_ords:
  assumes "antisymp le"
  shows "comp_of_ord le = comp_of_ords le (\<lambda>x y. le x y \<and> \<not> le y x)"
  by (intro ext, auto simp: comp_of_ord_def comp_of_ords_def intro: assms antisympD)

lemma comparator_converse:
  assumes "comparator cmp"
  shows "comparator (\<lambda>x y. cmp y x)"
proof -
  from assms interpret comp: comparator cmp .
  show ?thesis by (unfold_locales, auto simp: comp.eq comp.sym intro: comp.trans)
qed

lemma comparator_composition:
  assumes "comparator cmp" and "inj f"
  shows "comparator (\<lambda>x y. cmp (f x) (f y))"
proof -
  from assms(1) interpret comp: comparator cmp .
  from assms(2) have *: "x = y" if "f x = f y" for x y using that by (rule injD)
  show ?thesis by (unfold_locales, auto simp: comp.sym comp.eq * intro: comp.trans)
qed

(*
subsection \<open>Syntactic Type Class for Default Elements\<close>

text \<open>We do not want to use the existing type-class @{class default}, but instead introduce a new one:\<close>

class oalist_dflt = fixes dflt::'a

simproc_setup reorient_dflt ("dflt = x") = Reorient_Proc.proc
*)

subsection \<open>Type \<open>key_order\<close>\<close>

typedef 'a key_order = "{compare :: 'a comparator. comparator compare}"
  morphisms key_compare Abs_key_order
proof -
  from well_order_on obtain r where "well_order_on (UNIV::'a set) r" ..
  hence "linear_order r" by (simp only: well_order_on_def)
  hence lin: "(x, y) \<in> r \<or> (y, x) \<in> r" for x y
    by (metis Diff_iff Linear_order_in_diff_Id UNIV_I \<open>well_order r\<close> well_order_on_Field)
  have antisym: "(x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y" for x y
    by (meson \<open>linear_order r\<close> antisymD linear_order_on_def partial_order_on_def)
  have trans: "(x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r" for x y z
    by (meson \<open>linear_order r\<close> linear_order_on_def order_on_defs(1) partial_order_on_def trans_def)
  define comp where "comp = (\<lambda>x y. if (x, y) \<in> r then if (y, x) \<in> r then Eq else Lt else Gt)"
  show ?thesis
  proof (rule, simp)
    show "comparator comp"
    proof (standard, simp_all add: comp_def split: if_splits, intro impI)
      fix x y
      assume "(x, y) \<in> r" and "(y, x) \<in> r"
      thus "x = y" by (rule antisym)
    next
      fix x y
      assume "(x, y) \<notin> r"
      with lin show "(y, x) \<in> r" by blast
    next
      fix x y z
      assume "(y, x) \<notin> r" and "(z, y) \<notin> r"
      assume "(x, y) \<in> r" and "(y, z) \<in> r"
      hence "(x, z) \<in> r" by (rule trans)
      moreover have "(z, x) \<notin> r"
      proof
        assume "(z, x) \<in> r"
        with \<open>(x, z) \<in> r\<close> have "x = z" by (rule antisym)
        from \<open>(z, y) \<notin> r\<close> \<open>(x, y) \<in> r\<close> show False unfolding \<open>x = z\<close> ..
      qed
      ultimately show "(z, x) \<notin> r \<and> ((z, x) \<notin> r \<longrightarrow> (x, z) \<in> r)" by simp
    qed
  qed
qed

lemma comparator_key_compare [simp, intro!]: "comparator (key_compare ko)"
  using key_compare[of ko] by simp

instantiation key_order :: (type) equal
begin

definition equal_key_order :: "'a key_order \<Rightarrow> 'a key_order \<Rightarrow> bool" where "equal_key_order = (=)"

instance by (standard, simp add: equal_key_order_def)

end

setup_lifting type_definition_key_order

instantiation key_order :: (type) uminus
begin

lift_definition uminus_key_order :: "'a key_order \<Rightarrow> 'a key_order" is "\<lambda>c x y. c y x"
  by (fact comparator_converse)

instance ..

end

lift_definition le_of_key_order :: "'a key_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" is "\<lambda>cmp. le_of_comp cmp" .

lift_definition lt_of_key_order :: "'a key_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" is "\<lambda>cmp. lt_of_comp cmp" .

definition key_order_of_ord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a key_order"
  where "key_order_of_ord ord = Abs_key_order (comp_of_ord ord)"

lift_definition key_order_of_le :: "'a::linorder key_order" is comparator_of
  by (fact comparator_of)

interpretation key_order_lin: linorder "le_of_key_order ko" "lt_of_key_order ko"
proof transfer
  fix comp::"'a comparator"
  assume "comparator comp"
  then interpret comp: comparator comp .
  show "class.linorder comp.le comp.lt" by (fact comp.linorder)
qed

lemma le_of_key_order_alt: "le_of_key_order ko x y = (key_compare ko x y \<noteq> Gt)"
  by (transfer, simp add: comparator.nGt_le_conv)

lemma lt_of_key_order_alt: "lt_of_key_order ko x y = (key_compare ko x y = Lt)"
  by (transfer, meson comparator.Lt_lt_conv)

lemma key_compare_Gt: "key_compare ko x y = Gt \<longleftrightarrow> key_compare ko y x = Lt"
  by (transfer, meson comparator.nGt_le_conv comparator.nLt_le_conv)

lemma key_compare_Eq: "key_compare ko x y = Eq \<longleftrightarrow> x = y"
  by (transfer, simp add: comparator.eq)

lemma key_compare_same [simp]: "key_compare ko x x = Eq"
  by (simp add: key_compare_Eq)

lemma uminus_key_compare [simp]: "invert_order (key_compare ko x y) = key_compare ko y x"
  by (transfer, simp add: comparator.sym)

lemma key_compare_uminus [simp]: "key_compare (- ko) x y = key_compare ko y x"
  by (transfer, rule refl)

lemma uminus_key_order_sameD:
  assumes "- ko = (ko::'a key_order)"
  shows "x = (y::'a)"
proof (rule ccontr)
  assume "x \<noteq> y"
  hence "key_compare ko x y \<noteq> Eq" by (simp add: key_compare_Eq)
  hence "key_compare ko x y \<noteq> invert_order (key_compare ko x y)"
    by (metis invert_order.elims order.distinct(5))
  also have "invert_order (key_compare ko x y) = key_compare (- ko) x y" by simp
  finally have "- ko \<noteq> ko" by (auto simp del: key_compare_uminus)
  thus False using assms ..
qed

lemma key_compare_key_order_of_ord:
  assumes "antisymp ord" and "transp ord" and "\<And>x y. ord x y \<or> ord y x"
  shows "key_compare (key_order_of_ord ord) = (\<lambda>x y. if ord x y then if x = y then Eq else Lt else Gt)"
proof -
  have eq: "key_compare (key_order_of_ord ord) = comp_of_ord ord"
    unfolding key_order_of_ord_def comp_of_ord_eq_comp_of_ords[OF assms(1)]
  proof (rule Abs_key_order_inverse, simp, rule comp_of_ords, unfold_locales)
    fix x
    from assms(3) show "ord x x" by blast
  next
    fix x y z
    assume "ord x y" and "ord y z"
    with assms(2) show "ord x z" by (rule transpD)
  next
    fix x y
    assume "ord x y" and "ord y x"
    with assms(1) show "x = y" by (rule antisympD)
  qed (rule refl, rule assms(3))
  have *: "x = y" if "ord x y" and "ord y x" for x y using assms(1) that by (rule antisympD)
  show ?thesis by (rule, rule, auto simp: eq comp_of_ord_def intro: *)
qed

lemma key_compare_key_order_of_le:
  "key_compare key_order_of_le = (\<lambda>x y. if x < y then Lt else if x = y then Eq else Gt)"
  by (transfer, intro ext, fact comparator_of_def)

subsection \<open>Invariant in Context @{locale comparator}\<close>

context comparator
begin

definition oalist_inv_raw :: "('a \<times> 'b::zero) list \<Rightarrow> bool"
  where "oalist_inv_raw xs \<longleftrightarrow> (0 \<notin> snd ` set xs \<and> sorted_wrt lt (map fst xs))"

lemma oalist_inv_rawI:
  assumes "0 \<notin> snd ` set xs" and "sorted_wrt lt (map fst xs)"
  shows "oalist_inv_raw xs"
  unfolding oalist_inv_raw_def using assms unfolding fst_conv snd_conv by blast

lemma oalist_inv_rawD1:
  assumes "oalist_inv_raw xs"
  shows "0 \<notin> snd ` set xs"
  using assms unfolding oalist_inv_raw_def fst_conv by blast

lemma oalist_inv_rawD2:
  assumes "oalist_inv_raw xs"
  shows "sorted_wrt lt (map fst xs)"
  using assms unfolding oalist_inv_raw_def fst_conv snd_conv by blast

lemma oalist_inv_raw_Nil: "oalist_inv_raw []"
  by (simp add: oalist_inv_raw_def)

lemma oalist_inv_raw_singleton: "oalist_inv_raw [(k, v)] \<longleftrightarrow> (v \<noteq> 0)"
  by (auto simp: oalist_inv_raw_def)

lemma oalist_inv_raw_ConsI:
  assumes "oalist_inv_raw xs" and "v \<noteq> 0" and "xs \<noteq> [] \<Longrightarrow> lt k (fst (hd xs))"
  shows "oalist_inv_raw ((k, v) # xs)"
proof (rule oalist_inv_rawI)
  from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
  with assms(2) show "0 \<notin> snd ` set ((k, v) # xs)" by simp
next
  show "sorted_wrt lt (map fst ((k, v) # xs))"
  proof (cases "xs = []")
    case True
    thus ?thesis by simp
  next
    case False
    then obtain k' v' xs' where xs: "xs = (k', v') # xs'" by (metis list.exhaust prod.exhaust)
    from assms(3)[OF False] have "lt k k'" by (simp add: xs)
    moreover from assms(1) have "sorted_wrt lt (map fst xs)" by (rule oalist_inv_rawD2)
    ultimately show "sorted_wrt lt (map fst ((k, v) # xs))"
      by (simp add: xs sorted_wrt2[OF transp_less] del: sorted_wrt.simps)
  qed
qed

lemma oalist_inv_raw_ConsD1:
  assumes "oalist_inv_raw (x # xs)"
  shows "oalist_inv_raw xs"
proof (rule oalist_inv_rawI)
  from assms have "0 \<notin> snd ` set (x # xs)" by (rule oalist_inv_rawD1)
  thus "0 \<notin> snd ` set xs" by simp
next
  from assms have "sorted_wrt lt (map fst (x # xs))" by (rule oalist_inv_rawD2)
  thus "sorted_wrt lt (map fst xs)" by simp
qed

lemma oalist_inv_raw_ConsD2:
  assumes "oalist_inv_raw ((k, v) # xs)"
  shows "v \<noteq> 0"
proof -
  from assms have "0 \<notin> snd ` set ((k, v) # xs)" by (rule oalist_inv_rawD1)
  thus ?thesis by auto
qed

lemma oalist_inv_raw_ConsD3:
  assumes "oalist_inv_raw ((k, v) # xs)" and "k' \<in> fst ` set xs"
  shows "lt k k'"
proof -
  from assms(2) obtain x where "x \<in> set xs" and "k' = fst x" by fastforce
  from assms(1) have "sorted_wrt lt (map fst ((k, v) # xs))" by (rule oalist_inv_rawD2)
  hence "\<forall>x\<in>set xs. lt k (fst x)" by simp
  hence "lt k (fst x)" using \<open>x \<in> set xs\<close> ..
  thus ?thesis by (simp only: \<open>k' = fst x\<close>)
qed

lemma oalist_inv_raw_tl:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (tl xs)"
proof (rule oalist_inv_rawI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
  thus "0 \<notin> snd ` set (tl xs)" by (metis (no_types, lifting) image_iff list.set_sel(2) tl_Nil)
next
  show "sorted_wrt lt (map fst (tl xs))"
    by (metis hd_Cons_tl oalist_inv_rawD2 oalist_inv_raw_ConsD1 assms tl_Nil)
qed

lemma oalist_inv_raw_filter:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (filter P xs)"
proof (rule oalist_inv_rawI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
  thus "0 \<notin> snd ` set (filter P xs)" by auto
next
  from assms have "sorted_wrt lt (map fst xs)" by (rule oalist_inv_rawD2)
  thus "sorted_wrt lt (map fst (filter P xs))" by (induct xs, simp, simp)
qed

lemma oalist_inv_raw_map:
  assumes "oalist_inv_raw xs"
    and "\<And>a. snd (f a) = 0 \<Longrightarrow> snd a = 0"
    and "\<And>a b. comp (fst (f a)) (fst (f b)) = comp (fst a) (fst b)"
  shows "oalist_inv_raw (map f xs)"
proof (rule oalist_inv_rawI)
  show "0 \<notin> snd ` set (map f xs)"
  proof (simp, rule)
    assume "0 \<in> snd ` f ` set xs"
    then obtain a where "a \<in> set xs" and "snd (f a) = 0" by fastforce
    from this(2) have "snd a = 0" by (rule assms(2))
    from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
    moreover from \<open>a \<in> set xs\<close> have "0 \<in> snd ` set xs" by (simp add: \<open>snd a = 0\<close>[symmetric])
    ultimately show False ..
  qed
next
  from assms(1) have "sorted_wrt lt (map fst xs)" by (rule oalist_inv_rawD2)
  hence "sorted_wrt (\<lambda>x y. comp (fst x) (fst y) = Lt) xs"
    by (simp only: sorted_wrt_map Lt_lt_conv)
  thus "sorted_wrt lt (map fst (map f xs))"
    by (simp add: sorted_wrt_map Lt_lt_conv[symmetric] assms(3))
qed

lemma oalist_inv_raw_induct [consumes 1, case_names Nil Cons]:
  assumes "oalist_inv_raw xs"
  assumes "P []"
  assumes "\<And>k v xs. oalist_inv_raw ((k, v) # xs) \<Longrightarrow> oalist_inv_raw xs \<Longrightarrow> v \<noteq> 0 \<Longrightarrow>
              (\<And>k'. k' \<in> fst ` set xs \<Longrightarrow> lt k k') \<Longrightarrow> P xs \<Longrightarrow> P ((k, v) # xs)"
  shows "P xs"
  using assms(1)
proof (induct xs)
  case Nil
  from assms(2) show ?case .
next
  case (Cons x xs)
  obtain k v where x: "x = (k, v)" by fastforce
  from Cons(2) have "oalist_inv_raw ((k, v) # xs)" and "oalist_inv_raw xs" and "v \<noteq> 0" unfolding x
    by (this, rule oalist_inv_raw_ConsD1, rule oalist_inv_raw_ConsD2)
  moreover from Cons(2) have "lt k k'" if "k' \<in> fst ` set xs" for k' using that
    unfolding x by (rule oalist_inv_raw_ConsD3)
  moreover from \<open>oalist_inv_raw xs\<close> have "P xs" by (rule Cons(1))
  ultimately show ?case unfolding x by (rule assms(3))
qed

subsection \<open>Operations on Lists of Pairs in Context @{locale comparator}\<close>

type_synonym (in -) ('a, 'b) comp_opt = "'a \<Rightarrow> 'b \<Rightarrow> (order option)"

definition (in -) lookup_dflt :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b::zero"
  where "lookup_dflt xs k = (case map_of xs k of Some v \<Rightarrow> v | None \<Rightarrow> 0)"

text \<open>@{const lookup_dflt} is only an auxiliary function needed for proving some lemmas.\<close>

fun lookup_pair :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b::zero"
where
  "lookup_pair [] x = 0"|
  "lookup_pair ((k, v) # xs) x =
    (case comp x k of
       Lt \<Rightarrow> 0
     | Eq \<Rightarrow> v
     | Gt \<Rightarrow> lookup_pair xs x)"

fun update_by_pair :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by_pair (k, v) [] = (if v = 0 then [] else [(k, v)])"
| "update_by_pair (k, v) ((k', v') # xs) =
  (case comp k k' of Lt \<Rightarrow> (if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | Eq \<Rightarrow> (if v = 0 then xs else (k, v) # xs)
                   | Gt \<Rightarrow> (k', v') # update_by_pair (k, v) xs)"

(* TODO: Add update_by_gr_pair. *)

definition sort_oalist :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
  where "sort_oalist xs = foldr update_by_pair xs []"

fun update_by_fun_pair :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by_fun_pair k f [] = (let v = f 0 in if v = 0 then [] else [(k, v)])"
| "update_by_fun_pair k f ((k', v') # xs) =
  (case comp k k' of Lt \<Rightarrow> (let v = f 0 in if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | Eq \<Rightarrow> (let v = f v' in if v = 0 then xs else (k, v) # xs)
                   | Gt \<Rightarrow> (k', v') # update_by_fun_pair k f xs)"

definition update_by_fun_gr_pair :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
  where "update_by_fun_gr_pair k f xs =
          (if xs = [] then
            (let v = f 0 in if v = 0 then [] else [(k, v)])
          else if comp k (fst (last xs)) = Gt then
            (let v = f 0 in if v = 0 then xs else xs @ [(k, v)])
          else
            update_by_fun_pair k f xs
          )"

fun (in -) map_pair :: "(('a \<times> 'b) \<Rightarrow> ('a \<times> 'c)) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list"
where
  "map_pair f [] = []"
| "map_pair f (kv # xs) =
    (let (k, v) = f kv; aux = map_pair f xs in if v = 0 then aux else (k, v) # aux)"

text \<open>The difference between @{const List.map} and @{const map_pair} is that the latter removes
  @{term 0} values, whereas the former does not.\<close>

abbreviation (in -) map_val_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list"
  where "map_val_pair f \<equiv> map_pair (\<lambda>(k, v). (k, f k v))"

fun map2_val_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (('a \<times> 'b) list \<Rightarrow> ('a \<times> 'd) list) \<Rightarrow>
                      (('a \<times> 'c) list \<Rightarrow> ('a \<times> 'd) list) \<Rightarrow>
                      ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> ('a \<times> 'd::zero) list"
where
  "map2_val_pair f g h xs [] = g xs"
| "map2_val_pair f g h [] ys = h ys"
| "map2_val_pair f g h ((kx, vx) # xs) ((ky, vy) # ys) =
    (case comp kx ky of
             Lt    \<Rightarrow> (let v = f kx vx 0; aux = map2_val_pair f g h xs ((ky, vy) # ys) in if v = 0 then aux else (kx, v) # aux)
           | Eq   \<Rightarrow> (let v = f kx vx vy; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (kx, v) # aux)
           | Gt \<Rightarrow> (let v = f ky 0 vy; aux = map2_val_pair f g h ((kx, vx) # xs) ys in if v = 0 then aux else (ky, v) # aux))"

fun lex_ord_pair :: "('a \<Rightarrow> (('b, 'c) comp_opt)) \<Rightarrow> (('a \<times> 'b::zero) list, ('a \<times> 'c::zero) list) comp_opt"
where
  "lex_ord_pair f []       []       = Some Eq"|
  "lex_ord_pair f []       ((ky, vy) # ys) =
    (let aux = f ky 0 vy in if aux = Some Eq then lex_ord_pair f [] ys else aux)"|
  "lex_ord_pair f ((kx, vx) # xs) []       =
    (let aux = f kx vx 0 in if aux = Some Eq then lex_ord_pair f xs [] else aux)"|
  "lex_ord_pair f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case comp kx ky of
             Lt    \<Rightarrow> (let aux = f kx vx 0 in if aux = Some Eq then lex_ord_pair f xs ((ky, vy) # ys) else aux)
           | Eq   \<Rightarrow> (let aux = f kx vx vy in if aux = Some Eq then lex_ord_pair f xs ys else aux)
           | Gt \<Rightarrow> (let aux = f ky 0 vy in if aux = Some Eq then lex_ord_pair f ((kx, vx) # xs) ys else aux))"

fun prod_ord_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> bool"
where
  "prod_ord_pair f []       []       = True"|
  "prod_ord_pair f []       ((ky, vy) # ys) = (f ky 0 vy \<and> prod_ord_pair f [] ys)"|
  "prod_ord_pair f ((kx, vx) # xs) []       = (f kx vx 0 \<and> prod_ord_pair f xs [])"|
  "prod_ord_pair f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case comp kx ky of
             Lt    \<Rightarrow> (f kx vx 0 \<and> prod_ord_pair f xs ((ky, vy) # ys))
           | Eq   \<Rightarrow> (f kx vx vy \<and> prod_ord_pair f xs ys)
           | Gt \<Rightarrow> (f ky 0 vy \<and> prod_ord_pair f ((kx, vx) # xs) ys))"

text \<open>@{const prod_ord_pair} is actually just a special case of @{const lex_ord_pair}, as proved below
  in lemma \<open>prod_ord_pair_eq_lex_ord_pair\<close>.\<close>

subsubsection \<open>@{const lookup_pair}\<close>

lemma lookup_pair_eq_0:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair xs k = 0 \<longleftrightarrow> (k \<notin> fst ` set xs)"
  using assms
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  show ?case
  proof (simp add: Cons(3) eq split: order.splits, rule, simp_all only: atomize_imp[symmetric])
    assume "comp k k' = Lt"
    hence "k \<noteq> k'" by auto
    moreover have "k \<notin> fst ` set xs"
    proof
      assume "k \<in> fst ` set xs"
      hence "lt k' k" by (rule Cons(4))
      with \<open>comp k k' = Lt\<close> show False by (simp add: Lt_lt_conv)
    qed
    ultimately show "k \<noteq> k' \<and> k \<notin> fst ` set xs" ..
  next
    assume "comp k k' = Gt"
    hence "k \<noteq> k'" by auto
    thus "(lookup_pair xs k = 0) = (k \<noteq> k' \<and> k \<notin> fst ` set xs)" by (simp add: Cons(5))
  qed
qed

lemma lookup_pair_eq_value:
  assumes "oalist_inv_raw xs" and "v \<noteq> 0"
  shows "lookup_pair xs k = v \<longleftrightarrow> ((k, v) \<in> set xs)"
  using assms(1)
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  from assms(2) show ?case by simp
next
  case (Cons k' v' xs)
  have *: "(k', u) \<notin> set xs" for u
  proof
    assume "(k', u) \<in> set xs"
    hence "fst (k', u) \<in> fst ` set xs" by fastforce
    hence "k' \<in> fst ` set xs" by simp
    hence "lt k' k'" by (rule Cons(4))
    thus False by (simp add: lt_of_key_order_alt[symmetric])
  qed
  show ?case
  proof (simp add: assms(2) Cons(5) eq split: order.split, intro conjI impI)
    assume "comp k k' = Lt"
    show "(k, v) \<notin> set xs"
    proof
      assume "(k, v) \<in> set xs"
      hence "fst (k, v) \<in> fst ` set xs" by fastforce
      hence "k \<in> fst ` set xs" by simp
      hence "lt k' k" by (rule Cons(4))
      with \<open>comp k k' = Lt\<close> show False by (simp add: Lt_lt_conv)
    qed
  qed (auto simp: *)
qed

lemma lookup_pair_eq_valueI:
  assumes "oalist_inv_raw xs" and "(k, v) \<in> set xs"
  shows "lookup_pair xs k = v"
proof -
  from assms(2) have "v \<in> snd ` set xs" by force
  moreover from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
  ultimately have "v \<noteq> 0" by blast
  with assms show ?thesis by (simp add: lookup_pair_eq_value)
qed

lemma lookup_dflt_eq_lookup_pair:
  assumes "oalist_inv_raw xs"
  shows "lookup_dflt xs = lookup_pair xs"
proof (rule, simp add: lookup_dflt_def split: option.split, intro conjI impI allI)
  fix k
  assume "map_of xs k = None"
  with assms show "lookup_pair xs k = 0" by (simp add: lookup_pair_eq_0 map_of_eq_None_iff)
next
  fix k v
  assume "map_of xs k = Some v"
  hence "(k, v) \<in> set xs" by (rule map_of_SomeD)
  with assms have "lookup_pair xs k = v" by (rule lookup_pair_eq_valueI)
  thus "v = lookup_pair xs k" by (rule HOL.sym)
qed

lemma lookup_pair_inj:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys" and "lookup_pair xs = lookup_pair ys"
  shows "xs = ys"
  using assms
proof (induct xs arbitrary: ys rule: oalist_inv_raw_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k' v' ys)
    have "v' = lookup_pair ((k', v') # ys) k'" by simp
    also have "... = lookup_pair [] k'" by (simp only: Cons(6))
    also have "... = 0" by simp
    finally have "v' = 0" .
    with Cons(3) show ?case ..
  qed
next
  case *: (Cons k v xs)
  from *(6, 7) show ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    have "v = lookup_pair ((k, v) # xs) k" by simp
    also have "... = lookup_pair [] k" by (simp only: Nil)
    also have "... = 0" by simp
    finally have "v = 0" .
    with *(3) show ?case ..
  next
    case (Cons k' v' ys)
    show ?case
    proof (cases "comp k k'")
      case Lt
      hence "\<not> lt k' k" by (simp add: Lt_lt_conv)
      with Cons(4) have "k \<notin> fst ` set ys" by blast
      moreover from Lt have "k \<noteq> k'" by auto
      ultimately have "k \<notin> fst ` set ((k', v') # ys)" by simp
      hence "0 = lookup_pair ((k', v') # ys) k"
        by (simp add: lookup_pair_eq_0[OF Cons(1)] del: lookup_pair.simps)
      also have "... = lookup_pair ((k, v) # xs) k" by (simp only: Cons(6))
      also have "... = v" by simp
      finally have "v = 0" by simp
      with *(3) show ?thesis ..
    next
      case Eq
      hence "k' = k" by (simp only: eq)
      have "v' = lookup_pair ((k', v') # ys) k'" by simp
      also have "... = lookup_pair ((k, v) # xs) k" by (simp only: Cons(6) \<open>k' = k\<close>)
      also have "... = v" by simp
      finally have "v' = v" .
      moreover note \<open>k' = k\<close>
      moreover from Cons(2) have "xs = ys"
      proof (rule *(5))
        show "lookup_pair xs = lookup_pair ys"
        proof
          fix k0
          show "lookup_pair xs k0 = lookup_pair ys k0"
          proof (cases "lt k k0")
            case True
            hence eq: "comp k0 k = Gt"
              by (simp add: Gt_lt_conv)
            have "lookup_pair xs k0 = lookup_pair ((k, v) # xs) k0" by (simp add: eq)
            also have "... = lookup_pair ((k, v') # ys) k0" by (simp only: Cons(6) \<open>k' = k\<close>)
            also have "... = lookup_pair ys k0" by (simp add: eq)
            finally show ?thesis .
          next
            case False
            with *(4) have "k0 \<notin> fst ` set xs" by blast
            with *(2) have eq: "lookup_pair xs k0 = 0" by (simp add: lookup_pair_eq_0)
            from False Cons(4) have "k0 \<notin> fst ` set ys" unfolding \<open>k' = k\<close> by blast
            with Cons(2) have "lookup_pair ys k0 = 0" by (simp add: lookup_pair_eq_0)
            with eq show ?thesis by simp
          qed
        qed
      qed
      ultimately show ?thesis by simp
    next
      case Gt
      hence "\<not> lt k k'" by (simp add: Gt_lt_conv)
      with *(4) have "k' \<notin> fst ` set xs" by blast
      moreover from Gt have "k' \<noteq> k" by auto
      ultimately have "k' \<notin> fst ` set ((k, v) # xs)" by simp
      hence "0 = lookup_pair ((k, v) # xs) k'"
        by (simp add: lookup_pair_eq_0[OF *(1)] del: lookup_pair.simps)
      also have "... = lookup_pair ((k', v') # ys) k'" by (simp only: Cons(6))
      also have "... = v'" by simp
      finally have "v' = 0" by simp
      with Cons(3) show ?thesis ..
    qed
  qed
qed

lemma lookup_pair_tl:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (tl xs) k = (if (\<forall>k'\<in>fst ` set xs. le k k') then 0 else lookup_pair xs k)"
proof -
  from assms have 1: "oalist_inv_raw (tl xs)" by (rule oalist_inv_raw_tl)
  show ?thesis
  proof (split if_split, intro conjI impI)
    assume *: "\<forall>x\<in>fst ` set xs. le k x"
    show "lookup_pair (tl xs) k = 0"
    proof (simp add: lookup_pair_eq_0[OF 1], rule)
      assume k_in: "k \<in> fst ` set (tl xs)"
      hence "xs \<noteq> []" by auto
      then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
      have "k' \<in> fst ` set xs" unfolding xs by fastforce
      with * have "le k k'" ..
      from assms have "oalist_inv_raw ((k', v') # ys)" by (simp only: xs)
      moreover from k_in have "k \<in> fst ` set ys" by (simp add: xs)
      ultimately have "lt k' k" by (rule oalist_inv_raw_ConsD3)
      with \<open>le k k'\<close> show False by simp
    qed
  next
    assume "\<not> (\<forall>k'\<in>fst ` set xs. le k k')"
    hence "\<exists>x\<in>fst ` set xs. \<not> le k x" by simp
    then obtain k'' where k''_in: "k'' \<in> fst ` set xs" and "\<not> le k k''" ..
    from this(2) have "lt k'' k" by simp
    from k''_in have "xs \<noteq> []" by auto
    then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
    from k''_in have "k'' = k' \<or> k'' \<in> fst ` set ys" by (simp add: xs)
    hence "lt k' k"
    proof
      assume "k'' = k'"
      with \<open>lt k'' k\<close> show ?thesis by simp
    next
      from assms have "oalist_inv_raw ((k', v') # ys)" by (simp only: xs)
      moreover assume "k'' \<in> fst ` set ys"
      ultimately have "lt k' k''" by (rule oalist_inv_raw_ConsD3)
      thus ?thesis using \<open>lt k'' k\<close> by (rule less_trans)
    qed
    hence "comp k k' = Gt" by (simp add: Gt_lt_conv)
    thus "lookup_pair (tl xs) k = lookup_pair xs k" by (simp add: xs lt_of_key_order_alt)
  qed
qed

lemma lookup_pair_tl':
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (tl xs) k = (if k = fst (hd xs) then 0 else lookup_pair xs k)"
proof -
  from assms have 1: "oalist_inv_raw (tl xs)" by (rule oalist_inv_raw_tl)
  show ?thesis
  proof (split if_split, intro conjI impI)
    assume k: "k = fst (hd xs)"
    show "lookup_pair (tl xs) k = 0"
    proof (simp add: lookup_pair_eq_0[OF 1], rule)
      assume k_in: "k \<in> fst ` set (tl xs)"
      hence "xs \<noteq> []" by auto
      then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
      from assms have "oalist_inv_raw ((k', v') # ys)" by (simp only: xs)
      moreover from k_in have "k' \<in> fst ` set ys" by (simp add: k xs)
      ultimately have "lt k' k'" by (rule oalist_inv_raw_ConsD3)
      thus False by simp
    qed
  next
    assume "k \<noteq> fst (hd xs)"
    show "lookup_pair (tl xs) k = lookup_pair xs k"
    proof (cases "xs = []")
      case True
      show ?thesis by (simp add: True)
    next
      case False
      then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
      show ?thesis
      proof (simp add: xs eq Lt_lt_conv split: order.split, intro conjI impI)
        from \<open>k \<noteq> fst (hd xs)\<close> have "k \<noteq> k'" by (simp add: xs)
        moreover assume "k = k'"
        ultimately show "lookup_pair ys k' = v'" ..
      next
        assume "lt k k'"
        from assms have "oalist_inv_raw ys" unfolding xs by (rule oalist_inv_raw_ConsD1)
        moreover have "k \<notin> fst ` set ys"
        proof
          assume "k \<in> fst ` set ys"
          with assms have "lt k' k" unfolding xs by (rule oalist_inv_raw_ConsD3)
          with \<open>lt k k'\<close> show False by simp
        qed
        ultimately show "lookup_pair ys k = 0" by (simp add: lookup_pair_eq_0)
      qed
    qed
  qed
qed

lemma lookup_pair_filter:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (filter P xs) k = (let v = lookup_pair xs k in if P (k, v) then v else 0)"
  using assms
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  show ?case
  proof (simp add: Cons(5) Let_def eq split: order.split, intro conjI impI)
    show "lookup_pair xs k' = 0"
    proof (simp add: lookup_pair_eq_0 Cons(2), rule)
      assume "k' \<in> fst ` set xs"
      hence "lt k' k'" by (rule Cons(4))
      thus False by simp
    qed
  next
    assume "comp k k' = Lt"
    hence "lt k k'" by (simp only: Lt_lt_conv)
    show "lookup_pair xs k = 0"
    proof (simp add: lookup_pair_eq_0 Cons(2), rule)
      assume "k \<in> fst ` set xs"
      hence "lt k' k" by (rule Cons(4))
      with \<open>lt k k'\<close> show False by simp
    qed
  qed
qed

lemma lookup_pair_map:
  assumes "oalist_inv_raw xs"
    and "\<And>k'. snd (f (k', 0)) = 0"
    and "\<And>a b. comp (fst (f a)) (fst (f b)) = comp (fst a) (fst b)"
  shows "lookup_pair (map f xs) (fst (f (k, v))) = snd (f (k, lookup_pair xs k))"
  using assms(1)
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by (simp add: assms(2))
next
  case (Cons k' v' xs)
  obtain k'' v'' where f: "f (k', v') = (k'', v'')" by fastforce
  have "comp k k' = comp (fst (f (k, v))) (fst (f (k', v')))"
    by (simp add: assms(3))
  also have "... = comp (fst (f (k, v))) k''" by (simp add: f)
  finally have eq0: "comp k k' = comp (fst (f (k, v))) k''" .
  show ?case
  proof (simp add: assms(2) split: order.split, intro conjI impI, simp add: eq)
    assume "k = k'"
    hence "lookup_pair (f (k', v') # map f xs) (fst (f (k', v))) =
            lookup_pair (f (k', v') # map f xs) (fst (f (k, v)))" by simp
    also have "... = snd (f (k', v'))" by (simp add: f eq0[symmetric], simp add: \<open>k = k'\<close>)
    finally show "lookup_pair (f (k', v') # map f xs) (fst (f (k', v))) = snd (f (k', v'))" .
  qed (simp_all add: f eq0 Cons(5))
qed

lemma lookup_pair_Cons:
  assumes "oalist_inv_raw ((k, v) # xs)"
  shows "lookup_pair ((k, v) # xs) k0 = (if k = k0 then v else lookup_pair xs k0)"
proof (simp add: eq split: order.split, intro impI)
  assume "comp k0 k = Lt"
  from assms have inv: "oalist_inv_raw xs" by (rule oalist_inv_raw_ConsD1)
  show "lookup_pair xs k0 = 0"
  proof (simp only: lookup_pair_eq_0[OF inv], rule)
    assume "k0 \<in> fst ` set xs"
    with assms have "lt k k0" by (rule oalist_inv_raw_ConsD3)
    with \<open>comp k0 k = Lt\<close> show False by (simp add: Lt_lt_conv)
  qed
qed

lemma lookup_pair_single: "lookup_pair [(k, v)] k0 = (if k = k0 then v else 0)"
  by (simp add: eq split: order.split)

subsubsection \<open>@{const update_by_pair}\<close>

lemma set_update_by_pair_subset: "set (update_by_pair kv xs) \<subseteq> insert kv (set xs)"
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  have 1: "set xs \<subseteq> insert a (insert b (set xs))" for a b by auto
  have 2: "set (update_by_pair kv xs) \<subseteq> insert kv (insert (k', v') (set xs))" for kv
    using Cons by blast
  show ?case by (simp add: x kv 1 2 split: order.split)
qed

lemma update_by_pair_sorted:
  assumes "sorted_wrt lt (map fst xs)"
  shows "sorted_wrt lt (map fst (update_by_pair kv xs))"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "sorted_wrt lt (k' # (map fst xs))" by (simp add: x)
  hence 2: "sorted_wrt lt (map fst xs)" using sorted_wrt.elims(3) by fastforce
  hence 3: "sorted_wrt lt (map fst (update_by_pair (k, u) xs))" for u by (rule Cons(1))
  have 4: "sorted_wrt lt (k' # map fst (update_by_pair (k, u) xs))"
    if *: "comp k k' = Gt" for u
  proof (simp, intro conjI ballI)
    fix y
    assume "y \<in> set (update_by_pair (k, u) xs)"
    also from set_update_by_pair_subset have "... \<subseteq> insert (k, u) (set xs)" .
    finally have "y = (k, u) \<or> y \<in> set xs" by simp
    thus "lt k' (fst y)"
    proof
      assume "y = (k, u)"
      hence "fst y = k" by simp
      with * show ?thesis by (simp only: Gt_lt_conv)
    next
      from 1 have 5: "\<forall>y \<in> fst ` set xs. lt k' y" by simp
      assume "y \<in> set xs"
      hence "fst y \<in> fst ` set xs" by simp
      with 5 show ?thesis ..
    qed
  qed (fact 3)
  show ?case
    by (simp add: kv x 1 2 4 sorted_wrt2 split: order.split del: sorted_wrt.simps,
        intro conjI impI, simp add: 1 eq del: sorted_wrt.simps, simp add: Lt_lt_conv)
qed

lemma update_by_pair_not_0:
  assumes "0 \<notin> snd ` set xs"
  shows "0 \<notin> snd ` set (update_by_pair kv xs)"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "v' \<noteq> 0" and 2: "0 \<notin> snd ` set xs" by (auto simp: x)
  from 2 have 3: "0 \<notin> snd ` set (update_by_pair (k, u) xs)" for u by (rule Cons(1))
  show ?case by (auto simp: kv x 1 2 3 split: order.split)
qed

corollary oalist_inv_raw_update_by_pair:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (update_by_pair kv xs)"
proof (rule oalist_inv_rawI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_inv_rawD1)
  thus "0 \<notin> snd ` set (update_by_pair kv xs)" by (rule update_by_pair_not_0)
next
  from assms have "sorted_wrt lt (map fst xs)" by (rule oalist_inv_rawD2)
  thus "sorted_wrt lt (map fst (update_by_pair kv xs))" by (rule update_by_pair_sorted)
qed

lemma update_by_pair_less:
  assumes "v \<noteq> 0" and "xs = [] \<or> comp k (fst (hd xs)) = Lt"
  shows "update_by_pair (k, v) xs = (k, v) # xs"
  using assms(2)
proof (induct xs)
case Nil
  from assms(1) show ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  from Cons(2) have "comp k k' = Lt" by (simp add: x)
  with assms(1) show ?case by (simp add: x)
qed

lemma lookup_pair_update_by_pair:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (update_by_pair (k1, v) xs) k2 = (if k1 = k2 then v else lookup_pair xs k2)"
  using assms
proof (induct xs arbitrary: v rule: oalist_inv_raw_induct)
  case Nil
  show ?case by (simp split: order.split, simp add: eq)
next
  case (Cons k' v' xs)
  show ?case
  proof (split if_split, intro conjI impI)
    assume "k1 = k2"
    with Cons(5) have eq0: "lookup_pair (update_by_pair (k2, u) xs) k2 = u" for u
      by (simp del: update_by_pair.simps)
    show "lookup_pair (update_by_pair (k1, v) ((k', v') # xs)) k2 = v"
    proof (simp add: \<open>k1 = k2\<close> eq0 split: order.split, intro conjI impI)
      assume "comp k2 k' = Eq"
      hence "\<not> lt k' k2" by (simp add: eq)
      with Cons(4) have "k2 \<notin> fst ` set xs" by auto
      thus "lookup_pair xs k2 = 0" using Cons(2) by (simp add: lookup_pair_eq_0)
    qed
  next
    assume "k1 \<noteq> k2"
    with Cons(5) have eq0: "lookup_pair (update_by_pair (k1, u) xs) k2 = lookup_pair xs k2" for u
      by (simp del: update_by_pair.simps)
    have *: "lookup_pair xs k2 = 0" if "lt k2 k'"
    proof -
      from \<open>lt k2 k'\<close> have "\<not> lt k' k2" by auto
      with Cons(4) have "k2 \<notin> fst ` set xs" by auto
      thus "lookup_pair xs k2 = 0" using Cons(2) by (simp add: lookup_pair_eq_0)
    qed
    show "lookup_pair (update_by_pair (k1, v) ((k', v') # xs)) k2 = lookup_pair ((k', v') # xs) k2"
      by (simp add: \<open>k1 \<noteq> k2\<close> eq0 split: order.split,
          auto intro: * simp: \<open>k1 \<noteq> k2\<close>[symmetric] eq Gt_lt_conv Lt_lt_conv)
  qed
qed

corollary update_by_pair_id:
  assumes "oalist_inv_raw xs" and "lookup_pair xs k = v"
  shows "update_by_pair (k, v) xs = xs"
proof (rule lookup_pair_inj, rule oalist_inv_raw_update_by_pair)
  show "lookup_pair (update_by_pair (k, v) xs) = lookup_pair xs"
  proof
    fix k0
    from assms(2) show "lookup_pair (update_by_pair (k, v) xs) k0 = lookup_pair xs k0"
      by (auto simp: lookup_pair_update_by_pair[OF assms(1)])
  qed
qed fact+

lemma set_update_by_pair:
  assumes "oalist_inv_raw xs" and "v \<noteq> 0"
  shows "set (update_by_pair (k, v) xs) = insert (k, v) (set xs - range (Pair k))" (is "?A = ?B")
proof (rule set_eqI)
  fix x::"'a \<times> 'b"
  obtain k' v' where x: "x = (k', v')" by fastforce
  from assms(1) have inv: "oalist_inv_raw (update_by_pair (k, v) xs)"
    by (rule oalist_inv_raw_update_by_pair)
  show "(x \<in> ?A) \<longleftrightarrow> (x \<in> ?B)"
  proof (cases "v' = 0")
    case True
    have "0 \<notin> snd ` set (update_by_pair (k, v) xs)" and "0 \<notin> snd ` set xs"
      by (rule oalist_inv_rawD1, fact)+
    hence "(k', 0) \<notin> set (update_by_pair (k, v) xs)" and "(k', 0) \<notin> set xs"
      using image_iff by fastforce+
    thus ?thesis by (simp add: x True assms(2))
  next
    case False
    show ?thesis
      by (auto simp: x lookup_pair_eq_value[OF inv False, symmetric] lookup_pair_eq_value[OF assms(1) False]
          lookup_pair_update_by_pair[OF assms(1)])
  qed
qed

lemma set_update_by_pair_zero:
  assumes "oalist_inv_raw xs"
  shows "set (update_by_pair (k, 0) xs) = set xs - range (Pair k)" (is "?A = ?B")
proof (rule set_eqI)
  fix x::"'a \<times> 'b"
  obtain k' v' where x: "x = (k', v')" by fastforce
  from assms(1) have inv: "oalist_inv_raw (update_by_pair (k, 0) xs)"
    by (rule oalist_inv_raw_update_by_pair)
  show "(x \<in> ?A) \<longleftrightarrow> (x \<in> ?B)"
  proof (cases "v' = 0")
    case True
    have "0 \<notin> snd ` set (update_by_pair (k, 0) xs)" and "0 \<notin> snd ` set xs"
      by (rule oalist_inv_rawD1, fact)+
    hence "(k', 0) \<notin> set (update_by_pair (k, 0) xs)" and "(k', 0) \<notin> set xs"
      using image_iff by fastforce+
    thus ?thesis by (simp add: x True)
  next
    case False
    show ?thesis
      by (auto simp: x lookup_pair_eq_value[OF inv False, symmetric] lookup_pair_eq_value[OF assms False]
          lookup_pair_update_by_pair[OF assms] False)
  qed
qed

subsubsection \<open>@{const update_by_fun_pair} and @{const update_by_fun_gr_pair}\<close>

lemma update_by_fun_pair_eq_update_by_pair:
  assumes "oalist_inv_raw xs"
  shows "update_by_fun_pair k f xs = update_by_pair (k, f (lookup_pair xs k)) xs"
  using assms by (induct xs rule: oalist_inv_raw_induct, simp, simp split: order.split)

corollary oalist_inv_raw_update_by_fun_pair:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (update_by_fun_pair k f xs)"
  unfolding update_by_fun_pair_eq_update_by_pair[OF assms] using assms by (rule oalist_inv_raw_update_by_pair)

corollary lookup_pair_update_by_fun_pair:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (update_by_fun_pair k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_pair xs k2)"
  by (simp add: update_by_fun_pair_eq_update_by_pair[OF assms] lookup_pair_update_by_pair[OF assms])

lemma update_by_fun_pair_gr:
  assumes "oalist_inv_raw xs" and "xs = [] \<or> comp k (fst (last xs)) = Gt"
  shows "update_by_fun_pair k f xs = xs @ (if f 0 = 0 then [] else [(k, f 0)])"
  using assms
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  from Cons(6) have 1: "comp k (fst (last ((k', v') # xs))) = Gt" by simp
  have eq1: "comp k k' = Gt"
  proof (cases "xs = []")
    case True
    with 1 show ?thesis by simp
  next
    case False
    have "lt k' (fst (last xs))" by (rule Cons(4), simp add: False)
    from False 1 have "comp k (fst (last xs)) = Gt" by simp
    moreover from \<open>lt k' (fst (last xs))\<close> have "comp (fst (last xs)) k' = Gt"
      by (simp add: Gt_lt_conv)
    ultimately show ?thesis
      by (meson Gt_lt_conv less_trans Lt_lt_conv[symmetric])
  qed
  have eq2: "update_by_fun_pair k f xs = xs @ (if f 0 = 0 then [] else [(k, f 0)])"
  proof (rule Cons(5), simp only: disj_commute[of "xs = []"], rule disjCI)
    assume "xs \<noteq> []"
    with 1 show "comp k (fst (last xs)) = Gt" by simp
  qed
  show ?case by (simp split: order.split add: Let_def eq1 eq2)
qed

corollary update_by_fun_gr_pair_eq_update_by_fun_pair:
  assumes "oalist_inv_raw xs"
  shows "update_by_fun_gr_pair k f xs = update_by_fun_pair k f xs"
  by (simp add: update_by_fun_gr_pair_def Let_def update_by_fun_pair_gr[OF assms] split: order.split)

corollary oalist_inv_raw_update_by_fun_gr_pair:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (update_by_fun_gr_pair k f xs)"
  unfolding update_by_fun_pair_eq_update_by_pair[OF assms] update_by_fun_gr_pair_eq_update_by_fun_pair[OF assms]
  using assms by (rule oalist_inv_raw_update_by_pair)

corollary lookup_pair_update_by_fun_gr_pair:
  assumes "oalist_inv_raw xs"
  shows "lookup_pair (update_by_fun_gr_pair k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_pair xs k2)"
  by (simp add: update_by_fun_pair_eq_update_by_pair[OF assms]
      update_by_fun_gr_pair_eq_update_by_fun_pair[OF assms] lookup_pair_update_by_pair[OF assms])

subsubsection \<open>@{const map_pair}\<close>

lemma map_pair_cong:
  assumes "\<And>kv. kv \<in> set xs \<Longrightarrow> f kv = g kv"
  shows "map_pair f xs = map_pair g xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "f x = g x" by (rule Cons(2), simp)
  moreover have "map_pair f xs = map_pair g xs" by (rule Cons(1), rule Cons(2), simp)
  ultimately show ?case by simp
qed

lemma map_pair_subset: "set (map_pair f xs) \<subseteq> f ` set xs"
proof (induct xs rule: map_pair.induct)
  case (1 f)
  show ?case by simp
next
  case (2 f kv xs)
  obtain k v where f: "f kv = (k, v)" by fastforce
  from f[symmetric] refl have *: "set (map_pair f xs) \<subseteq> f ` set xs" by (rule 2)
  show ?case by (simp add: f Let_def, intro conjI impI subset_insertI2 *)
qed

lemma oalist_inv_raw_map_pair:
  assumes "oalist_inv_raw xs"
    and "\<And>a b. comp (fst (f a)) (fst (f b)) = comp (fst a) (fst b)"
  shows "oalist_inv_raw (map_pair f xs)"
  using assms(1)
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  from oalist_inv_raw_Nil show ?case by simp
next
  case (Cons k v xs)
  obtain k' v' where f: "f (k, v) = (k', v')" by fastforce
  show ?case
  proof (simp add: f Let_def Cons(5), rule)
    assume "v' \<noteq> 0"
    with Cons(5) show "oalist_inv_raw ((k', v') # map_pair f xs)"
    proof (rule oalist_inv_raw_ConsI)
      assume "map_pair f xs \<noteq> []"
      hence "hd (map_pair f xs) \<in> set (map_pair f xs)" by simp
      also have "... \<subseteq> f ` set xs" by (fact map_pair_subset)
      finally obtain x where "x \<in> set xs" and eq: "hd (map_pair f xs) = f x" ..
      from this(1) have "fst x \<in> fst ` set xs" by fastforce
      hence "lt k (fst x)" by (rule Cons(4))
      hence "lt (fst (f (k, v))) (fst (f x))"
        by (simp add: Lt_lt_conv[symmetric] assms(2))
      thus "lt k' (fst (hd (map_pair f xs)))" by (simp add: f eq)
    qed
  qed
qed

lemma lookup_pair_map_pair:
  assumes "oalist_inv_raw xs" and "snd (f (k, 0)) = 0"
    and "\<And>a b. comp (fst (f a)) (fst (f b)) = comp (fst a) (fst b)"
  shows "lookup_pair (map_pair f xs) (fst (f (k, v))) = snd (f (k, lookup_pair xs k))"
  using assms(1)
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by (simp add: assms(2))
next
  case (Cons k' v' xs)
  obtain k'' v'' where f: "f (k', v') = (k'', v'')" by fastforce
  have "comp (fst (f (k, v))) k'' = comp (fst (f (k, v))) (fst (f (k', v')))"
    by (simp add: f)
  also have "... = comp k k'"
    by (simp add: assms(3))
  finally have eq0: "comp (fst (f (k, v))) k'' = comp k k'" .
  have *: "lookup_pair xs k = 0" if "comp k k' \<noteq> Gt"
  proof (simp add: lookup_pair_eq_0[OF Cons(2)], rule)
    assume "k \<in> fst ` set xs"
    hence "lt k' k" by (rule Cons(4))
    hence "comp k k' = Gt" by (simp add: Gt_lt_conv)
    with \<open>comp k k' \<noteq> Gt\<close> show False ..
  qed
  show ?case
  proof (simp add: assms(2) f Let_def eq0 Cons(5) split: order.split, intro conjI impI)
    assume "comp k k' = Lt"
    hence "comp k k' \<noteq> Gt" by simp
    hence "lookup_pair xs k = 0" by (rule *)
    thus "snd (f (k, lookup_pair xs k)) = 0" by (simp add: assms(2))
  next
    assume "v'' = 0"
    assume "comp k k' = Eq"
    hence "k = k'" and "comp k k' \<noteq> Gt" by (simp only: eq, simp)
    from this(2) have "lookup_pair xs k = 0" by (rule *)
    hence "snd (f (k, lookup_pair xs k)) = 0" by (simp add: assms(2))
    also have "... = snd (f (k, v'))" by (simp add: \<open>k = k'\<close> f \<open>v'' = 0\<close>)
    finally show "snd (f (k, lookup_pair xs k)) = snd (f (k, v'))" .
  qed (simp add: f eq)
qed

lemma lookup_dflt_map_pair:
  assumes "distinct (map fst xs)" and "snd (f (k, 0)) = 0"
    and "\<And>a b. (fst (f a) = fst (f b)) \<longleftrightarrow> (fst a = fst b)"
  shows "lookup_dflt (map_pair f xs) (fst (f (k, v))) = snd (f (k, lookup_dflt xs k))"
  using assms(1)
proof (induct xs)
  case Nil
  show ?case by (simp add: lookup_dflt_def assms(2))
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k'' v'' where f: "f (k', v') = (k'', v'')" by fastforce
  from Cons(2) have "distinct (map fst xs)" and "k' \<notin> fst ` set xs" by (simp_all add: x)
  from this(1) have eq1: "lookup_dflt (map_pair f xs) (fst (f (k, v))) = snd (f (k, lookup_dflt xs k))"
    by (rule Cons(1))
  have eq2: "lookup_dflt ((a, b) # ys) c = (if c = a then b else lookup_dflt ys c)"
    for a b c and ys::"('b \<times> 'e::zero) list" by (simp add: lookup_dflt_def map_of_Cons_code)
  from \<open>k' \<notin> fst ` set xs\<close> have "map_of xs k' = None" by (simp add: map_of_eq_None_iff)
  hence eq3: "lookup_dflt xs k' = 0" by (simp add: lookup_dflt_def)
  show ?case
  proof (simp add: f Let_def x eq1 eq2 eq3, intro conjI impI)
    assume "k = k'"
    hence "snd (f (k', 0)) = snd (f (k, 0))" by simp
    also have "... = 0" by (fact assms(2))
    finally show "snd (f (k', 0)) = 0" .
  next
    assume "fst (f (k', v)) \<noteq> k''"
    hence "fst (f (k', v)) \<noteq> fst (f (k', v'))" by (simp add: f)
    thus "snd (f (k', 0)) = v''" by (simp add: assms(3))
  next
    assume "k \<noteq> k'"
    assume "fst (f (k, v)) = k''"
    also have "... = fst (f (k', v'))" by (simp add: f)
    finally have "k = k'" by (simp add: assms(3))
    with \<open>k \<noteq> k'\<close> show "v'' = snd (f (k, lookup_dflt xs k))" ..
  qed
qed

lemma distinct_map_pair:
  assumes "distinct (map fst xs)" and "\<And>a b. fst (f a) = fst (f b) \<Longrightarrow> fst a = fst b"
  shows "distinct (map fst (map_pair f xs))"
  using assms(1)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  obtain k v where x: "x = (k, v)" by fastforce
  obtain k' v' where f: "f (k, v) = (k', v')" by fastforce
  from Cons(2) have "distinct (map fst xs)" and "k \<notin> fst ` set xs" by (simp_all add: x)
  from this(1) have 1: "distinct (map fst (map_pair f xs))" by (rule Cons(1))
  show ?case
  proof (simp add: x f Let_def 1, intro impI notI)
    assume "v' \<noteq> 0"
    assume "k' \<in> fst ` set (map_pair f xs)"
    then obtain y where "y \<in> set (map_pair f xs)" and "k' = fst y" ..
    from this(1) map_pair_subset have "y \<in> f ` set xs" ..
    then obtain z where "z \<in> set xs" and "y = f z" ..
    from this(2) have "fst (f z) = k'" by (simp add: \<open>k' = fst y\<close>)
    also have "... = fst (f (k, v))" by (simp add: f)
    finally have "fst z = fst (k, v)" by (rule assms(2))
    also have "... = k" by simp
    finally have "k \<in> fst ` set xs" using \<open>z \<in> set xs\<close> by blast
    with \<open>k \<notin> fst ` set xs\<close> show False ..
  qed
qed

lemma map_val_pair_cong:
  assumes "\<And>k v. (k, v) \<in> set xs \<Longrightarrow> f k v = g k v"
  shows "map_val_pair f xs = map_val_pair g xs"
proof (rule map_pair_cong)
  fix kv
  assume "kv \<in> set xs"
  moreover obtain k v where "kv = (k, v)" by fastforce
  ultimately show "(case kv of (k, v) \<Rightarrow> (k, f k v)) = (case kv of (k, v) \<Rightarrow> (k, g k v))"
    by (simp add: assms)
qed

lemma oalist_inv_raw_map_val_pair:
  assumes "oalist_inv_raw xs"
  shows "oalist_inv_raw (map_val_pair f xs)"
  by (rule oalist_inv_raw_map_pair, fact assms, auto)

lemma lookup_pair_map_val_pair:
  assumes "oalist_inv_raw xs" and "f k 0 = 0"
  shows "lookup_pair (map_val_pair f xs) k = f k (lookup_pair xs k)"
proof -
  let ?f = "\<lambda>(k', v'). (k', f k' v')"
  have "lookup_pair (map_val_pair f xs) k = lookup_pair (map_val_pair f xs) (fst (?f (k, 0)))"
    by simp
  also have "... = snd (?f (k, local.lookup_pair xs k))"
    by (rule lookup_pair_map_pair, fact assms(1), auto simp: assms(2))
  also have "... = f k (lookup_pair xs k)" by simp
  finally show ?thesis .
qed

lemma map_pair_id:
  assumes "oalist_inv_raw xs"
  shows "map_pair id xs = xs"
  using assms
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by simp
next
  case (Cons k v xs')
  show ?case by (simp add: Let_def Cons(3, 5) id_def[symmetric])
qed

subsubsection \<open>@{const map2_val_pair}\<close>

definition map2_val_compat :: "(('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list) \<Rightarrow> bool"
  where "map2_val_compat f \<longleftrightarrow> (\<forall>zs. (oalist_inv_raw zs \<longrightarrow>
                                (oalist_inv_raw (f zs) \<and> fst ` set (f zs) \<subseteq> fst ` set zs)))"

lemma map2_val_compatI:
  assumes "\<And>zs. oalist_inv_raw zs \<Longrightarrow> oalist_inv_raw (f zs)"
    and "\<And>zs. oalist_inv_raw zs \<Longrightarrow> fst ` set (f zs) \<subseteq> fst ` set zs"
  shows "map2_val_compat f"
  unfolding map2_val_compat_def using assms by blast

lemma map2_val_compatD1:
  assumes "map2_val_compat f" and "oalist_inv_raw zs"
  shows "oalist_inv_raw (f zs)"
  using assms unfolding map2_val_compat_def by blast

lemma map2_val_compatD2:
  assumes "map2_val_compat f" and "oalist_inv_raw zs"
  shows "fst ` set (f zs) \<subseteq> fst ` set zs"
  using assms unfolding map2_val_compat_def by blast

lemma map2_val_compat_Nil:
  assumes "map2_val_compat (f::('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list)"
  shows "f [] = []"
proof -
  from assms oalist_inv_raw_Nil have "fst ` set (f []) \<subseteq> fst ` set ([]::('a \<times> 'b) list)"
    by (rule map2_val_compatD2)
  thus ?thesis by simp
qed

lemma map2_val_compat_id: "map2_val_compat id"
  by (rule map2_val_compatI, auto)

lemma map2_val_compat_map_val_pair: "map2_val_compat (map_val_pair f)"
proof (rule map2_val_compatI, erule oalist_inv_raw_map_val_pair)
  fix zs
  from map_pair_subset image_iff show "fst ` set (map_val_pair f zs) \<subseteq> fst ` set zs" by fastforce
qed

lemma fst_map2_val_pair_subset:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
  assumes "map2_val_compat g" and "map2_val_compat h"
  shows "fst ` set (map2_val_pair f g h xs ys) \<subseteq> fst ` set xs \<union> fst ` set ys"
  using assms
proof (induct f g h xs ys rule: map2_val_pair.induct)
  case (1 f g h xs)
  show ?case by (simp, rule map2_val_compatD2, fact+)
next
  case (2 f g h v va)
  show ?case by (simp del: set_simps(2), rule map2_val_compatD2, fact+)
next
  case (3 f g h kx vx xs ky vy ys)
  from 3(4) have "oalist_inv_raw xs" by (rule oalist_inv_raw_ConsD1)
  from 3(5) have "oalist_inv_raw ys" by (rule oalist_inv_raw_ConsD1)
  show ?case
  proof (simp split: order.split, intro conjI impI)
    assume "comp kx ky = Lt"
    hence "fst ` set (map2_val_pair f g h xs ((ky, vy) # ys)) \<subseteq> fst ` set xs \<union> fst ` set ((ky, vy) # ys)"
      using refl \<open>oalist_inv_raw xs\<close> 3(5, 6, 7) by (rule 3(2))
    thus "fst ` set (let v = f kx vx 0; aux = map2_val_pair f g h xs ((ky, vy) # ys)
                       in if v = 0 then aux else (kx, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  next
    assume "comp kx ky = Eq"
    hence "fst ` set (map2_val_pair f g h xs ys) \<subseteq> fst ` set xs \<union> fst ` set ys"
      using refl \<open>oalist_inv_raw xs\<close> \<open>oalist_inv_raw ys\<close> 3(6, 7) by (rule 3(1))
    thus "fst ` set (let v = f kx vx vy; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (kx, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  next
    assume "comp kx ky = Gt"
    hence "fst ` set (map2_val_pair f g h ((kx, vx) # xs) ys) \<subseteq> fst ` set ((kx, vx) # xs) \<union> fst ` set ys"
      using refl 3(4) \<open>oalist_inv_raw ys\<close> 3(6, 7) by (rule 3(3))
    thus "fst ` set (let v = f ky 0 vy; aux = map2_val_pair f g h ((kx, vx) # xs) ys
                        in if v = 0 then aux else (ky, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  qed
qed

lemma oalist_inv_raw_map2_val_pair:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
  assumes "map2_val_compat g" and "map2_val_compat h"
  shows "oalist_inv_raw (map2_val_pair f g h xs ys)"
  using assms(1, 2)
proof (induct xs arbitrary: ys rule: oalist_inv_raw_induct)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil, rule map2_val_compatD1, fact assms(3), fact oalist_inv_raw_Nil)
  next
    case (Cons y ys')
    show ?thesis by (simp add: Cons, rule map2_val_compatD1, fact assms(4), simp only: Cons[symmetric], fact Nil)
  qed
next
  case *: (Cons k v xs)
  from *(6) show ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    show ?case by (simp, rule map2_val_compatD1, fact assms(3), fact *(1))
  next
    case (Cons k' v' ys)
    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume "comp k k' = Lt"
      hence 0: "lt k k'" by (simp only: Lt_lt_conv)
      from Cons(1) have 1: "oalist_inv_raw (map2_val_pair f g h xs ((k', v') # ys))" by (rule *(5))
      show "oalist_inv_raw (let v = f k v 0; aux = map2_val_pair f g h xs ((k', v') # ys)
              in if v = 0 then aux else (k, v) # aux)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k v 0 \<noteq> 0"
        with 1 show "oalist_inv_raw ((k, f k v 0) # map2_val_pair f g h xs ((k', v') # ys))"
        proof (rule oalist_inv_raw_ConsI)
          define k0 where "k0 = fst (hd (local.map2_val_pair f g h xs ((k', v') # ys)))"
          assume "map2_val_pair f g h xs ((k', v') # ys) \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h xs ((k', v') # ys))" by (simp add: k0_def)
          also from *(2) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ((k', v') # ys)"
            by (rule fst_map2_val_pair_subset)
          finally have "k0 \<in> fst ` set xs \<or> k0 = k' \<or> k0 \<in> fst ` set ys" by auto
          thus "lt k k0"
          proof (elim disjE)
            assume "k0 = k'"
            with 0 show ?thesis by simp
          next
            assume "k0 \<in> fst ` set ys"
            hence "lt k' k0" by (rule Cons(4))
            with 0 show ?thesis by (rule less_trans)
          qed (rule *(4))
        qed
      qed (rule 1)
    next
      assume "comp k k' = Eq"
      hence "k = k'" by (simp only: eq)
      from Cons(2) have 1: "oalist_inv_raw (map2_val_pair f g h xs ys)" by (rule *(5))
      show "oalist_inv_raw (let v = f k v v'; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (k, v) # aux)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k v v' \<noteq> 0"
        with 1 show "oalist_inv_raw ((k, f k v v') # map2_val_pair f g h xs ys)"
        proof (rule oalist_inv_raw_ConsI)
          define k0 where "k0 = fst (hd (map2_val_pair f g h xs ys))"
          assume "map2_val_pair f g h xs ys \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h xs ys)" by (simp add: k0_def)
          also from *(2) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ys"
            by (rule fst_map2_val_pair_subset)
          finally show "lt k k0"
          proof
            assume "k0 \<in> fst ` set ys"
            hence "lt k' k0" by (rule Cons(4))
            thus ?thesis by (simp only: \<open>k = k'\<close>)
          qed (rule *(4))
        qed
      qed (rule 1)
    next
      assume "comp k k' = Gt"
      hence 0: "lt k' k" by (simp only: Gt_lt_conv)
      show "oalist_inv_raw (let va = f k' 0 v'; aux = map2_val_pair f g h ((k, v) # xs) ys
              in if va = 0 then aux else (k', va) # aux)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k' 0 v' \<noteq> 0"
        with Cons(5) show "oalist_inv_raw ((k', f k' 0 v') # map2_val_pair f g h ((k, v) # xs) ys)"
        proof (rule oalist_inv_raw_ConsI)
          define k0 where "k0 = fst (hd (map2_val_pair f g h ((k, v) # xs) ys))"
          assume "map2_val_pair f g h ((k, v) # xs) ys \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h ((k, v) # xs) ys)" by (simp add: k0_def)
          also from *(1) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ys"
            by (rule fst_map2_val_pair_subset)
          finally have "k0 = k \<or> k0 \<in> fst ` set xs \<or> k0 \<in> fst ` set ys" by auto
          thus "lt k' k0"
          proof (elim disjE)
            assume "k0 = k"
            with 0 show ?thesis by simp
          next
            assume "k0 \<in> fst ` set xs"
            hence "lt k k0" by (rule *(4))
            with 0 show ?thesis by (rule less_trans)
          qed (rule Cons(4))
        qed
      qed (rule Cons(5))
    qed
  qed
qed

lemma lookup_pair_map2_val_pair:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
  assumes "map2_val_compat g" and "map2_val_compat h"
  assumes "\<And>zs. oalist_inv_raw zs \<Longrightarrow> g zs = map_val_pair (\<lambda>k v. f k v 0) zs"
    and "\<And>zs. oalist_inv_raw zs \<Longrightarrow> h zs = map_val_pair (\<lambda>k. f k 0) zs"
    and "\<And>k. f k 0 0 = 0"
  shows "lookup_pair (map2_val_pair f g h xs ys) k0 = f k0 (lookup_pair xs k0) (lookup_pair ys k0)"
  using assms(1, 2)
proof (induct xs arbitrary: ys rule: oalist_inv_raw_induct)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil map2_val_compat_Nil[OF assms(3)] assms(7))
  next
    case (Cons y ys')
    then obtain k v ys' where ys: "ys = (k, v) # ys'" by fastforce
    from Nil have "lookup_pair (h ys) k0 = lookup_pair (map_val_pair (\<lambda>k. f k 0) ys) k0"
      by (simp only: assms(6))
    also have "... = f k0 0 (lookup_pair ys k0)" by (rule lookup_pair_map_val_pair, fact Nil, fact assms(7))
    finally have "lookup_pair (h ((k, v) # ys')) k0 = f k0 0 (lookup_pair ((k, v) # ys') k0)"
      by (simp only: ys)
    thus ?thesis by (simp add: ys)
  qed
next
  case *: (Cons k v xs)
  from *(6) show ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    from *(1) have "lookup_pair (g ((k, v) # xs)) k0 = lookup_pair (map_val_pair (\<lambda>k v. f k v 0) ((k, v) # xs)) k0"
      by (simp only: assms(5))
    also have "... = f k0 (lookup_pair ((k, v) # xs) k0) 0"
      by (rule lookup_pair_map_val_pair, fact *(1), fact assms(7))
    finally show ?case by simp
  next
    case (Cons k' v' ys)
    show ?case
    proof (cases "comp k0 k = Lt \<and> comp k0 k' = Lt")
      case True
      hence 1: "comp k0 k = Lt" and 2: "comp k0 k' = Lt" by simp_all
      hence eq: "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0) = 0"
        by (simp add: assms(7))
      from *(1) Cons(1) assms(3, 4) have inv: "oalist_inv_raw (map2_val_pair f g h ((k, v) # xs) ((k', v') # ys))"
        by (rule oalist_inv_raw_map2_val_pair)
      show ?thesis
      proof (simp only: eq lookup_pair_eq_0[OF inv], rule)
        assume "k0 \<in> fst ` set (local.map2_val_pair f g h ((k, v) # xs) ((k', v') # ys))"
        also from *(1) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ((k', v') # ys)"
          by (rule fst_map2_val_pair_subset)
        finally have "k0 \<in> fst ` set xs \<or> k0 \<in> fst ` set ys" using 1 2 by auto
        thus False
        proof
          assume "k0 \<in> fst ` set xs"
          hence "lt k k0" by (rule *(4))
          with 1 show ?thesis by (simp add: Lt_lt_conv)
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt k' k0" by (rule Cons(4))
          with 2 show ?thesis by (simp add: Lt_lt_conv)
        qed
      qed
    next
      case False
      show ?thesis
      proof (simp split: order.split del: lookup_pair.simps, intro conjI impI)
        assume "comp k k' = Lt"
        with False have "comp k0 k \<noteq> Lt" by (auto simp: Lt_lt_conv)
        show "lookup_pair (let v = f k v 0; aux = map2_val_pair f g h xs ((k', v') # ys)
                            in if v = 0 then aux else (k, v) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "comp k0 k")
          case Lt
          with \<open>comp k0 k \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k" by (simp only: eq)
          with \<open>comp k k' = Lt\<close> have "comp k0 k' = Lt" by simp
          hence eq1: "lookup_pair ((k', v') # ys) k = 0" by (simp add: \<open>k0 = k\<close>)
          have eq2: "lookup_pair ((k, v) # xs) k = v" by simp
          show ?thesis
          proof (simp add: Let_def eq1 eq2 \<open>k0 = k\<close> del: lookup_pair.simps, intro conjI impI)
            from *(2) Cons(1) assms(3, 4) have inv: "oalist_inv_raw (map2_val_pair f g h xs ((k', v') # ys))"
              by (rule oalist_inv_raw_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h xs ((k', v') # ys)) k = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k \<in> fst ` set (local.map2_val_pair f g h xs ((k', v') # ys))"
              also from *(2) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ((k', v') # ys)"
                by (rule fst_map2_val_pair_subset)
              finally have "k \<in> fst ` set xs \<or> k \<in> fst ` set ys" using \<open>comp k k' = Lt\<close>
                by auto
              thus False
              proof
                assume "k \<in> fst ` set xs"
                hence "lt k k" by (rule *(4))
                thus ?thesis by simp
              next
                assume "k \<in> fst ` set ys"
                hence "lt k' k" by (rule Cons(4))
                with \<open>comp k k' = Lt\<close> show ?thesis by (simp add: Lt_lt_conv)
              qed
            qed
          qed simp
        next
          case Gt
          hence eq1: "lookup_pair ((k, v) # xs) k0 = lookup_pair xs k0"
            and eq2: "lookup_pair ((k, f k v 0) # map2_val_pair f g h xs ((k', v') # ys)) k0 =
                  lookup_pair (map2_val_pair f g h xs ((k', v') # ys)) k0" by simp_all
          show ?thesis
            by (simp add: Let_def eq1 eq2 del: lookup_pair.simps, rule *(5), fact Cons(1))
        qed
      next
        assume "comp k k' = Eq"
        hence "k = k'" by (simp only: eq)
        with False have "comp k0 k' \<noteq> Lt" by (auto simp: Lt_lt_conv)
        show "lookup_pair (let v = f k v v'; aux = map2_val_pair f g h xs ys in
                            if v = 0 then aux else (k, v) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "comp k0 k'")
          case Lt
          with \<open>comp k0 k' \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k'" by (simp only: eq)
          show ?thesis
          proof (simp add: Let_def \<open>k = k'\<close> \<open>k0 = k'\<close>, intro impI)
            from *(2) Cons(2) assms(3, 4) have inv: "oalist_inv_raw (map2_val_pair f g h xs ys)"
              by (rule oalist_inv_raw_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h xs ys) k' = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k' \<in> fst ` set (map2_val_pair f g h xs ys)"
              also from *(2) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ys"
                by (rule fst_map2_val_pair_subset)
              finally show False
              proof
                assume "k' \<in> fst ` set ys"
                hence "lt k' k'" by (rule Cons(4))
                thus ?thesis by simp
              next
                assume "k' \<in> fst ` set xs"
                hence "lt k k'" by (rule *(4))
                thus ?thesis by (simp add: \<open>k = k'\<close>)
              qed
            qed
          qed
        next
          case Gt
          hence eq1: "lookup_pair ((k, v) # xs) k0 = lookup_pair xs k0"
            and eq2: "lookup_pair ((k', v') # ys) k0 = lookup_pair ys k0"
            and eq3: "lookup_pair ((k, f k v v') # map2_val_pair f g h xs ys) k0 =
                  lookup_pair (map2_val_pair f g h xs ys) k0" by (simp_all add: \<open>k = k'\<close>)
          show ?thesis by (simp add: Let_def eq1 eq2 eq3 del: lookup_pair.simps, rule *(5), fact Cons(2))
        qed
      next
        assume "comp k k' = Gt"
        hence "comp k' k = Lt" by (simp only: Gt_lt_conv Lt_lt_conv)
        with False have "comp k0 k' \<noteq> Lt" by (auto simp: Lt_lt_conv)
        show "lookup_pair (let va = f k' 0 v'; aux = map2_val_pair f g h ((k, v) # xs) ys
                            in if va = 0 then aux else (k', va) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "comp k0 k'")
          case Lt
          with \<open>comp k0 k' \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k'" by (simp only: eq)
          with \<open>comp k' k = Lt\<close> have "comp k0 k = Lt" by simp
          hence eq1: "lookup_pair ((k, v) # xs) k' = 0" by (simp add: \<open>k0 = k'\<close>)
          have eq2: "lookup_pair ((k', v') # ys) k' = v'" by simp
          show ?thesis
          proof (simp add: Let_def eq1 eq2 \<open>k0 = k'\<close> del: lookup_pair.simps, intro conjI impI)
            from *(1) Cons(2) assms(3, 4) have inv: "oalist_inv_raw (map2_val_pair f g h ((k, v) # xs) ys)"
              by (rule oalist_inv_raw_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h ((k, v) # xs) ys) k' = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k' \<in> fst ` set (map2_val_pair f g h ((k, v) # xs) ys)"
              also from *(1) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ys"
                by (rule fst_map2_val_pair_subset)
              finally have "k' \<in> fst ` set xs \<or> k' \<in> fst ` set ys" using \<open>comp k' k = Lt\<close>
                by auto
              thus False
              proof
                assume "k' \<in> fst ` set ys"
                hence "lt k' k'" by (rule Cons(4))
                thus ?thesis by simp
              next
                assume "k' \<in> fst ` set xs"
                hence "lt k k'" by (rule *(4))
                with \<open>comp k' k = Lt\<close> show ?thesis by (simp add: Lt_lt_conv)
              qed
            qed
          qed simp
        next
          case Gt
          hence eq1: "lookup_pair ((k', v') # ys) k0 = lookup_pair ys k0"
            and eq2: "lookup_pair ((k', f k' 0 v') # map2_val_pair f g h ((k, v) # xs) ys) k0 =
                  lookup_pair (map2_val_pair f g h ((k, v) # xs) ys) k0" by simp_all
          show ?thesis by (simp add: Let_def eq1 eq2 del: lookup_pair.simps, rule Cons(5))
        qed
      qed
    qed
  qed
qed

lemma map2_val_pair_singleton_eq_update_by_fun_pair:
  assumes "oalist_inv_raw xs"
  assumes "\<And>k x. f k x 0 = x" and "\<And>zs. oalist_inv_raw zs \<Longrightarrow> g zs = zs"
    and "h [(k, v)] = map_val_pair (\<lambda>k. f k 0) [(k, v)]"
  shows "map2_val_pair f g h xs [(k, v)] = update_by_fun_pair k (\<lambda>x. f k x v) xs"
  using assms(1)
proof (induct xs rule: oalist_inv_raw_induct)
  case Nil
  show ?case by (simp add: Let_def assms(4))
next
  case (Cons k' v' xs)
  show ?case
  proof (cases "comp k' k")
    case Lt
    hence gr: "comp k k' = Gt" by (simp only: Gt_lt_conv Lt_lt_conv)
    show ?thesis by (simp add: Lt gr Let_def assms(2) Cons(3, 5))
  next
    case Eq
    hence eq1: "comp k k' = Eq" and eq2: "k = k'" by (simp_all only: eq)
    show ?thesis by (simp add: Eq eq1 eq2 Let_def assms(3)[OF Cons(2)])
  next
    case Gt
    hence less: "comp k k' = Lt" by (simp only: Gt_lt_conv Lt_lt_conv)
    show ?thesis by (simp add: Gt less Let_def assms(3)[OF Cons(1)])
  qed
qed

subsubsection \<open>@{const lex_ord_pair}\<close>

lemma lex_ord_pair_EqI:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
    and "\<And>k. k \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
  shows "lex_ord_pair f xs ys = Some Eq"
  using assms
proof (induct xs arbitrary: ys rule: oalist_inv_raw_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v ys)
    show ?case
    proof (simp add: Let_def, intro conjI impI, rule Cons(5))
      fix k0
      assume "k0 \<in> fst ` set [] \<union> fst ` set ys"
      hence "k0 \<in> fst ` set ys" by simp
      hence "lt k k0" by (rule Cons(4))
      hence "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = f k0 (lookup_pair [] k0) (lookup_pair ((k, v) # ys) k0)"
        by (auto simp add: lookup_pair_Cons[OF Cons(1)] simp del: lookup_pair.simps)
      also have "... = Some Eq" by (rule Cons(6), simp add: \<open>k0 \<in> fst ` set ys\<close>)
      finally show "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = Some Eq" .
    next
      have "f k 0 v = f k (lookup_pair [] k) (lookup_pair ((k, v) # ys) k)" by simp
      also have "... = Some Eq" by (rule Cons(6), simp)
      finally show "f k 0 v = Some Eq" .
    qed
  qed
next
  case *: (Cons k v xs)
  from *(6, 7) show ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    show ?case
    proof (simp add: Let_def, intro conjI impI, rule *(5), rule oalist_inv_raw_Nil)
      fix k0
      assume "k0 \<in> fst ` set xs \<union> fst ` set []"
      hence "k0 \<in> fst ` set xs" by simp
      hence "lt k k0" by (rule *(4))
      hence "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair [] k0)"
        by (auto simp add: lookup_pair_Cons[OF *(1)] simp del: lookup_pair.simps)
      also have "... = Some Eq" by (rule Nil, simp add: \<open>k0 \<in> fst ` set xs\<close>)
      finally show "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = Some Eq" .
    next
      have "f k v 0 = f k (lookup_pair ((k, v) # xs) k) (lookup_pair [] k)" by simp
      also have "... = Some Eq" by (rule Nil, simp)
      finally show "f k v 0 = Some Eq" .
    qed
  next
    case (Cons k' v' ys)
    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume "comp k k' = Lt"
      show "(let aux = f k v 0 in if aux = Some Eq then lex_ord_pair f xs ((k', v') # ys) else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule *(5), rule Cons(1))
        fix k0
        assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ((k', v') # ys)"
        hence "k0 \<in> fst ` set xs \<or> k0 = k' \<or> k0 \<in> fst ` set ys" by auto
        hence "k0 \<noteq> k"
        proof (elim disjE)
          assume "k0 \<in> fst ` set xs"
          hence "lt k k0" by (rule *(4))
          thus ?thesis by simp
        next
          assume "k0 = k'"
          with \<open>comp k k' = Lt\<close> show ?thesis by auto
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt k' k0" by (rule Cons(4))
          with \<open>comp k k' = Lt\<close> show ?thesis by (simp add: Lt_lt_conv)
        qed
        hence "f k0 (lookup_pair xs k0) (lookup_pair ((k', v') # ys) k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (auto simp add: lookup_pair_Cons[OF *(1)] simp del: lookup_pair.simps)
        also have "... = Some Eq" by (rule Cons(6), rule rev_subsetD, fact k0_in, auto)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair ((k', v') # ys) k0) = Some Eq" .
      next
        have "f k v 0 = f k (lookup_pair ((k, v) # xs) k) (lookup_pair ((k', v') # ys) k)"
          by (simp add: \<open>comp k k' = Lt\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k v 0 = Some Eq" .
      qed
    next
      assume "comp k k' = Eq"
      hence "k = k'" by (simp only: eq)
      show "(let aux = f k v v' in if aux = Some Eq then lex_ord_pair f xs ys else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule *(5), rule Cons(2))
        fix k0
        assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
        hence "k0 \<noteq> k'"
        proof
          assume "k0 \<in> fst ` set xs"
          hence "lt k k0" by (rule *(4))
          thus ?thesis by (simp add: \<open>k = k'\<close>)
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt k' k0" by (rule Cons(4))
          thus ?thesis by simp
        qed
        hence "f k0 (lookup_pair xs k0) (lookup_pair ys k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (simp add: lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
              auto simp: \<open>k = k'\<close>)
        also have "... = Some Eq" by (rule Cons(6), rule rev_subsetD, fact k0_in, auto)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair ys k0) = Some Eq" .
      next
        have "f k v v' = f k (lookup_pair ((k, v) # xs) k) (lookup_pair ((k', v') # ys) k)"
          by (simp add: \<open>k = k'\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k v v' = Some Eq" .
      qed
    next
      assume "comp k k' = Gt"
      hence "comp k' k = Lt" by (simp only: Gt_lt_conv Lt_lt_conv)
      show "(let aux = f k' 0 v' in if aux = Some Eq then lex_ord_pair f ((k, v) # xs) ys else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule Cons(5))
        fix k0
        assume k0_in: "k0 \<in> fst ` set ((k, v) # xs) \<union> fst ` set ys"
        hence "k0 \<in> fst ` set xs \<or> k0 = k \<or> k0 \<in> fst ` set ys" by auto
        hence "k0 \<noteq> k'"
        proof (elim disjE)
          assume "k0 \<in> fst ` set xs"
          hence "lt k k0" by (rule *(4))
          with \<open>comp k' k = Lt\<close> show ?thesis by (simp add: Lt_lt_conv)
        next
          assume "k0 = k"
          with \<open>comp k' k = Lt\<close> show ?thesis by auto
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt k' k0" by (rule Cons(4))
          thus ?thesis by simp
        qed
        hence "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ys k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (auto simp add: lookup_pair_Cons[OF Cons(1)] simp del: lookup_pair.simps)
        also have "... = Some Eq" by (rule Cons(6), rule rev_subsetD, fact k0_in, auto)
        finally show "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ys k0) = Some Eq" .
      next
        have "f k' 0 v' = f k' (lookup_pair ((k, v) # xs) k') (lookup_pair ((k', v') # ys) k')"
          by (simp add: \<open>comp k' k = Lt\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k' 0 v' = Some Eq" .
      qed
    qed
  qed
qed

lemma lex_ord_pair_valI:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys" and "aux \<noteq> Some Eq"
  assumes "k \<in> fst ` set xs \<union> fst ` set ys" and "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
    and "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt k' k \<Longrightarrow>
              f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
  shows "lex_ord_pair f xs ys = aux"
  using assms(1, 2, 4, 5, 6)
proof (induct xs arbitrary: ys rule: oalist_inv_raw_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    from Nil(1) show ?case by simp
  next
    case (Cons k' v' ys)
    from Cons(6) have "k = k' \<or> k \<in> fst ` set ys" by simp
    thus ?case
    proof
      assume "k = k'"
      with Cons(7) have "f k' 0 v' = aux" by simp
      thus ?thesis by (simp add: Let_def \<open>k = k'\<close> assms(3))
    next
      assume "k \<in> fst `set ys"
      hence "lt k' k" by (rule Cons(4))
      hence "comp k k' = Gt" by (simp add: Gt_lt_conv)
      hence eq1: "lookup_pair ((k', v') # ys) k = lookup_pair ys k" by simp
      have "f k' (lookup_pair [] k') (lookup_pair ((k', v') # ys) k') = Some Eq"
        by (rule Cons(8), simp, fact)
      hence eq2: "f k' 0 v' = Some Eq" by simp
      show ?thesis
      proof (simp add: Let_def eq2, rule Cons(5))
        from \<open>k \<in> fst `set ys\<close> show "k \<in> fst ` set [] \<union> fst ` set ys" by simp
      next
        show "aux = f k (lookup_pair [] k) (lookup_pair ys k)" by (simp only: Cons(7) eq1)
      next
        fix k0
        assume "lt k0 k"
        assume "k0 \<in> fst ` set [] \<union> fst ` set ys"
        hence k0_in: "k0 \<in> fst ` set ys" by simp
        hence "lt k' k0" by (rule Cons(4))
        hence "comp k0 k' = Gt" by (simp add: Gt_lt_conv)
        hence "f k0 (lookup_pair [] k0) (lookup_pair ys k0) =
                f k0 (lookup_pair [] k0) (lookup_pair ((k', v') # ys) k0)" by simp
        also have "... = Some Eq" by (rule Cons(8), simp add: k0_in, fact)
        finally show "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = Some Eq" .
      qed
    qed
  qed
next
  case *: (Cons k' v' xs)
  from *(6, 7, 8, 9) show ?case
  proof (induct ys rule: oalist_inv_raw_induct)
    case Nil
    from Nil(1) have "k = k' \<or> k \<in> fst ` set xs" by simp
    thus ?case
    proof
      assume "k = k'"
      with Nil(2) have "f k' v' 0 = aux" by simp
      thus ?thesis by (simp add: Let_def \<open>k = k'\<close> assms(3))
    next
      assume "k \<in> fst ` set xs"
      hence "lt k' k" by (rule *(4))
      hence "comp k k' = Gt" by (simp add: Gt_lt_conv)
      hence eq1: "lookup_pair ((k', v') # xs) k = lookup_pair xs k" by simp
      have "f k' (lookup_pair ((k', v') # xs) k') (lookup_pair [] k') = Some Eq"
        by (rule Nil(3), simp, fact)
      hence eq2: "f k' v' 0 = Some Eq" by simp
      show ?thesis
      proof (simp add: Let_def eq2, rule *(5), fact oalist_inv_raw_Nil)
        from \<open>k \<in> fst `set xs\<close> show "k \<in> fst ` set xs \<union> fst ` set []" by simp
      next
        show "aux = f k (lookup_pair xs k) (lookup_pair [] k)" by (simp only: Nil(2) eq1)
      next
        fix k0
        assume "lt k0 k"
        assume "k0 \<in> fst ` set xs \<union> fst ` set []"
        hence k0_in: "k0 \<in> fst ` set xs" by simp
        hence "lt k' k0" by (rule *(4))
        hence "comp k0 k' = Gt" by (simp add: Gt_lt_conv)
        hence "f k0 (lookup_pair xs k0) (lookup_pair [] k0) =
                f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair [] k0)" by simp
        also have "... = Some Eq" by (rule Nil(3), simp add: k0_in, fact)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = Some Eq" .
      qed
    qed
  next
    case (Cons k'' v'' ys)

    have 0: thesis if 1: "lt k k'" and 2: "lt k k''" for thesis
    proof -
      from 1 have "k \<noteq> k'" by simp
      moreover from 2 have "k \<noteq> k''" by simp
      ultimately have "k \<in> fst ` set xs \<or> k \<in> fst ` set ys" using Cons(6) by simp
      thus ?thesis
      proof
        assume "k \<in> fst ` set xs"
        hence "lt k' k" by (rule *(4))
        with 1 show ?thesis by simp
      next
        assume "k \<in> fst ` set ys"
        hence "lt k'' k" by (rule Cons(4))
        with 2 show ?thesis by simp
      qed
    qed

    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume Lt: "comp k' k'' = Lt"
      show "(let aux = f k' v' 0 in if aux = Some Eq then lex_ord_pair f xs ((k'', v'') # ys) else aux) = aux"
      proof (simp add: Let_def split: order.split, intro conjI impI)
        assume "f k' v' 0 = Some Eq"
        have "k \<noteq> k'"
        proof
          assume "k = k'"
          have "aux = f k v' 0" by (simp add: Cons(7) \<open>k = k'\<close> Lt)
          with \<open>f k' v' 0 = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k'\<close>)
        qed
        from Cons(1) show "lex_ord_pair f xs ((k'', v'') # ys) = aux"
        proof (rule *(5))
          from Cons(6) \<open>k \<noteq> k'\<close> show "k \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)" by simp
        next
          show "aux = f k (lookup_pair xs k) (lookup_pair ((k'', v'') # ys) k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF *(1)] \<open>k \<noteq> k'\<close>[symmetric] del: lookup_pair.simps)
        next
          fix k0
          assume "lt k0 k"
          assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k' \<noteq> k0"
          proof
            assume "k' = k0"
            with k0_in have "k' \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)" by simp
            with Lt have "k' \<in> fst ` set xs \<or> k' \<in> fst ` set ys" by auto
            thus False
            proof
              assume "k' \<in> fst ` set xs"
              hence "lt k' k'" by (rule *(4))
              thus ?thesis by simp
            next
              assume "k' \<in> fst ` set ys"
              hence "lt k'' k'" by (rule Cons(4))
              with Lt show ?thesis by (simp add: Lt_lt_conv)
            qed
          qed
          hence "f k0 (lookup_pair xs k0) (lookup_pair ((k'', v'') # ys) k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF *(1)] del: lookup_pair.simps)
          also from k0_in' \<open>lt k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair xs k0) (lookup_pair ((k'', v'') # ys) k0) = Some Eq" .
        qed
      next
        assume "f k' v' 0 \<noteq> Some Eq"
        have "\<not> lt k' k"
        proof
          have "k' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt k' k"
          ultimately have "f k' (lookup_pair ((k', v') # xs) k') (lookup_pair ((k'', v'') # ys) k') = Some Eq"
            by (rule Cons(8))
          hence "f k' v' 0 = Some Eq" by (simp add: Lt)
          with \<open>f k' v' 0 \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt k k'"
        proof
          assume "lt k k'"
          moreover from this Lt have "lt k k''" by (simp add: Lt_lt_conv)
          ultimately show False by (rule 0)
        qed
        ultimately have "k = k'" by simp
        show "f k' v' 0 = aux" by (simp add: Cons(7) \<open>k = k'\<close> Lt)
      qed
    next
      assume "comp k' k'' = Eq"
      hence "k' = k''" by (simp only: eq)
      show "(let aux = f k' v' v'' in if aux = Some Eq then lex_ord_pair f xs ys else aux) = aux"
      proof (simp add: Let_def \<open>k' = k''\<close> split: order.split, intro conjI impI)
        assume "f k'' v' v'' = Some Eq"
        have "k \<noteq> k''"
        proof
          assume "k = k''"
          have "aux = f k v' v''" by (simp add: Cons(7) \<open>k = k''\<close> \<open>k' = k''\<close>)
          with \<open>f k'' v' v'' = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k''\<close>)
        qed
        from Cons(2) show "lex_ord_pair f xs ys = aux"
        proof (rule *(5))
          from Cons(6) \<open>k \<noteq> k''\<close> show "k \<in> fst ` set xs \<union> fst ` set ys" by (simp add: \<open>k' = k''\<close>)
        next
          show "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
                simp add: \<open>k' = k''\<close> \<open>k \<noteq> k''\<close>[symmetric])
        next
          fix k0
          assume "lt k0 k"
          assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k'' \<noteq> k0"
          proof
            assume "k'' = k0"
            with k0_in have "k'' \<in> fst ` set xs \<union> fst ` set ys" by simp
            thus False
            proof
              assume "k'' \<in> fst ` set xs"
              hence "lt k' k''" by (rule *(4))
              thus ?thesis by (simp add: \<open>k' = k''\<close>)
            next
              assume "k'' \<in> fst ` set ys"
              hence "lt k'' k''" by (rule Cons(4))
              thus ?thesis by simp
            qed
          qed
          hence "f k0 (lookup_pair xs k0) (lookup_pair ys k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
                simp add: \<open>k' = k''\<close>)
          also from k0_in' \<open>lt k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair xs k0) (lookup_pair ys k0) = Some Eq" .
        qed
      next
        assume "f k'' v' v'' \<noteq> Some Eq"
        have "\<not> lt k'' k"
        proof
          have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt k'' k"
          ultimately have "f k'' (lookup_pair ((k', v') # xs) k'') (lookup_pair ((k'', v'') # ys) k'') = Some Eq"
            by (rule Cons(8))
          hence "f k'' v' v'' = Some Eq" by (simp add: \<open>k' = k''\<close>)
          with \<open>f k'' v' v'' \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt k k''"
        proof
          assume "lt k k''"
          hence "lt k k'" by (simp only: \<open>k' = k''\<close>)
          thus False using \<open>lt k k''\<close> by (rule 0)
        qed
        ultimately have "k = k''" by simp
        show "f k'' v' v'' = aux" by (simp add: Cons(7) \<open>k = k''\<close> \<open>k' = k''\<close>)
      qed
    next
      assume Gt: "comp k' k'' = Gt"
      hence Lt: "comp k'' k' = Lt" by (simp only: Gt_lt_conv Lt_lt_conv)
      show "(let aux = f k'' 0 v'' in if aux = Some Eq then lex_ord_pair f ((k', v') # xs) ys else aux) = aux"
      proof (simp add: Let_def split: order.split, intro conjI impI)
        assume "f k'' 0 v'' = Some Eq"
        have "k \<noteq> k''"
        proof
          assume "k = k''"
          have "aux = f k 0 v''" by (simp add: Cons(7) \<open>k = k''\<close> Lt)
          with \<open>f k'' 0 v'' = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k''\<close>)
        qed
        show "lex_ord_pair f ((k', v') # xs) ys = aux"
        proof (rule Cons(5))
          from Cons(6) \<open>k \<noteq> k''\<close> show "k \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys" by simp
        next
          show "aux = f k (lookup_pair ((k', v') # xs) k) (lookup_pair ys k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF Cons(1)] \<open>k \<noteq> k''\<close>[symmetric] del: lookup_pair.simps)
        next
          fix k0
          assume "lt k0 k"
          assume k0_in: "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k'' \<noteq> k0"
          proof
            assume "k'' = k0"
            with k0_in have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys" by simp
            with Lt have "k'' \<in> fst ` set xs \<or> k'' \<in> fst ` set ys" by auto
            thus False
            proof
              assume "k'' \<in> fst ` set xs"
              hence "lt k' k''" by (rule *(4))
              with Lt show ?thesis by (simp add: Lt_lt_conv)
            next
              assume "k'' \<in> fst ` set ys"
              hence "lt k'' k''" by (rule Cons(4))
              thus ?thesis by simp
            qed
          qed
          hence "f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ys k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps)
          also from k0_in' \<open>lt k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ys k0) = Some Eq" .
        qed
      next
        assume "f k'' 0 v'' \<noteq> Some Eq"
        have "\<not> lt k'' k"
        proof
          have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt k'' k"
          ultimately have "f k'' (lookup_pair ((k', v') # xs) k'') (lookup_pair ((k'', v'') # ys) k'') = Some Eq"
            by (rule Cons(8))
          hence "f k'' 0 v'' = Some Eq" by (simp add: Lt)
          with \<open>f k'' 0 v'' \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt k k''"
        proof
          assume "lt k k''"
          with Lt have "lt k k'" by (simp add: Lt_lt_conv)
          thus False using \<open>lt k k''\<close> by (rule 0)
        qed
        ultimately have "k = k''" by simp
        show "f k'' 0 v'' = aux" by (simp add: Cons(7) \<open>k = k''\<close> Lt)
      qed
    qed
  qed
qed

lemma lex_ord_pair_EqD:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys" and "lex_ord_pair f xs ys = Some Eq"
    and "k \<in> fst ` set xs \<union> fst ` set ys"
  shows "f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
proof (rule ccontr)
  let ?A = "(fst ` set xs \<union> fst ` set ys) \<inter> {k. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq}"
  define k0 where "k0 = Min ?A"
  have "finite ?A" by auto
  assume "f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq"
  with assms(4) have "k \<in> ?A" by simp
  hence "?A \<noteq> {}" by blast
  with \<open>finite ?A\<close> have "k0 \<in> ?A" unfolding k0_def by (rule Min_in)
  hence k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
    and neq: "f k0 (lookup_pair xs k0) (lookup_pair ys k0) \<noteq> Some Eq" by simp_all
  have "le k0 k'" if "k' \<in> ?A" for k' unfolding k0_def using \<open>finite ?A\<close> that
    by (rule Min_le)
  hence "f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
    if "k' \<in> fst ` set xs \<union> fst ` set ys" and "lt k' k0" for k' using that by fastforce
  with assms(1, 2) neq k0_in refl have "lex_ord_pair f xs ys = f k0 (lookup_pair xs k0) (lookup_pair ys k0)"
    by (rule lex_ord_pair_valI)
  with assms(3) neq show False by simp
qed

lemma lex_ord_pair_valE:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys" and "lex_ord_pair f xs ys = aux"
    and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set xs \<union> fst ` set ys" and "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
    and "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt k' k \<Longrightarrow>
            f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
proof -
  let ?A = "(fst ` set xs \<union> fst ` set ys) \<inter> {k. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq}"
  define k where "k = Min ?A"
  have "finite ?A" by auto
  have "\<exists>k \<in> fst ` set xs \<union> fst ` set ys. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq" (is ?prop)
  proof (rule ccontr)
    assume "\<not> ?prop"
    hence "f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
      if "k \<in> fst ` set xs \<union> fst ` set ys" for k using that by auto
    with assms(1, 2) have "lex_ord_pair f xs ys = Some Eq" by (rule lex_ord_pair_EqI)
    with assms(3, 4) show False by simp
  qed
  then obtain k0 where "k0 \<in> fst ` set xs \<union> fst ` set ys"
    and "f k0 (lookup_pair xs k0) (lookup_pair ys k0) \<noteq> Some Eq" ..
  hence "k0 \<in> ?A" by simp
  hence "?A \<noteq> {}" by blast
  with \<open>finite ?A\<close> have "k \<in> ?A" unfolding k_def by (rule Min_in)
  hence k_in: "k \<in> fst ` set xs \<union> fst ` set ys"
    and neq: "f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq" by simp_all
  have "le k k'" if "k' \<in> ?A" for k' unfolding k_def using \<open>finite ?A\<close> that
    by (rule Min_le)
  hence *: "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt k' k \<Longrightarrow>
            f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq" by fastforce
  with assms(1, 2) neq k_in refl have "lex_ord_pair f xs ys = f k (lookup_pair xs k) (lookup_pair ys k)"
    by (rule lex_ord_pair_valI)
  hence "aux = f k (lookup_pair xs k) (lookup_pair ys k)" by (simp only: assms(3))
  with k_in show ?thesis using * ..
qed

subsubsection \<open>@{const prod_ord_pair}\<close>

lemma prod_ord_pair_eq_lex_ord_pair:
  "prod_ord_pair P xs ys = (lex_ord_pair (\<lambda>k x y. if P k x y then Some Eq else None) xs ys = Some Eq)"
proof (induct P xs ys rule: prod_ord_pair.induct)
  case (1 P)
  show ?case by simp
next
  case (2 P ky vy ys)
  thus ?case by simp
next
  case (3 P kx vx xs)
  thus ?case by simp
next
  case (4 P kx vx xs ky vy ys)
  show ?case
  proof (cases "comp kx ky")
    case Lt
    thus ?thesis by (simp add: 4(2)[OF Lt])
  next
    case Eq
    thus ?thesis by (simp add: 4(1)[OF Eq])
  next
    case Gt
    thus ?thesis by (simp add: 4(3)[OF Gt])
  qed
qed

lemma prod_ord_pairI:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
    and "\<And>k. k \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> P k (lookup_pair xs k) (lookup_pair ys k)"
  shows "prod_ord_pair P xs ys"
  unfolding prod_ord_pair_eq_lex_ord_pair by (rule lex_ord_pair_EqI, fact, fact, simp add: assms(3))

lemma prod_ord_pairD:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys" and "prod_ord_pair P xs ys"
    and "k \<in> fst ` set xs \<union> fst ` set ys"
  shows "P k (lookup_pair xs k) (lookup_pair ys k)"
proof -
  from assms have "(if P k (lookup_pair xs k) (lookup_pair ys k) then Some Eq else None) = Some Eq"
    unfolding prod_ord_pair_eq_lex_ord_pair by (rule lex_ord_pair_EqD)
  thus ?thesis by (simp split: if_splits)
qed

corollary prod_ord_pair_alt:
  assumes "oalist_inv_raw xs" and "oalist_inv_raw ys"
  shows "(prod_ord_pair P xs ys) \<longleftrightarrow> (\<forall>k\<in>fst ` set xs \<union> fst ` set ys. P k (lookup_pair xs k) (lookup_pair ys k))"
  using prod_ord_pairI[OF assms] prod_ord_pairD[OF assms] by meson

subsubsection \<open>@{const sort_oalist}\<close>

lemma oalist_inv_raw_foldr_update_by_pair:
  assumes "oalist_inv_raw ys"
  shows "oalist_inv_raw (foldr update_by_pair xs ys)"
proof (induct xs)
  case Nil
  from assms show ?case by simp
next
  case (Cons x xs)
  hence "oalist_inv_raw (update_by_pair x (foldr update_by_pair xs ys))"
    by (rule oalist_inv_raw_update_by_pair)
  thus ?case by simp
qed

corollary oalist_inv_raw_sort_oalist: "oalist_inv_raw (sort_oalist xs)"
proof -
  from oalist_inv_raw_Nil have "oalist_inv_raw (foldr local.update_by_pair xs [])"
    by (rule oalist_inv_raw_foldr_update_by_pair)
  thus "oalist_inv_raw (sort_oalist xs)" by (simp only: sort_oalist_def)
qed

lemma sort_oalist_id:
  assumes "oalist_inv_raw xs"
  shows "sort_oalist xs = xs"
proof -
  have "foldr update_by_pair xs ys = xs @ ys" if "oalist_inv_raw (xs @ ys)" for ys using assms that
  proof (induct xs rule: oalist_inv_raw_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs)
    from Cons(6) have *: "oalist_inv_raw ((k, v) # (xs @ ys))" by simp
    hence 1: "oalist_inv_raw (xs @ ys)" by (rule oalist_inv_raw_ConsD1)
    hence 2: "foldr update_by_pair xs ys = xs @ ys" by (rule Cons(5))
    show ?case
    proof (simp add: 2, rule update_by_pair_less)
      from * show "v \<noteq> 0" by (auto simp: oalist_inv_raw_def)
    next
      have "comp k (fst (hd (xs @ ys))) = Lt \<or> xs @ ys = []"
      proof (rule disjCI)
        assume "xs @ ys \<noteq> []"
        then obtain k'' v'' zs where eq0: "xs @ ys = (k'', v'') # zs"
          using list.exhaust prod.exhaust by metis
        from * have "lt k k''" by (simp add: eq0 oalist_inv_raw_def)
        thus "comp k (fst (hd (xs @ ys))) = Lt" by (simp add: eq0 Lt_lt_conv)
      qed
      thus "xs @ ys = [] \<or> comp k (fst (hd (xs @ ys))) = Lt" by auto
    qed
  qed
  with assms show ?thesis by (simp add: sort_oalist_def)
qed

lemma set_sort_oalist:
  assumes "distinct (map fst xs)"
  shows "set (sort_oalist xs) = {kv. kv \<in> set xs \<and> snd kv \<noteq> 0}"
  using assms
proof (induct xs)
  case Nil
  show ?case by (simp add: sort_oalist_def)
next
  case (Cons x xs)
  obtain k v where x: "x = (k, v)" by fastforce
  from Cons(2) have "distinct (map fst xs)" and "k \<notin> fst ` set xs" by (simp_all add: x)
  from this(1) have "set (sort_oalist xs) = {kv \<in> set xs. snd kv \<noteq> 0}" by (rule Cons(1))
  with \<open>k \<notin> fst ` set xs\<close> have eq: "set (sort_oalist xs) - range (Pair k) = {kv \<in> set xs. snd kv \<noteq> 0}"
    by (auto simp: image_iff)
  have "set (sort_oalist (x # xs)) = set (update_by_pair (k, v) (sort_oalist xs))"
    by (simp add: sort_oalist_def x)
  also have "... = {kv \<in> set (x # xs). snd kv \<noteq> 0}"
  proof (cases "v = 0")
    case True
    have "set (update_by_pair (k, v) (sort_oalist xs)) = set (sort_oalist xs) - range (Pair k)"
      unfolding True using oalist_inv_raw_sort_oalist by (rule set_update_by_pair_zero)
    also have "... = {kv \<in> set (x # xs). snd kv \<noteq> 0}" by (auto simp: eq x True)
    finally show ?thesis .
  next
    case False
    with oalist_inv_raw_sort_oalist
    have "set (update_by_pair (k, v) (sort_oalist xs)) = insert (k, v) (set (sort_oalist xs) - range (Pair k))"
      by (rule set_update_by_pair)
    also have "... = {kv \<in> set (x # xs). snd kv \<noteq> 0}" by (auto simp: eq x False)
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma lookup_pair_sort_oalist':
  assumes "distinct (map fst xs)"
  shows "lookup_pair (sort_oalist xs) = lookup_dflt xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by (simp add: sort_oalist_def lookup_dflt_def)
next
  case (Cons x xs)
  obtain k v where x: "x = (k, v)" by fastforce
  from Cons(2) have "distinct (map fst xs)" and "k \<notin> fst ` set xs" by (simp_all add: x)
  from this(1) have eq1: "lookup_pair (sort_oalist xs) = lookup_dflt xs" by (rule Cons(1))
  have eq2: "sort_oalist (x # xs) = update_by_pair (k, v) (sort_oalist xs)" by (simp add: x sort_oalist_def)
  show ?case
  proof
    fix k'
    have "lookup_pair (sort_oalist (x # xs)) k' = (if k = k' then v else lookup_dflt xs k')"
      by (simp add: eq1 eq2 lookup_pair_update_by_pair[OF oalist_inv_raw_sort_oalist])
    also have "... = lookup_dflt (x # xs) k'" by (simp add: x lookup_dflt_def)
    finally show "lookup_pair (sort_oalist (x # xs)) k' = lookup_dflt (x # xs) k'" .
  qed
qed

end

locale comparator2 = comparator comp1 + cmp2: comparator comp2 for comp1 comp2 :: "'a comparator"
begin

lemma set_sort_oalist:
  assumes "cmp2.oalist_inv_raw xs"
  shows "set (sort_oalist xs) = set xs"
proof -
  have rl: "set (foldr update_by_pair xs ys) = set xs \<union> set ys"
    if "oalist_inv_raw ys" and "fst ` set xs \<inter> fst ` set ys = {}" for ys
    using assms that(2)
  proof (induct xs rule: cmp2.oalist_inv_raw_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs)
    from Cons(6) have "k \<notin> fst ` set ys" and "fst ` set xs \<inter> fst ` set ys = {}" by simp_all
    from this(2) have eq1: "set (foldr update_by_pair xs ys) = set xs \<union> set ys" by (rule Cons(5))
    have "\<not> cmp2.lt k k" by auto
    with Cons(4) have "k \<notin> fst ` set xs" by blast
    with \<open>k \<notin> fst ` set ys\<close> have "k \<notin> fst ` (set xs \<union> set ys)" by (simp add: image_Un)
    hence "(set xs \<union> set ys) \<inter> range (Pair k) = {}" by (smt Int_emptyI fstI image_iff)
    hence eq2: "(set xs \<union> set ys) - range (Pair k) = set xs \<union> set ys" by (rule Diff_triv)
    from \<open>oalist_inv_raw ys\<close> have "oalist_inv_raw (foldr update_by_pair xs ys)"
      by (rule oalist_inv_raw_foldr_update_by_pair)
    hence "set (update_by_pair (k, v) (foldr update_by_pair xs ys)) =
            insert (k, v) (set (foldr update_by_pair xs ys) - range (Pair k))"
      using Cons(3) by (rule set_update_by_pair)
    also have "... = insert (k, v) (set xs \<union> set ys)" by (simp only: eq1 eq2)
    finally show ?case by simp
  qed
  have "set (foldr update_by_pair xs []) = set xs \<union> set []"
    by (rule rl, fact oalist_inv_raw_Nil, simp)
  thus ?thesis by (simp add: sort_oalist_def)
qed

lemma lookup_pair_eqI:
  assumes "oalist_inv_raw xs" and "cmp2.oalist_inv_raw ys" and "set xs = set ys"
  shows "lookup_pair xs = cmp2.lookup_pair ys"
proof
  fix k
  show "lookup_pair xs k = cmp2.lookup_pair ys k"
  proof (cases "cmp2.lookup_pair ys k = 0")
    case True
    with assms(2) have "k \<notin> fst ` set ys" by (simp add: cmp2.lookup_pair_eq_0)
    with assms(1) show ?thesis by (simp add: True assms(3)[symmetric] lookup_pair_eq_0)
  next
    case False
    define v where "v = cmp2.lookup_pair ys k"
    from False have "v \<noteq> 0" by (simp add: v_def)
    with assms(2) v_def[symmetric] have "(k, v) \<in> set ys" by (simp add: cmp2.lookup_pair_eq_value)
    with assms(1) \<open>v \<noteq> 0\<close> have "lookup_pair xs k = v"
      by (simp add: assms(3)[symmetric] lookup_pair_eq_value)
    thus ?thesis by (simp only: v_def)
  qed
qed

corollary lookup_pair_sort_oalist:
  assumes "cmp2.oalist_inv_raw xs"
  shows "lookup_pair (sort_oalist xs) = cmp2.lookup_pair xs"
  by (rule lookup_pair_eqI, rule oalist_inv_raw_sort_oalist, fact, rule set_sort_oalist, fact)

end (* comparator2 *)

subsection \<open>Invariant on Pairs\<close>

type_synonym ('a, 'b, 'c) oalist_raw = "('a \<times> 'b) list \<times> 'c"

locale oalist_raw = fixes rep_key_order::"'o \<Rightarrow> 'a key_order"
begin

sublocale comparator "key_compare (rep_key_order x)"
  by (fact comparator_key_compare)

definition oalist_inv :: "('a, 'b::zero, 'o) oalist_raw \<Rightarrow> bool"
  where "oalist_inv xs \<longleftrightarrow> oalist_inv_raw (snd xs) (fst xs)"

lemma oalist_inv_alt: "oalist_inv (xs, ko) \<longleftrightarrow> oalist_inv_raw ko xs"
  by (simp add: oalist_inv_def)

subsection \<open>Operations on Raw Ordered Associative Lists\<close>

fun sort_oalist_aux :: "'o \<Rightarrow> ('a, 'b, 'o) oalist_raw \<Rightarrow> ('a \<times> 'b::zero) list"
  where "sort_oalist_aux ko (xs, ox) = (if ko = ox then xs else sort_oalist ko xs)"

fun lookup_raw :: "('a, 'b, 'o) oalist_raw \<Rightarrow> 'a \<Rightarrow> 'b::zero"
  where "lookup_raw (xs, ko) = lookup_pair ko xs"

definition sorted_domain_raw :: "'o \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw \<Rightarrow> 'a list"
  where "sorted_domain_raw ko xs = map fst (sort_oalist_aux ko xs)"

fun tl_raw :: "('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  where "tl_raw (xs, ko) = (List.tl xs, ko)"

fun min_key_val_raw :: "'o \<Rightarrow> ('a, 'b, 'o) oalist_raw \<Rightarrow> ('a \<times> 'b::zero)"
  where "min_key_val_raw ko (xs, ox) =
      (if ko = ox then List.hd else min_list_param (\<lambda>x y. le ko (fst x) (fst y))) xs"

fun update_by_raw :: "('a \<times> 'b) \<Rightarrow> ('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  where "update_by_raw kv (xs, ko) = (update_by_pair ko kv xs, ko)"

fun update_by_fun_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  where "update_by_fun_raw k f (xs, ko) = (update_by_fun_pair ko k f xs, ko)"

fun update_by_fun_gr_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  where "update_by_fun_gr_raw k f (xs, ko) = (update_by_fun_gr_pair ko k f xs, ko)"

fun (in -) filter_raw :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<times> 'b) \<Rightarrow> ('a list \<times> 'b)"
  where "filter_raw P (xs, ko) = (filter P xs, ko)"

fun (in -) map_raw :: "(('a \<times> 'b) \<Rightarrow> ('a \<times> 'c)) \<Rightarrow> (('a \<times> 'b::zero) list \<times> 'd) \<Rightarrow> ('a \<times> 'c::zero) list \<times> 'd"
  where "map_raw f (xs, ko) = (map_pair f xs, ko)"

abbreviation (in -) "map_val_raw f \<equiv> map_raw (\<lambda>(k, v). (k, f k v))"

fun map2_val_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'd, 'o) oalist_raw) \<Rightarrow>
                      (('a, 'c, 'o) oalist_raw \<Rightarrow> ('a, 'd, 'o) oalist_raw) \<Rightarrow>
                      ('a, 'b::zero, 'o) oalist_raw \<Rightarrow> ('a, 'c::zero, 'o) oalist_raw \<Rightarrow>
                      ('a, 'd::zero, 'o) oalist_raw"
  where "map2_val_raw f g h (xs, ox) ys =
            (map2_val_pair ox f (\<lambda>zs. fst (g (zs, ox))) (\<lambda>zs. fst (h (zs, ox)))
                    xs (sort_oalist_aux ox ys), ox)"

definition lex_ord_raw :: "'o \<Rightarrow> ('a \<Rightarrow> (('b, 'c) comp_opt)) \<Rightarrow>
                      (('a, 'b::zero, 'o) oalist_raw, ('a, 'c::zero, 'o) oalist_raw) comp_opt"
  where "lex_ord_raw ko f xs ys = lex_ord_pair ko f (sort_oalist_aux ko xs) (sort_oalist_aux ko ys)"

fun prod_ord_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw \<Rightarrow>
                      ('a, 'c::zero, 'o) oalist_raw \<Rightarrow> bool"
  where "prod_ord_raw f (xs, ox) ys = prod_ord_pair ox f xs (sort_oalist_aux ox ys)"

fun oalist_eq_raw :: "('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw \<Rightarrow> bool"
  where "oalist_eq_raw (xs, ox) ys = (xs = (sort_oalist_aux ox ys))"

fun sort_oalist_raw :: "('a, 'b, 'o) oalist_raw \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  where "sort_oalist_raw (xs, ko) = (sort_oalist ko xs, ko)"

subsubsection \<open>@{const sort_oalist_aux}\<close>

lemma set_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "set (sort_oalist_aux ko xs) = set (fst xs)"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  interpret ko2: comparator2 "key_compare (rep_key_order ko)" "key_compare (rep_key_order ko')" ..
  from assms show ?thesis by (simp add: xs oalist_inv_alt ko2.set_sort_oalist)
qed

lemma oalist_inv_raw_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "oalist_inv_raw ko (sort_oalist_aux ko xs)"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show ?thesis by (simp add: xs oalist_inv_alt oalist_inv_raw_sort_oalist)
qed

lemma oalist_inv_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "oalist_inv (sort_oalist_aux ko xs, ko)"
  unfolding oalist_inv_alt using assms by (rule oalist_inv_raw_sort_oalist_aux)

lemma lookup_pair_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "lookup_pair ko (sort_oalist_aux ko xs) = lookup_raw xs"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  interpret ko2: comparator2 "key_compare (rep_key_order ko)" "key_compare (rep_key_order ko')" ..
  from assms show ?thesis by (simp add: xs oalist_inv_alt ko2.lookup_pair_sort_oalist)
qed

subsubsection \<open>@{const lookup_raw}\<close>

lemma lookup_raw_eq_value:
  assumes "oalist_inv xs" and "v \<noteq> 0"
  shows "lookup_raw xs k = v \<longleftrightarrow> ((k, v) \<in> set (fst xs))"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp add: xs oalist_inv_def)
  show ?thesis by (simp add: xs, rule lookup_pair_eq_value, fact+)
qed

lemma lookup_raw_eq_valueI:
  assumes "oalist_inv xs" and "(k, v) \<in> set (fst xs)"
  shows "lookup_raw xs k = v"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp add: xs oalist_inv_def)
  from assms(2) have "(k, v) \<in> set xs'" by (simp add: xs)
  show ?thesis by (simp add: xs, rule lookup_pair_eq_valueI, fact+)
qed

lemma lookup_raw_inj:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "lookup_raw (xs, ko) = lookup_raw (ys, ko)"
  shows "xs = ys"
  using assms unfolding lookup_raw.simps oalist_inv_alt by (rule lookup_pair_inj)

subsubsection \<open>@{const sorted_domain_raw}\<close>

lemma set_sorted_domain_raw:
  assumes "oalist_inv xs"
  shows "set (sorted_domain_raw ko xs) = fst ` set (fst xs)"
  using assms by (simp add: sorted_domain_raw_def set_sort_oalist_aux)

corollary in_sorted_domain_raw_iff_lookup_raw:
  assumes "oalist_inv xs"
  shows "k \<in> set (sorted_domain_raw ko xs) \<longleftrightarrow> (lookup_raw xs k \<noteq> 0)"
  unfolding set_sorted_domain_raw[OF assms]
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show "k \<in> fst ` set (fst xs) \<longleftrightarrow> (lookup_raw xs k \<noteq> 0)"
    by (simp add: xs oalist_inv_alt lookup_pair_eq_0)
qed

lemma sorted_sorted_domain_raw:
  assumes "oalist_inv xs"
  shows "sorted_wrt (lt_of_key_order (rep_key_order ko)) (sorted_domain_raw ko xs)"
  unfolding sorted_domain_raw_def oalist_inv_alt lt_of_key_order.rep_eq
  by (rule oalist_inv_rawD2, rule oalist_inv_raw_sort_oalist_aux, fact)

subsubsection \<open>@{const tl_raw}\<close>

lemma oalist_inv_tl_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (tl_raw xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs tl_raw.simps oalist_inv_alt by (rule oalist_inv_raw_tl)
qed

lemma lookup_raw_tl_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (tl_raw xs) k =
          (if (\<forall>k'\<in>fst ` set (fst xs). le (snd xs) k k') then 0 else lookup_raw xs k)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis by (simp add: xs lookup_pair_tl oalist_inv_alt split del: if_split cong: if_cong)
qed

lemma lookup_raw_tl_raw':
  assumes "oalist_inv xs"
  shows "lookup_raw (tl_raw xs) k = (if k = fst (List.hd (fst xs)) then 0 else lookup_raw xs k)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis by (simp add: xs lookup_pair_tl' oalist_inv_alt)
qed

subsubsection \<open>@{const min_key_val_raw}\<close>

lemma min_key_val_raw_alt:
  assumes "oalist_inv xs" and "fst xs \<noteq> []"
  shows "min_key_val_raw ko xs = List.hd (sort_oalist_aux ko xs)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(2) have "xs' \<noteq> []" by (simp add: xs)
  interpret ko2: comparator2 "key_compare (rep_key_order ko)" "key_compare (rep_key_order ox)" ..
  from assms(1) have "oalist_inv_raw ox xs'" by (simp only: xs oalist_inv_alt)
  hence set_sort: "set (sort_oalist ko xs') = set xs'" by (rule ko2.set_sort_oalist)
  also from \<open>xs' \<noteq> []\<close> have "... \<noteq> {}" by simp
  finally have "sort_oalist ko xs' \<noteq> []" by simp
  then obtain k v xs'' where eq: "sort_oalist ko xs' = (k, v) # xs''"
    using prod.exhaust list.exhaust by metis
  hence "(k, v) \<in> set xs'" by (simp add: set_sort[symmetric])
  have *: "le ko k k'" if "k' \<in> fst ` set xs'" for k'
  proof -
    from that have "k' = k \<or> k' \<in> fst ` set xs''" by (simp add: set_sort[symmetric] eq)
    thus ?thesis
    proof
      assume "k' = k"
      thus ?thesis by simp
    next
      have "oalist_inv_raw ko ((k, v) # xs'')" unfolding eq[symmetric] by (fact oalist_inv_raw_sort_oalist)
      moreover assume "k' \<in> fst ` set xs''"
      ultimately have "lt ko k k'" by (rule oalist_inv_raw_ConsD3)
      thus ?thesis by simp
    qed
  qed
  from \<open>xs' \<noteq> []\<close> have "min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs' \<in> set xs'" by (rule min_list_param_in)
  with \<open>oalist_inv_raw ox xs'\<close> have "lookup_pair ox xs' (fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs')) =
    snd (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs')" by (auto intro: lookup_pair_eq_valueI)
  moreover have 1: "fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs') = k"
  proof (rule antisym)
    from order.trans
    have "transp (\<lambda>x y. le ko (fst x) (fst y))" by (rule transpI)
    hence "le ko (fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs')) (fst (k, v))"
      using linear \<open>(k, v) \<in> set xs'\<close> by (rule min_list_param_minimal)
    thus "le ko (fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs')) k" by simp
  next
    show "le ko k (fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs'))" by (rule *, rule imageI, fact)
  qed
  ultimately have "snd (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs') = lookup_pair ox xs' k"
    by simp
  also from \<open>oalist_inv_raw ox xs'\<close> \<open>(k, v) \<in> set xs'\<close> have "... = v" by (rule lookup_pair_eq_valueI)
  finally have "snd (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs') = v" .
  with 1 have "min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs' = (k, v)" by auto
  thus ?thesis by (simp add: xs eq)
qed

lemma min_key_val_raw_in:
  assumes "fst xs \<noteq> []"
  shows "min_key_val_raw ko xs \<in> set (fst xs)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms have "xs' \<noteq> []" by (simp add: xs)
  show ?thesis unfolding xs
  proof (simp, intro conjI impI)
    from \<open>xs' \<noteq> []\<close> show "hd xs' \<in> set xs'" by simp
  next
    from \<open>xs' \<noteq> []\<close> show "min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs' \<in> set xs'"
      by (rule min_list_param_in)
  qed
qed

lemma snd_min_key_val_raw:
  assumes "oalist_inv xs" and "fst xs \<noteq> []"
  shows "snd (min_key_val_raw ko xs) = lookup_raw xs (fst (min_key_val_raw ko xs))"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp only: xs oalist_inv_alt)
  from assms(2) have "min_key_val_raw ko xs \<in> set (fst xs)" by (rule min_key_val_raw_in)
  hence *: "min_key_val_raw ko (xs', ox) \<in> set xs'" by (simp add: xs)
  show ?thesis unfolding xs lookup_raw.simps
    by (rule HOL.sym, rule lookup_pair_eq_valueI, fact, simp add: * del: min_key_val_raw.simps)
qed

lemma min_key_val_raw_minimal:
  assumes "oalist_inv xs" and "z \<in> set (fst xs)"
  shows "le ko (fst (min_key_val_raw ko xs)) (fst z)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms have "oalist_inv (xs', ox)" and "z \<in> set xs'" by (simp_all add: xs)
  show ?thesis unfolding xs
  proof (simp, intro conjI impI)
    from \<open>z \<in> set xs'\<close> have "xs' \<noteq> []" by auto
    then obtain k v ys where xs': "xs' = (k, v) # ys" using prod.exhaust list.exhaust by metis
    from \<open>z \<in> set xs'\<close> have "z = (k, v) \<or> z \<in> set ys" by (simp add: xs')
    thus "le ox (fst (hd xs')) (fst z)"
    proof
      assume "z = (k, v)"
      show ?thesis by (simp add: xs' \<open>z = (k, v)\<close>)
    next
      assume "z \<in> set ys"
      hence "fst z \<in> fst ` set ys" by fastforce
      with \<open>oalist_inv (xs', ox)\<close> have "lt ox k (fst z)"
        unfolding xs' oalist_inv_alt lt_of_key_order.rep_eq by (rule oalist_inv_raw_ConsD3)
      thus ?thesis by (simp add: xs')
    qed
  next
    show "le ko (fst (min_list_param (\<lambda>x y. le ko (fst x) (fst y)) xs')) (fst z)"
    proof (rule min_list_param_minimal[of "\<lambda>x y. le ko (fst x) (fst y)"])
      show "transp (\<lambda>x y. le ko (fst x) (fst y))" by (metis (no_types, lifting) order.trans transpI)
    qed (auto intro: \<open>z \<in> set xs'\<close>)
  qed
qed

subsubsection \<open>@{const filter_raw}\<close>

lemma oalist_inv_filter_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (filter_raw P xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs filter_raw.simps oalist_inv_alt
    by (rule oalist_inv_raw_filter)
qed

lemma lookup_raw_filter_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (filter_raw P xs) k = (let v = lookup_raw xs k in if P (k, v) then v else 0)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs lookup_raw.simps filter_raw.simps oalist_inv_alt
    by (rule lookup_pair_filter)
qed

subsubsection \<open>@{const update_by_raw}\<close>

lemma oalist_inv_update_by_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_raw kv xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs update_by_raw.simps oalist_inv_alt
    by (rule oalist_inv_raw_update_by_pair)
qed

lemma lookup_raw_update_by_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_raw (k1, v) xs) k2 = (if k1 = k2 then v else lookup_raw xs k2)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs lookup_raw.simps update_by_raw.simps oalist_inv_alt
    by (rule lookup_pair_update_by_pair)
qed

subsubsection \<open>@{const update_by_fun_raw} and @{const update_by_fun_gr_raw}\<close>

lemma update_by_fun_raw_eq_update_by_raw:
  assumes "oalist_inv xs"
  shows "update_by_fun_raw k f xs = update_by_raw (k, f (lookup_raw xs k)) xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv_raw ko xs'" by (simp only: xs oalist_inv_alt)
  show ?thesis unfolding xs update_by_fun_raw.simps lookup_raw.simps update_by_raw.simps
    by (rule, rule conjI, rule update_by_fun_pair_eq_update_by_pair, fact, fact refl)
qed

corollary oalist_inv_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_fun_raw k f xs)"
  unfolding update_by_fun_raw_eq_update_by_raw[OF assms] using assms by (rule oalist_inv_update_by_raw)

corollary lookup_raw_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_fun_raw k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_raw xs k2)"
  using assms by (simp add: update_by_fun_raw_eq_update_by_raw lookup_raw_update_by_raw)

lemma update_by_fun_gr_raw_eq_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "update_by_fun_gr_raw k f xs = update_by_fun_raw k f xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv_raw ko xs'" by (simp only: xs oalist_inv_alt)
  show ?thesis unfolding xs update_by_fun_raw.simps lookup_raw.simps update_by_fun_gr_raw.simps
    by (rule, rule conjI, rule update_by_fun_gr_pair_eq_update_by_fun_pair, fact, fact refl)
qed

corollary oalist_inv_update_by_fun_gr_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_fun_gr_raw k f xs)"
  unfolding update_by_fun_gr_raw_eq_update_by_fun_raw[OF assms] using assms by (rule oalist_inv_update_by_fun_raw)

corollary lookup_raw_update_by_fun_gr_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_fun_gr_raw k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_raw xs k2)"
  using assms by (simp add: update_by_fun_gr_raw_eq_update_by_fun_raw lookup_raw_update_by_fun_raw)

subsubsection \<open>@{const map_raw} and @{const map_val_raw}\<close>

lemma map_raw_cong:
  assumes "\<And>kv. kv \<in> set (fst xs) \<Longrightarrow> f kv = g kv"
  shows "map_raw f xs = map_raw g xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "f kv = g kv" if "kv \<in> set xs'" for kv using that by (simp add: xs)
  thus ?thesis by (simp add: xs, rule map_pair_cong)
qed

lemma map_raw_subset: "set (fst (map_raw f xs)) \<subseteq> f ` set (fst xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  show ?thesis by (simp add: xs map_pair_subset)
qed

lemma oalist_inv_map_raw:
  assumes "oalist_inv xs"
    and "\<And>a b. key_compare (rep_key_order (snd xs)) (fst (f a)) (fst (f b)) = key_compare (rep_key_order (snd xs)) (fst a) (fst b)"
  shows "oalist_inv (map_raw f xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms(1) have "oalist_inv (xs', ko)" by (simp only: xs)
  moreover from assms(2)
  have "\<And>a b. key_compare (rep_key_order ko) (fst (f a)) (fst (f b)) = key_compare (rep_key_order ko) (fst a) (fst b)"
    by (simp add: xs)
  ultimately show ?thesis unfolding xs map_raw.simps oalist_inv_alt by (rule oalist_inv_raw_map_pair)
qed

lemma lookup_raw_map_raw:
  assumes "oalist_inv xs" and "snd (f (k, 0)) = 0"
    and "\<And>a b. key_compare (rep_key_order (snd xs)) (fst (f a)) (fst (f b)) = key_compare (rep_key_order (snd xs)) (fst a) (fst b)"
  shows "lookup_raw (map_raw f xs) (fst (f (k, v))) = snd (f (k, lookup_raw xs k))"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms(1) have "oalist_inv (xs', ko)" by (simp only: xs)
  moreover note assms(2)
  moreover from assms(3)
  have "\<And>a b. key_compare (rep_key_order ko) (fst (f a)) (fst (f b)) = key_compare (rep_key_order ko) (fst a) (fst b)"
    by (simp add: xs)
  ultimately show ?thesis unfolding xs lookup_raw.simps map_raw.simps oalist_inv_alt
    by (rule lookup_pair_map_pair)
qed

lemma map_raw_id:
  assumes "oalist_inv xs"
  shows "map_raw id xs = xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv_raw ko xs'" by (simp only: xs oalist_inv_alt)
  hence "map_pair id xs' = xs'"
  proof (induct xs' rule: oalist_inv_raw_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs')
    show ?case by (simp add: Let_def Cons(3, 5) id_def[symmetric])
  qed
  thus ?thesis by (simp add: xs)
qed

lemma map_val_raw_cong:
  assumes "\<And>k v. (k, v) \<in> set (fst xs) \<Longrightarrow> f k v = g k v"
  shows "map_val_raw f xs = map_val_raw g xs"
proof (rule map_raw_cong)
  fix kv
  assume "kv \<in> set (fst xs)"
  moreover obtain k v where "kv = (k, v)" by fastforce
  ultimately show "(case kv of (k, v) \<Rightarrow> (k, f k v)) = (case kv of (k, v) \<Rightarrow> (k, g k v))"
    by (simp add: assms)
qed

lemma oalist_inv_map_val_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (map_val_raw f xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs map_raw.simps oalist_inv_alt by (rule oalist_inv_raw_map_val_pair)
qed

lemma lookup_raw_map_val_raw:
  assumes "oalist_inv xs" and "f k 0 = 0"
  shows "lookup_raw (map_val_raw f xs) k = f k (lookup_raw xs k)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs map_raw.simps lookup_raw.simps oalist_inv_alt
    by (rule lookup_pair_map_val_pair)
qed

subsubsection \<open>@{const map2_val_raw}\<close>

definition map2_val_compat' :: "(('a, 'b::zero, 'o) oalist_raw \<Rightarrow> ('a, 'c::zero, 'o) oalist_raw) \<Rightarrow> bool"
  where "map2_val_compat' f \<longleftrightarrow>
      (\<forall>zs. (oalist_inv zs \<longrightarrow> (oalist_inv (f zs) \<and> snd (f zs) = snd zs \<and> fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs))))"

lemma map2_val_compat'I:
  assumes "\<And>zs. oalist_inv zs \<Longrightarrow> oalist_inv (f zs)"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> snd (f zs) = snd zs"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs)"
  shows "map2_val_compat' f"
  unfolding map2_val_compat'_def using assms by blast

lemma map2_val_compat'D1:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "oalist_inv (f zs)"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'D2:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "snd (f zs) = snd zs"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'D3:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs)"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'_map_val_raw: "map2_val_compat' (map_val_raw f)"
proof (rule map2_val_compat'I, erule oalist_inv_map_val_raw)
  fix zs::"('a, 'b, 'o) oalist_raw"
  obtain zs' ko where "zs = (zs', ko)" by fastforce
  thus "snd (map_val_raw f zs) = snd zs" by simp
next
  fix zs::"('a, 'b, 'o) oalist_raw"
  obtain zs' ko where zs: "zs = (zs', ko)" by fastforce
  show "fst ` set (fst (map_val_raw f zs)) \<subseteq> fst ` set (fst zs)"
  proof (simp add: zs)
    from map_pair_subset have "fst ` set (map_val_pair f zs') \<subseteq> fst ` (\<lambda>(k, v). (k, f k v)) ` set zs'"
      by (rule image_mono)
    also have "... = fst ` set zs'" by force
    finally show "fst ` set (map_val_pair f zs') \<subseteq> fst ` set zs'" .
  qed
qed

lemma map2_val_compat'_id: "map2_val_compat' id"
  by (rule map2_val_compat'I, auto)

lemma map2_val_compat'_imp_map2_val_compat:
  assumes "map2_val_compat' g"
  shows "map2_val_compat ko (\<lambda>zs. fst (g (zs, ko)))"
proof (rule map2_val_compatI)
  fix zs::"('a \<times> 'b) list"
  assume a: "oalist_inv_raw ko zs"
  hence "oalist_inv (zs, ko)" by (simp only: oalist_inv_alt)
  with assms have "oalist_inv (g (zs, ko))" by (rule map2_val_compat'D1)
  hence "oalist_inv (fst (g (zs, ko)), snd (g (zs, ko)))" by simp
  thus "oalist_inv_raw ko (fst (g (zs, ko)))" using assms a by (simp add: oalist_inv_alt map2_val_compat'D2)
next
  fix zs::"('a \<times> 'b) list"
  assume a: "oalist_inv_raw ko zs"
  hence "oalist_inv (zs, ko)" by (simp only: oalist_inv_alt)
  with assms have "fst ` set (fst (g (zs, ko))) \<subseteq> fst ` set (fst (zs, ko))" by (rule map2_val_compat'D3)
  thus "fst ` set (fst (g (zs, ko))) \<subseteq> fst ` set zs" by simp
qed

lemma oalist_inv_map2_val_raw:
  assumes "oalist_inv xs" and "oalist_inv ys"
  assumes "map2_val_compat' g" and "map2_val_compat' h"
  shows "oalist_inv (map2_val_raw f g h xs ys)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist_aux ox ys"
  from assms(1) have "oalist_inv_raw ox xs'" by (simp add: xs oalist_inv_alt)
  moreover from assms(2) have "oalist_inv_raw ox (sort_oalist_aux ox ys)"
    by (rule oalist_inv_raw_sort_oalist_aux)
  moreover from assms(3) have "map2_val_compat ko (\<lambda>zs. fst (g (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  moreover from assms(4) have "map2_val_compat ko (\<lambda>zs. fst (h (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  ultimately have "oalist_inv_raw ox (map2_val_pair ox f (\<lambda>zs. fst (g (zs, ox))) (\<lambda>zs. fst (h (zs, ox))) xs' ?ys)"
    by (rule oalist_inv_raw_map2_val_pair)
  thus ?thesis by (simp add: xs oalist_inv_alt)
qed

lemma lookup_raw_map2_val_raw:
  assumes "oalist_inv xs" and "oalist_inv ys"
  assumes "map2_val_compat' g" and "map2_val_compat' h"
  assumes "\<And>zs. oalist_inv zs \<Longrightarrow> g zs = map_val_raw (\<lambda>k v. f k v 0) zs"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> h zs = map_val_raw (\<lambda>k. f k 0) zs"
    and "\<And>k. f k 0 0 = 0"
  shows "lookup_raw (map2_val_raw f g h xs ys) k0 = f k0 (lookup_raw xs k0) (lookup_raw ys k0)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist_aux ox ys"
  from assms(1) have "oalist_inv_raw ox xs'" by (simp add: xs oalist_inv_alt)
  moreover from assms(2) have "oalist_inv_raw ox (sort_oalist_aux ox ys)" by (rule oalist_inv_raw_sort_oalist_aux)
  moreover from assms(3) have "map2_val_compat ko (\<lambda>zs. fst (g (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  moreover from assms(4) have "map2_val_compat ko (\<lambda>zs. fst (h (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  ultimately have "lookup_pair ox (map2_val_pair ox f (\<lambda>zs. fst (g (zs, ox))) (\<lambda>zs. fst (h (zs, ox))) xs' ?ys) k0 =
                      f k0 (lookup_pair ox xs' k0) (lookup_pair ox ?ys k0)" using _ _ assms(7)
  proof (rule lookup_pair_map2_val_pair)
    fix zs::"('a \<times> 'b) list"
    assume "oalist_inv_raw ox zs"
    hence "oalist_inv (zs, ox)" by (simp only: oalist_inv_alt)
    hence "g (zs, ox) = map_val_raw (\<lambda>k v. f k v 0) (zs, ox)" by (rule assms(5))
    thus "fst (g (zs, ox)) = map_val_pair (\<lambda>k v. f k v 0) zs" by simp
  next
    fix zs::"('a \<times> 'c) list"
    assume "oalist_inv_raw ox zs"
    hence "oalist_inv (zs, ox)" by (simp only: oalist_inv_alt)
    hence "h (zs, ox) = map_val_raw (\<lambda>k. f k 0) (zs, ox)" by (rule assms(6))
    thus "fst (h (zs, ox)) = map_val_pair (\<lambda>k. f k 0) zs" by simp
  qed
  also from assms(2) have "... = f k0 (lookup_pair ox xs' k0) (lookup_raw ys k0)"
    by (simp only: lookup_pair_sort_oalist_aux)
  finally have *: "lookup_pair ox (map2_val_pair ox f (\<lambda>zs. fst (g (zs, ox))) (\<lambda>zs. fst (h (zs, ox))) xs' ?ys) k0 =
                    f k0 (lookup_pair ox xs' k0) (lookup_raw ys k0)" .
  thus ?thesis by (simp add: xs)
qed

lemma map2_val_raw_singleton_eq_update_by_fun_raw:
  assumes "oalist_inv xs"
  assumes "\<And>k x. f k x 0 = x" and "\<And>zs. oalist_inv zs \<Longrightarrow> g zs = zs"
    and "\<And>ko. h ([(k, v)], ko) = map_val_raw (\<lambda>k. f k 0) ([(k, v)], ko)"
  shows "map2_val_raw f g h xs ([(k, v)], ko) = update_by_fun_raw k (\<lambda>x. f k x v) xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist ox [(k, v)]"
  from assms(1) have inv: "oalist_inv (xs', ox)" by (simp only: xs)
  hence inv_raw: "oalist_inv_raw ox xs'" by (simp only: oalist_inv_alt)
  show ?thesis
  proof (simp add: xs, intro conjI impI)
    assume "ox = ko"
    from inv_raw have "oalist_inv_raw ko xs'" by (simp only: \<open>ox = ko\<close>)
    thus "map2_val_pair ko f (\<lambda>zs. fst (g (zs, ko))) (\<lambda>zs. fst (h (zs, ko))) xs' [(k, v)] =
              update_by_fun_pair ko k (\<lambda>x. f k x v) xs'"
      using assms(2)
    proof (rule map2_val_pair_singleton_eq_update_by_fun_pair)
      fix zs::"('a \<times> 'b) list"
      assume "oalist_inv_raw ko zs"
      hence "oalist_inv (zs, ko)" by (simp only: oalist_inv_alt)
      hence "g (zs, ko) = (zs, ko)" by (rule assms(3))
      thus "fst (g (zs, ko)) = zs" by simp
    next
      show "fst (h ([(k, v)], ko)) = map_val_pair (\<lambda>k. f k 0) [(k, v)]" by (simp add: assms(4))
    qed
  next
    show "map2_val_pair ox f (\<lambda>zs. fst (g (zs, ox))) (\<lambda>zs. fst (h (zs, ox))) xs' (sort_oalist ox [(k, v)]) =
          update_by_fun_pair ox k (\<lambda>x. f k x v) xs'"
    proof (cases "v = 0")
      case True
      have eq1: "sort_oalist ox [(k, 0)] = []" by (simp add: sort_oalist_def)
      from inv have eq2: "g (xs', ox) = (xs', ox)" by (rule assms(3))
      show ?thesis
        by (simp add: True eq1 eq2 assms(2) update_by_fun_pair_eq_update_by_pair[OF inv_raw],
            rule HOL.sym, rule update_by_pair_id, fact inv_raw, fact refl)
    next
      case False
      hence "oalist_inv_raw ox [(k, v)]" by (simp add: oalist_inv_raw_singleton)
      hence eq: "sort_oalist ox [(k, v)] = [(k, v)]" by (rule sort_oalist_id)
      show ?thesis unfolding eq using inv_raw assms(2)
      proof (rule map2_val_pair_singleton_eq_update_by_fun_pair)
        fix zs::"('a \<times> 'b) list"
        assume "oalist_inv_raw ox zs"
        hence "oalist_inv (zs, ox)" by (simp only: oalist_inv_alt)
        hence "g (zs, ox) = (zs, ox)" by (rule assms(3))
        thus "fst (g (zs, ox)) = zs" by simp
      next
        show "fst (h ([(k, v)], ox)) = map_val_pair (\<lambda>k. f k 0) [(k, v)]" by (simp add: assms(4))
      qed
    qed
  qed
qed

subsubsection \<open>@{const lex_ord_raw}\<close>

lemma lex_ord_raw_EqI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> f k (lookup_raw xs k) (lookup_raw ys k) = Some Eq"
  shows "lex_ord_raw ko f xs ys = Some Eq"
  unfolding lex_ord_raw_def
  by (rule lex_ord_pair_EqI, simp_all add: assms oalist_inv_raw_sort_oalist_aux lookup_pair_sort_oalist_aux set_sort_oalist_aux)

lemma lex_ord_raw_valI:
  assumes "oalist_inv xs" and "oalist_inv ys" and "aux \<noteq> Some Eq"
  assumes "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" and "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lt ko k' k \<Longrightarrow>
              f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
  shows "lex_ord_raw ko f xs ys = aux"
  unfolding lex_ord_raw_def
  using oalist_inv_sort_oalist_aux[OF assms(1)] oalist_inv_raw_sort_oalist_aux[OF assms(2)] assms(3)
  unfolding oalist_inv_alt
proof (rule lex_ord_pair_valI)
  from assms(1, 2, 4) show "k \<in> fst ` set (sort_oalist_aux ko xs) \<union> fst ` set (sort_oalist_aux ko ys)"
    by (simp add: set_sort_oalist_aux)
next
  from assms(1, 2, 5) show "aux = f k (lookup_pair ko (sort_oalist_aux ko xs) k) (lookup_pair ko (sort_oalist_aux ko ys) k)"
    by (simp add: lookup_pair_sort_oalist_aux)
next
  fix k'
  assume "k' \<in> fst ` set (sort_oalist_aux ko xs) \<union> fst ` set (sort_oalist_aux ko ys)"
  with assms(1, 2) have "k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: set_sort_oalist_aux)
  moreover assume "lt ko k' k"
  ultimately have "f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq" by (rule assms(6))
  with assms(1, 2) show "f k' (lookup_pair ko (sort_oalist_aux ko xs) k') (lookup_pair ko (sort_oalist_aux ko ys) k') = Some Eq"
    by (simp add: lookup_pair_sort_oalist_aux)
qed

lemma lex_ord_raw_EqD:
  assumes "oalist_inv xs" and "oalist_inv ys" and "lex_ord_raw ko f xs ys = Some Eq"
    and "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
  shows "f k (lookup_raw xs k) (lookup_raw ys k) = Some Eq"
proof -
  have "f k (lookup_pair ko (sort_oalist_aux ko xs) k) (lookup_pair ko (sort_oalist_aux ko ys) k) = Some Eq"
    by (rule lex_ord_pair_EqD[where f=f],
        simp_all add: oalist_inv_raw_sort_oalist_aux assms lex_ord_raw_def[symmetric] set_sort_oalist_aux del: Un_iff)
  with assms(1, 2) show ?thesis by (simp add: lookup_pair_sort_oalist_aux)
qed

lemma lex_ord_raw_valE:
  assumes "oalist_inv xs" and "oalist_inv ys" and "lex_ord_raw ko f xs ys = aux"
    and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
    and "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lt ko k' k \<Longrightarrow>
            f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
proof -
  let ?xs = "sort_oalist_aux ko xs"
  let ?ys = "sort_oalist_aux ko ys"
  from assms(3) have "lex_ord_pair ko f ?xs ?ys = aux" by (simp only: lex_ord_raw_def)
  with oalist_inv_sort_oalist_aux[OF assms(1)] oalist_inv_sort_oalist_aux[OF assms(2)]
  obtain k where a: "k \<in> fst ` set ?xs \<union> fst ` set ?ys"
    and b: "aux = f k (lookup_pair ko ?xs k) (lookup_pair ko ?ys k)"
    and c: "\<And>k'. k' \<in> fst ` set ?xs \<union> fst ` set ?ys \<Longrightarrow> lt ko k' k \<Longrightarrow>
            f k' (lookup_pair ko ?xs k') (lookup_pair ko ?ys k') = Some Eq"
    using assms(4) unfolding oalist_inv_alt by (rule lex_ord_pair_valE, blast)
  from a have "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
    by (simp add: set_sort_oalist_aux assms(1, 2))
  moreover from b have "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    by (simp add: lookup_pair_sort_oalist_aux assms(1, 2))
  moreover have "f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
    if k'_in: "k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" and k'_less: "lt ko k' k" for k'
  proof -
    have "f k' (lookup_raw xs k') (lookup_raw ys k') = f k' (lookup_pair ko ?xs k') (lookup_pair ko ?ys k')"
      by (simp add: lookup_pair_sort_oalist_aux assms(1, 2))
    also have "... = Some Eq"
    proof (rule c)
      from k'_in show "k' \<in> fst ` set ?xs \<union> fst ` set ?ys"
        by (simp add:  set_sort_oalist_aux assms(1, 2))
    next
      from k'_less show "lt ko k' k" by (simp only: lt_of_key_order.rep_eq)
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis ..
qed

subsubsection \<open>@{const prod_ord_raw}\<close>

lemma prod_ord_rawI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> P k (lookup_raw xs k) (lookup_raw ys k)"
  shows "prod_ord_raw P xs ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp only: xs oalist_inv_alt)
  hence *: "prod_ord_pair ox P xs' (sort_oalist_aux ox ys)" using oalist_inv_raw_sort_oalist_aux
  proof (rule prod_ord_pairI)
    fix k
    assume "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)"
    hence "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: xs set_sort_oalist_aux assms(2))
    hence "P k (lookup_raw xs k) (lookup_raw ys k)" by (rule assms(3))
    thus "P k (lookup_pair ox xs' k) (lookup_pair ox (sort_oalist_aux ox ys) k)"
      by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
  qed fact
  thus ?thesis by (simp add: xs)
qed

lemma prod_ord_rawD:
  assumes "oalist_inv xs" and "oalist_inv ys" and "prod_ord_raw P xs ys"
    and "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
  shows "P k (lookup_raw xs k) (lookup_raw ys k)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp only: xs oalist_inv_alt)
  moreover note oalist_inv_raw_sort_oalist_aux[OF assms(2)]
  moreover from assms(3) have "prod_ord_pair ox P xs' (sort_oalist_aux ox ys)" by (simp add: xs)
  moreover from assms(4) have "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)"
    by (simp add: xs set_sort_oalist_aux assms(2))
  ultimately have *: "P k (lookup_pair ox xs' k) (lookup_pair ox (sort_oalist_aux ox ys) k)"
    by (rule prod_ord_pairD)
  thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
qed

corollary prod_ord_raw_alt:
  assumes "oalist_inv xs" and "oalist_inv ys"
  shows "prod_ord_raw P xs ys \<longleftrightarrow>
          (\<forall>k\<in>fst ` set (fst xs) \<union> fst ` set (fst ys). P k (lookup_raw xs k) (lookup_raw ys k))"
  using prod_ord_rawI[OF assms] prod_ord_rawD[OF assms] by meson

subsubsection \<open>@{const oalist_eq_raw}\<close>

lemma oalist_eq_rawI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lookup_raw xs k = lookup_raw ys k"
  shows "oalist_eq_raw xs ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv_raw ox xs'" by (simp only: xs oalist_inv_alt)
  hence *: "xs' = sort_oalist_aux ox ys" using oalist_inv_raw_sort_oalist_aux[OF assms(2)]
  proof (rule lookup_pair_inj)
    show "lookup_pair ox xs' = lookup_pair ox (sort_oalist_aux ox ys)"
    proof
      fix k
      show "lookup_pair ox xs' k = lookup_pair ox (sort_oalist_aux ox ys) k"
      proof (cases "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)")
        case True
        hence "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: xs set_sort_oalist_aux assms(2))
        hence "lookup_raw xs k = lookup_raw ys k" by (rule assms(3))
        thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
      next
        case False
        hence "k \<notin> fst ` set xs'" and "k \<notin> fst ` set (sort_oalist_aux ox ys)" by simp_all
        with \<open>oalist_inv_raw ox xs'\<close> oalist_inv_raw_sort_oalist_aux[OF assms(2)]
        have "lookup_pair ox xs' k = 0" and "lookup_pair ox (sort_oalist_aux ox ys) k = 0"
          by (simp_all add: lookup_pair_eq_0)
        thus ?thesis by simp
      qed
    qed
  qed
  thus ?thesis by (simp add: xs)
qed

lemma oalist_eq_rawD:
  assumes "oalist_inv ys" and "oalist_eq_raw xs ys"
  shows "lookup_raw xs = lookup_raw ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(2) have "xs' = sort_oalist_aux ox ys" by (simp add: xs)
  hence "lookup_pair ox xs' = lookup_pair ox (sort_oalist_aux ox ys)" by simp
  thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(1))
qed

lemma oalist_eq_raw_alt:
  assumes "oalist_inv xs" and "oalist_inv ys"
  shows "oalist_eq_raw xs ys \<longleftrightarrow> (lookup_raw xs = lookup_raw ys)"
  using oalist_eq_rawI[OF assms] oalist_eq_rawD[OF assms(2)] by metis

subsubsection \<open>@{const sort_oalist_raw}\<close>

lemma oalist_inv_sort_oalist_raw: "oalist_inv (sort_oalist_raw xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  show ?thesis by (simp add: xs oalist_inv_raw_sort_oalist oalist_inv_alt)
qed

lemma sort_oalist_raw_id:
  assumes "oalist_inv xs"
  shows "sort_oalist_raw xs = xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv_raw ko xs'" by (simp only: xs oalist_inv_alt)
  hence "sort_oalist ko xs' = xs'" by (rule sort_oalist_id)
  thus ?thesis by (simp add: xs)
qed

lemma set_sort_oalist_raw:
  assumes "distinct (map fst (fst xs))"
  shows "set (fst (sort_oalist_raw xs)) = {kv. kv \<in> set (fst xs) \<and> snd kv \<noteq> 0}"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "distinct (map fst xs')" by (simp add: xs)
  hence "set (sort_oalist ko xs') = {kv \<in> set xs'. snd kv \<noteq> 0}" by (rule set_sort_oalist)
  thus ?thesis by (simp add: xs)
qed

end (* oalist_raw *)

subsection \<open>Fundamental Operations on One List\<close>

locale oalist_abstract = oalist_raw rep_key_order for rep_key_order::"'o \<Rightarrow> 'a key_order" +
  fixes list_of_oalist :: "'x \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  fixes oalist_of_list :: "('a, 'b, 'o) oalist_raw \<Rightarrow> 'x"
  assumes oalist_inv_list_of_oalist: "oalist_inv (list_of_oalist x)"
  and list_of_oalist_of_list: "list_of_oalist (oalist_of_list xs) = sort_oalist_raw xs"
  and oalist_of_list_of_oalist: "oalist_of_list (list_of_oalist x) = x"
begin

lemma list_of_oalist_of_list_id:
  assumes "oalist_inv xs"
  shows "list_of_oalist (oalist_of_list xs) = xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms show ?thesis by (simp add: xs list_of_oalist_of_list sort_oalist_id oalist_inv_alt)
qed

definition lookup :: "'x \<Rightarrow> 'a \<Rightarrow> 'b"
  where "lookup xs = lookup_raw (list_of_oalist xs)"

definition sorted_domain :: "'o \<Rightarrow> 'x \<Rightarrow> 'a list"
  where "sorted_domain ko xs = sorted_domain_raw ko (list_of_oalist xs)"

definition empty :: "'o \<Rightarrow> 'x"
  where "empty ko = oalist_of_list ([], ko)"

definition reorder :: "'o \<Rightarrow> 'x \<Rightarrow> 'x"
  where "reorder ko xs = oalist_of_list (sort_oalist_aux ko (list_of_oalist xs), ko)"

definition tl :: "'x \<Rightarrow> 'x"
  where "tl xs = oalist_of_list (tl_raw (list_of_oalist xs))"

definition hd :: "'x \<Rightarrow> ('a \<times> 'b)"
  where "hd xs = List.hd (fst (list_of_oalist xs))"

definition except_min :: "'o \<Rightarrow> 'x \<Rightarrow> 'x"
  where "except_min ko xs = tl (reorder ko xs)"

definition min_key_val :: "'o \<Rightarrow> 'x \<Rightarrow> ('a \<times> 'b)"
  where "min_key_val ko xs = min_key_val_raw ko (list_of_oalist xs)"

definition insert :: "('a \<times> 'b) \<Rightarrow> 'x \<Rightarrow> 'x"
  where "insert x xs = oalist_of_list (update_by_raw x (list_of_oalist xs))"

definition update_by_fun :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'x"
  where "update_by_fun k f xs = oalist_of_list (update_by_fun_raw k f (list_of_oalist xs))"

definition update_by_fun_gr :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'x"
  where "update_by_fun_gr k f xs = oalist_of_list (update_by_fun_gr_raw k f (list_of_oalist xs))"

definition filter :: "(('a \<times> 'b) \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> 'x"
  where "filter P xs = oalist_of_list (filter_raw P (list_of_oalist xs))"

definition map2_val_neutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'x \<Rightarrow> 'x"
  where "map2_val_neutr f xs ys = oalist_of_list (map2_val_raw f id id (list_of_oalist xs) (list_of_oalist ys))"

definition oalist_eq :: "'x \<Rightarrow> 'x \<Rightarrow> bool"
  where "oalist_eq xs ys = oalist_eq_raw (list_of_oalist xs) (list_of_oalist ys)"

subsubsection \<open>Invariant\<close>

lemma zero_notin_list_of_oalist: "0 \<notin> snd ` set (fst (list_of_oalist xs))"
proof -
  from oalist_inv_list_of_oalist have "oalist_inv_raw (snd (list_of_oalist xs)) (fst (list_of_oalist xs))"
    by (simp only: oalist_inv_def)
  thus ?thesis by (rule oalist_inv_rawD1)
qed

lemma list_of_oalist_sorted: "sorted_wrt (lt (snd (list_of_oalist xs))) (map fst (fst (list_of_oalist xs)))"
proof -
  from oalist_inv_list_of_oalist have "oalist_inv_raw (snd (list_of_oalist xs)) (fst (list_of_oalist xs))"
    by (simp only: oalist_inv_def)
  thus ?thesis by (rule oalist_inv_rawD2)
qed

subsubsection \<open>@{const lookup}\<close>

lemma lookup_eq_value: "v \<noteq> 0 \<Longrightarrow> lookup xs k = v \<longleftrightarrow> ((k, v) \<in> set (fst (list_of_oalist xs)))"
  unfolding lookup_def using oalist_inv_list_of_oalist by (rule lookup_raw_eq_value)

lemma lookup_eq_valueI: "(k, v) \<in> set (fst (list_of_oalist xs)) \<Longrightarrow> lookup xs k = v"
  unfolding lookup_def using oalist_inv_list_of_oalist by (rule lookup_raw_eq_valueI)

lemma lookup_oalist_of_list:
  "distinct (map fst xs) \<Longrightarrow> lookup (oalist_of_list (xs, ko)) = lookup_dflt xs"
  by (simp add: list_of_oalist_of_list lookup_def lookup_pair_sort_oalist')

subsubsection \<open>@{const sorted_domain}\<close>

lemma set_sorted_domain: "set (sorted_domain ko xs) = fst ` set (fst (list_of_oalist xs))"
  unfolding sorted_domain_def using oalist_inv_list_of_oalist by (rule set_sorted_domain_raw)

lemma in_sorted_domain_iff_lookup: "k \<in> set (sorted_domain ko xs) \<longleftrightarrow> (lookup xs k \<noteq> 0)"
  unfolding sorted_domain_def lookup_def using oalist_inv_list_of_oalist
  by (rule in_sorted_domain_raw_iff_lookup_raw)

lemma sorted_sorted_domain: "sorted_wrt (lt ko) (sorted_domain ko xs)"
  unfolding sorted_domain_def lt_of_key_order.rep_eq[symmetric]
  using oalist_inv_list_of_oalist by (rule sorted_sorted_domain_raw)

subsubsection \<open>@{const empty} and Singletons\<close>

lemma list_of_oalist_empty [simp, code abstract]: "list_of_oalist (empty ko) = ([], ko)"
  by (simp add: empty_def sort_oalist_def list_of_oalist_of_list)

lemma lookup_empty: "lookup (empty ko) k = 0"
  by (simp add: lookup_def)

lemma lookup_oalist_of_list_single:
  "lookup (oalist_of_list ([(k, v)], ko)) k' = (if k = k' then v else 0)"
  by (simp add: lookup_def list_of_oalist_of_list sort_oalist_def key_compare_Eq split: order.split)

subsubsection \<open>@{const reorder}\<close>

lemma list_of_oalist_reorder [simp, code abstract]:
  "list_of_oalist (reorder ko xs) = (sort_oalist_aux ko (list_of_oalist xs), ko)"
  unfolding reorder_def
  by (rule list_of_oalist_of_list_id, simp add: oalist_inv_def, rule oalist_inv_raw_sort_oalist_aux, fact oalist_inv_list_of_oalist)

lemma lookup_reorder: "lookup (reorder ko xs) k = lookup xs k"
  by (simp add: lookup_def lookup_pair_sort_oalist_aux oalist_inv_list_of_oalist)

subsubsection \<open>@{const hd} and @{const tl}\<close>

lemma list_of_oalist_tl [simp, code abstract]: "list_of_oalist (tl xs) = tl_raw (list_of_oalist xs)"
  unfolding tl_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_tl_raw, fact oalist_inv_list_of_oalist)

lemma lookup_tl:
  "lookup (tl xs) k =
        (if (\<forall>k'\<in>fst ` set (fst (list_of_oalist xs)). le (snd (list_of_oalist xs)) k k') then 0 else lookup xs k)"
  by (simp add: lookup_def lookup_raw_tl_raw oalist_inv_list_of_oalist)

lemma hd_in:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "hd xs \<in> set (fst (list_of_oalist xs))"
  unfolding hd_def using assms by (rule hd_in_set)

lemma snd_hd:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "snd (hd xs) = lookup xs (fst (hd xs))"
proof -
  from assms have *: "hd xs \<in> set (fst (list_of_oalist xs))" by (rule hd_in)
  show ?thesis by (rule HOL.sym, rule lookup_eq_valueI, simp add: *)
qed

lemma lookup_tl': "lookup (tl xs) k = (if k = fst (hd xs) then 0 else lookup xs k)"
  by (simp add: lookup_def lookup_raw_tl_raw' oalist_inv_list_of_oalist hd_def)

lemma hd_tl:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "list_of_oalist xs = ((hd xs) # (fst (list_of_oalist (tl xs))), snd (list_of_oalist (tl xs)))"
proof -
  obtain xs' ko where xs: "list_of_oalist xs = (xs', ko)" by fastforce
  from assms obtain x xs'' where xs': "xs' = x # xs''" unfolding xs fst_conv using list.exhaust by blast
  show ?thesis by (simp add: xs xs' hd_def)
qed

subsubsection \<open>@{const min_key_val}\<close>

lemma min_key_val_alt:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "min_key_val ko xs = hd (reorder ko xs)"
  using assms oalist_inv_list_of_oalist by (simp add: min_key_val_def hd_def min_key_val_raw_alt)

lemma min_key_val_in:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "min_key_val ko xs \<in> set (fst (list_of_oalist xs))"
  unfolding min_key_val_def using assms by (rule min_key_val_raw_in)

lemma snd_min_key_val:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "snd (min_key_val ko xs) = lookup xs (fst (min_key_val ko xs))"
  unfolding lookup_def min_key_val_def using oalist_inv_list_of_oalist assms by (rule snd_min_key_val_raw)

lemma min_key_val_minimal:
  assumes "z \<in> set (fst (list_of_oalist xs))"
  shows "le ko (fst (min_key_val ko xs)) (fst z)"
  unfolding min_key_val_def
  by (rule min_key_val_raw_minimal, fact oalist_inv_list_of_oalist, fact)

subsubsection \<open>@{const except_min}\<close>

lemma list_of_oalist_except_min [simp, code abstract]:
  "list_of_oalist (except_min ko xs) = (List.tl (sort_oalist_aux ko (list_of_oalist xs)), ko)"
  by (simp add: except_min_def)

lemma except_min_Nil:
  assumes "fst (list_of_oalist xs) = []"
  shows "fst (list_of_oalist (except_min ko xs)) = []"
proof -
  obtain xs' ox where eq: "list_of_oalist xs = (xs', ox)" by fastforce
  from assms have "xs' = []" by (simp add: eq)
  show ?thesis by (simp add: eq \<open>xs' = []\<close> sort_oalist_def)
qed

lemma lookup_except_min:
  "lookup (except_min ko xs) k =
        (if (\<forall>k'\<in>fst ` set (fst (list_of_oalist xs)). le ko k k') then 0 else lookup xs k)"
  by (simp add: except_min_def lookup_tl set_sort_oalist_aux oalist_inv_list_of_oalist lookup_reorder)

lemma lookup_except_min':
  "lookup (except_min ko xs) k = (if k = fst (min_key_val ko xs) then 0 else lookup xs k)"
proof (cases "fst (list_of_oalist xs) = []")
  case True
  hence "lookup xs k = 0" by (metis empty_def lookup_empty oalist_of_list_of_oalist prod.collapse)
  thus ?thesis by (simp add: lookup_except_min True)
next
  case False
  thus ?thesis by (simp add: except_min_def lookup_tl' min_key_val_alt lookup_reorder)
qed

subsubsection \<open>@{const insert}\<close>

lemma list_of_oalist_insert [simp, code abstract]:
  "list_of_oalist (insert x xs) = update_by_raw x (list_of_oalist xs)"
  unfolding insert_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_update_by_raw, fact oalist_inv_list_of_oalist)

lemma lookup_insert: "lookup (insert (k, v) xs) k' = (if k = k' then v else lookup xs k')"
  by (simp add: lookup_def lookup_raw_update_by_raw oalist_inv_list_of_oalist split del: if_split cong: if_cong)

subsubsection \<open>@{const update_by_fun} and @{const update_by_fun_gr}\<close>

lemma list_of_oalist_update_by_fun [simp, code abstract]:
  "list_of_oalist (update_by_fun k f xs) = update_by_fun_raw k f (list_of_oalist xs)"
  unfolding update_by_fun_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_update_by_fun_raw, fact oalist_inv_list_of_oalist)

lemma lookup_update_by_fun:
  "lookup (update_by_fun k f xs) k' = (if k = k' then f else id) (lookup xs k')"
  by (simp add: lookup_def lookup_raw_update_by_fun_raw oalist_inv_list_of_oalist split del: if_split cong: if_cong)

lemma list_of_oalist_update_by_fun_gr [simp, code abstract]:
  "list_of_oalist (update_by_fun_gr k f xs) = update_by_fun_gr_raw k f (list_of_oalist xs)"
  unfolding update_by_fun_gr_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_update_by_fun_gr_raw, fact oalist_inv_list_of_oalist)

lemma update_by_fun_gr_eq_update_by_fun: "update_by_fun_gr = update_by_fun"
  by (rule, rule, rule,
      simp add: update_by_fun_gr_def update_by_fun_def update_by_fun_gr_raw_eq_update_by_fun_raw oalist_inv_list_of_oalist)

subsubsection \<open>@{const filter}\<close>

lemma list_of_oalist_filter [simp, code abstract]:
  "list_of_oalist (filter P xs) = filter_raw P (list_of_oalist xs)"
  unfolding filter_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_filter_raw, fact oalist_inv_list_of_oalist)

lemma lookup_filter: "lookup (filter P xs) k = (let v = lookup xs k in if P (k, v) then v else 0)"
  by (simp add: lookup_def lookup_raw_filter_raw oalist_inv_list_of_oalist)

subsubsection \<open>@{const map2_val_neutr}\<close>

lemma list_of_oalist_map2_val_neutr [simp, code abstract]:
  "list_of_oalist (map2_val_neutr f xs ys) = map2_val_raw f id id (list_of_oalist xs) (list_of_oalist ys)"
  unfolding map2_val_neutr_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
      fact map2_val_compat'_id, fact map2_val_compat'_id)

lemma lookup_map2_val_neutr:
  assumes "\<And>k x. f k x 0 = x" and "\<And>k x. f k 0 x = x"
  shows "lookup (map2_val_neutr f xs ys) k = f k (lookup xs k) (lookup ys k)"
proof (simp add: lookup_def, rule lookup_raw_map2_val_raw)
  fix zs::"('a, 'b, 'o) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k v. f k v 0) zs" by (simp add: assms(1) map_raw_id)
next
  fix zs::"('a, 'b, 'o) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k. f k 0) zs" by (simp add: assms(2) map_raw_id)
qed (fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
    fact map2_val_compat'_id, fact map2_val_compat'_id, simp only: assms(1))

subsubsection \<open>@{const oalist_eq}\<close>

lemma oalist_eq_alt: "oalist_eq xs ys \<longleftrightarrow> (lookup xs = lookup ys)"
  by (simp add: oalist_eq_def lookup_def oalist_eq_raw_alt oalist_inv_list_of_oalist)

end (* oalist_abstract *)

subsection \<open>Fundamental Operations on Three Lists\<close>

locale oalist_abstract3 =
  oalist_abstract rep_key_order list_of_oalistx oalist_of_listx +
  oay: oalist_abstract rep_key_order list_of_oalisty oalist_of_listy +
  oaz: oalist_abstract rep_key_order list_of_oalistz oalist_of_listz
  for rep_key_order :: "'o \<Rightarrow> 'a key_order"
  and list_of_oalistx :: "'x \<Rightarrow> ('a, 'b::zero, 'o) oalist_raw"
  and oalist_of_listx :: "('a, 'b, 'o) oalist_raw \<Rightarrow> 'x"
  and list_of_oalisty :: "'y \<Rightarrow> ('a, 'c::zero, 'o) oalist_raw"
  and oalist_of_listy :: "('a, 'c, 'o) oalist_raw \<Rightarrow> 'y"
  and list_of_oalistz :: "'z \<Rightarrow> ('a, 'd::zero, 'o) oalist_raw"
  and oalist_of_listz :: "('a, 'd, 'o) oalist_raw \<Rightarrow> 'z"
begin

definition map_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'x \<Rightarrow> 'y"
  where "map_val f xs = oalist_of_listy (map_val_raw f (list_of_oalistx xs))"

definition map2_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'z"
  where "map2_val f xs ys =
            oalist_of_listz (map2_val_raw f (map_val_raw (\<lambda>k b. f k b 0)) (map_val_raw (\<lambda>k. f k 0))
              (list_of_oalistx xs) (list_of_oalisty ys))"

definition map2_val_rneutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'x"
  where "map2_val_rneutr f xs ys =
            oalist_of_listx (map2_val_raw f id (map_val_raw (\<lambda>k. f k 0)) (list_of_oalistx xs) (list_of_oalisty ys))"

definition lex_ord :: "'o \<Rightarrow> ('a \<Rightarrow> ('b, 'c) comp_opt) \<Rightarrow> ('x, 'y) comp_opt"
  where "lex_ord ko f xs ys = lex_ord_raw ko f (list_of_oalistx xs) (list_of_oalisty ys)"

definition prod_ord :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool"
  where "prod_ord f xs ys = prod_ord_raw f (list_of_oalistx xs) (list_of_oalisty ys)"

subsubsection \<open>@{const map_val}\<close>

lemma map_val_cong:
  assumes "\<And>k v. (k, v) \<in> set (fst (list_of_oalistx xs)) \<Longrightarrow> f k v = g k v"
  shows "map_val f xs = map_val g xs"
  unfolding map_val_def by (rule arg_cong[where f=oalist_of_listy], rule map_val_raw_cong, elim assms)

lemma list_of_oalist_map_val [simp, code abstract]:
  "list_of_oalisty (map_val f xs) = map_val_raw f (list_of_oalistx xs)"
  unfolding map_val_def
  by (rule oay.list_of_oalist_of_list_id, rule oalist_inv_map_val_raw, fact oalist_inv_list_of_oalist)

lemma lookup_map_val: "f k 0 = 0 \<Longrightarrow> oay.lookup (map_val f xs) k = f k (lookup xs k)"
  by (simp add: oay.lookup_def lookup_def lookup_raw_map_val_raw oalist_inv_list_of_oalist)

subsubsection \<open>@{const map2_val} and @{const map2_val_rneutr}\<close>

lemma list_of_oalist_map2_val [simp, code abstract]:
  "list_of_oalistz (map2_val f xs ys) =
      map2_val_raw f (map_val_raw (\<lambda>k b. f k b 0)) (map_val_raw (\<lambda>k. f k 0)) (list_of_oalistx xs) (list_of_oalisty ys)"
  unfolding map2_val_def
  by (rule oaz.list_of_oalist_of_list_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oay.oalist_inv_list_of_oalist,
      fact map2_val_compat'_map_val_raw, fact map2_val_compat'_map_val_raw)

lemma list_of_oalist_map2_val_rneutr [simp, code abstract]:
  "list_of_oalistx (map2_val_rneutr f xs ys) =
      map2_val_raw f id (map_val_raw (\<lambda>k c. f k 0 c)) (list_of_oalistx xs) (list_of_oalisty ys)"
  unfolding map2_val_rneutr_def
  by (rule list_of_oalist_of_list_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oay.oalist_inv_list_of_oalist,
      fact map2_val_compat'_id, fact map2_val_compat'_map_val_raw)

lemma lookup_map2_val:
  assumes "\<And>k. f k 0 0 = 0"
  shows "oaz.lookup (map2_val f xs ys) k = f k (lookup xs k) (oay.lookup ys k)"
  by (simp add: oaz.lookup_def oay.lookup_def lookup_def lookup_raw_map2_val_raw
      map2_val_compat'_map_val_raw assms oalist_inv_list_of_oalist oay.oalist_inv_list_of_oalist)

lemma lookup_map2_val_rneutr:
  assumes "\<And>k x. f k x 0 = x"
  shows "lookup (map2_val_rneutr f xs ys) k = f k (lookup xs k) (oay.lookup ys k)"
proof (simp add: lookup_def oay.lookup_def, rule lookup_raw_map2_val_raw)
  fix zs::"('a, 'b, 'o) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k v. f k v 0) zs" by (simp add: assms map_raw_id)
qed (fact oalist_inv_list_of_oalist, fact oay.oalist_inv_list_of_oalist,
    fact map2_val_compat'_id, fact map2_val_compat'_map_val_raw, rule refl, simp only: assms)

lemma map2_val_rneutr_singleton_eq_update_by_fun:
  assumes "\<And>a x. f a x 0 = x" and "list_of_oalisty ys = ([(k, v)], oy)"
  shows "map2_val_rneutr f xs ys = update_by_fun k (\<lambda>x. f k x v) xs"
  by (simp add: map2_val_rneutr_def update_by_fun_def assms map2_val_raw_singleton_eq_update_by_fun_raw oalist_inv_list_of_oalist)

subsubsection \<open>@{const lex_ord} and @{const prod_ord}\<close>

lemma lex_ord_EqI:
  "(\<And>k. k \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
     f k (lookup xs k) (oay.lookup ys k) = Some Eq) \<Longrightarrow>
  lex_ord ko f xs ys = Some Eq"
  by (simp add: lex_ord_def lookup_def oay.lookup_def, rule lex_ord_raw_EqI,
      rule oalist_inv_list_of_oalist, rule oay.oalist_inv_list_of_oalist, blast)

lemma lex_ord_valI:
  assumes "aux \<noteq> Some Eq" and "k \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys))"
  shows "aux = f k (lookup xs k) (oay.lookup ys k) \<Longrightarrow>
         (\<And>k'. k' \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
              lt ko k' k \<Longrightarrow> f k' (lookup xs k') (oay.lookup ys k') = Some Eq) \<Longrightarrow>
          lex_ord ko f xs ys = aux"
  by (simp (no_asm_use) add: lex_ord_def lookup_def oay.lookup_def, rule lex_ord_raw_valI,
      rule oalist_inv_list_of_oalist, rule oay.oalist_inv_list_of_oalist, rule assms(1), rule assms(2), blast+)

lemma lex_ord_EqD:
  "lex_ord ko f xs ys = Some Eq \<Longrightarrow>
   k \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
   f k (lookup xs k) (oay.lookup ys k) = Some Eq"
  by (simp add: lex_ord_def lookup_def oay.lookup_def, rule lex_ord_raw_EqD[where f=f],
      rule oalist_inv_list_of_oalist, rule oay.oalist_inv_list_of_oalist, assumption, simp)

lemma lex_ord_valE:
  assumes "lex_ord ko f xs ys = aux" and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys))"
    and "aux = f k (lookup xs k) (oay.lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
            lt ko k' k \<Longrightarrow> f k' (lookup xs k') (oay.lookup ys k') = Some Eq"
proof -
  note oalist_inv_list_of_oalist oay.oalist_inv_list_of_oalist
  moreover from assms(1) have "lex_ord_raw ko f (list_of_oalistx xs) (list_of_oalisty ys) = aux"
    by (simp only: lex_ord_def)
  ultimately obtain k where 1: "k \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys))"
    and "aux = f k (lookup_raw (list_of_oalistx xs) k) (lookup_raw (list_of_oalisty ys) k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
            lt ko k' k \<Longrightarrow>
            f k' (lookup_raw (list_of_oalistx xs) k') (lookup_raw (list_of_oalisty ys) k') = Some Eq"
    using assms(2) by (rule lex_ord_raw_valE, blast)
  from this(2, 3) have "aux = f k (lookup xs k) (oay.lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)) \<Longrightarrow>
            lt ko k' k \<Longrightarrow> f k' (lookup xs k') (oay.lookup ys k') = Some Eq"
    by (simp_all only: lookup_def oay.lookup_def)
  with 1 show ?thesis ..
qed

lemma prod_ord_alt:
  "prod_ord P xs ys \<longleftrightarrow>
                  (\<forall>k\<in>fst ` set (fst (list_of_oalistx xs)) \<union> fst ` set (fst (list_of_oalisty ys)).
                      P k (lookup xs k) (oay.lookup ys k))"
  by (simp add: prod_ord_def lookup_def oay.lookup_def prod_ord_raw_alt oalist_inv_list_of_oalist oay.oalist_inv_list_of_oalist)

end (* oalist_abstract3 *)

subsection \<open>Type \<open>oalist\<close>\<close>

global_interpretation ko: comparator "key_compare ko"
  defines lookup_pair_ko = ko.lookup_pair
  and update_by_pair_ko = ko.update_by_pair
  and update_by_fun_pair_ko = ko.update_by_fun_pair
  and update_by_fun_gr_pair_ko = ko.update_by_fun_gr_pair
  and map2_val_pair_ko = ko.map2_val_pair
  and lex_ord_pair_ko = ko.lex_ord_pair
  and prod_ord_pair_ko = ko.prod_ord_pair
  and sort_oalist_ko' = ko.sort_oalist
  by (fact comparator_key_compare)

lemma ko_le: "ko.le = le_of_key_order"
  by (intro ext, simp add: le_of_comp_def le_of_key_order_alt split: order.split)

global_interpretation ko: oalist_raw "\<lambda>x. x"
  rewrites "comparator.lookup_pair (key_compare ko) = lookup_pair_ko ko"
  and "comparator.update_by_pair (key_compare ko) = update_by_pair_ko ko"
  and "comparator.update_by_fun_pair (key_compare ko) = update_by_fun_pair_ko ko"
  and "comparator.update_by_fun_gr_pair (key_compare ko) = update_by_fun_gr_pair_ko ko"
  and "comparator.map2_val_pair (key_compare ko) = map2_val_pair_ko ko"
  and "comparator.lex_ord_pair (key_compare ko) = lex_ord_pair_ko ko"
  and "comparator.prod_ord_pair (key_compare ko) = prod_ord_pair_ko ko"
  and "comparator.sort_oalist (key_compare ko) = sort_oalist_ko' ko"
  defines sort_oalist_aux_ko = ko.sort_oalist_aux
  and lookup_ko = ko.lookup_raw
  and sorted_domain_ko = ko.sorted_domain_raw
  and tl_ko = ko.tl_raw
  and min_key_val_ko = ko.min_key_val_raw
  and update_by_ko = ko.update_by_raw
  and update_by_fun_ko = ko.update_by_fun_raw
  and update_by_fun_gr_ko = ko.update_by_fun_gr_raw
  and map2_val_ko = ko.map2_val_raw
  and lex_ord_ko = ko.lex_ord_raw
  and prod_ord_ko = ko.prod_ord_raw
  and oalist_eq_ko = ko.oalist_eq_raw
  and sort_oalist_ko = ko.sort_oalist_raw
  subgoal by (simp only: lookup_pair_ko_def)
  subgoal by (simp only: update_by_pair_ko_def)
  subgoal by (simp only: update_by_fun_pair_ko_def)
  subgoal by (simp only: update_by_fun_gr_pair_ko_def)
  subgoal by (simp only: map2_val_pair_ko_def)
  subgoal by (simp only: lex_ord_pair_ko_def)
  subgoal by (simp only: prod_ord_pair_ko_def)
  subgoal by (simp only: sort_oalist_ko'_def)
  done

typedef (overloaded) ('a, 'b) oalist = "{xs::('a, 'b::zero, 'a key_order) oalist_raw. ko.oalist_inv xs}"
  morphisms list_of_oalist Abs_oalist
  by (auto simp: ko.oalist_inv_def intro: ko.oalist_inv_raw_Nil)

lemma oalist_eq_iff: "xs = ys \<longleftrightarrow> list_of_oalist xs = list_of_oalist ys"
  by (simp add: list_of_oalist_inject)

lemma oalist_eqI: "list_of_oalist xs = list_of_oalist ys \<Longrightarrow> xs = ys"
  by (simp add: oalist_eq_iff)

text \<open>Formal, totalized constructor for @{typ "('a, 'b) oalist"}:\<close>

definition OAlist :: "('a \<times> 'b) list \<times> 'a key_order \<Rightarrow> ('a, 'b::zero) oalist" where
  "OAlist xs = Abs_oalist (sort_oalist_ko xs)"

definition "oalist_of_list = OAlist"

lemma oalist_inv_list_of_oalist: "ko.oalist_inv (list_of_oalist xs)"
  using list_of_oalist [of xs] by simp

lemma list_of_oalist_OAlist: "list_of_oalist (OAlist xs) = sort_oalist_ko xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  show ?thesis by (simp add: xs OAlist_def Abs_oalist_inverse ko.oalist_inv_raw_sort_oalist ko.oalist_inv_alt)
qed

lemma OAlist_list_of_oalist [code abstype]: "OAlist (list_of_oalist xs) = xs"
proof -
  obtain xs' ox where xs: "list_of_oalist xs = (xs', ox)" by fastforce
  have "ko.oalist_inv_raw ox xs'" by (simp add: xs[symmetric] ko.oalist_inv_alt[symmetric] oalist_inv_list_of_oalist)
  thus ?thesis by (simp add: xs OAlist_def ko.sort_oalist_id, simp add: list_of_oalist_inverse xs[symmetric])
qed

lemma [code abstract]: "list_of_oalist (oalist_of_list xs) = sort_oalist_ko xs"
  by (simp add: list_of_oalist_OAlist oalist_of_list_def)

global_interpretation oa: oalist_abstract "\<lambda>x. x" list_of_oalist OAlist
  defines OAlist_lookup = oa.lookup
  and OAlist_sorted_domain = oa.sorted_domain
  and OAlist_empty = oa.empty
  and OAlist_reorder = oa.reorder
  and OAlist_tl = oa.tl
  and OAlist_hd = oa.hd
  and OAlist_except_min = oa.except_min
  and OAlist_min_key_val = oa.min_key_val
  and OAlist_insert = oa.insert
  and OAlist_update_by_fun = oa.update_by_fun
  and OAlist_update_by_fun_gr = oa.update_by_fun_gr
  and OAlist_filter = oa.filter
  and OAlist_map2_val_neutr = oa.map2_val_neutr
  and OAlist_eq = oa.oalist_eq
  apply standard
  subgoal by (fact oalist_inv_list_of_oalist)
  subgoal by (simp only: list_of_oalist_OAlist sort_oalist_ko_def)
  subgoal by (fact OAlist_list_of_oalist)
  done

global_interpretation oa: oalist_abstract3 "\<lambda>x. x"
    "list_of_oalist::('a, 'b) oalist \<Rightarrow> ('a, 'b::zero, 'a key_order) oalist_raw" OAlist
    "list_of_oalist::('a, 'c) oalist \<Rightarrow> ('a, 'c::zero, 'a key_order) oalist_raw" OAlist
    "list_of_oalist::('a, 'd) oalist \<Rightarrow> ('a, 'd::zero, 'a key_order) oalist_raw" OAlist
  defines OAlist_map_val = oa.map_val
  and OAlist_map2_val = oa.map2_val
  and OAlist_map2_val_rneutr = oa.map2_val_rneutr
  and OAlist_lex_ord = oa.lex_ord
  and OAlist_prod_ord = oa.prod_ord ..

lemmas OAlist_lookup_single = oa.lookup_oalist_of_list_single[folded oalist_of_list_def]

subsection \<open>Type \<open>oalist_tc\<close>\<close>

text \<open>``tc'' stands for ``type class''.\<close>

global_interpretation tc: comparator "comparator_of"
  defines lookup_pair_tc = tc.lookup_pair
  and update_by_pair_tc = tc.update_by_pair
  and update_by_fun_pair_tc = tc.update_by_fun_pair
  and update_by_fun_gr_pair_tc = tc.update_by_fun_gr_pair
  and map2_val_pair_tc = tc.map2_val_pair
  and lex_ord_pair_tc = tc.lex_ord_pair
  and prod_ord_pair_tc = tc.prod_ord_pair
  and sort_oalist_tc = tc.sort_oalist
  by (fact comparator_of)

lemma tc_le_lt [simp]: "tc.le = (\<le>)" "tc.lt = (<)"
  by (auto simp: le_of_comp_def lt_of_comp_def comparator_of_def intro!: ext split: order.split_asm if_split_asm)

typedef (overloaded) ('a, 'b) oalist_tc = "{xs::('a::linorder \<times> 'b::zero) list. tc.oalist_inv_raw xs}"
  morphisms list_of_oalist_tc Abs_oalist_tc
  by (auto intro: tc.oalist_inv_raw_Nil)

lemma oalist_tc_eq_iff: "xs = ys \<longleftrightarrow> list_of_oalist_tc xs = list_of_oalist_tc ys"
  by (simp add: list_of_oalist_tc_inject)

lemma oalist_tc_eqI: "list_of_oalist_tc xs = list_of_oalist_tc ys \<Longrightarrow> xs = ys"
  by (simp add: oalist_tc_eq_iff)

text \<open>Formal, totalized constructor for @{typ "('a, 'b) oalist_tc"}:\<close>

definition OAlist_tc :: "('a \<times> 'b) list \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc" where
  "OAlist_tc xs = Abs_oalist_tc (sort_oalist_tc xs)"

definition "oalist_tc_of_list = OAlist_tc"

lemma oalist_inv_list_of_oalist_tc: "tc.oalist_inv_raw (list_of_oalist_tc xs)"
  using list_of_oalist_tc[of xs] by simp

lemma list_of_oalist_OAlist_tc: "list_of_oalist_tc (OAlist_tc xs) = sort_oalist_tc xs"
  by (simp add: OAlist_tc_def Abs_oalist_tc_inverse tc.oalist_inv_raw_sort_oalist)

lemma OAlist_list_of_oalist_tc [code abstype]: "OAlist_tc (list_of_oalist_tc xs) = xs"
  by (simp add: OAlist_tc_def tc.sort_oalist_id list_of_oalist_tc_inverse oalist_inv_list_of_oalist_tc)

lemma list_of_oalist_tc_of_list [code abstract]: "list_of_oalist_tc (oalist_tc_of_list xs) = sort_oalist_tc xs"
  by (simp add: list_of_oalist_OAlist_tc oalist_tc_of_list_def)

lemma list_of_oalist_tc_of_list_id:
  assumes "tc.oalist_inv_raw xs"
  shows "list_of_oalist_tc (OAlist_tc xs) = xs"
  using assms by (simp add: list_of_oalist_OAlist_tc tc.sort_oalist_id)

text \<open>It is better to define the following operations directly instead of interpreting
  @{locale oalist_abstract}, because @{locale oalist_abstract} defines the operations via their
  \<open>_raw\<close> analogues, whereas in this case we can define them directly via their \<open>_pair\<close> analogues.\<close>

definition OAlist_tc_lookup :: "('a::linorder, 'b::zero) oalist_tc \<Rightarrow> 'a \<Rightarrow> 'b"
  where "OAlist_tc_lookup xs = lookup_pair_tc (list_of_oalist_tc xs)"

definition OAlist_tc_sorted_domain :: "('a::linorder, 'b::zero) oalist_tc \<Rightarrow> 'a list"
  where "OAlist_tc_sorted_domain xs = map fst (list_of_oalist_tc xs)"

definition OAlist_tc_empty :: "('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_empty = OAlist_tc []"

definition OAlist_tc_except_min :: "('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_except_min xs = OAlist_tc (tl (list_of_oalist_tc xs))"

definition OAlist_tc_min_key_val :: "('a::linorder, 'b::zero) oalist_tc \<Rightarrow> ('a \<times> 'b)"
  where "OAlist_tc_min_key_val xs = hd (list_of_oalist_tc xs)"

definition OAlist_tc_insert :: "('a \<times> 'b) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_insert x xs = OAlist_tc (update_by_pair_tc x (list_of_oalist_tc xs))"

definition OAlist_tc_update_by_fun :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_update_by_fun k f xs = OAlist_tc (update_by_fun_pair_tc k f (list_of_oalist_tc xs))"

definition OAlist_tc_update_by_fun_gr :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_update_by_fun_gr k f xs = OAlist_tc (update_by_fun_gr_pair_tc k f (list_of_oalist_tc xs))"

definition OAlist_tc_filter :: "(('a \<times> 'b) \<Rightarrow> bool) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_filter P xs = OAlist_tc (filter P (list_of_oalist_tc xs))"

definition OAlist_tc_map_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::zero) oalist_tc \<Rightarrow> ('a::linorder, 'c::zero) oalist_tc"
  where "OAlist_tc_map_val f xs = OAlist_tc (map_val_pair f (list_of_oalist_tc xs))"

definition OAlist_tc_map2_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, 'b::zero) oalist_tc \<Rightarrow> ('a, 'c::zero) oalist_tc \<Rightarrow>
                                    ('a::linorder, 'd::zero) oalist_tc"
  where "OAlist_tc_map2_val f xs ys =
            OAlist_tc (map2_val_pair_tc f (map_val_pair (\<lambda>k b. f k b 0)) (map_val_pair (\<lambda>k. f k 0))
              (list_of_oalist_tc xs) (list_of_oalist_tc ys))"

definition OAlist_tc_map2_val_rneutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> ('a, 'c::zero) oalist_tc \<Rightarrow>
                                    ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_map2_val_rneutr f xs ys =
            OAlist_tc (map2_val_pair_tc f id (map_val_pair (\<lambda>k. f k 0)) (list_of_oalist_tc xs) (list_of_oalist_tc ys))"

definition OAlist_tc_map2_val_neutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow>
                                          ('a, 'b) oalist_tc \<Rightarrow> ('a::linorder, 'b::zero) oalist_tc"
  where "OAlist_tc_map2_val_neutr f xs ys = OAlist_tc (map2_val_pair_tc f id id (list_of_oalist_tc xs) (list_of_oalist_tc ys))"

definition OAlist_tc_lex_ord :: "('a \<Rightarrow> ('b, 'c) comp_opt) \<Rightarrow> (('a, 'b::zero) oalist_tc, ('a::linorder, 'c::zero) oalist_tc) comp_opt"
  where "OAlist_tc_lex_ord f xs ys = lex_ord_pair_tc f (list_of_oalist_tc xs) (list_of_oalist_tc ys)"

definition OAlist_tc_prod_ord :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b::zero) oalist_tc \<Rightarrow> ('a::linorder, 'c::zero) oalist_tc \<Rightarrow> bool"
  where "OAlist_tc_prod_ord f xs ys = prod_ord_pair_tc f (list_of_oalist_tc xs) (list_of_oalist_tc ys)"

subsubsection \<open>@{const OAlist_tc_lookup}\<close>

lemma OAlist_tc_lookup_eq_valueI: "(k, v) \<in> set (list_of_oalist_tc xs) \<Longrightarrow> OAlist_tc_lookup xs k = v"
  unfolding OAlist_tc_lookup_def using oalist_inv_list_of_oalist_tc by (rule tc.lookup_pair_eq_valueI)

lemma OAlist_tc_lookup_inj: "OAlist_tc_lookup xs = OAlist_tc_lookup ys \<Longrightarrow> xs = ys"
  by (simp add: OAlist_tc_lookup_def oalist_inv_list_of_oalist_tc oalist_tc_eqI tc.lookup_pair_inj)

lemma OAlist_tc_lookup_oalist_of_list:
  "distinct (map fst xs) \<Longrightarrow> OAlist_tc_lookup (oalist_tc_of_list xs) = lookup_dflt xs"
  by (simp add: OAlist_tc_lookup_def list_of_oalist_tc_of_list tc.lookup_pair_sort_oalist')

subsubsection \<open>@{const OAlist_tc_sorted_domain}\<close>

lemma set_OAlist_tc_sorted_domain: "set (OAlist_tc_sorted_domain xs) = fst ` set (list_of_oalist_tc xs)"
  unfolding OAlist_tc_sorted_domain_def by simp

lemma in_OAlist_tc_sorted_domain_iff_lookup: "k \<in> set (OAlist_tc_sorted_domain xs) \<longleftrightarrow> (OAlist_tc_lookup xs k \<noteq> 0)"
  unfolding OAlist_tc_sorted_domain_def OAlist_tc_lookup_def using oalist_inv_list_of_oalist_tc tc.lookup_pair_eq_0
  by fastforce

lemma sorted_OAlist_tc_sorted_domain: "sorted_wrt (<) (OAlist_tc_sorted_domain xs)"
  unfolding OAlist_tc_sorted_domain_def tc_le_lt[symmetric] using oalist_inv_list_of_oalist_tc
  by (rule tc.oalist_inv_rawD2)

subsubsection \<open>@{const OAlist_tc_empty} and Singletons\<close>

lemma list_of_oalist_OAlist_tc_empty [simp, code abstract]: "list_of_oalist_tc OAlist_tc_empty = []"
  unfolding OAlist_tc_empty_def using tc.oalist_inv_raw_Nil by (rule list_of_oalist_tc_of_list_id)

lemma lookup_OAlist_tc_empty: "OAlist_tc_lookup OAlist_tc_empty k = 0"
  by (simp add: OAlist_tc_lookup_def)

lemma OAlist_tc_lookup_single:
  "OAlist_tc_lookup (oalist_tc_of_list [(k, v)]) k' = (if k = k' then v else 0)"
  by (simp add: OAlist_tc_lookup_def list_of_oalist_tc_of_list tc.sort_oalist_def comparator_of_def split: order.split)

subsubsection \<open>@{const OAlist_tc_except_min}\<close>

lemma list_of_oalist_OAlist_tc_except_min [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_except_min xs) = tl (list_of_oalist_tc xs)"
  unfolding OAlist_tc_except_min_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_tl, fact oalist_inv_list_of_oalist_tc)

lemma lookup_OAlist_tc_except_min:
  "OAlist_tc_lookup (OAlist_tc_except_min xs) k =
        (if (\<forall>k'\<in>fst ` set (list_of_oalist_tc xs). k \<le> k') then 0 else OAlist_tc_lookup xs k)"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_tl oalist_inv_list_of_oalist_tc split del: if_split cong: if_cong)

subsubsection \<open>@{const OAlist_tc_min_key_val}\<close>

lemma OAlist_tc_min_key_val_in:
  assumes "list_of_oalist_tc xs \<noteq> []"
  shows "OAlist_tc_min_key_val xs \<in> set (list_of_oalist_tc xs)"
  unfolding OAlist_tc_min_key_val_def using assms by simp

lemma snd_OAlist_tc_min_key_val:
  assumes "list_of_oalist_tc xs \<noteq> []"
  shows "snd (OAlist_tc_min_key_val xs) = OAlist_tc_lookup xs (fst (OAlist_tc_min_key_val xs))"
proof -
  let ?xs = "list_of_oalist_tc xs"
  from assms have *: "OAlist_tc_min_key_val xs \<in> set ?xs" by (rule OAlist_tc_min_key_val_in)
  show ?thesis unfolding OAlist_tc_lookup_def
    by (rule HOL.sym, rule tc.lookup_pair_eq_valueI, fact oalist_inv_list_of_oalist_tc, simp add: *)
qed

lemma OAlist_tc_min_key_val_minimal:
  assumes "z \<in> set (list_of_oalist_tc xs)"
  shows "fst (OAlist_tc_min_key_val xs) \<le> fst z"
proof -
  let ?xs = "list_of_oalist_tc xs"
  from assms have "?xs \<noteq> []" by auto
  hence "OAlist_tc_sorted_domain xs \<noteq> []" by (simp add: OAlist_tc_sorted_domain_def)
  then obtain h xs' where eq: "OAlist_tc_sorted_domain xs = h # xs'" using list.exhaust by blast
  with sorted_OAlist_tc_sorted_domain[of xs] have *: "\<forall>y\<in>set xs'. h < y" by simp
  from assms have "fst z \<in> set (OAlist_tc_sorted_domain xs)" by (simp add: OAlist_tc_sorted_domain_def)
  hence disj: "fst z = h \<or> fst z \<in> set xs'" by (simp add: eq)
  from \<open>?xs \<noteq> []\<close> have "fst (OAlist_tc_min_key_val xs) = hd (OAlist_tc_sorted_domain xs)"
    by (simp add: OAlist_tc_min_key_val_def OAlist_tc_sorted_domain_def hd_map)
  also have "... = h" by (simp add: eq)
  also from disj have "... \<le> fst z"
  proof
    assume "fst z = h"
    thus ?thesis by simp
  next
    assume "fst z \<in> set xs'"
    with * have "h < fst z" ..
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

subsubsection \<open>@{const OAlist_tc_insert}\<close>

lemma list_of_oalist_OAlist_tc_insert [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_insert x xs) = update_by_pair_tc x (list_of_oalist_tc xs)"
  unfolding OAlist_tc_insert_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_update_by_pair, fact oalist_inv_list_of_oalist_tc)

lemma lookup_OAlist_tc_insert: "OAlist_tc_lookup (OAlist_tc_insert (k, v) xs) k' = (if k = k' then v else OAlist_tc_lookup xs k')"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_update_by_pair oalist_inv_list_of_oalist_tc split del: if_split cong: if_cong)

subsubsection \<open>@{const OAlist_tc_update_by_fun} and @{const OAlist_tc_update_by_fun_gr}\<close>

lemma list_of_oalist_OAlist_tc_update_by_fun [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_update_by_fun k f xs) = update_by_fun_pair_tc k f (list_of_oalist_tc xs)"
  unfolding OAlist_tc_update_by_fun_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_update_by_fun_pair, fact oalist_inv_list_of_oalist_tc)

lemma lookup_OAlist_tc_update_by_fun:
  "OAlist_tc_lookup (OAlist_tc_update_by_fun k f xs) k' = (if k = k' then f else id) (OAlist_tc_lookup xs k')"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_update_by_fun_pair oalist_inv_list_of_oalist_tc split del: if_split cong: if_cong)

lemma list_of_oalist_OAlist_tc_update_by_fun_gr [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_update_by_fun_gr k f xs) = update_by_fun_gr_pair_tc k f (list_of_oalist_tc xs)"
  unfolding OAlist_tc_update_by_fun_gr_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_update_by_fun_gr_pair, fact oalist_inv_list_of_oalist_tc)

lemma OAlist_tc_update_by_fun_gr_eq_OAlist_tc_update_by_fun: "OAlist_tc_update_by_fun_gr = OAlist_tc_update_by_fun"
  by (rule, rule, rule,
      simp add: OAlist_tc_update_by_fun_gr_def OAlist_tc_update_by_fun_def
                tc.update_by_fun_gr_pair_eq_update_by_fun_pair oalist_inv_list_of_oalist_tc)

subsubsection \<open>@{const OAlist_tc_filter}\<close>

lemma list_of_oalist_OAlist_tc_filter [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_filter P xs) = filter P (list_of_oalist_tc xs)"
  unfolding OAlist_tc_filter_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_filter, fact oalist_inv_list_of_oalist_tc)

lemma lookup_OAlist_tc_filter: "OAlist_tc_lookup (OAlist_tc_filter P xs) k = (let v = OAlist_tc_lookup xs k in if P (k, v) then v else 0)"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_filter oalist_inv_list_of_oalist_tc)

subsubsection \<open>@{const OAlist_tc_map_val}\<close>

lemma list_of_oalist_OAlist_tc_map_val [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_map_val f xs) = map_val_pair f (list_of_oalist_tc xs)"
  unfolding OAlist_tc_map_val_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_map_val_pair, fact oalist_inv_list_of_oalist_tc)

lemma OAlist_tc_map_val_cong:
  assumes "\<And>k v. (k, v) \<in> set (list_of_oalist_tc xs) \<Longrightarrow> f k v = g k v"
  shows "OAlist_tc_map_val f xs = OAlist_tc_map_val g xs"
  unfolding OAlist_tc_map_val_def by (rule arg_cong[where f=OAlist_tc], rule tc.map_val_pair_cong, elim assms)

lemma lookup_OAlist_tc_map_val: "f k 0 = 0 \<Longrightarrow> OAlist_tc_lookup (OAlist_tc_map_val f xs) k = f k (OAlist_tc_lookup xs k)"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_map_val_pair oalist_inv_list_of_oalist_tc)

subsubsection \<open>@{const OAlist_tc_map2_val} @{const OAlist_tc_map2_val_rneutr} and @{const OAlist_tc_map2_val_neutr}\<close>

lemma list_of_oalist_map2_val [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_map2_val f xs ys) =
      map2_val_pair_tc f (map_val_pair (\<lambda>k b. f k b 0)) (map_val_pair (\<lambda>k. f k 0)) (list_of_oalist_tc xs) (list_of_oalist_tc ys)"
  unfolding OAlist_tc_map2_val_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_map2_val_pair,
      fact oalist_inv_list_of_oalist_tc, fact oalist_inv_list_of_oalist_tc,
      fact tc.map2_val_compat_map_val_pair, fact tc.map2_val_compat_map_val_pair)

lemma list_of_oalist_OAlist_tc_map2_val_rneutr [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_map2_val_rneutr f xs ys) =
      map2_val_pair_tc f id (map_val_pair (\<lambda>k c. f k 0 c)) (list_of_oalist_tc xs) (list_of_oalist_tc ys)"
  unfolding OAlist_tc_map2_val_rneutr_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_map2_val_pair,
      fact oalist_inv_list_of_oalist_tc, fact oalist_inv_list_of_oalist_tc,
      fact tc.map2_val_compat_id, fact tc.map2_val_compat_map_val_pair)

lemma list_of_oalist_OAlist_tc_map2_val_neutr [simp, code abstract]:
  "list_of_oalist_tc (OAlist_tc_map2_val_neutr f xs ys) = map2_val_pair_tc f id id (list_of_oalist_tc xs) (list_of_oalist_tc ys)"
  unfolding OAlist_tc_map2_val_neutr_def
  by (rule list_of_oalist_tc_of_list_id, rule tc.oalist_inv_raw_map2_val_pair,
      fact oalist_inv_list_of_oalist_tc, fact oalist_inv_list_of_oalist_tc,
      fact tc.map2_val_compat_id, fact tc.map2_val_compat_id)

lemma lookup_OAlist_tc_map2_val:
  assumes "\<And>k. f k 0 0 = 0"
  shows "OAlist_tc_lookup (OAlist_tc_map2_val f xs ys) k = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k)"
  by (simp add: OAlist_tc_lookup_def tc.lookup_pair_map2_val_pair
      tc.map2_val_compat_map_val_pair assms oalist_inv_list_of_oalist_tc)

lemma lookup_OAlist_tc_map2_val_rneutr:
  assumes "\<And>k x. f k x 0 = x"
  shows "OAlist_tc_lookup (OAlist_tc_map2_val_rneutr f xs ys) k = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k)"
proof (simp add: OAlist_tc_lookup_def, rule tc.lookup_pair_map2_val_pair)
  fix zs::"('a \<times> 'b) list"
  assume "tc.oalist_inv_raw zs"
  thus "id zs = map_val_pair (\<lambda>k v. f k v 0) zs" by (simp add: assms tc.map_pair_id)
qed (fact oalist_inv_list_of_oalist_tc, fact oalist_inv_list_of_oalist_tc,
    fact tc.map2_val_compat_id, fact tc.map2_val_compat_map_val_pair, rule refl, simp only: assms)

lemma lookup_OAlist_tc_map2_val_neutr:
  assumes "\<And>k x. f k x 0 = x" and "\<And>k x. f k 0 x = x"
  shows "OAlist_tc_lookup (OAlist_tc_map2_val_neutr f xs ys) k = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k)"
proof (simp add: OAlist_tc_lookup_def, rule tc.lookup_pair_map2_val_pair)
  fix zs::"('a \<times> 'b) list"
  assume "tc.oalist_inv_raw zs"
  thus "id zs = map_val_pair (\<lambda>k v. f k v 0) zs" by (simp add: assms(1) tc.map_pair_id)
next
  fix zs::"('a \<times> 'b) list"
  assume "tc.oalist_inv_raw zs"
  thus "id zs = map_val_pair (\<lambda>k. f k 0) zs" by (simp add: assms(2) tc.map_pair_id)
qed (fact oalist_inv_list_of_oalist_tc, fact oalist_inv_list_of_oalist_tc,
    fact tc.map2_val_compat_id, fact tc.map2_val_compat_id, simp only: assms(1))

lemma OAlist_tc_map2_val_rneutr_singleton_eq_OAlist_tc_update_by_fun:
  assumes "\<And>a x. f a x 0 = x" and "list_of_oalist_tc ys = [(k, v)]"
  shows "OAlist_tc_map2_val_rneutr f xs ys = OAlist_tc_update_by_fun k (\<lambda>x. f k x v) xs"
  by (simp add: OAlist_tc_map2_val_rneutr_def OAlist_tc_update_by_fun_def assms
      tc.map2_val_pair_singleton_eq_update_by_fun_pair oalist_inv_list_of_oalist_tc)

subsubsection \<open>@{const OAlist_tc_lex_ord} and @{const OAlist_tc_prod_ord}\<close>

lemma OAlist_tc_lex_ord_EqI:
  "(\<And>k. k \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
     f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k) = Some Eq) \<Longrightarrow>
  OAlist_tc_lex_ord f xs ys = Some Eq"
  by (simp add: OAlist_tc_lex_ord_def OAlist_tc_lookup_def, rule tc.lex_ord_pair_EqI,
      rule oalist_inv_list_of_oalist_tc, rule oalist_inv_list_of_oalist_tc, blast)

lemma OAlist_tc_lex_ord_valI:
  assumes "aux \<noteq> Some Eq" and "k \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)"
  shows "aux = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k) \<Longrightarrow>
         (\<And>k'. k' \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
              k' < k \<Longrightarrow> f k' (OAlist_tc_lookup xs k') (OAlist_tc_lookup ys k') = Some Eq) \<Longrightarrow>
          OAlist_tc_lex_ord f xs ys = aux"
  by (simp (no_asm_use) add: OAlist_tc_lex_ord_def OAlist_tc_lookup_def, rule tc.lex_ord_pair_valI,
      rule oalist_inv_list_of_oalist_tc, rule oalist_inv_list_of_oalist_tc, rule assms(1), rule assms(2), simp_all)

lemma OAlist_tc_lex_ord_EqD:
  "OAlist_tc_lex_ord f xs ys = Some Eq \<Longrightarrow>
   k \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
   f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k) = Some Eq"
  by (simp add: OAlist_tc_lex_ord_def OAlist_tc_lookup_def, rule tc.lex_ord_pair_EqD[where f=f],
      rule oalist_inv_list_of_oalist_tc, rule oalist_inv_list_of_oalist_tc, assumption, simp)

lemma OAlist_tc_lex_ord_valE:
  assumes "OAlist_tc_lex_ord f xs ys = aux" and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)"
    and "aux = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
            k' < k \<Longrightarrow> f k' (OAlist_tc_lookup xs k') (OAlist_tc_lookup ys k') = Some Eq"
proof -
  note oalist_inv_list_of_oalist_tc oalist_inv_list_of_oalist_tc
  moreover from assms(1) have "lex_ord_pair_tc f (list_of_oalist_tc xs) (list_of_oalist_tc ys) = aux"
    by (simp only: OAlist_tc_lex_ord_def)
  ultimately obtain k where 1: "k \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys)"
    and "aux = f k (lookup_pair_tc (list_of_oalist_tc xs) k) (lookup_pair_tc (list_of_oalist_tc ys) k)"
    and "\<And>k'. k' \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
            k' < k \<Longrightarrow>
            f k' (lookup_pair_tc (list_of_oalist_tc xs) k') (lookup_pair_tc (list_of_oalist_tc ys) k') = Some Eq"
    using assms(2) unfolding tc_le_lt[symmetric] by (rule tc.lex_ord_pair_valE, blast)
  from this(2, 3) have "aux = f k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys) \<Longrightarrow>
            k' < k \<Longrightarrow> f k' (OAlist_tc_lookup xs k') (OAlist_tc_lookup ys k') = Some Eq"
    by (simp_all only: OAlist_tc_lookup_def)
  with 1 show ?thesis ..
qed

lemma OAlist_tc_prod_ord_alt:
  "OAlist_tc_prod_ord P xs ys \<longleftrightarrow>
                  (\<forall>k\<in>fst ` set (list_of_oalist_tc xs) \<union> fst ` set (list_of_oalist_tc ys).
                      P k (OAlist_tc_lookup xs k) (OAlist_tc_lookup ys k))"
  by (simp add: OAlist_tc_prod_ord_def OAlist_tc_lookup_def tc.prod_ord_pair_alt oalist_inv_list_of_oalist_tc)

subsubsection \<open>Instance of @{class equal}\<close>

instantiation oalist_tc :: (linorder, zero) equal
begin

definition equal_oalist_tc :: "('a, 'b) oalist_tc \<Rightarrow> ('a, 'b) oalist_tc \<Rightarrow> bool"
  where "equal_oalist_tc xs ys = (list_of_oalist_tc xs = list_of_oalist_tc ys)"

instance by (intro_classes, simp add: equal_oalist_tc_def list_of_oalist_tc_inject)

end

subsection \<open>Experiment\<close>

lemma "oalist_tc_of_list [(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)] = oalist_tc_of_list [(0, 4), (1, 3)]"
  by eval

lemma "OAlist_tc_except_min (oalist_tc_of_list ([(1, 3), (0::nat, 4::nat), (0, 2), (1, 1)])) = oalist_tc_of_list [(1, 3)]"
  by eval

lemma "OAlist_tc_min_key_val (oalist_tc_of_list [(1, 3), (0::nat, 4::nat), (0, 2), (1, 1)]) = (0, 4)"
  by eval

lemma "OAlist_tc_lookup (oalist_tc_of_list [(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)]) 1 = 3"
  by eval

lemma "OAlist_tc_prod_ord (\<lambda>_. greater_eq)
                (oalist_tc_of_list [(1, 4), (0::nat, 4::nat), (1, 3), (0, 2), (3, 1)])
                (oalist_tc_of_list [(0, 4), (1, 3), (2, 2), (1, 1)]) = False"
  by eval

lemma "OAlist_tc_map2_val_rneutr (\<lambda>_. minus)
                (oalist_tc_of_list [(1, 4), (0::nat, 4::int), (1, 3), (0, 2), (3, 1)])
                (oalist_tc_of_list [(0, 4), (1, 3), (2, 2), (1, 1)]) =
             oalist_tc_of_list [(1, 1), (2, - 2), (3, 1)]"
  by eval

end (* theory *)
