(*<*)
theory SWA
  imports Main
begin
(*>*)

section \<open>Sliding Window Algorithm\<close>

datatype 'a tree =
  Leaf
| Node (l: nat) (r: nat) (val: "'a option") (lchild: "'a tree") (rchild: "'a tree")
where
  "l Leaf = 0"
| "r Leaf = 0"
| "val Leaf = None"
| "lchild Leaf = Leaf"
| "rchild Leaf = Leaf"

lemma neq_Leaf_if_l_gt0: "0 < l t \<Longrightarrow> t \<noteq> Leaf"
  by auto

primrec discharge :: "'a tree \<Rightarrow> 'a tree" where
  "discharge Leaf = Leaf"
| "discharge (Node i j _ t u) = Node i j None t u"

instantiation option :: (semigroup_add) semigroup_add begin

fun plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "plus_option None _ = None"
| "plus_option _ None = None"
| "plus_option (Some a) (Some b) = Some (a + b)"

instance proof
  fix a b c :: "'a option"
  show "a + b + c = a + (b + c)"
    by (induct a b rule: plus_option.induct; cases c)
      (auto simp: algebra_simps)
qed

end

fun combine :: "'a :: semigroup_add tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "combine t Leaf = t"
| "combine Leaf t = t"
| "combine t u = Node (l t) (r u) (val t + val u) (discharge t) u"

lemma combine_non_Leaves: "\<lbrakk>t \<noteq> Leaf; u \<noteq> Leaf\<rbrakk> \<Longrightarrow> combine t u = Node (l t) (r u) (val t + val u) (discharge t) u"
proof -
  assume assms: "t \<noteq> Leaf" "u \<noteq> Leaf"
  from assms have "combine t u = Node (l (Node (l t) (r t) (val t) (lchild t) (rchild t))) (r (Node (l u) (r u) (val u) (lchild u) (rchild u))) (val (Node (l t) (r t) (val t) (lchild t) (rchild t)) + val (Node (l u) (r u) (val u) (lchild u) (rchild u))) (discharge (Node (l t) (r t) (val t) (lchild t) (rchild t))) (Node (l u) (r u) (val u) (lchild u) (rchild u))"
    by (metis (no_types) combine.simps(3) tree.exhaust_sel)
  with assms show ?thesis
    by simp
qed

lemma r_combine_non_Leaves: "\<lbrakk>t \<noteq> Leaf; u \<noteq> Leaf\<rbrakk> \<Longrightarrow> r (combine t u) = r u"
  by (simp add: combine_non_Leaves)

type_synonym window = "nat \<times> nat"

definition window :: "'a list \<Rightarrow> window \<Rightarrow> bool" where
  "window as = (\<lambda>(l, r). 0 < l \<and> l \<le> r \<and> r \<le> length as)"

definition windows :: "'a list \<Rightarrow> window list \<Rightarrow> bool" where
  "windows as ws = ((\<forall>w \<in> set ws. window as w) \<and>
    sorted (map fst ws) \<and> sorted (map snd ws))"

function reusables :: "'a tree \<Rightarrow> window \<Rightarrow> 'a tree list" where
  "reusables t w = (if fst w > r t then [] else if fst w = l t then [t]
     else let v = lchild t; u = rchild t in if fst w \<ge> l u then
       reusables u w else u # reusables v w)"
  by auto
termination
  by (relation "measure (\<lambda>p. size (fst p))")
    (auto simp: lchild_def rchild_def split: tree.splits)

declare reusables.simps[simp del]

lemma reusables_Leaf[simp]: "0 < fst w \<Longrightarrow> reusables Leaf w = []"
  by (simp add: reusables.simps)

primrec well_shaped :: "'a tree \<Rightarrow> bool" where
  "well_shaped Leaf = True"
| "well_shaped (Node i j _ t u) = (i \<le> j \<and> (i = j \<longrightarrow> t = Leaf \<and> u = Leaf) \<and>
    (i < j \<longrightarrow> t \<noteq> Leaf \<and> u \<noteq> Leaf \<and> well_shaped t \<and> well_shaped u \<and>
      i = l t \<and> j = r u \<and> Suc (r t) = l u))"

lemma l_lchild_eq_l_if_well_shaped[simp]:
  "\<lbrakk>well_shaped t; l t < r t\<rbrakk> \<Longrightarrow> l (lchild t) = l t"
  by (induct t) auto

lemma r_rchild_eq_r_if_well_shaped[simp]:
  "\<lbrakk>well_shaped t; l t < r t\<rbrakk> \<Longrightarrow> r (rchild t) = r t"
  by (induct t) auto

lemma r_lchild_eq_l_rchild_if_well_shaped:
  "\<lbrakk>well_shaped t; l t < r t\<rbrakk> \<Longrightarrow> r (lchild t) = l (rchild t) - 1"
  by (induct t) auto

lemma r_lchild_le_r: "well_shaped t \<Longrightarrow> r (lchild t) \<le> r t"
proof (induct t)
  case (Node i j a t1 t2)
  then show ?case
    by auto
      (metis Suc_eq_plus1_left order.trans le_add2 tree.exhaust_sel well_shaped.simps(2))
qed simp

lemma well_shaped_lchild[simp]: "well_shaped t \<Longrightarrow> well_shaped (lchild t)"
  by (induct t) auto

lemma well_shaped_rchild[simp]: "well_shaped t \<Longrightarrow> well_shaped (rchild t)"
  by (induct t) auto

definition adjacent where
  "adjacent w ts = (Leaf \<notin> set ts \<and>
     list_all2 (\<lambda>t u. l t = Suc (r u)) (butlast ts) (tl ts) \<and>
     (ts = [] \<or> (l (last ts) = fst w \<and> r (hd ts) = snd w)))"

lemma adjacent_Nil[simp]: "adjacent w []"
  unfolding adjacent_def by simp

lemma adjacent_Cons: "adjacent w (t # ts) =
  (t \<noteq> Leaf \<and> r t = snd w \<and> (case ts of [] \<Rightarrow> l t = fst w
     | u # us \<Rightarrow> adjacent (fst w, r u) ts \<and> l t = Suc (r u)))"
  unfolding adjacent_def by (auto split: list.splits)

lemma adjacent_ConsI: "\<lbrakk>t \<noteq> Leaf; r t = snd w;
  (case ts of [] \<Rightarrow> l t = fst w
     | u # us \<Rightarrow> adjacent (fst w, r u) ts \<and> l t = Suc (r u))\<rbrakk> \<Longrightarrow> 
  adjacent w (t # ts)"
  by (simp add: adjacent_Cons)

lemma adjacent_singleton: "t \<noteq> Leaf \<Longrightarrow> adjacent (l t, r t) [t]"
  unfolding adjacent_def by simp

lemma append_Cons_eq_append_append: "xs @ y # ys = xs @ [y] @ ys"
  by simp

lemma list_all2_append_singletonI: "\<lbrakk>list_all2 P xs ys; P x y\<rbrakk> \<Longrightarrow> list_all2 P (xs @ [x]) (ys @ [y])"
  by (simp add: list_all2_appendI)

lemma list_all2_Cons_append_singletonI: "\<lbrakk>xs \<noteq> []; list_all2 P (x # butlast xs) ys; P (last xs) y\<rbrakk> \<Longrightarrow> list_all2 P (x # xs) (ys @ [y])"
  using list_all2_append_singletonI by fastforce

lemma adjacent_appendI: "\<lbrakk>0 < fst w; fst w \<le> snd w;
  (case us of [] \<Rightarrow> adjacent w ts
    | u # us' \<Rightarrow> adjacent (Suc (r u), snd w) ts \<and> adjacent (fst w, (case ts of [] \<Rightarrow> snd w | ts \<Rightarrow> r u)) (u # us'))\<rbrakk> \<Longrightarrow> 
  adjacent w (ts @ us)"
  unfolding adjacent_def butlast_append
  by (auto simp: intro: list_all2_Cons_append_singletonI
    list_all2_appendI[OF list_all2_Cons_append_singletonI, simplified] split: list.splits if_splits)

lemma adjacent_Cons_implies_adjacent: "adjacent (a, b) (t # ts) \<Longrightarrow> adjacent (a, l t - Suc 0) ts"
  by (cases ts) (simp_all add: adjacent_def)

lemma (in semigroup_add) fold_add_add: "fold (+) xs (x + y) = fold (+) xs x + y"
  by (induct xs arbitrary: x) (auto simp: add_assoc[symmetric])

context
  fixes as :: "'a :: semigroup_add list"
  and ws :: "window list"
begin

abbreviation atomic where
  "atomic i \<equiv> Node i i (Some (nth as (i - 1))) Leaf Leaf"

definition atomics :: "nat \<Rightarrow> nat \<Rightarrow> 'a tree list" where
  "atomics i j \<equiv> map atomic (rev [i ..< Suc j])"

definition slide :: "'a tree \<Rightarrow> window \<Rightarrow> 'a tree" where
  "slide t w =
    (let
      ts = atomics (max (fst w) (Suc (r t))) (snd w);
      ts' = reusables t w
    in fold combine (ts @ ts') Leaf)"

primrec iterate :: "'a tree \<Rightarrow> window list \<Rightarrow> 'a list" where
  "iterate t [] = []"
| "iterate t (w # xs) = (let t' = slide t w in the (val t') # iterate t' xs)"

definition sliding_window :: "'a list" where
  "sliding_window = iterate Leaf ws"


section \<open>Correctness\<close>

abbreviation sum where
  "sum i j \<equiv> fold (+) (rev (map (nth as) [i - 1 ..< j - 1])) (nth as (j - 1))"

primrec well_valued0 :: "'a tree \<Rightarrow> bool" where
  "well_valued0 Leaf = True"
| "well_valued0 (Node i j a t u) = (0 < i \<and> j \<le> length as \<and> (a \<noteq> None \<longrightarrow> a = Some (sum i j)) \<and>
    well_valued0 t \<and> well_valued0 u \<and> (u = Leaf \<or> val u \<noteq> None))"

abbreviation well_valued :: "'a tree \<Rightarrow> bool" where
  "well_valued t \<equiv> (well_valued0 t \<and> (t \<noteq> Leaf \<longrightarrow> val t \<noteq> None))"

definition valid :: "'a tree \<Rightarrow> bool" where
  "valid t = (well_shaped t \<and> well_valued t)"

lemma valid_Leaf: "valid Leaf"
  unfolding valid_def by auto

lemma add_sum:
  assumes "i > 0" "j \<ge> i" "k > j"
  shows "sum i j + sum (Suc j) k = sum i k"
proof -
  have *: "[i - 1 ..< k - 1] = [i - 1..< j] @ [j..< k - 1]"
    using assms upt_add_eq_append[of "i - 1" "j - 1" "k - j"]
    by (cases j) (auto simp: upt_conv_Cons)
  then show ?thesis using assms
    by (cases j) (auto simp: fold_add_add)
qed

lemma well_valued0_rchild_if_well_valued0[simp]: "well_valued0 t \<Longrightarrow> well_valued0 (rchild t)"
  by (induct t) auto

lemma well_valued0_lchild_if_well_valued0[simp]: "well_valued0 t \<Longrightarrow> well_valued0 (lchild t)"
  by (induct t) auto

lemma valid_rchild_if_valid: "valid t \<Longrightarrow> valid (rchild t)"
  by (metis tree.exhaust_sel tree.sel(9) valid_def well_shaped_rchild well_valued0.simps(2))

lemma val_eq_Some_sum_if_valid_neq_Leaf: "\<lbrakk>valid t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow> val t = Some (sum (l t) (r t))"
  by (auto simp: valid_def foldr_conv_fold)
    (metis One_nat_def option.distinct(1) option.inject tree.exhaust_sel well_valued0.simps(2))


subsection \<open>Correctness of the Slide Function\<close>

(* fact (b) part 1 *)
lemma adjacent_atomics: "adjacent (i, j) (atomics i j)"
  unfolding adjacent_def atomics_def
  by (auto 0 1 simp: last_map last_rev nth_tl
    map_butlast[symmetric] list_all2_conv_all_nth nth_Cons' rev_nth nth_append)

(* fact (b) part 2 *)
lemma valid_atomics: "\<lbrakk>t \<in> set (atomics i j); 0 < i; j \<le> length as\<rbrakk> \<Longrightarrow> valid t"
  unfolding atomics_def
  by (auto simp: valid_def)

lemma reusables_neq_Nil_if_well_shaped_and_overlapping:
  "\<lbrakk>well_shaped t; l t \<le> fst w; r t \<le> snd w; fst w \<le> r t\<rbrakk> \<Longrightarrow> reusables t w \<noteq> []"
  by (induction t w rule: reusables.induct) (simp add: reusables.simps Let_def)

lemma reusables_lchild_neq_Nil_under_some_conditions:
  "\<lbrakk>well_shaped t; l t \<le> fst w; r t \<le> snd w; fst w \<noteq> l t; r t \<ge> fst w; l (rchild t) > fst w\<rbrakk> \<Longrightarrow>
    reusables (lchild t) w \<noteq> []"
  using r_lchild_eq_l_rchild_if_well_shaped[of "t"] r_lchild_le_r[of t]
  by (intro reusables_neq_Nil_if_well_shaped_and_overlapping) auto

(* fact (a) part 1 *)
lemma adjacent_reusables: "\<lbrakk>0 < fst w; well_shaped t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
  adjacent (fst w, r t) (reusables t w)"
proof (induction t w rule: reusables.induct)
  case (1 t w)
  show ?case
  proof (cases "fst w > r t")
    case False
    with 1 show ?thesis
    proof (cases "fst w = l t")
      case False
      then show ?thesis
      proof (cases "fst w \<ge> l (rchild t)")
        case True
        with 1 \<open>fst w \<noteq> l t\<close> show ?thesis by (subst reusables.simps) auto
      next
        case False
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> obtain x xs where *: "reusables (lchild t) w = x # xs"
          by (cases "reusables (lchild t) w") (auto simp: reusables_lchild_neq_Nil_under_some_conditions)
        with 1(2-6) \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> \<open>\<not> l (rchild t) \<le> fst w\<close>
        have "adjacent (fst w, r (lchild t)) (x # xs)"
          by (simp add: adjacent_Cons r_lchild_le_r dual_order.trans)
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> * show ?thesis
          by (subst reusables.simps)
            (auto simp add: Let_def adjacent_Cons r_lchild_eq_l_rchild_if_well_shaped)
      qed
    qed (auto simp: reusables.simps intro!: adjacent_singleton)
  qed (auto simp: reusables.simps)
qed

lemma valid_rchild_if_well_valued0: "\<lbrakk>well_shaped t; well_valued0 t\<rbrakk> \<Longrightarrow> valid (rchild t)"
  by (metis tree.exhaust_sel tree.sel(9) valid_def well_shaped_rchild well_valued0.simps(2))

lemma valid_reusables_under_some_conditions:
  "\<lbrakk>0 < fst w; well_valued0 t; well_shaped t; l t < fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
    \<forall>t' \<in> set (reusables t w). valid t'"
proof (induction t w rule: reusables.induct)
  case (1 t w)
  show ?case
  proof (cases "fst w > r t")
    case False
    with 1 show ?thesis
    proof (cases "fst w = l t")
    next
      case False
      then show ?thesis
      proof (cases "fst w \<ge> l (rchild t)")
        case True
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> have *: "Ball (set (reusables (rchild t) w)) valid"
          by (metis (no_types, lifting) ball_empty dual_order.strict_trans2 leI le_neq_implies_less list.set(1) r_rchild_eq_r_if_well_shaped reusables.simps set_ConsD valid_rchild_if_well_valued0 well_shaped_rchild well_valued0_rchild_if_well_valued0)
        from 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> True have "reusables t w = reusables (rchild t) w"
          by (subst reusables.simps)
            simp
        with 1 * show ?thesis
          by simp
      next
        case False
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> have *: "Ball (set (reusables (lchild t) w)) valid"
          by (metis dual_order.strict_trans2 l_lchild_eq_l_if_well_shaped leI order_trans r_lchild_le_r well_shaped_lchild well_valued0_lchild_if_well_valued0)
        with 1 have valid_rchild: "valid (rchild t)"
          by (simp add: valid_rchild_if_well_valued0)
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> False have "reusables t w = rchild t # reusables (lchild t) w"
          by (subst reusables.simps) presburger
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> False * valid_rchild show ?thesis
          by (metis set_ConsD)
      qed
    qed (auto simp: reusables.simps)
  qed (auto simp: reusables.simps)
qed

(* fact (a) part 2 *)
lemma valid_reusables:
  assumes "0 < fst w" "valid t" "l t \<le> fst w" "r t \<le> snd w"
  shows "\<forall>t' \<in> set (reusables t w). valid t'"
proof (cases "l t < fst w")
  case True
  with assms show ?thesis
    using valid_def valid_reusables_under_some_conditions by blast
next
  case False
  with assms show ?thesis
    by (simp add: reusables.simps)
qed

lemma combine_valid_Nodes_aux:
  assumes prems: "0 < l a" "a \<noteq> Leaf" "z \<noteq> Leaf" "l z = Suc (r a)" "well_shaped a" "well_shaped z"
    "well_valued0 a" "val a = Some va" "well_valued0 z" "val z = Some vz"
  shows "va + vz = fold (+) (rev (map ((!) as) [l a - Suc 0..<r z - Suc 0])) (as ! (r z - Suc 0))"
proof -
  from prems have "l a > 0" by simp
  moreover from prems have "r a \<ge> l a"
    by (metis tree.collapse well_shaped.simps(2))
  moreover have "r z > r a"
    by (metis Suc_le_lessD prems(3) prems(4) prems(6) tree.collapse well_shaped.simps(2))
  ultimately have *: "sum (l a) (r a) + sum (Suc (r a)) (r z) = sum (l a) (r z)"
    by (frule add_sum)
  from prems have "va = sum (l a) (r a)"
    by (metis option.discI option.inject tree.collapse well_valued0.simps(2))
  moreover from prems have "vz = sum (Suc (r a)) (r z)"
    by (metis option.discI option.inject prems(2) prems(3) prems(8) prems(9) tree.collapse well_valued0.simps(2))
  moreover have "fold (+) (rev (map ((!) as) [l a - Suc 0..<r z - Suc 0])) (as ! (r z - Suc 0)) = sum (l a) (r z)"
    by simp
  ultimately show ?thesis
    using * by (auto simp: add_sum)
qed

lemma discharge_is_Leaf[simp]: "discharge a = Leaf \<longleftrightarrow> a = Leaf"
  by (cases a) auto

lemma well_shaped_discharge[simp]: "well_shaped a \<Longrightarrow> well_shaped (discharge a)"
  by (cases a) auto

lemma well_valued0_discharge[simp]: "well_valued0 a \<Longrightarrow> well_valued0 (discharge a)"
  by (cases a) auto

lemma l_discharge[simp]: "l (discharge a) = l a"
  by (cases a) auto

lemma r_discharge[simp]: "r (discharge a) = r a"
  by (cases a) auto

lemma well_shaped_lr: "well_shaped a \<Longrightarrow> l a \<le> r a"
  by (cases a) auto

lemma well_valued0_r: "well_valued0 a \<Longrightarrow> a \<noteq> Leaf \<Longrightarrow> r a \<le> length as"
  by (cases a) auto

lemma valid_combine_if_valid: "\<lbrakk>0 < l a; valid a; valid z; a \<noteq> Leaf; z \<noteq> Leaf; l z = Suc (r a)\<rbrakk> \<Longrightarrow>
  valid (combine a z)"
  by (force simp add: valid_def combine_non_Leaves combine_valid_Nodes_aux
    dest: well_shaped_lr well_valued0_r)

lemma combine_neq_Leaf_if_both_non_Leaf: "\<lbrakk>a \<noteq> Leaf; z \<noteq> Leaf\<rbrakk> \<Longrightarrow>
  combine a z \<noteq> Leaf"
  by (simp add: combine_non_Leaves)

(* generalized version of fact (c) *)
lemma valid_fold_combine: "\<lbrakk>0 < fst w; ts = h # ts'; \<forall>t \<in> set ts. valid t; adjacent (fst w, l h - 1) ts';
    valid z; z \<noteq> Leaf; l z = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1)); r z = snd w\<rbrakk> \<Longrightarrow>
      valid (fold combine ts' z) \<and>
      l (fold combine ts' z) = fst w \<and> r (fold combine ts' z) = snd w"
proof (induction ts' arbitrary: z ts h)
  case Nil
  then show ?case by simp
next
  case (Cons a ts')
  moreover from Cons(3-4) have "valid a" by simp
  moreover from Cons(5) have "adjacent (fst w, l a - Suc 0) ts'"
    unfolding adjacent_Cons by (auto split: list.splits)
  moreover from Cons(2-6,8) have "valid (combine a z)"
    unfolding adjacent_Cons
    by (intro valid_combine_if_valid) (auto split: list.splits)
  moreover from Cons(5,7) have "combine a z \<noteq> Leaf" 
    by (intro combine_neq_Leaf_if_both_non_Leaf) (simp_all add: adjacent_Cons)
  moreover from Cons(5,7) have "l (combine a z) = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1))"
    by (auto simp add: adjacent_def combine_non_Leaves split: list.splits)
  moreover from Cons(5,7,9) have "r (combine a z) = snd w" 
    by (subst r_combine_non_Leaves) (auto simp add: adjacent_def)
  ultimately show ?case
    by simp
qed

(* fact (c) *)
lemma valid_fold_combine_Leaf: 
  assumes "0 < fst w" "ts = h # ts'" "\<forall>t \<in> set ts. valid t" "adjacent w ts"
  shows "valid (fold combine ts Leaf) \<and>
  l (fold combine ts Leaf) = fst w \<and> r (fold combine ts Leaf) = snd w"
proof -
  from assms(2) have "fold combine ts Leaf = fold combine ts' h"
    by simp
  moreover have "valid (fold combine ts' h) \<and>
    l (fold combine ts' h) = fst w \<and> r (fold combine ts' h) = snd w"
  proof (rule valid_fold_combine)
    from assms show "0 < fst w" "ts = h # ts'" "\<forall>t \<in> set ts. valid t" "valid h" "h \<noteq> Leaf" "r h = snd w"
      "l h = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1))"
      by (simp_all add: adjacent_Cons list.case_eq_if)
    from assms show "adjacent (fst w, l h - 1) ts'"
      by (metis One_nat_def adjacent_Cons_implies_adjacent prod.collapse)
  qed
  ultimately show ?thesis by simp
qed

lemma adjacent_atomics_nonempty_reusables:
  fixes x :: "'a tree" and xs :: "'a tree list"
  assumes a1: "0 < fst w"
      and a2: "l t \<le> fst w"
      and a3: "r t \<le> snd w"
      and a4: "valid t"
      and a5: "reusables t w = x # xs"
  shows "adjacent (Suc (r x), snd w) (atomics (max (fst w) (Suc (r t))) (snd w))" 
proof -
  have f6: "\<forall>p ts. adjacent p ts = ((Leaf::'a tree) \<notin> set ts \<and> list_all2 (\<lambda>t ta. l t = Suc (r ta)) (butlast ts) (tl ts) \<and> (ts = [] \<or> l (last ts) = fst p \<and> r (hd ts) = snd p))"
    using adjacent_def by blast
  then have f7: "Leaf \<notin> set (atomics (max (fst w) (Suc (r t))) (snd w)) \<and> list_all2 (\<lambda>t ta. l t = Suc (r ta)) (butlast (atomics (max (fst w) (Suc (r t))) (snd w))) (tl (atomics (max (fst w) (Suc (r t))) (snd w))) \<and> (atomics (max (fst w) (Suc (r t))) (snd w) = [] \<or> l (last (atomics (max (fst w) (Suc (r t))) (snd w))) = fst (max (fst w) (Suc (r t)), snd w) \<and> r (hd (atomics (max (fst w) (Suc (r t))) (snd w))) = snd (max (fst w) (Suc (r t)), snd w))"
    using adjacent_atomics by presburger
  have "adjacent (fst w, r t) (reusables t w)"
    using a4 a3 a2 a1 by (simp add: adjacent_reusables valid_def)
  then have f8: "r x = r t"
    using a5 by (simp add: adjacent_Cons)
  have "max (fst w) (Suc (r t)) = Suc (r t)"
    using a5 by (metis (no_types) Suc_n_not_le_n list.simps(3) max.bounded_iff max_def_raw not_le_imp_less reusables.simps)
  then show ?thesis
    using f8 f7 f6 by presburger
qed

lemma adjacent_Cons_r: "adjacent (a, r t) (x # xs) \<Longrightarrow> adjacent (a, r x) (x # xs)"
  by (simp add: adjacent_Cons)

lemma adjacent_Cons_r2:
  "adjacent (fst w, r t) (x # xs) \<Longrightarrow> 0 < fst w \<Longrightarrow> fst w \<le> snd w \<Longrightarrow> r t \<le> snd w \<Longrightarrow>
   atomics (max (fst w) (Suc (r t))) (snd w) = [] \<Longrightarrow>
   adjacent w (x # xs)"
  by (metis (no_types, lifting) atomics_def adjacent_def append_is_Nil_conv diff_Suc_Suc diff_zero le_Suc_eq list.simps(3) map_is_Nil_conv max_Suc_Suc max_def_raw prod.sel(1) prod.sel(2) rev_is_Nil_conv upt.simps(2))

lemma adjacent_append_atomics_reusables:
  "\<lbrakk>0 < fst w; fst w \<le> snd w; valid t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
    adjacent w (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w)"
  using adjacent_atomics_nonempty_reusables[of w t] reusables_neq_Nil_if_well_shaped_and_overlapping[of t w]
    adjacent_atomics[of "fst w" "snd w"] adjacent_reusables[of w t]
  by (intro adjacent_appendI) (auto simp: valid_def max.absorb1 atomize_not
    elim: adjacent_Cons_r adjacent_Cons_r2 split: list.splits nat.splits)

lemma valid_append_atomics_reusables: "\<lbrakk>0 < fst w; valid t; l t \<le> fst w; r t \<le> snd w; snd w \<le> length as\<rbrakk> \<Longrightarrow>
  \<forall>t \<in> set (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w). valid t"
  by (auto simp only: set_append valid_reusables dest: valid_atomics split: if_splits)

lemma append_atomics_reusables_neq_Nil: "\<lbrakk>0 < fst w; fst w \<le> snd w; valid t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
  atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w \<noteq> []"
  by (simp add: reusables_neq_Nil_if_well_shaped_and_overlapping valid_def atomics_def)

(* lemma 1 *)
lemma valid_slide:
  assumes "0 < fst w" "fst w \<le> snd w" "valid t" "l t \<le> fst w" "r t \<le> snd w" "snd w \<le> length as"
  shows "valid (slide t w) \<and> l (slide t w) = fst w \<and> r (slide t w) = snd w"
proof -
  from assms have non_empty: "atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w \<noteq> []"
    using append_atomics_reusables_neq_Nil by blast
  from assms have adjacent: "adjacent w (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w)"
    using adjacent_append_atomics_reusables by blast
  from assms have valid: "\<forall>t \<in> set (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w). valid t"
    using valid_append_atomics_reusables by blast
  have *: "slide t w = fold combine (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w) Leaf"
    by (simp add: slide_def)
  from assms(1) non_empty adjacent valid show "valid (slide t w) \<and> l (slide t w) = fst w \<and> r (slide t w) = snd w"
    unfolding * neq_Nil_conv using valid_fold_combine_Leaf by blast
qed


subsection \<open>Correctness of the Sliding Window Algorithm\<close>

lemma iterate_eq_map_sum: "\<lbrakk>valid t; windows as xs; (case xs of [] \<Rightarrow> True | x # xs' \<Rightarrow> l t \<le> fst x \<and> r t \<le> snd x)\<rbrakk> \<Longrightarrow>
  iterate t xs = map (\<lambda>w. sum (fst w) (snd w)) xs"
  by (induction xs arbitrary: t)
    (auto simp: valid_slide windows_def window_def val_eq_Some_sum_if_valid_neq_Leaf neq_Leaf_if_l_gt0 split: list.split)

(* theorem 2: functional correctness *)
theorem correctness: "windows as ws \<Longrightarrow> sliding_window = map (\<lambda>w. sum (fst w) (snd w)) ws"
  by (auto simp only: sliding_window_def intro!: iterate_eq_map_sum)
    (auto simp: valid_def split: list.split)

end

(*<*)
value[code] "sliding_window [2,4,5,2 :: nat] [(1, 3), (1, 4), (2, 4)]"
value[code] "slide [2,4,5,2 :: nat] Leaf (1, 3)"
(*>*)


subsection \<open>Summary of the Correctness Proof\<close>

text \<open>We closely follow Basin et al.'s proof outline~\cite{BASIN2015186}.
  \begin{enumerate}
    \item Lemma 1, the correctness result about the function @{term SWA.slide}, is formalized 
      by @{thm[source] SWA.valid_slide}. It follows from the following auxiliary facts:
      \begin{itemize}
        \item Fact (a) is formalized by @{thm[source] SWA.adjacent_reusables} and @{thm[source] SWA.valid_reusables}.
        \item Fact (b) is formalized by @{thm[source] SWA.adjacent_atomics} and @{thm[source] SWA.valid_atomics}.
        \item Fact (c) is formalized by @{thm[source] SWA.valid_fold_combine_Leaf}.
      \end{itemize}
    \item Theorem 2, the correctness result about the function @{term SWA.sliding_window}, is formalized
      by @{thm[source] SWA.correctness}.
  \end{enumerate}
\<close>


section \<open>Alternative Slide Interface and Additional Operations\<close>

subsection \<open>Alternative Slide Interface\<close>

text \<open>
  The slide operation above takes the \emph{entire} input sequence as a parameter. This is often
  impractical. We provide an alternative interface to the slide operation that takes only the
  \emph{new} elements as a parameter.
\<close>

abbreviation atomic' where
  "atomic' as b idx \<equiv> Node b b (Some (nth as idx)) Leaf Leaf"

abbreviation atomics' :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree list" where
  "atomics' as i j sidx \<equiv> map (\<lambda>b. atomic' as b (b - sidx)) (rev [i ..< Suc j])"

definition slide' :: "'a :: semigroup_add list \<Rightarrow> 'a tree \<Rightarrow> window \<Rightarrow> 'a tree" where
"slide' as t w =
    (let
      ts = atomics' as (max (fst w) (Suc (r t))) (snd w) (Suc (r t));
      ts' = reusables t w
    in fold combine (ts @ ts') Leaf)"

(* examples from paper *)
(*<*)
value[code] "slide' [2,4,5,2 :: nat] Leaf (1, 3)"
value[code] "slide' [2,4,5,2 :: nat] Leaf (1, 4)"
value[code] "slide' [2,4,5,2 :: nat] Leaf (2, 4)"
value[code] "slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (1, 4)"
value[code] "slide' [] (slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (1, 4)) (2, 4)"
value[code] "slide' [2,4,5 :: nat] Leaf (1, 3)"
value[code] "slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (2, 4)"
(*>*)

lemma slide_eq_slide':
  assumes "0 < fst w" "fst w \<le> snd w" "valid as t" "r t = length as" "l t \<le> fst w" "r t \<le> snd w" "snd w \<le> length (as @ as')"
  shows "slide (as @ as') t w = slide' as' t w"
proof (cases "r t = snd w")
  case True
  with assms have *: "atomics' (as @ as') (max (fst w) (Suc (r t))) (snd w) 1 = []"
    by simp
  from True assms have "atomics' as' (max (fst w) (Suc (r t))) (snd w) (Suc (r t)) = []"
    by simp
  with * show ?thesis
    unfolding slide_def slide'_def atomics_def by simp
next
  case False
  with assms have "r t < snd w"
    by simp
  with assms have "atomic' (as @ as') (snd w) (snd w - Suc 0) = atomic' as' (snd w) (snd w - Suc (length as))"
    by (simp add: leD nth_append)
  with assms have *: "\<forall>i. i \<in> set ([max (fst w) (Suc (length as))..<snd w]) \<longrightarrow> atomic' (as @ as') i (i - Suc 0) = atomic' as' i (i - Suc (length as))"
    by (auto simp: nth_append)
  then have "map (\<lambda>i. atomic' (as @ as') i (i - Suc 0)) (rev [max (fst w) (Suc (length as))..<snd w]) = map (\<lambda>b. atomic' as' b (b - Suc (r t))) (rev [max (fst w) (Suc (r t))..<snd w])"
    by (simp add: assms(4))
  with assms have "atomics' (as @ as') (max (fst w) (Suc (r t))) (snd w) 1 = atomics' as' (max (fst w) (Suc (r t))) (snd w) (Suc (r t))"
    by (auto simp: nth_append)
  then show ?thesis
    unfolding slide_def slide'_def atomics_def
    by presburger
qed

lemma sum_eq_sum_append: "\<lbrakk>0 < i; i \<le> j; j \<le> length as\<rbrakk> \<Longrightarrow> sum as i j = sum (as @ as') i j"
proof -
  assume assms: "0 < i" "i \<le> j" "j \<le> length as"
  then have *: "rev (map ((!) as) [i - Suc 0..<j - Suc 0]) = rev (map ((!) (as@as')) [i - Suc 0..<j - Suc 0])"
    by (auto simp: nth_append)
  from assms have "as ! (j - Suc 0) = (as @ as') ! (j - Suc 0)"
    by (auto simp: nth_append)
  then show ?thesis
    by (simp add: *)
qed

lemma well_valued0_append: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow> well_valued0 (as @ as') t"
proof (induction t)
  case (Node i j a t1 t2)
  then show ?case
    using sum_eq_sum_append
    by (auto 4 0)
qed simp

lemma valid_append: "valid as t \<Longrightarrow> valid (as @ as') t"
  unfolding valid_def
  by (auto intro: well_valued0_append)

lemma valid_slide_append: "\<lbrakk>0 < fst w; fst w \<le> snd w; valid as t; l t \<le> fst w; r t \<le> snd w; snd w \<le> length as + length as'\<rbrakk> \<Longrightarrow>
  valid (as @ as') (slide (as @ as') t w) \<and> l (slide (as @ as') t w) = fst w \<and> r (slide (as @ as') t w) = snd w"
  by (auto simp: valid_append valid_slide)

(* correctness of alternative slide interface *)
theorem valid_slide':
  assumes "0 < fst w" "fst w \<le> snd w" "valid as t" "length as = r t" "length as' \<ge> snd w - r t" "l t \<le> fst w" "r t \<le> snd w"
  shows "valid (as @ as') (slide' as' t w) \<and> l (slide' as' t w) = fst w \<and> r (slide' as' t w) = snd w"
proof -
  from assms have "valid (as @ as') (slide (as @ as') t w) \<and> l (slide (as @ as') t w) = fst w \<and> r (slide (as @ as') t w) = snd w"
    using valid_slide_append by (metis add_le_cancel_left le_add_diff_inverse)
  with assms show ?thesis
    using slide_eq_slide' by (metis add_le_cancel_left le_add_diff_inverse length_append)
qed


subsection \<open>Updating all Values in the Tree\<close>

text \<open>
  So far, we have assumed that the sequence is fixed. However, under certain conditions,
  SWA can be applied even if the sequence changes. In particular, if a function that distributes
  over the associative operation is mapped onto the sequence, validity of the tree can be preserved
  by mapping the same function onto the tree using @{term map_tree}.
\<close>

lemma map_tree_eq_Leaf_iff: "map_tree f t = Leaf \<longleftrightarrow> t = Leaf"
  by simp

lemma l_map_tree_eq_l[simp]: "l (map_tree f t) = l t"
  by (cases t)
    (auto split: option.splits)

lemma r_map_tree_eq_r[simp]: "r (map_tree f t) = r t"
  by (cases t)
    (auto split: option.splits)

lemma val_map_tree_neq_None: "val t \<noteq> None \<Longrightarrow> val (map_tree f t) \<noteq> None"
  by (cases t) auto

lemma well_shaped_map_tree: "well_shaped t \<Longrightarrow> well_shaped (map_tree f t)"
  by (induction t)
    (auto split: option.split)

lemma fold_distr: "(\<forall>x y. f (x + y) = f x + f y) \<Longrightarrow> f (fold (+) list e) = fold (+) (map f list) (f e)"
  by (induction list arbitrary: e) auto

lemma map_rev_map_nth_eq: "\<forall>x \<in> set xs. x < length as \<Longrightarrow> map f (rev (map ((!) as) xs)) = rev (map ((!) (map f as)) xs)"
  by (simp add: rev_map)

lemma f_nth_eq_map_f_nth: "\<lbrakk>as \<noteq> []; length as \<ge> n\<rbrakk> \<Longrightarrow> f (as ! (n - Suc 0)) = map f as ! (n - Suc 0)"
  by (cases "n = length as") auto

lemma well_valued0_map_map_tree:
   "\<lbrakk>\<forall>x y. f (x + y) = f x + f y; well_shaped t; well_valued0 as t; r t \<le> length as; as \<noteq> []\<rbrakk> \<Longrightarrow>
     well_shaped (map_tree f t) \<and> well_valued0 (map f as) (map_tree f t)"
proof (rule conjI[OF well_shaped_map_tree], assumption, induction t)
  case (Node i j a t1 t2)
  then have "map f (rev (map ((!) as) [l t1 - Suc 0..<r t2 - Suc 0])) =
    rev (map ((!) (map f as)) [l t1 - Suc 0..<r t2 - Suc 0])"
    by (subst map_rev_map_nth_eq) auto
  moreover from Node have "r t1 \<le> length as"
    by (cases t1) auto
  ultimately show ?case using Node(3-7)
    by (auto simp: fold_distr[of f] val_map_tree_neq_None
      well_shaped_map_tree intro!: Node(1,2))
qed simp

lemma valid_map_map_tree:
  assumes "\<forall>x y. f (x + y) = f x + f y" "valid as t" "r t \<le> length as"
  shows "valid (map f as) (map_tree f t)"
proof (cases "as \<noteq> []")
  case True
  with assms show ?thesis
    by (metis map_tree_eq_Leaf_iff val_map_tree_neq_None valid_def well_valued0_map_map_tree)
next
  case False
  with assms show ?thesis
    by (metis le_zero_eq list.size(3) tree.exhaust_sel map_tree_eq_Leaf_iff valid_Leaf valid_def well_shaped.simps(2) well_valued0.simps(2))
qed

lemma valid_Nil_iff: "valid [] t \<longleftrightarrow> t = Leaf"
  unfolding valid_def
proof
  assume "well_shaped t \<and> well_valued [] t"
  then show "t = Leaf"
    by (metis le_neq_implies_less list.size(3) not_less_zero tree.collapse well_shaped.simps(2) well_valued0.simps(2))
qed simp


subsection \<open>Updating the Rightmost Leaf of the Tree\<close>

text \<open>
  We provide a function to update the rightmost leaf of the tree. This may be used in an online
  setting where the input sequence is not known in advance to update the latest observed element
  using the same associative operation used in SWA. We show that validity of the tree is preserved
  in this case.
\<close>

fun update_rightmost :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "update_rightmost _ Leaf = Leaf"
| "update_rightmost f (Node i j a t u) = Node i j (map_option f a) t (update_rightmost f u)"

lemma update_rightmost_eq_Leaf_iff: "update_rightmost f t = Leaf \<longleftrightarrow> t = Leaf"
  by (cases t)
    (auto split: option.splits)

lemma l_update_rightmost_eq_l[simp]: "l (update_rightmost f t) = l t"
  by (cases t)
    (auto split: option.splits)

lemma r_update_rightmost_eq_r[simp]: "r (update_rightmost f t) = r t"
  by (cases t)
    (auto split: option.splits)

lemma val_update_rightmost_neq_None: "val t \<noteq> None \<Longrightarrow> val (update_rightmost f t) \<noteq> None"
  by (cases t) auto

lemma well_shaped_update_rightmost: "well_shaped t \<Longrightarrow> well_shaped (update_rightmost f t)"
  by (induction t)
    (auto simp: update_rightmost_eq_Leaf_iff split: option.split)

lemma sum_eq_sum_prepend: "\<lbrakk>0 < i; i \<le> j; length xs < i; length ys = length xs\<rbrakk> \<Longrightarrow> sum (xs @ as) i j = sum (ys @ as) i j"
proof -
  assume assms: "0 < i" "i \<le> j" "length xs < i" "length ys = length xs"
  then have *: "rev (map ((!) (xs @ as)) [i - Suc 0..<j - Suc 0]) = rev (map ((!) (ys @ as)) [i - Suc 0..<j - Suc 0])"
    by (auto simp: nth_append)
  from assms have "(xs @ as) ! (j - Suc 0) = (ys @ as) ! (j - Suc 0)"
    by (auto simp: nth_append)
  then show ?thesis
    by (simp add: *)
qed

lemma well_valued0_prepend: "\<lbrakk>length xs \<le> l t - 1; length ys = length xs; well_shaped t; well_valued0 (xs @ as) t\<rbrakk> \<Longrightarrow> well_valued0 (ys @ as) t"
proof (induction t)
  case (Node i j a t1 t2)
  then have well_valued0_t1: "well_valued0 (ys @ as) t1"
    by auto
  from Node have "well_valued0 (ys @ as) t2"
  proof (cases a)
    case None
    with Node show ?thesis
      by auto
        (metis One_nat_def Suc_pred diff_Suc_1 le_Suc_eq le_Suc_ex trans_le_add1 tree.exhaust_sel well_shaped.simps(2))
  next
    case (Some a')
    with Node show ?thesis
      by auto
        (metis One_nat_def diff_Suc_1 diff_le_self le_trans tree.exhaust_sel well_shaped.simps(2))
  qed
  with Node well_valued0_t1 show ?case
  proof -
    have f1: "0 < i \<and> j \<le> length (xs @ as) \<and> (a = None \<or> a = Some (SWA.sum (xs @ as) i j)) \<and> well_valued0 (xs @ as) t1 \<and> well_valued0 (xs @ as) t2 \<and> (t2 = Leaf \<or> val t2 \<noteq> None)"
      by (meson \<open>well_valued0 (xs @ as) (Node i j a t1 t2)\<close> well_valued0.simps(2))
    then have f2: "j \<le> length (ys @ as)"
      by (simp add: \<open>length ys = length xs\<close>)
    have "a = None \<or> a = Some (SWA.sum (ys @ as) i j)"
      using f1 by (metis Node.prems(1) Node.prems(2) Node.prems(3) One_nat_def Suc_pred le_imp_less_Suc sum_eq_sum_prepend tree.sel(2) well_shaped.simps(2))
    then show ?thesis
      using f2 f1 \<open>well_valued0 (ys @ as) t2\<close> well_valued0.simps(2) well_valued0_t1 by blast
  qed
qed simp

lemma valid_prepend: "\<lbrakk>length xs \<le> l t - 1; length ys = length xs; valid (xs @ as) t\<rbrakk> \<Longrightarrow> valid (ys @ as) t"
  unfolding valid_def
  by (auto intro: well_valued0_prepend)

lemma take_eq_append_take_take_drop: "m \<le> n \<Longrightarrow> take n xs = take m xs @ take (n-m) (drop m xs)"
proof (induction xs)
  case (Cons a xs)
  then show ?case
    by (metis le_add_diff_inverse take_add)
qed simp

lemma well_valued0_take_r: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow> well_valued0 (take (r t) as) t"
proof (induction t)
  case (Node i j a t1 t2)
  from Node have well_valued0_t1: "well_valued0 (take j as) t1"
  proof -
    from Node have "r t1 \<le> j"
      using r_lchild_le_r by (metis tree.sel(4) tree.sel(8))
    with Node have "take j as = take (r t1) as @ take (j - r t1) (drop (r t1) as)"
      using take_eq_append_take_take_drop[of "r t1" j as] by simp
    with Node show ?thesis
      by (auto intro!: well_valued0_append)
  qed
  from Node have well_valued0_t2: "well_valued0 (take j as) t2"
    by auto
  from Node have sum_eq: "fold (+) (rev (map ((!) as) [l t1 - Suc 0..<r t2 - Suc 0])) (as ! (r t2 - Suc 0)) =
      fold (+) (rev (map ((!) (take (r t2) as)) [l t1 - Suc 0..<r t2 - Suc 0])) (as ! (r t2 - Suc 0))"
    by (intro arg_cong[where f="\<lambda>xs. fold _ xs _"]) auto
  from Node well_valued0_t1 well_valued0_t2 sum_eq show ?case
    by auto
qed simp

lemma valid_take_r: "valid as t \<Longrightarrow> valid (take (r t) as) t"
  unfolding valid_def
  by (auto intro: well_valued0_take_r)

lemma well_valued0_butlast: "\<lbrakk>well_shaped t; well_valued0 as t; r t < length as\<rbrakk> \<Longrightarrow> well_valued0 (butlast as) t"
proof (induction t)
  case (Node i j a t1 t2)
  then  have r_le_length: "j \<le> length (butlast as)"
    by simp
  from Node have "i > 0"
    by simp
  with r_le_length Node have sum_eq: "sum as i j = sum (butlast as) i j"
    by (metis append_butlast_last_id le_zero_eq less_imp_le_nat list.size(3) neq_iff
      sum_eq_sum_append well_shaped.simps(2))
  from Node have "r t1 < length as"
    by (metis dual_order.strict_trans2 r_lchild_le_r tree.sel(8))
  with Node r_le_length show ?case
    by (metis (no_types, lifting) dual_order.strict_iff_order sum_eq tree.sel(10) tree.sel(4)
      well_shaped.simps(2) well_shaped_rchild well_valued0.simps(2))
qed simp

lemma well_valued0_append_butlast_lchild: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow>
  well_valued0 (butlast as @ [last as + x]) (lchild t)"
proof (cases t)
  case (Node i j a t1 t2)
  assume assms: "well_shaped t" "well_valued0 as t"
  from Node assms have "r t1 < length as"
    by (fastforce dest: well_shaped_lr)
  with Node assms show ?thesis
    by (auto simp: well_valued0_butlast well_valued0_append)
qed simp

lemma sum_update_rightmost: "\<lbrakk>0 < i; i \<le> j; length as = j\<rbrakk> \<Longrightarrow>
  sum as i j + x = sum (butlast as @ [last as + x]) i j"
  by (cases as)
    (auto simp: nth_append[abs_def] fold_add_add last_conv_nth nth_Cons' nth_butlast
     intro!: arg_cong2[where f="(+)"] arg_cong[where f="\<lambda>xs. fold _ xs _"])

lemma well_valued0_update_rightmost: "\<lbrakk>well_shaped t; well_valued0 as t; length as = r t\<rbrakk> \<Longrightarrow>
  well_valued0 (butlast as @ [last as + x]) (update_rightmost (\<lambda>a. a + x) t)"
proof (induction t)
  case Leaf
  then show ?case
    by (auto simp add: valid_Leaf)
next
  case (Node i j a t1 t2)
  moreover
  from Node have well_valued0_t1: "well_valued0 (butlast as @ [last as + x]) t1"
    using well_valued0_append_butlast_lchild by (metis tree.sel(8))
  moreover
  from Node have well_valued0_t2:
    "well_valued0 (butlast as @ [last as + x]) (update_rightmost ((\<lambda>a. a + x)) t2)"
    by (metis \<open>well_valued0 (butlast as @ [last as + x]) t1\<close> dual_order.strict_iff_order
      tree.sel(4) update_rightmost.simps(1) well_shaped.simps(2) well_valued0.simps(2))
  ultimately show ?case
    using sum_update_rightmost
    by (cases a) (auto simp: val_update_rightmost_neq_None)
qed

(* correctness of update_rightmost *)
lemma valid_update_rightmost: "\<lbrakk>valid as t; length as = r t\<rbrakk> \<Longrightarrow>
  valid (butlast as @ [last as + x]) (update_rightmost (\<lambda>a. a + x) t)"
  unfolding valid_def
  using well_valued0_update_rightmost
  by (metis update_rightmost.simps(1) val_update_rightmost_neq_None well_shaped_update_rightmost)

(*<*)
end
(*>*)
