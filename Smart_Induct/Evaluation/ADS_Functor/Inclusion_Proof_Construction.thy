(* Author: Andreas Lochbihler, Digital Asset
   Author: Ognjen Maric, Digital Asset *)

theory Inclusion_Proof_Construction imports
  ADS_Construction
begin

primrec blind_blindable :: "('a\<^sub>m \<Rightarrow> 'a\<^sub>h) \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m" where
  "blind_blindable h (Blinded x) = Blinded x"
| "blind_blindable h (Unblinded x) = Blinded (Content (h x))"

lemma hash_blind_blindable [simp]: "hash_blindable h (blind_blindable h x) = hash_blindable h x"
  by(cases x) simp_all

subsection \<open>Inclusion proof construction for rose trees\<close>

(************************************************************)
subsubsection \<open> Hashing, embedding and blinding source trees \<close>
(************************************************************)

context fixes h :: "'a \<Rightarrow> 'a\<^sub>h" begin
fun hash_source_tree :: "'a rose_tree \<Rightarrow> 'a\<^sub>h rose_tree\<^sub>h" where
  "hash_source_tree (Tree (data, subtrees)) = Tree\<^sub>h (Content (h data, map hash_source_tree subtrees))"
end

context fixes e :: "'a \<Rightarrow> 'a\<^sub>m" begin
fun embed_source_tree :: "'a rose_tree \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m" where
  "embed_source_tree (Tree (data, subtrees)) =
    Tree\<^sub>m (Unblinded (e data, map embed_source_tree subtrees))"
end

context fixes h :: "'a \<Rightarrow> 'a\<^sub>h" begin
fun blind_source_tree :: "'a rose_tree \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m" where
  "blind_source_tree (Tree (data, subtrees)) = Tree\<^sub>m (Blinded (Content (h data, map (hash_source_tree h) subtrees)))"
end

case_of_simps blind_source_tree_cases: blind_source_tree.simps

fun is_blinded :: "('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m \<Rightarrow> bool" where
  "is_blinded (Tree\<^sub>m (Blinded _)) = True"
| "is_blinded _ = False"

lemma hash_blinded_simp: "hash_tree h' (blind_source_tree h st) = hash_source_tree h st"
  by(cases st rule: blind_source_tree.cases)(simp_all add: hash_rt_F\<^sub>m_def)

lemma hash_embedded_simp:
  "hash_tree h (embed_source_tree e st) = hash_source_tree (h \<circ> e) st"
  by(induction st rule: embed_source_tree.induct)(simp add: hash_rt_F\<^sub>m_def)

lemma blinded_embedded_same_hash:
  "hash_tree h'' (blind_source_tree (h o e) st) = hash_tree h (embed_source_tree e st)"
  by(simp add: hash_blinded_simp hash_embedded_simp)

lemma blinding_blinds [simp]:
  "is_blinded (blind_source_tree h t)"
  by(simp add: blind_source_tree_cases split: rose_tree.split)

lemma blinded_blinds_embedded: 
  "blinding_of_tree h bo (blind_source_tree (h o e) st) (embed_source_tree e st)"
  by(cases st rule: blind_source_tree.cases)(simp_all add: hash_embedded_simp)

fun embed_hash_tree :: "'ha rose_tree\<^sub>h \<Rightarrow> ('a, 'ha) rose_tree\<^sub>m" where
  "embed_hash_tree (Tree\<^sub>h h) = Tree\<^sub>m (Blinded h)"


(************************************************************)
subsubsection \<open>Auxiliary definitions: selectors and list splits\<close>
(************************************************************)

fun children :: "'a rose_tree \<Rightarrow> 'a rose_tree list" where
  "children (Tree (data, subtrees)) = subtrees"

fun children\<^sub>m :: "('a, 'a\<^sub>h) rose_tree\<^sub>m \<Rightarrow> ('a, 'a\<^sub>h) rose_tree\<^sub>m list" where
  "children\<^sub>m (Tree\<^sub>m (Unblinded (data, subtrees))) = subtrees"
| "children\<^sub>m _ = undefined"

fun splits :: "'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) list" where
  "splits [] = []"
| "splits (x#xs) = ([], x, xs) # map (\<lambda>(l, y, r). (x # l, y, r)) (splits xs)"

lemma splits_iff: "(l, a, r) \<in> set (splits ll) = (ll = l @ a # r)"
  by(induction ll arbitrary: l a r)(auto simp add: Cons_eq_append_conv)

(************************************************************)
subsubsection \<open> Zippers \<close>
(************************************************************)

text \<open> Zippers provide a neat representation of tree-like ADSs when they have only a single 
  unblinded subtree. The zipper path provides the "inclusion proof" that the unblinded subtree is
  included in a larger structure. \<close>

type_synonym 'a path_elem = "'a \<times> 'a rose_tree list \<times> 'a rose_tree list"
type_synonym 'a path = "'a path_elem list"
type_synonym 'a zipper = "'a path \<times> 'a rose_tree"

definition zipper_of_tree :: "'a rose_tree \<Rightarrow> 'a zipper" where
  "zipper_of_tree t \<equiv> ([], t)"
               
fun tree_of_zipper :: "'a zipper \<Rightarrow> 'a rose_tree" where
  "tree_of_zipper ([], t) = t"
| "tree_of_zipper ((a, l, r) # z, t) = tree_of_zipper (z, (Tree (a, (l @ t # r))))"

case_of_simps tree_of_zipper_cases: tree_of_zipper.simps

lemma tree_of_zipper_id[iff]: "tree_of_zipper (zipper_of_tree t) = t"
  by(simp add: zipper_of_tree_def)

fun zipper_children :: "'a zipper \<Rightarrow> 'a zipper list" where
  "zipper_children (p, Tree (a, ts)) = map (\<lambda>(l, t, r). ((a, l, r) # p, t)) (splits ts)"

lemma zipper_children_same_tree:
  assumes "z' \<in> set (zipper_children z)"
  shows "tree_of_zipper z' = tree_of_zipper z"
proof-
  obtain p a ts where z: "z = (p, Tree (a, ts))"
    using assms
    by(cases z rule: zipper_children.cases) (simp_all)

  then obtain l t r where ltr: "z' = ((a, l, r) # p, t)" and "(l, t, r) \<in> set (splits ts)"
    using assms
    by(auto)

  with z show ?thesis
    by(simp add: splits_iff)
qed

type_synonym ('a\<^sub>m, 'a\<^sub>h) path_elem\<^sub>m = "'a\<^sub>m \<times> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m list \<times> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m list"
type_synonym ('a\<^sub>m, 'a\<^sub>h) path\<^sub>m = "('a\<^sub>m, 'a\<^sub>h) path_elem\<^sub>m list"
type_synonym ('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m = "('a\<^sub>m, 'a\<^sub>h) path\<^sub>m \<times> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m"

definition zipper_of_tree\<^sub>m :: "('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m" where
  "zipper_of_tree\<^sub>m t \<equiv> ([], t)"

fun tree_of_zipper\<^sub>m :: "('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m" where
  "tree_of_zipper\<^sub>m ([], t) = t"
| "tree_of_zipper\<^sub>m ((m, l, r) # z, t) = tree_of_zipper\<^sub>m (z, Tree\<^sub>m (Unblinded (m, l @ t # r)))"

lemma tree_of_zipper\<^sub>m_append:
  "tree_of_zipper\<^sub>m (p @ p', t) = tree_of_zipper\<^sub>m (p', tree_of_zipper\<^sub>m (p, t))"
  by(induction p arbitrary: p' t) auto

fun zipper_children\<^sub>m :: "('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m list" where
  "zipper_children\<^sub>m (p, Tree\<^sub>m (Unblinded (a, ts))) = map (\<lambda>(l, t, r). ((a, l, r) # p, t)) (splits ts) "
| "zipper_children\<^sub>m _ = []"

lemma zipper_children_same_tree\<^sub>m:
  assumes "z' \<in> set (zipper_children\<^sub>m z)"
  shows "tree_of_zipper\<^sub>m z' = tree_of_zipper\<^sub>m z"
proof-
  obtain p a ts where z: "z = (p, Tree\<^sub>m (Unblinded (a, ts)))"
    using assms
    by(cases z rule: zipper_children\<^sub>m.cases) (simp_all)

  then obtain l t r where ltr: "z' = ((a, l, r) # p, t)" and "(l, t, r) \<in> set (splits ts)"
    using assms
    by(auto)

  with z show ?thesis
    by(simp add: splits_iff)
qed

fun blind_path_elem :: "('a \<Rightarrow> 'a\<^sub>m) \<Rightarrow> ('a\<^sub>m \<Rightarrow> 'a\<^sub>h) \<Rightarrow> 'a path_elem \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) path_elem\<^sub>m"  where
  "blind_path_elem e h (x, l, r) = (e x, map (blind_source_tree (h \<circ> e)) l, map (blind_source_tree (h \<circ> e)) r)"

case_of_simps blind_path_elem_cases: blind_path_elem.simps

definition blind_path :: "('a \<Rightarrow> 'a\<^sub>m) \<Rightarrow> ('a\<^sub>m \<Rightarrow> 'a\<^sub>h) \<Rightarrow> 'a path \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) path\<^sub>m" where
  "blind_path e h \<equiv> map (blind_path_elem e h)"

fun embed_path_elem :: "('a \<Rightarrow> 'a\<^sub>m) \<Rightarrow> 'a path_elem \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) path_elem\<^sub>m" where
  "embed_path_elem e (d, l, r) = (e d, map (embed_source_tree e) l, map (embed_source_tree e) r)"

definition embed_path :: "('a \<Rightarrow> 'a\<^sub>m) \<Rightarrow> 'a path \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) path\<^sub>m" where
  "embed_path embed_elem \<equiv> map (embed_path_elem embed_elem)"

lemma hash_tree_of_zipper_same_path: 
  "hash_tree h (tree_of_zipper\<^sub>m (p, v)) = hash_tree h (tree_of_zipper\<^sub>m (p, v'))
        \<longleftrightarrow> hash_tree h v = hash_tree h v'"
  by(induction p arbitrary: v v')(auto simp add: hash_rt_F\<^sub>m_def)

fun hash_path_elem :: "('a\<^sub>m \<Rightarrow> 'a\<^sub>h) \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) path_elem\<^sub>m \<Rightarrow> ('a\<^sub>h \<times> 'a\<^sub>h rose_tree\<^sub>h list \<times> 'a\<^sub>h rose_tree\<^sub>h list)" where
  "hash_path_elem h (e, l, r) = (h e, map (hash_tree h) l, map (hash_tree h) r)"

lemma hash_view_zipper_eqI:
  "\<lbrakk> hash_list (hash_path_elem h) p = hash_list (hash_path_elem h') p';
    hash_tree h v = hash_tree h' v' \<rbrakk> \<Longrightarrow>
    hash_tree h (tree_of_zipper\<^sub>m (p, v)) = hash_tree h' (tree_of_zipper\<^sub>m (p', v'))"
  by(induction p arbitrary: p' v v')(auto simp add: hash_rt_F\<^sub>m_def)

lemma blind_embed_path_same_hash:
  "hash_tree h (tree_of_zipper\<^sub>m (blind_path e h p, t)) = hash_tree h (tree_of_zipper\<^sub>m (embed_path e p, t))"
proof -
  have "hash_path_elem h \<circ> blind_path_elem e h = hash_path_elem h \<circ> embed_path_elem e"
    by(clarsimp simp add: hash_blinded_simp hash_embedded_simp fun_eq_iff intro!: arg_cong2[where f=hash_source_tree, OF _ refl])
  then show ?thesis
    by(intro hash_view_zipper_eqI)(simp_all add: embed_path_def blind_path_def list.map_comp)
qed

lemma tree_of_embed_commute:
  "tree_of_zipper\<^sub>m (embed_path e p, embed_source_tree e t) = embed_source_tree e (tree_of_zipper (p, t))"
  by(induction "(p, t)" arbitrary: p t rule: tree_of_zipper.induct)(simp_all add: embed_path_def)

lemma childz_same_tree:
  "(l, t, r) \<in> set (splits ts) \<Longrightarrow>
  tree_of_zipper\<^sub>m (embed_path e p, embed_source_tree e (Tree (d, ts))) 
  = tree_of_zipper\<^sub>m (embed_path e ((d, l, r) # p), embed_source_tree e t)"
  by(simp add: tree_of_embed_commute splits_iff del: embed_source_tree.simps)

lemma blinding_of_same_path:
  assumes bo: "blinding_of_on UNIV h bo"
  shows
  "blinding_of_tree h bo (tree_of_zipper\<^sub>m (p, t)) (tree_of_zipper\<^sub>m (p, t'))
  \<longleftrightarrow> blinding_of_tree h bo t t'"
proof -
  interpret a: blinding_of_on UNIV h bo by fact
  interpret tree: blinding_of_on UNIV "hash_tree h" "blinding_of_tree h bo" ..
  show ?thesis
    by(induction p arbitrary: t t')(auto simp add: list_all2_append list.rel_refl a.refl tree.refl)
qed

lemma zipper_children_size_change [termination_simp]: "(a, b) \<in> set (zipper_children (p, v)) \<Longrightarrow> size b < size v"
  by(cases v)(clarsimp simp add: splits_iff Set.image_iff)


subsection \<open>All zippers of a rose tree\<close>

context fixes e :: "'a \<Rightarrow> 'a\<^sub>m" and h :: "'a\<^sub>m \<Rightarrow> 'a\<^sub>h" begin

fun zippers_rose_tree :: "'a zipper \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h) zipper\<^sub>m list" where
  "zippers_rose_tree (p, t) = (blind_path e h p, embed_source_tree e t) # 
    concat (map zippers_rose_tree (zipper_children (p, t)))"

end

lemmas [simp del] = zippers_rose_tree.simps zipper_children.simps

lemma zippers_rose_tree_same_hash':
  assumes "z \<in> set (zippers_rose_tree e h (p, t))"
  shows "hash_tree h (tree_of_zipper\<^sub>m z) = 
    hash_tree h (tree_of_zipper\<^sub>m (embed_path e p, embed_source_tree e t))"
  using assms(1)
proof(induction "(p, t)" arbitrary: p t rule: zippers_rose_tree.induct)
  case (1 p t)
  from "1.prems"[unfolded zippers_rose_tree.simps] 
  consider (find) "z = (blind_path e h p, embed_source_tree e t)"
    | (rec) x ts l t' r where "t = Tree (x, ts)" "(l, t', r) \<in> set (splits ts)" "z \<in> set (zippers_rose_tree e h ((x, l, r) # p, t'))"
    by(cases t)(auto simp add: zipper_children.simps) 
  then show ?case
  proof cases
    case rec
    then show ?thesis
      apply(subst "1.hyps"[of "(x, l, r) # p" "t'"])
      apply(simp_all add: rev_image_eqI zipper_children.simps)
      by (metis (no_types) childz_same_tree comp_apply embed_source_tree.simps rec(2))
  qed(simp add: blind_embed_path_same_hash)
qed

lemma zippers_rose_tree_blinding_of:
  assumes "blinding_of_on UNIV h bo" 
    and z: "z \<in> set (zippers_rose_tree e h (p, t))"
  shows "blinding_of_tree h bo (tree_of_zipper\<^sub>m z) (tree_of_zipper\<^sub>m (blind_path e h p, embed_source_tree e t))"
  using z
proof(induction "(p, t)" arbitrary: p t rule: zippers_rose_tree.induct)
  case (1 p t)

  interpret a: blinding_of_on UNIV h bo by fact
  interpret rt: blinding_of_on UNIV "hash_tree h" "blinding_of_tree h bo" ..

  from "1.prems"[unfolded zippers_rose_tree.simps] 
  consider (find) "z = (blind_path e h p, embed_source_tree e t)"
    | (rec) x ts l t' r where "t = Tree (x, ts)" "(l, t', r) \<in> set (splits ts)" "z \<in> set (zippers_rose_tree e h ((x, l, r) # p, t'))"
    by(cases t)(auto simp add: zipper_children.simps) 
  then show ?case 
  proof cases
    case find
    then show ?thesis by(simp add: rt.refl)
  next
    case rec
    then have "blinding_of_tree h bo 
      (tree_of_zipper\<^sub>m z) 
      (tree_of_zipper\<^sub>m (blind_path e h ((x, l, r) # p), embed_source_tree e t'))"
      by(intro 1)(simp add: rev_image_eqI zipper_children.simps)
    also have "blinding_of_tree h bo 
      (tree_of_zipper\<^sub>m (blind_path e h ((x, l, r) # p), embed_source_tree e t'))
      (tree_of_zipper\<^sub>m (blind_path e h p, embed_source_tree e (Tree (x, ts))))"
      using rec
      by(simp add: blind_path_def splits_iff blinding_of_same_path[OF assms(1)] a.refl list_all2_append list_all2_same list.rel_map blinded_blinds_embedded rt.refl)
    finally (rt.trans) show ?thesis using rec by simp
  qed
qed

lemma zippers_rose_tree_neq_Nil: "zippers_rose_tree e h (p, t) \<noteq> []"
  by(simp add: zippers_rose_tree.simps)

lemma (in comp_fun_idem) fold_set_union:
  assumes "finite A" "finite B"
  shows "Finite_Set.fold f z (A \<union> B) = Finite_Set.fold f (Finite_Set.fold f z A) B"
  using assms(2,1) by induct simp_all

context merkle_interface begin

lemma comp_fun_idem_merge: "comp_fun_idem (\<lambda>x yo. yo \<bind> m x)"
  apply(unfold_locales; clarsimp simp add: fun_eq_iff split: bind_split)
  subgoal by (metis assoc bind.bind_lunit bind.bind_lzero idem option.distinct(1))
  subgoal by (simp add: join)
  done

interpretation merge: comp_fun_idem "\<lambda>x yo. yo \<bind> m x" by(rule comp_fun_idem_merge)

definition Merge :: "'a\<^sub>m set \<Rightarrow> 'a\<^sub>m option" where
  "Merge A = (if A = {} \<or> infinite A then None else Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some (SOME x. x \<in> A)) A)"

lemma Merge_empty [simp]: "Merge {} = None"
  by(simp add: Merge_def)

lemma Merge_infinite [simp]: "infinite A \<Longrightarrow> Merge A = None"
  by(simp add: Merge_def)

lemma Merge_cong_start:
  "Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some x) A = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some y) A" (is "?lhs = ?rhs")
  if "x \<in> A" "y \<in> A" "finite A"
proof -
  have "?lhs = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some x) (insert y A)" using that by(simp add: insert_absorb)
  also have "\<dots> = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (m x y) A" using that 
    by(simp only: merge.fold_insert_idem2)(simp add: commute)
  also have "\<dots> = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some y) (insert x A)" using that
    by(simp only: merge.fold_insert_idem2)(simp)
  also have "\<dots> = ?rhs" using that by(simp add: insert_absorb)
  finally show ?thesis .
qed

lemma Merge_insert [simp]: "Merge (insert x A) = (if A = {} then Some x else Merge A \<bind> m x)" (is "?lhs = ?rhs")
proof(cases "finite A \<and> A \<noteq> {}")
  case True
  then have "?lhs = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some (SOME x. x \<in> A)) (insert x A)" 
    unfolding Merge_def by(subst Merge_cong_start[where y="SOME x. x \<in> A", OF someI])(auto intro: someI)
  also have "\<dots> = ?rhs" using True by(simp add: Merge_def)
  finally show ?thesis .
qed(auto simp add: Merge_def idem)

lemma Merge_insert_alt:
  "Merge (insert x A) = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some x) A" (is "?lhs = ?rhs") if "finite A"
proof -
  have "?lhs = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some x) (insert x A)" using that
    unfolding Merge_def by(subst Merge_cong_start[where y=x, OF someI]) auto
  also have "\<dots> = ?rhs" using that by(simp only: merge.fold_insert_idem2)(simp add: idem)
  finally show ?thesis .
qed

lemma Merge_None [simp]: "Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) None A = None"
proof(cases "finite A")
  case True
  then show ?thesis by(induction) auto
qed simp

lemma Merge_union: 
  "Merge (A \<union> B) = (if A = {} then Merge B else if B = {} then Merge A else (Merge A \<bind> (\<lambda>a. Merge B \<bind> m a)))"
  (is "?lhs = ?rhs")
proof(cases "finite (A \<union> B) \<and> A \<noteq> {} \<and> B \<noteq> {}")
  case True
  then have "?lhs = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some (SOME x. x \<in> B)) (B \<union> A)"
    unfolding Merge_def by(subst Merge_cong_start[where y="SOME x. x \<in> B", OF someI])(auto intro: someI simp add: Un_commute)
  also have "\<dots> = Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Merge B) A" using True 
    by(simp add: Merge_def merge.fold_set_union)
  also have "\<dots> = Merge A \<bind> (\<lambda>a. Merge B \<bind> m a)"
  proof(cases "Merge B")
    case (Some b)
    thus ?thesis using True 
      by simp(subst Merge_insert_alt[symmetric]; simp add: commute; metis commute)
  qed simp
  finally show ?thesis using True by simp
qed auto

lemma Merge_upper:
  assumes m: "Merge A = Some x" and y: "y \<in> A"
  shows "bo y x"
proof -
  have "Merge A = Merge (insert y A)" using y by(simp add: insert_absorb)
  also have "\<dots> = Merge A \<bind> m y" using y by auto
  finally have "m y x = Some x" using m by simp
  thus ?thesis by(simp add: bo_def)
qed

lemma Merge_least:
  assumes m: "Merge A = Some x" and u[rule_format]: "\<forall>a\<in>A. bo a u"
  shows "bo x u"
proof -
  define a where "a \<equiv> SOME x. x \<in> A"
  from m have A: "finite A" "A \<noteq> {}" 
    and *: "Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some a) A = Some x" 
    by(auto simp add: Merge_def a_def split: if_splits)
  from A have "bo a u" by(auto intro: someI u simp add: a_def)
  with A * u show ?thesis
  proof(induction A arbitrary: a)
    case (insert x A)
    then show ?case
      by(cases "m x a"; cases "A = {}"; simp only: merge.fold_insert_idem2; simp)(auto simp add: join)
  qed simp
qed

lemma Merge_defined:
  assumes "finite A" "A \<noteq> {}" "\<forall>a\<in>A. \<forall>b \<in> A. h a = h b"
  shows "Merge A \<noteq> None"
proof
  define a where "a \<equiv> SOME a. a \<in> A"
  have a: "a \<in> A" unfolding a_def using assms by(auto intro: someI)
  hence ha: "\<forall>b \<in> A. h b = h a" using assms by blast

  assume m: "Merge A = None"
  hence "Finite_Set.fold (\<lambda>x yo. yo \<bind> m x) (Some a) A = None"
    using assms by(simp add: Merge_def a_def)
  with assms(1) show False using ha
  proof(induction arbitrary: a)
    case (insert x A)
    thus ?case
      apply(cases "m x a"; use nothing in \<open>simp only: merge.fold_insert_idem2\<close>)
       apply(simp add: merge_respects_hashes)
      apply(fastforce simp add: join vimage2p_def dest: hash[THEN predicate2D])
      done
  qed simp
qed

lemma Merge_hash:
  assumes "Merge A = Some x" "a \<in> A"
  shows "h a = h x"
  using Merge_upper[OF assms] hash by(auto simp add: vimage2p_def)

end

end