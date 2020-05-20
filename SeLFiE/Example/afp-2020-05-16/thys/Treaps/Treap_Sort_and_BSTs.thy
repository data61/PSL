(*
  File:      Treap_Sort_and_BSTs.thy
  Authors:   Max Haslbeck
*)
section \<open>Relationship between treaps and BSTs\<close>
theory Treap_Sort_and_BSTs
imports
  Treap
  Random_List_Permutation
  "Random_BSTs.Random_BSTs"
begin

text \<open>
  Here, we will show that if we ``forget'' the priorities of a treap, we essentially get a
  BST into which the elements have been inserted by ascending priority.

  First, we show some facts about sorting that we will need.
\<close>

text \<open>
  The following two lemmas are only important for measurability later.
\<close>
lemma insort_key_conv_rec_list:
  "insort_key f x xs =
     rec_list [x] (\<lambda>y ys zs. if f x \<le> f y then x # y # ys else y # zs) xs"
  by (induction xs) simp_all

lemma insort_key_conv_rec_list':
  "insort_key = (\<lambda>f x.
     rec_list [x] (\<lambda>y ys zs. if f x \<le> f y then x # y # ys else y # zs))"
  by (intro ext) (simp add: insort_key_conv_rec_list)

lemma bst_of_list_trees:
  assumes "set ys \<subseteq> A"
  shows "bst_of_list ys \<in> trees A"
  using assms by (induction ys rule: bst_of_list.induct) auto

lemma insort_wrt_insort_key:
   "a \<in> A \<Longrightarrow>
   set xs \<subseteq> A \<Longrightarrow>
   insert_wrt (linorder_from_keys A f) a xs = insort_key f a xs"
 unfolding linorder_from_keys_def by (induction xs) (auto)

lemma insort_wrt_sort_key:
  assumes "set xs \<subseteq> A"
  shows "insort_wrt (linorder_from_keys A f) xs = sort_key f xs"
  using assms by (induction xs) (auto simp add: insort_wrt_def insort_wrt_insort_key)


text \<open>
  The following is an important recurrence for @{term "sort_key"} that states that for distinct
  priorities, sorting a list w.\,r.\,t.\ those priorities can be seen as selection sort, i.\,e.\ 
  we can first choose the (unique) element with minimum priority as the first element and then
  sort the rest of the list and append it.
\<close>
lemma sort_key_arg_min_on:
  assumes "zs \<noteq> []"  "inj_on p (set zs)"
  shows "sort_key p (zs::'a::linorder list) = 
         (let z = arg_min_on p (set zs) in z # sort_key p (remove1 z zs))"
proof -
  have "mset zs = mset (let z = arg_min_on p (set zs) in z # sort_key p (remove1 z zs))"
  proof -
    define m where "m = arg_min_on p (set zs)"
    have "m \<in> (set zs)"
      unfolding m_def by (rule arg_min_if_finite) (use assms in auto)
    then show ?thesis
      by (auto simp add: Let_def m_def)
  qed
  moreover have "linorder_class.sorted
                 (map p (let z = arg_min_on p (set zs) in z # sort_key p (remove1 z zs)))"
  proof -
    have "set (map p (sort_key p (remove1 (arg_min_on p (set zs)) zs))) \<subseteq> p ` set zs"
      using set_remove1_subset by (fastforce)
    moreover have "\<And>y. y \<in> p ` set zs \<Longrightarrow> p (arg_min_on p (set zs)) \<le> y"
      using arg_min_least assms by force
    ultimately have "linorder_class.sorted
        (p (arg_min_on p (set zs)) # map p (sort_key p (remove1 (arg_min_on p (set zs)) zs)))"
      by (auto)
    then show ?thesis
      by (simp add: Let_def)
  qed
  ultimately show ?thesis
    using sort_key_inj_key_eq assms by blast
qed

lemma arg_min_on_image_finite:
  fixes f :: "'b \<Rightarrow> 'c :: linorder"
  assumes "inj_on f (g ` B)" "finite B" "B \<noteq> {}"
  shows "arg_min_on f (g ` B) = g (arg_min_on (f \<circ> g) B)"
proof -
  note * = arg_min_if_finite[OF \<open>finite B\<close> \<open>B \<noteq> {}\<close>, of \<open>f \<circ> g\<close>]
  show ?thesis
    using assms * arg_min_inj_eq
    by (smt arg_min_if_finite(1) arg_min_least 
        comp_apply finite_imageI imageE image_eqI image_is_empty inj_onD less_le)
qed

lemma fst_snd_arg_min_on: fixes p::"'a \<Rightarrow> 'b::linorder"
  assumes "finite B" "inj_on p B" "B \<noteq> {}"
  shows   "fst (arg_min_on snd ((\<lambda>x. (x, p x)) ` B)) = arg_min_on p B"
  by (subst arg_min_on_image_finite [OF inj_on_imageI]) 
     (auto simp: o_def assms)

text \<open>
  The following is now the main result:
\<close>
theorem treap_of_bst_of_list':
  assumes "ys = map (\<lambda>x. (x, p x)) xs" "inj_on p (set xs)" "xs' = sort_key p xs"
  shows "map_tree fst (treap_of (set ys)) = bst_of_list xs'"
  using assms
proof(induction xs' arbitrary: xs ys rule: bst_of_list.induct)
  case 1
  from \<open>[] = sort_key p xs\<close>[symmetric] \<open>ys = map (\<lambda>x. (x, p x)) xs\<close>
  have "ys = []"
    by (cases xs) (auto)
  then show ?case by (simp add: treap_of.simps)
next
  case (2 z zs)
  note IH = 2(1,2)
  note assms = 2(3,4,5)
  define m where "m = arg_min_on snd (set ys)"
  define ls where "ls = map (\<lambda>x. (x, p x)) [y\<leftarrow>zs . y < z]"
  define rs where "rs = map (\<lambda>x. (x, p x)) [y\<leftarrow>zs . y > z]"
  define L where "L = {p \<in> (set ys). fst p < fst m}"
  define R where "R = {p \<in> (set ys). fst p > fst m}"
  have h1: "set (z#zs) = set xs"
    using assms by simp
  then have h2: "inj_on p {x \<in> set zs. x < z}" "inj_on p (set (filter ((<) z) zs))"
    "inj_on p (set zs)"
    using \<open>inj_on p (set xs)\<close> by (auto intro!: inj_on_subset[of _ "set xs"])
  have "z # zs = (let z = arg_min_on p (set xs) in z # sort_key p (remove1 z xs))"
  proof -
    have "xs \<noteq> []"
      using assms by force
    then show ?thesis
      by (auto simp add: assms intro!: sort_key_arg_min_on)
  qed
  then have h3: "z = arg_min_on p (set xs)" "zs = sort_key p (remove1 z xs)"
    unfolding Let_def by auto
  have h4: "sort_key p zs = zs"
  proof -
    have "linorder_class.sorted (map p (z#zs))"
      using assms by simp
    then have "linorder_class.sorted (map p zs)"
      by auto
    then show ?thesis
      using h1 h2 sort_key_inj_key_eq by blast
  qed
  note helpers = h1 h2 h3 h4
  have "fst m = z"
  proof -
    have "fst m = arg_min_on p (set xs)"
      unfolding m_def using assms by (auto intro!: fst_snd_arg_min_on)
    also have "\<dots> = z"
      using helpers by auto
    finally show ?thesis .
  qed
  moreover have "map_tree fst (treap_of L) = bst_of_list [y\<leftarrow>zs . y < z]"
  proof -
    have "L = set ls"
      unfolding L_def ls_def \<open>fst m = z\<close> using helpers assms by force
    moreover have "map_tree fst (treap_of (set ls)) = bst_of_list [y\<leftarrow>zs . y < z]"
      unfolding ls_def using helpers 
      by (intro IH(1)[of _ "[y\<leftarrow>zs . y < z]"]) (auto simp add: filter_sort[symmetric])
    ultimately show ?thesis
      by blast
  qed
  moreover have "map_tree fst (treap_of R) = bst_of_list [y\<leftarrow>zs . z < y]"
  proof -
    have 0: "R = set rs"
      unfolding R_def rs_def \<open>fst m = z\<close> using helpers assms by force
    moreover have "map_tree fst (treap_of (set rs)) = bst_of_list [y\<leftarrow>zs . z < y]"
      unfolding rs_def using helpers
      by (intro IH(2)[of _ "[y\<leftarrow>zs . z < y]"]) (auto simp add: filter_sort[symmetric])
    ultimately show ?thesis
      by blast
  qed
  moreover have "treap_of (set ys) = \<langle>treap_of L, m, treap_of R\<rangle>"
    unfolding L_def m_def R_def using assms by (auto simp add: treap_of.simps Let_def)
  ultimately show ?case by auto
qed

corollary treap_of_bst_of_list: "inj_on p (set zs) \<Longrightarrow>
   map_tree fst (treap_of (set (map (\<lambda>x. (x, p x)) zs))) = bst_of_list (sort_key p zs)"
  using treap_of_bst_of_list' by blast

corollary treap_of_bst_of_list'': "inj_on p (set zs) \<Longrightarrow>
   map_tree fst (treap_of ((\<lambda>x. (x, p x)) ` set zs)) = bst_of_list (sort_key p zs)"
  using treap_of_bst_of_list by auto

corollary fold_ins_bst_of_list: "distinct zs \<Longrightarrow> inj_on p (set zs) \<Longrightarrow>
   map_tree fst (foldl (\<lambda>t (x,p). ins x p t) \<langle>\<rangle> (map (\<lambda>x. (x, p x)) zs)) = bst_of_list (sort_key p zs)"
  by (auto simp add: foldl_ins_treap_of distinct_map inj_on_def inj_on_convol_ident
                     treap_of_bst_of_list'')

end