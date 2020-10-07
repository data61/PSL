(*
  File:      Random_Treap.thy
  Authors:   Max Haslbeck
*)
section \<open>Random treaps\<close>
theory Random_Treap
imports
  Probability_Misc
  Treap_Sort_and_BSTs
begin

subsection \<open>Measurability\<close>

text \<open>
  The following lemmas are only relevant for measurability.
\<close>

(* TODO Move *)
lemma tree_sigma_cong:
  assumes "sets M = sets M'"
  shows   "tree_sigma M = tree_sigma M'"
  using sets_eq_imp_space_eq[OF assms] using assms by (simp add: tree_sigma_def)

lemma distr_restrict:
  assumes "sets N = sets L" "sets K \<subseteq> sets M"
          "\<And>X. X \<in> sets K \<Longrightarrow> emeasure M X = emeasure K X"
          "\<And>X. X \<in> sets M \<Longrightarrow> X \<subseteq> space M - space K \<Longrightarrow> emeasure M X = 0"
          "f \<in> M \<rightarrow>\<^sub>M N" "f \<in> K \<rightarrow>\<^sub>M L"
  shows   "distr M N f = distr K L f"
proof (rule measure_eqI)
  fix X assume "X \<in> sets (distr M N f)"
  thus "emeasure (distr M N f) X = emeasure (distr K L f) X"
    using assms(1) by (intro emeasure_distr_restrict assms) simp_all
qed (use assms in auto)
(* END TODO *)

lemma sets_tree_sigma_count_space:
  assumes "countable B"
  shows   "sets (tree_sigma (count_space B)) = Pow (trees B)"
proof (intro equalityI subsetI)
  fix X assume X: "X \<in> Pow (trees B)"
  have "{t} \<in> sets (tree_sigma (count_space B))" if "t \<in> trees B" for t
    using that
  proof (induction t)
    case (2 l r x)
    hence "{\<langle>la, v, ra\<rangle> |la v ra. (v, la, ra) \<in> {x} \<times> {l} \<times> {r}}
               \<in> sets (tree_sigma (count_space B))"
      by (intro Node_in_tree_sigma pair_measureI) auto
    thus ?case by simp
  qed simp_all
  with X have "(\<Union>t\<in>X. {t}) \<in> sets (tree_sigma (count_space B))"
    by (intro sets.countable_UN' countable_subset[OF _ countable_trees[OF assms]]) auto
  also have "(\<Union>t\<in>X. {t}) = X" by blast
  finally show "X \<in> sets (tree_sigma (count_space B))" .
next
  fix X assume "X \<in> sets (tree_sigma (count_space B))"
  from sets.sets_into_space[OF this] show "X \<in> Pow (trees B)"
    by (simp add: space_tree_sigma)
qed

lemma height_primrec: "height = rec_tree 0 (\<lambda>_ _ _ a b. Suc (max a b))"
proof
  fix t :: "'a tree"
  show "height t = rec_tree 0 (\<lambda>_ _ _ a b. Suc (max a b)) t"
    by (induction t) simp_all
qed

lemma ipl_primrec: "ipl = rec_tree 0 (\<lambda>l _ r a b. size l + size r + a + b)"
proof 
  fix t :: "'a tree"
  show "ipl t = rec_tree 0 (\<lambda>l _ r a b. size l + size r + a + b) t"
    by (induction t) auto
qed

lemma size_primrec: "size = rec_tree 0 (\<lambda>_ _ _ a b. 1 + a + b)"
proof 
  fix t :: "'a tree"
  show "size t = rec_tree 0 (\<lambda>_ _ _ a b. 1 + a + b) t"
    by (induction t) auto
qed

lemma ipl_map_tree[simp]: "ipl (map_tree f t) = ipl t"
by (induction t) auto

lemma set_pmf_random_bst: "finite A \<Longrightarrow> set_pmf (random_bst A) \<subseteq> trees A"
  by (subst random_bst_altdef) 
     (auto intro!: bst_of_list_trees simp add: bst_of_list_trees permutations_of_setD)

lemma trees_mono: "A \<subseteq> B \<Longrightarrow> trees A \<subseteq> trees B"
proof
  fix t
  assume "A \<subseteq> B" "t \<in> trees A"
  then show "t \<in> trees B"
    by (induction t) auto
qed

lemma ins_primrec:
  "ins k (p::real) t = rec_tree 
    (Node Leaf (k,p) Leaf)
    (\<lambda>l z r l' r'. case z of (k1, p1) \<Rightarrow>
      if k < k1 then
        (case l' of
          Leaf \<Rightarrow> Leaf
        | Node l2 (k2,p2) r2 \<Rightarrow> 
            if 0 \<le> p2 - p1 then Node (Node l2 (k2,p2) r2) (k1,p1) r
            else Node l2 (k2,p2) (Node r2 (k1,p1) r))
      else if k > k1 then
        (case r' of
          Leaf \<Rightarrow> Leaf
        | Node l2 (k2,p2) r2 \<Rightarrow>
            if 0 \<le> p2 - p1 then Node l (k1,p1) (Node l2 (k2,p2) r2)
            else Node (Node l (k1,p1) l2) (k2,p2) r2)
      else Node l (k1,p1) r
      ) t"
proof (induction k p t rule: ins.induct)
  case (2 k p l k1 p1 r)
  thus ?case 
    by (cases "k < k1") (auto simp add: case_prod_beta ins_neq_Leaf split: tree.splits if_splits)
qed auto

lemma measurable_less_count_space [measurable (raw)]:
  assumes "countable A"
  assumes [measurable]: "a \<in> B \<rightarrow>\<^sub>M count_space A"
  assumes [measurable]: "b \<in> B \<rightarrow>\<^sub>M count_space A"
  shows   "Measurable.pred B (\<lambda>x. a x < b x)"
proof -
  have "Measurable.pred (count_space (A \<times> A)) (\<lambda>x. fst x < snd x)" by simp
  also have "count_space (A \<times> A) = count_space A \<Otimes>\<^sub>M count_space A"
    using assms(1) by (simp add: pair_measure_countable)
  finally have "Measurable.pred B ((\<lambda>x. fst x < snd x) \<circ> (\<lambda>x. (a x, b x)))"
    by measurable
  thus ?thesis by (simp add: o_def)
qed

lemma measurable_ins [measurable (raw)]:
  assumes [measurable]: "countable A"
  assumes [measurable]: "k \<in> B \<rightarrow>\<^sub>M count_space A"
  assumes [measurable]: "x \<in> B \<rightarrow>\<^sub>M (lborel :: real measure)"
  assumes [measurable]: "t \<in> B \<rightarrow>\<^sub>M tree_sigma (count_space A \<Otimes>\<^sub>M lborel)"
  shows   "(\<lambda>y. ins (k y) (x y) (t y)) \<in> B \<rightarrow>\<^sub>M tree_sigma (count_space A \<Otimes>\<^sub>M lborel)"
  unfolding ins_primrec by measurable

lemma map_tree_primrec: "map_tree f t = rec_tree \<langle>\<rangle> (\<lambda>l a r l' r'.  \<langle>l', f a, r'\<rangle>) t"
  by (induction t) auto

definition \<U> where "\<U> = (\<lambda>a b::real. uniform_measure lborel {a..b})"

declare \<U>_def[simp]

fun insR:: "'a::linorder \<Rightarrow> ('a \<times> real) tree \<Rightarrow> 'a set \<Rightarrow> ('a \<times> real) tree measure" where
  "insR x t A  = distr (\<U> 0 1) (tree_sigma (count_space A \<Otimes>\<^sub>M lborel)) (\<lambda>p. ins x p t)"

fun rinss :: "'a::linorder list \<Rightarrow> ('a \<times> real) tree \<Rightarrow> 'a set \<Rightarrow> ('a \<times> real) tree measure" where
  "rinss [] t A =  return (tree_sigma (count_space A \<Otimes>\<^sub>M lborel)) t" |
  "rinss (x#xs) t A = insR x t A \<bind> (\<lambda>t. rinss xs t A)"

lemma sets_rinss':
  assumes "countable B" "set ys \<subseteq> B"
  shows "t \<in> trees (B \<times> UNIV) \<Longrightarrow> sets (rinss ys t B) = sets (tree_sigma (count_space B \<Otimes>\<^sub>M lborel))"
  using assms proof(induction ys arbitrary: t)
  case (Cons y ys)
  then show ?case
    by (subst rinss.simps, subst sets_bind) (auto simp add: space_tree_sigma space_pair_measure)
qed auto

lemma measurable_foldl [measurable]:
  assumes "f \<in> A \<rightarrow>\<^sub>M B" "set xs \<subseteq> space C"
  assumes "\<And>c. c \<in> set xs \<Longrightarrow> (\<lambda>(a,b). g a b c) \<in> (A \<Otimes>\<^sub>M B) \<rightarrow>\<^sub>M B"
  shows   "(\<lambda>x. foldl (g x) (f x) xs) \<in> A \<rightarrow>\<^sub>M B"
  using assms
proof (induction xs arbitrary: f)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  note [measurable] = Cons.prems(1)
  from Cons.prems have [measurable]: "x \<in> space C" by simp
  have "(\<lambda>a. (a, f a)) \<in> A \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B"
    by measurable
  hence "(\<lambda>(a,b). g a b x) \<circ> (\<lambda>a. (a, f a)) \<in> A \<rightarrow>\<^sub>M B"
    by (rule measurable_comp) (rule Cons.prems, auto)
  hence "(\<lambda>a. g a (f a) x) \<in> A \<rightarrow>\<^sub>M B" by (simp add: o_def)
  hence "(\<lambda>xa. foldl (g xa) (g xa (f xa) x) xs) \<in> A \<rightarrow>\<^sub>M B"
    by (rule Cons.IH) (use Cons.prems in auto)
  thus ?case by simp
qed

lemma ins_trees: "t \<in> trees A \<Longrightarrow> (x,y) \<in> A \<Longrightarrow> ins x y t \<in> trees A"
  by (induction x y t rule: ins.induct)
     (auto split: tree.splits simp: ins_neq_Leaf)


subsection \<open>Main result\<close>

text \<open>
  In our setting, we have some countable set of values that may appear in the input and
  a concrete list consisting only of those elements with no repeated elements.

  We further define an abbreviation for the uniform distribution of permutations of that lists.
\<close>

context
  fixes xs::"'a::linorder list" and A::"'a set" and random_perm :: "'a list \<Rightarrow> 'a list measure"
  assumes con_assms: "countable A" "set xs \<subseteq> A" "distinct xs"
  defines "random_perm \<equiv> (\<lambda>xs. uniform_measure (count_space (permutations_of_set (set xs)))
                                 (permutations_of_set (set xs)))"
begin

text \<open>
  Again, we first need some facts about measurability.
\<close>
lemma sets_rinss [simp]: 
  assumes "t \<in> trees (A \<times> UNIV)" 
  shows "sets (rinss xs t A) = tree_sigma (count_space A \<Otimes>\<^sub>M borel)"
proof -
  have "tree_sigma (count_space A \<Otimes>\<^sub>M (lborel::real measure)) = tree_sigma (count_space A \<Otimes>\<^sub>M borel)"
    by (intro tree_sigma_cong sets_pair_measure_cong) auto
  then show ?thesis
    using assms con_assms by (subst sets_rinss') auto
qed

lemma bst_of_list_measurable [measurable]:
  "bst_of_list \<in> measurable (count_space (lists A)) (tree_sigma (count_space A))"
  by (subst measurable_count_space_eq1)
    (auto simp: space_tree_sigma intro!: bst_of_list_trees)

lemma insort_wrt_measurable [measurable]:
  "(\<lambda>x. insort_wrt x xs) \<in> count_space (Pow (A \<times> A)) \<rightarrow>\<^sub>M count_space (lists A)"
  using con_assms by auto

lemma bst_of_list_sort_meaurable [measurable]:
  "(\<lambda>x. bst_of_list (sort_key x xs)) \<in> 
     Pi\<^sub>M (set xs) (\<lambda>i. borel::real measure) \<rightarrow>\<^sub>M tree_sigma (count_space A)"
proof -
  note measurable_linorder_from_keys_restrict'[measurable]
  have "(0::real) < 1"
    by auto
  then have [measurable]: "(\<lambda>x. bst_of_list (insort_wrt (linorder_from_keys (set xs) x) xs))
                      \<in> Pi\<^sub>M (set xs) (\<lambda>i. borel :: real measure) \<rightarrow>\<^sub>M tree_sigma (count_space A)"
    using con_assms by measurable
  show ?thesis
    by (subst insort_wrt_sort_key[symmetric]) (measurable, auto)
qed


text \<open>
  In a first step, we convert the bulk insertion operation to first choosing the
  priorities i.\,i.\,d.\ ahead of time and then inserting all the elements deterministically
  with their associated priority.
\<close>
lemma random_treap_fold:
  assumes "t \<in> space (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))"
  shows "rinss xs t A = distr (\<Pi>\<^sub>M x\<in>set xs. \<U> 0 1)
                              (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))
                              (\<lambda>p. foldl (\<lambda>t x. ins x (p x) t) t xs)"
proof -
  let ?U = "uniform_measure lborel {0::real..1}"
  have "set xs \<subseteq> space (count_space A)" "c \<in> set xs \<Longrightarrow> c \<in> space (count_space A)" for c
    using con_assms by auto
  then have *[intro]: "(\<lambda>p. foldl (\<lambda>t x. ins x (p x) t) t xs) \<in>
    Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<rightarrow>\<^sub>M tree_sigma (count_space A \<Otimes>\<^sub>M lborel)"
    if "t \<in> space (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))" for t
   using that con_assms by measurable
  have insR': 
    "insR x t A = ?U \<bind> (\<lambda>u. return (tree_sigma (count_space A \<Otimes>\<^sub>M lborel)) (ins x u t))"
    if "x \<in> A" "t \<in> space (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))" for t x
    using con_assms assms that by (auto simp add: bind_return_distr' \<U>_def)
  have "rinss xs t A = (\<Pi>\<^sub>M x\<in>set xs. ?U) \<bind>
     (\<lambda>p. return (tree_sigma (count_space A \<Otimes>\<^sub>M lborel)) (foldl (\<lambda>t x. ins x (p x) t) t xs))"
    using con_assms(2,3) assms proof (induction xs arbitrary: t)
  case Nil
  then show ?case
    by (intro measure_eqI) (auto simp add: space_PiM_empty emeasure_distr bind_return_distr')
next
  case (Cons x xs)
  note insR.simps[simp del]
  let ?treap_sigma  = "tree_sigma (count_space A \<Otimes>\<^sub>M lborel)"
  have [measurable]: "set xs \<subseteq> space (count_space A)" "x \<in> A"
                     "c \<in> A \<Longrightarrow> c \<in> space (count_space A)" for c
    using Cons by auto
  have [intro!]: "ins k p t \<in> space ?treap_sigma" if "t \<in> space ?treap_sigma" "k \<in> A"
    for k t and p::real
    using that
    by (auto intro!: ins_trees simp add: space_tree_sigma space_pair_measure)
  have [measurable]: "Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<in> space (prob_algebra (Pi\<^sub>M (set xs) (\<lambda>i. ?U)))"
    unfolding space_prob_algebra by (auto intro!: prob_space_uniform_measure prob_space_PiM)
  have [measurable]: "Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<in> space (subprob_algebra (Pi\<^sub>M (set xs) (\<lambda>i. ?U)))"
    unfolding space_subprob_algebra
    by (auto intro!: prob_space_imp_subprob_space prob_space_uniform_measure prob_space_PiM)
  have [measurable]: "(\<lambda>x. x) \<in> (?treap_sigma \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>i. ?U)) \<Otimes>\<^sub>M ?treap_sigma \<rightarrow>\<^sub>M
            (?treap_sigma \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>i. borel)) \<Otimes>\<^sub>M ?treap_sigma"
    by (auto intro!: measurable_ident_sets sets_pair_measure_cong sets_PiM_cong simp add: \<U>_def)
  have [simp]: "(\<lambda>w. Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<bind>
        (\<lambda>p. return ?treap_sigma (foldl (\<lambda>t x. ins x (p x) t) w xs)))
        \<in> ?treap_sigma \<rightarrow>\<^sub>M subprob_algebra ?treap_sigma"
  proof -
    have [measurable]: "c \<in> set xs \<Longrightarrow> c \<in> A" for c
      using Cons by auto
    show ?thesis
      using con_assms by measurable
  qed
  have [measurable]: "?U \<in> space (prob_algebra (?U))"
    by (simp add: prob_space_uniform_measure space_prob_algebra)
  have [measurable, intro]: "(\<lambda>t. rinss xs t A) \<in> ?treap_sigma \<rightarrow>\<^sub>M subprob_algebra ?treap_sigma"
    if "set xs \<subseteq> A" for xs
    using that proof (induction xs)
    case (Cons x xs)
    then have [measurable]: "x \<in> A" "set xs \<subseteq> A"
      by auto
    have [measurable]: "(\<lambda>y. x) \<in> tree_sigma (count_space A \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?U \<rightarrow>\<^sub>M count_space A"
      using Cons by measurable
    have [measurable]: "(\<lambda>x. x) \<in> ?treap_sigma \<Otimes>\<^sub>M ?U \<rightarrow>\<^sub>M ?treap_sigma \<Otimes>\<^sub>M borel"
      unfolding \<U>_def by auto
    have [measurable]: "(\<lambda>t. distr (?U) (tree_sigma (count_space A \<Otimes>\<^sub>M lborel)) (\<lambda>p. ins x p t))
    \<in> ?treap_sigma \<rightarrow>\<^sub>M subprob_algebra ?treap_sigma"
      using con_assms by (intro measurable_prob_algebraD) measurable
    from Cons show ?case
      unfolding rinss.simps insR.simps \<U>_def by measurable
  qed auto
  have [intro]: "(\<lambda>u. return ?treap_sigma (ins x u t)) \<in> ?U \<rightarrow>\<^sub>M subprob_algebra ?treap_sigma"
    using con_assms Cons by measurable
  have [simp]: "space (?U \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>x. ?U)) \<noteq> {}"
    by (simp add: prob_space.not_empty prob_space_PiM prob_space_pair prob_space_uniform_measure)
  from Cons have "rinss (x # xs) t A = (?U \<bind>
                                       (\<lambda>u. return ?treap_sigma (ins x u t))) \<bind>
                                       (\<lambda>t. rinss xs t A)"
    by (simp add: insR')
  also have "\<dots> = ?U \<bind> (\<lambda>u. return ?treap_sigma (ins x u t) \<bind> (\<lambda>t. rinss xs t A))"
    using con_assms Cons by (subst bind_assoc) auto
  also have "\<dots> = ?U \<bind> (\<lambda>u. rinss xs (ins x u t) A)"
    using con_assms Cons by (subst bind_return) auto
  also have "\<dots> = ?U \<bind>
                 (\<lambda>u. Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<bind>
                 (\<lambda>p. return ?treap_sigma (foldl (\<lambda>t x. ins x (p x) t) (ins x u t) xs)))"
    using Cons by (subst Cons) (auto simp add: treap_ins keys_ins)
  also have "\<dots> = ?U \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>x. ?U) \<bind>
                  (\<lambda>(u,p). return ?treap_sigma (foldl (\<lambda>t x. ins x (p x) t) (ins x u t) xs))"
  proof -
    have [measurable]: "pair_prob_space (?U) (Pi\<^sub>M (set xs) (\<lambda>x. ?U))"
      by (simp add: \<U>_def pair_prob_space_def pair_sigma_finite.intro prob_space_PiM 
          prob_space_imp_sigma_finite prob_space_uniform_measure)
    note this[unfolded \<U>_def, measurable]
    have [measurable]: "c \<in> set xs \<Longrightarrow> c \<in> A" for c
      using Cons by auto
    show ?thesis
      using con_assms Cons by (subst pair_prob_space.pair_measure_bind) measurable
  qed
  also have "\<dots> = distr (?U \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>x. ?U)) (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))
                  (\<lambda>(u, f). foldl (\<lambda>t x. ins x (f x) t) (ins x u t) xs)"
  proof -
    have [simp]: "c \<in> set xs \<Longrightarrow> c \<in> A" for c
      using Cons by auto
    have "(\<lambda>xa. foldl (\<lambda>t x. ins x (snd xa x) t) (ins x (fst xa) t) xs) = 
          (\<lambda>(u, f). foldl (\<lambda>t x. ins x (f x) t) (ins x u t) xs)"
      by (auto simp add: case_prod_beta')
    then show ?thesis
      using con_assms Cons by (subst case_prod_beta', subst bind_return_distr') measurable
  qed
  also have
    "\<dots> = distr (?U \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>i. ?U)) ?treap_sigma
          (\<lambda>f. foldl (\<lambda>t y. ins y (if y = x then fst f else snd f y) t) (ins x (fst f) t) xs)"
  proof -
    have "foldl (\<lambda>t y. ins y (snd f y) t) (ins x (fst f) t) xs =
          foldl (\<lambda>t y. ins y (if y = x then fst f else snd f y) t) (ins x (fst f) t) xs" for f
      using Cons by (intro foldl_cong) auto
    then show ?thesis
      by (auto simp add: case_prod_beta')
  qed
  also have "\<dots> = distr (?U \<Otimes>\<^sub>M Pi\<^sub>M (set xs) (\<lambda>i. ?U)) (Pi\<^sub>M (insert x (set xs)) (\<lambda>i. ?U)) 
                          (\<lambda>(r, f). f(x := r)) \<bind>
                          (\<lambda>p. return ?treap_sigma (foldl (\<lambda>t x. ins x (p x) t) (ins x (p x) t) xs))"
    using con_assms  Cons 
    by (subst bind_distr_return) (measurable, auto simp add: case_prod_beta')
  also have "\<dots> = Pi\<^sub>M (insert x (set xs)) (\<lambda>x. ?U) \<bind>
                  (\<lambda>p. return ?treap_sigma (foldl (\<lambda>t x. ins x (p x) t) (ins x (p x) t) xs))"
    by (subst distr_pair_PiM_eq_PiM) (auto simp add: prob_space_uniform_measure)
  finally show ?case
    by (simp)
qed
  then show ?thesis
    using assms by (subst bind_return_distr'[symmetric]) (auto simp add: bind_return_distr')
qed

corollary random_treap_fold_Leaf:
  shows "rinss xs Leaf A =
         distr (\<Pi>\<^sub>M x\<in>set xs. \<U> 0 1)
               (tree_sigma (count_space A \<Otimes>\<^sub>M lborel))
               (\<lambda>p. foldl (\<lambda>t x. ins x (p x) t) Leaf xs)"
  by (auto simp add: random_treap_fold)

text \<open>
  Next, we show that additionally forgetting the priorities in the end will yield
  the same distribution as inserting the elements into a BST by ascending priority.
\<close>
lemma rinss_bst_of_list:
      "distr (rinss xs Leaf A) (tree_sigma (count_space A)) (map_tree fst) =
       distr (Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1)) (tree_sigma (count_space A))
             (\<lambda>p. bst_of_list (sort_key p xs))" (is "?lhs = ?rhs")
proof -
  have [measurable]: "set xs \<subseteq> space (count_space A)"
    "c \<in> set xs \<Longrightarrow> c \<in> space (count_space A)" for c
    using con_assms by auto
  have [simp]: "map_tree fst \<circ> (\<lambda>p. foldl (\<lambda>t x. ins x (p x) t) \<langle>\<rangle> xs)
                \<in> Pi\<^sub>M (set xs) (\<lambda>x. uniform_measure lborel {0::real..1}) \<rightarrow>\<^sub>M
                  tree_sigma (count_space A)"
    unfolding \<U>_def map_tree_primrec using con_assms by measurable
  have "AE f in Pi\<^sub>M (set xs) (\<lambda>i. \<U> 0 1). inj_on f (set xs)"
    unfolding \<U>_def by (rule almost_everywhere_avoid_finite) auto
  then have "AE f in Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1).
             map_tree fst (foldl (\<lambda>t (k,p). ins k p t) \<langle>\<rangle> (map (\<lambda>x. (x, f x)) xs)) =
             bst_of_list (sort_key f xs)"
    by (eventually_elim) (use con_assms in \<open>auto simp add: fold_ins_bst_of_list\<close>)
  then have [simp]: "AE f in Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1).
             map_tree fst (foldl (\<lambda>t k. ins k (f k) t) \<langle>\<rangle> xs) = bst_of_list (sort_key f xs)"
    by (simp add: foldl_map)
  have "?lhs = distr (Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1)) (tree_sigma (count_space A))
                     (map_tree fst \<circ> (\<lambda>p. foldl (\<lambda>t x. ins x (p x) t) \<langle>\<rangle> xs))"
    unfolding random_treap_fold_Leaf \<U>_def map_tree_primrec using con_assms
    by (subst distr_distr) measurable
  also have "\<dots> = ?rhs"
    by (intro distr_cong_AE) (auto simp add: \<U>_def)
  finally show ?thesis .
qed

text \<open>
  This in turn is the same as choosing a random permutation of the input list and
  inserting the elements into a BST in that order.
\<close>
lemma lborel_permutations_of_set_bst_of_list:
  shows "distr (Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1)) (tree_sigma (count_space A))
               (\<lambda>p. bst_of_list (sort_key p xs)) =
         distr (random_perm xs) (tree_sigma (count_space A)) bst_of_list" (is "?lhs = ?rhs")
proof -
  have [measurable]: "(0::real) < 1"
    by auto
  have "insort_wrt R xs = insort_wrt R (remdups xs)" for R
    using con_assms distinct_remdups_id by metis
  then have *: "insort_wrt R xs = sorted_wrt_list_of_set R (set xs)"
    if "linorder_on (set xs) R" for R
    using that by (subst sorted_wrt_list_set) auto
  have [measurable]: "(\<lambda>x. x) \<in> count_space (permutations_of_set (set xs)) \<rightarrow>\<^sub>M count_space (lists A)"
    using con_assms permutations_of_setD by fastforce
  have [measurable]: "(\<lambda>R. insort_wrt R xs) \<in>
                      count_space (Pow (A \<times> A)) \<rightarrow>\<^sub>M count_space (permutations_of_set (set xs))"
    using con_assms by (simp add: permutations_of_setI)
  have "?lhs 
   = distr (Pi\<^sub>M (set xs) (\<lambda>x. \<U> 0 1)) (tree_sigma (count_space A))
           (\<lambda>p. bst_of_list (insort_wrt (linorder_from_keys (set xs) p) xs))"
    unfolding Let_def by (simp add: insort_wrt_sort_key)
 also have "\<dots> = 
  distr (distr (Pi\<^sub>M (set xs) (\<lambda>x. uniform_measure lborel {0::real..1}))
    (count_space (Pow (A \<times> A))) (linorder_from_keys (set xs)))
  (tree_sigma (count_space A)) (\<lambda>R. bst_of_list (insort_wrt R xs))"
   unfolding \<U>_def using con_assms by (subst distr_distr) (measurable, metis comp_apply)
  also have "\<dots> = 
  distr (uniform_measure (count_space (Pow (A \<times> A))) (linorders_on (set xs)))
        (tree_sigma (count_space A)) (\<lambda>R. bst_of_list (insort_wrt R xs))"
    using con_assms by (subst random_linorder_by_prios) auto
  also have "\<dots> = distr (distr (uniform_measure (count_space (Pow (A \<times> A))) (linorders_on (set xs)))
                               (count_space (permutations_of_set (set xs))) (\<lambda>R. insort_wrt R xs))
                        (tree_sigma (count_space A)) bst_of_list"
    by (subst distr_distr) (measurable, metis comp_apply)
  also have "\<dots> = distr (uniform_measure (count_space (permutations_of_set (set xs)))
                          ((\<lambda>R. insort_wrt R xs) ` linorders_on (set xs)))
                    (tree_sigma (count_space A)) bst_of_list"
  proof -
    have "bij_betw (\<lambda>R. insort_wrt R xs) (linorders_on (set xs)) (permutations_of_set (set xs))"
      by (subst bij_betw_cong, fastforce simp add: * linorders_on_def bij_betw_cong)
         (use bij_betw_linorders_on' in blast)
    then have "inj_on (\<lambda>R. insort_wrt R xs) (linorders_on (set xs))"
      by (rule bij_betw_imp_inj_on)
    then have "distr (uniform_measure (count_space (Pow (A \<times> A))) (linorders_on (set xs)))
                     (count_space (permutations_of_set (set xs))) (\<lambda>R. insort_wrt R xs)
               = uniform_measure (count_space (permutations_of_set (set xs)))
                                 ((\<lambda>R. insort_wrt R xs) ` linorders_on (set xs))"
      using con_assms by (intro distr_uniform_measure_count_space_inj)
        (auto simp add: linorders_on_def linorder_on_def refl_on_def)
    then show ?thesis by auto
  qed
  also have "\<dots> = distr (random_perm xs) (tree_sigma (count_space A)) bst_of_list"
  proof -
    have "((\<lambda>R. insort_wrt R xs) ` linorders_on (set xs)) = permutations_of_set (set xs)"
      by (intro bij_betw_imp_surj_on, subst bij_betw_cong, rule *)
         (fastforce simp add: linorders_on_def,  use bij_betw_linorders_on' in blast)
   then show ?thesis by (simp add: random_perm_def)
 qed
  finally show ?thesis .
qed

lemma distr_bst_of_list_tree_sigma_count_space: "
   distr (random_perm xs) (tree_sigma (count_space A)) bst_of_list =
     distr (random_perm xs) (count_space (trees A)) bst_of_list"
  using con_assms by (intro distr_cong)  (auto intro!: sets_tree_sigma_count_space)

text \<open>
  This is the same as a \emph{random BST}.
\<close>
lemma distr_bst_of_list_random_bst: "
  distr (random_perm xs) (count_space (trees A)) bst_of_list =
    restrict_space (random_bst (set xs)) (trees A)" (is "?lhs = ?rhs")
proof -
  have "?rhs = restrict_space (distr (uniform_measure (count_space UNIV)
                 (permutations_of_set (set xs))) (count_space UNIV) bst_of_list) (trees A)"
    by (auto simp: random_bst_altdef measure_pmf_of_set map_pmf_rep_eq)
  also have "distr (uniform_measure (count_space UNIV) (permutations_of_set (set xs))) 
                   (count_space UNIV) bst_of_list = 
               distr (random_perm xs) (count_space UNIV) bst_of_list"
    by (intro distr_restrict) (auto simp: random_perm_def)
  also have "restrict_space \<dots> (trees A) =
               distr (random_perm xs) (count_space (trees A)) bst_of_list"
    using con_assms
    by (subst restrict_distr)
       (auto simp: random_perm_def bst_of_list_trees restrict_count_space permutations_of_setD)
  finally show ?thesis ..
qed

text \<open>
  We put everything together and obtain our main result:
\<close>
theorem rinss_random_bst:
  "distr (rinss xs \<langle>\<rangle> A) (tree_sigma (count_space A)) (map_tree fst) =
     restrict_space (measure_pmf (random_bst (set xs))) (trees A)"
  by (simp only: rinss_bst_of_list lborel_permutations_of_set_bst_of_list
                 distr_bst_of_list_tree_sigma_count_space distr_bst_of_list_random_bst)

end
end