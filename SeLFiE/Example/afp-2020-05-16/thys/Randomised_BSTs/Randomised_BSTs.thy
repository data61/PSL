(*
  File:      Randomised_BSTs.thy
  Author:    Manuel Eberl (TU München)

  A formalisation of the randomised binary search trees described by Martínez & Roura.
*)
section \<open>Randomised Binary Search Trees\<close>
theory Randomised_BSTs
  imports "Random_BSTs.Random_BSTs" "Monad_Normalisation.Monad_Normalisation"
begin

subsection \<open>Auxiliary facts\<close>

text \<open>
  First of all, we need some fairly simple auxiliary lemmas.
\<close>

lemma return_pmf_if: "return_pmf (if P then a else b) = (if P then return_pmf a else return_pmf b)"
  by simp

context
begin

interpretation pmf_as_function .

lemma True_in_set_bernoulli_pmf_iff [simp]:
  "True \<in> set_pmf (bernoulli_pmf p) \<longleftrightarrow> p > 0"
  by transfer auto

lemma False_in_set_bernoulli_pmf_iff [simp]:
  "False \<in> set_pmf (bernoulli_pmf p) \<longleftrightarrow> p < 1"
  by transfer auto

end

lemma in_set_pmf_of_setD: "x \<in> set_pmf (pmf_of_set A) \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x \<in> A"
  by (subst (asm) set_pmf_of_set) auto

lemma random_bst_reduce:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
     random_bst A = do {x \<leftarrow> pmf_of_set A; l \<leftarrow> random_bst {y\<in>A. y < x};
                        r \<leftarrow> random_bst {y\<in>A. y > x}; return_pmf \<langle>l, x, r\<rangle>}"
  by (subst random_bst.simps) auto

lemma pmf_bind_bernoulli:
  assumes "x \<in> {0..1}"
  shows   "pmf (bernoulli_pmf x \<bind> f) y = x * pmf (f True) y + (1 - x) * pmf (f False) y"
  using assms by (simp add: pmf_bind)

lemma vimage_bool_pair:
  "f -` A = (\<Union>x\<in>{True, False}. \<Union>y\<in>{True, False}. if f (x, y) \<in> A then {(x, y)} else {})"
  (is "?lhs = ?rhs") unfolding set_eq_iff
proof
  fix x :: "bool \<times> bool"
  obtain a b where [simp]: "x = (a, b)" by (cases x)
  show "x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs"
    by (cases a; cases b) auto
qed

lemma Leaf_in_set_random_bst_iff [simp]:
  "Leaf \<in> set_pmf (random_bst A) \<longleftrightarrow> A = {} \<or> \<not>finite A"
  by (subst random_bst.simps) auto

lemma bst_insert [intro]: "bst t \<Longrightarrow> bst (Tree_Set.insert x t)"
  by (simp add: bst_iff_sorted_wrt_less inorder_insert sorted_ins_list)

lemma bst_bst_of_list [intro]: "bst (bst_of_list xs)"
proof -
  have "bst (fold Tree_Set.insert xs t)" if "bst t" for t
    using that
  proof (induction xs arbitrary: t)
    case (Cons y xs)
    show ?case by (auto intro!: Cons bst_insert)
  qed auto
  thus ?thesis by (simp add: bst_of_list_altdef)
qed

lemma bst_random_bst:
  assumes "t \<in> set_pmf (random_bst A)"
  shows   "bst t"
proof (cases "finite A")
  case True
  have "random_bst A = map_pmf bst_of_list (pmf_of_set (permutations_of_set A))"
    by (rule random_bst_altdef) fact+
  also have "set_pmf \<dots> = bst_of_list ` permutations_of_set A"
    using True by auto
  finally show ?thesis using assms by auto
next
  case False
  hence "random_bst A = return_pmf \<langle>\<rangle>"
    by (simp add: random_bst.simps)
  with assms show ?thesis by simp
qed

lemma set_random_bst:
  assumes "t \<in> set_pmf (random_bst A)" "finite A"
  shows   "set_tree t = A"
proof -
  have "random_bst A = map_pmf bst_of_list (pmf_of_set (permutations_of_set A))"
    by (rule random_bst_altdef) fact+
  also have "set_pmf \<dots> = bst_of_list ` permutations_of_set A"
    using assms by auto
  finally show ?thesis using assms
    by (auto simp: permutations_of_setD)
qed

lemma isin_bst:
  assumes "bst t"
  shows   "isin t x \<longleftrightarrow> x \<in> set_tree t"
  using assms
  by (subst isin_set) (auto simp: bst_iff_sorted_wrt_less)

lemma isin_random_bst:
  assumes "finite A" "t \<in> set_pmf (random_bst A)"
  shows   "isin t x \<longleftrightarrow> x \<in> A"
proof -
  from assms have "bst t" by (auto dest: bst_random_bst)
  with assms show ?thesis by (simp add: isin_bst set_random_bst)
qed

lemma card_3way_split:
  assumes "x \<in> (A :: 'a :: linorder set)" "finite A"
  shows   "card A = card {y\<in>A. y < x} + card {y\<in>A. y > x} + 1"
proof -
  from assms have "A = insert x ({y\<in>A. y < x} \<union> {y\<in>A. y > x})"
    by auto
  also have "card \<dots> = card {y\<in>A. y < x} + card {y\<in>A. y > x} + 1"
    using assms by (subst card_insert_disjoint) (auto intro: card_Un_disjoint)
  finally show ?thesis .
qed


text \<open>
  The following theorem allows splitting a uniformly random choice from a union of two disjoint
  sets to first tossing a coin to decide on one of the constituent sets and then chooing an 
  element from it uniformly at random.
\<close>
lemma pmf_of_set_union_split:
  assumes "finite A" "finite B" "A \<inter> B = {}" "A \<union> B \<noteq> {}"
  assumes "p = card A / (card A + card B)"
  shows   "do {b \<leftarrow> bernoulli_pmf p; if b then pmf_of_set A else pmf_of_set B} = pmf_of_set (A \<union> B)"
            (is "?lhs = ?rhs")
proof (rule pmf_eqI)
  fix x :: 'a
  from assms have p: "p \<in> {0..1}"
    by (auto simp: divide_simps assms(5) split: if_splits)

  have "pmf ?lhs x = pmf (pmf_of_set A) x * p + pmf (pmf_of_set B) x * (1 - p)"
    unfolding pmf_bind using p by (subst integral_bernoulli_pmf) auto
  also consider "x \<in> A" "B \<noteq> {}" | "x \<in> B" "A \<noteq> {}" | "x \<in> A" "B = {}" | "x \<in> B" "A = {}" |
                "x \<notin> A" "x \<notin> B"
    using assms by auto
  hence "pmf (pmf_of_set A) x * p + pmf (pmf_of_set B) x * (1 - p) = pmf ?rhs x"
  proof cases
    assume "x \<notin> A" "x \<notin> B"
    thus ?thesis using assms by (cases "A = {}"; cases "B = {}") auto
  next
    assume "x \<in> A" and [simp]: "B \<noteq> {}"
    have "pmf (pmf_of_set A) x * p + pmf (pmf_of_set B) x * (1 - p) = p / real (card A)"
      using \<open>x \<in> A\<close> assms(1-4) by (subst (1 2) pmf_of_set) (auto simp: indicator_def)
    also have "\<dots> = pmf ?rhs x"
      using assms \<open>x \<in> A\<close> by (subst pmf_of_set) (auto simp: card_Un_disjoint)
    finally show ?thesis .
  next
    assume "x \<in> B" and [simp]: "A \<noteq> {}"
    from assms have *: "card (A \<union> B) > 0" by (subst card_gt_0_iff) auto
    have "pmf (pmf_of_set A) x * p + pmf (pmf_of_set B) x * (1 - p) = (1 - p) / real (card B)"
      using \<open>x \<in> B\<close> assms(1-4) by (subst (1 2) pmf_of_set) (auto simp: indicator_def)
    also have "\<dots> = pmf ?rhs x"
      using assms \<open>x \<in> B\<close> *
      by (subst pmf_of_set) (auto simp: card_Un_disjoint assms(5) divide_simps)
    finally show ?thesis .
  qed (insert assms(1-4), auto simp: assms(5))
  finally show "pmf ?lhs x = pmf ?rhs x" .
qed

lemma pmf_of_set_split_inter_diff:
  assumes "finite A" "finite B" "A \<noteq> {}" "B \<noteq> {}"
  assumes "p = card (A \<inter> B) / card B"
  shows   "do {b \<leftarrow> bernoulli_pmf p; if b then pmf_of_set (A \<inter> B) else pmf_of_set (B - A)} =
             pmf_of_set B" (is "?lhs = ?rhs")
proof -
  have eq: "B = (A \<inter> B) \<union> (B - A)" by auto
  have card_eq: "card B = card (A \<inter> B) + card (B - A)"
    using assms by (subst eq, subst card_Un_disjoint) auto
  have "?lhs = pmf_of_set ((A \<inter> B) \<union> (B - A))"
    using assms by (intro pmf_of_set_union_split) (auto simp: card_eq)
  with eq show ?thesis by simp
qed

text \<open>
  Similarly to the above rule, we can split up a uniformly random choice from the disjoint
  union of three sets. This could be done with two coin flips, but it is more convenient to
  choose a natural number uniformly at random instead and then do a case distinction on it.
\<close>
lemma pmf_of_set_3way_split:
  fixes f g h :: "'a \<Rightarrow> 'b pmf"
  assumes "finite A" "A \<noteq> {}" "A1 \<inter> A2 = {}" "A1 \<inter> A3 = {}" "A2 \<inter> A3 = {}" "A1 \<union> A2 \<union> A3 = A"
  shows   "do {x \<leftarrow> pmf_of_set A; if x \<in> A1 then f x else if x \<in> A2 then g x else h x} =
           do {i \<leftarrow> pmf_of_set {..<card A};
               if i < card A1 then pmf_of_set A1 \<bind> f
               else if i < card A1 + card A2 then pmf_of_set A2 \<bind> g
               else pmf_of_set A3 \<bind> h}" (is "?lhs = ?rhs")
proof (intro pmf_eqI)
  fix x :: 'b
  define m n l where "m = card A1" and "n = card A2" and "l = card A3"
  have [simp]: "finite A1" "finite A2" "finite A3"
    by (rule finite_subset[of _ A]; use assms in force)+
  from assms have card_pos: "card A > 0" by auto
  have A_eq: "A = A1 \<union> A2 \<union> A3" using assms by simp
  have card_A_eq: "card A = card A1 + card A2 + card A3"
    using assms unfolding A_eq by (subst card_Un_disjoint, simp, simp, force)+ auto
  have card_A_eq': "{..<card A} = {..<m} \<union> {m..<m + n} \<union> {m + n..<card A}"
    by (auto simp: m_def n_def card_A_eq)
  let ?M = "\<lambda>i. if i < m then pmf_of_set A1 \<bind> f else if i < m + n then
                  pmf_of_set A2 \<bind> g else pmf_of_set A3 \<bind> h"

  have card_times_pmf_of_set_bind:
      "card X * pmf (pmf_of_set X \<bind> f) x = (\<Sum>y\<in>X. pmf (f y) x)"
      if "finite X" for X :: "'a set" and f :: "'a \<Rightarrow> 'b pmf"
    using that by (cases "X = {}") (auto simp: pmf_bind_pmf_of_set)  

  have "pmf ?rhs x = (\<Sum>i<card A. pmf (?M i) x) / card A"
    (is "_ = ?S / _") using assms card_pos unfolding m_def n_def
    by (subst pmf_bind_pmf_of_set) auto
  also have "?S = (real m * pmf (pmf_of_set A1 \<bind> f) x +
                   real n * pmf (pmf_of_set A2 \<bind> g) x +
                   real l * pmf (pmf_of_set A3 \<bind> h) x)" unfolding card_A_eq'
    by (subst sum.union_disjoint, simp, simp, force)+ (auto simp: card_A_eq m_def n_def l_def)
  also have "\<dots> = (\<Sum>y\<in>A1. pmf (f y) x) + (\<Sum>y\<in>A2. pmf (g y) x) + (\<Sum>y\<in>A3. pmf (h y) x)"
    unfolding m_def n_def l_def by (subst (1 2 3) card_times_pmf_of_set_bind) auto
  also have "\<dots> = (\<Sum>y\<in>A1 \<union> A2 \<union> A3.
                       pmf (if y \<in> A1 then f y else if y \<in> A2 then g y else h y) x)"
    using assms(1-5)
    by (subst sum.union_disjoint, simp, simp, force)+
       (intro arg_cong2[of _ _ _ _ "(+)"] sum.cong, auto)
  also have "\<dots> / card A = pmf ?lhs x"
    using assms by (simp add: pmf_bind_pmf_of_set)
  finally show "pmf ?lhs x = pmf ?rhs x"
    unfolding m_def n_def l_def card_A_eq ..
qed


subsection \<open>Partitioning a BST\<close>

text \<open>
  The split operation takes a search parameter \<open>x\<close> and partitions a BST into two BSTs
  containing all the values that are smaller than \<open>x\<close> and those that are greater than \<open>x\<close>,
  respectively. Note that \<open>x\<close> need not be an element of the tree.
\<close>

fun split_bst :: "'a :: linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<times> 'a tree" where
  "split_bst _ \<langle>\<rangle> = (\<langle>\<rangle>, \<langle>\<rangle>)"
| "split_bst x \<langle>l, y, r\<rangle> =
     (if y < x then
        case split_bst x r of (t1, t2) \<Rightarrow> (\<langle>l, y, t1\<rangle>, t2)
      else if y > x then
        case split_bst x l of (t1, t2) \<Rightarrow> (t1, \<langle>t2, y, r\<rangle>)
      else
        (l, r))"

fun split_bst' :: "'a :: linorder \<Rightarrow> 'a tree \<Rightarrow> bool \<times> 'a tree \<times> 'a tree" where
  "split_bst' _ \<langle>\<rangle> = (False, \<langle>\<rangle>, \<langle>\<rangle>)"
| "split_bst' x \<langle>l, y, r\<rangle> =
     (if y < x then
        case split_bst' x r of (b, t1, t2) \<Rightarrow> (b, \<langle>l, y, t1\<rangle>, t2)
      else if y > x then
        case split_bst' x l of (b, t1, t2) \<Rightarrow> (b, t1, \<langle>t2, y, r\<rangle>)
      else
        (True, l, r))"

lemma split_bst'_altdef: "split_bst' x t = (isin t x, split_bst x t)"
  by (induction x t rule: split_bst.induct) (auto simp: case_prod_unfold)

lemma fst_split_bst' [simp]: "fst (split_bst' x t) = isin t x"
  and snd_split_bst' [simp]: "snd (split_bst' x t) = split_bst x t"
  by (simp_all add: split_bst'_altdef)


lemma size_fst_split_bst [termination_simp]: "size (fst (split_bst x t)) \<le> size t"
  by (induction t) (auto simp: case_prod_unfold)

lemma size_snd_split_bst [termination_simp]: "size (snd (split_bst x t)) \<le> size t"
  by (induction t) (auto simp: case_prod_unfold)

lemmas size_split_bst = size_fst_split_bst size_snd_split_bst

lemma set_split_bst1: "bst t \<Longrightarrow> set_tree (fst (split_bst x t)) = {y \<in> set_tree t. y < x}"
  by (induction t) (auto split: prod.splits)

lemma set_split_bst2: "bst t \<Longrightarrow> set_tree (snd (split_bst x t)) = {y \<in> set_tree t. y > x}"
  by (induction t) (auto split: prod.splits)

lemma bst_split_bst1 [intro]: "bst t \<Longrightarrow> bst (fst (split_bst x t))"
  by (induction t) (auto simp: case_prod_unfold set_split_bst1)

lemma bst_split_bst2 [intro]: "bst t \<Longrightarrow> bst (snd (split_bst x t))"
  by (induction t) (auto simp: case_prod_unfold set_split_bst2)

text \<open>
  Splitting a random BST produces two random BSTs:
\<close>
theorem split_random_bst:
  assumes "finite A"
  shows   "map_pmf (split_bst x) (random_bst A) =
             pair_pmf (random_bst {y\<in>A. y < x}) (random_bst {y\<in>A. y > x})"
  using assms
proof (induction A rule: random_bst.induct)
  case (1 A)
  define A\<^sub>1 A\<^sub>2 where "A\<^sub>1 = {y\<in>A. y < x}" and "A\<^sub>2 = {y\<in>A. y > x}"
  have [simp]: "\<not>x \<in> A\<^sub>2" if "x \<in> A\<^sub>1" for x using that by (auto simp: A\<^sub>1_def A\<^sub>2_def)
  from \<open>finite A\<close> have [simp]: "finite A\<^sub>1" "finite A\<^sub>2" by (auto simp: A\<^sub>1_def A\<^sub>2_def)
  include monad_normalisation

  show ?case
  proof (cases "A = {}")
    case True
    thus ?thesis by (auto simp: pair_return_pmf1)
  next
    case False

    have "map_pmf (split_bst x) (random_bst A) =
            do {y \<leftarrow> pmf_of_set A;
                if y < x then
                  do {
                    l \<leftarrow> random_bst {z\<in>A. z < y};
                    (t1, t2) \<leftarrow> map_pmf (split_bst x) (random_bst {z\<in>A. z > y});
                    return_pmf (\<langle>l, y, t1\<rangle>, t2)
                  }
                else if y > x then
                  do {
                    (t1, t2) \<leftarrow> map_pmf (split_bst x) (random_bst {z\<in>A. z < y});
                    r \<leftarrow> random_bst {z\<in>A. z > y};
                    return_pmf (t1, (\<langle>t2, y, r\<rangle>))
                  }
                else
                  do {
                    l \<leftarrow> random_bst {z\<in>A. z < y};
                    r \<leftarrow> random_bst {z\<in>A. z > y};
                    return_pmf (l, r)
                  }
               }"
      using "1.prems" False
      by (subst random_bst.simps)
         (simp add: map_bind_pmf bind_map_pmf return_pmf_if case_prod_unfold cong: if_cong)
    also have "\<dots> = do {y \<leftarrow> pmf_of_set A;
                        if y < x then
                          do {
                            l \<leftarrow> random_bst {z\<in>A. z < y};
                            (t1, t2) \<leftarrow> pair_pmf (random_bst {z\<in>{z\<in>A. z > y}. z < x})
                                                 (random_bst {z\<in>{z\<in>A. z > y}. z > x});
                            return_pmf (\<langle>l, y, t1\<rangle>, t2)
                          }
                        else if y > x then
                          do {
                            (t1, t2) \<leftarrow> pair_pmf (random_bst {z\<in>{z\<in>A. z < y}. z < x})
                                                 (random_bst {z\<in>{z\<in>A. z < y}. z > x});
                            r \<leftarrow> random_bst {z\<in>A. z > y};
                            return_pmf (t1, (\<langle>t2, y, r\<rangle>))
                          }
                         else 
                           do {
                             l \<leftarrow> random_bst {z\<in>A. z < y};
                             r \<leftarrow> random_bst {z\<in>A. z > y};
                             return_pmf (l, r)
                           }
                       }"
      using \<open>finite A\<close> and \<open>A \<noteq> {}\<close> thm "1.IH"
      by (intro bind_pmf_cong if_cong refl "1.IH") auto
    also have "\<dots> = do {y \<leftarrow> pmf_of_set A;
                        if y < x then
                          do {
                            l \<leftarrow> random_bst {z\<in>A. z < y};
                            t1 \<leftarrow> random_bst {z\<in>{z\<in>A. z > y}. z < x};
                            t2 \<leftarrow> random_bst {z\<in>{z\<in>A. z > y}. z > x};
                            return_pmf (\<langle>l, y, t1\<rangle>, t2)
                          }
                        else if y > x then
                          do {
                            t1 \<leftarrow> random_bst {z\<in>{z\<in>A. z < y}. z < x};
                            t2 \<leftarrow> random_bst {z\<in>{z\<in>A. z < y}. z > x};
                            r \<leftarrow> random_bst {z\<in>A. z > y};
                            return_pmf (t1, (\<langle>t2, y, r\<rangle>))
                          }
                         else 
                           do {
                             l \<leftarrow> random_bst {z\<in>A. z < y};
                             r \<leftarrow> random_bst {z\<in>A. z > y};
                             return_pmf (l, r)
                           }
                       }"
      by (simp add: pair_pmf_def cong: if_cong)
    also have "\<dots> = do {y \<leftarrow> pmf_of_set A;
                        if y \<in> A\<^sub>1 then
                          do {
                            l \<leftarrow> random_bst {z\<in>A\<^sub>1. z < y};
                            t1 \<leftarrow> random_bst {z\<in>A\<^sub>1. z > y};
                            t2 \<leftarrow> random_bst A\<^sub>2;
                            return_pmf (\<langle>l, y, t1\<rangle>, t2)
                          }
                        else if y \<in> A\<^sub>2 then
                          do {
                            t1 \<leftarrow> random_bst A\<^sub>1;
                            t2 \<leftarrow> random_bst {z\<in>A\<^sub>2. z < y};
                            r \<leftarrow> random_bst {z\<in>A\<^sub>2. z > y};
                            return_pmf (t1, (\<langle>t2, y, r\<rangle>))
                          }
                         else
                           pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)
                       }"
      using \<open>finite A\<close> \<open>A \<noteq> {}\<close>
      by (intro bind_pmf_cong refl if_cong arg_cong[of _ _ random_bst])
         (auto simp: A\<^sub>1_def A\<^sub>2_def pair_pmf_def)
    also have "\<dots> = do {i \<leftarrow> pmf_of_set {..<card A};
                        if i < card A\<^sub>1 then
                          do {
                            y \<leftarrow> pmf_of_set A\<^sub>1;
                            l \<leftarrow> random_bst {z\<in>A\<^sub>1. z < y};
                            t1 \<leftarrow> random_bst {z\<in>A\<^sub>1. z > y};
                            t2 \<leftarrow> random_bst A\<^sub>2;
                            return_pmf (\<langle>l, y, t1\<rangle>, t2)
                          }
                        else if i < card A\<^sub>1 + card A\<^sub>2 then
                          do {
                            y \<leftarrow> pmf_of_set A\<^sub>2;
                            t1 \<leftarrow> random_bst A\<^sub>1;
                            t2 \<leftarrow> random_bst {z\<in>A\<^sub>2. z < y};
                            r \<leftarrow> random_bst {z\<in>A\<^sub>2. z > y};
                            return_pmf (t1, (\<langle>t2, y, r\<rangle>))
                          }
                         else do {
                           y \<leftarrow> pmf_of_set (if x \<in> A then {x} else {});
                           pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)
                         }
                       }" using \<open>finite A\<close> \<open>A \<noteq> {}\<close>
      by (intro pmf_of_set_3way_split) (auto simp: A\<^sub>1_def A\<^sub>2_def not_less_iff_gr_or_eq)
    also have "\<dots> = do {i \<leftarrow> pmf_of_set {..<card A};
                        if i < card A\<^sub>1 then
                          pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)
                        else if i < card A\<^sub>1 + card A\<^sub>2 then
                          pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)
                         else 
                          pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)
                       }"
      using \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    proof (intro bind_pmf_cong refl if_cong, goal_cases)
      case (1 i)
      hence "A\<^sub>1 \<noteq> {}" by auto
      thus ?case using \<open>finite A\<close> by (simp add: pair_pmf_def random_bst_reduce)
    next
      case (2 i)
      hence "A\<^sub>2 \<noteq> {}" by auto
      thus ?case using \<open>finite A\<close> by (simp add: pair_pmf_def random_bst_reduce)
    qed auto
    also have "\<dots> = pair_pmf (random_bst A\<^sub>1) (random_bst A\<^sub>2)"
      by (simp cong: if_cong)
    finally show ?thesis by (simp add: A\<^sub>1_def A\<^sub>2_def)
  qed
qed


subsection \<open>Joining\<close>

text \<open>
  The ``join'' operation computes the union of two BSTs \<open>l\<close> and \<open>r\<close> where all the values in
  \<open>l\<close> are stricly smaller than those in \<open>r\<close>.
\<close>
fun mrbst_join :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree pmf" where
  "mrbst_join t1 t2 =
     (if t1 = \<langle>\<rangle> then return_pmf t2
      else if t2 = \<langle>\<rangle> then return_pmf t1
      else do {
        b \<leftarrow> bernoulli_pmf (size t1 / (size t1 + size t2));
        if b then
          (case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2))
        else
          (case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l))
      })"

lemma mrbst_join_Leaf_left [simp]: "mrbst_join \<langle>\<rangle> = return_pmf"
  by (simp add: fun_eq_iff)

lemma mrbst_join_Leaf_right [simp]: "mrbst_join t \<langle>\<rangle> = return_pmf t"
  by (simp add: fun_eq_iff)

lemma mrbst_join_reduce:
  "t1 \<noteq> \<langle>\<rangle> \<Longrightarrow> t2 \<noteq> \<langle>\<rangle> \<Longrightarrow> mrbst_join t1 t2 =
     do {
        b \<leftarrow> bernoulli_pmf (size t1 / (size t1 + size t2));
        if b then
          (case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2))
        else
          (case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l))
      }"
  by (subst mrbst_join.simps) auto

lemmas [simp del] = mrbst_join.simps

lemma
  assumes "t' \<in> set_pmf (mrbst_join t1 t2)" "bst t1" "bst t2"
  assumes "\<And>x y. x \<in> set_tree t1 \<Longrightarrow> y \<in> set_tree t2 \<Longrightarrow> x < y"
  shows   bst_mrbst_join: "bst t'"
    and   set_mrbst_join: "set_tree t' = set_tree t1 \<union> set_tree t2"
proof -
  have "bst t' \<and> set_tree t' = set_tree t1 \<union> set_tree t2"
  using assms
  proof (induction "size t1 + size t2" arbitrary: t1 t2 t' rule: less_induct)
    case (less t1 t2 t')
    show ?case
    proof (cases "t1 = \<langle>\<rangle> \<or> t2 = \<langle>\<rangle>")
      case False
      hence "t' \<in> set_pmf (case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (Node l x) (mrbst_join r t2)) \<or>
             t' \<in> set_pmf (case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l))"
        using less.prems by (subst (asm) mrbst_join_reduce) (auto split: if_splits)
      thus ?thesis
      proof
        assume "t' \<in> set_pmf (case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (Node l x) (mrbst_join r t2))"
        then obtain l x r r'
          where *: "t1 = \<langle>l, x, r\<rangle>" "r' \<in> set_pmf (mrbst_join r t2)" "t' = \<langle>l, x, r'\<rangle>"
          using False by (auto split: tree.splits)
        from * and less.prems have "bst r' \<and> set_tree r' = set_tree r \<union> set_tree t2"
          by (intro less) auto
        with * and less.prems show ?thesis by auto
      next
        assume "t' \<in> set_pmf (case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l))"
        then obtain l x r l'
          where *: "t2 = \<langle>l, x, r\<rangle>" "l' \<in> set_pmf (mrbst_join t1 l)" "t' = \<langle>l', x, r\<rangle>"
          using False by (auto split: tree.splits)
        from * and less.prems have "bst l' \<and> set_tree l' = set_tree t1 \<union> set_tree l"
          by (intro less) auto
        with * and less.prems show ?thesis by auto
      qed
    qed (insert less.prems, auto)
  qed
  thus "bst t'" "set_tree t' = set_tree t1 \<union> set_tree t2" by auto
qed

text \<open>
  Joining two random BSTs that satisfy the necessary preconditions again yields a random BST.
\<close>
theorem mrbst_join_correct:
  fixes A B :: "'a :: linorder set"
  assumes "finite A" "finite B" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x < y"
  shows   "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_join t1 t2} = random_bst (A \<union> B)"
proof -
  from assms have "finite (A \<union> B)" by simp
  from this and assms show ?thesis
  proof (induction "A \<union> B" arbitrary: A B rule: finite_psubset_induct)
    case (psubset A B)
    define m n where "m = card A" and "n = card B"
    define p where "p = m / (m + n)"

    include monad_normalisation
    show ?case
    proof (cases "A = {} \<or> B = {}")
      case True
      thus ?thesis by auto
    next
      case False
      have AB: "A \<noteq> {}" "B \<noteq> {}" "finite A" "finite B"
        using False psubset.prems by auto
      have p_pos: "A \<noteq> {}" if "p > 0" using \<open>finite A\<close> that
        using AB by (auto simp: p_def m_def n_def)
      have p_lt1: "B \<noteq> {}" if "p < 1"
        using AB by (auto simp: p_def m_def n_def)

      have "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_join t1 t2} =
            do {t1 \<leftarrow> random_bst A;
                t2 \<leftarrow> random_bst B;
                b \<leftarrow> bernoulli_pmf (size t1 / (size t1 + size t2));
                if b then
                  case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2)
                else
                  case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l)
               }"
        using AB
        by (intro bind_pmf_cong refl, subst mrbst_join_reduce) auto
      also have "\<dots> = do {t1 \<leftarrow> random_bst A;
                          t2 \<leftarrow> random_bst B;
                          b \<leftarrow> bernoulli_pmf p;
                          if b then
                            case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2)
                          else
                            case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l)
                         }"
        using AB by (intro bind_pmf_cong refl arg_cong[of _ _ bernoulli_pmf])
                    (auto simp: p_def m_def n_def size_random_bst)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          t1 \<leftarrow> random_bst A;
                          t2 \<leftarrow> random_bst B;
                          case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2)
                        } else do {
                          t1 \<leftarrow> random_bst A;
                          t2 \<leftarrow> random_bst B;
                          case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l)
                        }
                      }"
        by simp
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                          r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          x \<leftarrow> pmf_of_set B;
                          l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                          r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                      }"
      proof (intro bind_pmf_cong refl if_cong, goal_cases)
        case (1 b)
        hence [simp]: "A \<noteq> {}" using p_pos by auto
        have "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B;
                  case t1 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>l, x, r'\<rangle>) (mrbst_join r t2)} =
              do {
                x \<leftarrow> pmf_of_set A;
                l \<leftarrow> random_bst {y\<in>A. y < x};
                r \<leftarrow> do {r \<leftarrow> random_bst {y\<in>A. y > x}; t2 \<leftarrow> random_bst B; mrbst_join r t2};
                return_pmf \<langle>l, x, r\<rangle>
              }"
          using AB by (subst random_bst_reduce) (auto simp: map_pmf_def)
        also have "\<dots> = do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {y\<in>A. y < x};
                          r \<leftarrow> random_bst ({y\<in>A. y > x} \<union> B);
                          return_pmf \<langle>l, x, r\<rangle>
                        }"
          using AB psubset.prems 
          by (intro bind_pmf_cong refl psubset arg_cong[of _ _ random_bst]) auto
        also have "\<dots> = do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                          r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        }"
          using AB psubset.prems
          by (intro bind_pmf_cong refl arg_cong[of _ _ random_bst]; force)
        finally show ?case .
      next
        case (2 b)
        hence [simp]: "B \<noteq> {}" using p_lt1 by auto
        have "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B;
                  case t2 of \<langle>l, x, r\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', x, r\<rangle>) (mrbst_join t1 l)} =
              do {
                x \<leftarrow> pmf_of_set B;
                l \<leftarrow> do {t1 \<leftarrow> random_bst A; l \<leftarrow> random_bst {y\<in>B. y < x}; mrbst_join t1 l};
                r \<leftarrow> random_bst {y\<in>B. y > x};
                return_pmf \<langle>l, x, r\<rangle>
              }"
          using AB by (subst random_bst_reduce) (auto simp: map_pmf_def)
        also have "\<dots> = do {
                          x \<leftarrow> pmf_of_set B;
                          l \<leftarrow> random_bst (A \<union> {y\<in>B. y < x});
                          r \<leftarrow> random_bst {y\<in>B. y > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        }"
          using AB psubset.prems 
          by (intro bind_pmf_cong refl psubset arg_cong[of _ _ random_bst]) auto
        also have "\<dots> = do {
                          x \<leftarrow> pmf_of_set B;
                          l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                          r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        }"
          using AB psubset.prems
          by (intro bind_pmf_cong refl arg_cong[of _ _ random_bst]; force)
        finally show ?case .
      qed
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        x \<leftarrow> (if b then pmf_of_set A else pmf_of_set B);
                        l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                        r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                        return_pmf \<langle>l, x, r\<rangle>
                      }"
        by (intro bind_pmf_cong) simp_all
      also have "\<dots> = do {
                        x \<leftarrow> do {b \<leftarrow> bernoulli_pmf p; if b then pmf_of_set A else pmf_of_set B};
                        l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                        r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                        return_pmf \<langle>l, x, r\<rangle>
                      }"
        by simp
      also have "do {b \<leftarrow> bernoulli_pmf p; if b then pmf_of_set A else pmf_of_set B} =
                   pmf_of_set (A \<union> B)"
        using AB psubset.prems by (intro pmf_of_set_union_split) (auto simp: p_def m_def n_def) 
      also have "do {
                   x \<leftarrow> pmf_of_set (A \<union> B);
                   l \<leftarrow> random_bst {y\<in>A \<union> B. y < x};
                   r \<leftarrow> random_bst {y\<in>A \<union> B. y > x};
                   return_pmf \<langle>l, x, r\<rangle>
                 } = random_bst (A \<union> B)"
        using AB by (intro random_bst_reduce [symmetric]) auto
      finally show ?thesis .
    qed
  qed
qed


subsection \<open>Pushdown\<close>

text \<open>
  The ``push down'' operation ``forgets'' information about the root of a tree in the following
  sense: It takes a non-empty tree whose root is some known fixed value and whose children are
  random BSTs and shuffles the root in such a way that the resulting tree is a random BST.
\<close>
fun mrbst_push_down :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree pmf" where
  "mrbst_push_down l x r =
     do {
       k \<leftarrow> pmf_of_set {0..size l + size r};
       if k < size l then
         case l of
           \<langle>ll, y, lr\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>ll, y, r'\<rangle>) (mrbst_push_down lr x r)
       else if k < size l + size r then
         case r of
           \<langle>rl, y, rr\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', y, rr\<rangle>) (mrbst_push_down l x rl)
       else
         return_pmf \<langle>l, x, r\<rangle>
     }"

lemmas [simp del] = mrbst_push_down.simps

lemma
  assumes "t' \<in> set_pmf (mrbst_push_down t1 x t2)" "bst t1" "bst t2"
  assumes "\<And>y. y \<in> set_tree t1 \<Longrightarrow> y < x" "\<And>y. y \<in> set_tree t2 \<Longrightarrow> y > x"
  shows   bst_mrbst_push_down: "bst t'"
    and   set_mrbst_push_down: "set_tree t' = {x} \<union> set_tree t1 \<union> set_tree t2"
proof -
  have "bst t' \<and> set_tree t' = {x} \<union> set_tree t1 \<union> set_tree t2"
  using assms
  proof (induction "size t1 + size t2" arbitrary: t1 t2 t' rule: less_induct)
    case (less t1 t2 t')
    have "t1 \<noteq> \<langle>\<rangle> \<and> t' \<in> set_pmf (case t1 of \<langle>l, y, r\<rangle> \<Rightarrow>
                            map_pmf (Node l y) (mrbst_push_down r x t2)) \<or>
          t2 \<noteq> \<langle>\<rangle> \<and> t' \<in> set_pmf (case t2 of \<langle>l, y, r\<rangle> \<Rightarrow>
                            map_pmf (\<lambda>l'. \<langle>l', y, r\<rangle>) (mrbst_push_down t1 x l)) \<or>
          t' = \<langle>t1, x, t2\<rangle>"
      using less.prems by (subst (asm) mrbst_push_down.simps) (auto split: if_splits)
    thus ?case
    proof (elim disjE, goal_cases)
      case 1
      then obtain l y r r'
        where *: "t1 = \<langle>l, y, r\<rangle>" "r' \<in> set_pmf (mrbst_push_down r x t2)" "t' = \<langle>l, y, r'\<rangle>"
        by (auto split: tree.splits)
      from * and less.prems have "bst r' \<and> set_tree r' = {x} \<union> set_tree r \<union> set_tree t2"
        by (intro less) auto
      with * and less.prems show ?case by force
    next
      case 2
      then obtain l y r l'
        where *: "t2 = \<langle>l, y, r\<rangle>" "l' \<in> set_pmf (mrbst_push_down t1 x l)" "t' = \<langle>l', y, r\<rangle>"
        by (auto split: tree.splits)
      from * and less.prems have "bst l' \<and> set_tree l' = {x} \<union> set_tree t1 \<union> set_tree l"
        by (intro less) auto
      with * and less.prems show ?case by force
    qed (insert less.prems, auto)
  qed
  thus "bst t'" "set_tree t' = {x} \<union> set_tree t1 \<union> set_tree t2" by auto
qed

theorem mrbst_push_down_correct:
  fixes A B :: "'a :: linorder set"
  assumes "finite A" "finite B" "\<And>y. y \<in> A \<Longrightarrow> y < x" "\<And>y. y \<in> B \<Longrightarrow> x < y"
  shows   "do {l \<leftarrow> random_bst A; r \<leftarrow> random_bst B; mrbst_push_down l x r} =
             random_bst ({x} \<union> A \<union> B)"
proof -
  from assms have "finite (A \<union> B)" by simp
  from this and assms show ?thesis
  proof (induction "A \<union> B" arbitrary: A B rule: finite_psubset_induct)
    case (psubset A B)
    define m n where "m = card A" and "n = card B"
    have A_ne: "A \<noteq> {}" if "m > 0"
      using that by (auto simp: m_def)
    have B_ne: "B \<noteq> {}" if "n > 0"
      using that by (auto simp: n_def)

    include monad_normalisation
    have "do {l \<leftarrow> random_bst A; r \<leftarrow> random_bst B; mrbst_push_down l x r} =
          do {l \<leftarrow> random_bst A;
              r \<leftarrow> random_bst B;
              k \<leftarrow> pmf_of_set {0..m + n};
              if k < m then
                case l of \<langle>ll, y, lr\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>ll, y, r'\<rangle>) (mrbst_push_down lr x r)
              else if k < m + n then
                case r of \<langle>rl, y, rr\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', y, rr\<rangle>) (mrbst_push_down l x rl)
              else
                return_pmf \<langle>l, x, r\<rangle>
             }"
      using psubset.prems
      by (subst mrbst_push_down.simps, intro bind_pmf_cong refl)
         (auto simp: size_random_bst m_def n_def)
    also have "\<dots> = do {k \<leftarrow> pmf_of_set {0..m + n};
                        if k < m then do {
                          l \<leftarrow> random_bst A;
                          r \<leftarrow> random_bst B;
                          case l of \<langle>ll, y, lr\<rangle> \<Rightarrow> map_pmf (\<lambda>r'. \<langle>ll, y, r'\<rangle>) (mrbst_push_down lr x r)
                        } else if k < m + n then do {
                          l \<leftarrow> random_bst A;
                          r \<leftarrow> random_bst B;
                          case r of \<langle>rl, y, rr\<rangle> \<Rightarrow> map_pmf (\<lambda>l'. \<langle>l', y, rr\<rangle>) (mrbst_push_down l x rl)
                        } else do {
                          l \<leftarrow> random_bst A;
                          r \<leftarrow> random_bst B;
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                       }"
      by (simp cong: if_cong)
    also have "\<dots> = do {k \<leftarrow> pmf_of_set {0..m + n};
                        if k < m then do {
                          y \<leftarrow> pmf_of_set A;
                          ll \<leftarrow> random_bst {z\<in>A. z < y};
                          r' \<leftarrow> do {lr \<leftarrow> random_bst {z\<in>A. z > y};
                                    r \<leftarrow> random_bst B;
                                    mrbst_push_down lr x r};
                          return_pmf \<langle>ll, y, r'\<rangle>
                        } else if k < m + n then do {
                          y \<leftarrow> pmf_of_set B;
                          l' \<leftarrow> do {l \<leftarrow> random_bst A;
                                    rl \<leftarrow> random_bst {z\<in>B. z < y};
                                    mrbst_push_down l x rl};
                          rr \<leftarrow> random_bst {z\<in>B. z > y};
                          return_pmf \<langle>l', y, rr\<rangle>
                        } else do {
                          l \<leftarrow> random_bst A;
                          r \<leftarrow> random_bst B;
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                       }"
    proof (intro bind_pmf_cong refl if_cong, goal_cases)
      case (1 k)
      hence "A \<noteq> {}" by (auto simp: m_def)
      with \<open>finite A\<close> show ?case by (simp add: random_bst_reduce map_pmf_def)
    next
      case (2 k)
      hence "B \<noteq> {}" by (auto simp: m_def n_def)
      with \<open>finite B\<close> show ?case by (simp add: random_bst_reduce map_pmf_def)
    qed
    also have "\<dots> = do {k \<leftarrow> pmf_of_set {0..m + n};
                        if k < m then do {
                          y \<leftarrow> pmf_of_set A;
                          ll \<leftarrow> random_bst {z\<in>A. z < y};
                          r' \<leftarrow> random_bst ({x} \<union> {z\<in>A. z > y} \<union> B);
                          return_pmf \<langle>ll, y, r'\<rangle>
                        } else if k < m + n then do {
                          y \<leftarrow> pmf_of_set B;
                          l' \<leftarrow> random_bst ({x} \<union> A \<union> {z\<in>B. z < y});
                          rr \<leftarrow> random_bst {z\<in>B. z > y};
                          return_pmf \<langle>l', y, rr\<rangle>
                        } else do {
                          l \<leftarrow> random_bst A;
                          r \<leftarrow> random_bst B;
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                       }"
      using psubset.prems A_ne B_ne
    proof (intro bind_pmf_cong refl if_cong psubset)
      fix k y assume "k < m" "y \<in> set_pmf (pmf_of_set A)"
      thus "{z\<in>A. z > y} \<union> B \<subset> A \<union> B"
        using psubset.prems A_ne by (fastforce dest!: in_set_pmf_of_setD)
    next
      fix k y assume "\<not>k < m" "k < m + n" "y \<in> set_pmf (pmf_of_set B)"
      thus "A \<union> {z\<in>B. z < y} \<subset> A \<union> B"
        using psubset.prems B_ne by (fastforce dest!: in_set_pmf_of_setD)
    qed auto
    also have "\<dots> = do {k \<leftarrow> pmf_of_set {0..m + n};
                        if k < m then do {
                          y \<leftarrow> pmf_of_set A;
                          ll \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                          r' \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                          return_pmf \<langle>ll, y, r'\<rangle>
                        } else if k < m + n then do {
                          y \<leftarrow> pmf_of_set B;
                          l' \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                          rr \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                          return_pmf \<langle>l', y, rr\<rangle>
                        } else do {
                          l \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                       }"
      using psubset.prems A_ne B_ne
      by (intro bind_pmf_cong if_cong refl arg_cong[of _ _ random_bst];
          force dest: psubset.prems(3,4))
    also have "\<dots> = do {k \<leftarrow> pmf_of_set {0..m + n};
                        if k < m then do {
                          y \<leftarrow> pmf_of_set A;
                          ll \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                          r' \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                          return_pmf \<langle>ll, y, r'\<rangle>
                        } else if k < m + n then do {
                          y \<leftarrow> pmf_of_set B;
                          l' \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                          rr \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                          return_pmf \<langle>l', y, rr\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set {x};
                          l \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                          r \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                          return_pmf \<langle>l, x, r\<rangle>
                        }
                       }" (is "_ = ?X {0..m+n}")
      by (simp add: pmf_of_set_singleton cong: if_cong)
    also have "{0..m + n} = {..<card (A \<union> B \<union> {x})}" using psubset.prems
      by (subst card_Un_disjoint, simp, simp, force)+
         (auto simp: m_def n_def)
    also have "?X \<dots> = do {y \<leftarrow> pmf_of_set ({x} \<union> A \<union> B);
                           l \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z < y};
                           r \<leftarrow> random_bst {z\<in>{x} \<union> A \<union> B. z > y};
                           return_pmf \<langle>l, y, r\<rangle>}"
      unfolding m_def n_def using psubset.prems
      by (subst pmf_of_set_3way_split [symmetric])
         (auto dest!: psubset.prems(3,4) cong: if_cong intro: bind_pmf_cong)
    also have "\<dots> = random_bst ({x} \<union> A \<union> B)"
      using psubset.prems by (simp add: random_bst_reduce)
    finally show ?case .
  qed
qed

lemma mrbst_push_down_correct':
  assumes "finite (A :: 'a :: linorder set)" "x \<in> A"
  shows   "do {l \<leftarrow> random_bst {y\<in>A. y < x}; r \<leftarrow> random_bst {y\<in>A. y > x}; mrbst_push_down l x r} =
             random_bst A" (is "?lhs = ?rhs")
proof -
  have "?lhs = random_bst ({x} \<union> {y\<in>A. y < x} \<union> {y\<in>A. y > x})"
    using assms by (intro mrbst_push_down_correct) auto
  also have "{x} \<union> {y\<in>A. y < x} \<union> {y\<in>A. y > x} = A"
    using assms by auto
  finally show ?thesis .
qed


subsection \<open>Intersection and Difference\<close>

text \<open>
  The algorithms for intersection and difference of two trees are almost identical; the only
  difference is that the ``if'' statement at the end of the recursive case is flipped. We
  therefore introduce a generic intersection/difference operation first and prove its correctness
  to avoid duplication.
\<close>
fun mrbst_inter_diff where
  "mrbst_inter_diff _ \<langle>\<rangle> _ = return_pmf \<langle>\<rangle>"
| "mrbst_inter_diff b \<langle>l1, x, r1\<rangle> t2 =
     (case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
          l \<leftarrow> mrbst_inter_diff b l1 l2;
          r \<leftarrow> mrbst_inter_diff b r1 r2;
          if sep = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
        })"

lemma mrbst_inter_diff_reduce:
  "mrbst_inter_diff b \<langle>l1, x, r1\<rangle> =
     (\<lambda>t2. case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
           l \<leftarrow> mrbst_inter_diff b l1 l2;
           r \<leftarrow> mrbst_inter_diff b r1 r2;
           if sep = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
         })"
  by (rule ext) simp

lemma mrbst_inter_diff_Leaf_left [simp]:
  "mrbst_inter_diff b \<langle>\<rangle> = (\<lambda>_. return_pmf \<langle>\<rangle>)"
  by (simp add: fun_eq_iff)

lemma mrbst_inter_diff_Leaf_right [simp]:
  "mrbst_inter_diff b (t1 :: 'a :: linorder tree) \<langle>\<rangle> = return_pmf (if b then \<langle>\<rangle> else t1)"
  by (induction t1) (auto simp: bind_return_pmf)

lemma
  fixes t1 t2 :: "'a :: linorder tree" and b :: bool
  defines "setop \<equiv> (if b then (\<inter>) else (-) :: 'a set \<Rightarrow> _)"
  assumes "t' \<in> set_pmf (mrbst_inter_diff b t1 t2)" "bst t1" "bst t2"
  shows   bst_mrbst_inter_diff: "bst t'"
    and   set_mrbst_inter_diff: "set_tree t' = setop (set_tree t1) (set_tree t2)"
proof -
  write setop (infixl "\<diamondop>" 80)
  have "bst t' \<and> set_tree t' = set_tree t1 \<diamondop> set_tree t2"
  using assms(2-)
  proof (induction t1 arbitrary: t2 t')
    case (Node l1 x r1 t2)
    note bst = \<open>bst \<langle>l1, x, r1\<rangle>\<close> \<open>bst t2\<close>
    define l2 r2 where "l2 = fst (split_bst x t2)" and "r2 = snd (split_bst x t2)"
    obtain l r
      where lr: "l \<in> set_pmf (mrbst_inter_diff b l1 l2)" "r \<in> set_pmf (mrbst_inter_diff b r1 r2)"
        and t': "t' \<in> (if x \<in> set_tree t2 \<longleftrightarrow> b then {\<langle>l, x, r\<rangle>} else set_pmf (mrbst_join l r))"
      using Node.prems by (force simp: case_prod_unfold l2_def r2_def isin_bst split: if_splits)
    from lr have lr': "bst l \<and> set_tree l = set_tree l1 \<diamondop> set_tree l2"
                      "bst r \<and> set_tree r = set_tree r1 \<diamondop> set_tree r2"
      using Node.prems by (intro Node.IH; force simp: l2_def r2_def)+

    have "set_tree t' = set_tree l \<union> set_tree r \<union> (if x \<in> set_tree t2 \<longleftrightarrow> b then {x} else {})"
    proof (cases "x \<in> set_tree t2 \<longleftrightarrow> b")
      case False
      have "x < y" if "x \<in> set_tree l" "y \<in> set_tree r" for x y
        using that lr' bst by (force simp: setop_def split: if_splits)
      hence set_t': "set_tree t' = set_tree l \<union> set_tree r"
        using t' set_mrbst_join[of t' l r] False lr' by auto
      with False show ?thesis by simp
    qed (use t' in auto)
    also have "\<dots> = set_tree \<langle>l1, x, r1\<rangle> \<diamondop> set_tree t2"
      using lr' bst by (auto simp: setop_def l2_def r2_def set_split_bst1 set_split_bst2)
    finally have "set_tree t' = set_tree \<langle>l1, x, r1\<rangle> \<diamondop> set_tree t2" .
    moreover from lr' t' bst have "bst t'"
      by (force split: if_splits simp: setop_def intro!: bst_mrbst_join[of t' l r])
    ultimately show ?case by auto
  qed (auto simp: setop_def)
  thus "bst t'" and "set_tree t' = set_tree t1 \<diamondop> set_tree t2" by auto
qed

theorem mrbst_inter_diff_correct:
  fixes A B :: "'a :: linorder set" and b :: bool
  defines "setop \<equiv> (if b then (\<inter>) else (-) :: 'a set \<Rightarrow> _)"
  assumes "finite A" "finite B"
  shows   "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_inter_diff b t1 t2} =
             random_bst (setop A B)"
  using assms(2-)
proof (induction A arbitrary: B rule: finite_psubset_induct)
  case (psubset A B)
  write setop (infixl "\<diamondop>" 80)
  include monad_normalisation
  show ?case
  proof (cases "A = {}")
    case True
    thus ?thesis by (auto simp: setop_def)
  next
    case False
    define R1 R2 where "R1 = (\<lambda>x. random_bst {y\<in>A. y < x})" "R2 = (\<lambda>x. random_bst {y\<in>A. y > x})"

    have A_eq: "A = (A \<inter> B) \<union> (A - B)" by auto
    have card_A_eq: "card A = card (A \<inter> B) + card (A - B)"
      using \<open>finite A\<close> \<open>finite B\<close> by (subst A_eq, subst card_Un_disjoint) auto
    have eq: "pmf_of_set A =
                do {b \<leftarrow> bernoulli_pmf (card (A \<inter> B) / card A);
                    if b then pmf_of_set (A \<inter> B) else pmf_of_set (A - B)}"
      using psubset.prems False \<open>finite A\<close> A_eq card_A_eq
      by (subst A_eq, intro pmf_of_set_union_split [symmetric]) auto
    have "card A > 0"
      using \<open>finite A\<close> \<open>A \<noteq> {}\<close> by (subst card_gt_0_iff) auto
    have not_subset: "\<not>A \<subseteq> B" if "card (A \<inter> B) < card A"
    proof
      assume "A \<subseteq> B"
      hence "A \<inter> B = A" by auto
      with that show False by simp
    qed

    have "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_inter_diff b t1 t2} =
          do {
            x \<leftarrow> pmf_of_set A;
            l1 \<leftarrow> random_bst {y\<in>A. y < x};
            r1 \<leftarrow> random_bst {y\<in>A. y > x};
            t2 \<leftarrow> random_bst B;
            let (l2, r2) = split_bst x t2;
            l \<leftarrow> mrbst_inter_diff b l1 l2;
            r \<leftarrow> mrbst_inter_diff b r1 r2;
            if isin t2 x = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
          }"
      using \<open>finite A\<close> \<open>A \<noteq> {}\<close>
      by (subst random_bst_reduce)
         (auto simp: mrbst_inter_diff_reduce map_pmf_def split_bst'_altdef)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l1 \<leftarrow> random_bst {y\<in>A. y < x};
                      r1 \<leftarrow> random_bst {y\<in>A. y > x};
                      t2 \<leftarrow> random_bst B;
                      let (l2, r2) = split_bst x t2;
                      l \<leftarrow> mrbst_inter_diff b l1 l2;
                      r \<leftarrow> mrbst_inter_diff b r1 r2;
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      unfolding Let_def case_prod_unfold using \<open>finite B\<close>
      by (intro bind_pmf_cong refl) (auto simp: isin_random_bst)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l1 \<leftarrow> random_bst {y\<in>A. y < x};
                      r1 \<leftarrow> random_bst {y\<in>A. y > x};
                      (l2, r2) \<leftarrow> map_pmf (split_bst x) (random_bst B);
                      l \<leftarrow> mrbst_inter_diff b l1 l2;
                      r \<leftarrow> mrbst_inter_diff b r1 r2;
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      by (simp add: Let_def map_pmf_def)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l1 \<leftarrow> random_bst {y\<in>A. y < x};
                      r1 \<leftarrow> random_bst {y\<in>A. y > x};
                      (l2, r2) \<leftarrow> pair_pmf (random_bst {y\<in>B. y < x}) (random_bst {y\<in>B. y > x});
                      l \<leftarrow> mrbst_inter_diff b l1 l2;
                      r \<leftarrow> mrbst_inter_diff b r1 r2;
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      by (intro bind_pmf_cong refl split_random_bst \<open>finite B\<close>)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l1 \<leftarrow> R1 x;
                      r1 \<leftarrow> R2 x;
                      l2 \<leftarrow> random_bst {y\<in>B. y < x};
                      r2 \<leftarrow> random_bst {y\<in>B. y > x};
                      l \<leftarrow> mrbst_inter_diff b l1 l2;
                      r \<leftarrow> mrbst_inter_diff b r1 r2;
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      unfolding pair_pmf_def bind_assoc_pmf R1_R2_def by simp
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l \<leftarrow> do {l1 \<leftarrow> R1 x; l2 \<leftarrow> random_bst {y\<in>B. y < x}; mrbst_inter_diff b l1 l2};
                      r \<leftarrow> do {r1 \<leftarrow> R2 x; r2 \<leftarrow> random_bst {y\<in>B. y > x}; mrbst_inter_diff b r1 r2};
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      unfolding bind_assoc_pmf by (intro bind_pmf_cong[OF refl]) simp
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      l \<leftarrow> random_bst ({y\<in>A. y < x} \<diamondop> {y\<in>B. y < x});
                      r \<leftarrow> random_bst ({y\<in>A. y > x} \<diamondop> {y\<in>B. y > x});
                      if x \<in> B = b then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
                    }"
      using \<open>finite A\<close> \<open>finite B\<close> \<open>A \<noteq> {}\<close> unfolding R1_R2_def
      by (intro bind_pmf_cong refl psubset.IH) auto
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      if x \<in> B = b then do {
                        l \<leftarrow> random_bst ({y\<in>A. y < x} \<diamondop> {y\<in>B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A. y > x} \<diamondop> {y\<in>B. y > x});
                        return_pmf \<langle>l, x, r\<rangle>
                      } else do {
                        l \<leftarrow> random_bst ({y\<in>A. y < x} \<diamondop> {y\<in>B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A. y > x} \<diamondop> {y\<in>B. y > x});
                        mrbst_join l r
                      }
                    }"
      by simp
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      if x \<in> B = b then do {
                        l \<leftarrow> random_bst ({y\<in>A. y < x} \<diamondop> {y\<in>B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A. y > x} \<diamondop> {y\<in>B. y > x});
                        return_pmf \<langle>l, x, r\<rangle>
                      } else do {
                        random_bst ({y\<in>A. y < x} \<diamondop> {y\<in>B. y < x} \<union> {y\<in>A. y > x} \<diamondop> {y\<in>B. y > x})
                      }
                    }"
      using \<open>finite A\<close> \<open>finite B\<close>
      by (intro bind_pmf_cong refl mrbst_join_correct if_cong) (auto simp: setop_def)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      if x \<in> B = b then do {
                        l \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y > x});
                        return_pmf \<langle>l, x, r\<rangle>
                      } else do {
                        random_bst (A \<diamondop> B)
                      }
                    }" (is "_ = pmf_of_set A \<bind> ?f")
      using \<open>finite A\<close> \<open>A \<noteq> {}\<close>
      by (intro bind_pmf_cong refl if_cong arg_cong[of _ _ random_bst])
         (auto simp: order.strict_iff_order setop_def)
    also have "\<dots> = do {
                      b' \<leftarrow> bernoulli_pmf (card (A \<inter> B) / card A);
                      x \<leftarrow> (if b' then pmf_of_set (A \<inter> B) else pmf_of_set (A - B));
                      if b' = b then do {
                        l \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y > x});
                        return_pmf \<langle>l, x, r\<rangle>
                      } else do {
                        random_bst (A \<diamondop> B)
                      }
                    }"
      unfolding bind_assoc_pmf eq using \<open>card A > 0\<close> \<open>finite A\<close> \<open>finite B\<close> not_subset
      by (intro bind_pmf_cong refl if_cong)
         (auto intro: bind_pmf_cong split: if_splits simp: divide_simps card_gt_0_iff
               dest!: in_set_pmf_of_setD)
    also have "\<dots> = do {
                      b' \<leftarrow> bernoulli_pmf (card (A \<inter> B) / card A);
                      if b' = b then do {
                        x \<leftarrow> pmf_of_set (A \<diamondop> B);
                        l \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y < x});
                        r \<leftarrow> random_bst ({y\<in>A \<diamondop> B. y > x});
                        return_pmf \<langle>l, x, r\<rangle>
                      } else do {
                        random_bst (A \<diamondop> B)
                      }
                    }"
      by (intro bind_pmf_cong) (auto simp: setop_def)
    also have "\<dots> = do {
                      b' \<leftarrow> bernoulli_pmf (card (A \<inter> B) / card A);
                      if b' = b then do {
                        random_bst (A \<diamondop> B)
                      } else do {
                        random_bst (A \<diamondop> B)
                      }
                    }"
      using \<open>finite A\<close> \<open>finite B\<close> \<open>A \<noteq> {}\<close> not_subset \<open>card A > 0\<close>
      by (intro bind_pmf_cong refl if_cong random_bst_reduce [symmetric])
         (auto simp: setop_def field_simps)
    also have "\<dots> = random_bst (A \<diamondop> B)" by simp
    finally show ?thesis .
  qed
qed


text \<open>
  We now derive the intersection and difference from the generic operation:
\<close>

fun mrbst_inter where
  "mrbst_inter \<langle>\<rangle> _ = return_pmf \<langle>\<rangle>"
| "mrbst_inter \<langle>l1, x, r1\<rangle> t2 =
     (case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
          l \<leftarrow> mrbst_inter l1 l2;
          r \<leftarrow> mrbst_inter r1 r2;
          if sep then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
        })"

lemma mrbst_inter_Leaf_left [simp]:
  "mrbst_inter \<langle>\<rangle> = (\<lambda>_. return_pmf \<langle>\<rangle>)"
  by (simp add: fun_eq_iff)

lemma mrbst_inter_Leaf_right [simp]:
  "mrbst_inter (t1 :: 'a :: linorder tree) \<langle>\<rangle> = return_pmf \<langle>\<rangle>"
  by (induction t1) (auto simp: bind_return_pmf)

lemma mrbst_inter_reduce:
  "mrbst_inter \<langle>l1, x, r1\<rangle> =
     (\<lambda>t2. case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
           l \<leftarrow> mrbst_inter l1 l2;
           r \<leftarrow> mrbst_inter r1 r2;
           if sep then return_pmf \<langle>l, x, r\<rangle> else mrbst_join l r
         })"
  by (rule ext) simp

lemma mrbst_inter_altdef: "mrbst_inter = mrbst_inter_diff True"
proof (intro ext)
  fix t1 t2 :: "'a tree"
  show "mrbst_inter t1 t2 = mrbst_inter_diff True t1 t2"
    by (induction t1 arbitrary: t2) auto
qed

corollary
  fixes t1 t2 :: "'a :: linorder tree"
  assumes "t' \<in> set_pmf (mrbst_inter t1 t2)" "bst t1" "bst t2"
  shows   bst_mrbst_inter: "bst t'"
    and   set_mrbst_inter: "set_tree t' = set_tree t1 \<inter> set_tree t2"
  using bst_mrbst_inter_diff[of t' True t1 t2] set_mrbst_inter_diff[of t' True t1 t2] assms
  by (simp_all add: mrbst_inter_altdef)

corollary mrbst_inter_correct:
  fixes A B :: "'a :: linorder set"
  assumes "finite A" "finite B"
  shows   "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_inter t1 t2} = random_bst (A \<inter> B)"
  using assms unfolding mrbst_inter_altdef by (subst mrbst_inter_diff_correct) simp_all


fun mrbst_diff where
  "mrbst_diff \<langle>\<rangle> _ = return_pmf \<langle>\<rangle>"
| "mrbst_diff \<langle>l1, x, r1\<rangle> t2 =
     (case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
          l \<leftarrow> mrbst_diff l1 l2;
          r \<leftarrow> mrbst_diff r1 r2;
          if sep then mrbst_join l r else return_pmf \<langle>l, x, r\<rangle>
        })"

lemma mrbst_diff_Leaf_left [simp]:
  "mrbst_diff \<langle>\<rangle> = (\<lambda>_. return_pmf \<langle>\<rangle>)"
  by (simp add: fun_eq_iff)

lemma mrbst_diff_Leaf_right [simp]:
  "mrbst_diff (t1 :: 'a :: linorder tree) \<langle>\<rangle> = return_pmf t1"
  by (induction t1) (auto simp: bind_return_pmf)

lemma mrbst_diff_reduce:
  "mrbst_diff \<langle>l1, x, r1\<rangle> =
     (\<lambda>t2. case split_bst' x t2 of (sep, l2, r2) \<Rightarrow>
        do {
           l \<leftarrow> mrbst_diff l1 l2;
           r \<leftarrow> mrbst_diff r1 r2;
           if sep then mrbst_join l r else return_pmf \<langle>l, x, r\<rangle>
         })"
  by (rule ext) simp

lemma If_not: "(if \<not>b then x else y) = (if b then y else x)"
  by auto

lemma mrbst_diff_altdef: "mrbst_diff = mrbst_inter_diff False"
proof (intro ext)
  fix t1 t2 :: "'a tree"
  show "mrbst_diff t1 t2 = mrbst_inter_diff False t1 t2"
    by (induction t1 arbitrary: t2) (auto simp: If_not)
qed

corollary
  fixes t1 t2 :: "'a :: linorder tree"
  assumes "t' \<in> set_pmf (mrbst_diff t1 t2)" "bst t1" "bst t2"
  shows   bst_mrbst_diff: "bst t'"
    and   set_mrbst_diff: "set_tree t' = set_tree t1 - set_tree t2"
  using bst_mrbst_inter_diff[of t' False t1 t2] set_mrbst_inter_diff[of t' False t1 t2] assms
  by (simp_all add: mrbst_diff_altdef)

corollary mrbst_diff_correct:
  fixes A B :: "'a :: linorder set"
  assumes "finite A" "finite B"
  shows   "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_diff t1 t2} = random_bst (A - B)"
  using assms unfolding mrbst_diff_altdef by (subst mrbst_inter_diff_correct) simp_all


subsection \<open>Union\<close>

text \<open>
  The algorithm for the union of two trees is by far the most complicated one. It involves a 
\<close>

(*<*)
context
  notes
    case_prod_unfold [termination_simp]
    if_splits [split]
begin
(*>*)

fun mrbst_union where
  "mrbst_union \<langle>\<rangle> t2 = return_pmf t2"
| "mrbst_union t1 \<langle>\<rangle> = return_pmf t1"
| "mrbst_union \<langle>l1, x, r1\<rangle> \<langle>l2, y, r2\<rangle> =
     do {
       let m = size \<langle>l1, x, r1\<rangle>; let n = size \<langle>l2, y, r2\<rangle>;
       b \<leftarrow> bernoulli_pmf (m / (m + n));
       if b then do {
         let (l2', r2') = split_bst x \<langle>l2, y, r2\<rangle>;
         l \<leftarrow> mrbst_union l1 l2';
         r \<leftarrow> mrbst_union r1 r2';
         return_pmf \<langle>l, x, r\<rangle>
       } else do {
         let (sep, l1', r1') = split_bst' y \<langle>l1, x, r1\<rangle>;
         l \<leftarrow> mrbst_union l1' l2;
         r \<leftarrow> mrbst_union r1' r2;
         if sep then
           mrbst_push_down l y r
         else
           return_pmf \<langle>l, y, r\<rangle>
       }
     }"

(*<*)
end
(*>*)

lemma mrbst_union_Leaf_left [simp]: "mrbst_union \<langle>\<rangle> = return_pmf"
  by (rule ext) simp

lemma mrbst_union_Leaf_right [simp]: "mrbst_union t1 \<langle>\<rangle> = return_pmf t1"
  by (cases t1) simp_all

lemma
  fixes t1 t2 :: "'a :: linorder tree" and b :: bool
  assumes "t' \<in> set_pmf (mrbst_union t1 t2)" "bst t1" "bst t2"
  shows   bst_mrbst_union: "bst t'"
    and   set_mrbst_union: "set_tree t' = set_tree t1 \<union> set_tree t2"
proof -
  have "bst t' \<and> set_tree t' = set_tree t1 \<union> set_tree t2"
  using assms
  proof (induction "size t1 + size t2" arbitrary: t1 t2 t' rule: less_induct)
    case (less t1 t2 t')
    show ?case
    proof (cases "t1 = \<langle>\<rangle> \<or> t2 = \<langle>\<rangle>")
      case False
      then obtain l1 x r1 l2 y r2 where t1: "t1 = \<langle>l1, x, r1\<rangle>" and t2: "t2 = \<langle>l2, y, r2\<rangle>"
        by (cases t1; cases t2) auto
      from less.prems consider l r where
        "l \<in> set_pmf (mrbst_union l1 (fst (split_bst x t2)))"
        "r \<in> set_pmf (mrbst_union r1 (snd (split_bst x t2)))"
        "t' = \<langle>l, x, r\<rangle>"
      | l r where
        "l \<in> set_pmf (mrbst_union (fst (split_bst y t1)) l2)"
        "r \<in> set_pmf (mrbst_union (snd (split_bst y t1)) r2)"
        "t' \<in> (if isin \<langle>l1, x, r1\<rangle> y then set_pmf (mrbst_push_down l y r) else {\<langle>l, y, r\<rangle>})"
        by (auto simp: case_prod_unfold t1 t2 Let_def
                 simp del: split_bst.simps split_bst'.simps isin.simps split: if_splits)
      thus ?thesis
      proof cases
        case 1
        hence lr: "bst l \<and> set_tree l = set_tree l1 \<union> set_tree (fst (split_bst x t2))"
                  "bst r \<and> set_tree r = set_tree r1 \<union> set_tree (snd (split_bst x t2))"
          using less.prems size_split_bst[of x t2]
          by (intro less; force simp: t1)+
        thus ?thesis
          using 1 less.prems by (auto simp: t1 set_split_bst1 set_split_bst2)
      next
        case 2
        hence lr: "bst l \<and> set_tree l = set_tree (fst (split_bst y t1)) \<union> set_tree l2"
                  "bst r \<and> set_tree r = set_tree (snd (split_bst y t1)) \<union> set_tree r2"
          using less.prems size_split_bst[of y t1]
          by (intro less; force simp: t2)+
        show ?thesis
        proof (cases "isin \<langle>l1, x, r1\<rangle> y")
          case False
          thus ?thesis using 2 less.prems lr
            by (auto simp del: isin.simps simp: t2 set_split_bst1 set_split_bst2)
        next
          case True
          have bst': "\<forall>z\<in>set_tree l. z < y" "\<forall>z\<in>set_tree r. z > y"
            using lr less.prems by (auto simp: set_split_bst1 set_split_bst2 t2)
          from True and 2 have t': "t' \<in> set_pmf (mrbst_push_down l y r)"
            by (auto simp del: isin.simps)
          from t' have "bst t'"
            by (rule bst_mrbst_push_down) (use lr bst' in auto)
          moreover from t' have "set_tree t' = {y} \<union> set_tree l \<union> set_tree r"
            by (rule set_mrbst_push_down) (use lr bst' in auto)
          ultimately show ?thesis using less.prems lr
            by (auto simp del: isin.simps simp: t2 set_split_bst1 set_split_bst2)
        qed
      qed
    qed (use less.prems in auto)
  qed
  thus "bst t'" and "set_tree t' = set_tree t1 \<union> set_tree t2" by auto
qed

theorem mrbst_union_correct:
  assumes "finite A" "finite B"
  shows   "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_union t1 t2} =
             random_bst (A \<union> B)"
proof -
  from assms have "finite (A \<union> B)" by simp
  thus ?thesis
  proof (induction "A \<union> B" arbitrary: A B rule: finite_psubset_induct)
    case (psubset A B)
    show ?case
    proof (cases "A = {} \<or> B = {}")
      case True
      thus ?thesis including monad_normalisation by auto
    next
      case False
      with psubset.hyps have AB: "finite A" "finite B" "A \<noteq> {}" "B \<noteq> {}" by auto
      define m n l where "m = card A" and "n = card B" and "l = card (A \<inter> B)"
      define p q where "p = m / (m + n)" and "q = l / n"
      define r where "r = p / (1 - (1 - p) * q)"
      from AB have mn: "m > 0" "n > 0" by (auto simp: m_def n_def)
      have pq: "p \<in> {0..1}" "q \<in> {0..1}"
        using AB by (auto simp: p_def q_def m_def n_def l_def divide_simps intro: card_mono)
      moreover have "p \<noteq> 0"
        using AB by (auto simp: p_def m_def n_def divide_simps add_nonneg_eq_0_iff)
      ultimately have "p > 0" by auto

      have "B - A = B - (A \<inter> B)" by auto
      also have "card \<dots> = n - l"
        using AB unfolding n_def l_def by (intro card_Diff_subset) auto
      finally have [simp]: "card (B - A) = n - l" .
      from AB have "l \<le> n" unfolding l_def n_def by (intro card_mono) auto

      have "p \<le> 1 - (1 - p) * q"
        using mn \<open>l \<le> n\<close> by (auto simp: p_def q_def divide_simps)
      hence r_aux: "(1 - p) * q \<in> {0..1 - p}"
        using pq by auto

      include monad_normalisation
      define RA1 RA2 RB1 RB2
        where "RA1 = (\<lambda>x. random_bst {z\<in>A. z < x})" and "RA2 = (\<lambda>x. random_bst {z\<in>A. z > x})"
          and "RB1 = (\<lambda>x. random_bst {z\<in>B. z < x})" and "RB2 = (\<lambda>x. random_bst {z\<in>B. z > x})"

      have "do {t1 \<leftarrow> random_bst A; t2 \<leftarrow> random_bst B; mrbst_union t1 t2} =
              do {
                x \<leftarrow> pmf_of_set A;
                l1 \<leftarrow> random_bst {z\<in>A. z < x};
                r1 \<leftarrow> random_bst {z\<in>A. z > x};
                y \<leftarrow> pmf_of_set B;
                l2 \<leftarrow> random_bst {z\<in>B. z < y};
                r2 \<leftarrow> random_bst {z\<in>B. z > y};
                let m = size \<langle>l1, x, r1\<rangle>;
                let n = size \<langle>l2, y, r2\<rangle>;
                b \<leftarrow> bernoulli_pmf (m / (m + n));
                if b then do {
                  l \<leftarrow> mrbst_union l1 (fst (split_bst x \<langle>l2, y, r2\<rangle>));
                  r \<leftarrow> mrbst_union r1 (snd (split_bst x \<langle>l2, y, r2\<rangle>));
                  return_pmf \<langle>l, x, r\<rangle>
                } else do {
                  l \<leftarrow> mrbst_union (fst (split_bst y \<langle>l1, x, r1\<rangle>)) l2;
                  r \<leftarrow> mrbst_union (snd (split_bst y \<langle>l1, x, r1\<rangle>)) r2;
                  if isin \<langle>l1, x, r1\<rangle> y then
                    mrbst_push_down l y r
                  else
                    return_pmf \<langle>l, y, r\<rangle>
                }
              }" using AB
        by (simp add: random_bst_reduce split_bst'_altdef Let_def case_prod_unfold cong: if_cong)
      also have "\<dots> = do {
                        x \<leftarrow> pmf_of_set A;
                        l1 \<leftarrow> random_bst {z\<in>A. z < x};
                        r1 \<leftarrow> random_bst {z\<in>A. z > x};
                        y \<leftarrow> pmf_of_set B;
                        l2 \<leftarrow> random_bst {z\<in>B. z < y};
                        r2 \<leftarrow> random_bst {z\<in>B. z > y};
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          l \<leftarrow> mrbst_union l1 (fst (split_bst x \<langle>l2, y, r2\<rangle>));
                          r \<leftarrow> mrbst_union r1 (snd (split_bst x \<langle>l2, y, r2\<rangle>));
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          l \<leftarrow> mrbst_union (fst (split_bst y \<langle>l1, x, r1\<rangle>)) l2;
                          r \<leftarrow> mrbst_union (snd (split_bst y \<langle>l1, x, r1\<rangle>)) r2;
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        unfolding Let_def
      proof (intro bind_pmf_cong refl if_cong)
        fix l1 x r1 y
        assume "l1 \<in> set_pmf (random_bst {z\<in>A. z < x})" "r1 \<in> set_pmf (random_bst {z\<in>A. z > x})"
               "x \<in> set_pmf (pmf_of_set A)"
        thus "isin \<langle>l1, x, r1\<rangle> y \<longleftrightarrow> (y \<in> A)"
          using AB by (subst isin_bst) (auto simp: bst_random_bst set_random_bst)
      qed (insert AB,
           auto simp: size_random_bst m_def n_def p_def isin_random_bst dest!: card_3way_split)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          (l1, r1) \<leftarrow> pair_pmf (random_bst {z\<in>A. z < x}) (random_bst {z\<in>A. z > x});
                          (l2, r2) \<leftarrow> map_pmf (split_bst x) (random_bst B);
                          l \<leftarrow> mrbst_union l1 l2;
                          r \<leftarrow> mrbst_union r1 r2;
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set B;
                          (l1, r1) \<leftarrow> map_pmf (split_bst y) (random_bst A);
                          (l2, r2) \<leftarrow> pair_pmf (random_bst {z\<in>B. z < y}) (random_bst {z\<in>B. z > y});
                          l \<leftarrow> mrbst_union l1 l2;
                          r \<leftarrow> mrbst_union r1 r2;
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }" using AB
        by (simp add: random_bst_reduce map_pmf_def case_prod_unfold pair_pmf_def cong: if_cong)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          (l1, r1) \<leftarrow> pair_pmf (RA1 x) (RA2 x);
                          (l2, r2) \<leftarrow> pair_pmf (RB1 x) (RB2 x);
                          l \<leftarrow> mrbst_union l1 l2;
                          r \<leftarrow> mrbst_union r1 r2;
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set B;
                          (l1, r1) \<leftarrow> pair_pmf (RA1 y) (RA2 y);
                          (l2, r2) \<leftarrow> pair_pmf (RB1 y) (RB2 y);
                          l \<leftarrow> mrbst_union l1 l2;
                          r \<leftarrow> mrbst_union r1 r2;
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        unfolding case_prod_unfold RA1_def RA2_def RB1_def RB2_def
        by (intro bind_pmf_cong refl if_cong split_random_bst AB)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> do {l1 \<leftarrow> RA1 x; l2 \<leftarrow> RB1 x; mrbst_union l1 l2};
                          r \<leftarrow> do {r1 \<leftarrow> RA2 x; r2 \<leftarrow> RB2 x; mrbst_union r1 r2};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set B;
                          l \<leftarrow> do {l1 \<leftarrow> RA1 y; l2 \<leftarrow> RB1 y; mrbst_union l1 l2};
                          r \<leftarrow> do {r1 \<leftarrow> RA2 y; r2 \<leftarrow> RB2 y; mrbst_union r1 r2};
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        by (simp add: pair_pmf_def cong: if_cong)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst ({z\<in>A. z < x} \<union> {z\<in>B. z < x});
                          r \<leftarrow> random_bst ({z\<in>A. z > x} \<union> {z\<in>B. z > x});
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set B;
                          l \<leftarrow> random_bst ({z\<in>A. z < y} \<union> {z\<in>B. z < y});
                          r \<leftarrow> random_bst ({z\<in>A. z > y} \<union> {z\<in>B. z > y});
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        unfolding RA1_def RA2_def RB1_def RB2_def using AB
        by (intro bind_pmf_cong if_cong refl psubset) auto
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          y \<leftarrow> pmf_of_set B;
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                          if y \<in> A then
                            mrbst_push_down l y r
                          else
                            return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        by (intro bind_pmf_cong if_cong refl arg_cong[of _ _ random_bst]) auto
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          b' \<leftarrow> bernoulli_pmf q;
                          if b' then do {
                            y \<leftarrow> pmf_of_set (A \<inter> B);
                            random_bst (A \<union> B)
                          } else do {
                            y \<leftarrow> pmf_of_set (B - A);
                            l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                            r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                            return_pmf \<langle>l, y, r\<rangle>
                          }
                        }
                      }"
      proof (intro bind_pmf_cong refl if_cong, goal_cases)
        case (1 b)
        have q_pos: "A \<inter> B \<noteq> {}" if "q > 0" using that by (auto simp: q_def l_def)
        have q_lt1: "B - A \<noteq> {}" if "q < 1"
        proof
          assume "B - A = {}"
          hence "A \<inter> B = B" by auto
          thus False using that AB by (auto simp: q_def l_def n_def)
        qed

        have eq: "pmf_of_set B = do {b' \<leftarrow> bernoulli_pmf q;
                                     if b' then pmf_of_set (A \<inter> B) else pmf_of_set (B - A)}"
          using AB by (intro pmf_of_set_split_inter_diff [symmetric])
                      (auto simp: q_def l_def n_def)
        have "do {y \<leftarrow> pmf_of_set B;
                  l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                  r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                  if y \<in> A then
                    mrbst_push_down l y r
                  else
                    return_pmf \<langle>l, y, r\<rangle>
                 } =
              do {
                b' \<leftarrow> bernoulli_pmf q;
                y \<leftarrow> (if b' then pmf_of_set (A \<inter> B) else pmf_of_set (B - A));
                l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                if b' then
                  mrbst_push_down l y r
                else
                  return_pmf \<langle>l, y, r\<rangle>
              }" unfolding eq bind_assoc_pmf using AB q_pos q_lt1
          by (intro bind_pmf_cong refl if_cong) (auto split: if_splits)
        also have "\<dots> = do {
                          b' \<leftarrow> bernoulli_pmf q;
                          if b' then do {
                            y \<leftarrow> pmf_of_set (A \<inter> B);
                            do {l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                                r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                                mrbst_push_down l y r}
                          } else do {
                            y \<leftarrow> pmf_of_set (B - A);
                            l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                            r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                            return_pmf \<langle>l, y, r\<rangle>
                          }
                        }" by (simp cong: if_cong)
        also have "\<dots> = do {
                          b' \<leftarrow> bernoulli_pmf q;
                          if b' then do {
                            y \<leftarrow> pmf_of_set (A \<inter> B);
                            random_bst (A \<union> B)
                          } else do {
                            y \<leftarrow> pmf_of_set (B - A);
                            l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                            r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                            return_pmf \<langle>l, y, r\<rangle>
                          }
                        }"
          using AB q_pos by (intro bind_pmf_cong if_cong refl mrbst_push_down_correct') auto
        finally show ?case .
      qed
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf p;
                        b' \<leftarrow> bernoulli_pmf q;
                        if b then do {
                          x \<leftarrow> pmf_of_set A;
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else if b' then do {
                            random_bst (A \<union> B)
                        } else do {
                          y \<leftarrow> pmf_of_set (B - A);
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < y};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > y};
                          return_pmf \<langle>l, y, r\<rangle>
                        }
                      }"
        by (simp cong: if_cong)
      also have "\<dots> = do {
                        (b, b') \<leftarrow> pair_pmf (bernoulli_pmf p) (bernoulli_pmf q);
                        if b \<or> \<not>b' then do {
                          x \<leftarrow> (if b then pmf_of_set A else pmf_of_set (B - A));
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                            random_bst (A \<union> B)
                        }
                      }" unfolding pair_pmf_def bind_assoc_pmf
        by (intro bind_pmf_cong) auto
      also have "\<dots> = do {
                        (b, b') \<leftarrow> map_pmf (\<lambda>(b, b'). (b \<or> \<not>b', b))
                                    (pair_pmf (bernoulli_pmf p) (bernoulli_pmf q));
                        if b then do {
                          x \<leftarrow> (if b' then pmf_of_set A else pmf_of_set (B - A));
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                            random_bst (A \<union> B)
                        }
                      }" (is "_ = bind_pmf _ ?f")
        by (simp add: bind_map_pmf case_prod_unfold cong: if_cong)
      also have "map_pmf (\<lambda>(b, b'). (b \<or> \<not>b', b))
                   (pair_pmf (bernoulli_pmf p) (bernoulli_pmf q)) =
                 do {
                   b \<leftarrow> bernoulli_pmf (1 - (1 - p) * q);
                   b' \<leftarrow> (if b then bernoulli_pmf r else return_pmf False);
                   return_pmf (b, b')
                 }" (is "?lhs = ?rhs")
      proof (intro pmf_eqI)
        fix bb' :: "bool \<times> bool" 
        obtain b b' where [simp]: "bb' = (b, b')" by (cases bb')
        thus "pmf ?lhs bb' = pmf ?rhs bb'"
          using pq r_aux \<open>p > 0\<close>
          by (cases b; cases b')
             (auto simp: pmf_map pmf_bind_bernoulli measure_measure_pmf_finite 
                         vimage_bool_pair pmf_pair r_def field_simps)
      qed
      also have "\<dots> \<bind> ?f = do {
                              b \<leftarrow> bernoulli_pmf (1 - (1 - p) * q);
                              if b then do {
                                x \<leftarrow> do {b' \<leftarrow> bernoulli_pmf r;
                                         if b' then pmf_of_set A else pmf_of_set (B - A)};
                                l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                                r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                                return_pmf \<langle>l, x, r\<rangle>
                              } else do {
                                random_bst (A \<union> B)
                              }
                            }"
        by (simp cong: if_cong)
      also have "\<dots> = do {
                        b \<leftarrow> bernoulli_pmf (1 - (1 - p) * q);
                        if b then do {
                          x \<leftarrow> pmf_of_set (A \<union> (B - A));
                          l \<leftarrow> random_bst {z\<in>A \<union> B. z < x};
                          r \<leftarrow> random_bst {z\<in>A \<union> B. z > x};
                          return_pmf \<langle>l, x, r\<rangle>
                        } else do {
                          random_bst (A \<union> B)
                        }
                      }" (is "_ = ?f (A \<union> (B - A))")
        using AB pq \<open>l \<le> n\<close> mn
        by (intro bind_pmf_cong if_cong refl pmf_of_set_union_split)
           (auto simp: m_def [symmetric] n_def [symmetric] r_def p_def q_def divide_simps)
      also have "A \<union> (B - A) = A \<union> B" by auto
      also have "?f \<dots> = random_bst (A \<union> B)"
        using AB by (simp add: random_bst_reduce cong: if_cong)
      finally show ?thesis .
    qed
  qed
qed


subsection \<open>Insertion and Deletion\<close>

text \<open>
  The insertion and deletion operations are simple special cases of the union
  and difference operations where one of the trees is a singleton tree.
\<close>
fun mrbst_insert where
  "mrbst_insert x \<langle>\<rangle> = return_pmf \<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>"
| "mrbst_insert x \<langle>l, y, r\<rangle> =
     do {
       b \<leftarrow> bernoulli_pmf (1 / real (size l + size r + 2));
       if b then do {
         let (l', r') = split_bst x \<langle>l, y, r\<rangle>;
         return_pmf \<langle>l', x, r'\<rangle>
       } else if x < y then do {
         map_pmf (\<lambda>l'. \<langle>l', y, r\<rangle>) (mrbst_insert x l)
       } else if x > y then do {
         map_pmf (\<lambda>r'. \<langle>l, y, r'\<rangle>) (mrbst_insert x r)
       } else do {
         mrbst_push_down l y r
       }
     }"

lemma mrbst_insert_altdef: "mrbst_insert x t = mrbst_union \<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle> t"
  by (induction x t rule: mrbst_insert.induct)
     (simp_all add: Let_def map_pmf_def bind_return_pmf case_prod_unfold cong: if_cong)

corollary
  fixes t :: "'a :: linorder tree"
  assumes "t' \<in> set_pmf (mrbst_insert x t)" "bst t"
  shows   bst_mrbst_insert: "bst t'"
    and   set_mrbst_insert: "set_tree t' = insert x (set_tree t)"
  using bst_mrbst_union[of t' "\<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>" t] set_mrbst_union[of t' "\<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>" t] assms
  by (simp_all add: mrbst_insert_altdef)

corollary mrbst_insert_correct:
  assumes "finite A"
  shows   "random_bst A \<bind> mrbst_insert x = random_bst (insert x A)"
  using mrbst_union_correct[of "{x}" A] assms
  by (simp add: mrbst_insert_altdef[abs_def] bind_return_pmf)


fun mrbst_delete :: "'a :: ord \<Rightarrow> 'a tree \<Rightarrow> 'a tree pmf" where
  "mrbst_delete x \<langle>\<rangle> = return_pmf \<langle>\<rangle>"
| "mrbst_delete x \<langle>l, y, r\<rangle> = (
     if x < y then
       map_pmf (\<lambda>l'. \<langle>l', y, r\<rangle>) (mrbst_delete x l)
     else if x > y then
       map_pmf (\<lambda>r'. \<langle>l, y, r'\<rangle>) (mrbst_delete x r)
     else 
       mrbst_join l r)"

lemma mrbst_delete_altdef: "mrbst_delete x t = mrbst_diff t \<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>"
  by (induction t) (auto simp: bind_return_pmf map_pmf_def)

corollary
  fixes t :: "'a :: linorder tree"
  assumes "t' \<in> set_pmf (mrbst_delete x t)" "bst t"
  shows   bst_mrbst_delete: "bst t'"
    and   set_mrbst_delete: "set_tree t' = set_tree t - {x}"
  using bst_mrbst_diff[of t' t "\<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>"] set_mrbst_diff[of t' t "\<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>"] assms
  by (simp_all add: mrbst_delete_altdef)

corollary mrbst_delete_correct:
  "finite A \<Longrightarrow> do {t \<leftarrow> random_bst A; mrbst_delete x t} = random_bst (A - {x})"
  using mrbst_diff_correct[of A "{x}"] by (simp add: mrbst_delete_altdef bind_return_pmf)

end