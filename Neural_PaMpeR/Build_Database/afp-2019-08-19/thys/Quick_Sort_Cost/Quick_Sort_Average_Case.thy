(*
  File:     Quick_Sort_Average_Case.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  Definition and average-case analysis of the standard deterministic QuickSort algorithm
*)
section \<open>Average case analysis of deterministic QuickSort\<close>
theory Quick_Sort_Average_Case
  imports Randomised_Quick_Sort
begin
  
subsection \<open>Definition of deterministic QuickSort\<close>
  
text \<open>
  This is the functional description of the standard variant of deterministic QuickSort that 
  always chooses the first list element as the pivot as given by Hoare in 1962~\cite{hoare}. 
  For a list that is already sorted, this leads to $n(n-1)$ 
  comparisons, but as is well known, the average case is not that bad.
\<close>
fun quicksort :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "quicksort _ [] = []"
| "quicksort R (x # xs) = 
     quicksort R (filter (\<lambda>y. (y,x) \<in> R) xs) @ [x] @ quicksort R (filter (\<lambda>y. (y,x) \<notin> R) xs)"

text \<open>
  We can easily show that this QuickSort is correct:
\<close>
theorem mset_quicksort [simp]: "mset (quicksort R xs) = mset xs"
  by (induction R xs rule: quicksort.induct) (simp_all)

corollary set_quicksort [simp]: "set (quicksort R xs) = set xs"
  by (induction R xs rule: quicksort.induct) auto

theorem sorted_wrt_quicksort: 
  assumes "trans R" and "total_on (set xs) R" and "\<And>x. x \<in> set xs \<Longrightarrow> (x, x) \<in> R"
  shows   "sorted_wrt R (quicksort R xs)"
using assms
proof (induction R xs rule: quicksort.induct)
  case (2 R x xs)
  have total: "(a, b) \<in> R" if "(b, a) \<notin> R" "a \<in> set (x#xs)" "b \<in> set (x#xs)" for a b
    using "2.prems" that unfolding total_on_def by (cases "a = b") auto
    
  have *: "sorted_wrt R (quicksort R (filter (\<lambda>y. (y,x) \<in> R) xs))"
          "sorted_wrt R (quicksort R (filter (\<lambda>y. (y,x) \<notin> R) xs))"
    by ((rule 2 total_on_subset[OF \<open>total_on (set (x#xs)) R\<close>]) | force)+
  show ?case
    by (auto intro!: sorted_wrt_append sorted_wrt.intros \<open>trans R\<close> * 
             intro: transD[OF \<open>trans R\<close>] dest!: total simp: total_on_def)
qed auto

corollary sorted_wrt_quicksort':
  assumes "linorder_on A R" and "set xs \<subseteq> A"
  shows   "sorted_wrt R (quicksort R xs)"
  by (rule sorted_wrt_quicksort)
     (insert assms, auto simp: linorder_on_def refl_on_def dest: total_on_subset)

text \<open>
  We now define another version of QuickSort that is identical to the previous one but also 
  counts the number of comparisons that were made.
\<close>
fun quicksort' :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> nat" where
  "quicksort' _ [] = ([], 0)"
| "quicksort' R (x # xs) = (
     let (ls, rs)  = partition (\<lambda>y. (y,x) \<in> R) xs;
         (ls', n1) = quicksort' R ls;
         (rs', n2) = quicksort' R rs
     in
         (ls' @ [x] @ rs', length xs + n1 + n2))"

text \<open>
  For convenience, we also define a function that computes only the number of comparisons that 
  were made and not the result list.
\<close>
fun qs_cost :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> nat" where
  "qs_cost _ [] = 0"
| "qs_cost R (x # xs) = 
     length xs + qs_cost R (filter (\<lambda>y. (y,x)\<in>R) xs) + qs_cost R (filter (\<lambda>y. (y,x)\<notin>R) xs)"


text \<open>
  It is obvious that the original QuickSort and the cost function are the projections 
  of the cost-counting QuickSort.
\<close>  
lemma fst_quicksort' [simp]: "fst (quicksort' R xs) = quicksort R xs"
  by (induction R xs rule: quicksort.induct) (simp_all add: case_prod_unfold Let_def o_def)

lemma snd_quicksort' [simp]: "snd (quicksort' R xs) = qs_cost R xs"
  by (induction R xs rule: quicksort.induct) (simp_all add: case_prod_unfold Let_def o_def)

    
subsection \<open>Analysis\<close>

text \<open>
  We will reduce the average-case analysis to showing that it is essentially equivalent to 
  the randomised QuickSort we analysed earlier. Similar, but more direct analyses are given 
  by Hoare~\cite{hoare} and Sedgewick~\cite{sedgewick}. 

  The proof is relatively straightforward -- but still a bit messy. We show that the cost 
  distribution of QuickSort run on a random permutation of a set of size $n$ is exactly the same 
  as that of randomised QuickSort being run on any fixed list of size $n$ (which we analysed 
  before):  
\<close>
theorem qs_cost_average_conv_rqs_cost:
  assumes "finite A" and "linorder_on B R" and "A \<subseteq> B"
  shows   "map_pmf (qs_cost R) (pmf_of_set (permutations_of_set A)) = rqs_cost (card A)"
using assms(1,3)
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "A = {}")
    case True
    thus ?thesis by (simp add: pmf_of_set_singleton)
  next
    case False
    note A = \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    define n where "n = card A - 1"
    from A have "pmf_of_set (permutations_of_set A) = 
      do {x \<leftarrow> pmf_of_set A; xs \<leftarrow> pmf_of_set (permutations_of_set (A - {x})); return_pmf (x#xs)}"
      by (rule random_permutation_of_set)
    also have "map_pmf (qs_cost R) \<dots> =
                 do {
                   x \<leftarrow> pmf_of_set A;
                   xs \<leftarrow> pmf_of_set (permutations_of_set (A - {x}));
                   return_pmf (length xs + qs_cost R [y\<leftarrow>xs. (y,x)\<in>R] + qs_cost R [y\<leftarrow>xs. (y,x)\<notin>R])
                 }" by (simp add: map_bind_pmf)
    also have "\<dots> = map_pmf (\<lambda>m. n + m) (
          do {
            x \<leftarrow> pmf_of_set A;
            xs \<leftarrow> pmf_of_set (permutations_of_set (A - {x}));
            return_pmf (qs_cost R [y\<leftarrow>xs. (y,x)\<in>R] + qs_cost R [y\<leftarrow>xs. (y,x)\<notin>R])
          })" (is "_ = map_pmf _ ?X") using A unfolding n_def map_bind_pmf
      by (intro bind_pmf_cong map_pmf_cong refl) (auto simp: length_finite_permutations_of_set)
    also have "?X = do {
                      x \<leftarrow> pmf_of_set A;
                      (ls,rs) \<leftarrow> map_pmf (partition (\<lambda>y. (y,x)\<in>R)) 
                                   (pmf_of_set (permutations_of_set (A - {x})));
                      return_pmf (qs_cost R ls + qs_cost R rs)
                    }" by (simp add: bind_map_pmf o_def)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      (n1, n2) \<leftarrow> pair_pmf 
                        (rqs_cost (linorder_rank R A x)) (rqs_cost (n - linorder_rank R A x));
                      return_pmf (n1 + n2)}"
    proof (intro bind_pmf_cong refl, goal_cases)
      case (1 x)
      have "map_pmf (partition (\<lambda>y. (y,x)\<in>R)) (pmf_of_set (permutations_of_set (A - {x})))
              \<bind> (\<lambda>(ls, rs). return_pmf (qs_cost R ls + qs_cost R rs)) = 
            map_pmf (\<lambda>(n1, n2). n1 + n2) (pair_pmf
              (map_pmf (qs_cost R) (pmf_of_set (permutations_of_set {xa \<in> A - {x}. (xa, x) \<in> R})))
              (map_pmf (qs_cost R) (pmf_of_set (permutations_of_set {xa \<in> A - {x}. (xa, x) \<notin> R}))))"
        (is "_ = map_pmf _ (pair_pmf ?X ?Y)")
        by (subst partition_random_permutations)
           (simp_all add: map_pmf_def case_prod_unfold bind_return_pmf bind_assoc_pmf pair_pmf_def A)
      also {
        have "{xa \<in> A - {x}. (xa, x) \<in> R} \<subseteq> A - {x}" by blast
        also have "\<dots> \<subset> A" using 1 A by auto
        finally have subset: "{xa \<in> A - {x}. (xa, x) \<in> R} \<subset> A" .
        also have "\<dots> \<subseteq> B" by fact
        finally have "?X = rqs_cost (card {xa \<in> A - {x}. (xa, x) \<in> R})" using subset
          by (intro psubset.IH) auto
        also have "card {xa \<in> A - {x}. (xa, x) \<in> R} = linorder_rank R A x"
          by (simp add: linorder_rank_def)
        finally have "?X = rqs_cost \<dots>" .
      }
      also {
        have "{xa \<in> A - {x}. (xa, x) \<notin> R} \<subseteq> A - {x}" by blast
        also have "\<dots> \<subset> A" using 1 A by auto
        finally have subset: "{xa \<in> A - {x}. (xa, x) \<notin> R} \<subset> A" .
        also have "\<dots> \<subseteq> B" by fact
        finally have "?Y = rqs_cost (card {xa \<in> A - {x}. (xa, x) \<notin> R})" using subset
          by (intro psubset.IH) auto
        also {
          have "card ({y\<in>A-{x}. (y,x)\<in>R} \<union> {y\<in>A-{x}. (y,x)\<notin>R}) = 
                  linorder_rank R A x + card {xa \<in> A - {x}. (xa, x) \<notin> R}"
            unfolding linorder_rank_def using A by (intro card_Un_disjoint) auto
          also have "{y\<in>A-{x}. (y,x)\<in>R} \<union> {y\<in>A-{x}. (y,x)\<notin>R} = A - {x}" by blast
          also have "card \<dots> = n" using A 1 by (simp add: n_def)
          finally have "card {xa \<in> A - {x}. (xa, x) \<notin> R} = n - linorder_rank R A x" by simp
        }
        finally have "?Y = rqs_cost (n - linorder_rank R A x)" .
      }
      finally show ?case by (simp add: case_prod_unfold map_pmf_def)
    qed
    also have "\<dots> = do {
                      i \<leftarrow> map_pmf (linorder_rank R A) (pmf_of_set A);
                      (n1, n2) \<leftarrow> pair_pmf (rqs_cost i) (rqs_cost (n - i));
                      return_pmf (n1 + n2)
                    }" by (simp add: bind_map_pmf)
    also have "map_pmf (linorder_rank R A) (pmf_of_set A) = pmf_of_set {..<card A}"
      by (intro map_pmf_of_set_bij_betw bij_betw_linorder_rank[OF assms(2)] A psubset.prems)
    also from A have "card A > 0" by (intro Nat.gr0I) auto
    hence "{..<card A} = {..n}" by (auto simp: n_def)
    also have "map_pmf (\<lambda>m. n + m) (
                 do {
                      i \<leftarrow> pmf_of_set {..n};
                      (n1, n2) \<leftarrow> pair_pmf (rqs_cost i) (rqs_cost (n - i));
                      return_pmf (n1 + n2)
                    }) = rqs_cost (Suc n)"
      by (simp add: pair_pmf_def map_bind_pmf case_prod_unfold
                    bind_assoc_pmf bind_return_pmf add_ac)
    also from A have "card A > 0" by (intro Nat.gr0I) auto
    hence "Suc n = card A" by (simp add: n_def)
    finally show ?thesis .
  qed
qed

text \<open>
  We therefore have the same expectation as well. (Note that we showed 
  @{thm rqs_cost_exp_eq [no_vars]} and @{thm rqs_cost_exp_asymp_equiv [no_vars]} before.
\<close>
corollary expectation_qs_cost: 
  assumes "finite A" and "linorder_on B R" and "A \<subseteq> B"
  defines "random_list \<equiv> pmf_of_set (permutations_of_set A)"
  shows   "measure_pmf.expectation (map_pmf (qs_cost R) random_list) real = 
             rqs_cost_exp (card A)"
  unfolding random_list_def
  by (subst qs_cost_average_conv_rqs_cost[OF assms(1-3)]) (simp add: expectation_rqs_cost)

end