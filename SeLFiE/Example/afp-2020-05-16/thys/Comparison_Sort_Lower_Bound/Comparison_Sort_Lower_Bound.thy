(*
  File:     Comparison_Sort_Lower_Bound.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  Proof of the lower-bound on worst-case comparisons in a comparison-based sorting algorithm.
*)
section \<open>Lower bound on costs of comparison-based sorting\<close>
theory Comparison_Sort_Lower_Bound
  imports 
    Complex_Main 
    Linorder_Relations
    Stirling_Formula.Stirling_Formula
    "Landau_Symbols.Landau_More"
begin
  
subsection \<open>Abstract description of sorting algorithms\<close>

text \<open>
  We have chosen to model a sorting algorithm in the following way: A sorting algorithm takes a 
  list with distinct elements and a linear ordering on these elements, and it returns a list 
  with the same elements that is sorted w.\,r.\,t.\ the given ordering.

  The use of an explicit ordering means that the algorithm must look at the ordering, i.\,e.\ 
  it has to use pair-wise comparison of elements, since all the information that is relevant 
  for producing the correct sorting is in the ordering; the elements themselves are irrelevant.

  Furthermore, we record the number of comparisons that the algorithm makes by not giving it the 
  relation explicitly, but in the form of a comparison oracle that may be queried.

  A sorting algorithm (or `sorter') for a fixed input list (but for arbitrary orderings) can then
  be written as a recursive datatype that is either the result (the sorted list) or a comparison 
  query consisting of two elements and a continuation that maps the result of the comparison
  to the remaining computation.
\<close>  

datatype 'a sorter = Return "'a list" | Query 'a 'a "bool \<Rightarrow> 'a sorter"
    

text \<open>
  Cormen~\emph{et\ al.}~\cite{cormen}\ use a similar `decision tree' model where an sorting 
  algorithm for lists of fixed size $n$ is modelled as a binary tree where each node is a 
  comparison of two elements. They also demand that every leaf in the tree be reachable in 
  order to avoid `dead' subtrees (if the algorithm makes redundant comparisons, there may be 
  branches that can never be taken). Then, the worst-case number of comparisons made is simply 
  the height of the tree.

  We chose a subtly different model that does not have this restriction on the algorithm but 
  instead uses a more semantic way of counting the worst-case number of comparisons: We simply 
  use the maximum number of comparisons that occurs for any of the (finitely many) inputs.

  We therefore first define a function that counts the number of queries for a specific
  ordering and then a function that counts the number of queries in the worst case (ranging 
  over a given set of allowed orderings; typically, this will be the set of all linear orders
  on the list).
\<close>
primrec count_queries :: "('a \<times> 'a) set \<Rightarrow> 'a sorter \<Rightarrow> nat" where
  "count_queries _ (Return _)    = 0"
| "count_queries R (Query a b f) = Suc (count_queries R (f ((a, b) \<in> R)))"

definition count_wc_queries :: "('a \<times> 'a) set set \<Rightarrow> 'a sorter \<Rightarrow> nat" where
  "count_wc_queries Rs sorter = (if Rs = {} then 0 else Max ((\<lambda>R. count_queries R sorter) ` Rs))"

lemma count_wc_queries_empty [simp]: "count_wc_queries {} sorter = 0"
  by (simp add: count_wc_queries_def)

lemma count_wc_queries_aux:
  assumes "\<And>R. R \<in> Rs \<Longrightarrow> sorter = sorter' R" "Rs \<subseteq> Rs'" "finite Rs'"
  shows   "count_wc_queries Rs sorter \<le> Max ((\<lambda>R. count_queries R (sorter' R)) ` Rs')" 
proof (cases "Rs = {}")
  case False
  hence "count_wc_queries Rs sorter = Max ((\<lambda>R. count_queries R sorter) ` Rs)"
    by (simp add: count_wc_queries_def)
  also have "(\<lambda>R. count_queries R sorter) ` Rs = (\<lambda>R. count_queries R (sorter' R)) ` Rs"
    by (intro image_cong refl) (simp_all add: assms)
  also have "Max \<dots> \<le> Max ((\<lambda>R. count_queries R (sorter' R)) ` Rs')" using False
    by (intro Max_mono assms image_mono finite_imageI) auto
  finally show ?thesis .
qed simp_all

primrec eval_sorter :: "('a \<times> 'a) set \<Rightarrow> 'a sorter \<Rightarrow> 'a list" where
  "eval_sorter _ (Return ys)   = ys"
| "eval_sorter R (Query a b f) = eval_sorter R (f ((a,b) \<in> R))"
  
text \<open>
  We now get an obvious bound on the maximum number of different results that a given sorter 
  can produce.
\<close>
lemma card_range_eval_sorter:
  assumes "finite Rs"
  shows   "card ((\<lambda>R. eval_sorter R e) ` Rs) \<le> 2 ^ count_wc_queries Rs e"
using assms
proof (induction e arbitrary: Rs)
  case (Return xs Rs)
  have *: "(\<lambda>R. eval_sorter R (Return xs)) ` Rs = (if Rs = {} then {} else {xs})" by auto
  show ?case by (subst *) auto
next
  case (Query a b f Rs)
  have "f True \<in> range f" "f False \<in> range f" by simp_all
  note IH = this [THEN Query.IH]
  let ?Rs1 = "{R\<in>Rs. (a, b) \<in> R}" and ?Rs2 = "{R\<in>Rs. (a, b) \<notin> R}"
  let ?A = "(\<lambda>R. eval_sorter R (f True)) ` ?Rs1" and ?B = "(\<lambda>R. eval_sorter R (f False)) ` ?Rs2"
  from Query.prems have fin: "finite ?Rs1" "finite ?Rs2" by simp_all

  have *: "(\<lambda>R. eval_sorter R (Query a b f)) ` Rs \<subseteq> ?A \<union> ?B"
  proof (intro subsetI, elim imageE, goal_cases)
    case (1 xs R)
    thus ?case by (cases "(a,b) \<in> R") auto
  qed
  
  show ?case
  proof (cases "Rs = {}")
    case False
    have "card ((\<lambda>R. eval_sorter R (Query a b f)) ` Rs) \<le> card (?A \<union> ?B)"
      by (intro card_mono finite_UnI finite_imageI fin *)
    also have "\<dots> \<le> card ?A + card ?B" by (rule card_Un_le)
    also have "\<dots> \<le> 2 ^ count_wc_queries ?Rs1 (f True) + 2 ^ count_wc_queries ?Rs2 (f False)"
      by (intro add_mono IH fin)
    also have "count_wc_queries ?Rs1 (f True) \<le> Max ((\<lambda>R. count_queries R (f ((a,b)\<in>R))) ` Rs)"
      by (intro count_wc_queries_aux Query.prems) auto
    also have "count_wc_queries ?Rs2 (f False) \<le> Max ((\<lambda>R. count_queries R (f ((a,b)\<in>R))) ` Rs)"
      by (intro count_wc_queries_aux Query.prems) auto
    also have "2 ^ \<dots> + 2 ^ \<dots> = (2 ^ Suc \<dots> :: nat)" by simp
    also have "Suc (Max ((\<lambda>R. count_queries R (f ((a,b)\<in>R))) ` Rs)) = 
                 Max (Suc ` ((\<lambda>R. count_queries R (f ((a,b)\<in>R))) ` Rs))" using False
      by (intro mono_Max_commute finite_imageI Query.prems) (auto simp: incseq_def)
    also have "Suc ` ((\<lambda>R. count_queries R (f ((a,b)\<in>R))) ` Rs) = 
                 (\<lambda>R. Suc (count_queries R (f ((a,b)\<in>R)))) ` Rs" by (simp add: image_image)
    also have "Max \<dots> = count_wc_queries Rs (Query a b f)" using False
      by (auto simp add: count_wc_queries_def)
    finally show ?thesis by - simp_all
  qed simp_all
qed

text \<open>
  The following predicate describes what constitutes a valid sorting result for a given 
  ordering and a given input list. Note that when the ordering is linear, the result is
  actually unique.
\<close>
definition is_sorting :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_sorting R xs ys \<longleftrightarrow> (mset xs = mset ys) \<and> sorted_wrt R ys"


subsection \<open>Lower bounds on number of comparisons\<close>

text \<open>
  For a list of $n$ distinct elements, there are $n!$ linear orderings on $n$ elements,
  each of which leads to a different result after sorting the original list. 
  Since a sorter can produce at most $2^k$ different results with $k$ comparisons, we get 
  the bound $2^k \geq n!$:
\<close>
theorem
  fixes sorter :: "'a sorter" and xs :: "'a list"
  assumes distinct: "distinct xs"
  assumes sorter: "\<And>R. linorder_on (set xs) R \<Longrightarrow> is_sorting R xs (eval_sorter R sorter)"
  defines "Rs \<equiv> {R. linorder_on (set xs) R}"
  shows   two_power_count_queries_ge: "fact (length xs) \<le> (2 ^ count_wc_queries Rs sorter :: nat)"
    and   count_queries_ge:           "log 2 (fact (length xs)) \<le> real (count_wc_queries Rs sorter)"
proof -
  have "Rs \<subseteq> Pow (set xs \<times> set xs)" by (auto simp: Rs_def linorder_on_def refl_on_def)
  hence fin: "finite Rs" by (rule finite_subset) simp_all
  from assms have "fact (length xs) = card (permutations_of_set (set xs))"
    by (simp add: distinct_card)
  also have "permutations_of_set (set xs) \<subseteq> (\<lambda>R. eval_sorter R sorter) ` Rs"
  proof (rule subsetI, goal_cases)
    case (1 ys)
    define R where "R = linorder_of_list ys"
    define zs where "zs = eval_sorter R sorter"
    from 1 and distinct have mset_ys: "mset ys = mset xs" 
      by (auto simp: set_eq_iff_mset_eq_distinct permutations_of_set_def)
    from 1 have *: "linorder_on (set xs) R" unfolding R_def using linorder_linorder_of_list[of ys]
      by (simp add: permutations_of_set_def)
    from sorter[OF this] have "mset xs = mset zs" "sorted_wrt R zs"
      by (simp_all add: is_sorting_def zs_def)
    moreover from 1 have "sorted_wrt R ys" unfolding R_def
      by (intro sorted_wrt_linorder_of_list) (simp_all add: permutations_of_set_def)
    ultimately have "zs = ys"
      by (intro sorted_wrt_linorder_unique[OF *]) (simp_all add: mset_ys)
    moreover from * have "R \<in> Rs" by (simp add: Rs_def)
    ultimately show ?case unfolding zs_def by blast
  qed
  hence "card (permutations_of_set (set xs)) \<le> card ((\<lambda>R. eval_sorter R sorter) ` Rs)"
    by (intro card_mono finite_imageI fin)
  also from fin have "\<dots> \<le> 2 ^ count_wc_queries Rs sorter" by (rule card_range_eval_sorter)
  finally show *: "fact (length xs) \<le> (2 ^ count_wc_queries Rs sorter :: nat)" .
  
  have "ln (fact (length xs)) = ln (real (fact (length xs)))" by simp
  also have "\<dots> \<le> ln (real (2 ^ count_wc_queries Rs sorter))"
  proof (subst ln_le_cancel_iff)
    show "real (fact (length xs)) \<le> real (2 ^ count_wc_queries Rs sorter)" 
      by (subst of_nat_le_iff) (rule *)
  qed simp_all
  also have "\<dots> = real (count_wc_queries Rs sorter) * ln 2" by (simp add: ln_realpow)
  finally have "real (count_wc_queries Rs sorter) \<ge> ln (fact (length xs)) / ln 2" 
    by (simp add: field_simps)
  also have "ln (fact (length xs)) / ln 2 = log 2 (fact (length xs))" by (simp add: log_def)
  finally show **: "log 2 (fact (length xs)) \<le> real (count_wc_queries Rs sorter)" .
qed

(* TODO: Good example for automation. Also, move. *)
lemma ln_fact_bigo: "(\<lambda>n. ln (fact n) - (ln (2 * pi * n) / 2 + n * ln n - n)) \<in> O(\<lambda>n. 1 / n)"
  and asymp_equiv_ln_fact [asymp_equiv_intros]: "(\<lambda>n. ln (fact n)) \<sim>[at_top] (\<lambda>n. n * ln n)"
proof -
  include asymp_equiv_notation
  define f where "f = (\<lambda>n. ln (2 * pi * real n) / 2 + real n * ln (real n) - real n)"
  have "eventually (\<lambda>n. ln (fact n) - f n \<in> {0..1/(12*real n)}) at_top"
    using eventually_gt_at_top[of "1::nat"]
  proof eventually_elim
    case (elim n)
    with ln_fact_bounds[of n] show ?case by (simp add: f_def)
  qed
  hence "eventually (\<lambda>n. norm (ln (fact n) - f n) \<le> (1/12) * norm (1 / real n)) at_top"
    using eventually_gt_at_top[of "0::nat"] by eventually_elim (simp_all add: field_simps)
  thus "(\<lambda>n. ln (fact n) - f n) \<in> O(\<lambda>n. 1 / real n)" 
    using bigoI[of "\<lambda>n. ln (fact n) - f n" "1/12" "\<lambda>n. 1 / real n"] by simp
  also have "(\<lambda>n. 1 / real n) \<in> o(f)" unfolding f_def by (intro smallo_real_nat_transfer) simp
  finally have "(\<lambda>n. f n + (ln (fact n) - f n)) \<sim> f"
    by (subst asymp_equiv_add_right) simp_all
  hence "(\<lambda>n. ln (fact n)) \<sim> f" by simp
  also have "f \<sim> (\<lambda>n. n * ln n + (ln (2*pi*n)/2 - n))" by (simp add: f_def algebra_simps)
  also have "\<dots> \<sim> (\<lambda>n. n * ln n)" by (subst asymp_equiv_add_right) auto
  finally show "(\<lambda>n. ln (fact n)) \<sim> (\<lambda>n. n * ln n)" .
qed
    
text \<open>
  This leads to the following well-known Big-Omega bound on the number of comparisons 
  that a general sorting algorithm has to make:
\<close>
corollary count_queries_bigomega:
  fixes sorter :: "nat \<Rightarrow> nat sorter"
  assumes sorter: "\<And>n R. linorder_on {..<n} R \<Longrightarrow> 
                         is_sorting R [0..<n] (eval_sorter R (sorter n))"
  defines "Rs \<equiv> \<lambda>n. {R. linorder_on {..<n} R}"
  shows   "(\<lambda>n. count_wc_queries (Rs n) (sorter n)) \<in> \<Omega>(\<lambda>n. n * ln n)"
proof -
  have "(\<lambda>n. n * ln n) \<in> \<Theta>(\<lambda>n. ln (fact n))"
    by (subst bigtheta_sym) (intro asymp_equiv_imp_bigtheta asymp_equiv_intros)
  also have "(\<lambda>n. ln (fact n)) \<in> \<Theta>(\<lambda>n. log 2 (fact n))" by (simp add: log_def)
  also have "(\<lambda>n. log 2 (fact n)) \<in> O(\<lambda>n. count_wc_queries (Rs n) (sorter n))"
  proof (intro bigoI[where c = 1] always_eventually allI, goal_cases)
    case (1 n)
    have "norm (log 2 (fact n)) = log 2 (fact (length [0..<n]))" by simp
    also from sorter[of n] have "\<dots> \<le> real (count_wc_queries (Rs n) (sorter n))" 
      using count_queries_ge[of "[0..<n]" "sorter n"] by (auto simp: Rs_def atLeast0LessThan) 
    also have "\<dots> = 1 * norm \<dots>" by simp
    finally show ?case by simp
  qed
  finally show ?thesis by (simp add: bigomega_iff_bigo)
qed

end
