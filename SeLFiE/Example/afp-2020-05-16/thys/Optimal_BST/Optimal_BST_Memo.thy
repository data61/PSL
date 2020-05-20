section \<open>Memoization\label{sec:memo}\<close>

theory Optimal_BST_Memo
imports
  Optimal_BST
  "Monad_Memo_DP.State_Main"
  "HOL-Library.Product_Lexorder"
  "HOL-Library.RBT_Mapping"
  Optimal_BST_Examples
begin

text \<open>This theory memoizes the recursive algorithms with the help of our generic memoization
framework. Note that currently only the tree building (function @{const Optimal_BST.opt_bst}) is memoized but not the computation of \<open>w\<close>.\<close>

global_interpretation Wpl
where a = a and b = b for a b
defines w_ab = w and wpl_ab = "wpl.wpl w_ab" .

text \<open>First we express @{const argmin} via @{const fold}.
Primarily because we have a monadic version of @{const fold} already.
At the same time we improve efficiency.\<close>

lemma fold_argmin: "fold (\<lambda>x (m,fm). let fx = f x in if fx \<le> fm then (x,fx) else (m,fm)) xs (x,f x)
 = (argmin f (x#xs), f(argmin f (x#xs)))"
by (induction xs arbitrary: x) (auto simp: Let_def split: prod.split)

lemma argmin_fold: "argmin f xs = (case xs of [] \<Rightarrow> undefined |
  x#xs \<Rightarrow> fst(fold (\<lambda>x (m,fm). let fx = f x in if fx \<le> fm then (x,fx) else (m,fm)) xs (x,f x)))"
apply(auto simp:fold_argmin split: list.split)
apply (meson argmin.elims list.distinct(1))
done

text \<open>The actual memoization of the cubic algorithm:\<close>

context Optimal_BST
begin

memoize_fun opt_bst\<^sub>m: opt_bst with_memory dp_consistency_mapping
monadifies (state) opt_bst.simps[unfolded argmin_fold]
(* FIXME why not argmin_argmin2? memoize_prover breaks!
How about opt_bst_wpl?
*)
thm opt_bst\<^sub>m'.simps

memoize_correct
by memoize_prover

lemmas [code] = opt_bst\<^sub>m.memoized_correct

end

text \<open>Code generation:\<close>

global_interpretation Optimal_BST
where w = "w_ab a b"
rewrites "wpl.wpl (w_ab a b) = wpl_ab a b" for a b
defines opt_bst_ab = opt_bst and opt_bst_ab' = opt_bst\<^sub>m'
by(simp add: wpl_ab_def)

text \<open>Examples:\<close>

lemma "opt_bst_ab a_ex1 b_ex1 0 3 = t_opt_ex1"
by eval

lemma "opt_bst_ab a_ex2 b_ex2 0 13 = t_opt_ex2"
by eval

end
