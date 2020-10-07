(* Author: Tobias Nipkow *)

section \<open>Code Generation (unmemoized)\<close>

theory Optimal_BST_Code
imports
  Optimal_BST2
  Optimal_BST_Examples
begin

locale Wpl_Optimal_BST = Wpl a b + Optimal_BST where w = "Wpl.w a b" for a b

locale Wpl_Optimal_BST2 = Wpl a b + Optimal_BST2 where w = "Wpl.w a b" for a b

(* Simultaneous interpretation to avoid technical problem *)
global_interpretation Wpl_Optimal_BST + Wpl_Optimal_BST2
defines wpl_ab = wpl and opt_bst_ab = opt_bst and opt_bst2_ab = opt_bst2
proof (standard, unfold Wpl.w_def, goal_cases)
  case (1 i i' j j')
  thus ?case by (simp add: add_mono_thms_linordered_semiring(1) sum_mono2)
next
  note un1 = ivl_disj_un_two(7)[symmetric]
  note un2 = ivl_disj_un_two(8)[symmetric]
  case (2 i i' j j')
  have "{i..<i'} \<inter> {j<..ub} = {}" for ub using \<open>i' \<le> j\<close> by auto
  with 2 show ?case
    using un2[of i' j j'] un1[of i i' j] un1[of i i' j']
          un2[of i' j "j'+1"] un1[of i i' "j+1"] un1[of i i' "j'+1"]
    by (simp add: sum_Un_nat algebra_simps ivl_disj_int Int_Un_distrib)
qed

text \<open>Examples:\<close>

lemma "opt_bst_ab a_ex1 b_ex1 0 3 = t_opt_ex1"
by eval

lemma "opt_bst2_ab a_ex2 b_ex2 0 13 = t_opt_ex2"
by eval

end
