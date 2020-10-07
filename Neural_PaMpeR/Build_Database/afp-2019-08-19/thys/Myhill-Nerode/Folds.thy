(* Author: Xingyuan Zhang, Chunhan Wu, Christian Urban *)
theory Folds
imports "Regular-Sets.Regular_Exp"
begin

section \<open>``Summation'' for regular expressions\<close>

text \<open>
  To obtain equational system out of finite set of equivalence classes, a fold operation
  on finite sets \<open>folds\<close> is defined. The use of \<open>SOME\<close> makes \<open>folds\<close>
  more robust than the \<open>fold\<close> in the Isabelle library. The expression \<open>folds f\<close>
  makes sense when \<open>f\<close> is not \<open>associative\<close> and \<open>commutitive\<close>,
  while \<open>fold f\<close> does not.  
\<close>


definition 
  folds :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
where
  "folds f z S \<equiv> SOME x. fold_graph f z S x"

text \<open>Plus-combination for a set of regular expressions\<close>

abbreviation
  Setalt :: "'a rexp set \<Rightarrow> 'a rexp" ("\<Uplus>_" [1000] 999) 
where
  "\<Uplus>A \<equiv> folds Plus Zero A"

text \<open>
  For finite sets, @{term Setalt} is preserved under @{term lang}.
\<close>

lemma folds_plus_simp [simp]:
  fixes rs::"('a rexp) set"
  assumes a: "finite rs"
  shows "lang (\<Uplus>rs) = \<Union> (lang ` rs)"
unfolding folds_def
apply(rule set_eqI)
apply(rule someI2_ex)
apply(rule_tac finite_imp_fold_graph[OF a])
apply(erule fold_graph.induct)
apply(auto)
done

end
