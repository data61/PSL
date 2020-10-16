theory Boolean_Expression_Example
  imports Boolean_Expression_Checkers Boolean_Expression_Checkers_AList_Mapping
begin

section \<open>Example\<close>

text \<open>Example usage of checkers. We have our own type of Boolean expressions with its own evaluation function:\<close>

datatype 'a bexp =
  Const bool |
  Atom 'a |
  Neg "'a bexp" |
  And "'a bexp" "'a bexp"

fun bval where
"bval (Const b) s = b" |
"bval (Atom a) s = s a" |
"bval (Neg b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"

subsection \<open>Indirect Translation using the Boolean Expression Interface\<close> 

text \<open>Now we translate into @{datatype bool_expr} provided by the checkers interface and show that the 
  semantics remains the same:\<close>

fun bool_expr_of_bexp :: "'a bexp \<Rightarrow> 'a bool_expr" 
where
  "bool_expr_of_bexp (Const b) = Const_bool_expr b" 
| "bool_expr_of_bexp (Atom a) = Atom_bool_expr a" 
| "bool_expr_of_bexp (Neg b) = Neg_bool_expr(bool_expr_of_bexp b)" 
| "bool_expr_of_bexp (And b1 b2) = And_bool_expr (bool_expr_of_bexp b1) (bool_expr_of_bexp b2)"

lemma val_preservation: 
  "val_bool_expr (bool_expr_of_bexp b) s = bval b s"
  by (induction b) auto 

definition "my_taut_test_bool = bool_taut_test o bool_expr_of_bexp"

corollary my_taut_test: 
  "my_taut_test_bool b = (\<forall>s. bval b s)"
  by (simp add: my_taut_test_bool_def val_preservation bool_tests)

subsection \<open>Direct Translation into Reduced Binary Decision Trees\<close> 

text \<open>Now we translate into a reduced binary decision tree, show that the semantics remains the same and 
  the tree is reduced:\<close>

fun ifex_of :: "'a bexp \<Rightarrow> 'a ifex" 
where
  "ifex_of (Const b) = (if b then Trueif else Falseif)" 
| "ifex_of (Atom a) = IF a Trueif Falseif" 
| "ifex_of (Neg b)   = normif Mapping.empty (ifex_of b) Falseif Trueif" 
| "ifex_of (And b1 b2) = normif Mapping.empty (ifex_of b1) (ifex_of b2) Falseif"

lemma val_ifex: 
  "val_ifex (ifex_of b) s = bval b s"
  by (induction b) (simp_all add: agree_Nil val_normif)

theorem reduced_ifex: 
  "reduced (ifex_of b) {}"
  by (induction b) (simp; metis keys_empty reduced_normif)+

definition "my_taut_test_ifex = taut_test ifex_of"

corollary my_taut_test_ifex: 
  "my_taut_test_ifex b = (\<forall>s. bval b s)"
proof -
  interpret reduced_bdt_checkers ifex_of bval
    by (unfold_locales; insert val_ifex reduced_ifex; blast)
  show ?thesis
    by (simp add: my_taut_test_ifex_def taut_test)
qed

subsection \<open>Test: Pigeonhole Formulas\<close>

definition "Or b1 b2 == Neg (And (Neg b1) (Neg b2))"
definition "ors = foldl Or (Const False)"
definition "ands = foldl And (Const True)"

definition "pc n = ands[ors[Atom(i,j). j <- [1..<n+1]]. i <- [1..<n+2]]"
definition "nc n = ands[Or (Neg(Atom(i,k))) (Neg(Atom(j,k))). k <- [1..<n+1], i <- [1..<n+1], j <- [i+1..<n+2]]"

definition "php n = Neg(And (pc n) (nc n))"

text \<open>Takes about 5 secs each; with 7 instead of 6 it takes about 4 mins (2015).\<close>

lemma "my_taut_test_bool (php 6)"
  by eval

lemma "my_taut_test_ifex (php 6)"
  by eval 

end
