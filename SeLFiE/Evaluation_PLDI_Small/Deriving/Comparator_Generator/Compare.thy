(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Compare\<close>

theory Compare
imports Comparator
keywords "compare_code" :: thy_decl
begin

text \<open>This introduces a type class for having a proper comparator, similar to @{class linorder}.
  Since most of the Isabelle/HOL algorithms work on the latter, we also provide a method which 
  turns linear-order based algorithms into comparator-based algorithms, where two consecutive 
  invocations of linear orders and equality are merged into one comparator invocation.
  We further define a class which both define a linear order and a comparator, and where the
  induces orders coincide.\<close>

class compare =
  fixes compare :: "'a comparator"
  assumes comparator_compare: "comparator compare"
begin

lemma compare_Eq_is_eq [simp]:
  "compare x y = Eq \<longleftrightarrow> x = y"
  by (rule comparator.eq [OF comparator_compare])
  
lemma compare_refl [simp]:
  "compare x x = Eq"
  by simp

end

lemma (in linorder) le_lt_comparator_of:
  "le_of_comp comparator_of = (\<le>)" "lt_of_comp comparator_of = (<)"
  by (intro ext, auto simp: comparator_of_def le_of_comp_def lt_of_comp_def)+

class compare_order = ord + compare +
  assumes ord_defs: "le_of_comp compare = (\<le>) " "lt_of_comp compare = (<)"

text \<open> @{class compare_order} is @{class compare} and @{class linorder}, where comparator and orders 
  define the same ordering.\<close>

subclass (in compare_order) linorder
  by (unfold ord_defs[symmetric], rule comparator.linorder, rule comparator_compare)

context compare_order
begin

lemma compare_is_comparator_of: 
  "compare = comparator_of" 
proof (intro ext)
  fix x y :: 'a
  show "compare x y = comparator_of x y"
    by  (unfold comparator_of_def, unfold ord_defs[symmetric] lt_of_comp_def, 
      cases "compare x y", auto)
qed

lemmas two_comparisons_into_compare = 
  comparator.two_comparisons_into_case_order[OF comparator_compare, unfolded ord_defs]
  
thm two_comparisons_into_compare
end

ML_file \<open>compare_code.ML\<close>

text \<open>\<open>Compare_Code.change_compare_code const ty-vars\<close> changes the code equations of some constant such that
  two consecutive comparisons via @{term "(<=)"}, @{term "(<)"}", or @{term "(=)"} are turned into one
  invocation of @{const compare}. 
  The difference to a standard \<open>code_unfold\<close> is that here we change the code-equations
  where an additional sort-constraint on @{class compare_order} can be added. Otherwise, there would
  be no @{const compare}-function.\<close>

end
