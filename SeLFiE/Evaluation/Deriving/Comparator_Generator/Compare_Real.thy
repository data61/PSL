(*
    Author:      René Thiemann
    License:     LGPL
*)
subsection \<open>Compare Instance for Real Numbers\<close>

theory Compare_Real
imports
  Compare_Generator
  HOL.Real
begin
  
derive (linorder) compare_order real

lemma invert_order_compare_real[simp]: "\<And> x y :: real. invert_order (compare x y) = compare y x" 
  by (simp add: comparator_of_def compare_is_comparator_of)


end
