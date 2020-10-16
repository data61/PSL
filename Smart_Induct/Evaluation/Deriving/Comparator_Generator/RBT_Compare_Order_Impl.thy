subsection \<open>Example: Modifying the Code-Equations of Red-Black-Trees\<close>

theory RBT_Compare_Order_Impl
imports
  Compare
  "HOL-Library.RBT_Impl"
begin

text \<open>In the following, we modify all code-equations of the red-black-tree 
  implementation that perform comparisons. As a positive result, they now all require
  one invocation of comparator, where before two comparisons have been performed.
  The disadvantage of this simple solution is the additional class constraint on
  @{class compare_order}.\<close>

compare_code ("'a") rbt_ins
compare_code ("'a") rbt_lookup
compare_code ("'a") rbt_del
compare_code ("'a") rbt_map_entry
compare_code ("'a") sunion_with
compare_code ("'a") sinter_with

export_code rbt_ins rbt_lookup rbt_del rbt_map_entry rbt_union_with_key rbt_inter_with_key in Haskell

end
