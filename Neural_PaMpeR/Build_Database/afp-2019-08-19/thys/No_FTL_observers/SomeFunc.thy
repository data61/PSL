(*
   Author: Mike Stannett
   Date: 27 April 2016
   m.stannett@sheffield.ac.uk
*)
theory SomeFunc
  imports Main
begin


fun  someFunc :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b"  where
    "someFunc P x = (SOME y. (P x y))"

lemma lemSomeFunc:
  assumes "\<exists>y . P x y"
     and  "f = someFunc P"
  shows   "P x (f x)"
proof -
  have "f x = (SOME y. (P x y))" 
    using assms(2) by simp
  thus ?thesis using assms(1) 
    by (simp add: someI_ex)
qed


end
