(* Author: Tobias Nipkow *)

theory Optimal_BST_Examples
imports "HOL-Library.Tree"
begin

text \<open>Example by Mehlhorn:\<close>

definition a_ex1 :: "int \<Rightarrow> nat" where
"a_ex1 i = [4,0,0,3,10] ! nat i"

definition b_ex1 :: "int \<Rightarrow> nat" where
"b_ex1 i = [1,3,3,0] ! nat i"

definition t_opt_ex1 :: "int tree" where
"t_opt_ex1 = \<langle>\<langle>\<langle>\<rangle>, 0, \<langle>\<langle>\<rangle>, 1, \<langle>\<rangle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>"

text \<open>Example by Knuth:\<close>

definition a_ex2 :: "int \<Rightarrow> nat" where
"a_ex2 i = 0"

definition b_ex2 :: "int \<Rightarrow> nat" where
"b_ex2 i = [32,7,69,13,6,15,10,8,64,142,22,79,18,9] ! nat i"

definition t_opt_ex2 :: "int tree" where
"t_opt_ex2 =
  \<langle>
   \<langle>
    \<langle>\<langle>\<rangle>, 0, \<langle>\<langle>\<rangle>, 1, \<langle>\<rangle>\<rangle>\<rangle>,
    2,
    \<langle>
     \<langle>
      \<langle>\<langle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 4, \<langle>\<rangle>\<rangle>\<rangle>,
      5,
      \<langle>\<langle>\<rangle>, 6, \<langle>\<langle>\<rangle>, 7, \<langle>\<rangle>\<rangle>\<rangle>
     \<rangle>,
     8,
     \<langle>\<rangle>
    \<rangle>
   \<rangle>,
   9,
   \<langle>\<langle>\<langle>\<rangle>, 10, \<langle>\<rangle>\<rangle>,
    11,
    \<langle>\<langle>\<rangle>, 12, \<langle>\<langle>\<rangle>, 13, \<langle>\<rangle>\<rangle>
    \<rangle>
   \<rangle>
  \<rangle>"

end
