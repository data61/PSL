(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Preliminaries\<close>
section \<open>Errorable\<close>
theory Errorable
  imports Main
begin

notation bot ("\<bottom>")

typedef 'a errorable ("_\<^sub>\<bottom>" [21] 21) = "UNIV :: 'a option set" ..

definition errorable :: "'a \<Rightarrow> 'a errorable" ("_\<^sub>\<bottom>" [1000] 1000) where
  "errorable x = Abs_errorable (Some x)"

instantiation errorable :: (type) bot
begin
definition "\<bottom> \<equiv> Abs_errorable None"
instance ..
end

free_constructors case_errorable for
  errorable
| "\<bottom> :: 'a errorable"
  unfolding errorable_def bot_errorable_def
  apply (metis Abs_errorable_cases not_None_eq)
  apply (metis Abs_errorable_inverse UNIV_I option.inject)
  by (simp add: Abs_errorable_inject)

copy_bnf 'a errorable

end
