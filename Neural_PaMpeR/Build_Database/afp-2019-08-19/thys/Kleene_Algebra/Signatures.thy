(* Title:      Signatures for Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Signatures\<close>

theory Signatures
imports Main
begin

text \<open>
Default notation in Isabelle/HOL is occasionally different from
established notation in the relation/algebra community. We use the
latter where possible.
\<close>

notation
  times (infixl "\<cdot>" 70)

text \<open>
Some classes in our algebraic hierarchy are most naturally defined as
subclasses of two (or more) superclasses that impose different
restrictions on the same parameter(s).

Alas, in Isabelle/HOL, a class cannot have multiple superclasses that
independently declare the same parameter(s). One workaround, which
motivated the following syntactic classes, is to shift the parameter
declaration to a common superclass.
\<close>

class star_op =
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)

class omega_op =
  fixes omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100)

(*
class residual_r_op =
  fixes residual_r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60)

class residual_l_op =
  fixes residual_l :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60)
*)

text \<open>
We define a type class that combines addition and the definition of
order in, e.g., semilattices. This class makes the definition of
various other type classes more slick.
\<close>

class plus_ord = plus + ord +
  assumes less_eq_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and less_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

end
