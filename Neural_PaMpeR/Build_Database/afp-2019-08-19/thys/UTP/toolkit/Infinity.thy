(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Infinity.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section \<open> Infinity Supplement \<close>

theory Infinity
imports HOL.Real
  "HOL-Library.Infinite_Set"
  "Optics.Two"
begin

text \<open>
  This theory introduces a type class \<open>infinite\<close> that guarantees that the
  underlying universe of the type is infinite. It also provides useful theorems
  to prove infinity of the universes for various HOL types.
\<close>

subsection \<open> Type class \<open>infinite\<close> \<close>

text \<open>
  The type class postulates that the universe (carrier) of a type is infinite.
\<close>

class infinite =
  assumes infinite_UNIV [simp]: "infinite (UNIV :: 'a set)"

subsection \<open> Infinity Theorems \<close>

text \<open> Useful theorems to prove that a type's @{const UNIV} is infinite. \<close>

text \<open>
  Note that @{thm [source] infinite_UNIV_nat} is already a simplification rule
  by default.
\<close>

lemmas infinite_UNIV_int [simp]

theorem infinite_UNIV_real [simp]:
"infinite (UNIV :: real set)"
  by (rule infinite_UNIV_char_0)

theorem infinite_UNIV_fun1 [simp]:
"infinite (UNIV :: 'a set) \<Longrightarrow>
 card (UNIV :: 'b set) \<noteq> Suc 0 \<Longrightarrow>
 infinite (UNIV :: ('a \<Rightarrow> 'b) set)"
  apply (erule contrapos_nn)
  apply (erule finite_fun_UNIVD1)
  apply (assumption)
  done

theorem infinite_UNIV_fun2 [simp]:
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a \<Rightarrow> 'b) set)"
  apply (erule contrapos_nn)
  apply (erule finite_fun_UNIVD2)
  done

theorem infinite_UNIV_set [simp]:
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: 'a set set)"
  apply (erule contrapos_nn)
  apply (simp add: Finite_Set.finite_set)
  done

theorem infinite_UNIV_prod1 [simp]:
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: ('a \<times> 'b) set)"
  apply (erule contrapos_nn)
  apply (simp add: finite_prod)
  done

theorem infinite_UNIV_prod2 [simp]:
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a \<times> 'b) set)"
  apply (erule contrapos_nn)
  apply (simp add: finite_prod)
  done

theorem infinite_UNIV_sum1 [simp]:
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: ('a + 'b) set)"
  apply (erule contrapos_nn)
  apply (simp)
  done

theorem infinite_UNIV_sum2 [simp]:
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a + 'b) set)"
  apply (erule contrapos_nn)
  apply (simp)
  done

theorem infinite_UNIV_list [simp]:
"infinite (UNIV :: 'a list set)"
  apply (rule infinite_UNIV_listI)
  done

theorem infinite_UNIV_option [simp]:
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: 'a option set)"
  apply (erule contrapos_nn)
  apply (simp)
  done

theorem infinite_image [intro]:
"infinite A \<Longrightarrow> inj_on f A \<Longrightarrow> infinite (f ` A)"
  apply (metis finite_imageD)
  done

theorem infinite_transfer (*[intro]*) :
"infinite B \<Longrightarrow> B \<subseteq> f ` A \<Longrightarrow> infinite A"
  using infinite_super
  apply (blast)
  done

subsection \<open> Instantiations \<close>

text \<open>
  The instantiations for product and sum types have stronger caveats than in
  principle needed. Namely, it would be sufficient for one type of a product
  or sum to be infinite. A corresponding rule, however, cannot be formulated
  using type classes. Generally, classes are not entirely adequate for the
  purpose of deriving the infinity of HOL types, which is perhaps why a class
  such as @{class infinite} was omitted from the Isabelle/HOL library.
\<close>

instance nat :: infinite by (intro_classes, simp)
instance int :: infinite by (intro_classes, simp)
instance real :: infinite by (intro_classes, simp)
instance "fun" :: (type, infinite) infinite by (intro_classes, simp)
instance set :: (infinite) infinite by (intro_classes, simp)
instance prod :: (infinite, infinite) infinite by (intro_classes, simp)
instance sum :: (infinite, infinite) infinite by (intro_classes, simp)
instance list :: (type) infinite by (intro_classes, simp)
instance option :: (infinite) infinite by (intro_classes, simp)

subclass (in infinite) two  by (intro_classes, auto)
    
end