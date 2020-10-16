(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Defining Comparators and Compare-Instances for Common Types\<close>

theory Compare_Instances
imports
  Compare_Generator
  "HOL-Library.Char_ord"
begin


text \<open>For all of the following types, we define comparators and register them in the class 
  @{class compare}:
  @{type int}, @{type integer}, @{type nat}, @{type char}, @{type bool}, @{type unit}, @{type sum}, @{type option}, @{type list},
  and @{type prod}. We do not register those classes in @{class compare_order} where
  so far no linear order is defined, in particular if there are conflicting orders, like pair-wise or
  lexicographic comparison on pairs.\<close>

text \<open>For @{type int}, @{type nat}, @{type integer} and @{type char} we just use their linear orders as comparators.\<close>
derive (linorder) compare_order int integer nat char

text \<open>For @{type sum}, @{type list}, @{type prod}, and @{type option} we generate comparators 
  which are however are not used to instantiate @{class linorder}.\<close>
derive compare sum list prod option

text \<open>We do not use the linear order to define the comparator for @{typ bool} and @{typ unit}, 
  but implement more efficient ones.\<close>

fun comparator_unit :: "unit comparator" where
  "comparator_unit x y = Eq"

fun comparator_bool :: "bool comparator" where
  "comparator_bool False False = Eq"
| "comparator_bool False True = Lt"
| "comparator_bool True True = Eq"
| "comparator_bool True False = Gt"

lemma comparator_unit: "comparator comparator_unit"
  by (unfold_locales, auto)

lemma comparator_bool: "comparator comparator_bool"
proof
  fix x y z :: bool
  show "invert_order (comparator_bool x y) = comparator_bool y x" by (cases x, (cases y, auto)+)
  show "comparator_bool x y = Eq \<Longrightarrow> x = y" by (cases x, (cases y, auto)+)
  show "comparator_bool x y = Lt \<Longrightarrow> comparator_bool y z = Lt \<Longrightarrow> comparator_bool x z = Lt"
    by (cases x, (cases y, auto), cases y, (cases z, auto)+)
qed


local_setup \<open>
  Comparator_Generator.register_foreign_comparator @{typ unit}
    @{term comparator_unit}
    @{thm comparator_unit}
\<close>

local_setup \<open>
  Comparator_Generator.register_foreign_comparator @{typ bool}
    @{term comparator_bool}
    @{thm comparator_bool}
\<close>

derive compare bool unit

text \<open>It is not directly possible to \<open>derive (linorder) bool unit\<close>, since 
  @{term "compare :: bool comparator"}
  was not defined as @{term "comparator_of :: bool comparator"}, but as
  @{const comparator_bool}.
  However, we can manually prove this equivalence
  and then use this knowledge to prove the instance of @{class compare_order}.\<close>

lemma comparator_bool_comparator_of [compare_simps]:
  "comparator_bool = comparator_of"
proof (intro ext)
  fix a b 
  show "comparator_bool a b = comparator_of a b"
    unfolding comparator_of_def
    by (cases a, (cases b, auto))
qed

lemma comparator_unit_comparator_of [compare_simps]:
  "comparator_unit = comparator_of"
proof (intro ext)
  fix a b 
  show "comparator_unit a b = comparator_of a b"
    unfolding comparator_of_def by auto
qed

derive (linorder) compare_order bool unit
end
