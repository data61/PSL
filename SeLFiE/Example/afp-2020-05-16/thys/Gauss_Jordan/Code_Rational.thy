(*  
    Title:      Code_Rational.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Code Generation for rational numbers in Haskell\<close>

theory Code_Rational
imports

  (*VERY IMPORTANT! When code is exported, the order of the imports is very important.
  In this case, I have to import here the following three theories.
  They allow the computation of the Gauss-Jordan algorithm in Haskell*)
  
  Code_Real_Approx_By_Float_Haskell
  Code_Generation_IArrays
    
  (*These theories are necessary for the serialisation:*)
  HOL.Rat
  "HOL-Library.Code_Target_Int"
begin

subsection\<open>Serializations\<close>

text\<open>The following \<open>code_printing code_module\<close> module is the usual way to import libraries 
in Haskell. In this case, we rebind some functions from Data.Ratio. 
See @{url "https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-June/msg00007.html"}\<close>

code_printing code_module Rational \<rightharpoonup> (Haskell)
 \<open>module Rational(fract, numerator, denominator) where

  import qualified Data.Ratio
  import Data.Ratio(numerator, denominator)

  fract (a, b) = a Data.Ratio.% b\<close>

context
includes integer.lifting
begin
lift_definition Frct_integer :: "integer \<times> integer => rat"
  is "Frct :: int \<times> int => rat" .
end

consts Foo::rat
code_datatype Foo

context
includes integer.lifting
begin

lemma [code]:
"Frct a = Frct_integer ((of_int (fst a)), (of_int (snd a)))"
  by (transfer, simp)

lemma [code]:
"Rat.of_int a = Frct_integer (of_int a, 1)"
  by transfer (auto simp: Fract_of_int_eq Rat.of_int_def)

definition numerator :: "rat => int"
where "numerator x = fst (quotient_of x)"

definition denominator :: "rat => int"
where "denominator x = snd (quotient_of x)"

lift_definition numerator_integer :: "rat => integer"
  is "numerator" .

lift_definition denominator_integer :: "rat => integer"
  is "denominator" .

lemma [code]:
"inverse x = Frct_integer (denominator_integer x, numerator_integer x)"
  apply (cases x)
  apply transfer
  apply (auto simp: inverse_eq_divide numerator_def denominator_def quotient_of_Fract One_rat_def)
  done

lemma quotient_of_num_den: "quotient_of x = ((numerator x), (denominator x))"
unfolding numerator_def denominator_def
by simp


lemma [code]: "quotient_of x = (int_of_integer (numerator_integer x), int_of_integer(denominator_integer x))"
by (transfer, simp add: quotient_of_num_den)
end

code_printing
  type_constructor rat \<rightharpoonup> (Haskell) "Prelude.Rational"
  | class_instance rat :: "HOL.equal" => (Haskell) -
  | constant "0 :: rat" \<rightharpoonup> (Haskell) "(Prelude.toRational (0::Integer))"
  | constant "1 :: rat" \<rightharpoonup> (Haskell) "(Prelude.toRational (1::Integer))"
  | constant "Frct_integer" \<rightharpoonup> (Haskell) "Rational.fract (_)"
  | constant "numerator_integer" \<rightharpoonup> (Haskell) "Rational.numerator (_)"
  | constant "denominator_integer" \<rightharpoonup> (Haskell) "Rational.denominator (_)"  
  | constant "HOL.equal :: rat \<Rightarrow> rat \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "(_) == (_)"
  |  constant "(<) :: rat => rat => bool" \<rightharpoonup>
    (Haskell) "_ < _"
  |  constant "(\<le>) :: rat => rat => bool" \<rightharpoonup>
    (Haskell) "_ <= _"
  | constant "(+) :: rat \<Rightarrow> rat \<Rightarrow> rat" \<rightharpoonup>
    (Haskell) "(_) + (_)"
  | constant "(-) :: rat \<Rightarrow> rat \<Rightarrow> rat" \<rightharpoonup>
    (Haskell) "(_) - (_)"
  | constant "(*) :: rat \<Rightarrow> rat \<Rightarrow> rat" \<rightharpoonup>
    (Haskell) "(_) * (_)"
  | constant "(/) :: rat \<Rightarrow> rat \<Rightarrow> rat" \<rightharpoonup>
    (Haskell) " (_) '/ (_)"
 | constant "uminus :: rat => rat" \<rightharpoonup>
    (Haskell) "Prelude.negate"

(*
definition "test1 = (3::rat)"
definition "test2 = (3/9::rat)"
definition "test3 = (3/8 + 8/7::rat)"
definition "test4 = (3/8 - 8/7::rat)"
definition "test5 = (3/8 * 8/7::rat)"
definition "test6 = (3/8 / 8/7::rat)"
definition "test7 = (34 < (53 :: rat))"
definition "test8 = (34 <= (53 :: rat))"
definition "test9 = (inverse (8/5::rat))"
definition "test10 = quotient_of (8/3::rat)"
export_code
  test1
  test2
  test3
  test4
  test5
  test6
  test7
  test8
  test9
  test10
  in Haskell
  module_name "Rational_Haskell"
  file "haskell"
*)
end
