(*  
    Title:      Code_Bit.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Code Generation for Bits\<close>

theory Code_Bit
imports "HOL-Library.Bit"
begin

text\<open>Implementation for the field of integer numbers module 2.
Experimentally we have checked that the implementation by means of booleans is the fastest one.\<close>

code_datatype "0::bit" "(1::bit)"
code_printing
  type_constructor bit \<rightharpoonup> (SML) "Bool.bool"
 | constant "0::bit" \<rightharpoonup> (SML) "false"
 | constant "1::bit" \<rightharpoonup> (SML) "true"

code_printing
  type_constructor bit \<rightharpoonup> (Haskell) "Bool"
 | constant "0::bit" \<rightharpoonup> (Haskell) "False"
 | constant "1::bit" \<rightharpoonup> (Haskell) "True"
 | class_instance bit :: "HOL.equal" => (Haskell) - (*This is necessary. See the tutorial on code generation, page 29*)


(*Other possible serialisation to Integers with arbitrary precision (performance is similar in PolyML, 
  worse in MLton and Haskell):*)
(*
code_printing
  type_constructor bit \<rightharpoonup> (SML) "IntInf.int"
 | constant "0::bit" \<rightharpoonup> (SML) "0"
 | constant "1::bit" \<rightharpoonup> (SML) "1"
 | constant "(+) :: bit => bit => bit" \<rightharpoonup> (SML) "IntInf.rem ((IntInf.+ ((_), (_))), 2)"
 | constant "( * ) :: bit => bit => bit" \<rightharpoonup> (SML) "IntInf.* ((_), (_))"
 | constant "(/) :: bit => bit => bit" \<rightharpoonup> (SML) "IntInf.* ((_), (_))"
*)
(*
code_printing
  type_constructor bit \<rightharpoonup> (Haskell) "Integer"
 | constant "0::bit" \<rightharpoonup> (Haskell) "0"
 | constant "1::bit" \<rightharpoonup> (Haskell) "1"
 | constant "(+) :: bit => bit => bit" \<rightharpoonup> (Haskell) "Prelude.rem ((_) + (_))  2"
 | constant "( * ) :: bit => bit => bit" \<rightharpoonup> (Haskell) "(_) * (_)"
 | constant "(/) :: bit => bit => bit" \<rightharpoonup> (Haskell) "(_) * (_)"
 | class_instance bit :: "HOL.equal" => (Haskell) - (*This is necessary. See the tutorial on code generation, page 29*)
*)


(*Other possible serialisation to Integers with finite precision (performance is worse):*)
(*
code_printing
  type_constructor bit \<rightharpoonup> (SML) "Int.int"
 | constant "0::bit" \<rightharpoonup> (SML) "0"
 | constant "1::bit" \<rightharpoonup> (SML) "1"
 | constant "(+) :: bit => bit => bit" \<rightharpoonup> (SML) "Int.rem ((Int.+ ((_), (_))), 2)"
 | constant "( * ) :: bit => bit => bit" \<rightharpoonup> (SML) "Int.* ((_), (_))"
 | constant "(/) :: bit => bit => bit" \<rightharpoonup> (SML) "Int.* ((_), (_))"
*)
end
