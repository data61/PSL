(*
  File:    Pell_Algorithm_Test.thy
  Author:  Manuel Eberl, TU München

  Tests for the executable algorithms for Pell's equation.
*)

subsubsection \<open>Tests\<close>
theory Pell_Algorithm_Test
imports
  Pell_Algorithm
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Code_Lazy"
begin

code_lazy_type stream

value "find_fund_sol 73"
value "find_fund_sol 106"

value "stake 100 (pell_solutions 73)"
value "snth (pell_solutions 73) 600"

value "find_nth_solution 73 600"
value "find_nth_solution 106 10"

end