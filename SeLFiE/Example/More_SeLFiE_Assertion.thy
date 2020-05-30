theory More_SeLFiE_Assertion
imports "../SeLFiE"
begin

ML\<open> structure More_SeLFiE_Assertion =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Quantifier_Domain;
open Pattern;

infix Imply;

end;
\<close>



declare[[ML_print_depth=100]]

end