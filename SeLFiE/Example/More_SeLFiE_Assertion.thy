(*  Title:      SeLFiE/Example/More_SeLFiE_Assertion.thy
    Author:     Yutaka Nagashima

Example SeLFiE assertions built from SeLFiE_Util, Eval_Syntactic_Sugar,
Quantifier_Domain, and Pattern.
*)
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