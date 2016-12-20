(*  Title:      PSL.thy
    Author:     Yutaka Nagashima, Data61, CSIRO

Import this file to install PSL. That is all you need to do to install PSL.
See ./Example.thy for examples.
*)

theory PSL
imports Try_Hard
begin

text{* Uncomment the following to unleash the power parallelism. *}
(*
ML {* Multithreading.max_threads_update 28 *}
ML {* Goal.parallel_proofs := 1 *}
*)

end