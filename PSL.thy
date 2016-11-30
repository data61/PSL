(* Read me first.                                                            *)
(* Import this file to install PSL.                                          *)
(* That is all you have to do to install PSL.                                *)
theory PSL
imports "PSLCore/Try_Hard"
begin

text{* Uncomment the following to unleash the power parallelism. *}
(*
ML {* Multithreading.max_threads_update 28 *}
ML {* Goal.parallel_proofs := 1 *}
*)

end