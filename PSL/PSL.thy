(*  Title:      PSL.thy
    Author:     Yutaka Nagashima, Data61, CSIRO

Import this file to install PSL. That is all you need to do to install PSL.
See ./Example.thy for examples.
*)

theory PSL
imports "Try_Hard"
begin

text\<open> Uncomment the following to unleash the power parallelism. \<close>

ML\<open> Multithreading.max_threads_update 28 \<close>
ML\<open> Multithreading.parallel_proofs := 0; \<close>

end