(******************************************************************************
 * Clean
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

(*
 * SquareRoot_concept --- Example of monadic symbolic execution for a WHILE program.
 * Burkhart Wolff and Chantal Keller, LRI, Univ. Paris-Sud, France
 *)

section \<open> The Squareroot Example for Symbolic Execution \<close>

theory SquareRoot_concept
  imports Test_Clean
begin


subsection\<open> The Conceptual Algorithm in Clean Notation\<close>

text\<open> In high-level notation, the algorithm we are investigating looks like this:

@{cartouche [display=true]
\<open>\<open>
function_spec sqrt (a::int) returns int
pre          "\<open>0 \<le> a\<close>"
post         "\<open>\<lambda>res::int.  (res + 1)\<^sup>2 > a \<and> a \<ge> (res)\<^sup>2\<close>"
defines      " (\<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               return\<^sub>C result_value_update \<open>i\<close>
               )"
\<close>\<close>}

\<close>


subsection\<open> Definition of the Global State \<close>

text\<open>The state is just a record; and the global variables correspond to fields in this
     record. This corresponds to typed, structured, non-aliasing states.
     Note that the types in the state can be arbitrary HOL-types - want to have
     sets of functions in a ghost-field ? No problem !
    \<close>

text\<open> The state of the square-root program looks like this : \<close>

typ "Clean.control_state"

ML\<open>
val Type(s,t) = StateMgt_core.get_state_type_global @{theory}
val Type(u,v) = @{typ unit}
\<close>

(* could also be local variable, we flipped a coin and it became this way *)
global_vars state
   tm    :: int
   i     :: int
   sqsum :: int


ML\<open>
val Type(s,t) = StateMgt_core.get_state_type_global @{theory}
val Type(u,v) = @{typ unit}
\<close>


(* should be automatic *)
lemma tm_independent [simp]: "\<sharp> tm_update"
  unfolding control_independence_def  by auto

lemma i_independent [simp]: "\<sharp> i_update"
  unfolding control_independence_def  by auto

lemma sqsum_independent [simp]: "\<sharp> sqsum_update"
  unfolding control_independence_def  by auto





subsection\<open> Setting for Symbolic Execution \<close>

text\<open> Some lemmas to reason about memory\<close>

lemma tm_simp : "tm (\<sigma>\<lparr>tm := t\<rparr>) = t"
  using [[simp_trace]]  by simp
(* from trace:
   [1]Procedure "record" produced rewrite rule:
   tm (?r\<lparr>tm := ?k\<rparr>) \<equiv> ?k

   Unfortunately, this lemma is not exported ... It looks as if it is computed on the fly ...
   This could explain why this is slow for our purposes ...
*)
lemma tm_simp1 : "tm (\<sigma>\<lparr>sqsum := s\<rparr>) = tm \<sigma>" by simp
lemma tm_simp2 : "tm (\<sigma>\<lparr>i := s\<rparr>) = tm \<sigma>" by simp
lemma sqsum_simp : "sqsum (\<sigma>\<lparr>sqsum := s\<rparr>) = s" by simp
lemma sqsum_simp1 : "sqsum (\<sigma>\<lparr>tm := t\<rparr>) = sqsum \<sigma>" by simp
lemma sqsum_simp2 : "sqsum (\<sigma>\<lparr>i := t\<rparr>) = sqsum \<sigma>" by simp
lemma i_simp : "i (\<sigma>\<lparr>i := i'\<rparr>) = i'" by simp
lemma i_simp1 : "i (\<sigma>\<lparr>tm := i'\<rparr>) = i \<sigma>" by simp
lemma i_simp2 : "i (\<sigma>\<lparr>sqsum := i'\<rparr>) = i \<sigma>" by simp

lemmas memory_theory =
  tm_simp tm_simp1 tm_simp2
  sqsum_simp sqsum_simp1 sqsum_simp2
  i_simp i_simp1 i_simp2


declare memory_theory [memory_theory]


lemma non_exec_assign_globalD':
  assumes "\<sharp> upd"
  shows   "\<sigma> \<Turnstile> assign_global upd rhs ;- M \<Longrightarrow>\<not> exec_stop \<sigma> \<Longrightarrow>  upd (\<lambda>_. rhs \<sigma>) \<sigma> \<Turnstile> M"
  apply(drule non_exec_assign_global'[THEN iffD1])
  using assms exec_stop_vs_control_independence apply blast
  by auto

lemmas non_exec_assign_globalD'_tm = non_exec_assign_globalD'[OF tm_independent]
lemmas non_exec_assign_globalD'_i = non_exec_assign_globalD'[OF i_independent]
lemmas non_exec_assign_globalD'_sqsum = non_exec_assign_globalD'[OF sqsum_independent]

text\<open> Now we run a symbolic execution. We run match-tactics (rather than the Isabelle simplifier
  which would do the trick as well) in order to demonstrate a symbolic execution in Isabelle. \<close>


subsection\<open> A Symbolic Execution Simulation \<close>


lemma
  assumes non_exec_stop[simp]: "\<not> exec_stop \<sigma>\<^sub>0"
   and    pos : "0 \<le> (a::int)"
   and    annotated_program:
          "\<sigma>\<^sub>0 \<Turnstile> \<open>tm := 1\<close> ;-
                \<open>sqsum := 1\<close> ;-
                \<open>i := 0\<close> ;-
                (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do
                   \<open>i := i+1\<close> ;-
                   \<open>tm := tm + 2\<close> ;-
                   \<open>sqsum := tm + sqsum\<close>
                od) ;-
                assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"

       shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i\<^sup>2  \<le> a \<and> a < (i + 1)\<^sup>2\<close> "


  apply(insert annotated_program)

  apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_tm\"}] 1",simp)
  apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_sqsum\"}] 1",simp)
  apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_i\"}] 1",simp)

  apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
  apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
   apply(simp_all only: memory_theory MonadSE.bind_assoc')

   apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_i\"}] 1",simp)
   apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_tm\"}] 1",simp)
   apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_sqsum\"}] 1",simp)

   apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
    apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
    apply(simp_all only: memory_theory MonadSE.bind_assoc')

    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_i\"}] 1",simp)
    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_tm\"}] 1",simp)
    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_sqsum\"}] 1",simp)

    apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
    apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
    apply(simp_all only: memory_theory MonadSE.bind_assoc')


    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_i\"}] 1",simp)
    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_tm\"}] 1",simp)
    apply(tactic "dmatch_tac @{context} [@{thm \"non_exec_assign_globalD'_sqsum\"}] 1",simp)
     apply(simp_all)

  text\<open>Here are all abstract test-cases explicit. Each subgoal correstponds to
       a path taken through the loop.\<close>


  txt\<open>push away the test-hyp: postcond is true for programs with more than
    three loop traversals (criterion: all-paths(k). This reveals explicitly
    the three test-cases for  @{term "k<3"}. \<close>
   defer 1


(*
txt\<open>Instead of testing, we @{emph \<open>prove\<close>} that the test cases satisfy the
    post-condition for all @{term "k<3"} loop traversals and @{emph \<open>all\<close>}
    positive inputs @{term "a "}.\<close>
   apply(auto  simp: assert_simp)
 *)
oops

text\<open>TODO: re-establish  automatic test-coverage tactics of @{cite "DBLP:conf/tap/Keller18"}.\<close>

end
