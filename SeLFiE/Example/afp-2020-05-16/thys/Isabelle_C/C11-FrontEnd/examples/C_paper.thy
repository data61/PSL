(******************************************************************************
 * Isabelle/C
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

chapter \<open>Examples from the F-IDE Paper\<close>

theory C_paper
  imports "../C_Main"
begin

text \<open> This theory contains the examples presented in F-IDE
2019~\cite{Tuong-IsabelleC:2019}. \<close>

section \<open>Setup\<close>

ML\<open>
\<comment> \<open>Annotation Commands Mimicking the \<^theory_text>\<open>setup\<close> command\<close>
val _ = Theory.setup
          (C_Inner_Syntax.command C_Inner_Isar_Cmd.setup' C_Parse.ML_source ("\<simeq>setup", \<^here>, \<^here>))

val C' = C_Module.C'

fun C opt = case opt of NONE => C' (C_Module.env (Context.the_generic_context ()))
                      | SOME env => C' env

fun C_def dir name _ _ =
  Context.map_theory 
    (C_Inner_Syntax.command'
      (C_Inner_Syntax.drop1
        (C_Scan.Right ( (fn src => fn context =>
                          C' (C_Stack.Data_Lang.get' context |> #2) src context)
                      , dir)))
      C_Parse.C_source
      name)

\<comment> \<open>Defining the ML Antiquotation \<open>C_def\<close> to define on the fly new C annotation commands\<close>
local
in
val _ = Theory.setup
  (ML_Antiquotation.declaration
    @{binding "C_def"}
    (Scan.lift (Parse.sym_ident -- Parse.position Parse.name))
    (fn _ => fn (top_down, (name, pos)) =>
      tap (fn ctxt => Context_Position.reports ctxt [(pos, Markup.keyword1)]) #>
      C_Context.fun_decl
               "cmd" "x" ( "C_def "
                         ^ (case top_down of "\<Up>" => "C_Inner_Syntax.bottom_up"
                                           | "\<Down>" => "C_Env.Top_down"
                                           | _ => error "Illegal symbol")
                         ^ " (\"" ^ name ^ "\", " ^ ML_Syntax.print_position pos ^ ")")))
end
\<close>

text \<open> The next command is predefined here, so that the example below can later refer to the
constant. \<close>
definition [simplified]: "UINT_MAX \<equiv> (2 :: nat) ^ 32 - 1"

section \<open>Defining Annotation Commands\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close> \<open>
local
datatype antiq_hol = Invariant of string (* term *)
val scan_colon = C_Parse.$$$ ":" >> SOME
fun command cmd scan0 scan f =
  C_Annotation.command' cmd "" (K (scan0 -- (scan >> f)
                                      >> K C_Env.Never))
in
val _ = Theory.setup ((* 1 '@' *)
                         command ("INVARIANT", \<^here>) scan_colon C_Parse.term Invariant
                      #> command ("INV", \<^here>) scan_colon C_Parse.term Invariant)
end
\<close>

text\<open>Demonstrating the Effect of Annotation Command Context Navigation \<close>


C \<open>
int sum1(int a)
{
  while (a < 10)
    /*@ @ INV: \<open>\<dots>\<close>
        @ highlight */
    { a = a + 1; }
  return a;
}\<close>



C \<open>
int sum2(int a)
/*@ ++@ INV: \<open>\<dots>\<close>
    ++@ highlight */
{
  while (a < 10)
    { a = a + 1; }
  return a;
}\<close>




C (*NONE*) \<comment> \<open>starting environment = empty\<close> \<open>
int a (int b) { return &a + b + c; }
/*@ \<simeq>setup \<open>fn stack_top => fn env =>
            C (SOME env) \<open>int c = &a + b + c;\<close>\<close>
    \<simeq>setup \<open>fn stack_top => fn env =>
            C  NONE      \<open>int c = &a + b + c;\<close>\<close>
    declare [[C_starting_env = last]]
    C        (*SOME*)    \<open>int c = &a + b + c;\<close>
*/\<close>

section \<open>Proofs inside C-Annotations\<close>

\<comment> \<open>See also: \<^url>\<open>https://gitlri.lri.fr/ftuong/isabelle_c/blob/C/C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_TEC.thy\<close>\<close>

C \<open>
#define SQRT_UINT_MAX 65536
/*@ lemma uint_max_factor [simp]:
      "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
    by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)
*/\<close>

term SQRT_UINT_MAX

section \<open>Scheduling the Effects on the Logical Context\<close>

C \<open>int _;
/*@ @ C \<open>//@ C1 \<open>int _; //@ @ \<simeq>setup\<Down> \<open>@{C_def \<Up> C2}\<close> \
                            @ C1  \<open>//* C2 \<open>int _;\<close>\<close>   \
                            @ C1\<Down> \<open>//* C2 \<open>int _;\<close>\<close>    \<close>\<close>
    @ C \<open>//* C2 \<open>int _;\<close>                                \<close>
      \<simeq>setup \<open>@{C_def \<Up> (* bottom-up *)  C1  }\<close>
      \<simeq>setup \<open>@{C_def \<Down> (* top-down  *) "C1\<Down>"}\<close>
*/\<close>

section \<open>As Summary: A Spaghetti Language --- Bon Appétit!\<close>

text\<open>... with the Bonus of a local C-inside-ML-inside-C-inside-Isar ...\<close>

ML\<open>
fun highlight (_, (_, pos1, pos2)) =
  tap (fn _ => Position.reports_text [((Position.range (pos1, pos2)
                                        |> Position.range_position, Markup.intensify), "")])
\<close>

C (*NONE*) \<comment> \<open> the command starts with a default empty environment \<close>
\<open>int f (int a)
  //@ ++& \<simeq>setup \<open>fn stack_top => fn env => highlight stack_top\<close>
  { /*@ @ \<simeq>setup \<open>fn stack_top => fn env =>
                    C (SOME env) (* the command starts with some provided environment *)
                     \<open>int b = a + b; //@ C1' \<open>int c; //@ @ \<simeq>setup\<Down> \<open>@{C_def \<Up> C2'}\<close> \
                                                         @ C1'  \<open>//* C2' \<open>int d;\<close>\<close>        \
                                                         @ C1'\<Down> \<open>//* C2' \<open>int d;\<close>\<close>        \<close>
                      int b = a + b + c + d;\<close>\<close>
        @ \<simeq>setup \<open>fn stack_top => fn env => C NONE \<open>#define int int
                                                    int b = a + b; //* C2' \<open>int c = b;\<close>\<close>\<close>
          \<simeq>setup \<open>@{C_def \<Up> (* bottom-up *)  C1'  }\<close>
          \<simeq>setup \<open>@{C_def \<Down> (* top-down  *) "C1'\<Down>"}\<close>
     */
    return a + b + c + d; /* explicit highlighting */ }\<close>

text \<open> Note that in the current design-implementation of Isabelle/C, C directives have a
propagation side-effect to any occurring subsequent C annotations, even if C directives are supposed
to be all evaluated before any C code. (Making such effect inexistent would be equally easier to
implement though, this is what was the default behavior of directives in previous versions of
Isabelle/C.)\<close>

end
