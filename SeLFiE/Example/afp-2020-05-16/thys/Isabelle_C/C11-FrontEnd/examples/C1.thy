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

chapter \<open>Example: Annotation Navigation and Context Serialization\<close>

theory C1
  imports "../C_Main"
          "HOL-ex.Cartouche_Examples"
begin

text \<open> Operationally, the \<^theory_text>\<open>C\<close> command can be thought of as
behaving as \<^theory_text>\<open>ML\<close>, where it is for example possible to recursively nest C
code in C. Generally, the present chapter assumes a familiarity with all advance concepts of ML as
described in \<^file>\<open>~~/src/HOL/ex/ML.thy\<close>, as well as the concept of ML
antiquotations (\<^file>\<open>~~/src/Doc/Implementation/ML.thy\<close>). However, even if
\<^theory_text>\<open>C\<close> might resemble to \<^theory_text>\<open>ML\<close>, we will now see
in detail that there are actually subtle differences between the two commands.\<close>

section \<open>Setup of ML Antiquotations Displaying the Environment (For Debugging) \<close>

ML\<open>
fun print_top make_string f _ (_, (value, _, _)) _ = tap (fn _ => writeln (make_string value)) o f

fun print_top' _ f _ _ env = tap (fn _ => writeln ("ENV " ^ C_Env.string_of env)) o f

fun print_stack s make_string stack _ _ thy =
  let
    val () = Output.information ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ")
                                 ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () =   stack
            |> split_list
            |> #2
            |> map_index I
            |> app (fn (i, (value, pos1, pos2)) =>
                     writeln ("   " ^ Int.toString (length stack - i) ^ " " ^ make_string value
                              ^ " " ^ Position.here pos1 ^ " " ^ Position.here pos2))
  in thy end

fun print_stack' s _ stack _ env thy =
  let
    val () = Output.information ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ")
                                 ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () = writeln ("ENV " ^ C_Env.string_of env)
  in thy end
\<close>

setup \<open>ML_Antiquotation.inline @{binding print_top}
                               (Args.context
                                >> K ("print_top " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_top'}
                               (Args.context
                                >> K ("print_top' " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_stack}
                               (Scan.peek (fn _ => Scan.option Args.text)
                                >> (fn name => ("print_stack "
                                                ^ (case name of NONE => "NONE"
                                                              | SOME s => "(SOME \"" ^ s ^ "\")")
                                                ^ " " ^ ML_Pretty.make_string_fn)))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_stack'}
                               (Scan.peek (fn _ => Scan.option Args.text)
                                >> (fn name => ("print_stack' "
                                                ^ (case name of NONE => "NONE"
                                                              | SOME s => "(SOME \"" ^ s ^ "\")")
                                                ^ " " ^ ML_Pretty.make_string_fn)))\<close>

declare[[C_lexer_trace]]

section \<open>Introduction to C Annotations: Navigating in the Parsing Stack\<close>

subsection \<open>Basics\<close>

text \<open> Since the present theory \<^file>\<open>C1.thy\<close> is depending on
\<^theory>\<open>Isabelle_C.C_Lexer_Language\<close> and
\<^theory>\<open>Isabelle_C.C_Parser_Language\<close>, the syntax one is writing in the
\<^theory_text>\<open>C\<close> command is C11. Additionally, \<^file>\<open>C1.thy\<close> also
depends on \<^theory>\<open>Isabelle_C.C_Parser_Annotation\<close>, making it possible to write
commands in C comments, called annotation commands, such as
\<^theory_text>\<open>\<approx>setup\<close>. \<close>

C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a = (((0))); /*@ highlight */
                 /*@ \<approx>setup \<open>@{print_stack}\<close> */
                 /*@ \<approx>setup \<open>@{print_top}\<close> */
\<close>

text \<open> In terms of execution order, nested annotation commands are not pre-filtered out of the
C code, but executed when the C code is still being parsed. Since the parser implemented is a LALR
parser \<^footnote>\<open>\<^url>\<open>https://en.wikipedia.org/wiki/LALR\<close>\<close>, C tokens
are uniquely read and treated from left to right. Thus, each nested command is (supposed by default
to be) executed when the parser has already read all C tokens before the comment associated to the
nested command, so when the parser is in a particular intermediate parsing step (not necessarily
final)
\<^footnote>\<open>\<^url>\<open>https://en.wikipedia.org/wiki/Shift-reduce_parser\<close>\<close>. \<close>

text \<open>The command \<^theory_text>\<open>\<approx>setup\<close> is similar to the command
\<^theory_text>\<open>setup\<close> except that the former takes a function with additional
arguments. These arguments are precisely depending on the current parsing state. To better examine
these arguments, it is convenient to use ML antiquotations (be it for printing, or for doing any
regular ML actions like PIDE reporting).

Note that, in contrast with \<^theory_text>\<open>setup\<close>, the return type of the
\<^theory_text>\<open>\<approx>setup\<close> function is not
\<^ML_type>\<open>theory -> theory\<close> but
\<^ML_type>\<open>Context.generic -> Context.generic\<close>. \<close>

C \<comment> \<open>Positional navigation: referring to any previous parsed sub-tree in the stack\<close> \<open>
int a = (((0
      + 5)))  /*@@ \<approx>setup \<open>print_top @{make_string} I\<close>
                 @ highlight
               */
      * 4; 
float b = 7 / 3;
\<close>

text \<open>The special \<open>@\<close> symbol makes the command be executed whenever the first element \<open>E\<close>
 in the stack is about to be irremediably replaced by a more structured parent element (having \<open>E\<close>
as one of its direct children). It is the parent element which is provided to the ML code.

Instead of always referring to the first element of the stack, 
\<open>N\<close> consecutive occurrences of \<open>@\<close> will make the ML code getting as argument the direct parent
of the \<open>N\<close>-th element.\<close>

C \<comment> \<open>Positional navigation: referring to any previous parsed sub-tree in the stack\<close> \<open>
int a = (((0 + 5)))  /*@@ highlight */
      * 4;

int a = (((0 + 5)))  /*@& highlight */
      * 4;

int a = (((0 + 5)))  /*@@@@@ highlight */
      * 4;

int a = (((0 + 5)))  /*@&&&& highlight */
      * 4;
\<close>

text \<open>\<open>&\<close> behaves as \<open>@\<close>, but instead of always giving the designated direct parent to the ML code,
it finds the first parent ancestor making non-trivial changes in the respective grammar rule
(a non-trivial change can be for example the registration of the position of the current AST node
being built).\<close>

C \<comment> \<open>Positional navigation: moving the comment after a number of C token\<close> \<open>
int b = 7 / (3) * 50;
/*@+++@@ highlight */
long long f (int a) {
  while (0) { return 0; }
}
int b = 7 / (3) * 50;
\<close>

text \<open>\<open>N\<close> consecutive occurrences of \<open>+\<close> will delay the interpretation of the comment,
which is ignored at the place it is written. The comment is only really considered after the
C parser has treated \<open>N\<close> more tokens.\<close>

C \<comment> \<open>Closing C comments \<open>*/\<close> must close anything, even when editing ML code\<close> \<open>
int a = (((0 //@ (* inline *) \<approx>setup \<open>fn _ => fn _ => fn _ => fn context => let in (* */ *) context end\<close>
             /*@ \<approx>setup \<open>(K o K o K) I\<close> (*   * /   *) */
         )));
\<close>

C \<comment> \<open>Inline comments with antiquotations\<close> \<open>
 /*@ \<approx>setup\<open>(K o K o K) (fn x => K x @{con\
text (**)})\<close> */ // break of line activated everywhere (also in antiquotations)
int a = 0; //\
@ \<approx>setup\<open>(K o K o K) (fn x => K x @{term \<open>a \
          + b\<close> (* (**) *\      
\     
)})\<close>
\<close>

subsection \<open>Erroneous Annotations Treated as Regular C Comments\<close>

C \<comment> \<open>Permissive Types of Antiquotations\<close> \<open>
int a = 0;
  /*@ \<approx>setup (* Errors: Explicit warning + Explicit markup reporting *)
   */
  /** \<approx>setup (* Errors: Turned into tracing report information *)
   */

  /** \<approx>setup \<open>fn _ => fn _ => fn _ => I\<close> (* An example of correct syntax accepted as usual *)
   */
\<close>

C \<comment> \<open>Permissive Types of Antiquotations\<close> \<open>
int a = 0;
  /*@ \<approx>setup \<open>fn _ => fn _ => fn _ => I\<close>
      \<approx>setup (* Parsing error of a single command does not propagate to other commands *)
      \<approx>setup \<open>fn _ => fn _ => fn _ => I\<close>
      context
   */
  /** \<approx>setup \<open>fn _ => fn _ => fn _ => I\<close>
      \<approx>setup (* Parsing error of a single command does not propagate to other commands *)
      \<approx>setup \<open>fn _ => fn _ => fn _ => I\<close>
      context
   */
  
  /*@ \<approx>setup (* Errors in all commands are all rendered *)
      \<approx>setup (* Errors in all commands are all rendered *)
      \<approx>setup (* Errors in all commands are all rendered *)
   */
  /** \<approx>setup (* Errors in all commands makes the whole comment considered as an usual comment *)
      \<approx>setup (* Errors in all commands makes the whole comment considered as an usual comment *)
      \<approx>setup (* Errors in all commands makes the whole comment considered as an usual comment *)
   */
\<close>

subsection \<open>Bottom-Up vs. Top-Down Evaluation\<close>

ML\<open>
structure Example_Data = Generic_Data (type T = string list
                                       val empty = [] val extend = K empty val merge = K empty)
fun add_ex s1 s2 =
  Example_Data.map (cons s2)
  #> (fn context => let val () = Output.information (s1 ^ s2)
                        val () = app (fn s => writeln ("  Data content: " ^ s))
                                     (Example_Data.get context)
                    in context end)
\<close>

setup \<open>Context.theory_map (Example_Data.put [])\<close>

declare[[ML_source_trace]]
declare[[C_parser_trace]]

C \<comment> \<open>Arbitrary interleaving of effects: \<open>\<approx>setup\<close> vs \<open>\<approx>setup\<Down>\<close>\<close> \<open>
int b,c,d/*@@ \<approx>setup \<open>fn s => fn x => fn env => @{print_top} s x env
                                                #> add_ex "evaluation of " "3_print_top"\<close>
          */,e = 0; /*@@
              \<approx>setup \<open>fn s => fn x => fn env => @{print_top} s x env
                                                #> add_ex "evaluation of " "4_print_top"\<close> */

int b,c,d/*@@ \<approx>setup\<Down> \<open>fn s => fn x => fn env => @{print_top} s x env
                                                #> add_ex "evaluation of " "6_print_top"\<close>
          */,e = 0; /*@@
              \<approx>setup\<Down> \<open>fn s => fn x => fn env => @{print_top} s x env
                                                #> add_ex "evaluation of " "5_print_top"\<close> */
\<close>

section \<open>Reporting of Positions and Contextual Update of Environment\<close>

text \<open>
To show the content of the parsing environment, the ML antiquotations \<open>print_top'\<close> and \<open>print_stack'\<close>
will respectively be used instead of \<open>print_top\<close> and \<open>print_stack\<close>. 
This example suite allows to explore the bindings represented in the C environment 
and made accessible in PIDE for hovering. \<close>

subsection \<open>Reporting: \<open>typedef\<close>, \<open>enum\<close>\<close> (*\<open>struct\<close>*)

declare [[ML_source_trace = false]]
declare [[C_lexer_trace = false]]

C \<comment> \<open>Reporting of Positions\<close> \<open>
typedef int i, j;
  /*@@ \<approx>setup \<open>@{print_top'}\<close> @highlight */ //@ +++++@ \<approx>setup \<open>@{print_top'}\<close> +++++@highlight
int j = 0;
typedef int i, j;
j jj1 = 0;
j jj = jj1;
j j = jj1 + jj;
typedef i j;
typedef i j;
typedef i j;
i jj = jj;
j j = jj;
\<close>

C \<comment> \<open>Nesting type definitions\<close> \<open>
typedef int j;
j a = 0;
typedef int k;
int main (int c) {
  j b = 0;
  typedef int k;
  typedef k l;
  k a = c;
  l a = 0;
}
k a = a;
\<close>

C \<comment> \<open>Reporting \<open>enum\<close>\<close> \<open>
enum a b; // bound case: undeclared
enum a {aaa}; // define case
enum a {aaa}; // define case: redefined
enum a _; // bound case

__thread (f ( enum a,  enum a vv));

enum a /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.function_definition4\<close>\<close>*/ f (enum a a) {
}

__thread enum a /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.declaration_specifier2\<close>\<close>*/ f (enum a a) {
  enum c {ccc}; // define case
  __thread enum c f (enum c a) {
    return 0;
  }
  enum c /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.nested_function_definition2\<close>\<close>*/ f (enum c a) {
    return 0;
  }
  return 0;
}

enum z {zz}; // define case
int main (enum z *x) /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.parameter_type_list2\<close>\<close>*/ {
  return zz; }
int main (enum a *x, ...) /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.parameter_type_list3\<close>\<close>*/ {
  return zz; }
\<close>

subsection \<open>Continuation Calculus with the C Environment: Presentation in ML\<close>

declare [[C_parser_trace = false]]

ML\<open>
val C = tap o C_Module.C
val C' = C_Module.C'
\<close>

C \<comment> \<open>Nesting C code without propagating the C environment\<close> \<open>
int a = 0;
int b = 7 / (3) * 50
  /*@@@@@ \<approx>setup \<open>fn _ => fn _ => fn _ =>
               C      \<open>int b = a + a + a + a + a + a + a
                       ;\<close> \<close> */;
\<close>

C \<comment> \<open>Nesting C code and propagating the C environment\<close> \<open>
int a = 0;
int b = 7 / (3) * 50
  /*@@@@@ \<approx>setup \<open>fn _ => fn _ => fn env =>
               C' env \<open>int b = a + a + a + a + a + a + a
                       ;\<close> \<close> */;
\<close>

subsection \<open>Continuation Calculus with the C Environment: Presentation with Outer Commands\<close>

ML\<open>
val _ = Theory.setup
          (C_Inner_Syntax.command0 
            (fn src => fn context => C' (C_Stack.Data_Lang.get' context |> #2) src context)
            C_Parse.C_source
            ("C'", \<^here>, \<^here>, \<^here>))
\<close>

C \<comment> \<open>Nesting C code without propagating the C environment\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C  \<open>int b = a + a + a + a + a + a + a;\<close> */;
  int c = b + a + a + a + a + a + a;
} \<close>

C \<comment> \<open>Nesting C code and propagating the C environment\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C' \<open>int b = a + a + a + a + a + a + a;\<close> */;
  int c = b + b + b + b + a + a + a + a + a + a;
} \<close>

C \<comment> \<open>Miscellaneous\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C  \<open>int b = a + a + a + a + a; //@ C' \<open>int c = b + b + b + b + a;\<close> \<close> */;
  int b = 7 / (3) * 50 /*@ C' \<open>int b = a + a + a + a + a; //@ C' \<open>int c = b + b + b + b + a;\<close> \<close> */;
  int c = b + b + b + b + a + a + a + a + a + a;
} \<close>

subsection \<open>Continuation Calculus with the C Environment: Deep-First Nesting vs Breadth-First Folding: Propagation of \<^ML_type>\<open>C_Env.env_lang\<close>\<close>

C \<comment> \<open>Propagation of report environment while manually composing at ML level (with \<open>#>\<close>)\<close>
  \<comment> \<open>In \<open>c1 #> c2\<close>, \<open>c1\<close> and \<open>c2\<close> should not interfere each other.\<close> \<open>
//@ ML \<open>fun C_env src _ _ env = C' env src\<close>
int a;
int f (int b) {
int c = 0; /*@ \<approx>setup \<open>fn _ => fn _ => fn env =>
     C' env \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C' env \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
\<close> */
int e = a + b + c + d;
}\<close>

C \<comment> \<open>Propagation of directive environment (evaluated before parsing)
      to any other annotations (evaluated at parsing time)\<close> \<open>
#undef int
#define int(a,b) int
#define int int
int a;
int f (int b) {
int c = 0; /*@ \<approx>setup \<open>fn _ => fn _ => fn env =>
     C' env \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C' env \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ \<approx>setup \<open>C_env \<open>int e = a + b + c + d;\<close>\<close>\<close>
\<close> */
#undef int
int e = a + b + c + d;
}
\<close>

subsection \<open>Continuation Calculus with the C Environment: Deep-First Nesting vs Breadth-First Folding: Propagation of \<^ML_type>\<open>C_Env.env_tree\<close>\<close>

ML\<open>
structure Data_Out = Generic_Data
  (type T = int
   val empty = 0
   val extend = K empty
   val merge = K empty)

fun show_env0 make_string f msg context =
  Output.information ("(" ^ msg ^ ") " ^ make_string (f (Data_Out.get context)))

val show_env = tap o show_env0 @{make_string} I
\<close>

setup \<open>Context.theory_map (C_Module.Data_Accept.put (fn _ => fn _ => Data_Out.map (fn x => x + 1)))\<close>

C \<comment> \<open>Propagation of Updates\<close> \<open>
typedef int i, j;
int j = 0;
typedef int i, j;
j jj1 = 0;
j jj = jj1; /*@@ \<approx>setup \<open>fn _ => fn _ => fn _ => show_env "POSITION 0"\<close> @\<approx>setup \<open>@{print_top'}\<close> */
typedef int k; /*@@ \<approx>setup \<open>fn _ => fn _ => fn env =>
                          C' env \<open>k jj = jj; //@@ \<approx>setup \<open>@{print_top'}\<close>
                                  k jj = jj + jj1;
                                  typedef k l; //@@ \<approx>setup \<open>@{print_top'}\<close>\<close>
                          #> show_env "POSITION 1"\<close> */
j j = jj1 + jj; //@@ \<approx>setup \<open>@{print_top'}\<close>
typedef i j; /*@@ \<approx>setup \<open>fn _ => fn _ => fn _ => show_env "POSITION 2"\<close> */
typedef i j;
typedef i j;
i jj = jj;
j j = jj;
\<close>

ML\<open>show_env "POSITION 3" (Context.Theory @{theory})\<close>

setup \<open>Context.theory_map (C_Module.Data_Accept.put (fn _ => fn _ => I))\<close>

subsection \<open>Reporting: Scope of Recursive Functions\<close>

declare [[C_starting_env = last]]

C \<comment> \<open>Propagation of Updates\<close> \<open>
int a = 0;
int b = a * a + 0;
int jjj = b;
int main (void main(int *x,int *y),int *jjj) {
  return a + jjj + main(); }
int main2 () {
  int main3 () { main2() + main(); }
  int main () { main2() + main(); }
  return a + jjj + main3() + main(); }
\<close>

C \<open>
int main3 () { main2 (); }
\<close>

declare [[C_starting_env = empty]]

subsection \<open>Reporting: Extensions to Function Types, Array Types\<close>

C \<open>int f (int z);\<close>
C \<open>int * f (int z);\<close>
C \<open>int (* f) (int z /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.declarator1\<close>\<close>*/);\<close>
C \<open>typedef int (* f) (int z);\<close>
C \<open>int f (int z) {}\<close>
C \<open>int * f (int z) {return z;}\<close>
C \<open>int ((* f) (int z1, int z2)) {return z1 + z2;}\<close>
C \<open>int (* (* f) (int z1, int z2)) {return z1 + z2;}\<close>
C \<open>typedef int (* f) (int z); f uuu (int b) {return b;};\<close>
C \<open>typedef int (* (* f) (int z, int z)) (int a); f uuu (int b) {return b;};\<close>
C \<open>struct z { int (* f) (int z); int (* (* ff) (int z)) (int a); };\<close>
C \<open>double (* (* f (int a /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Wrap_Overloading.declarator1\<close>\<close>*/)) (int a, double d)) (char a);\<close>
C \<open>double (* (((* f) []) (int a)) (int b, double c)) (char d) {int a = b + c + d;}\<close>
C \<open>double ((*((f) (int a))) (int a /* \<leftarrow>\<comment> \<open>\<^ML>\<open>C_Grammar_Rule_Lib.doFuncParamDeclIdent\<close>\<close>*/, double)) (char c) {int a = 0;}\<close>

C \<comment> \<open>Nesting functions\<close> \<open>
double (* (* f (int a)) (int a, double)) (char c) {
double (* (* f (int a)) (double a, int a)) (char) {
  return a;
}
}
\<close>

C \<comment> \<open>Old function syntax\<close> \<open>
f (x) int x; {return x;}
\<close>

section \<open>General Isar Commands\<close>

locale zz begin definition "z' = ()"
          end

C \<comment> \<open>Mixing arbitrary commands\<close> \<open>
int a = 0;
int b = a * a + 0;
int jjj = b;
/*@
  @@@ ML \<open>@{lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close> by (ml_tactic \<open>blast_tac ctxt 1\<close>)}\<close>
  definition "a' = ()"
  declare [[ML_source_trace]]
  lemma (in zz) \<open>A \<and> B \<longrightarrow> B \<and> A\<close> by (ml_tactic \<open>blast_tac ctxt 1\<close>)
  definition (in zz) "z = ()"
  corollary "zz.z' = ()"
   apply (unfold zz.z'_def)
  by blast
  theorem "True &&& True" by (auto, presburger?)
*/
\<close>

declare [[ML_source_trace = false]]

C \<comment> \<open>Backslash newlines must be supported by \<^ML>\<open>C_Token.syntax'\<close> (in particular in keywords)\<close> \<open>
//@  lem\
ma (i\
n z\
z) \
\<open>\  
AA \<and> B\
                    \<longrightarrow>\     
                    B \<and> A\    
\
A\<close> b\
y (ml_t\
actic \<open>\
bla\
st_tac c\
txt\
 0\  
001\<close>)
\<close>

section \<open>Starting Parsing Rule\<close>

subsection \<open>Basics\<close>

C \<comment> \<open>Parameterizing starting rule\<close> \<open>
/*@
declare [[C_starting_rule = "statement"]]
C \<open>while (a) {}\<close>
C \<open>a = 2;\<close>
declare [[C_starting_rule = "expression"]]
C \<open>2 + 3\<close>
C \<open>a = 2\<close>
C \<open>a[1]\<close>
C \<open>&a\<close>
C \<open>a\<close>
*/
\<close>

subsection \<open>Embedding in Inner Terms\<close>

term \<open>\<^C> \<comment> \<open>default behavior of parsing depending on the activated option\<close> \<open>0\<close>\<close>
term \<open>\<^C>\<^sub>u\<^sub>n\<^sub>i\<^sub>t \<comment> \<open>force the explicit parsing\<close> \<open>f () {while (a) {}; return 0;} int a = 0;\<close>\<close>
term \<open>\<^C>\<^sub>d\<^sub>e\<^sub>c\<^sub>l \<comment> \<open>force the explicit parsing\<close> \<open>int a = 0; \<close>\<close>
term \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r \<comment> \<open>force the explicit parsing\<close> \<open>a\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<comment> \<open>force the explicit parsing\<close> \<open>while (a) {}\<close>\<close>

declare [[C_starting_rule = "translation_unit"]]

term \<open>\<^C> \<comment> \<open>default behavior of parsing depending on the current option\<close> \<open>int a = 0;\<close>\<close>

subsection \<open>User Defined Setup of Syntax\<close>

setup \<open>C_Module.C_Term.map_expression (fn _ => fn _ => fn _ => @{term "10 :: nat"})\<close>
setup \<open>C_Module.C_Term.map_statement (fn _ => fn _ => fn _ => @{term "20 :: nat"})\<close>
value \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>1\<close> + \<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t\<open>for (;;);\<close>\<close>

setup \<comment> \<open>redefinition\<close> \<open>C_Module.C_Term.map_expression
                           (fn _ => fn _ => fn _ => @{term "1000 :: nat"})\<close>
value \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>1\<close> + \<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t\<open>for (;;);\<close>\<close>

setup \<open>C_Module.C_Term.map_default (fn _ => fn _ => fn _ => @{term "True"})\<close>

subsection \<open>Validity of Context for Annotations\<close>

ML \<open>fun fac x = if x = 0 then 1 else x * fac (x - 1)\<close>

ML \<comment> \<open>Execution of annotations in term possible in (the outermost) \<^theory_text>\<open>ML\<close>\<close> \<open>
\<^term>\<open> \<^C> \<open>int c = 0; /*@ ML \<open>fac 100\<close> */\<close> \<close>
\<close>

definition \<comment> \<open>Execution of annotations in term possible in \<^ML_type>\<open>local_theory\<close> commands (such as \<^theory_text>\<open>definition\<close>)\<close> \<open>
term = \<^C> \<open>int c = 0; /*@ ML \<open>fac 100\<close> */\<close>
\<close>

section \<open>Scopes of Inner and Outer Terms\<close>

ML \<open>
local
fun bind scan ((stack1, (to_delay, stack2)), _) =
  C_Parse.range scan
  >> (fn (src, range) =>
      C_Env.Parsing
        ( (stack1, stack2)
        , ( range
          , C_Inner_Syntax.bottom_up
              (fn _ => fn context =>
                ML_Context.exec
                  (tap (fn _ => Syntax.read_term (Context.proof_of context)
                                                 (Token.inner_syntax_of src)))
                  context)
          , Symtab.empty
          , to_delay)))
in
val _ =
  Theory.setup
    (   C_Annotation.command'
          ("term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r", \<^here>)
          ""
          (bind (C_Token.syntax' (Parse.token Parse.cartouche)))
     #> C_Inner_Syntax.command0
          (C_Inner_Toplevel.keep'' o C_Inner_Isar_Cmd.print_term)
          (C_Token.syntax' (Scan.succeed [] -- Parse.term))
          ("term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r", \<^here>, \<^here>, \<^here>))
end
\<close>

C \<open>
int z = z;
 /*@ C  \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>
     C  \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close> */\<close>
term(*outer*) \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>

C \<open>
int z = z;
 /*@ C  \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>
     C  \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close> */\<close>
term(*outer*) \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>

declare [[C_starting_env = last]]

C \<open>
int z = z;
 /*@ C  \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>
     C  \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
     C' \<open>//@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>\<close>
             term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close> */\<close>
term(*outer*) \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>z\<close>\<close>

declare [[C_starting_env = empty]]

C \<comment> \<open>Propagation of report environment while manually composing at ML level\<close> \<open>
int a;
int f (int b) {
int c = 0;
/*@ \<approx>setup \<open>fn _ => fn _ => fn env =>
     C' env \<open>int d = a + b + c + d; //@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close> term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close> term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close>\<close>
  #> C' env \<open>int d = a + b + c + d; //@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close> term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close>\<close>
  #> C      \<open>int d = a + b + c + d; //@ term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close> term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close>\<close>
\<close>
    term\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close>
    term\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>c\<close> + \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>d\<close>\<close> */
int e = a + b + c + d;
}\<close>

section \<open>Calculation in Directives\<close>

subsection \<open>Annotation Command Classification\<close>

C \<comment> \<open>Lexing category vs. parsing category\<close> \<open>
int a = 0;

// \<comment> \<open>Category 2: only parsing\<close>

//@   \<approx>setup  \<open>K (K (K I))\<close> (* evaluation at parsing *)
//@@  \<approx>setup\<Down> \<open>K (K (K I))\<close> (* evaluation at parsing *)

//@   highlight             (* evaluation at parsing *)
//@@  highlight\<Down>            (* evaluation at parsing *)

// \<comment> \<open>Category 3: with lexing\<close>

//@  #setup  I              (* evaluation at lexing (and directives resolving) *)
//@   setup  I              (* evaluation at parsing *)
//@@  setup\<Down> I              (* evaluation at parsing *)

//@  #ML     I              (* evaluation at lexing (and directives resolving) *)
//@   ML     I              (* evaluation at parsing *)
//@@  ML\<Down>    I              (* evaluation at parsing *)

//@  #C     \<open>\<close>              (* evaluation at lexing (and directives resolving) *)
//@   C     \<open>\<close>              (* evaluation at parsing *)
//@@  C\<Down>    \<open>\<close>              (* evaluation at parsing *)
\<close>

C \<comment> \<open>Scheduling example\<close> \<open>
//@+++++   ML  \<open>writeln "2"\<close>
int a = 0;
//@@       ML\<Down> \<open>writeln "3"\<close>
//@       #ML  \<open>writeln "1"\<close>
\<close>

C \<comment> \<open>Scheduling example\<close> \<open>
//*  lemma True  by simp
//* #lemma True #by simp
//* #lemma True  by simp
//*  lemma True #by simp
\<close>

C \<comment> \<open>Scheduling example\<close> \<open> /*@
lemma \<open>1 = one\<close>
      \<open>2 = two\<close>
      \<open>two + one = three\<close>
by auto

#definition [simp]: \<open>three = 3\<close>
#definition [simp]: \<open>two   = 2\<close>
#definition [simp]: \<open>one   = 1\<close>
*/ \<close>

subsection \<open>Generalizing ML Antiquotations with C Directives\<close>

ML \<open>
structure Directive_setup_define = Generic_Data
  (type T = int
   val empty = 0
   val extend = K empty
   val merge = K empty)

fun setup_define1 pos f =
  C_Directive.setup_define
    pos
    (fn toks => fn (name, (pos1, _)) =>
      tap (fn _ => writeln ("Executing " ^ name ^ Position.here pos1 ^ " (only once)"))
      #> pair (f toks))
    (K I)

fun setup_define2 pos = C_Directive.setup_define pos (K o pair)
\<close>

C \<comment> \<open>General scheme of C antiquotations\<close> \<open>
/*@
    #setup \<comment> \<open>Overloading \<open>#define\<close>\<close> \<open>
      setup_define2
        \<^here>
        (fn (name, (pos1, _)) =>
          op ` Directive_setup_define.get
          #>> (case name of "f3" => curry op * 152263 | _ => curry op + 1)
          #>  tap (fn (nb, _) =>
                    tracing ("Executing antiquotation " ^ name ^ Position.here pos1
                             ^ " (number = " ^ Int.toString nb ^ ")"))
          #>  uncurry Directive_setup_define.put)
    \<close>
*/
#define f1
#define f2 int a = 0;
#define f3
        f1
        f2
        f1
        f3

//@ #setup \<comment> \<open>Resetting \<open>#define\<close>\<close> \<open>setup_define2 \<^here> (K I)\<close>
        f3
#define f3
        f3
\<close>

C \<comment> \<open>Dynamic token computing in \<open>#define\<close>\<close> \<open>

//@ #setup \<open>setup_define1 \<^here> (K [])\<close>
#define f int a = 0;
        f f f f

//@ #setup \<open>setup_define1 \<^here> (fn toks => toks @ toks)\<close>
#define f int b = a;
        f f

//@ #setup \<open>setup_define1 \<^here> I\<close>
#define f int a = 0;
        f f
\<close>

section \<open>Miscellaneous\<close>

C \<comment> \<open>Antiquotations acting on a parsed-subtree\<close> \<open>
# /**/ include  <a\b\\c> // backslash rendered unescaped
f(){0 +  0;} /**/  // val _ : theory => 'a => theory
# /* context */ if if elif
#include <stdio.h>
if then else ;
# /* zzz */  elif /**/
#else\
            
#define FOO  00 0 "" ((
FOO(FOO(a,b,c))
#endif\<close>

C \<comment> \<open>Header-names in directives\<close> \<open>
#define F <stdio.h>
#define G "stdio\h" // expecting an error whenever expanded
#define H "stdio_h" // can be used anywhere without errors
int f = /*F*/ "";
int g = /*G*/ "";
int h =   H   "";

#include F
\<close>

C \<comment> \<open>Parsing tokens as directives only when detecting space symbols before \<open>#\<close>\<close> \<open>/*
 */ \
    \

 //
         #  /*
*/   define /**/ \
 a
a a /*#include <>*/ // must not be considered as a directive
\<close>

C \<comment> \<open>Universal character names in identifiers and Isabelle symbols\<close> \<open>
#include <stdio.h>
int main () {
  char * ó\<^url>ò = "ó\<^url>ò";
  printf ("%s", ó\<^url>ò);
}
\<close>

end
