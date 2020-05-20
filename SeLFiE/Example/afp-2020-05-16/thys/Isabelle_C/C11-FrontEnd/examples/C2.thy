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

chapter \<open>Example: A Simple C Program with Directives and Annotations\<close>

theory C2
  imports "../C_Main"
begin

section \<open>A Simplistic Setup: Parse and Store\<close>

text\<open>The following setup just stores the result of the parsed values in the environment.\<close>


ML\<open>
structure Data_Out = Generic_Data
  (type T = (C_Grammar_Rule.start_happy * C_Antiquote.antiq C_Env.stream) list
   val empty = []
   val extend = K empty
   val merge = K empty)

fun get_module thy =
  let val context = Context.Theory thy
  in (Data_Out.get context 
      |> map (apfst (C_Grammar_Rule.start_happy1 #> the)), C_Module.Data_In_Env.get context)
  end
\<close>

setup \<open>Context.theory_map (C_Module.Data_Accept.put
                            (fn ast => fn env_lang =>
                              Data_Out.map (cons (ast, #stream_ignored env_lang |> rev))))\<close>


section \<open>Example of a Possible Semantics for \<open>#include\<close>\<close>

subsection \<open>Implementation\<close>

text \<open> The CPP directive \<^C>\<open>#include _\<close> is used to import signatures of
modules in C. This has the effect that imported identifiers are included in the C environment and,
as a consequence, appear as constant symbols and not as free variables in the output. \<close>

text \<open> The following structure is an extra mechanism to define the effect of \<^C>\<open>#include _\<close> wrt. to
its definition in its environment. \<close>

ML \<open>
structure Directive_include = Generic_Data
  (type T = (Input.source * C_Env.markup_ident) list Symtab.table
   val empty = Symtab.empty
   val extend = K empty
   val merge = K empty)
\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
local
fun return f (env_cond, env) = ([], (env_cond, f env))

val _ =
  Theory.setup
  (Context.theory_map
    (C_Context0.Directives.map
      (C_Context.directive_update ("include", \<^here>)
        ( (return o K I)
        , fn C_Lex.Include (C_Lex.Group2 (toks_bl, _, tok :: _)) =>
               let
                 fun exec file =
                   if exists (fn C_Scan.Left _ => false | C_Scan.Right _ => true) file then
                     K (error ("Unsupported character"
                               ^ Position.here
                                   (Position.range_position
                                     (C_Lex.pos_of tok, C_Lex.end_pos_of (List.last toks_bl)))))
                   else
                     fn (env_lang, env_tree) =>
                       fold
                         (fn (src, data) => fn (env_lang, env_tree) => 
                           let val (name, pos) = Input.source_content src
                           in C_Grammar_Rule_Lib.shadowTypedef0''''
                                name
                                [pos]
                                data
                                env_lang
                                env_tree
                           end)
                         (these (Symtab.lookup (Directive_include.get (#context env_tree))
                                               (String.concat
                                                 (maps (fn C_Scan.Left s => [s] | _ => []) file))))
                         (env_lang, env_tree)
               in
                 case tok of
                   C_Lex.Token (_, (C_Lex.String (_, file), _)) => exec file
                 | C_Lex.Token (_, (C_Lex.File (_, file), _)) => exec file
                 | _ => tap (fn _ => (* not yet implemented *)
                                     warning ("Ignored directive"
                                              ^ Position.here 
                                                  (Position.range_position
                                                    ( C_Lex.pos_of tok
                                                    , C_Lex.end_pos_of (List.last toks_bl)))))
               end |> K |> K
           | _ => K (K I)))))
in end
\<close>

ML \<open>
structure Include =
struct
fun init name vars =
  Context.theory_map
    (Directive_include.map
      (Symtab.update
        (name, map (rpair {global = true, params = [], ret = C_Env.Previous_in_stack}) vars)))

fun append name vars =
  Context.theory_map
    (Directive_include.map
      (Symtab.map_default
        (name, [])
        (rev o fold (cons o rpair {global = true, params = [], ret = C_Env.Previous_in_stack}) vars
             o rev)))

val show =
  Context.theory_map
    (Directive_include.map
      (tap
        (Symtab.dest
         #>
          app (fn (fic, vars) =>
            writeln ("Content of \"" ^ fic ^ "\": "
                     ^ String.concat (map (fn (i, _) => let val (name, pos) = Input.source_content i
                                                        in name ^ Position.here pos ^ " " end)
                                          vars))))))
end
\<close>

setup \<open>Include.append "stdio.h" [\<open>printf\<close>, \<open>scanf\<close>]\<close>

subsection \<open>Tests\<close>

C \<open>
//@ setup \<open>Include.append "tmp" [\<open>b\<close>]\<close>
#include "tmp"
int a = b;

\<close>

C \<open>
int b = 0;
//@ setup \<open>Include.init "tmp" [\<open>b\<close>]\<close>
#include "tmp"
int a = b;
\<close>

C \<open>
int c = 0;
//@ setup \<open>Include.append "tmp" [\<open>c\<close>]\<close>
//@ setup \<open>Include.append "tmp" [\<open>c\<close>]\<close>
#include "tmp"
int a = b + c;
//@ setup \<open>Include.show\<close>
\<close>

section \<open>Working with Pragmas\<close>
C\<open>

#include <stdio.h>
#include /*sdfsdf */ <stdlib.h>
#define a B
#define b(C) 
#pragma   /* just exists syntaxically */
\<close>


text\<open>In the following, we retrieve the C11 AST parsed above. \<close>
ML\<open> val ((C_Ast.CTranslUnit0 (t,u), v)::R, env) = get_module @{theory};
    val u = C_Grammar_Rule_Lib.decode u; 
    C_Ast.CTypeSpec0; \<close>



section \<open>Working with Annotation Commands\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close> \<open>
\<comment> \<open>setup for a dummy ensures : the "Hello World" of Annotation Commands\<close>
local
datatype antiq_hol = Term of string (* term *)

val scan_opt_colon = Scan.option (C_Parse.$$$ ":")

fun msg cmd_name call_pos cmd_pos =
  tap (fn _ =>
        tracing ("\<open>Hello World\<close> reported by \"" ^ cmd_name ^ "\" here" ^ call_pos cmd_pos))

fun command (cmd as (cmd_name, _)) scan0 scan f =
  C_Annotation.command'
    cmd
    ""
    (fn (_, (cmd_pos, _)) =>
      (scan0 -- (scan >> f) >> (fn _ => C_Env.Never |> msg cmd_name Position.here cmd_pos)))
in
val _ = Theory.setup (   C_Inner_Syntax.command_no_range
                           (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup \<open>K (K (K I))\<close>)
                           ("loop", \<^here>, \<^here>)
                      #> command ("ensures", \<^here>) scan_opt_colon C_Parse.term Term
                      #> command ("invariant", \<^here>) scan_opt_colon C_Parse.term Term
                      #> command ("assigns", \<^here>) scan_opt_colon C_Parse.term Term
                      #> command ("requires", \<^here>) scan_opt_colon C_Parse.term Term
                      #> command ("variant", \<^here>) scan_opt_colon C_Parse.term Term)
end
\<close>

C\<open>
/*@ ensures "result >= x && result >= y"
 */

int max(int x, int y) {
  if (x > y) return x; else return y;
}
\<close>

ML\<open> 
val ((C_Ast.CTranslUnit0 (t,u), v)::R, env) = get_module @{theory};
val u = C_Grammar_Rule_Lib.decode u
\<close>


section \<open>C Code: Various Examples\<close>

text\<open>This example suite is drawn from Frama-C and used in our GLA - TPs. \<close>

C\<open>
int sqrt(int a) {
  int i = 0;
  int tm = 1;
  int sum = 1;

  /*@ loop invariant "1 <= sum <= a+tm"
      loop invariant "(i+1)*(i+1) == sum"
      loop invariant "tm+(i*i) == sum"
      loop invariant "1<=tm<=sum"
      loop assigns "i, tm, sum"
      loop variant "a-sum"
   */
  while (sum <= a) {      
    i++;
    tm = tm + 2;
    sum = sum + tm;
  }
  
  return i;
}
\<close>

C\<open>
/*@ requires "n >= 0"
    requires "valid(t+(0..n-1))"
    ensures "exists integer i; (0<=i<n && t[i] != 0) <==> result == 0"
    ensures "(forall integer i; 0<=i<n ==> t[i] == 0) <==> result == 1"
    assigns nothing
 */

int allzeros(int t[], int n) {
  int k = 0;

  /*@ loop invariant "0 <= k <= n"
      loop invariant "forall integer i; 0<=i<k ==> t[i] == 0"
      loop assigns k
      loop variant "n-k"
   */
  while(k < n) {
    if (t[k]) return 0;
    k = k + 1;
  }
  return 1;
}

\<close>

C\<open>

/*@ requires "n >= 0"
    requires "valid(t+(0..n-1))"
    ensures "(forall integer i; 0<=i<n ==> t[i] != v) <==> result == -1"
    ensures "(exists integer i; 0<=i<n && t[i] == v) <==> result == v"
    assigns nothing
 */

int binarysearch(int t[], int n, int v) {
  int l = 0;
  int u = n-1;

  /*@ loop invariant false
   */
  while (l <= u) {
    int m = (l + u) / 2;
    if (t[m] < v) {
      l = m + 1;
    } else if (t[m] > v) {
      u = m - 1;
    }
    else return m; 
  }
  return -1;
}
\<close>


C\<open>
/*@ requires "n >= 0"
    requires "valid(t+(0..n-1))"
    requires "(forall integer i,j; 0<=i<=j<n ==> t[i] <= t[j])"
    ensures "exists integer i; (0<=i<n && t[i] == x) <==> result == 1"
    ensures "(forall integer i; 0<=i<n ==> t[i] != x) <==> result == 0"
    assigns nothing
 */

int linearsearch(int x, int t[], int n) {
  int i = 0;

  /*@ loop invariant "0<=i<=n"
      loop invariant "forall integer j; 0<=j<i ==> (t[j] != x)"
      loop assigns i
      loop variant "n-i"
   */
  while (i < n) {
    if (t[i] < x) {
      i++;
    } else {
      return (t[i] == x);
    }
  }

  return 0;
}
\<close>


section \<open>C Code: A Sorting Algorithm\<close>

C\<open>
#include <stdio.h>
 
int main()
{
  int array[100], n, c, d, position, swap;
 
  printf("Enter number of elements\n");
  scanf("%d", &n);
 
  printf("Enter %d integers\n", n);
 
  for (c = 0; c < n; c++) scanf("%d", &array[c]);
 
  for (c = 0; c < (n - 1); c++)
  {
    position = c;
   
    for (d = c + 1; d < n; d++)
    {
      if (array[position] > array[d])
        position = d;
    }
    if (position != c)
    {
      swap = array[c];
      array[c] = array[position];
      array[position] = swap;
    }
  }

printf("Sorted list in ascending order:\n");
 
  for (c = 0; c < n; c++)
    printf("%d\n", array[c]);
 
  return 0;
}
\<close>

text\<open>A better example implementation:\<close>

C\<open>
#include <stdio.h>
#include <stdlib.h>
 
#define SIZE 10
 
void swap(int *x,int *y);
void selection_sort(int* a, const int n);
void display(int a[],int size);
 
void main()
{
 
    int a[SIZE] = {8,5,2,3,1,6,9,4,0,7};
 
    int i;
    printf("The array before sorting:\n");
    display(a,SIZE);
 
    selection_sort(a,SIZE);
 
    printf("The array after sorting:\n");
    display(a,SIZE);
}
 
/*
    swap two integers
*/
void swap(int *x,int *y)
{
    int temp;
 
    temp = *x;
    *x = *y;
    *y = temp;
}
/*
    perform selection sort
*/
void selection_sort(int* a,const int size)
{
    int i, j, min;
 
    for (i = 0; i < size - 1; i++)
    {
        min = i;
        for (j = i + 1; j < size; j++)
        {
            if (a[j] < a[min])
            {
                min = j;
            }
        }
        swap(&a[i], &a[min]);
    }
}
/*
    display array content
*/
void display(int a[],const int size)
{
    int i;
    for(i=0; i<size; i++)
        printf("%d ",a[i]);
    printf("\n");
}
\<close>

text\<open>Accessing the underlying C11-AST's via the ML Interface.\<close>

ML\<open>
local open C_Ast in
val _ = CTranslUnit0
val ((CTranslUnit0 (t,u), v)::_, _) = get_module @{theory};
val u = C_Grammar_Rule_Lib.decode u
val _ = case u of Left (p1,p2) => writeln (Position.here p1 ^ " " ^ Position.here p2)
                | Right _ => error "Not expecting that value"
val CDeclExt0(x1)::_ = t;
val _ = CDecl0
end
\<close>

section \<open>C Code: Floats Exist\<close>

C\<open>
int a;
float b;
int m() {return 0;}
\<close>

end