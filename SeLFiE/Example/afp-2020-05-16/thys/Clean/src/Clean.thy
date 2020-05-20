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
 * Clean --- a basic abstract ("shallow") programming language for test and proof.
 * Burkhart Wolff, Frédéric Tuong and Chantal Keller, LRI, Univ. Paris-Saclay, France
 *)

chapter \<open>The Clean Language\<close>

theory Clean
  imports Symbex_MonadSE
  keywords "global_vars" "local_vars_test" :: thy_decl 
     and "returns" "pre" "post" "local_vars" "variant" 
     and "function_spec" :: thy_decl
     and "rec_function_spec"   :: thy_decl

begin

text\<open>Clean (pronounced as: ``C lean'' or ``Céline'' [selin]) is a minimalistic imperative language 
with C-like control-flow operators based on a shallow embedding into the ``State Exception Monads'' theory 
formalized in \<^file>\<open>MonadSE.thy\<close>. It strives for a type-safe notation of program-variables, an
incremental construction of the typed state-space in order to facilitate incremental verification
and open-world extensibility to new type definitions intertwined with the program
definition.

It comprises:
\begin{itemize}
\item C-like control flow with \<^term>\<open>break\<close> and \<^term>\<open>return\<close>,
\item global variables,
\item function calls (seen as monadic executions) with side-effects, recursion
      and local variables,
\item parameters are modeled via functional abstractions 
      (functions are monads); a passing of parameters to local variables
      might be added later,
\item direct recursive function calls,
\item cartouche syntax for \<open>\<lambda>\<close>-lifted update operations supporting global and local variables.
\end{itemize}

Note that Clean in its current version is restricted to \<^emph>\<open>monomorphic\<close> global and local variables
as well as function parameters. This limitation will be overcome at a later stage. The construction
in itself, however, is deeply based on parametric polymorphism (enabling structured proofs over
extensible records as used in languages of the ML family
\<^url>\<open>http://www.cs.ioc.ee/tfp-icfp-gpce05/tfp-proc/21num.pdf\<close>
and Haskell \<^url>\<open>https://www.schoolofhaskell.com/user/fumieval/extensible-records\<close>).
\<close>

(*<*)
text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close> 
(*>*)

section\<open>A High-level Description of the Clean Memory Model\<close>

subsection\<open>A Simple Typed Memory Model of Clean: An Introduction \<close>
text\<open> Clean is based on a ``no-frills'' state-exception monad 
\<^theory_text>\<open>type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = \<open>'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)\<close>\<close> with the 
usual definitions of \<^term>\<open>bind\<close> and \<^term>\<open>unit\<close>.
In this language, sequence operators, conditionals and loops can be integrated. \<close>

text\<open>From a concrete program, the underlying state \<^theory_text>\<open>'\<sigma>\<close> is \<^emph>\<open>incrementally\<close> constructed by a
sequence of extensible record definitions:
\<^enum> Initially, an internal control state is defined to give semantics to \<^term>\<open>break\<close> and
 \<^term>\<open>return\<close> statements:
  \begin{isar}
        record control_state =  break_val  :: bool   return_val :: bool
  \end{isar}
  \<^theory_text>\<open>control_state\<close> represents the $\sigma_0$ state.
\<^enum> Any global variable definition block with definitions $a_1 : \tau_1$ $\dots$ $a_n : \tau_n$  
  is translated into a record extension:
  \begin{isar}
        record \<sigma>$_{n+1}$ = \<sigma>$_n$    +    a$_1$ :: $\tau_1$; ...; $a_n$ :: $\tau_n$
  \end{isar}
\<^enum> Any local variable definition block (as part of a procedure declaration) 
  with definitions $a_1 : \tau_1$ $\dots$ $a_n : \tau_n$ is translated into the record extension:
  \begin{isar}
        record \<sigma>$_{n+1}$ = \<sigma>$_n$    +    a$_1$ :: $\tau_1$ list; ...; $a_n$ :: $\tau_n$ list; result :: $\tau_{result-type}$ list; 
  \end{isar}
  where the \<^typ>\<open>_ list\<close>-lifting is used to model a \<^emph>\<open>stack\<close> of local variable instances
  in case of direct recursions and the \<^term>\<open>result_value\<close> used for the value of the \<^term>\<open>return\<close>
  statement.\<close>

text \<open> The \<^theory_text>\<open>record\<close> package creates an \<^theory_text>\<open>'\<sigma>\<close> extensible record type 
\<^theory_text>\<open>'\<sigma> control_state_ext\<close> where the \<^theory_text>\<open>'\<sigma>\<close> stands for extensions that are subsequently ``stuffed'' in
them. Furthermore, it generates definitions for the constructor, accessor and update functions and
automatically derives a number of theorems over them (e.g., ``updates on different fields commute'',
``accessors on a record are surjective'', ``accessors yield the value of the last update''). The
collection of these theorems constitutes the \<^emph>\<open>memory model\<close> of Clean, providing an incrementally 
extensible state-space for global and local program variables. In contrast to axiomatizations
of memory models, our generated state-spaces might be ``wrong'' in the sense that they do not 
reflect the operational behaviour of a particular compiler or a sufficiently large portion of the 
C language; however, it is by construction \<^emph>\<open>logically consistent\<close> since it is
impossible to derive falsity from the entire set of conservative extension schemes used in their
construction. A particular advantage of the incremental state-space construction is that it
supports incremental verification and interleaving of program definitions with theory development.\<close>

subsection\<open> Formally Modeling Control-States  \<close>

text\<open>The control state is the ``root'' of all extensions for local and global variable
spaces in Clean. It contains just the information of the current control-flow: a \<^term>\<open>break\<close> occurred
(meaning all commands till the end of the control block will be skipped) or a \<^term>\<open>return\<close> occurred
(meaning all commands till the end of the current function body will be skipped).\<close>
  
record  control_state = 
            break_status  :: bool
            return_status :: bool

(* break quits innermost while or for, return quits an entire execution sequence. *)  
definition break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := True \<rparr>))"
  
definition unset_break_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "unset_break_status \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := False \<rparr>))"

definition set_return_status :: " (unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "set_return_status = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := True \<rparr>))"
    
definition unset_return_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "unset_return_status  = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := False \<rparr>))"


definition exec_stop :: "('\<sigma>_ext) control_state_ext \<Rightarrow> bool"
  where   "exec_stop = (\<lambda> \<sigma>. break_status \<sigma> \<or> return_status \<sigma> )"

lemma exec_stop1[simp] : "break_status \<sigma> \<Longrightarrow> exec_stop \<sigma>" 
  unfolding exec_stop_def by simp

lemma exec_stop2[simp] : "return_status \<sigma> \<Longrightarrow> exec_stop \<sigma>" 
  unfolding exec_stop_def by simp

text\<open> On the basis of the control-state, assignments, conditionals and loops are reformulated
  into \<^term>\<open>break\<close>-aware and \<^term>\<open>return\<close>-aware versions as shown in the definitions of
  \<^term>\<open>assign\<close> and \<^term>\<open>if_C\<close> (in this theory file, see below). \<close>

text\<open>For Reasoning over Clean programs, we need the notion of independance of an
     update from the control-block: \<close>


definition control_independence ::
                 "(('b\<Rightarrow>'b)\<Rightarrow>'a control_state_scheme \<Rightarrow> 'a control_state_scheme) \<Rightarrow> bool"    ("\<sharp>")
           where "\<sharp> upd \<equiv> (\<forall>\<sigma> T b. break_status (upd T \<sigma>) = break_status \<sigma> 
                                 \<and> return_status (upd T \<sigma>) = return_status \<sigma>
                                 \<and> upd T (\<sigma>\<lparr> return_status := b \<rparr>) = (upd T \<sigma>)\<lparr> return_status := b \<rparr>
                                 \<and> upd T (\<sigma>\<lparr> break_status := b \<rparr>) = (upd T \<sigma>)\<lparr> break_status := b \<rparr>) "



lemma exec_stop_vs_control_independence [simp]:
  "\<sharp> upd \<Longrightarrow> exec_stop (upd f \<sigma>) = exec_stop \<sigma>"
  unfolding control_independence_def exec_stop_def  by simp


lemma exec_stop_vs_control_independence' [simp]:
  "\<sharp> upd \<Longrightarrow> (upd f (\<sigma> \<lparr> return_status := b \<rparr>)) = (upd f \<sigma>)\<lparr> return_status := b \<rparr>"
  unfolding control_independence_def exec_stop_def by simp

lemma exec_stop_vs_control_independence'' [simp]:
  "\<sharp> upd \<Longrightarrow> (upd f (\<sigma> \<lparr> break_status := b \<rparr>)) = (upd f \<sigma>) \<lparr> break_status := b \<rparr>"
  unfolding control_independence_def exec_stop_def  by simp




subsection\<open>An Example for Global Variable Declarations.\<close>
text\<open>We present the above definition of the incremental construction of the state-space in more
detail via an example construction.

Consider a global variable \<open>A\<close> representing an array of integer. This 
\<^emph>\<open>global variable declaration\<close> corresponds to the effect of the following
record declaration:

\<^theory_text>\<open>record state0 = control_state + A :: "int list"\<close>

which is later extended by another global variable, say, \<open>B\<close> representing a real
described in the Cauchy Sequence form @{typ "nat \<Rightarrow> (int \<times> int)"} as follows:

\<^theory_text>\<open>record state1 = state0 + B :: "nat \<Rightarrow> (int \<times> int)"\<close>.

A further extension would be needed if a (potentially recursive) function \<open>f\<close> with some local
variable \<open>tmp\<close> is defined:
\<^theory_text>\<open>record state2 = state1 + tmp :: "nat stack" result_value :: "nat stack" \<close>, where the \<open>stack\<close>
needed for modeling recursive instances is just a synonym for \<open>list\<close>.
\<close>

subsection\<open> The Assignment Operations (embedded in State-Exception Monad) \<close>
text\<open>Based on the global variable states, we define   \<^term>\<open>break\<close>-aware and \<^term>\<open>return\<close>-aware 
version of the assignment. The trick to do this in a generic \<^emph>\<open>and\<close> type-safe way is to provide
the generated accessor and update functions (the ``lens'' representing this global variable,
cf. @{cite "Foster2009BidirectionalPL" and "DBLP:journals/toplas/FosterGMPS07" and
"DBLP:conf/ictac/FosterZW16"}) to the generic assign operators. This pair of accessor and update
carries all relevant semantic and type information of this particular variable and \<^emph>\<open>characterizes\<close>
this variable semantically. Specific syntactic support~\<^footnote>\<open>via the Isabelle concept of
cartouche: \<^url>\<open>https://isabelle.in.tum.de/doc/isar-ref.pdf\<close>\<close> will hide away the syntactic overhead and permit a human-readable
form of assignments or expressions accessing the underlying state. \<close>


consts syntax_assign :: "('\<alpha>  \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> term" (infix ":=" 60)

definition assign :: "(('\<sigma>_ext) control_state_scheme  \<Rightarrow> 
                       ('\<sigma>_ext) control_state_scheme) \<Rightarrow> 
                       (unit,('\<sigma>_ext) control_state_scheme)MON\<^sub>S\<^sub>E"
  where   "assign f = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>) else Some((), f \<sigma>))"


definition  assign_global :: "(('a  \<Rightarrow> 'a ) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                              \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                              \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where    "assign_global upd rhs = assign(\<lambda>\<sigma>. ((upd) (\<lambda>_. rhs \<sigma>)) \<sigma>)"

text\<open>An update of the variable \<open>A\<close> based on the state of the previous example is done 
by @{term [source = true] \<open>assign_global A_upd (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))\<close>}
representing \<open>A[i] = A[j]\<close>; arbitrary nested updates can be constructed accordingly.\<close>

text\<open>Local variable spaces work analogously; except that they are represented by a stack
in order to support individual instances in case of function recursion. This requires
automated generation of specific push- and pop operations used to model the effect of
entering or leaving a function block (to be discussed later).\<close>


fun      map_hd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" 
  where "map_hd f [] = []"
      | "map_hd f (a#S) = f a # S"

lemma tl_map_hd [simp] :"tl (map_hd f S) = tl S"  by (metis list.sel(3) map_hd.elims) 

definition "map_nth = (\<lambda>i f l. list_update l i (f (l ! i)))"

definition  assign_local :: "(('a list \<Rightarrow> 'a list) 
                                 \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                             \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                             \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where    "assign_local upd rhs = assign(\<lambda>\<sigma>. ((upd o map_hd) (%_. rhs \<sigma>)) \<sigma>)"


text\<open>Semantically, the difference between \<^emph>\<open>global\<close> and \<^emph>\<open>local\<close> is rather unimpressive as the 
     following lemma shows. However, the distinction matters for the pretty-printing setup of Clean.\<close>
lemma "assign_local upd rhs = assign_global (upd o map_hd) rhs "
      unfolding assign_local_def assign_global_def by simp

text\<open>The \<open>return\<close> command in C-like languages is represented basically by an assignment to a local
variable \<open>result_value\<close> (see below in the Clean-package generation), plus some setup of 
\<^term>\<open>return_status\<close>. Note that a \<^term>\<open>return\<close> may appear after a \<^term>\<open>break\<close> and should have no effect
in this case.\<close>

definition return\<^sub>C :: "(('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where   "return\<^sub>C upd rhs =(\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>) 
                                                else (assign_local upd rhs ;- set_return_status) \<sigma>)" 

subsection\<open>Example for a Local Variable Space\<close>
text\<open>Consider the usual operation \<open>swap\<close> defined in some free-style syntax as follows:
@{cartouche [display] \<open>
  function_spec swap (i::nat,j::nat)
  local_vars   tmp :: int 
  defines      " \<open> tmp  := A ! i\<close> ;-
                 \<open> A[i] := A ! j\<close> ;- 
                 \<open> A[j] := tmp\<close> "\<close>}
\<close>

text\<open> 
For the fantasy syntax  \<open>tmp := A ! i\<close>, we can construct the following semantic code:
@{term [source = true] \<open>assign_local tmp_update (\<lambda>\<sigma>. (A \<sigma>) ! i )\<close>} where \<open>tmp_update\<close> is the
update operation generated by the \<^theory_text>\<open>record\<close>-package, which is generated while treating local variables
of \<open>swap\<close>. By the way, a stack for \<open>return\<close>-values is also generated in order to give semantics
to a \<open>return\<close> operation: it is syntactically equivalent to the assignment of 
the result variable  in the local state (stack). It sets the \<^term>\<open>return_val\<close> flag.

The management of the local state space requires function-specific \<open>push\<close> and \<open>pop\<close> operations,
for which suitable definitions are generated as well:

@{cartouche [display]
\<open>definition push_local_swap_state :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
   where   "push_local_swap_state \<sigma> = 
                     Some((),\<sigma>\<lparr>local_swap_state.tmp := undefined # local_swap_state.tmp \<sigma>,
                               local_swap_state.result_value := undefined # 
                                                                  local_swap_state.result_value \<sigma>  \<rparr>)"

 definition pop_local_swap_state :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
   where   "pop_local_swap_state \<sigma> = 
                    Some(hd(local_swap_state.result_value \<sigma>), 
                         \<sigma>\<lparr>local_swap_state.tmp:= tl( local_swap_state.tmp \<sigma>) \<rparr>)"\<close>}
where \<open>result_value\<close> is the stack for potential result values (not needed in the concrete
example \<open>swap\<close>).
\<close>


section\<open> Global and Local State Management via Extensible Records \<close>

text\<open>In the sequel, we present the automation of the state-management as schematically discussed
in the previous section; the declarations of global and local variable blocks are constructed by 
subsequent extensions of @{typ "'a control_state_scheme"}, defined above.\<close>
ML\<open>

structure StateMgt_core = 
struct

val control_stateT = Syntax.parse_typ @{context} "control_state"
val control_stateS = @{typ "('a)control_state_scheme"};

fun optionT t = Type(@{type_name "Option.option"},[t]);
fun MON_SE_T res state = state --> optionT(HOLogic.mk_prodT(res,state));

fun merge_control_stateS (@{typ "('a)control_state_scheme"},t) = t
   |merge_control_stateS (t, @{typ "('a)control_state_scheme"}) = t
   |merge_control_stateS (t, t') = if (t = t') then t else error"can not merge Clean state"

datatype var_kind = global_var of typ | local_var of typ

fun type_of(global_var t) = t | type_of(local_var t) = t

type state_field_tab = var_kind Symtab.table

structure Data = Generic_Data
(
  type T                      = (state_field_tab * typ (* current extensible record *)) 
  val  empty                  = (Symtab.empty,control_stateS)
  val  extend                 = I
  fun  merge((s1,t1),(s2,t2)) = (Symtab.merge (op =)(s1,s2),merge_control_stateS(t1,t2))
);


val get_data                   = Data.get o Context.Proof;
val map_data                   = Data.map;
val get_data_global            = Data.get o Context.Theory;
val map_data_global            = Context.theory_map o map_data;

val get_state_type             = snd o get_data
val get_state_type_global      = snd o get_data_global
val get_state_field_tab        = fst o get_data
val get_state_field_tab_global = fst o get_data_global
fun upd_state_type f           = map_data (fn (tab,t) => (tab, f t))
fun upd_state_type_global f    = map_data_global (fn (tab,t) => (tab, f t))

fun fetch_state_field (ln,X)   = let val a::b:: _  = rev (Long_Name.explode ln) in ((b,a),X) end;

fun filter_name name ln        = let val ((a,b),X) = fetch_state_field ln
                                 in  if a = name then SOME((a,b),X) else NONE end;

fun filter_attr_of name thy    = let val tabs = get_state_field_tab_global thy
                                 in  map_filter (filter_name name) (Symtab.dest tabs) end;

fun is_program_variable name thy = Symtab.defined((fst o get_data_global) thy) name

fun is_global_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(global_var _) => true
                                           | _ => false

fun is_local_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(local_var _) => true
                                           | _ => false

fun declare_state_variable_global f field thy  =  
             let val Const(name,ty) = Syntax.read_term_global thy field
             in  (map_data_global (apfst (Symtab.update_new(name,f ty))) (thy)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

fun declare_state_variable_local f field ctxt  = 
             let val Const(name,ty) = Syntax.read_term_global  (Context.theory_of ctxt) field
             in  (map_data (apfst (Symtab.update_new(name,f ty)))(ctxt)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

end\<close>

subsection\<open>Block-Structures\<close>
text\<open> On the managed local state-spaces, it is now straight-forward to define the semantics for 
a \<open>block\<close> representing the necessary management of local variable instances:
\<close>
definition block\<^sub>C :: "  (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E  
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "block\<^sub>C push core pop \<equiv> (          \<comment> \<open>assumes break and return unset \<close> 
                                   push ;-   \<comment> \<open>create new instances of local variables \<close> 
                                   core ;-   \<comment> \<open>execute the body \<close>
                                   unset_break_status ;-    \<comment> \<open>unset a potential break \<close>
                                   unset_return_status;-    \<comment> \<open>unset a potential return break \<close>
                                   (x \<leftarrow> pop;           \<comment> \<open>restore previous local var instances \<close>
                                    unit\<^sub>S\<^sub>E(x)))"        \<comment> \<open>yield the return value \<close>

text\<open> Based on this definition, the running \<open>swap\<close> example is represented as follows:

@{cartouche [display]
\<open>definition swap_core :: "nat \<times> nat \<Rightarrow>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
    where "swap_core  \<equiv> (\<lambda>(i,j). ((assign_local tmp_update (\<lambda>\<sigma>. A \<sigma> ! i ))   ;-
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) ((hd o tmp) \<sigma>)))))" 

definition swap :: "nat \<times> nat \<Rightarrow>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "swap \<equiv> \<lambda>(i,j). block\<^sub>C push_local_swap_state (swap_core (i,j)) pop_local_swap_state"
\<close>}

\<close>

subsection\<open>Call Semantics\<close>

text\<open>It is now straight-forward to define the semantics of a generic call --- 
which is simply a monad execution that is \<^term>\<open>break\<close>-aware and \<^term>\<open>return\<close>-aware.\<close>

definition call\<^sub>C :: "( '\<alpha> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call\<^sub>C M A\<^sub>1 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) \<sigma>)"

text\<open>Note that this presentation assumes a uncurried format of the arguments. The 
question arises if this is the right approach to handle calls of operation with multiple arguments.
Is it better to go for an some appropriate currying principle? Here are 
 some more experimental variants for curried operations...
\<close>

definition call_0\<^sub>C :: "('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_0\<^sub>C M = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M \<sigma>)"

text\<open>The generic version using tuples is identical with @{term \<open>call_1\<^sub>C\<close>}.\<close>
definition call_1\<^sub>C :: "( '\<alpha> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"                                                      
  where   "call_1\<^sub>C  = call\<^sub>C"

definition call_2\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_2\<^sub>C M A\<^sub>1 A\<^sub>2 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) \<sigma>)"

definition call_3\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow>  '\<gamma> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<gamma>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_3\<^sub>C M A\<^sub>1 A\<^sub>2 A\<^sub>3 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) 
                                                   else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) (A\<^sub>3 \<sigma>) \<sigma>)"

(* and 4 and 5 and ... *)                        
  

section\<open> Some Term-Coding Functions \<close>

text\<open>In the following, we add a number of advanced HOL-term constructors in the style of 
@{ML_structure "HOLogic"} from the Isabelle/HOL libraries. They incorporate the construction
of types during term construction in a bottom-up manner. Consequently, the leafs of such
terms should always be typed, and anonymous loose-@{ML "Bound"} variables avoided.\<close>

ML\<open>
(* HOLogic extended *)

fun mk_None ty = let val none = \<^const_name>\<open>Option.option.None\<close>
                     val none_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(none, none_ty)
                end;

fun mk_Some t = let val some = \<^const_name>\<open>Option.option.Some\<close> 
                    val ty = fastype_of t
                    val some_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(some, some_ty) $ t
                end;

fun dest_listTy (Type(\<^type_name>\<open>List.list\<close>, [T])) = T;

fun mk_hdT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.hd\<close>, ty --> (dest_listTy ty)) $ t end

fun mk_tlT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.tl\<close>, ty --> ty) $ t end


fun  mk_undefined (@{typ "unit"}) = Const (\<^const_name>\<open>Product_Type.Unity\<close>, \<^typ>\<open>unit\<close>)
    |mk_undefined t               = Const (\<^const_name>\<open>HOL.undefined\<close>, t)

fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);

fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;

fun   mk_pat_tupleabs [] t = t
    | mk_pat_tupleabs [(s,ty)] t = absfree(s,ty)(t)
    | mk_pat_tupleabs ((s,ty)::R) t = HOLogic.mk_case_prod(absfree(s,ty)(mk_pat_tupleabs R t));

fun read_constname ctxt n = fst(dest_Const(Syntax.read_term ctxt n))

fun wfrecT order recs = 
    let val funT = domain_type (fastype_of recs)
        val aTy  = domain_type funT
        val ordTy = HOLogic.mk_setT(HOLogic.mk_prodT (aTy,aTy))
    in Const(\<^const_name>\<open>Wfrec.wfrec\<close>, ordTy --> (funT --> funT) --> funT) $ order $ recs end


\<close>

text\<open>And here comes the core of the \<^theory_text>\<open>Clean\<close>-State-Management: the module that provides the 
functionality for the commands keywords \<^theory_text>\<open>global_vars\<close>, \<^theory_text>\<open>local_vars\<close>  and \<^theory_text>\<open>local_vars_test\<close>.
Note that the difference between \<^theory_text>\<open>local_vars\<close> and \<^theory_text>\<open>local_vars_test\<close> is just a technical one:
\<^theory_text>\<open>local_vars\<close> can only be used inside a Clean function specification, made with the \<^theory_text>\<open>function_spec\<close>
command. On the other hand, \<^theory_text>\<open>local_vars_test\<close> is defined as a global Isar command for test purposes. 

A particular feature of the local-variable management is the provision of definitions for \<^term>\<open>push\<close>
and \<^term>\<open>pop\<close> operations --- encoded as \<^typ>\<open>('o, '\<sigma>) MON\<^sub>S\<^sub>E\<close> operations --- which are vital for
the function specifications defined below.
\<close>

ML\<open>
structure StateMgt = 
struct

open StateMgt_core

val result_name = "result_value"

fun get_result_value_conf name thy = 
        let val  S = filter_attr_of name thy
        in  hd(filter (fn ((_,b),_) => b = result_name) S) 
            handle Empty => error "internal error: get_result_value_conf " end; 


fun mk_lookup_result_value_term name sty thy =
    let val ((prefix,name),local_var(Type("fun", [_,ty]))) = get_result_value_conf name thy;
        val long_name = Sign.intern_const thy (prefix^"."^name)
        val term = Const(long_name, sty --> ty)
    in  mk_hdT (term $ Free("\<sigma>",sty)) end


fun  map_to_update sty is_pop thy ((struct_name, attr_name), local_var (Type("fun",[_,ty]))) term = 
       let val tlT = if is_pop then Const(\<^const_name>\<open>List.tl\<close>, ty --> ty)
                     else Const(\<^const_name>\<open>List.Cons\<close>, dest_listTy ty --> ty --> ty)
                          $ mk_undefined (dest_listTy ty)
           val update_name = Sign.intern_const  thy (struct_name^"."^attr_name^"_update")
       in (Const(update_name, (ty --> ty) --> sty --> sty) $ tlT) $ term end
   | map_to_update _ _ _ ((_, _),_) _ = error("internal error map_to_update")     

fun mk_local_state_name binding = 
       Binding.prefix_name "local_" (Binding.suffix_name "_state" binding)  
fun mk_global_state_name binding = 
       Binding.prefix_name "global_" (Binding.suffix_name "_state" binding)  

fun construct_update is_pop binding sty thy = 
       let val long_name = Binding.name_of( binding)
           val attrS = StateMgt_core.filter_attr_of long_name thy
       in  fold (map_to_update sty is_pop thy) (attrS) (Free("\<sigma>",sty)) end

fun cmd (decl, spec, prems, params) = #2 oo Specification.definition' decl params prems spec

fun mk_push_name binding = Binding.prefix_name "push_" binding

fun push_eq binding  name_op rty sty lthy = 
         let val mty = MON_SE_T rty sty 
             val thy = Proof_Context.theory_of lthy
             val term = construct_update false binding sty thy
         in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                         mk_Some ( HOLogic.mk_prod (mk_undefined rty,term)))
                          
         end;

fun mk_push_def binding sty lthy =
    let val name_pushop =  mk_push_name binding
        val rty = \<^typ>\<open>unit\<close>
        val eq = push_eq binding  (Binding.name_of name_pushop) rty sty lthy
        val mty = StateMgt_core.MON_SE_T rty sty 
        val args = (SOME(name_pushop, SOME mty, NoSyn), (Binding.empty_atts,eq),[],[])
    in cmd args true lthy  end;

fun mk_pop_name binding = Binding.prefix_name "pop_"  binding

fun pop_eq  binding name_op rty sty lthy = 
         let val mty = MON_SE_T rty sty 
             val thy = Proof_Context.theory_of lthy
             val res_access = mk_lookup_result_value_term (Binding.name_of binding) sty thy
             val term = construct_update true binding  sty thy                 
         in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                         mk_Some ( HOLogic.mk_prod (res_access,term)))                          
         end;


fun mk_pop_def binding rty sty lthy = 
    let val mty = StateMgt_core.MON_SE_T rty sty 
        val name_op =  mk_pop_name binding
        val eq = pop_eq binding (Binding.name_of name_op) rty sty lthy
        val args = (SOME(name_op, SOME mty, NoSyn),(Binding.empty_atts,eq),[],[])
    in cmd args true lthy
    end;


fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
       (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

fun parse_typ_'a ctxt binding = 
  let val ty_bind =  Binding.prefix_name "'a " (Binding.suffix_name "_scheme" binding)
  in case Syntax.parse_typ ctxt (Binding.name_of ty_bind) of
       Type (s, _) => Type (s, [@{typ "'a::type"}])
     | _ => error ("Unexpected type" ^ Position.here \<^here>)
  end

fun add_record_cmd0 read_fields overloaded is_global_kind raw_params binding raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    fun lift (a,b,c) =  (a, HOLogic.listT b, c)
    val fields' = if is_global_kind then fields else map lift fields
    val params' = map (Proof_Context.check_tfree ctxt3) params;
    val declare = StateMgt_core.declare_state_variable_global
    fun upd_state_typ thy = let val ctxt = Proof_Context.init_global thy
                                val ty = Syntax.parse_typ ctxt (Binding.name_of binding)
                            in  StateMgt_core.upd_state_type_global(K ty)(thy) end
    fun insert_var ((f,_,_), thy) =           
            if is_global_kind   
            then declare StateMgt_core.global_var (Binding.name_of f) thy
            else declare StateMgt_core.local_var  (Binding.name_of f) thy
    fun define_push_pop thy = 
            if not is_global_kind 
            then let val sty = parse_typ_'a (Proof_Context.init_global thy) binding;
                     val rty = dest_listTy (#2(hd(rev fields')))
                 in thy

                    |> Named_Target.theory_map (mk_push_def binding sty) 
                    |> Named_Target.theory_map (mk_pop_def  binding rty sty) 
                                                            
                 end
            else thy
  in thy |> Record.add_record overloaded (params', binding) parent fields' 
         |> (fn thy =>  List.foldr insert_var (thy) (fields'))
         |> upd_state_typ
         |> define_push_pop 
  end;



fun typ_2_string_raw (Type(s,[TFree _])) = if String.isSuffix "_scheme" s
                                            then Long_Name.base_name(unsuffix "_scheme" s)
                                            else Long_Name.base_name(unsuffix "_ext" s)
                                          
   |typ_2_string_raw (Type(s,_)) = 
                         error ("Illegal parameterized state type - not allowed in Clean:"  ^ s) 
   |typ_2_string_raw _ = error  "Illegal state type - not allowed in Clean." 
                                  
             
fun new_state_record0 add_record_cmd is_global_kind (((raw_params, binding), res_ty), raw_fields) thy =
    let val binding = if is_global_kind 
                      then mk_global_state_name binding
                      else mk_local_state_name binding
        val raw_parent = SOME(typ_2_string_raw (StateMgt_core.get_state_type_global thy))
        val pos = Binding.pos_of binding
        fun upd_state_typ thy =
          StateMgt_core.upd_state_type_global (K (parse_typ_'a (Proof_Context.init_global thy) binding)) thy
        val result_binding = Binding.make(result_name,pos)
        val raw_fields' = case res_ty of 
                            NONE => raw_fields
                          | SOME res_ty => raw_fields @ [(result_binding,res_ty, NoSyn)]
    in  thy |> add_record_cmd {overloaded = false} is_global_kind 
                              raw_params binding raw_parent raw_fields' 
            |> upd_state_typ 

    end

val add_record_cmd    = add_record_cmd0 read_fields;
val add_record_cmd'   = add_record_cmd0 pair;

val new_state_record  = new_state_record0 add_record_cmd
val new_state_record' = new_state_record0 add_record_cmd'

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>global_vars\<close>   
      "define global state record"
      ((Parse.type_args_constrained -- Parse.binding)
    -- Scan.succeed NONE
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record true));
;

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>local_vars_test\<close>  
      "define local state record"
      ((Parse.type_args_constrained -- Parse.binding) 
    -- (Parse.typ >> SOME)
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record false))
;
end
\<close>

section\<open>Syntactic Sugar supporting \<open>\<lambda>\<close>-lifting for Global and Local Variables \<close>

ML \<open>
structure Clean_Syntax_Lift =
struct
  local
    fun mk_local_access X = Const (@{const_name "Fun.comp"}, dummyT) 
                            $ Const (@{const_name "List.list.hd"}, dummyT) $ X
  in
    fun app_sigma db tm ctxt = case tm of
        Const(name, _) => if StateMgt_core.is_global_program_variable name (Proof_Context.theory_of ctxt) 
                          then tm $ (Bound db) (* lambda lifting *)
                          else if StateMgt_core.is_local_program_variable name (Proof_Context.theory_of ctxt) 
                               then (mk_local_access tm) $ (Bound db) (* lambda lifting local *)
                               else tm              (* no lifting *)
      | Free _ => tm
      | Var _ => tm
      | Bound n => if n > db then Bound(n + 1) else Bound n 
      | Abs (x, ty, tm') => Abs(x, ty, app_sigma (db+1) tm' ctxt)
      | t1 $ t2 => (app_sigma db t1 ctxt) $ (app_sigma db t2 ctxt)

    fun scope_var name =
      Proof_Context.theory_of
      #> (fn thy =>
            if StateMgt_core.is_global_program_variable name thy then SOME true
            else if StateMgt_core.is_local_program_variable name thy then SOME false
            else NONE)

    fun assign_update var = var ^ Record.updateN

    fun transform_term0 abs scope_var tm =
      case tm of
         Const (@{const_name "Clean.syntax_assign"}, _)
         $ (t1 as Const ("_type_constraint_", _) $ Const (name, ty))
         $ t2 =>
            Const ( case scope_var name of
                      SOME true => @{const_name "assign_global"}
                    | SOME false => @{const_name "assign_local"}
                    | NONE => raise TERM ("mk_assign", [t1])
                  , dummyT)
            $ Const(assign_update name, ty)
            $ abs t2
       | _ => abs tm

    fun transform_term ctxt sty =
      transform_term0
        (fn tm => Abs ("\<sigma>", sty, app_sigma 0 tm ctxt))
        (fn name => scope_var name ctxt)

    fun transform_term' ctxt = transform_term ctxt dummyT

    fun string_tr ctxt content args =
      let fun err () = raise TERM ("string_tr", args)
      in
        (case args of
          [(Const (@{syntax_const "_constrain"}, _)) $ (Free (s, _)) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => Symbol_Pos.implode (content (s, pos))
                            |> Syntax.parse_term ctxt
                            |> transform_term ctxt (StateMgt_core.get_state_type ctxt)
                            |> Syntax.check_term ctxt
            | NONE => err ())
        | _ => err ())
      end
  end
end
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> string"  ("_")

parse_translation \<open>
  [(@{syntax_const "_cartouche_string"},
    (fn ctxt => Clean_Syntax_Lift.string_tr ctxt (Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

section\<open>Support for (direct recursive) Clean Function Specifications \<close>

text\<open>Based on the machinery for the State-Management and  implicitly cooperating with the 
cartouches for assignment syntax, the function-specification \<^theory_text>\<open>function_spec\<close>-package coordinates:
\<^enum> the parsing and type-checking of parameters,
\<^enum> the parsing and type-checking of pre and post conditions in MOAL notation
  (using \<open>\<lambda>\<close>-lifting cartouches and implicit reference to parameters, pre and post states),
\<^enum> the parsing local variable section with the local-variable space generation,
\<^enum> the parsing of the body in this extended variable space,
\<^enum> and optionally the support of measures for recursion proofs.

The reader interested in details is referred to the \<^file>\<open>../examples/Quicksort_concept.thy\<close>-example,
accompanying this distribution.
\<close>

definition old :: "'a \<Rightarrow> 'a" where "old x = x"


ML\<open> 
\<close>

ML \<open> 
structure Function_Specification_Parser  = 
  struct

    type funct_spec_src = {    
        binding:  binding,                         (* name *)
        params: (binding*string) list,             (* parameters and their type*)
        ret_type: string,                          (* return type; default unit *)
        locals: (binding*string*mixfix)list,       (* local variables *)
        pre_src: string,                           (* precondition src *)
        post_src: string,                          (* postcondition src *)
        variant_src: string option,                       (* variant src *)
        body_src: string * Position.T              (* body src *)
      }

    type funct_spec_sem = {    
        params: (binding*typ) list,                (* parameters and their type*)
        ret_ty: typ,                               (* return type *)
        pre: term,                                 (* precondition  *)
        post: term,                                (* postcondition  *)
        variant: term option                       (* variant  *)
      }


    val parse_arg_decl = Parse.binding -- (Parse.$$$ "::" |-- Parse.typ)

    val parse_param_decls = Args.parens (Parse.enum "," parse_arg_decl)
      
    val parse_returns_clause = Scan.optional (\<^keyword>\<open>returns\<close> |--  Parse.typ) "unit"
 
    val locals_clause = (Scan.optional ( \<^keyword>\<open>local_vars\<close> 
                                        -- (Scan.repeat1 Parse.const_binding)) ("", []))
    
    val parse_proc_spec = (
          Parse.binding 
       -- parse_param_decls
       -- parse_returns_clause
       --| \<^keyword>\<open>pre\<close>             -- Parse.term 
       --| \<^keyword>\<open>post\<close>            -- Parse.term 
       -- (Scan.option  ( \<^keyword>\<open>variant\<close> |-- Parse.term))
       -- (Scan.optional( \<^keyword>\<open>local_vars\<close> |-- (Scan.repeat1 Parse.const_binding))([]))
       --| \<^keyword>\<open>defines\<close>         -- (Parse.position (Parse.term)) 
      ) >> (fn ((((((((binding,params),ret_ty),pre_src),post_src),variant_src),locals)),body_src) => 
        {
          binding = binding, 
          params=params, 
          ret_type=ret_ty, 
          pre_src=pre_src, 
          post_src=post_src, 
          variant_src=variant_src,
          locals=locals,
          body_src=body_src} : funct_spec_src
        )

   fun read_params params ctxt =
     let
       val Ts = Syntax.read_typs ctxt (map snd params);
     in (Ts, fold Variable.declare_typ Ts ctxt) end;
   
   fun read_result ret_ty ctxt = 
          let val [ty] = Syntax.read_typs ctxt [ret_ty]
              val ctxt' = Variable.declare_typ ty ctxt           
          in  (ty, ctxt') end

   fun read_function_spec ({ params, ret_type, variant_src, ...} : funct_spec_src) ctxt =
       let val (params_Ts, ctxt') = read_params params ctxt
           val (rty, ctxt'') = read_result ret_type ctxt' 
           val variant = Option.map (Syntax.read_term ctxt'')  variant_src
       in ({params = (params, params_Ts), ret_ty = rty,variant = variant},ctxt'') end 


   fun check_absence_old term = 
            let fun test (s,ty) = if s = @{const_name "old"} andalso fst (dest_Type ty) = "fun"
                                  then error("the old notation is not allowed here!")  
                                  else false
            in  exists_Const test term end
   
   fun transform_old sty term = 
       let fun  transform_old0 (Const(@{const_name "old"}, Type ("fun", [_,_])) $ term ) 
                              = (case term of
                                  (Const(s,ty) $ Bound x) =>  (Const(s,ty) $ Bound (x+1))
                                | _ => error("illegal application of the old notation."))
               |transform_old0 (t1 $ t2) = transform_old0 t1 $ transform_old0 t2
               |transform_old0 (Abs(s,ty,term)) = Abs(s,ty,transform_old0 term) 
               |transform_old0 term = term
       in  Abs("\<sigma>\<^sub>p\<^sub>r\<^sub>e", sty, transform_old0 term) end
   
   fun define_cond binding f_sty transform_old src_suff check_absence_old params src ctxt = 
       let val src' = case transform_old (Syntax.read_term ctxt src) of 
                        Abs(nn, sty_pre, term) => mk_pat_tupleabs (map (apsnd #2) params) (Abs(nn,sty_pre(* sty root ! !*),term))
                      | _ => error ("define abstraction for result" ^ Position.here \<^here>)
           val bdg = Binding.suffix_name src_suff binding
           val _ = check_absence_old src'
           val eq =  mk_meta_eq(Free(Binding.name_of bdg, HOLogic.mk_tupleT(map (#2 o #2) params) --> f_sty HOLogic.boolT),src')
           val args = (SOME(bdg,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) 
       in  StateMgt.cmd args true ctxt end

   fun define_precond binding sty =
     define_cond binding (fn boolT => sty --> boolT) I "_pre" check_absence_old

   fun define_postcond binding rty sty =
     define_cond binding (fn boolT => sty --> sty --> rty --> boolT) (transform_old sty) "_post" I

   fun define_body_core binding args_ty sty params body =
       let val bdg_core = Binding.suffix_name "_core" binding
           val bdg_core_name = Binding.name_of bdg_core

           val umty = args_ty --> StateMgt.MON_SE_T @{typ "unit"} sty

           val eq = mk_meta_eq(Free (bdg_core_name, umty),mk_pat_tupleabs(map(apsnd #2)params) body)
           val args_core =(SOME (bdg_core, SOME umty, NoSyn), (Binding.empty_atts, eq), [], [])

       in StateMgt.cmd args_core true
       end 
 
   fun define_body_main {recursive = x:bool} binding rty sty params variant_src _ ctxt = 
       let val push_name = StateMgt.mk_push_name (StateMgt.mk_local_state_name binding)
           val pop_name = StateMgt.mk_pop_name (StateMgt.mk_local_state_name binding)
           val bdg_core = Binding.suffix_name "_core" binding
           val bdg_core_name = Binding.name_of bdg_core
           val bdg_rec_name = Binding.name_of(Binding.suffix_name "_rec" binding)
           val bdg_ord_name = Binding.name_of(Binding.suffix_name "_order" binding)

           val args_ty = HOLogic.mk_tupleT (map (#2 o #2) params)
           val params' = map (apsnd #2) params
           val rmty = StateMgt_core.MON_SE_T rty sty 

           val umty = StateMgt.MON_SE_T @{typ "unit"} sty
           val argsProdT = HOLogic.mk_prodT(args_ty,args_ty)
           val argsRelSet = HOLogic.mk_setT argsProdT
           val measure_term = case variant_src of
                                 NONE => Free(bdg_ord_name,args_ty --> HOLogic.natT)
                               | SOME str => (Syntax.read_term ctxt str |> mk_pat_tupleabs params')
           val measure =  Const(@{const_name "Wellfounded.measure"}, (args_ty --> HOLogic.natT)
                                                                     --> argsRelSet )
                          $ measure_term
           val lhs_main = if x andalso is_none variant_src
                          then Free(Binding.name_of binding, (args_ty --> HOLogic.natT)
                                                                       --> args_ty --> rmty) $
                                         Free(bdg_ord_name, args_ty --> HOLogic.natT)
                          else Free(Binding.name_of binding, args_ty --> rmty)
           val rhs_main = mk_pat_tupleabs params'
                          (Const(@{const_name "Clean.block\<^sub>C"}, umty --> umty  --> rmty --> rmty)
                          $ Const(read_constname ctxt (Binding.name_of push_name),umty)
                          $ (Const(read_constname ctxt bdg_core_name, args_ty --> umty)  
                             $ HOLogic.mk_tuple (map Free params'))
                          $ Const(read_constname ctxt (Binding.name_of pop_name),rmty))
           val rhs_main_rec = wfrecT 
                              measure 
                              (Abs(bdg_rec_name, (args_ty --> umty) , 
                                   mk_pat_tupleabs params'
                                   (Const(@{const_name "Clean.block\<^sub>C"}, umty-->umty-->rmty-->rmty)
                                   $ Const(read_constname ctxt (Binding.name_of push_name),umty)
                                   $ (Const(read_constname ctxt bdg_core_name,
                                            (args_ty --> umty) --> args_ty --> umty)  
                                      $ (Bound (length params))
                                      $ HOLogic.mk_tuple (map Free params'))
                                   $ Const(read_constname ctxt (Binding.name_of pop_name),rmty))))
           val eq_main = mk_meta_eq(lhs_main, if x then rhs_main_rec else rhs_main )
           val args_main = (SOME(binding,NONE,NoSyn), (Binding.empty_atts,eq_main),[],[]) 
       in  ctxt |> StateMgt.cmd args_main true 
       end 


   fun checkNsem_function_spec {recursive = false} ({variant_src=SOME _, ...}) _ = 
                               error "No measure required in non-recursive call"
      |checkNsem_function_spec (isrec as {recursive = _:bool}) 
                               (args as {binding, ret_type, variant_src, locals, body_src, pre_src, post_src, ...} : funct_spec_src)
                               thy =
       let val (theory_map, thy') =
             Named_Target.theory_map_result
               (K (fn f => Named_Target.theory_map o f))
               (read_function_spec args
               #> uncurry (fn {params=(params, Ts),ret_ty,variant = _} =>
                            pair (fn f =>
                                  Proof_Context.add_fixes (map2 (fn (b, _) => fn T => (b, SOME T, NoSyn)) params Ts)
                                    (* this declares the parameters of a function specification
                                       as Free variables (overrides a possible constant declaration)
                                       and assigns the declared type to them *)
                                  #> uncurry (fn params' => f (@{map 3} (fn b' => fn (b, _) => fn T => (b',(b,T))) params' params Ts) ret_ty))))
                thy
       in  thy' |> theory_map
                     let val sty_old = StateMgt_core.get_state_type_global thy'
                     in fn params => fn ret_ty =>
                         define_precond binding sty_old params pre_src
                      #> define_postcond binding ret_ty sty_old params post_src end
                |> StateMgt.new_state_record false ((([],binding), SOME ret_type),locals)
                |> theory_map
                         (fn params => fn ret_ty => fn ctxt => 
                          let val sty = StateMgt_core.get_state_type ctxt
                              val args_ty = HOLogic.mk_tupleT (map (#2 o #2) params)
                              val mon_se_ty = StateMgt_core.MON_SE_T ret_ty sty
                              val ctxt' =
                                if #recursive isrec then
                                  Proof_Context.add_fixes 
                                    [(binding, SOME (args_ty --> mon_se_ty), NoSyn)] ctxt |> #2
                                else
                                  ctxt
                              val body = Syntax.read_term ctxt' (fst body_src)
                          in  ctxt' |> define_body_core binding args_ty sty params body
                          end)
                |> theory_map
                         (fn params => fn ret_ty => fn ctxt => 
                          let val sty = StateMgt_core.get_state_type ctxt
                              val body = Syntax.read_term ctxt (fst body_src)
                          in  ctxt |> define_body_main isrec binding ret_ty sty params variant_src body
                          end)
        end

  
   val _ =
     Outer_Syntax.command 
         \<^command_keyword>\<open>function_spec\<close>   
         "define Clean function specification"
         (parse_proc_spec >> (Toplevel.theory o checkNsem_function_spec {recursive = false}));
   
   val _ =
     Outer_Syntax.command 
         \<^command_keyword>\<open>rec_function_spec\<close>   
         "define recursive Clean function specification"
         (parse_proc_spec >> (Toplevel.theory o checkNsem_function_spec {recursive = true}));
       
  end
\<close>

section\<open>The Rest of Clean: Break/Return aware Version of If, While, etc.\<close>

definition if_C :: "[('\<sigma>_ext) control_state_ext \<Rightarrow> bool, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "if_C c E F = (\<lambda>\<sigma>. if exec_stop \<sigma> 
                              then Some(undefined, \<sigma>)  \<comment> \<open>state unchanged, return arbitrary\<close>
                              else if c \<sigma> then E \<sigma> else F \<sigma>)"     

syntax    (xsymbols)
          "_if_SECLEAN" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>C _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>C cond then T1 else T2 fi)" == "CONST Clean.if_C cond T1 T2"

          
          
definition while_C :: "(('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "while_C c B \<equiv> (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>)
                               else ((MonadSE.while_SE (\<lambda> \<sigma>. \<not>exec_stop \<sigma> \<and> c \<sigma>) B) ;- 
                                     unset_break_status) \<sigma>)"
  
syntax    (xsymbols)
          "_while_C" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>C _ do _ od)" [8,8]8)
translations 
          "while\<^sub>C c do b od" == "CONST Clean.while_C c b"

  

end

  
  