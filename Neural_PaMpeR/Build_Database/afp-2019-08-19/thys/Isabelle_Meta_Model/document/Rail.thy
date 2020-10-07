(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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

(*<*)
theory Rail
imports "../toy_example/embedding/Generator_dynamic_sequential"
begin
ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>
(*>*)

section\<open>Main Setup of Meta Commands\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def generation_syntax} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command generation_syntax}
    ( '[' (@{syntax syntax} * ',') ']'
    | @{syntax syntax}
    | @'deep' @'flush_all')
  ;
  @{syntax_def syntax}:
                 @'deep' @{syntax semantics} @{syntax deep_embedding}
               | @'shallow' @{syntax semantics} @{syntax long_or_dirty}
               | @'syntax_print' number?
  ;
  @{syntax_def semantics}:
               ('(' @'generation_semantics' \<newline>
                 ('[' (@'design' | @'analysis') (',' @'oid_start' nat)? ']') ')')?
  ;
  @{syntax_def deep_embedding}:
               (@'skip_export')? \<newline>
               ('(' @'THEORY' name ')' \<newline>
                '(' @'IMPORTS' '[' (name * ',') ']' name ')')? \<newline>
               (@'SECTION')? \<newline>
               @{syntax long_or_dirty} \<newline>
               ('[' (@{syntax export_code} + ',') ']') \<newline>
               ('(' @'output_directory' name ')')?
  ;
  @{syntax_def export_code}:
               @'in' (  'Haskell'
                      | ((  'OCaml'
                          | 'Scala'
                          | 'SML') @'module_name' name)) ( '(' args ')' ) ?
  ;
  @{syntax_def long_or_dirty}:
               (@'SORRY' | @'no_dirty')?
  ;
\<close>}
\<close>

text\<open>
@{command generation_syntax} sets the behavior of all incoming meta-commands.
By default, without firstly writing @{command generation_syntax}, 
meta-commands will only print in output what they have parsed, 
this is similar as giving to @{command generation_syntax}
a non-empty list having only @{keyword "syntax_print"} as elements
(on the other hand, nothing is printed when an empty list is received).
Additionally @{keyword "syntax_print"} can be followed by an integer
indicating the printing depth in output, similar as declaring
@{attribute "ML_print_depth"} with an integer,
but the global option @{keyword "syntax_print"} is restricted to meta-commands.
Besides the printing of syntaxes, several options are provided to further analyze
the semantics of languages being embedded,
and tell if their evaluation should occur immediately using the @{keyword "shallow"} mode,
or to only display what would have been evaluated using the @{keyword "deep"} mode
(i.e., to only show the generated Isabelle content in the output window).

Since several occurrences of
 @{keyword "deep"}, @{keyword "shallow"} or @{keyword "syntax_print"}
can appear in the parameterizing list,
for each meta-command the overall evaluation respects the order of events
given in the list (from head to tail).
At the time of writing, it is only possible to evaluate this list sequentially:
the execution stops as soon as one first error is raised, thus ignoring remaining events.

@{command generation_syntax} @{keyword "deep"} @{keyword "flush_all"}
performs as side effect the writing of all the generated Isabelle contents
to the hard disk (all at the calling time),
by iterating the saving for each @{keyword "deep"} mode in the list.
In particular, this is only effective
if there is at least one @{keyword "deep"} mode earlier declared.

As a side note, target languages for the @{keyword "deep"} mode currently supported are:
 Haskell, OCaml, Scala and SML.
So in principle, all these targets generate the same Isabelle content and exit correctly.
However, depending on the intended use, exporting with some targets may be more appropriate
than other targets: 
\begin{itemize}
\item For efficiency reasons, the meta-compiler has implemented a particular optimization 
for accelerating the process of evaluating incoming meta-commands. 
By default in Haskell and OCaml, the meta-compiler (at HOL side) is exported only once, 
during the @{command generation_syntax} step. 
Then all incoming meta-commands are considered as arguments sent to the exported meta-compiler.
As a compositionality aspect, these arguments are compiled then linked together
with the (already compiled) meta-compiler, but
this implies the use of one call of 
\<open>unsafeCoerce\<close> in Haskell and one \<open>Obj.magic\<close> statement in OCaml 
(otherwise another solution would be to extract the meta-compiler as a functor).
Similar optimizations are not yet implemented for Scala and are only half-implemented for the SML target
(which basically performs a step of marshalling to string in Isabelle/ML).
\item For safety reasons, it simply suffices to extract all the meta-compiler together with the respective 
arguments in front of each incoming meta-commands everytime, then the overall needs to be newly 
compiled everytime. 
This is the current implemented behavior for Scala. 
For Haskell, OCaml and SML, it was also the default behavior in a prototyping version of the compiler,
as a consequence one can restore that functionality for future versions.
\end{itemize}

Concerning the semantics of generated contents, if lemmas and proofs are generated,
@{keyword "SORRY"} allows to explicitly skip the evaluation of all proofs,
irrespective of the presence of @{command sorry} or not in generated proofs. 
In any cases, the semantics of @{command sorry} has not been overloaded, e.g., 
red background may appear as usual.

Finally @{keyword "generation_semantics"} is a container for specifying various options
for varying the semantics of languages being embedded.
For example, @{keyword "design"} and @{keyword "analysis"} are two options for specifying how 
the modelling of objects will be represented in the Toy Language.
Similarly, this would be a typical place for options like
\<open>eager\<close> or \<open>lazy\<close> for choosing how the evaluation should happen...
\<close>

section\<open>All Meta Commands of the Toy Language\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def Class} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def Abstract_class} & : & \<open>theory \<rightarrow> theory\<close> \\
\end{matharray}

@{rail \<open>
  (  @@{command Class}
   | @@{command Abstract_class})
                   (  binding '=' @{syntax type_base}
                    | @{syntax type_object}
                      @{syntax class})
  ;
  @{syntax_def class}:
               @'Attributes'? ((binding ':' @{syntax toy_type}) * (';'?)) \<newline>
               @{syntax context}
  ;
  @{syntax_def context}:
            (( ((() | @'Operations' | '::')
                binding @{syntax toy_type} \<newline>
                ('=' term | term)? (((@'Pre' | @'Post') @{syntax use_prop}
                                    | @{syntax invariant}) * ())
               )
             | @{syntax invariant}) * ())
  ;
  @{syntax_def invariant}:
               @'Constraints'? @'Existential'? @'Inv' @{syntax use_prop}
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def Aggregation} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def Association} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def Composition} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  (  @@{command Aggregation}
   | @@{command Association}
   | @@{command Composition}) binding? @{syntax association}
  ;
  @{syntax_def association}:
               @'Between'? (@{syntax association_end} (@{syntax association_end}+))?
  ;
  @{syntax_def association_end}:
               @{syntax type_object}
               @{syntax category}
               ';'?
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def Associationclass} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def Abstract_associationclass} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  (  @@{command Associationclass}
   | @@{command Abstract_associationclass}) @{syntax type_object} \<newline>
                                            @{syntax association} @{syntax class} (() | 'aggregation' | 'composition')
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def Context} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command Context} ('[' @'shallow' ']')? @{syntax type_object} @{syntax context}
  ;
\<close>}
\<close>


text \<open>
\begin{matharray}{rcl}
  @{command_def Instance} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command Instance} ((binding ('::' @{syntax type_object})? '=' \<newline>
                         (@{syntax term_object} | @{syntax object_cast})) * ('and'?))
  ;
  @{syntax_def term_object}:
                 ('[' ((('(' binding ',' binding ')' '|=')? \<newline>
                        binding '=' @{syntax toy_term}) * ',') ']')
  ;
  @{syntax_def object_cast}:
               '(' @{syntax term_object} '::' @{syntax type_object} ')' \<newline>
               (('\<rightarrow>' 'toyAsType' '(' @{syntax type_object} ')') * ())
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def State} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command State} ('[' @'shallow' ']')? binding ('=' @{syntax state})?
  ;
  @{syntax_def state}:
               '[' ((binding | @{syntax object_cast}) * ',') ']'
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def PrePost} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command PrePost} ('[' @'shallow' ']')? (binding '=')? \<newline>
    @{syntax pre_post}
    @{syntax pre_post}?
  ;
  @{syntax_def pre_post}:
               binding | @{syntax state}
  ;
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def End} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command End} ('[' 'forced' ']' | '!')?
\<close>}
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def BaseType} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command BaseType} '[' (@{syntax term_base} * ',') ']'
  ;
\<close>}
\<close>

section\<open>Extensions of Isabelle Commands\<close>

(* WARNING syntax errors during the extraction to LaTeX for the symbol "acute":
           fun\<acute>, definition\<acute> or code_reflect\<acute> *)
text \<open>
\begin{matharray}{rcl}
  @{command_def "code_reflect'"} & : & \<open>theory \<rightarrow> theory\<close>
\end{matharray}

@{rail \<open>
  @@{command "code_reflect'"} @'open'? string \<newline>
    ( @'datatypes' ( string '=' ( '_' | ( string + '|' ) + @'and' ) ) ) ? \<newline>
    ( @'functions' ( string + ) ) ? ( @'file' string ) ?
  ;
\<close>}
\<close>

text\<open>
@{command code_reflect'} has the same semantics as @{command code_reflect}
except that it additionally contains the option @{keyword "open"} inspired
from the command @{command export_code} (with the same semantics).
\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def lazy_code_printing} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def apply_code_printing} & : & \<open>theory \<rightarrow> theory\<close> \\
  @{command_def apply_code_printing_reflect} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

@{rail \<open>
  @@{command lazy_code_printing}
      ( ( printing_const | printing_typeconstructor
      | printing_class | printing_class_relation | printing_class_instance
      | printing_module ) + '|' )
  ;
  @@{command apply_code_printing} '(' ')'
  ;
  @@{command apply_code_printing_reflect} text
  ;
\<close>}
\<close>

text\<open>
@{command lazy_code_printing} has the same semantics as @{command code_printing} 
or @{command ML},
except that no side effects occur until we give more details about its intended future semantics:
this will be precised by calling
@{command apply_code_printing} or @{command apply_code_printing_reflect}.
\<close>

text\<open>
@{command apply_code_printing} repeatedly calls @{command code_printing}
to all previously registered elements with @{command lazy_code_printing} (the order is preserved).
\<close>

text\<open>
@{command apply_code_printing_reflect} repeatedly calls @{command ML}
to all previously registered elements with @{command lazy_code_printing} (the order is preserved).
As a consequence, code for other targets (Haskell, OCaml, Scala) are ignored.
Moreover before the execution of the overall,
it is possible to give an additional piece of SML code as argument to priorly execute.
\<close>

(*<*)
end
(*>*)
