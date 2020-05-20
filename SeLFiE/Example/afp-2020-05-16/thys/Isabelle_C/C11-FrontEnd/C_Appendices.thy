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

chapter \<open>Annexes\<close>

theory C_Appendices
  imports "examples/C1"
          Isar_Ref.Base
begin

(*<*)
ML \<comment> \<open>\<^file>\<open>~~/src/Doc/antiquote_setup.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Doc/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)
\<open>
structure C_Antiquote_Setup =
struct

(* misc utils *)

fun translate f = Symbol.explode #> map f #> implode;

val clean_string = translate
  (fn "_" => "\\_"
    | "#" => "\\#"
    | "$" => "\\$"
    | "%" => "\\%"
    | "<" => "$<$"
    | ">" => "$>$"
    | "{" => "\\{"
    | "|" => "$\\mid$"
    | "}" => "\\}"
    | "\<hyphen>" => "-"
    | c => c);

fun clean_name "\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-"
                                    | "\<hyphen>" => "-"
                                    | "#" => "symbol-hash"
                                    | "\<approx>" => "symbol-lower-approx"
                                    | "\<Down>" => "symbol-upper-down"
                                    | c => c);


(* Isabelle/Isar entities (with index) *)

local

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Thy_Output.antiquotation_raw
    (binding |> Binding.map_name (fn name => name ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Parse.position Args.name))
    (fn ctxt => fn (logic, (name, pos)) =>
      let
        val kind = translate (fn "_" => " " | c => c) (Binding.name_of binding);
        val hyper_name =
          "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
        val hyper =
          enclose ("\\hyperlink" ^ hyper_name ^ "{") "}" #>
          index = SOME true ? enclose ("\\hypertarget" ^ hyper_name ^ "{") "}";
        val idx =
          (case index of
            NONE => ""
          | SOME is_def =>
              "\\index" ^ (if is_def then "def" else "ref") ^ arg logic ^ arg kind ^ arg name);
        val _ =
          if Context_Position.is_reported ctxt pos then ignore (check ctxt (name, pos)) else ();
        val latex =
          idx ^
          (Output.output name
            |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
            |> hyper o enclose "\\mbox{\\isa{" "}}");
      in Latex.string latex end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val _ =
  Theory.setup
   (entity_antiqs C_Annotation.check_command "isacommand" \<^binding>\<open>annotation\<close>);

end;

end;

\<close>
(*>*)

section \<open>Syntax Commands for Isabelle/C\<close>

subsection \<open>Outer Classical Commands\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "C_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_export_boot"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_prf"} & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "C_val"} & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "C_export_file"} & : & \<open>any \<rightarrow>\<close> \\
  \end{matharray}
  \begin{tabular}{rcll}
    @{attribute_def C_lexer_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_parser_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_ML_verbose} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def C_starting_env} & : & \<open>attribute\<close> & default \<open>empty\<close> \\
    @{attribute_def C_starting_rule} & : & \<open>attribute\<close> & default \<open>translation_unit\<close> \\
  \end{tabular}

  \<^rail>\<open>
    @@{command C_file} @{syntax name} ';'?
    ;
    (@@{command C} | @@{command C_export_boot} | @@{command C_prf} |
      @@{command C_val}) @{syntax text}
    ;
    @@{command C_export_file}
    ;
  \<close>

  \<^descr> \<^theory_text>\<open>C_file name\<close> reads the given C file, and let any attached
  semantic back-ends to proceed for further subsequent evaluation. Top-level C bindings are stored
  within the (global or local) theory context; the initial environment is set by default to be an
  empty one, or the one returned by a previous \<^theory_text>\<open>C_file\<close> (depending on
  @{attribute_def C_starting_env}). The entry-point of the grammar taken as initial starting parser
  is read from @{attribute_def C_starting_rule} (see
  \<^url>\<open>https://www.haskell.org/happy/doc/html/sec-directives.html#sec-parser-name\<close>).
  Multiple \<^theory_text>\<open>C_file\<close> commands may be used to build larger C projects if
  they are all written in a single theory file (existing parent theories are ignored, and not
  affecting the current working theory).

  \<^descr> \<^theory_text>\<open>C\<close> is similar to
  \<^theory_text>\<open>C_file\<close>, but evaluates directly the
  given \<open>text\<close>. Top-level resulting bindings are stored
  within the (global or local) theory context.

  \<^descr> \<^theory_text>\<open>C_export_boot\<close> is similar to
  \<^theory_text>\<open>ML_export\<close>, except that the code in
  input is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_prf\<close> is similar to
  \<^theory_text>\<open>ML_prf\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_val\<close> is similar to
  \<^theory_text>\<open>ML_val\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_export_file\<close> is similar to
  \<^theory_text>\<open>generate_file fic = \<open>code\<close>
    export_generated_files fic\<close>, except that
    \<^item> \<open>code\<close> refers to the dump of all existing previous C code in the current
    theory (parent theories are ignored),
    \<^item> and any ML antiquotations in \<open>code\<close> are not analyzed by
    \<^theory_text>\<open>generate_file\<close> (in contrast with its default behavior). \<close>

text \<open>

  \<^descr> @{attribute C_lexer_trace} indicates whether the list of C
  tokens associated to the source text should be output (that list is
  computed during the lexing phase).

  \<^descr> @{attribute C_parser_trace} indicates whether the stack
  forest of Shift-Reduce node should be output (it is the final stack
  which is printed, i.e., the one taken as soon as the parsing
  terminates).

  \<^descr> @{attribute C_ML_verbose} indicates whether nested
  \<^theory_text>\<open>ML\<close> commands are acting similarly as
  their default verbose configuration in top-level.

  \<^descr> @{attribute C_starting_env} makes the start of a C
  command (e.g., \<^theory_text>\<open>C_file\<close>,
  \<^theory_text>\<open>C\<close>) initialized with the environment of
  the previous C command if existing.

  \<^descr> @{attribute C_starting_rule} sets which parsing function will be used to parse the next
  C commands (e.g., \<^theory_text>\<open>C_file\<close>, \<^theory_text>\<open>C\<close>).
\<close>

subsection \<open>Inner Annotation Commands\<close>

text \<open>
  \<^rail>\<open>
    (@@{annotation "#ML_file"} | @@{annotation ML_file} | @@{annotation "ML_file\<Down>"} |
      @@{annotation "#C_file"} | @@{annotation C_file} | @@{annotation "C_file\<Down>"}) @{syntax name} ';'?
    ;
    (@@{annotation "#ML"} | @@{annotation ML} | @@{annotation "ML\<Down>"} |
      @@{annotation "#setup"} | @@{annotation setup} | @@{annotation "setup\<Down>"} |
      @@{annotation "\<approx>setup"} | @@{annotation "\<approx>setup\<Down>"} |
      @@{annotation "#C"} | @@{annotation C} | @@{annotation "C\<Down>"} |
      @@{annotation "#C_export_boot"} | @@{annotation C_export_boot} | @@{annotation "C_export_boot\<Down>"}) @{syntax text}
    ;
    (@@{annotation "#C_export_file"} | @@{annotation C_export_file} | @@{annotation "C_export_file\<Down>"} |
     @@{annotation highlight} | @@{annotation "highlight\<Down>"})
    ;
  \<close>

  \<^descr> \<^C_theory_text>\<open>ML_file\<close>, \<^C_theory_text>\<open>C_file\<close>,
  \<^C_theory_text>\<open>ML\<close>, \<^C_theory_text>\<open>setup\<close>,
  \<^C_theory_text>\<open>C\<close>, \<^C_theory_text>\<open>C_export_boot\<close>, and
  \<^C_theory_text>\<open>C_export_file\<close> behave similarly as the respective outer commands
  \<^theory_text>\<open>ML_file\<close>, \<^theory_text>\<open>C_file\<close>,
  \<^theory_text>\<open>ML\<close>, \<^theory_text>\<open>setup\<close>,
  \<^theory_text>\<open>C\<close>, \<^theory_text>\<open>C_export_boot\<close>,
  \<^theory_text>\<open>C_export_file\<close>.

  \<^descr> \<^C_theory_text>\<open>\<approx>setup \<open>f'\<close>\<close> has the same semantics
  as \<^C_theory_text>\<open>setup \<open>f\<close>\<close> whenever \<^term>\<open>\<And> stack top
  env. f' stack top env = f\<close>. In particular, depending on where the annotation
  \<^C_theory_text>\<open>\<approx>setup \<open>f'\<close>\<close> is located in the C code, the
  additional values \<open>stack\<close>, \<open>top\<close> and \<open>env\<close> can drastically
  vary, and then can be possibly used in the body of \<open>f'\<close> for implementing new
  interactive features (e.g., in contrast to \<open>f\<close>, which by default does not have the
  possibility to directly use the information provided by \<open>stack\<close>, \<open>top\<close>
  and \<open>env\<close>).

  \<^descr> \<^C_theory_text>\<open>highlight\<close> changes the background color of the C tokens pointed by the command.

  \<^descr> \<^C_theory_text>\<open>#ML_file\<close>,
  \<^C_theory_text>\<open>#C_file\<close>, \<^C_theory_text>\<open>#ML\<close>,
  \<^C_theory_text>\<open>#setup\<close>,
  \<^C_theory_text>\<open>#C\<close>,
  \<^C_theory_text>\<open>#C_export_boot\<close>, and
  \<^C_theory_text>\<open>#C_export_file\<close>
  behave similarly as the respective (above inner) commands
  \<^C_theory_text>\<open>ML_file\<close>,
  \<^C_theory_text>\<open>C_file\<close>, \<^C_theory_text>\<open>ML\<close>,
  \<^C_theory_text>\<open>setup\<close>,
  \<^C_theory_text>\<open>C\<close>,
  \<^C_theory_text>\<open>C_export_boot\<close>, and
  \<^C_theory_text>\<open>C_export_file\<close>
  except that their evaluations happen as earliest as possible.

  \<^descr> \<^C_theory_text>\<open>ML_file\<Down>\<close>,
  \<^C_theory_text>\<open>C_file\<Down>\<close>, \<^C_theory_text>\<open>ML\<Down>\<close>,
  \<^C_theory_text>\<open>setup\<Down>\<close>,
  \<^C_theory_text>\<open>\<approx>setup\<Down>\<close>, \<^C_theory_text>\<open>C\<Down>\<close>,
  \<^C_theory_text>\<open>C_export_boot\<Down>\<close>,
  \<^C_theory_text>\<open>C_export_file\<Down>\<close>, and
  \<^C_theory_text>\<open>highlight\<Down>\<close>
  behave similarly as the respective (above inner) commands
  \<^C_theory_text>\<open>ML_file\<close>, \<^C_theory_text>\<open>C_file\<close>,
  \<^C_theory_text>\<open>ML\<close>, \<^C_theory_text>\<open>setup\<close>,
  \<^C_theory_text>\<open>\<approx>setup\<close>, \<^C_theory_text>\<open>C\<close>,
  \<^C_theory_text>\<open>C_export_boot\<close>,
  \<^C_theory_text>\<open>C_export_file\<close>, and
  \<^C_theory_text>\<open>highlight\<close>
  except that their evaluations happen as latest as possible.
\<close>

subsection \<open>Inner Directive Commands\<close>

text \<open>
  \<^descr> Among the directives provided as predefined in Isabelle/C, we currently have:
  \<^C>\<open>#define _\<close> and \<^C>\<open>#undef _\<close>. In particular, for the case of
  \<^C>\<open>#define _\<close>, rewrites are restricted to variable-form macros: support of
  functional macros is not yet provided.
  \<^descr> In Isabelle/C, not-yet-defined directives (such as \<^C>\<open>#include _\<close> or
  \<^C>\<open>#if
  #endif\<close>, etc.) do not make the parsing fail, but are treated as ``free variable commands''.
\<close>

section \<open>Quick Start (for People More Familiar with C than Isabelle)\<close>

text \<open>
\<^item> Assuming we are working with Isabelle 2019
\<^url>\<open>http://isabelle.in.tum.de/dist/Isabelle2019_app.tar.gz\<close>, the shortest way to
start programming in C is to open a new theory file with the shell-command:

\<^verbatim>\<open>$ISABELLE_HOME/bin/isabelle jedit -d $AFP_HOME/thys Scratch.thy\<close>

where \<^verbatim>\<open>$ISABELLE_HOME\<close> is the path of the above extracted Isabelle source,
and \<^verbatim>\<open>$AFP_HOME\<close> is the downloaded content of
\<^url>\<open>https://bitbucket.org/isa-afp/afp-2019\<close>.\<^footnote>\<open>This folder
particularly contains the Isabelle/C project, located in
\<^url>\<open>https://bitbucket.org/isa-afp/afp-2019/src/default/thys/Isabelle_C\<close>. To inspect
the latest developper version, one can also replace \<^verbatim>\<open>$AFP_HOME/thys\<close> by the
content downloaded from \<^url>\<open>https://gitlri.lri.fr/ftuong/isabelle_c\<close>.\<close>
\<^item> The next step is to copy this minimal content inside the newly opened window:
\<^verbatim>\<open>theory Scratch imports Isabelle_C.C_Main begin C \<open>
// C code
\<close> end\<close>
\<^item> \<^emph>\<open>Quod Erat Demonstrandum!\<close> This already enables the support of C code inside the special
brackets ``\<^verbatim>\<open>\<open>\<close>\<close>'', now depicted as
``\<open>\<open>\<close>\<close>'' for readability reasons. \<close>

text_raw \<open>
\begin{figure}
  \centering
\includegraphics[width=\textwidth]{figures/C-export-example}
  \caption{Making the File Browser Pointing to the Virtual File System}
  \label{fig:file-bro}
\end{figure}
\<close>

text \<open> Additionally, Isabelle/C comes with several functionalities that can be alternatively
explored:
\<^item> To write theorems and proofs along with C code, the special C comment
\<^C>\<open>/*@ (* Isabelle content *) */\<close> can be used at any position where C comments are
usually regularly allowed. At the time of writing, not yet all Isabelle commands can be written in C
comments, and certain proof-solving-command combinations are also not yet implemented --- manual
registration of commands to retrieve some more or less native user-experience remains possible
though. Generally, the kind of content one can write in C comments should be arbitrary. The
exhaustive list of Isabelle commands is provided in the accompanying above archive, for example in
\<^dir>\<open>$ISABELLE_HOME/src/Doc/Isar_Ref\<close> or
\<^url>\<open>https://isabelle.in.tum.de/doc/isar-ref.pdf\<close>.

\<^item> Instead of starting from scratch, any existing C files can also be opened with Isabelle/C,
it suffices to replace:

\begin{tabular}{c}
 \<^verbatim>\<open>C\<close> \<^theory_text>\<open>\<open> /* C */ \<close>\<close> \\
 by \\
 \<^verbatim>\<open>C_file\<close> \<^theory_text>\<open>\<open>~/file.c\<close>\<close>
\end{tabular}

Once done, one can press a CTRL-like key while hovering the mouse over the file name, then followed
by a click on it to open a new window loading that file.

\<^item> After a \<^verbatim>\<open>C\<close> \<^theory_text>\<open>\<open> /* C */ \<close>\<close>
command, one has either the possibility to keep the content as such in the theory file, or use
\<^verbatim>\<open>C_export_file\<close> to export all previous C content into a ``real'' C file.

Note that since Isabelle2019, Isabelle/C uses a virtual file-system. This has the consequence, that
some extra operations are needed to export a file generated into the virtual file-system of Isabelle
into the ``real'' file-system. First, the \<^verbatim>\<open>C_export_file\<close> command needs to
be activated, by putting the cursor on the command. This leads to the following message in the
output window: \<^verbatim>\<open>See theory exports "C/*/*.c"\<close> (see
\autoref{fig:file-bro}). By clicking on \<open>theory exports\<close> in
this message, Isabelle opens a \<open>File Browser\<close> showing the content of the virtual
file-system in the left window. Selecting and opening a generated file in the latter lets jEdit
display it in a new buffer, which gives the possibility to export this file via ``\<open>File
\<rightarrow> Save As\<dots>\<close>'' into the real file-system. \<close>

section \<open>Case Study: Mapping on the Parsed AST\<close>

text \<open> In this section, we give a concrete example of a situation where one is interested to
do some automated transformations on the parsed AST, such as changing the type of every encountered
variables from \<^C>\<open>int _;\<close> to \<^C>\<open>int _ [];\<close>. The main theory of
interest here is \<^theory>\<open>Isabelle_C.C_Parser_Language\<close>, where the C grammar is
loaded, in contrast to \<^theory>\<open>Isabelle_C.C_Lexer_Language\<close> which is only dedicated
to build a list of C tokens. As another example,
\<^theory>\<open>Isabelle_C.C_Parser_Language\<close> also contains the portion of the code
implementing the report to the user of various characteristics of encountered variables during
parsing: if a variable is bound or free, or if the declaration of a variable is made in the global
topmost space or locally declared in a function. \<close>

subsection \<open>Prerequisites\<close>

text \<open> Even if \<^file>\<open>generated/c_grammar_fun.grm.sig\<close> and
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close> are files written in ML syntax, we have
actually modified \<^dir>\<open>../src_ext/mlton/lib/mlyacc-lib\<close> in such a way that at run
time, the overall loading and execution of
\<^theory>\<open>Isabelle_C.C_Parser_Language\<close> will mimic all necessary features of the
Haskell parser generator Happy
\<^footnote>\<open>\<^url>\<open>https://www.haskell.org/happy/doc/html/index.html\<close>\<close>,
including any monadic interactions between the lexing
(\<^theory>\<open>Isabelle_C.C_Lexer_Language\<close>) and parsing part
(\<^theory>\<open>Isabelle_C.C_Parser_Language\<close>).

This is why in the remaining part, we will at least assume a mandatory familiarity with Happy (e.g.,
the reading of ML-Yacc's manual can happen later if wished
\<^footnote>\<open>\<^url>\<open>https://www.cs.princeton.edu/~appel/modern/ml/ml-yacc/manual.html\<close>\<close>). In
particular, we will use the term \<^emph>\<open>rule code\<close> to designate \<^emph>\<open>a
Haskell expression enclosed in braces\<close>
\<^footnote>\<open>\<^url>\<open>https://www.haskell.org/happy/doc/html/sec-grammar.html\<close>\<close>.
\<close>

subsection \<open>Structure of \<^theory>\<open>Isabelle_C.C_Parser_Language\<close>\<close>

text \<open> In more detail, \<^theory>\<open>Isabelle_C.C_Parser_Language\<close> can be seen as being
principally divided into two parts:
  \<^item> a first part containing the implementation of
  \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>, which provides the ML implementation library
  used by any rule code written in the C grammar
  \<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
  (\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>).
  \<^item> a second part implementing \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close>, providing
  one wrapping function for each rule code, for potentially complementing the rule code with an
  additional action to be executed after its call. The use of wrapping functions is very optional:
  by default, they are all assigned as identity functions.

The difference between \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> relies in how often functions in the two
structures are called: while building subtree pieces of the final AST, grammar rules are free to
call any functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> for completing their
respective tasks, but also free to not use \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> at
all. On the other hand, irrespective of the actions done by a rule code, the function associated to
the rule code in \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> is retrieved and always executed
(but a visible side-effect will likely mostly happen whenever one has provided an implementation far
different from \<^ML>\<open>I\<close>). \<close>

text \<open> Because the grammar
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
(\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>) has been defined in such a way that
computation of variable scopes are completely handled by functions in
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and not in rule code (which are just calling
functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>), it is enough to overload functions
in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> whenever it is wished to perform new actions
depending on variable scopes, for example to do a specific PIDE report at the first time when a C
variable is being declared. In particular, functions in
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> are implemented in monadic style, making a
subsequent modification on the parsing environment \<^theory>\<open>Isabelle_C.C_Environment\<close> possible
(whenever appropriate) as this last is carried in the monadic state.

Fundamentally, this is feasible because the monadic environment fulfills the property of being
always properly enriched with declared variable information at any time, because we assume
  \<^item> working with a language where a used variable must be at most declared or redeclared
  somewhere before its actual usage,
  \<^item> and using a parser scanning tokens uniquely, from left to right, in the same order as
  the execution of rule code actions. \<close>

subsubsection \<open>Example\<close>

text \<open> As illustration, \<^ML>\<open>C_Grammar_Rule_Lib.markup_var o C_Ast.Left\<close> is
(implicitly) called by a rule code while a variable being declared is encountered. Later, a call to
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var o C_Ast.Right\<close> in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> (actually, in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap_Overloading\<close>) is made after the execution of
another rule code to signal the position of a variable in use, together with the information
retrieved from the environment of the position of where it is declared. \<close>

text \<open> In more detail, the second argument of
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> is among other of the form:
\<^ML_type>\<open>Position.T * {global: bool}\<close>, where particularly the field
\<^ML>\<open>#global : C_Env.markup_ident -> bool\<close> of the record is informing
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> if the variable being reported (at either first
declaration time, or first use time) is global or local (inside a function for instance). Because
once declared, the property \<^ML>\<open>#global : C_Env.markup_ident -> bool\<close> of a variable
does not change afterwards, it is enough to store that information in the monadic environment:
\<^item> \<^bold>\<open>Storing the information at declaration time\<close> The part deciding if a
variable being declared is global or not is implemented in
\<^ML>\<open>C_Grammar_Rule_Lib.doDeclIdent\<close> and
\<^ML>\<open>C_Grammar_Rule_Lib.doFuncParamDeclIdent\<close>. The two functions come from
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
(so do any functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>). Ultimately, they are
both calling \<^ML>\<open>C_Grammar_Rule_Lib.markup_var o C_Ast.Left\<close> at some point.
\<^item> \<^bold>\<open>Retrieving the information at use time\<close>
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var o C_Ast.Right\<close> is only called by
\<^ML>\<open>C_Grammar_Rule_Wrap.primary_expression1\<close>, while treating a variable being
already declared. In particular the second argument of
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> is just provided by what has been computed by the
above point when the variable was declared (e.g., the globality versus locality
information). \<close>

subsection \<open>Rewriting of AST node\<close>

text \<open> For the case of rewriting a specific AST node, from subtree \<open>T1\<close> to
subtree \<open>T2\<close>, it is useful to zoom on the different parsing evaluation stages, as well
as make precise when the evaluation of semantic back-ends are starting.

\<^enum> Whereas annotations in Isabelle/C code have the potential of carrying arbitrary ML code (as
in \<^theory>\<open>Isabelle_C.C1\<close>), the moment when they are effectively evaluated
will not be discussed here, because to closely follow the semantics of the language in embedding (so
C), we suppose comments --- comprising annotations --- may not affect any parsed tokens living
outside comments. So no matter when annotations are scheduled to be future evaluated in Isabelle/C,
the design decision of Isabelle/C is to not let a code do directive-like side-effects in
annotations, such as changing \<open>T1\<close> to \<open>T2\<close> inside annotations.

\<^enum> To our knowledge, the sole category of code having the capacity to affect incoming stream
of tokens are directives, which are processed and evaluated before the ``major'' parsing step
occurs. Since in Isabelle/C, directives are relying on ML code, changing an AST node from
\<open>T1\<close> to \<open>T2\<close> can then be perfectly implemented in directives.

\<^enum> After the directive (pre)processing step, the main parsing happens. But since what are
driving the parsing engine are principally rule code, this step means to execute
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close>, i.e., rules in
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>.

\<^enum> Once the parsing finishes, we have a final AST value, which topmost root type entry-point
constitutes the last node built before the grammar parser
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
ever entered in a stop state. For the case of a stop acceptance state, that moment happens when we
reach the first rule code building the type \<^ML_type>\<open>C_Ast.CTranslUnit\<close>, since there
is only one possible node making the parsing stop, according to what is currently written in the C
grammar. (For the case of a state stopped due to an error, it is the last successfully built value
that is returned, but to simplify the discussion, we will assume in the rest of the document the
parser is taking in input a fully well-parsed C code.)

\<^enum> By \<^emph>\<open>semantic back-ends\<close>, we denote any kind of ``relatively
efficient'' compiled code generating Isabelle/HOL theorems, proofs, definitions, and so with the
potential of generally generating Isabelle packages. In our case, the input of semantic back-ends
will be the type \<^ML_type>\<open>C_Ast.CTranslUnit\<close> (actually, whatever value provided by
the above parser). But since our parser is written in monadic style, it is as well possible to give
slightly more information to semantic back-ends, such as the last monadic computed state, so
including the last state of the parsing environment. \<close>

text \<open> Generally, semantic back-ends can be written in full ML starting from
\<^ML_type>\<open>C_Ast.CTranslUnit\<close>, but to additionally support formalizing tasks requiring
to start from an AST defined in Isabelle/HOL, we provide an equivalent AST in HOL in the project,
such as the one obtained after loading
\<^url>\<open>https://gitlri.lri.fr/ftuong/citadelle-devel/blob/master/doc/Meta_C_generated.thy\<close>.
(In fact, the ML AST is just generated from the HOL one.) \<close>



text \<open>
Based on the above information, there are now several \<^emph>\<open>equivalent\<close> ways to
proceed for the purpose of having an AST node be mapped from \<open>T1\<close> to
\<open>T2\<close>. The next bullets providing several possible solutions to follow are particularly
sorted in increasing action time.

\<^item> \<^emph>\<open>Before even starting the Isabelle system.\<close> A first approach would be
to modify the C code in input, by adding a directive \<^C>\<open>#define _ _\<close> performing the
necessary rewrite.

\<^item> \<^emph>\<open>Before even starting the Isabelle system.\<close> As an alternative of
changing the C code, one can modify
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
by hand, by explicitly writing \<open>T2\<close> at the specific position of the rule code
generating \<open>T1\<close>. However, this solution implies to re-generate
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>.

\<^item> \<^emph>\<open>At grammar loading time, while the source of Isabelle/C is still being
processed.\<close> Instead of modifying the grammar, it should be possible to first locate which
rule code is building \<open>T1\<close>. Then it would remain to retrieve and modify the respective
function of \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> executed after that rule code, by
providing a replacement function to be put in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap_Overloading\<close>. However, as a design decision,
wrapping functions generated in \<^file>\<open>generated/c_grammar_fun.grm.sml\<close> have only
been generated to affect monadic states, not AST values. This is to prevent an erroneous replacement
of an end-user while parsing C code. (It is currently left open about whether this feature will be
implemented in future versions of the parser...)

\<^item> \<^emph>\<open>At directive setup time, before executing any
\<^theory_text>\<open>C\<close> command of interest.\<close> Since the behavior of directives can be
dynamically modified, this solution amounts to change the semantics of any wished directive,
appearing enough earlier in the code. (But for the overall code be in the end mostly compatible with
any other C preprocessors, the implementation change has to be somehow at least consistent with how
a preprocessor is already expected to treat an initial C un(pre)processed code.) For example, the
current semantics of \<^C>\<open>#undef _\<close> depends on what has been registered in
\<^ML>\<open>C_Context.directive_update\<close> (see \<^theory>\<open>Isabelle_C.C_Command\<close>).

\<^item> \<^emph>\<open>After parsing and obtaining a constructive value.\<close> Another solution
consists in directly writing a mapping function acting on the full AST, so writing a ML function of
type \<^ML_type>\<open>C_Ast.CTranslUnit -> C_Ast.CTranslUnit\<close> (or a respective HOL function)
which has to act on every constructor of the AST (so in the worst case about hundred of constructors
for the considered AST, i.e., whenever a node has to be not identically returned). However, as we
have already implemented a conversion function from \<^ML_type>\<open>C_Ast.CTranslUnit\<close>
(subset of C11) to a subset AST of C99, it might be useful to save some effort by starting from this
conversion function, locate where \<open>T1\<close> is pattern-matched by the conversion function,
and generate \<open>T2\<close> instead.

As example, the conversion function \<^ML>\<open>C_Ast.main\<close> is particularly used to connect
the C11 front-end to the entry-point of AutoCorres in
\<^verbatim>\<open>l4v/src/tools/c-parser/StrictCParser.ML\<close>.

\<^item> \<^emph>\<open>At semantic back-ends execution time.\<close> The above points were dealing
with the cases where modification actions were all occurring before getting a final
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> value. But this does not mean it is forbidden to make
some slight adjustments once that resulting \<^ML_type>\<open>C_Ast.CTranslUnit\<close> value
obtained. In particular, it is the tasks of semantic back-ends to precisely work with
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> as starting point, and possibly translate it to another
different type. So letting a semantic back-end implement the mapping from \<open>T1\<close> to
\<open>T2\<close> would mean here to first understand the back-end of interest's architecture, to
see where the necessary minimal modifications must be made.

By taking l4v as a back-end example, its integration with Isabelle/C first starts with translating
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> to l4v's default C99 AST. Then various analyses on the
obtained AST are performed in
\<^url>\<open>https://github.com/seL4/l4v/tree/master/tools/c-parser\<close> (the reader interested
in the details can start by further exploring the ML files loaded by
\<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/CTranslation.thy\<close>). In
short, to implement the mapping from \<open>T1\<close> to \<open>T2\<close> in the back-end part,
one can either:
  \<^item> modify the translation from \<^ML_type>\<open>C_Ast.CTranslUnit\<close> to C99,
  \<^item> or modify the necessary ML files of interests in the l4v project.
\<close>

text \<open> More generally, to better inspect the list of rule code really executed when a C code
is parsed, it might be helpful to proceed as in \<^theory>\<open>Isabelle_C.C1\<close>, by activating
\<^theory_text>\<open>declare[[C_parser_trace]]\<close>. Then, the output window will display the
sequence of Shift Reduce actions associated to the \<^theory_text>\<open>C\<close> command of
interest.
\<close>

section \<open>Known Limitations, Troubleshooting\<close>
subsection \<open>The Document Model of the Isabelle/PIDE (applying for Isabelle 2019)\<close>
subsubsection \<open>Introduction\<close>

text \<open> Embedding C directives in C code is an act of common practice in numerous applications,
as well as largely highlighted in the C standard. As an example of frequently encountered
directives, \<open>#include <some_file.c>\<close> is used to insert the content of
\<open>some_file.c\<close> at the place where it is written. In Isabelle/C, we can also write a C
code containing directives like \<open>#include\<close>, and generally the PIDE reporting of
directives is supported to a certain extent. Yet, the dynamic inclusion of arbitrary file with
\<open>#include\<close> is hurting a certain technological barrier. This is related to how the
document model of Isabelle 2019 is functioning, but also to the design decisions behind the
implementation of \<^theory_text>\<open>C\<open> .. \<close>\<close>. Thus, providing a complete
semantic implementation of \<open>#include\<close> might be not as evident as usual, if not more
dangerous, i.e. ``something requiring a manual intervention in the source of Isabelle 2019''. In the
next part, we show why in our current implementation of Isabelle/C there is no way for user
programmed extensions to exploit implicit dependencies between sub-documents in pure ML: a
sub-document referred to via \<open>#include <some_file>\<close> will not lead to a reevaluation of
a \<^theory_text>\<open>C\<open> .. \<close>\<close> command whenever modified.\<close>

subsubsection \<open>Embedding a language in Isabelle/PIDE\<close>

text \<open>
To clarify why the way a language being embedded in Isabelle is influencing the interaction between
a future parser of the language with the Isabelle's document model, we recall the two ``different''
ways of embedding a language in Isabelle/PIDE.

At its most basic form, the general syntactic scope of an Isabelle/Isar document can be seen as
being composed of two syntactic alternations of editing space: fragments of the inner syntax
language, themselves part of the more general outer syntax (the inner syntax is implemented as an
atomic entity of the outer language); see
\<^file>\<open>~~/src/Doc/Isar_Ref/Outer_Syntax.thy\<close>. So strictly speaking, when attempting
to support a new language \<open>L\<close> in Isabelle, there is always the question of fine-grain
estimating which subsets of \<open>L\<close> will be represented in the outer syntax part, and if it
possibly remains any left subsets to be represented on the more inner (syntactic) part.

Generally, to answer this question, there are several criteria to consider:
  \<^item> Are there any escaping symbols conflicting between \<open>L\<close> and the outer
  (syntax) language, including for example the ASCII \<^verbatim>\<open>"\<close> or
  \<^verbatim>\<open>`\<close>?
  \<^item> Is \<open>L\<close> a realistic language, i.e. more complex than any combinations of
  outer named tokens that can be ever covered in terms of expressivity power (where the list of
  outer named tokens is provided in \<^file>\<open>~~/src/Doc/Isar_Ref/Outer_Syntax.thy\<close>)?
  \<^item> Is it preferable of not altering the outer syntax language with too specific and
  challenging features of \<open>L\<close>? This is particularly true since in Isabelle 2019, there
  is no way of modifying the outer syntax without making the modifications irremediably happen on
  its source code.

For the above reasons, we have come up in Isabelle/C with the choice of making the full C language
be supported inside the inner syntax allocated space. In particular, this has become all the more
syntactically easy with the introduction of cartouches since Isabelle
2014.\<^footnote>\<open>Fortunately, parsing tokens of C do not strongly conflict with cartouche
delimiter symbols. For example, it should not be ethically wrong in C to write an opening cartouche
symbol (possibly in a C comment) without writing any closing cartouche symbol afterwards. However,
we have not encountered such C code in our tested codebase, and it is a functionality implicitly
rejected by the current parser of Isabelle/C, as it is relying on Isabelle 2019's parser combinator
library for the lexing part.\<close> However, for the case of the C language, certain C directives
like \<open>#include\<close> are meant to heavily interact with external files. In particular,
resources would be best utilized if we were taking advantage of the Isabelle's asynchronous document
model for such interaction task. Unfortunately, the inner syntax space only has a minimum
interaction with the document model, compared to the outer syntax one. Otherwise said, be it for
experimenting the inner syntax layer and see how far it can deal with the document layer, or
otherwise reimplementing parts of Isabelle/C in the outer syntax layer, the two solutions are
conducting to do modifications in the Isabelle 2019 source code. \<close>

text \<open> Note that the language embedding space of \<^theory_text>\<open>C\<close> closely
resembles to how ML sources are delimited within a \<^theory_text>\<open>ML\<close>
command. Additionally, in ML, one can use antiquotations to also refer to external files
(particularly in formal comments). Still, the problem is still present in ML: referred files are not
loaded in the document model. \<close>

subsubsection \<open>Examples\<close>

text \<open>
  \<^item> Commands declared as of type \<open>thy_decl\<close> in the theory header are scheduled
  to be executed once. Additionally, they are not tracking the content of file names provided in
  argument, so a change there will not trigger a reevaluation of the associated command. For
  example, even if the type of \<^theory_text>\<open>ML_file\<close> is not \<open>thy_decl\<close>,
  nothing prevents one to set it with \<open>thy_decl\<close> as type. In particular, by doing so,
  it is no more possible to CTRL-hover-click on the file name written after
  \<^theory_text>\<open>ML_file\<close>.
  \<^item> To make a command \<open>C\<close> track the content of \<open>file\<close>, whenever the
  file is changing, setting \<open>C\<close> to be of type \<open>thy_load\<close> in the theory
  header is a first step, but not enough. To be effective, \<open>file\<close> must also be loaded,
  by either explicitly opening it, or clicking on its name after the command. Examples of commands
  in this situation requiring a preliminary one-time-click include:
  \<^theory_text>\<open>external_file\<close>, \<^theory_text>\<open>bibtex_file\<close>,
  \<^theory_text>\<open>ML_file\<close>.
  Internally, the click is bound to a Scala code invoking a request to make an asynchronous
  dependency to the newly opened document at ML side.
  \<^item> In terms of recursivity, for the case of a chain of sub-documents of the form
  (a theory file containing: \<^theory_text>\<open>C_file \<open>file0.c\<close>\<close>)
  \<open>\<Longrightarrow>\<close>
  (C file \<^verbatim>\<open>file0.c\<close> containing: \<^C>\<open>#include <file1.c>\<close>)
  \<open>\<Longrightarrow>\<close>
  (C file \<^verbatim>\<open>file1.c\<close> containing: \<^C>\<open>#include <file2.c>\<close>)
  \<open>\<Longrightarrow>\<close>
  (C file \<^verbatim>\<open>file2.c\<close> containing: \<^C>\<open>#include <file3.c>\<close>), we
  ideally expect a modification in \<^verbatim>\<open>file3.c\<close> be taken into account in all
  ancestor files including the initial theory, provoking the associated command of the theory be
  reevaluated. However in C, directives resolving might be close to Turing-complete. For instance,
  one can also include files based on particular conditional situations: \<^C>\<open>#if _
    #include <file1>
  #else
    #include <file2>
    #include <file3>
  #endif\<close>
  \<^item> When a theory is depending on other theories (such as
  \<^theory>\<open>Isabelle_C.C_Eval\<close> depending on
  \<^theory>\<open>Isabelle_C.C_Parser_Language\<close> and
  \<^theory>\<open>Isabelle_C.C_Parser_Annotation\<close>), modifying the list of theories in
  importation automatically triggers what the user is expecting: for example, the newly added
  theories are dynamically imported, any change by another external editor makes everything
  consequently propagated.

  Following the internal implementation of the document model engine, we basically distinguish two
  phases of document importation: either at start-up time, or dynamically on user requests. Although
  the case of start-up time can be handled in pure ML side, the language dedicated to express which
  Isabelle theory files to import is less powerful than the close-to-Turing-completeness
  expressivity of C directives. On the other hand, the dynamic importation of files on user requests
  seems to be performed (at the time of writing) through a too high level ML protocol, mostly called
  from Scala side. Due to the fact that Isabelle/C is currently implemented in pure ML, a solution
  also in pure ML would thus sound more natural (although we are not excluding solutions interacting
  with Scala, as long as the resulting can be implemented in Isabelle, preferably outside of its own
  source).\<close>

subsection \<open>Parsing Error versus Parsing Correctness\<close>

text \<open> When trying to decide if the next parsing action is a Shift or Reduce action to
perform, the grammar simulator \<^ML>\<open>LALR_Parser_Eval.parse\<close> can actually decide to do
another action: ignore everything and immediately stop the simulation.

If the parser ever decides to stop, this can only be for two reasons:
\<^item> The parser is supposed to have correctly finished its parsing task, making it be in an
acceptance state. As acceptance states are encoded in the grammar, it is easy to find if this
information is correct, or if it has to be adjusted in more detail by inspecting
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
(\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>).
\<^item> The parser seems to be unable to correctly finish its parsing task. In this case, the user
will see an error be explicitly raised by the prover IDE. However raising an error is just the
default behavior of Isabelle/C: the decision to whether raise interruptive errors ultimately depends
on how front-end commands are implemented (such as \<^theory_text>\<open>C\<close>,
\<^theory_text>\<open>C_file\<close>, etc.). For instance, similarly as to how outer syntax commands
are implemented, we can imagine a tool implementing a kind of partial parsing, analyzing the longest
sequence of well-formed input, and discarding some strategic next set of faulty tokens with a well
suited informative message, so that the parsing process could be maximally repeated on what is
coming afterwards.

Currently, the default behavior of Isabelle/C is to raise the error defined in
\<^ML>\<open>C_Module.err\<close> at the very first opportunity \<^footnote>\<open>At the time of
writing it is: \<^emph>\<open>No matching grammar rule\<close>.\<close>. The possible solutions to
make the error disappear at the position the error is indicated can be detailed as follows:
  \<^item> Modifying the C code in input would be a first solution whenever we suspect something is
  making it erroneous (and when we have a reason to believe that the grammar is behaving as it
  should).

  \<^item> However, we could still get the above error in front of an input where one is usually
  expecting to see not causing a failure. In particular, there are several C features (such as C
  directives) explicitly left for semantic back-ends (pre-) processing, so in general not fully
  semantically processed at parsing time.

  For example, whereas the code \<^C>\<open>#define i int
  i a;\<close> succeeds, replacing its first line with the directive
  \<^C>\<open>#include <file.c>\<close> will not initially work, even if \<open>file.c\<close>
  contains \<^C>\<open>#define i int\<close>, as the former directive has been left for semantic
  back-end treatment. One way of solving this would be to modify the C code in input for it to be
  already preprocessed (without directives, for example the C example of
  \<^url>\<open>https://gitlri.lri.fr/ftuong/isabelle_c/blob/C/C11-BackEnds/AutoCorres_wrapper/examples/TestSEL4.thy\<close> is already provided as
  preprocessed). Another way would be adding a specific new semantic back-end implementing the
  automation of the preprocessing task (as done in
  \<^url>\<open>https://gitlri.lri.fr/ftuong/isabelle_c/blob/C/C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_TEC.thy\<close>, where the
  back-end explicitly makes a call to \<open>cpp\<close> at run-time).

  \<^item> Ultimately, modifying the grammar with new rules cancelling the exception would only work
  if the problem really relies on the grammar, as it was mentioned for the acceptance state.
  \<close>

text \<open> In terms of parsing correctness, Isabelle/C provides at least two different parsers:
\<^item> a parser limited to C99/C11 code provided in \<^dir>\<open>../C11-FrontEnd\<close> that can
parse certain liberal extensions out of the C
standard~\<^footnote>\<open>\<^url>\<open>http://hackage.haskell.org/package/language-c\<close>\<close>;
\<^item> and another parser accepting C99/C11/C18 code in \<^url>\<open>https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C18-FrontEnd\<close> that
is close to the C standard while focusing on resolving ambiguities of the
standard~\<^footnote>\<open>\<^url>\<open>https://github.com/jhjourdan/C11parser\<close>\<close>~\cite{DBLP:journals/toplas/JourdanP17}. \<close>

text \<open> Note that the two parsers are not accepting/rejecting the same range of arbitrary C
code. We have actually already encountered situations where an error is raised by one parser, while
a success is happening with the other parser (and vice-versa). Consequently, in front of a C code,
it can be a good recommendation to try out the parsing with all possible parsers of Isabelle/C. In
any cases, a failure in one or several activated parsers might not be necessarily harmful: it might
also indicate that a wrong parser has been selected, or a semantic back-end not yet supporting
aspects of the C code being parsed. \<close>

subsection \<open>Exporting C Files to the File-System\<close>

text \<open> From the Isabelle/C side, the task is easy, just type:\<close>

C_export_file

text \<open> ... which does the trick and generates a file
\<^verbatim>\<open>C_Appendices.c\<close>. But hold on --- where is it? Well, Isabelle/C uses since
version Isabelle2019 a virtual file-system. Exporting from it to the real file-system requires a few
mouse-clicks (unfortunately).

So activating the command \<^theory_text>\<open>C_export_file\<close> leads to the output
\<^verbatim>\<open>See theory exports "C/*/C_Appendices.c"\<close> (see
\autoref{fig:file-bro}), and clicking on the highlighted
\<^verbatim>\<open>theory exports\<close> lets Isabelle display a part of the virtual file-system
(see subwidget left). Activating it in the subwidget lets jEdit open it as an editable file, which
can be exported via ``\<open>File \<rightarrow> Save As\<dots>\<close>'' into the real
file-system. \<close>

end
