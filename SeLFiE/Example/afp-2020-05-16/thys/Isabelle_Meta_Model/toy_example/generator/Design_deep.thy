(******************************************************************************
 * HOL-TOY
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

section\<open>Example: A Class Model Converted into a Theory File\<close>
subsection\<open>Introduction\<close>

theory
  Design_deep
imports
  "../embedding/Generator_dynamic_sequential"
begin
ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>

text\<open>
In this example, we configure our package to generate a \verb|.thy| file,
without executing the associated generated code contained in this \verb|.thy| file
(c.f. @{file \<open>Design_shallow.thy\<close>} for a direct evaluation).
This mode is particularly relevant for debugging purposes:
while by default no evaluation occurs, 
the generated files (and their proofs!) can be executed on
a step by step basis, depending on how we interact with the output window
(by selectively clicking on what is generated).

After clicking on the generated content, the newly inserted content could depend on some theories
which are not loaded by this current one.
In this case, it is necessary to manually add all the needed dependencies above after the 
keyword @{keyword "imports"}.
One should compare this current theory with @{file \<open>Design_shallow.thy\<close>}
to see the differences of imported theories, and which ones to manually import
(whenever an error happens).
\<close>

generation_syntax [ (*deep
                      (generation_semantics [ design (*, oid_start 10*) ])
                      (THEORY Design_generated)
                      (IMPORTS ["../Toy_Library", "../Toy_Library_Static"]
                               "../embedding/Generator_dynamic_sequential")
                      SECTION
                      (*SORRY*) (*no_dirty*)
                      [ (* in Haskell *)
                        (* in OCaml module_name M *)
                        (* in Scala module_name M *)
                        in SML module_name M ]
                      (output_directory "../document_generated")
                  (*, syntax_print*)*) ]

text\<open>
\begin{verbatim}
generation_syntax
  [ deep
      (generation_semantics [ design ])
      (THEORY Design_generated)
      (IMPORTS ["../Toy_Library", "../Toy_Library_Static"]
               "../embedding/Generator_dynamic_sequential")
      SECTION
      (*SORRY*) (*no_dirty*)
      [ (* in Haskell *)
        (* in OCaml module_name M *)
        (* in Scala module_name M *)
        in SML module_name M ]
      (output_directory "../document_generated")
  (*, syntax_print*) ]
\end{verbatim}
While in theory it is possible to set the @{keyword "deep"} mode
for generating in all target languages, i.e. by writing 
\<open>[ in Haskell, in OCaml module_name M, in Scala module_name M, in SML module_name M ]\<close>,
usually using only one target is enough,
since the task of all target is to generate the same Isabelle content.
However in case one language takes too much time to setup,
we recommend to try the generation with another target language,
because all optimizations are currently not (yet) seemingly implemented for all target languages,
or differently activated.\<close>

subsection\<open>Designing Class Models (I): Basics\<close>

text\<open>
The following example shows the definitions of a set of classes, 
called the ``universe'' of classes.
Instead of providing a single command for building all the complete universe of classes
directly in one block, 
we are constructing classes one by one.
So globally the universe describing all classes is partial, it
will only be fully constructed when all classes will be finished to be defined.

This allows to define classes without having to follow a particular order of definitions.
Here \<open>Atom\<close> is defined before the one of \<open>Molecule\<close>
(\<open>Molecule\<close> will come after):
\<close>

Class Atom < Molecule
  Attributes size : Integer
End

text\<open>The ``blue'' color of @{command End} indicates that
@{command End} is not a ``green'' keyword. 
@{command End} and @{command Class} are in fact similar, they belong to the group of meta-commands
(all meta-commands are defined in @{theory Isabelle_Meta_Model.Generator_dynamic_sequential}).
At run-time and in @{keyword "deep"} mode, the semantics of all meta-commands are 
approximately similar: all meta-commands displays some quantity of Isabelle code
in the output window (as long as meta-commands are syntactically correctly formed).
However each meta-command is unique because what is displayed
in the output window depends on the sequence of all meta-commands already encountered before
(and also depends on arguments given to the meta-commands).\<close>

text\<open>
One particularity of @{command End} is to behave as the identity function when 
@{command End} is called without arguments.
As example, here we are calling lots of @{command End} without arguments,
and no Isabelle code is generated.\<close>
       End End End 
text\<open>
We remark that, like any meta-commands, @{command End} could have been written anywhere
in this theory, for example before @{command Class} or even before @{command generation_syntax}...
Something does not have to be specially opened before using an @{command End}.
\<close>

Class Molecule < Person
text\<open>As example, here no @{command End} is written.\<close>

text\<open>
The semantics of @{command End} is further precised here. 
We earlier mentioned that the universe of classes is partially constructed, but one can still
examine what is partially constructed, and one possibility is to use @{command End} for doing so.

@{command End} can be seen as a lazy meta-command: 
\begin{itemize}
\item without parameters, no code is generated,
\item with some parameters (e.g., the symbol \verb|!|), it forces the generation of the computation
of the universe, by considering all already encountered classes. 
Then a partial representation of the universe can be interactively inspected.
\end{itemize}
\<close>

Class Galaxy
  Attributes wormhole : UnlimitedNatural
             is_sound : Void
End!

text\<open>At this position, in the output window, 
we can observe for the first time some generated Isabelle code,
corresponding to the partial universe of classes being constructed.

Note: By default, \<open>Atom\<close> and \<open>Molecule\<close> are not (yet) present in the shown universe
because \<open>Person\<close> has not been defined in a separate line (unlike \<open>Galaxy\<close> above).\<close>

Class Person < Galaxy
  Attributes salary : Integer
             boss : Person
             is_meta_thinking: Boolean

text\<open>
There is not only @{command End} which forces the computation of the universe, for example
@{command Instance} declares a set of objects belonging to the classes earlier defined, 
but the entire universe is needed as knowledge, so there is no choice than forcing
the generation of the universe.
\<close>

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 ]

text\<open>
Here we will call @{command Instance} again to show that the universe will not be computed again
since it was already computed in the previous @{command Instance}.
\<close>

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = [ salary = 1 ]

text\<open>However at any time, the universe can (or will) automatically be recomputed,
whenever we are adding meanwhile another class:

@{verbatim "(* Class Big_Bang < Atom (* This will force the creation of a new universe. *) *)"}

As remark, not only the universe is recomputed, but 
the recomputation takes also into account all meta-commands already encountered. 
So in the new setting, \<open>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<close>, \<open>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<close> and \<open>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<close> 
will be resurrected... after the \<open>Big_Bang\<close>.
\<close>

subsection\<open>Designing Class Models (II): Jumping to Another Semantic Floor\<close>

text\<open>
Until now, meta-commands was used to generate lines of code, and
these lines belong to the Isabelle language.
One particularity of meta-commands is to generate pieces of code containing not only Isabelle code
but also arbitrary meta-commands. 
In @{keyword "deep"} mode, this is particularly not a danger 
for meta-commands to generate themselves
(whereas for @{keyword "shallow"} the recursion might not terminate).

In this case, such meta-commands must automatically generate the appropriate call to
@{command generation_syntax} beforehand. 
However this is not enough, the compiling environment (comprising the
history of meta-commands) are changing throughout the interactive evaluations,
so the environment must also be taken into account and propagated when meta-commands
are generating themselves.
For example, the environment is needed for consultation whenever resurrecting objects,
recomputing the universe or accessing the hierarchy of classes being
defined.

As a consequence, in the next example a line @{command setup} is added
after @{command generation_syntax} for bootstrapping the state of the compiling environment.
\<close>

State \<sigma>\<^sub>1 =
  [ ([ salary = 1000 , boss = self 1 ] :: Person)
  , ([ salary = 1200 ] :: Person)
  (* *)
  , ([ salary = 2600 , boss = self 3 ] :: Person)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
  , ([ salary = 2300 , boss = self 2 ] :: Person)
  (* *)
  (* *)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]

State \<sigma>\<^sub>1' =
  [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 ]

text \<open>
In certain circumstances, the command @{command setup}
must be added again between some particular interleaving of two meta-commands
and this may not depend on the presence of @{command generation_syntax}
(which is defined only once when generating the first meta-command).
For more details, one can refer to the source code of
@{term "ignore_meta_header"} and @{term "bootstrap_floor"}.\<close>

PrePost \<sigma>\<^sub>1 \<sigma>\<^sub>1'

text\<open>
The generation of meta-commands allows to perform various extensions
on the Toy language being embedded, without altering the semantics of a particular command.
@{command PrePost} usually only takes ``bound variables'' as parameters
(not arbitrary \<open>\<lambda>\<close>-terms), however the semantics of @{command PrePost} was extended
to mimic the support of some particular terms not restricted to variables.
This extension was implemented by executing some steps of ``\<open>\<zeta>\<close>-reductions rewriting rules''
operating on the meta-level of commands.
First, it is at least needed to extend the syntax of expressions accepted by @{command PrePost}, 
we then modify the parsing so that a larger subset of \<open>\<lambda>\<close>-terms
can be given as parameters.
Starting from this expression: \\
@{verbatim "(* PrePost \<sigma>\<^sub>1 [ ([ salary = 1000 , boss = self 1 ] :: Person) ] *)"}

the rewriting begins with a first call to the next semantic floor, we obtain 
the following meta-commands (where @{command PrePost} \<open>[shallow]\<close> is an expression 
in normal form): \\
@{verbatim \<open>(* State WFF_10_post = [ ([ "salary" = 1000, "boss" = self 1 ] :: Person) ]\<close>} \\
@{verbatim "   PrePost[shallow] \<sigma>\<^sub>1 WFF_10_post *)"}
(\<open>WFF_10_post\<close> is an automatically generated name).

The rewriting of the above @{command State} is performed in its turn.
Finally the overall ultimately terminates when reaching @{command Instance} being already 
in normal form: \\
@{verbatim \<open>(* Instance WFF_10_post_object0 :: Person = [ "salary" = 1000, "boss" = [  ] ]\<close>} \\
@{verbatim "   State[shallow] WFF_10_post = [ WFF_10_post_object0 ]"} \\
@{verbatim "   PrePost[shallow] \<sigma>\<^sub>1 WFF_10_post *)"}
\<close>

subsection\<open>Designing Class Models (III): Interaction with (Pure) Term\<close>

text\<open>
Meta-commands are obviously not restricted to manipulate expressions in the Outer Syntax level.
It is possible to build meta-commands so that Inner Syntax expressions are directly parsed.
However the dependencies of this theory have been minimized so that experimentations
and debugging can easily occur in @{keyword "deep"} mode 
(this file only depends on @{theory Isabelle_Meta_Model.Generator_dynamic_sequential}). 
Since the Inner Syntax expressions would perhaps manipulate expressions coming from other theories
than @{theory Isabelle_Meta_Model.Generator_dynamic_sequential}, 
it can be desirable to consider the Inner Syntax container as a string and leave the parsing 
for subsequent semantic floors.

This is what is implemented here:
\<close>
text\<open>
\verb|Context Person :: content ()| \\
\verb|  Post "><"|
\<close>

text\<open>
Here the expression @{verbatim "><"} is not well-typed in Isabelle, but an error is not raised
because the above expression is not (yet) parsed as an Inner Syntax element\footnote{
In any case an error will not be raised, because the above code 
is written in verbatim in the real @{verbatim ".thy"} file,
however one can copy-paste this code out of the verbatim scope to see that
no errors are really raised.
For presentation purposes, it was embedded in verbatim because we will later discuss about
meta-commands generating Isabelle code,
and then what is generated by this meta-command is of course not well-typed!}.

However, this is not the same for the resulting generated meta-command: \\
\verb|Context [shallow] Person :: content ()| \\
\verb|  Post : "(\<lambda> result self. (><))"| \\
and an error is immediately raised because the parsing of Inner Syntax expressions
is activated in this case.
\<close>

text\<open>For example, one can put the mouse, with the CTRL gesture,
over the variable @{term "a"}, @{term "b"} or @{term "c"}
to be convinced that they are free variables compared with above:\<close>

Context[shallow] Person :: content () 
  Post : "a + b = c"

subsection\<open>Designing Class Models (IV): Saving the Generated to File\<close>

text\<open>
The experimentations usually finish by saving all the universe 
and generated Isabelle theory to the hard disk: \\
@{verbatim "(* generation_syntax deep flush_all *)"}
\<close>

subsection\<open>Designing Class Models (V): Inspection of Generated Files\<close>

text\<open>
According to options given to the (first) command @{command generation_syntax} above, 
we retrieve the first generated file in the mentioned directory:
@{file \<open>../document_generated/Design_generated.thy\<close>}.

Because this file still contains meta-commands, we are here executing again
a new generating step inside this file, the new result becomes saved in
@{file \<open>../document_generated/Design_generated_generated.thy\<close>}.
As remark, in this last file, the dependency to @{theory Isabelle_Meta_Model.Generator_dynamic_sequential} was 
automatically removed because the meta-compiler has detected the absence of meta-commands
in the generated content.

Note: While the first generated file is intended to be always well-typed, 
it can happen that subsequent generations will lead to a not well-typed file. 
This is because the meta-compiler only saves the history of meta-commands.
In case some ``native'' Isabelle declarations 
are generated among meta-commands, then these Isabelle declarations
are not saved by the meta-compiler,
so these declarations will not be again generated.
Anyway, we see potential solutions for solving this and 
they would perhaps be implemented in a future version of the meta-compiler...
\<close>

end
