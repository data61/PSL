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

section\<open>Example: A Class Model Interactively Executed\<close>
subsection\<open>Introduction\<close>

theory
  Design_shallow
imports
  "../Toy_Library"
  "../Toy_Library_Static"
  "../embedding/Generator_dynamic_sequential"
begin
ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>

text\<open>
In this example, we configure our package to execute tactic SML code
(corresponding to some generated \verb|.thy| file, @{file \<open>Design_deep.thy\<close>}
details how to obtain such generated \verb|.thy| file).
Since SML code are already compiled (or reflected) and bound with the native Isabelle API in
@{theory Isabelle_Meta_Model.Generator_dynamic_sequential}, nothing is generated in this theory.
The system only parses arguments given to meta-commands and immediately calls the corresponding 
compiled functions.

The execution time is comparatively similar as if tactics were written by hand,
except that the generated SML code potentially inherits all optimizations performed
by the raw code generation of Isabelle (if any).
\<close>

generation_syntax [ shallow (generation_semantics [ design ])
                            (*SORRY*) (*no_dirty*)
                  (*, syntax_print*) ]
text\<open>
The configuration in @{keyword "shallow"} mode is straightforward:
in this mode @{command generation_syntax} basically terminates in $O(1)$.
\<close>

subsection\<open>Designing Class Models (I): Basics\<close>

Class Atom < Molecule
  Attributes size : Integer
End

       End End End 

Class Molecule < Person

Class Galaxy
  Attributes wormhole : UnlimitedNatural
             is_sound : Void
End!

Class Person < Galaxy
  Attributes salary : Integer
             boss : Person
             is_meta_thinking: Boolean

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 ]

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = [ salary = 1 ]

(* Class Big_Bang < Atom (* This will force the creation of a new universe. *) *)

subsection\<open>Designing Class Models (II): Jumping to Another Semantic Floor\<close>

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

PrePost \<sigma>\<^sub>1 \<sigma>\<^sub>1'

(* PrePost \<sigma>\<^sub>1 [ ([ salary = 1000 , boss = self 1 ] :: Person) ] *)

subsection\<open>Designing Class Models (III): Interaction with (Pure) Term\<close>

text\<open>
Here in @{keyword "shallow"} mode, the following expression is directly rejected: \\
\verb|Context Person :: content ()| \\
\verb|  Post "><"|
\<close>

Context[shallow] Person :: content () 
  Post : "a + b = c"

end
