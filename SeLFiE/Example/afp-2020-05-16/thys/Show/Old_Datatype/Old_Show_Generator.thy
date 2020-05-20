(*
Copyright 2009-2014 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Generating Show-Functions for Data Types\<close>

theory Old_Show_Generator
imports
  Datatype_Order_Generator.Derive_Aux
  Old_Show
begin

subsection \<open>Introduction\<close>

text \<open>
  The show-generator registers itself at the derive-manager for the class @{class show}. To be more
  precise, it automatically generates the functions @{const shows_prec} and @{const shows_list} for
  some data type \<open>dtyp\<close> and proves the following instantiation.
  \begin{itemize}
  \item \<open>instantiation dtyp :: (show, ..., show) show\<close>
  \end{itemize}
  All the non-recursive types that are used in the data type must have a similar instantiation. For
  recursive type-dependencies this is automatically generated.

  For example, for the data type \<open>datatype tree = Leaf nat | Node (tree list)\<close> we require
  that \<open>nat\<close> is already in @{class show}, whereas for type @{typ "'a list"} nothing is
  required, since it is used recursively.

  However, if we define \<open>datatype tree = Leaf (nat list) | Node tree tree\<close> then also
  @{typ "'a list"} must provide a @{class show} instance.
\<close>

subsection \<open>Implementation Notes\<close>

text \<open>
  The generator uses the recursors from the data type package to define the show function.
  Constructors are displayed by their short names and arguments are separated by blanks and
  surrounded by parenthesis.

  The associativity is proven using the induction theorem from the data type package.
\<close>

subsection \<open>Features and Limitations\<close>

text \<open>
  The show-generator has been developed mainly for data types without explicit mutual recursion. For
  mutual recursive data types -- like \<open>datatype a = C b and b = D a a\<close> -- only for the first
  mentioned data type -- here \<open>a\<close> -- instantiations of the @{class show} are derived.

  Indirect recursion like in \<open>datatype tree = Leaf nat | Node (tree list)\<close> should work
  without problems.
\<close>

subsection \<open>Installing the Generator\<close>

definition shows_sep_paren :: "shows \<Rightarrow> shows"
where
  "shows_sep_paren s = ('' ('' +#+ s +@+ shows '')'')"

text \<open>
  The four crucial properties which are used to ensure associativity.
\<close>
lemma append_assoc_trans:
  assumes "\<And>r s. b r @ s = b (r @ s)"
  shows "((@) a +@+ b) r @ s = ((@) a +@+ b) (r @ s)"
  using assms by simp

lemma shows_sep_paren:
  assumes "\<And>r s. a r @ s = a (r @ s)"
    and "\<And>r s. b r @ s = b (r @ s)"
  shows "(shows_sep_paren a +@+ b) r @ s = (shows_sep_paren a +@+ b) (r @ s)"
  unfolding shows_sep_paren_def by (simp add: assms)

lemma shows_sep_paren_final:
  assumes "\<And>r s. a r @ s = a (r @ s)"
  shows "(shows_sep_paren a) r @ s = (shows_sep_paren a) (r @ s)"
  unfolding shows_sep_paren_def by (simp add: assms)

ML_file \<open>old_show_generator.ML\<close>

end

