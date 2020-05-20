(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

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

section Examples

theory Derive_Examples
imports 
  Derive
  HOL.Rat
begin

subsection "Register standard existing types"

derive linorder list sum prod

subsection "Without nested recursion"

datatype 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree"

derive linorder bintree
derive hashable bintree
derive countable bintree

subsection "Using other datatypes"

datatype nat_list_list = NNil | CCons "nat list" nat_list_list

derive linorder nat_list_list
derive hashable nat_list_list
derive countable nat_list_list

subsection "Explicit mutual recursion"

datatype
  'a mtree = MEmpty | MNode 'a "'a mtree_list" and
  'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"

derive linorder mtree
derive hashable mtree
derive countable mtree

subsection "Implicit mutual recursion"

datatype 'a tree = Empty | Node 'a "'a tree list"

datatype_compat tree

derive linorder tree
derive hashable tree
derive countable tree

datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"

datatype_compat ttree

derive linorder ttree
derive hashable ttree
derive countable ttree

subsection "Examples from IsaFoR"

datatype ('f,'v) "term" = Var 'v | Fun 'f "('f,'v) term list"

datatype_compat "term"

datatype ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"

datatype_compat lab

derive linorder "term" lab
derive countable "term" lab
derive hashable "term" lab

subsection "A complex datatype"
text \<open>
The following datatype has nested indirect recursion, mutual recursion and
uses other datatypes.
\<close>

datatype ('a, 'b) complex = 
  C1 nat "'a ttree" |
  C2 "('a, 'b) complex list tree tree" 'b "('a, 'b) complex" "('a, 'b) complex2 ttree list"
and ('a, 'b) complex2 = D1 "('a, 'b) complex ttree"

datatype_compat complex complex2

derive linorder complex
derive hashable complex
derive countable complex

end
