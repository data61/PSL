(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section Examples

theory Derive_Examples
imports 
  Derive
  "Comparator_Generator/Compare_Order_Instances"
  "Equality_Generator/Equality_Instances"
  HOL.Rat
begin

subsection "Rational Numbers"

text \<open>The rational numbers are not a datatype, so it will not be possible to derive 
  corresponding instances of comparators, hashcodes, etc. via the generators. But we can and should
  still register the existing instances, so that later datatypes are supported 
  which use rational numbers.\<close> 

text \<open>Use the linear order on rationals to define the @{class compare_order}-instance.\<close>
derive (linorder) compare_order rat

text \<open>Use @{term "(=) :: rat => rat => bool"} as equality function.\<close>
derive (eq) equality rat

text \<open>First manually define a hashcode function.\<close>

instantiation rat :: hashable
begin
definition "def_hashmap_size = (\<lambda>_ :: rat itself. 10)"
definition "hashcode (r :: rat) = hashcode (quotient_of r)"
instance
  by (intro_classes)(simp_all add: def_hashmap_size_rat_def)
end

text \<open>And then register it at the generator.\<close>

derive (hashcode) hash_code rat

subsection "A Datatype Without Nested Recursion"

datatype 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree"

derive compare_order bintree
derive countable bintree
derive equality bintree
derive hashable bintree

subsection "Using Other datatypes"

datatype nat_list_list = NNil | CCons "nat list \<times> rat option" nat_list_list

derive compare_order nat_list_list
derive countable nat_list_list
derive (eq) equality nat_list_list
derive hashable nat_list_list

subsection "Mutual Recursion"

datatype
  'a mtree = MEmpty | MNode 'a "'a mtree_list" and
  'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"

derive compare_order mtree mtree_list
derive countable mtree mtree_list
derive hashable mtree mtree_list

text \<open>For \<open>derive (equality|comparator|hash_code) mutual_recursive_type\<close> 
  there is the speciality that only one of the mutual recursive types has to be mentioned in
  order to register all of them. So one of @{type mtree} and @{type mtree_list} suffices.\<close>

derive equality mtree 
 
subsection "Nested recursion"

datatype 'a tree = Empty | Node 'a "'a tree list"
datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"

derive compare_order tree ttree
derive countable tree ttree
derive equality tree ttree
derive hashable tree ttree

subsection \<open>Examples from \isafor\<close>

datatype ('f,'v) "term" = Var 'v | Fun 'f "('f,'v) term list"
datatype ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"

derive compare_order "term" lab
derive countable "term" lab
derive equality "term" lab
derive hashable "term" lab

subsection "A Complex Datatype"
text \<open>
The following datatype has nested and mutual recursion, and
uses other datatypes.
\<close>

datatype ('a, 'b) complex = 
  C1 nat "'a ttree \<times> rat + ('a,'b) complex list" |
  C2 "('a, 'b) complex list tree tree" 'b "('a, 'b) complex" "('a, 'b) complex2 ttree list"
and ('a, 'b) complex2 = D1 "('a, 'b) complex ttree"

text \<open>On this last example type we illustrate the difference of the various comparator- and order-generators.

  For @{type complex} we create an instance of @{class compare_order} which also defines
  a linear order. Note however that the instance will 
  be @{type complex} :: (@{class compare}, @{class compare}) @{class compare_order}, i.e., the 
  argument types have to be in class @{class compare}. 

  For @{type complex2} we only derive @{class compare} which is not a subclass of @{class linorder}.
  The instance will be @{type complex2} :: (@{class compare}, @{class compare}) @{class compare}, i.e., 
  again the argument types have to be in class @{class compare}.

  To avoid the dependence on @{class compare}, we can also instruct \<open>derive\<close> to be based on 
  @{class linorder}. Here, the command \<open>derive linorder complex2\<close> will create the instance
  @{type complex2} :: (@{class linorder}, @{class linorder}) @{class linorder}, i.e., 
  here the argument types have to be in class @{class linorder}.
  \<close>
derive compare_order complex 
derive compare complex2
derive linorder complex2
derive countable complex complex2
derive equality complex
derive hashable complex complex2

end
